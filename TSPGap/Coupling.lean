/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Flow
import TSPGap.AdjacentLayers

/-!
# Finite weighted Strassen, and the adjacent-layer covering

The covering coupling needed for Lemma 2.26 turns out to need no
Hahn–Banach and no separate Strassen development: `exists_flow_of_cut` is
already the right theorem, applied to the network whose arcs are the pairs
`S ⊆ T`.

* `exists_coupling_of_dominates` — **finite weighted Strassen**.  Give the
  allowed arcs capacity the common total mass `M`.  A cut is then paid for
  in one of two ways: if *any* allowed arc crosses it, that arc alone
  carries `M`; otherwise the upward closure of the source-side rows lies
  inside the source-side columns, and the domination hypothesis pays.
  Since the flow value is exactly `M = ∑ p = ∑ q` while the row and column
  sums are bounded by `p` and `q`, both marginals are *exact*.
* `exists_adjacent_covering` — the application.  ⚠️ Division-free: couple
  `p = m_{k+1} · E_k` with `q = m_k · E_{k+1}`, whose common mass is
  `m_k · m_{k+1}`; `adjacent_layer_mono` is literally the Hall condition for
  that pair.  Fixed ranks then force every arc of the coupling to add
  exactly one edge, `|S| = k` and `|T| = k+1`.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Two small mass lemmas -/

omit [DecidableEq ι] in
theorem weightMass_mem_finset (w : Finset ι → ℝ) (F : Finset (Finset ι)) :
    weightMass w (fun S => S ∈ F) = ∑ S ∈ F, w S := by
  classical
  rw [weightMass]
  refine Eq.trans (Finset.sum_subset (Finset.subset_univ F)
    (fun S _ hS => by simp [hS])).symm ?_
  exact Finset.sum_congr rfl fun S hS => by simp [hS]

omit [DecidableEq ι] in
theorem weightMass_smul (c : ℝ) (v : Finset ι → ℝ) (P : Finset ι → Prop) :
    weightMass (fun S => c * v S) P = c * weightMass v P := by
  classical
  rw [weightMass, weightMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hP : P S
  · rw [if_pos hP, if_pos hP]
  · rw [if_neg hP, if_neg hP, mul_zero]

omit [DecidableEq ι] in
theorem totalMass_smul (c : ℝ) (v : Finset ι → ℝ) :
    totalMass (fun S => c * v S) = c * totalMass v := by
  rw [totalMass, totalMass, Finset.mul_sum]

/-! ### Finite weighted Strassen -/

omit [DecidableEq ι] in
/-- **Stochastic domination yields a coupling.**  If `p` and `q` have the
same total mass and every increasing event is at least as heavy under `q`,
there is a nonnegative `z`, supported on pairs `S ⊆ T`, whose row and column
marginals are exactly `p` and `q`. -/
theorem exists_coupling_of_dominates {p q : Finset ι → ℝ}
    (hp : WeightNonneg p) (hq : WeightNonneg q)
    (htot : totalMass p = totalMass q)
    (hdom : ∀ W : Finset ι → Prop, Monotone W →
      weightMass p W ≤ weightMass q W) :
    ∃ z : Finset ι → Finset ι → ℝ, (∀ S T, 0 ≤ z S T)
      ∧ (∀ S T, ¬ S ⊆ T → z S T = 0)
      ∧ (∀ S, ∑ T, z S T = p S) ∧ (∀ T, ∑ S, z S T = q T) := by
  classical
  have hM0 : 0 ≤ totalMass p := totalMass_nonneg hp
  have hynn : ∀ S T : Finset ι,
      0 ≤ (if S ⊆ T then totalMass p else 0) := by
    intro S T
    by_cases h : S ⊆ T
    · rw [if_pos h]; exact hM0
    · rw [if_neg h]
  -- the cut condition
  have hcut : ∀ SA SB : Finset (Finset ι),
      totalMass p ≤ cutCap (α := Finset ι) (β := Finset ι)
        (fun S T => if S ⊆ T then totalMass p else 0) p q SA SB := by
    intro SA SB
    have hmid0 : 0 ≤ ∑ S ∈ SA, ∑ T ∈ SBᶜ,
        (if S ⊆ T then totalMass p else 0) :=
      Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun T _ => hynn S T
    have h1 : 0 ≤ ∑ S ∈ SAᶜ, p S := Finset.sum_nonneg fun S _ => hp S
    have h2 : 0 ≤ ∑ T ∈ SB, q T := Finset.sum_nonneg fun T _ => hq T
    by_cases hcross : ∃ S ∈ SA, ∃ T ∈ SBᶜ, S ⊆ T
    · -- one allowed arc crosses the cut, and it alone pays
      obtain ⟨S, hS, T, hT, hST⟩ := hcross
      have hval : (if S ⊆ T then totalMass p else (0:ℝ)) = totalMass p :=
        if_pos hST
      have hstep := Finset.single_le_sum (f := fun T' =>
        if S ⊆ T' then totalMass p else (0:ℝ)) (fun T' _ => hynn S T') hT
      rw [hval] at hstep
      have hinner : totalMass p
          ≤ ∑ T' ∈ SBᶜ, (if S ⊆ T' then totalMass p else 0) := hstep
      have houter : ∑ T' ∈ SBᶜ, (if S ⊆ T' then totalMass p else 0)
          ≤ ∑ S' ∈ SA, ∑ T' ∈ SBᶜ, (if S' ⊆ T' then totalMass p else 0) :=
        Finset.single_le_sum (f := fun S' =>
          ∑ T' ∈ SBᶜ, (if S' ⊆ T' then totalMass p else 0))
          (fun S' _ => Finset.sum_nonneg fun T' _ => hynn S' T') hS
      rw [cutCap]
      linarith
    · -- no crossing arc: the upward closure of `SA` lies inside `SB`
      have hclosed : ∀ S ∈ SA, ∀ T : Finset ι, S ⊆ T → T ∈ SB := by
        intro S hS T hST
        by_contra hT
        exact hcross ⟨S, hS, T, Finset.mem_compl.mpr hT, hST⟩
      have hWmono : Monotone (fun T => ∃ S ∈ SA, S ⊆ T) := by
        rintro T T' hTT ⟨S, hS, hST⟩
        exact ⟨S, hS, le_trans hST hTT⟩
      have hstep1 : weightMass p (fun S => S ∈ SA)
          ≤ weightMass p (fun T => ∃ S ∈ SA, S ⊆ T) :=
        weightMass_mono hp fun S hS => ⟨S, hS, Finset.Subset.refl S⟩
      have hstep2 : weightMass q (fun T => ∃ S ∈ SA, S ⊆ T)
          ≤ weightMass q (fun T => T ∈ SB) :=
        weightMass_mono hq fun T hT => by
          obtain ⟨S, hS, hST⟩ := hT
          exact hclosed S hS T hST
      have hkey : ∑ S ∈ SA, p S ≤ ∑ T ∈ SB, q T := by
        rw [← weightMass_mem_finset, ← weightMass_mem_finset]
        exact le_trans hstep1 (le_trans (hdom _ hWmono) hstep2)
      have hcompl : ∑ S ∈ SAᶜ, p S = totalMass p - ∑ S ∈ SA, p S := by
        rw [totalMass, ← Finset.sum_add_sum_compl SA p]
        ring
      rw [cutCap, hcompl]
      linarith
  obtain ⟨z, hzflow, hztot⟩ := exists_flow_of_cut (α := Finset ι) (β := Finset ι)
    (y := fun S T => if S ⊆ T then totalMass p else 0) (cA := p) (cB := q)
    (τ := totalMass p) hynn hp hq hM0 hcut
  refine ⟨z, hzflow.nonneg, ?_, ?_, ?_⟩
  · intro S T hST
    have hle := hzflow.le_cap S T
    rw [if_neg hST] at hle
    exact le_antisymm hle (hzflow.nonneg S T)
  · -- the row marginals are exact
    have hsum : ∑ S, (∑ T, z S T) = ∑ S, p S := hztot
    intro S
    exact (Finset.sum_eq_sum_iff_of_le
      (fun S _ => hzflow.row S)).mp hsum S (Finset.mem_univ S)
  · -- and so are the column marginals
    have hsum : ∑ T, (∑ S, z S T) = ∑ T, q T := by
      rw [← flowTotal_eq_col, hztot, htot]
      rfl
    intro T
    exact (Finset.sum_eq_sum_iff_of_le
      (fun T _ => hzflow.col T)).mp hsum T (Finset.mem_univ T)

/-! ### The adjacent-layer covering -/

/-- **Adjacent projected layers are coupled by single-edge additions.**
Division-free: the two sides are scaled by the *opposite* layer masses, so
the common total is `m_k · m_{k+1}` and `adjacent_layer_mono` is exactly the
Hall condition. -/
theorem exists_adjacent_covering {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι) (k : ℕ) :
    ∃ z : Finset ι → Finset ι → ℝ, (∀ S T, 0 ≤ z S T)
      ∧ (∀ S T, z S T ≠ 0 → S ⊆ T ∧ S.card = k ∧ T.card = k + 1)
      ∧ (∀ S, ∑ T, z S T
          = totalMass (projLayer w F (k + 1)) * projLayer w F k S)
      ∧ (∀ T, ∑ S, z S T
          = totalMass (projLayer w F k) * projLayer w F (k + 1) T) := by
  classical
  set m : ℝ := totalMass (projLayer w F k) with hm
  set m' : ℝ := totalMass (projLayer w F (k + 1)) with hm'
  have hkn : WeightNonneg (projLayer w F k) := weightNonneg_projLayer hnn F k
  have hk1n : WeightNonneg (projLayer w F (k + 1)) :=
    weightNonneg_projLayer hnn F (k + 1)
  have hm0 : 0 ≤ m := totalMass_nonneg hkn
  have hm'0 : 0 ≤ m' := totalMass_nonneg hk1n
  obtain ⟨z, hz0, hzsub, hrow, hcol⟩ := exists_coupling_of_dominates
    (p := fun S => m' * projLayer w F k S)
    (q := fun T => m * projLayer w F (k + 1) T)
    (fun S => mul_nonneg hm'0 (hkn S)) (fun T => mul_nonneg hm0 (hk1n T))
    (by rw [totalMass_smul, totalMass_smul, ← hm, ← hm']; ring)
    (fun W hW => by
      rw [weightMass_smul, weightMass_smul]
      have := adjacent_layer_mono hst hr hnn htot F k hW
      rw [← hm, ← hm'] at this
      linarith)
  refine ⟨z, hz0, ?_, hrow, hcol⟩
  intro S T hzST
  have hpos : 0 < z S T := lt_of_le_of_ne (hz0 S T) (Ne.symm hzST)
  have hsub : S ⊆ T := by
    by_contra hc
    exact hzST (hzsub S T hc)
  refine ⟨hsub, ?_, ?_⟩
  · have hrowpos : 0 < ∑ T', z S T' :=
      lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun T' _ => hz0 S T') (Finset.mem_univ T))
    rw [hrow S] at hrowpos
    have hne : projLayer w F k S ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hrowpos
      exact lt_irrefl 0 hrowpos
    exact fixedRankWeight_projLayer w F k S hne
  · have hcolpos : 0 < ∑ S', z S' T :=
      lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun S' _ => hz0 S' T) (Finset.mem_univ S))
    rw [hcol T] at hcolpos
    have hne : projLayer w F (k + 1) T ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcolpos
      exact lt_irrefl 0 hcolpos
    exact fixedRankWeight_projLayer w F (k + 1) T hne

end TSPGap

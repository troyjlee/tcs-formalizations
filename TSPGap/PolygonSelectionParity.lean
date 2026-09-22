/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonSelectionTransfer

/-!
# Symbolic parity bounds under polygon selection

Only the polygon law is required to be stable. The selected weight enters
through inside/outside independence and its one-hot crossing support.
Both kernels keep the exponential dependence on the mean error explicit.
-/

namespace TSPGap.PolygonSelection
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {ζ m : ℝ}

set_option maxHeartbeats 2000000 in
-- The parity expansion unfolds several conditioned laws and their count events.
/-- The symbolic odd-parity bound for the selected law. -/
theorem corollary_5_10_core {μ : TreeDist n x} {εη : ℝ} {S u : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ)
    (hSne : S.Nonempty) (huS : u ⊆ S)
    (hAB : Disjoint (cutEdges u) N.partA ∨ Disjoint (cutEdges u) N.partB)
    (hzero : weightMass (polygonLaw μ S N.partC)
      (fun T => (T ∩ (cutEdges u ∩ internalEdges S)).card = 0) = 0)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 0.0005)
    (hmlo : 2 - d ≤ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v)
    (hmhi : expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
      ≤ 2 + d) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      ≤ max ((1 + Real.exp (2 * d - 2)) / 2) (1 / 2 + d) * totalMass v := by
  classical
  obtain ⟨z, hvz⟩ := hb.selected
  set ν : Finset (Sym2 (Fin n)) → ℝ := polygonLaw μ S N.partC with hν
  set Din : Finset (Sym2 (Fin n)) := cutEdges u ∩ internalEdges S with hDin
  set Dout : Finset (Sym2 (Fin n)) := cutEdges u ∩ cutEdges S with hDout
  set M : ℝ := totalMass v with hM
  set a : ℝ := weightMass ν (fun T => Odd (T ∩ Din).card) with ha
  set b0 : ℝ := weightMass v (fun T => (T ∩ Dout).card = 0) with hb0
  set b1 : ℝ := weightMass v (fun T => (T ∩ Dout).card = 1) with hb1
  -- the support facts
  have hsupp : ∀ T, v T ≠ 0 → (T ∩ N.partA).card = 1 ∧ (T ∩ N.partB).card = 1
      ∧ (T ∩ N.partC).card = 0 := by
    intro T hT
    obtain ⟨hA, hB⟩ := hb.support T hT
    refine ⟨hA, hB, ?_⟩
    have hνT : ν T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  have hle1 : ∀ T, v T ≠ 0 → (T ∩ Dout).card ≤ 1 := by
    intro T hT
    obtain ⟨hA, hB, hC⟩ := hsupp T hT
    exact card_dout_le_one hroot hAB hA hB hC
  -- determinacy
  have hDinsub : ∀ g ∈ Din, ∀ w ∈ g, w ∈ S := by
    intro g hg w hw
    exact (mem_internalEdges.mp (Finset.mem_inter.mp hg).2).2 w hw
  have hDoutsub : Dout ⊆ cutEdges S := fun g hg => (Finset.mem_inter.mp hg).2
  have hinOdd : InsideDetermined S (fun T => Odd (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Odd X.card)
  have hinEven : InsideDetermined S (fun T => Even (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Even X.card)
  have houtD : ∀ k : ℕ, OutsideDetermined S (fun T => (T ∩ Dout).card = k) := fun k =>
    outsideDetermined_inter (fun g hg => not_forall_mem_of_mem_cutEdges (hDoutsub hg))
      (fun X => X.card = k)
  have hAcut : N.partA ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partA_subset_cutEdges_root
  have hBcut : N.partB ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partB_subset_cutEdges_root
  -- the cross-independence hypotheses
  have hcross : ∀ (P : Finset (Sym2 (Fin n)) → Prop), InsideDetermined S P → ∀ k : ℕ,
      weightMass v (fun T => P T ∧ (T ∩ Dout).card = k)
        = weightMass ν P * weightMass v (fun T => (T ∩ Dout).card = k) := by
    intro P hP k
    rw [hvz]
    refine weightMass_selected_cross ν N.partA N.partB z P _ (fun e f => ?_)
    exact polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass hb.avoidMass hP
      ((houtD k).and (outsideDetermined_pairCell hAcut hBcut e f))
  -- the parity split
  have hOr : weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      = weightMass v (fun T => Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
        + weightMass v (fun T => Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1) := by
    have hcongr : weightMass v (fun T => Odd (T ∩ cutEdges u).card)
        = weightMass v (fun T => (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
            ∨ (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) := by
      refine weightMass_congr_of_support fun T hT => ?_
      have hc := hle1 T hT
      have hsplitT := card_split_of_subcut huS T
      rw [← hDin, ← hDout] at hsplitT
      rw [hsplitT]
      have hcases : (T ∩ Dout).card = 0 ∨ (T ∩ Dout).card = 1 := by omega
      rcases hcases with h0 | h1
      · rw [h0]
        constructor
        · intro hodd
          exact Or.inl ⟨by simpa using hodd, rfl⟩
        · rintro (⟨hodd, -⟩ | ⟨-, hc1⟩)
          · simpa using hodd
          · exact absurd hc1 (by norm_num)
      · rw [h1]
        constructor
        · intro hodd
          refine Or.inr ⟨?_, rfl⟩
          rw [Nat.even_iff]
          rw [Nat.odd_iff] at hodd
          omega
        · rintro (⟨-, hc0⟩ | ⟨heven, -⟩)
          · exact absurd hc0 (by norm_num)
          · rw [Nat.odd_iff]
            rw [Nat.even_iff] at heven
            omega
    rw [hcongr]
    have hand : weightMass v (fun T => (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
        ∧ (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
            ∧ (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) = fun _ => False from ?_,
        weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      have h1 := h.1.2
      have h2 := h.2.2
      omega
    have := weightMass_or v (fun T => Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
      (fun T => Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)
    rw [hand, add_zero] at this
    exact this
  -- the two factors
  have hOdd := hcross (fun T => Odd (T ∩ Din).card) hinOdd 0
  have hEven := hcross (fun T => Even (T ∩ Din).card) hinEven 1
  have haEven : weightMass ν (fun T => Even (T ∩ Din).card) = 1 - a := by
    have hnot := weightMass_not ν (fun T => Odd (T ∩ Din).card)
    rw [hb.law.tot] at hnot
    rw [← hnot]
    exact weightMass_congr fun T => by rw [Nat.not_odd_iff_even]
  rw [hOdd, hEven, haEven] at hOr
  rw [← ha, ← hb0, ← hb1] at hOr
  -- the masses
  have hb0nn : 0 ≤ b0 := weightMass_nonneg hb.nonneg _
  have hb1nn : 0 ≤ b1 := weightMass_nonneg hb.nonneg _
  have hann : 0 ≤ a := weightMass_nonneg hb.law.nn _
  have ha1 : a ≤ 1 := by
    rw [← hb.law.tot]; exact weightMass_le_totalMass hb.law.nn _
  have hsum : b0 + b1 = M := by
    have hor := weightMass_or v (fun T => (T ∩ Dout).card = 0) (fun T => (T ∩ Dout).card = 1)
    have hand : weightMass v (fun T => (T ∩ Dout).card = 0 ∧ (T ∩ Dout).card = 1) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (T ∩ Dout).card = 0 ∧ (T ∩ Dout).card = 1) = fun _ => False from ?_, weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      have h1 := h.1
      have h2 := h.2
      omega
    have htrue : weightMass v (fun T => (T ∩ Dout).card = 0 ∨ (T ∩ Dout).card = 1) = M := by
      rw [hM, ← weightMass_true v]
      refine weightMass_congr_of_support fun T hT => ?_
      have := hle1 T hT
      exact ⟨fun _ => trivial, fun _ => by omega⟩
    rw [hand, add_zero, htrue] at hor
    exact hor.symm
  -- the zero-mass case
  have hMnn : 0 ≤ M := totalMass_nonneg hb.nonneg
  rcases eq_or_lt_of_le hMnn with hM0 | hMpos
  · have hb0z : b0 = 0 := by linarith
    have hb1z : b1 = 0 := by linarith
    rw [hOr, hb0z, hb1z, ← hM0]
    norm_num
  · -- the genuine case
    set β : ℝ := b1 / M with hβ
    have hβ0 : 0 ≤ β := div_nonneg hb1nn hMpos.le
    have hβ1 : β ≤ 1 := by
      rw [hβ, div_le_one hMpos]; linarith
    have hb1eq : b1 = β * M := by rw [hβ]; field_simp
    have hb0eq : b0 = M - β * M := by rw [← hb1eq]; linarith
    -- the inside mean is at most `2.2`
    have hEle : expCard ν Din ≤ 2.2 := by linarith
    have hup : β ≤ 1 / 2 →
        a ≤ (1 + Real.exp (-2 * ((expCard ν Din + β) - β - 1))) / 2 := by
      intro _
      have h := oddCount_le hb.law.st hb.law.rank hb.law.nn hb.law.tot Din hzero hEle
      have he : (expCard ν Din + β) - β - 1 = expCard ν Din - 1 := by ring
      rw [he]
      exact h
    have hlow : 1 / 2 < β → 2 - ((expCard ν Din + β) - β) ≤ a := by
      intro _
      have h := oddCount_ge hb.law.st hb.law.rank hb.law.nn hb.law.tot Din hzero
      have he : (expCard ν Din + β) - β = expCard ν Din := by ring
      rw [he]
      exact h
    have hkey := odd_split_le hβ0 hβ1 hd0
      (E := expCard ν Din + β) hmlo hmhi hup hlow
    have hring : a * (M - β * M) + (1 - a) * (β * M) = (a * (1 - 2 * β) + β) * M := by ring
    rw [hOr, hb0eq, hb1eq, hring]
    exact mul_le_mul_of_nonneg_right hkey hMpos.le

set_option maxHeartbeats 2000000 in
-- The parity expansion unfolds several conditioned laws and their count events.
/-- The symbolic even-parity bound for the selected law. -/
theorem corollary_5_11_even_core {μ : TreeDist n x} {εη : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ)
    (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 0.0005)
    (hmlo : 1 - d ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v)
    (hmhi : expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ≤ 1 + d) :
    weightMass v (fun T => Even (T ∩ D).card)
      ≤ max ((1 + Real.exp (2 * d - 2)) / 2) (1 / 2 + d) * totalMass v := by
  classical
  obtain ⟨z, hvz⟩ := hb.selected
  have hMpos : 0 < totalMass v := hb.total_pos
  set ν : Finset (Sym2 (Fin n)) → ℝ := polygonLaw μ S N.partC with hν
  set Din : Finset (Sym2 (Fin n)) := D ∩ internalEdges S with hDin
  set Dout : Finset (Sym2 (Fin n)) := D ∩ cutEdges S with hDout
  set M : ℝ := totalMass v with hM
  set α : ℝ := weightMass ν (fun T => Even (T ∩ Din).card) with hα
  set b0 : ℝ := weightMass v (fun T => (T ∩ Dout).card = 0) with hb0
  set b1 : ℝ := weightMass v (fun T => (T ∩ Dout).card = 1) with hb1
  -- determinacy
  have hDinsub : ∀ g ∈ Din, ∀ w ∈ g, w ∈ S := by
    intro g hg w hw
    exact (mem_internalEdges.mp (Finset.mem_inter.mp hg).2).2 w hw
  have hDoutsub : Dout ⊆ cutEdges S := fun g hg => (Finset.mem_inter.mp hg).2
  have hinOdd : InsideDetermined S (fun T => Odd (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Odd X.card)
  have hinEven : InsideDetermined S (fun T => Even (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Even X.card)
  have houtD : ∀ k : ℕ, OutsideDetermined S (fun T => (T ∩ Dout).card = k) := fun k =>
    outsideDetermined_inter (fun g hg => not_forall_mem_of_mem_cutEdges (hDoutsub hg))
      (fun X => X.card = k)
  have hAcut : N.partA ⊆ cutEdges S := N.partA_subset_cutEdges hroot
  have hBcut : N.partB ⊆ cutEdges S := N.partB_subset_cutEdges hroot
  -- the cross-independence hypotheses
  have hcross : ∀ (P : Finset (Sym2 (Fin n)) → Prop), InsideDetermined S P → ∀ k : ℕ,
      weightMass v (fun T => P T ∧ (T ∩ Dout).card = k)
        = weightMass ν P * weightMass v (fun T => (T ∩ Dout).card = k) := by
    intro P hP k
    rw [hvz]
    refine weightMass_selected_cross ν N.partA N.partB z P _ (fun e f => ?_)
    exact polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass hb.avoidMass hP
      ((houtD k).and (outsideDetermined_pairCell hAcut hBcut e f))
  -- the parity split, with the parities swapped relative to Corollary 5.10
  have hOr : weightMass v (fun T => Even (T ∩ D).card)
      = weightMass v (fun T => Even (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
        + weightMass v (fun T => Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 1) := by
    have hcongr : weightMass v (fun T => Even (T ∩ D).card)
        = weightMass v (fun T => (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
            ∨ (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) := by
      refine weightMass_congr_of_support fun T hT => ?_
      have hc := hone T hT
      have hsplitT := card_split_of_subset hD T
      rw [← hDin, ← hDout] at hsplitT
      rw [hsplitT]
      have hcases : (T ∩ Dout).card = 0 ∨ (T ∩ Dout).card = 1 := by omega
      rcases hcases with h0 | h1
      · rw [h0]
        constructor
        · intro heven
          exact Or.inl ⟨by simpa using heven, rfl⟩
        · rintro (⟨heven, -⟩ | ⟨-, hc1⟩)
          · simpa using heven
          · exact absurd hc1 (by norm_num)
      · rw [h1]
        constructor
        · intro heven
          refine Or.inr ⟨?_, rfl⟩
          rw [Nat.odd_iff]
          rw [Nat.even_iff] at heven
          omega
        · rintro (⟨-, hc0⟩ | ⟨hodd, -⟩)
          · exact absurd hc0 (by norm_num)
          · rw [Nat.even_iff]
            rw [Nat.odd_iff] at hodd
            omega
    rw [hcongr]
    have hand : weightMass v (fun T => (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
        ∧ (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
            ∧ (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) = fun _ => False from ?_,
        weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      have h1 := h.1.2
      have h2 := h.2.2
      omega
    have := weightMass_or v (fun T => Even (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
      (fun T => Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 1)
    rw [hand, add_zero] at this
    exact this
  -- the two factors
  have hEven := hcross (fun T => Even (T ∩ Din).card) hinEven 0
  have hOdd := hcross (fun T => Odd (T ∩ Din).card) hinOdd 1
  have haOdd : weightMass ν (fun T => Odd (T ∩ Din).card) = 1 - α := by
    have hnot := weightMass_not ν (fun T => Even (T ∩ Din).card)
    rw [hb.law.tot] at hnot
    rw [← hnot]
    exact weightMass_congr fun T => by rw [Nat.not_even_iff_odd]
  rw [hEven, hOdd, haOdd] at hOr
  rw [← hα, ← hb0, ← hb1] at hOr
  -- the masses
  have hb0nn : 0 ≤ b0 := weightMass_nonneg hb.nonneg _
  have hb1nn : 0 ≤ b1 := weightMass_nonneg hb.nonneg _
  have hαnn : 0 ≤ α := weightMass_nonneg hb.law.nn _
  have hsum : b0 + b1 = M := by
    have hor := weightMass_or v (fun T => (T ∩ Dout).card = 0) (fun T => (T ∩ Dout).card = 1)
    have hand : weightMass v (fun T => (T ∩ Dout).card = 0 ∧ (T ∩ Dout).card = 1) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (T ∩ Dout).card = 0 ∧ (T ∩ Dout).card = 1) = fun _ => False from ?_, weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      have h1 := h.1
      have h2 := h.2
      omega
    have htrue : weightMass v (fun T => (T ∩ Dout).card = 0 ∨ (T ∩ Dout).card = 1) = M := by
      rw [hM, ← weightMass_true v]
      refine weightMass_congr_of_support fun T hT => ?_
      have := hone T hT
      exact ⟨fun _ => trivial, fun _ => by omega⟩
    rw [hand, add_zero, htrue] at hor
    exact hor.symm
  -- the normalized crossing probability
  set β : ℝ := b1 / M with hβ
  have hβ0 : 0 ≤ β := div_nonneg hb1nn hMpos.le
  have hβ1 : β ≤ 1 := by
    rw [hβ, div_le_one hMpos]; linarith
  have hb1eq : b1 = β * M := by rw [hβ]; field_simp
  have hb0eq : b0 = M - β * M := by rw [← hb1eq]; linarith
  -- the two analytic branches
  have hEle : expCard ν Din ≤ 1.2 := by linarith
  have hup : β ≤ 1 / 2 → α ≤ (1 + Real.exp (-2 * expCard ν Din)) / 2 := by
    intro _
    exact evenCount_le hb.law.st hb.law.rank hb.law.nn hb.law.tot Din hEle
  have hlow : 1 / 2 < β → 1 - expCard ν Din ≤ α := by
    intro _
    -- both facts are ascribed at `ν`, so `linarith` sees a single atom for each
    have h0 : totalMass ν - expCard ν Din ≤ weightMass ν (fun T => (T ∩ Din).card = 0) :=
      le_weightMass_avoid hb.law.nn Din
    have htot : totalMass ν = 1 := hb.law.tot
    have hmono : weightMass ν (fun T => (T ∩ Din).card = 0) ≤ α := by
      rw [hα]
      exact weightMass_mono hb.law.nn fun T hT => by rw [hT]; exact ⟨0, rfl⟩
    linarith
  have hμ1 : 1 - d - β ≤ expCard ν Din := by linarith
  have hμ2 : expCard ν Din ≤ 1 + d - β := by linarith
  have hkey := even_split_le hβ0 hβ1 hd0 hμ1 hμ2 hup hlow
  have hring : α * (M - β * M) + (1 - α) * (β * M) = (α * (1 - 2 * β) + β) * M := by ring
  rw [hOr, hb0eq, hb1eq, hring]
  exact mul_le_mul_of_nonneg_right hkey hMpos.le

end TSPGap.PolygonSelection

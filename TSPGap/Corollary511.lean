/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Corollary510

/-!
# KKO21 Corollary 5.11

`P[u not left happy | E_S] ≤ 0.56797` for a polygon cut `u` strictly inside a
polygon cut `S`, at the max-flow selection of `S`.

Being left-happy for `u`'s own near-cycle `K` means `A_u` is met an odd number
of times **and** `C_u` is not met at all (`NearCycle.LeftHappy`), so the union
bound splits the failure into two pieces:

* the **even-parity** piece, `W_v[A_u odd fails] ≤ 0.56771 · M`.  This is the
  mirror of Corollary 5.10: `A_u ⊆ δ(u) ⊆ E(S) ∪ δ(S)` splits as
  `D_in ⊔ D_out`, Observation 4.32 with the max-flow support puts
  `|T ∩ D_out| ≤ 1` (`card_dout_le_one`, restricted along `A_u ⊆ δ(u)`), and
  on that support

  `A_u,T even  ⟺  (D_out = 0 ∧ X even) ∨ (D_out = 1 ∧ X odd)`

  for `X = |T ∩ D_in|`.  The inside parity is inside-determined and the
  crossing count outside-determined, so `weightMass_selected_cross` again
  turns the mass into `α·b₀ + (1 − α)·b₁ = (α(1 − 2β) + β)·M`.  ⚠️ The mean is
  near **`1`**, not `2`, so there is no sure coordinate to strip: the `β ≤ 1/2`
  branch is `evenCount_le` applied directly, and the `β > 1/2` branch is
  `le_weightMass_avoid` (`P[X = 0] ≥ 1 − E[X]`) followed by
  `P[X even] ≥ P[X = 0]`.  `even_split_le_num` is the resulting algebra.

* the **`C_u` avoidance** piece, `W_v[C_u met] ≤ 0.00026 · M`, which is Markov
  at level one (`weightMass_hit_le_expCard`) fed by `PolygonBase.expCard_split`
  — the division-free identity `E_v[D] = M · E_ν[D_in] + W_v[|T ∩ D_out| = 1]`
  that turns the mean transfer into a bound on the selected expected count.

Both pieces read their mean off the *same* generic transfer,
`mean_bounds_of_subset_part` at `D = K.partA` and `D = K.partC`, which is why
that lemma was stated for an arbitrary `D ⊆ δ(u)` rather than for `δ(u)`.  The
deviations are `ε_M + 5.5ε_η` for `A_u` (the extra `2ε_η` is `x(A_u) ≤ 1 + 2ε_η`
rather than exactly `1`) and `ε_M + 6.5ε_η` for `C_u` (the extra `3ε_η` is
`x(C_u) ≤ 3ε_η`); both sit inside the `0.00026` that `even_split_le_num` needs.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The count split at an arbitrary subset -/

/-- `|T ∩ D| = |T ∩ D_in| + |T ∩ D_out|` for any `D ⊆ E(S) ∪ δ(S)`; the
`δ(u)` case is `card_split_of_subcut`. -/
theorem card_split_of_subset {S : Finset (Fin n)} {D : Finset (Sym2 (Fin n))}
    (hD : D ⊆ internalEdges S ∪ cutEdges S) (T : Finset (Sym2 (Fin n))) :
    (T ∩ D).card
      = (T ∩ (D ∩ internalEdges S)).card + (T ∩ (D ∩ cutEdges S)).card := by
  classical
  have hd : Disjoint (T ∩ (D ∩ internalEdges S)) (T ∩ (D ∩ cutEdges S)) := by
    refine Finset.disjoint_left.mpr fun g h1 h2 => ?_
    exact Finset.disjoint_left.mp (disjoint_din_dout S D)
      (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
  have he : T ∩ D = (T ∩ (D ∩ internalEdges S)) ∪ (T ∩ (D ∩ cutEdges S)) := by
    rw [← Finset.inter_union_distrib_left, ← subset_eq_din_union_dout hD]
  rw [he, Finset.card_union_of_disjoint hd]

/-! ### The part of `δ(u) ∩ δ(S)` outside the chosen piece lies in `C` -/

/-- Whichever of `A`, `B` the crossing edges of `u` miss (Observation 4.32),
everything of `δ(u) ∩ δ(S)` outside the *other* one lies in `C`.  This is the
`hsel` hypothesis of `mean_bounds_of_subset_part`. -/
theorem sdiff_subset_partC {εη : ℝ} {S u : Finset (Fin n)} {N : NearCycle x εη}
    (hroot : N.root = Sᶜ) {Q R : Finset (Sym2 (Fin n))} (hQ : Disjoint (cutEdges u) Q)
    (hQR : (Q = N.partA ∧ R = N.partB) ∨ (Q = N.partB ∧ R = N.partA)) :
    (cutEdges u ∩ cutEdges S) \ R ⊆ N.partC := by
  classical
  have hpart : N.partA ∪ N.partB ∪ N.partC = cutEdges S := by
    rw [N.partA_union_partB_union_partC, hroot, cutEdges_compl]
  intro g hg
  obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
  obtain ⟨hgu, hgS⟩ := Finset.mem_inter.mp hg1
  rw [← hpart] at hgS
  rcases Finset.mem_union.mp hgS with hab | hc
  · rcases Finset.mem_union.mp hab with ha | hbb
    · rcases hQR with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
      · exact absurd ha (fun hc' => Finset.disjoint_left.mp hQ hgu hc')
      · exact absurd ha hg2
    · rcases hQR with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hbb hg2
      · exact absurd hbb (fun hc' => Finset.disjoint_left.mp hQ hgu hc')
  · exact hc

/-! ### Markov at level one, at the selection -/

/-- **The selected avoidance bound.**  `PolygonBase.expCard_split` computes the
selected expected count division-free; Markov at level one turns it into a
bound on the mass of trees meeting `D`. -/
theorem PolygonBase.weightMass_meets_le {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1)
    {c : ℝ}
    (hc : expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v ≤ c) :
    weightMass v (fun T => 1 ≤ (T ∩ D).card) ≤ c * totalMass v := by
  classical
  have hMpos : 0 < totalMass v :=
    not_le.mp fun hcon => by nlinarith [hb.mass, hb.cst_pos]
  have hMne : totalMass v ≠ 0 := ne_of_gt hMpos
  have hhit := weightMass_hit_le_expCard hb.nonneg D
  rw [hb.expCard_split hμ hroot hSne hD hone] at hhit
  have hmul := mul_le_mul_of_nonneg_right hc hMpos.le
  have hdiv : weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      * totalMass v = weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) :=
    div_mul_cancel₀ _ hMne
  have heq : (expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v) * totalMass v
      = totalMass v * expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
        + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) := by
    rw [add_mul, hdiv]
    ring
  rw [heq] at hmul
  linarith

/-! ### The even-parity core -/

set_option maxHeartbeats 2000000 in
-- the parity split unfolds several conditioned laws at once, as in 5.10's core
/-- **Corollary 5.11's even-parity core.**  On the support of the max-flow
selection, the even mass of a count `D ⊆ E(S) ∪ δ(S)` whose crossing part is
met at most once and whose mean is `1 ± d` is at most `0.56771 · M`. -/
theorem corollary_5_11_even_core {μ : TreeDist n x} {εη : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ)
    (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 0.00026)
    (hmlo : 1 - d ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v)
    (hmhi : expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ≤ 1 + d) :
    weightMass v (fun T => Even (T ∩ D).card) ≤ 0.56771 * totalMass v := by
  classical
  obtain ⟨z, hvz⟩ := hb.selected
  -- ⚠️ before the `set`s: `hb.mass` speaks of `totalMass v`, and `nlinarith`
  -- would not see it as the same atom as the abbreviation `M`
  have hMpos : 0 < totalMass v :=
    not_le.mp fun hcon => by nlinarith [hb.mass, hb.cst_pos]
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
  have hkey := even_split_le_num hβ0 hβ1 hd0 hd hμ1 hμ2 hup hlow
  have hring : α * (M - β * M) + (1 - α) * (β * M) = (α * (1 - 2 * β) + β) * M := by ring
  rw [hOr, hb0eq, hb1eq, hring]
  exact mul_le_mul_of_nonneg_right hkey hMpos.le


/-! ### The two failure modes, at a part of `u`'s polygon partition -/

set_option maxHeartbeats 1000000 in
-- two mean transfers and two `mean_bounds_of_subset_part` instances in one body
/-- **Corollary 5.11's shared body.**  At a part `P` of `u`'s polygon partition
with `x(P) ∈ 1 ± 2ε_η` — `A_u` or `B_u` — the two ways happiness can fail carry
mass at most `0.56797 · M`: `0.56771` for `P_T` even and `0.00026` for `C_u`
being met.  Both read their mean off `mean_bounds_of_subset_part`. -/
theorem corollary_5_11_part {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {K : NearCycle x εη} (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {P : Finset (Sym2 (Fin n))} (hPu : P ⊆ cutEdges u)
    (hxP1 : 1 - εη ≤ ∑ e ∈ P, x e) (hxP2 : (∑ e ∈ P, x e) ≤ 1 + 2 * εη) :
    weightMass v (fun T => Even (T ∩ P).card ∨ 1 ≤ (T ∩ K.partC).card)
      ≤ 0.56797 * totalMass v := by
  classical
  have hSne : S.Nonempty := (H.nearMin S hS).nonempty
  have huS : u ⊆ S := hlt.subset
  have hroot : N.root = Sᶜ := hN.1
  have hScut : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hAB := H.disjoint_partA_or_partB hS hu hlt hN
  -- the outer part of `S` is never met on the support
  have hC0 : ∀ T, v T ≠ 0 → (T ∩ N.partC).card = 0 := by
    intro T hT
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  -- the one-hot bound, at any `D ⊆ δ(u)`
  have hone : ∀ D : Finset (Sym2 (Fin n)), D ⊆ cutEdges u →
      ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1 := by
    intro D hDu T hT
    obtain ⟨hA, hB⟩ := hb.support T hT
    refine le_trans (Finset.card_le_card ?_) (card_dout_le_one hroot hAB hA hB (hC0 T hT))
    exact Finset.inter_subset_inter (Finset.Subset.refl T)
      (Finset.inter_subset_inter hDu (Finset.Subset.refl (cutEdges S)))
  -- the mean transfer, at any `D ⊆ δ(u)`
  have hmean : ∀ D : Finset (Sym2 (Fin n)), D ⊆ cutEdges u →
      (∑ e ∈ D, x e) - (0.00025 + 3.5 * εη)
          ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
            + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
        ∧ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
            + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
          ≤ (∑ e ∈ D, x e) + (0.00025 + 3.5 * εη) := by
    intro D hDu
    have hsub : (D ∩ cutEdges S) ⊆ (cutEdges u ∩ cutEdges S) :=
      Finset.inter_subset_inter hDu (Finset.Subset.refl (cutEdges S))
    rcases hAB with hDA | hDB
    · refine mean_bounds_of_subset_part hx hμ hb hroot hSne (H.avoids S hS) huS hεη hScut hDu
        N.partB_disjoint_partC hb.tvB (fun g hg => ?_) (hone D hDu)
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
      exact sdiff_subset_partC hroot hDA (Or.inl ⟨rfl, rfl⟩)
        (Finset.mem_sdiff.mpr ⟨hsub hg1, hg2⟩)
    · refine mean_bounds_of_subset_part hx hμ hb hroot hSne (H.avoids S hS) huS hεη hScut hDu
        N.partA_disjoint_partC hb.tvA (fun g hg => ?_) (hone D hDu)
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
      exact sdiff_subset_partC hroot hDB (Or.inr ⟨rfl, rfl⟩)
        (Finset.mem_sdiff.mpr ⟨hsub hg1, hg2⟩)
  -- the even-parity piece, at `P`
  have hCu : K.partC ⊆ cutEdges u := K.partC_subset_cutEdges hK.1
  have hPdom : P ⊆ internalEdges S ∪ cutEdges S :=
    hPu.trans (cutEdges_subset_internal_union_cut huS)
  have hCdom : K.partC ⊆ internalEdges S ∪ cutEdges S :=
    hCu.trans (cutEdges_subset_internal_union_cut huS)
  obtain ⟨hPlo, hPhi⟩ := hmean P hPu
  have hPeven : weightMass v (fun T => Even (T ∩ P).card) ≤ 0.56771 * totalMass v := by
    refine corollary_5_11_even_core hb hμ hroot hSne hPdom (hone P hPu)
      (d := 0.00025 + 5.5 * εη) (by linarith) (by linarith) ?_ ?_
    · linarith
    · linarith
  -- the `C_u` piece
  obtain ⟨-, hChi⟩ := hmean K.partC hCu
  have hxC : (∑ e ∈ K.partC, x e) ≤ 3 * εη := K.sum_partC_le
  have hCmet : weightMass v (fun T => 1 ≤ (T ∩ K.partC).card) ≤ 0.00026 * totalMass v :=
    hb.weightMass_meets_le hμ hroot hSne hCdom (hone K.partC hCu) (by linarith)
  -- the union bound
  have hor := weightMass_or v (fun T => Even (T ∩ P).card)
    (fun T => 1 ≤ (T ∩ K.partC).card)
  have hand : 0 ≤ weightMass v
      (fun T => Even (T ∩ P).card ∧ 1 ≤ (T ∩ K.partC).card) :=
    weightMass_nonneg hb.nonneg _
  linarith

/-! ### The wrapper -/

/-- **KKO21 Corollary 5.11.**  `P[u not left happy | E_S] ≤ 0.56797` for a
polygon cut `u` strictly inside a polygon cut `S`, presented by `K` and `N`. -/
theorem corollary_5_11 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {K : NearCycle x εη} (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) :
    weightMass v (fun T => ¬ K.LeftHappy T) ≤ 0.56797 * totalMass v := by
  classical
  refine le_trans (weightMass_mono hb.nonneg ?_)
    (corollary_5_11_part hx hμ H hS hu hlt hN hK hb hεη hεηcap
      (K.partA_subset_cutEdges hK.1) K.one_sub_le_sum_partA (K.sum_partA_le hx.nonneg))
  intro T hT
  by_cases hodd : Odd (K.partA ∩ T).card
  · refine Or.inr ?_
    -- `K.LeftHappy T` is the conjunction definitionally, so the anonymous
    -- constructor discharges it against `hT` without unfolding
    have hne : K.partC ∩ T ≠ ∅ := fun hc => hT ⟨hodd, hc⟩
    have hpos : 0 < (K.partC ∩ T).card :=
      Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hne)
    rw [Finset.inter_comm]
    omega
  · refine Or.inl ?_
    rw [Finset.inter_comm]
    exact Nat.not_odd_iff_even.mp hodd

/-- **KKO21 Corollary 5.11, the right-happy half.**  KKO's "and the same
follows for right happy": `B_u` for `A_u` throughout, with the same `C_u`
piece.  `tvA`/`tvB` are separate fields of `PolygonBase`, so the two halves
are not related by a symmetry of the selection; only the part of *`u`*'s
partition changes, and `corollary_5_11_part` is stated at that part. -/
theorem corollary_5_11_right {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {K : NearCycle x εη} (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) :
    weightMass v (fun T => ¬ K.RightHappy T) ≤ 0.56797 * totalMass v := by
  classical
  refine le_trans (weightMass_mono hb.nonneg ?_)
    (corollary_5_11_part hx hμ H hS hu hlt hN hK hb hεη hεηcap
      (K.partB_subset_cutEdges hK.1) K.one_sub_le_sum_partB (K.sum_partB_le hx.nonneg))
  intro T hT
  by_cases hodd : Odd (K.partB ∩ T).card
  · refine Or.inr ?_
    -- `K.RightHappy T` is the conjunction definitionally, so the anonymous
    -- constructor discharges it against `hT` without unfolding
    have hne : K.partC ∩ T ≠ ∅ := fun hc => hT ⟨hodd, hc⟩
    have hpos : 0 < (K.partC ∩ T).card :=
      Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hne)
    rw [Finset.inter_comm]
    omega
  · refine Or.inl ?_
    rw [Finset.inter_comm]
    exact Nat.not_odd_iff_even.mp hodd

end TSPGap

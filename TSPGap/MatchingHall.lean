/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MatchingDefs

/-!
# The Hall condition of KKO21's matching lemma

For every family `Q ⊆ A(S)` of atoms of a cut `S` with at least three atoms,

`∑_{u ∈ Q} demand(u) ≤ touchCap(Q)`

— the demand of `Q` is covered by the good ordered rows touching `Q`
(`hall_inequality`).  This is the min-cut side of KKO's Lemma 6.2:

* `Q ⊊ A(S)` is KKO's (30): the rows touching `Q` carry `x(δ→(Q))`
  (`touchCap_eq`, each unordered bundle once), the bad ones at most
  `j (1/2 + ε₂)` for `j` the number of bad-incident atoms of `Q`
  (`badCap_touch_le`, a union bound over the two orientations), and
  `x(δ→(Q)) ≥ |Q| − ε_η/2` (Lemma 6.3); on the demand side a bad-incident
  atom has demand at most `(1/2 + 9ε₂)(1 − ε_B)` and any atom at most
  `1 + ε_η` (Lemma 2.7).
* `Q = A(S)` is KKO's Claim 6.5, with `x(E→(S)) ≥ |A(S)| − 1 − ε_η/2`, the
  bad mass at most `j(1/2 + ε₂)/2` (every bad row is counted from its own
  first endpoint — no union bound), `∑_u demand(u) ≤ x(δ(S)) + [|A(S)| ≥ 4]
  |A(S)|/10`, and the cases `|A(S)| = 3` (no bad bundle, Lemma 6.4),
  `|A(S)| ≥ 5`, `|A(S)| = 4` with `j ≤ 2`, and `|A(S)| = 4` with `j = 4`
  (every atom bad-incident, hence fractional, hence `F_u = 1 − ε_B`).  The
  case `j = 3` is excluded by **parity**: the bad-incident atoms are matched
  by their unique bad partners (`badIncident_card_even`).

Parameters: `ε_F = 1/10`, `21ε₂ ≤ ε_B ≤ 1/100`, `2ε_η ≤ α ≤ 1`,
`ε₂ ≤ 0.0002`, `ε_η ≤ ε₂²`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Sums over ordered pairs of atoms -/

/-- Swapping the two indices of an off-diagonal double sum. -/
theorem sum_erase_comm {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ι → ℝ) :
    ∑ u ∈ s, ∑ u' ∈ s.erase u, f u u' = ∑ u' ∈ s, ∑ u ∈ s.erase u', f u u' := by
  have h : ∀ u ∈ s, ∑ u' ∈ s.erase u, f u u' = ∑ u' ∈ s, if u' ≠ u then f u u' else 0 := by
    intro u _
    rw [← Finset.sum_filter, Finset.filter_ne']
  have h' : ∀ u' ∈ s, ∑ u ∈ s.erase u', f u u' = ∑ u ∈ s, if u ≠ u' then f u u' else 0 := by
    intro u' _
    rw [← Finset.sum_filter, Finset.filter_ne']
  rw [Finset.sum_congr rfl h, Finset.sum_congr rfl h', Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun u _ => ?_
  by_cases hne : u = u'
  · subst hne; simp
  · rw [if_pos (Ne.symm hne), if_pos hne]

/-- Restricting the inner index to `Q ⊆ s`. -/
theorem sum_erase_filter_mem {ι : Type*} [DecidableEq ι] {s Q : Finset ι} (hQ : Q ⊆ s)
    (u : ι) (f : ι → ℝ) :
    ∑ u' ∈ s.erase u, (if u' ∈ Q then f u' else 0) = ∑ u' ∈ Q.erase u, f u' := by
  rw [← Finset.sum_filter]
  congr 1
  ext u'
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hQ h2⟩, h2⟩

namespace Hierarchy

variable {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη)

/-- **The ordered rows touching `Q` carry `x(δ→(Q))`**, each bundle once. -/
theorem sum_touch_pairSum {S : Finset (Fin n)} {Q : Finset (Finset (Fin n))}
    (hQ : Q ⊆ H.children S) :
    ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if u ∈ Q ∨ u' ∈ Q then pairSum x u u' / 2 else 0)
      = touchSum x S Q := by
  set ch := H.children S with hch
  -- inclusion–exclusion on the indicator
  have hsplit : ∀ u u' : Finset (Fin n),
      (if u ∈ Q ∨ u' ∈ Q then pairSum x u u' / 2 else 0)
        = (if u ∈ Q then pairSum x u u' / 2 else 0) + (if u' ∈ Q then pairSum x u u' / 2 else 0)
          - (if u ∈ Q then (if u' ∈ Q then pairSum x u u' / 2 else 0) else 0) := by
    intro u u'
    by_cases h1 : u ∈ Q <;> by_cases h2 : u' ∈ Q
    · simp only [if_pos h1, if_pos h2, if_pos (Or.inl h1 : u ∈ Q ∨ u' ∈ Q)]; ring
    · simp only [if_pos h1, if_neg h2, if_pos (Or.inl h1 : u ∈ Q ∨ u' ∈ Q)]; ring
    · simp only [if_neg h1, if_pos h2, if_pos (Or.inr h2 : u ∈ Q ∨ u' ∈ Q)]; ring
    · simp only [if_neg h1, if_neg h2, if_neg (not_or.mpr ⟨h1, h2⟩ : ¬ (u ∈ Q ∨ u' ∈ Q))]; ring
  have hsum : ∑ u ∈ ch, ∑ u' ∈ ch.erase u, (if u ∈ Q ∨ u' ∈ Q then pairSum x u u' / 2 else 0)
      = ∑ u ∈ ch, ∑ u' ∈ ch.erase u, (if u ∈ Q then pairSum x u u' / 2 else 0)
        + ∑ u ∈ ch, ∑ u' ∈ ch.erase u, (if u' ∈ Q then pairSum x u u' / 2 else 0)
        - ∑ u ∈ ch, ∑ u' ∈ ch.erase u,
            (if u ∈ Q then (if u' ∈ Q then pairSum x u u' / 2 else 0) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u' _ => hsplit u u'
  rw [hsum]
  -- the three pieces
  have e1 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u, (if u ∈ Q then pairSum x u u' / 2 else 0)
      = ∑ u ∈ Q, arrowSum x S u / 2 := by
    have : ∀ u ∈ ch, ∑ u' ∈ ch.erase u, (if u ∈ Q then pairSum x u u' / 2 else 0)
        = if u ∈ Q then ∑ u' ∈ ch.erase u, pairSum x u u' / 2 else 0 := by
      intro u _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [H.arrowSum_eq_sum (H.mem_children.mp (hQ hu)), Finset.sum_div]
    rfl
  have e2 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u, (if u' ∈ Q then pairSum x u u' / 2 else 0)
      = ∑ u ∈ Q, arrowSum x S u / 2 := by
    rw [sum_erase_comm]
    have : ∀ u' ∈ ch, ∑ u ∈ ch.erase u', (if u' ∈ Q then pairSum x u u' / 2 else 0)
        = if u' ∈ Q then ∑ u ∈ ch.erase u', pairSum x u' u / 2 else 0 := by
      intro u' _
      split_ifs
      · exact Finset.sum_congr rfl fun u _ => by rw [pairSum_comm]
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [H.arrowSum_eq_sum (H.mem_children.mp (hQ hu)), Finset.sum_div]
    rfl
  have e3 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u,
      (if u ∈ Q then (if u' ∈ Q then pairSum x u u' / 2 else 0) else 0)
      = internalPairSum x Q / 2 := by
    have : ∀ u ∈ ch, ∑ u' ∈ ch.erase u,
        (if u ∈ Q then (if u' ∈ Q then pairSum x u u' / 2 else 0) else 0)
        = if u ∈ Q then ∑ u' ∈ Q.erase u, pairSum x u u' / 2 else 0 := by
      intro u _
      split_ifs with h
      · exact sum_erase_filter_mem hQ u _
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ, internalPairSum, Finset.sum_div]
    exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_div]
  rw [e1, e2, e3]
  unfold touchSum
  rw [← Finset.sum_div]
  ring

/-! ### Bad rows -/

/-- At most one bad partner: the bad rows at `u` carry at most `1/2 + ε₂`,
and nothing unless `u` is bad-incident. -/
theorem sum_bad_pairSum_le {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) (hx : IsRestrictedLP e₀ x) {u : Finset (Fin n)}
    (hu : u ∈ H.children S) :
    ∑ u' ∈ (H.children S).erase u, (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0)
      ≤ if IsBadIncident H μ S ε₂ u then 1 / 2 + ε₂ else 0 := by
  by_cases hbi : IsBadIncident H μ S ε₂ u
  · rw [if_pos hbi]
    obtain ⟨w, hw, huw, hbad⟩ := hbi
    have hwmem : w ∈ (H.children S).erase u := Finset.mem_erase.mpr ⟨Ne.symm huw, hw⟩
    rw [Finset.sum_eq_single w]
    · rw [if_pos hbad]
      have hhalf := half_of_not_good hbad
      exact hhalf.le
    · intro u' hu' hne
      rw [if_neg]
      intro hbad'
      exact hne (D.bad_unique u hu u' (Finset.mem_erase.mp hu').2 w hw
        (Ne.symm (Finset.mem_erase.mp hu').1) huw hbad' hbad)
    · intro h; exact absurd hwmem h
  · rw [if_neg hbi]
    refine le_of_eq (Finset.sum_eq_zero fun u' hu' => ?_)
    rw [if_neg]
    intro hbad
    exact hbi ⟨u', (Finset.mem_erase.mp hu').2, Ne.symm (Finset.mem_erase.mp hu').1, hbad⟩

/-- The bad ordered rows touching `Q` carry at most `j (1/2 + ε₂)`, `j` the
number of bad-incident atoms of `Q` (union bound over the orientations). -/
theorem badCap_touch_le {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) (hx : IsRestrictedLP e₀ x) (hε₂ : 0 ≤ ε₂)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) :
    ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if (u ∈ Q ∨ u' ∈ Q) ∧ ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0)
      ≤ ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * (1 / 2 + ε₂) := by
  set ch := H.children S with hch
  have hps : ∀ u ∈ ch, ∀ u' ∈ ch.erase u, 0 ≤ pairSum x u u' := fun u hu u' hu' =>
    pairSum_nonneg_lp hx.nonneg (H.children_disjoint (H.mem_children.mp hu)
      (H.mem_children.mp (Finset.mem_erase.mp hu').2) (Ne.symm (Finset.mem_erase.mp hu').1))
  -- union bound on the indicator
  have hsplit : ∀ u ∈ ch, ∀ u' ∈ ch.erase u,
      (if (u ∈ Q ∨ u' ∈ Q) ∧ ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0)
        ≤ (if u ∈ Q then (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0) / 2 else 0)
          + (if u' ∈ Q then (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0) / 2
            else 0) := by
    intro u hu u' hu'
    have := hps u hu u' hu'
    by_cases h1 : u ∈ Q <;> by_cases h2 : u' ∈ Q <;> by_cases h3 : IsGoodBundle μ ε₂ u u' <;>
      simp [h1, h2, h3] <;> linarith
  refine le_trans (Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun u' hu' =>
    hsplit u hu u' hu') ?_
  simp_rw [Finset.sum_add_distrib]
  -- the first orientation
  have e1 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u,
      (if u ∈ Q then (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0) / 2 else 0)
      ≤ ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * (1 / 2 + ε₂) / 2 := by
    have : ∀ u ∈ ch, ∑ u' ∈ ch.erase u,
        (if u ∈ Q then (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0) / 2 else 0)
        = if u ∈ Q then (∑ u' ∈ ch.erase u,
            (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0)) / 2 else 0 := by
      intro u _
      split_ifs
      · rw [Finset.sum_div]
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ]
    calc ∑ u ∈ Q, (∑ u' ∈ ch.erase u,
          (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0)) / 2
        ≤ ∑ u ∈ Q, (if IsBadIncident H μ S ε₂ u then 1 / 2 + ε₂ else 0) / 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact div_le_div_of_nonneg_right (H.sum_bad_pairSum_le D hx (hQ hu)) (by norm_num)
      _ = ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * (1 / 2 + ε₂) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- the second orientation, by symmetry
  have e2 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u,
      (if u' ∈ Q then (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0) / 2 else 0)
      ≤ ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * (1 / 2 + ε₂) / 2 := by
    rw [sum_erase_comm]
    have : ∀ u' ∈ ch, ∑ u ∈ ch.erase u',
        (if u' ∈ Q then (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0) / 2 else 0)
        = if u' ∈ Q then (∑ u ∈ ch.erase u',
            (if ¬ IsGoodBundle μ ε₂ u' u then pairSum x u' u else 0)) / 2 else 0 := by
      intro u' _
      split_ifs
      · rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [pairSum_comm]
        by_cases hg : IsGoodBundle μ ε₂ u' u
        · rw [if_neg (not_not.mpr (isGoodBundle_comm.mp hg)), if_neg (not_not.mpr hg)]
        · rw [if_pos (fun h => hg (isGoodBundle_comm.mp h)), if_pos hg]
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ]
    calc ∑ u ∈ Q, (∑ u' ∈ ch.erase u,
          (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0)) / 2
        ≤ ∑ u ∈ Q, (if IsBadIncident H μ S ε₂ u then 1 / 2 + ε₂ else 0) / 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact div_le_div_of_nonneg_right (H.sum_bad_pairSum_le D hx (hQ hu)) (by norm_num)
      _ = ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * (1 / 2 + ε₂) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- **All bad rows** carry at most `j (1/2 + ε₂)/2`: each is counted from its
own first endpoint. -/
theorem badCap_all_le {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) (hx : IsRestrictedLP e₀ x) :
    ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0)
      ≤ (((H.children S).filter (IsBadIncident H μ S ε₂)).card : ℝ) * (1 / 2 + ε₂) / 2 := by
  calc ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0)
      = ∑ u ∈ H.children S, (∑ u' ∈ (H.children S).erase u,
        (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' else 0)) / 2 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun u' _ => by split_ifs <;> simp
    _ ≤ ∑ u ∈ H.children S, (if IsBadIncident H μ S ε₂ u then 1 / 2 + ε₂ else 0) / 2 := by
        refine Finset.sum_le_sum fun u hu => ?_
        exact div_le_div_of_nonneg_right (H.sum_bad_pairSum_le D hx hu) (by norm_num)
    _ = _ := by
        rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The capacity of the rows touching `Q` is `(1 + α)` times the touching mass
minus the bad touching mass. -/
theorem touchCap_eq {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ α : ℝ}
    (Q : Finset (Finset (Fin n))) :
    touchCap μ ε₂ α (H.children S) Q
      = (1 + α) * (∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
          (if u ∈ Q ∨ u' ∈ Q then pairSum x u u' / 2 else 0)
        - ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
          (if (u ∈ Q ∨ u' ∈ Q) ∧ ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0)) := by
  unfold touchCap
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u' _ => ?_
  unfold rowCap
  by_cases h1 : u ∈ Q ∨ u' ∈ Q <;> by_cases h2 : IsGoodBundle μ ε₂ u u' <;> simp [h1, h2] <;> ring

/-! ### Parity of the bad-incident atoms -/

/-- **The bad-incident atoms are matched by their bad partners**, so there
are evenly many. -/
theorem badIncident_card_even {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) :
    Even ((H.children S).filter (IsBadIncident H μ S ε₂)).card := by
  set B := (H.children S).filter (IsBadIncident H μ S ε₂) with hB
  -- the partner map
  have hpart : ∀ u ∈ B, ∃ w ∈ H.children S, u ≠ w ∧ ¬ IsGoodBundle μ ε₂ u w :=
    fun u hu => (Finset.mem_filter.mp hu).2
  choose! g hg using hpart
  have hgB : ∀ u ∈ B, g u ∈ B := by
    intro u hu
    obtain ⟨hw, huw, hbad⟩ := hg u hu
    refine Finset.mem_filter.mpr ⟨hw, u, (Finset.mem_filter.mp hu).1, Ne.symm huw, ?_⟩
    exact fun h => hbad (isGoodBundle_comm.mp h)
  have hgg : ∀ u ∈ B, g (g u) = u := by
    intro u hu
    obtain ⟨hw, huw, hbad⟩ := hg u hu
    obtain ⟨hw', hww', hbad'⟩ := hg (g u) (hgB u hu)
    -- `g (g u)` and `u` are both bad partners of `g u`
    exact D.bad_unique (g u) hw (g (g u)) hw' u (Finset.mem_filter.mp hu).1 hww' (Ne.symm huw)
      hbad' (fun h => hbad (isGoodBundle_comm.mp h))
  have hne : ∀ u ∈ B, g u ≠ u := fun u hu => Ne.symm (hg u hu).2.1
  -- the sum of `1` over `B` in `ZMod 2` vanishes
  have hsum : ∑ u ∈ B, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun u _ => g u) (fun u _ => ?_) (fun u hu _ => hne u hu)
      (fun u hu => hgB u hu) (fun u hu => hgg u hu)
    decide
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have h2 : (2 : ℕ) ∣ B.card := (ZMod.natCast_eq_zero_iff B.card 2).mp hsum
  exact even_iff_two_dvd.mpr h2

/-! ### Demand bounds -/

/-- Every atom's demand is at most `1 + ε_η` (Lemma 2.7), and a bad-incident
atom's at most `(1/2 + 9ε₂)(1 − ε_B)`. -/
theorem demand_le {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ εB : ℝ}
    (D : MatchingInputs H μ S ε₂) (hx : IsRestrictedLP e₀ x) (hS : S ∈ H.cuts)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεB0 : 0 ≤ εB) (hεB : εB ≤ 1 / 100)
    {u : Finset (Fin n)} (hu : u ∈ H.children S) (k : ℕ) :
    demand x S εB k u ≤ 1 + εη
    ∧ (IsBadIncident H μ S ε₂ u → demand x S εB k u ≤ (1 / 2 + 9 * ε₂) * (1 - εB)) := by
  have hu_c := H.mem_children.mp hu
  have hup0 := upSum_nonneg hx.nonneg S u
  have hup1 : upSum x S u ≤ 1 + εη :=
    upSum_le_one_add hx (H.avoids S hS) hu_c.2.2.1 (H.child_nonempty hu_c) (H.nearMin S hS).cut_le
      (H.child_nearMin hu_c).cut_le
  constructor
  · unfold demand fFactor zFactor
    split_ifs with h1 h2 h2 <;> nlinarith [h2]
  · intro hbi
    have hbad := D.upSum_le_of_badIncident hu hbi
    unfold demand fFactor zFactor
    split_ifs with h1 h2 h2
    · nlinarith [h2.2]
    · nlinarith
    · nlinarith [h2.2]
    · -- not fractional: then `x(δ↑(u)) < 1/10`
      unfold IsFractional at h1
      have hlt : upSum x S u < 1 / 10 := by
        by_contra hc
        push_neg at hc
        exact h1 ⟨hc, by linarith⟩
      nlinarith

/-- The demand of a family: bad-incident atoms at `(1/2 + 9ε₂)(1 − ε_B)`, the
rest at `1 + ε_η`. -/
theorem sum_demand_le {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ εB : ℝ}
    (D : MatchingInputs H μ S ε₂) (hx : IsRestrictedLP e₀ x) (hS : S ∈ H.cuts)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεB0 : 0 ≤ εB) (hεB : εB ≤ 1 / 100)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) (k : ℕ) :
    ∑ u ∈ Q, demand x S εB k u
      ≤ ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * ((1 / 2 + 9 * ε₂) * (1 - εB))
        + ((Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u)).card : ℝ) * (1 + εη) := by
  rw [← Finset.sum_filter_add_sum_filter_not Q (IsBadIncident H μ S ε₂)]
  have h1 : ∑ u ∈ Q.filter (IsBadIncident H μ S ε₂), demand x S εB k u
      ≤ ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) * ((1 / 2 + 9 * ε₂) * (1 - εB)) := by
    have := Finset.sum_le_card_nsmul (Q.filter (IsBadIncident H μ S ε₂))
      (fun u => demand x S εB k u) ((1 / 2 + 9 * ε₂) * (1 - εB)) fun u hu =>
        (H.demand_le D hx hS hεη hε₂ hε₂cap hεB0 hεB (hQ (Finset.mem_filter.mp hu).1) k).2
          (Finset.mem_filter.mp hu).2
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ u ∈ Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u), demand x S εB k u
      ≤ ((Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u)).card : ℝ) * (1 + εη) := by
    have := Finset.sum_le_card_nsmul (Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u))
      (fun u => demand x S εB k u) (1 + εη) fun u hu =>
        (H.demand_le D hx hS hεη hε₂ hε₂cap hεB0 hεB (hQ (Finset.mem_filter.mp hu).1) k).1
    rwa [nsmul_eq_mul] at this
  linarith

/-- `∑_u x(δ↑(u)) = x(δ(S))` over the atoms. -/
theorem sum_upSum_children (x : Sym2 (Fin n) → ℝ) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hne : (H.children S).Nonempty) : ∑ u ∈ H.children S, upSum x S u = cutSum x S := by
  have hup := sum_upSum_eq x (H.children S) (fun a ha => H.children_subset ha)
    (H.children_pairwiseDisjoint S)
  rw [H.biUnion_children_eq hS hne] at hup
  rw [← hup]
  unfold upSum upEdges cutSum
  rw [Finset.inter_self]

/-! ### The Hall inequality -/

set_option maxHeartbeats 2000000 in
/-- **The Hall condition** (KKO (30) and Claim 6.5): for every atom family
`Q` of a cut with at least three atoms, the demand of `Q` is at most the
capacity of the good ordered rows touching `Q`. -/
theorem hall_inequality (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) {ε₂ εB α : ℝ} (D : MatchingInputs H μ S ε₂)
    (h3 : 3 ≤ (H.children S).card)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hα1 : 2 * εη ≤ α) (hα2 : α ≤ 1) (hεB1 : 21 * ε₂ ≤ εB) (hεB2 : εB ≤ 1 / 100)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) :
    ∑ u ∈ Q, demand x S εB (H.children S).card u
      ≤ touchCap μ ε₂ α (H.children S) Q := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hεB0 : 0 ≤ εB := by linarith
  have hα0 : 0 ≤ α := by linarith
  have hjQ : (Q.filter (IsBadIncident H μ S ε₂)).card ≤ Q.card := Finset.card_filter_le _ _
  have hcards : (Q.filter (IsBadIncident H μ S ε₂)).card
      + (Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u)).card = Q.card :=
    Finset.card_filter_add_card_filter_not _
  have hdem := H.sum_demand_le D hx hS hεη hε₂ hε₂cap hεB0 hεB2 hQ (H.children S).card
  have hcap := H.touchCap_eq (μ := μ) (S := S) (ε₂ := ε₂) (α := α) Q
  rw [H.sum_touch_pairSum hQ] at hcap
  have hbad := H.badCap_touch_le D hx hε₂ hQ
  have hjR : ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) ≤ Q.card := by exact_mod_cast hjQ
  have hcR : ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ)
      + ((Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u)).card : ℝ) = Q.card := by
    exact_mod_cast hcards
  have hjnn : (0 : ℝ) ≤ (Q.filter (IsBadIncident H μ S ε₂)).card := Nat.cast_nonneg _
  rcases eq_or_ne Q (H.children S) with hQch | hQch
  · /- ### `Q = A(S)`: Claim 6.5 -/
    subst hQch
    have hne : (H.children S).Nonempty := Finset.card_pos.mp ((show (0 : ℕ) < 3 by norm_num).trans_le h3)
    have hsumup := H.sum_upSum_children x hS hne
    have hcS := (H.nearMin S hS).cut_le
    have hcS2 := H.two_le_cutSum hx hS
    have htop := H.topSum_ge hx hS hne
    have hbadall := H.badCap_all_le D hx
    -- the all-touching bad mass is the bad mass
    have hbadeq : ∑ u ∈ (H.children S), ∑ u' ∈ (H.children S).erase u,
        (if (u ∈ (H.children S) ∨ u' ∈ (H.children S)) ∧ ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0)
        = ∑ u ∈ (H.children S), ∑ u' ∈ (H.children S).erase u,
        (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0) := by
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' _ => ?_
      simp [hu]
    rw [hbadeq] at hcap
    -- the demand: at most `x(δ(S)) + [k ≥ 4] k/10`
    have hdemZ : ∑ u ∈ (H.children S), demand x S εB (H.children S).card u
        ≤ cutSum x S + (if 4 ≤ (H.children S).card then ((H.children S).card : ℝ) / 10 else 0) := by
      have hterm : ∀ u ∈ (H.children S), demand x S εB (H.children S).card u
          ≤ upSum x S u + (if 4 ≤ (H.children S).card then (1 : ℝ) / 10 else 0) := by
        intro u hu
        have hup0 := upSum_nonneg hx.nonneg S u
        have hF := fFactor_le_one (x := x) (S := S) hεB0 u
        have hFnn : 0 ≤ fFactor x S εB u := (fFactor_pos (by linarith) u).le
        have hZ1 := one_le_zFactor (x := x) S (H.children S).card u
        have hZ : upSum x S u * zFactor x S (H.children S).card u
            ≤ upSum x S u + (if 4 ≤ (H.children S).card then (1 : ℝ) / 10 else 0) := by
          unfold zFactor
          split_ifs with hz hk hk
          · linarith [hz.2]
          · exact absurd hz.1 hk
          · linarith
          · linarith
        unfold demand
        nlinarith [mul_le_mul_of_nonneg_right hF (mul_nonneg hup0 (by linarith : (0:ℝ) ≤ zFactor x S (H.children S).card u))]
      calc ∑ u ∈ (H.children S), demand x S εB (H.children S).card u
          ≤ ∑ u ∈ (H.children S), (upSum x S u + (if 4 ≤ (H.children S).card then (1 : ℝ) / 10 else 0)) :=
            Finset.sum_le_sum hterm
        _ = cutSum x S + (if 4 ≤ (H.children S).card then ((H.children S).card : ℝ) / 10 else 0) := by
            rw [Finset.sum_add_distrib, hsumup, Finset.sum_const, nsmul_eq_mul]
            split_ifs <;> simp <;> ring
    -- the touching mass is `x(E→(S))`
    have htouch : touchSum x S (H.children S) = H.topSum x S := rfl
    rw [htouch] at hcap
    have hjk : (((H.children S).filter (IsBadIncident H μ S ε₂)).card : ℝ) ≤ (H.children S).card := hjR
    have hk3 : (3 : ℝ) ≤ (H.children S).card := by exact_mod_cast h3
    rw [hcap]
    set j : ℝ := (((H.children S).filter (IsBadIncident H μ S ε₂)).card : ℝ) with hj
    set B := ∑ u ∈ (H.children S), ∑ u' ∈ (H.children S).erase u,
      (if ¬ IsGoodBundle μ ε₂ u u' then pairSum x u u' / 2 else 0) with hB
    have hBnn : 0 ≤ B := by
      rw [hB]
      refine Finset.sum_nonneg fun u hu => Finset.sum_nonneg fun u' hu' => ?_
      have hp : 0 ≤ pairSum x u u' / 2 :=
        div_nonneg (pairSum_nonneg_lp hx.nonneg (H.children_disjoint (H.mem_children.mp hu)
          (H.mem_children.mp (Finset.mem_erase.mp hu').2)
          (Ne.symm (Finset.mem_erase.mp hu').1))) (by norm_num)
      split_ifs <;> first | exact le_rfl | exact hp
    -- cases on `k = |A(S)|`
    rcases Nat.lt_or_ge (H.children S).card 4 with hk4 | hk4
    · -- `k = 3`: no bad bundle
      have hk3' : (H.children S).card = 3 := by omega
      have hj0 : ((H.children S).filter (IsBadIncident H μ S ε₂)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u hu ⟨u', hu', huu', hbad⟩
        exact hbad (D.isGoodBundle_of_card_three hx hS hk3' hε₂ hε₂cap hεηcap hu hu' huu')
      have hj0R : j = 0 := by rw [hj, hj0]; simp
      rw [hj0R] at hbadall
      simp only [zero_mul, zero_div] at hbadall
      rw [if_neg (not_le.mpr hk4)] at hdemZ
      have hkR : ((H.children S).card : ℝ) = 3 := by exact_mod_cast hk3'
      rw [hkR] at htop
      have hB0 : B = 0 := le_antisymm hbadall hBnn
      rw [hB0, sub_zero]
      have h1 : (2 - εη / 2) * (2 * εη) ≤ (2 - εη / 2) * α :=
        mul_le_mul_of_nonneg_left hα1 (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left htop (by linarith : (0 : ℝ) ≤ 1 + α)]
    · rw [if_pos hk4] at hdemZ
      have hk4R : (4 : ℝ) ≤ (H.children S).card := by exact_mod_cast hk4
      rcases Nat.lt_or_ge (H.children S).card 5 with hk5 | hk5
      · -- `k = 4`
        have hk4' : (H.children S).card = 4 := by omega
        have hkR : ((H.children S).card : ℝ) = 4 := by exact_mod_cast hk4'
        rw [hkR] at htop hdemZ
        have heven := H.badIncident_card_even D
        have hj4 : ((H.children S).filter (IsBadIncident H μ S ε₂)).card ≤ 4 := by rw [← hk4']; exact hjQ
        rcases Nat.lt_or_ge ((H.children S).filter (IsBadIncident H μ S ε₂)).card 3 with hjlt | hjge
        · -- at most one bad bundle
          have hjR2 : j ≤ 2 := by rw [hj]; exact_mod_cast (by omega : ((H.children S).filter (IsBadIncident H μ S ε₂)).card ≤ 2)
          have hBle : B ≤ 1 / 2 + ε₂ := by nlinarith
          have hbr : 0 ≤ H.topSum x S - B := by linarith
          nlinarith [mul_nonneg hα0 hbr]
        · -- `j = 4`: every atom is bad-incident, hence fractional
          have hj4' : ((H.children S).filter (IsBadIncident H μ S ε₂)).card = 4 := by
            rcases heven with ⟨m, hm⟩; omega
          have hall : ∀ u ∈ (H.children S), IsBadIncident H μ S ε₂ u := by
            intro u hu
            have : (H.children S).filter (IsBadIncident H μ S ε₂) = (H.children S) :=
              Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hj4', hk4'])
            rw [← this] at hu
            exact (Finset.mem_filter.mp hu).2
          have hup : ∀ u ∈ (H.children S), upSum x S u ≤ 1 / 2 + 9 * ε₂ :=
            fun u hu => D.upSum_le_of_badIncident hu (hall u hu)
          have hlow : ∀ u ∈ (H.children S), 1 / 10 < upSum x S u := by
            intro u hu
            by_contra hc
            push_neg at hc
            have hrest : ∑ u' ∈ (H.children S).erase u, upSum x S u' ≤ 3 * (1 / 2 + 9 * ε₂) := by
              have := Finset.sum_le_card_nsmul ((H.children S).erase u) (fun u' => upSum x S u')
                (1 / 2 + 9 * ε₂) fun u' hu' => hup u' (Finset.mem_erase.mp hu').2
              rw [nsmul_eq_mul, Finset.card_erase_of_mem hu, hk4'] at this
              norm_num at this
              linarith
            have hsplit := Finset.sum_erase_add (H.children S) (fun u' => upSum x S u') hu
            linarith
          have hdem' : ∑ u ∈ (H.children S), demand x S εB (H.children S).card u = (1 - εB) * cutSum x S := by
            rw [← hsumup, Finset.mul_sum]
            refine Finset.sum_congr rfl fun u hu => ?_
            unfold demand fFactor zFactor
            rw [if_pos ⟨(hlow u hu).le, by linarith [hup u hu]⟩,
              if_neg (fun h => absurd h.2 (not_le.mpr (hlow u hu)))]
            ring
          rw [hdem']
          have hjR4 : j = 4 := by rw [hj, hj4']; norm_num
          rw [hjR4] at hbadall
          have hbr : 0 ≤ H.topSum x S - B := by linarith
          nlinarith [mul_nonneg hα0 hbr]
      · -- `k ≥ 5`
        have hk5R : (5 : ℝ) ≤ (H.children S).card := by exact_mod_cast hk5
        have hBle : B ≤ ((H.children S).card : ℝ) * (1 / 2 + ε₂) / 2 :=
          le_trans hbadall (by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_right hjk (by linarith))
        have hkε : ((H.children S).card : ℝ) * ε₂ ≤ ((H.children S).card : ℝ) * 0.0002 :=
          mul_le_mul_of_nonneg_left hε₂cap (Nat.cast_nonneg _)
        have hbr : 0 ≤ H.topSum x S - B := by nlinarith
        nlinarith [mul_nonneg hα0 hbr]
  · /- ### `Q ⊊ A(S)`: KKO (30) -/
    rcases Q.eq_empty_or_nonempty with hQe | hQne
    · subst hQe
      simp only [Finset.sum_empty]
      unfold touchCap
      refine Finset.sum_nonneg fun u hu => Finset.sum_nonneg fun u' hu' => ?_
      split_ifs with h
      · exact rowCap_nonneg hx.nonneg μ hα0 (H.children_disjoint (H.mem_children.mp hu)
          (H.mem_children.mp (Finset.mem_erase.mp hu').2) (Ne.symm (Finset.mem_erase.mp hu').1))
      · exact le_rfl
    have htouch := H.touchSum_ge_card hx hS hQ hQch
    have hq1 : (1 : ℝ) ≤ Q.card := by exact_mod_cast Finset.card_pos.mpr hQne
    rw [hcap]
    set j : ℝ := ((Q.filter (IsBadIncident H μ S ε₂)).card : ℝ) with hj
    set q : ℝ := (Q.card : ℝ) with hq
    -- KKO's inequality: `(1 + α)(q − ε_η/2 − j(1/2 + ε₂)) ≥ j(1/2 + 9ε₂)(1 − ε_B) + (q − j)(1 + ε_η)`
    have key : j * ((1 / 2 + 9 * ε₂) * (1 - εB)) + (q - j) * (1 + εη)
        ≤ (1 + α) * (q - εη / 2 - j * (1 / 2 + ε₂)) := by
      set b : ℝ := 10 * ε₂ + α / 2 + α * ε₂ - εB / 2 - 9 * ε₂ * εB - εη with hb
      have hexp : (1 + α) * (q - εη / 2 - j * (1 / 2 + ε₂))
          - (j * ((1 / 2 + 9 * ε₂) * (1 - εB)) + (q - j) * (1 + εη))
          = q * (α - εη) - (1 + α) * εη / 2 - j * b := by rw [hb]; ring
      have hαε : α * ε₂ ≤ 0.0002 * α := by nlinarith
      have hεBε : 0 ≤ 9 * ε₂ * εB := by positivity
      rcases le_or_gt 0 b with hb0 | hb0
      · have h1 : j * b ≤ q * b := mul_le_mul_of_nonneg_right hjR hb0
        have hc : 0 ≤ α - εη - b := by rw [hb]; nlinarith
        have h2 : 1 * (α - εη - b) ≤ q * (α - εη - b) := mul_le_mul_of_nonneg_right hq1 hc
        nlinarith
      · have h1 : 0 ≤ j * (-b) := mul_nonneg hjnn (by linarith)
        have h2 : 1 * (α - εη) ≤ q * (α - εη) := mul_le_mul_of_nonneg_right hq1 (by linarith)
        nlinarith
    have hQj : ((Q.filter (fun u => ¬ IsBadIncident H μ S ε₂ u)).card : ℝ) = q - j := by
      rw [hq, hj]; linarith
    rw [hQj] at hdem
    have h1 := mul_le_mul_of_nonneg_left hbad (by linarith : (0 : ℝ) ≤ 1 + α)
    have h2 := mul_le_mul_of_nonneg_left htouch (by linarith : (0 : ℝ) ≤ 1 + α)
    linarith

end Hierarchy

end TSPGap

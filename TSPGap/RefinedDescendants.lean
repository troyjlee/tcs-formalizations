/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedDegreePartition
import TSPGap.BundleSetup
import TSPGap.OJoin

/-!
# Definition 5.18's descendant clause, on pieces

`RefinedDegreePartition.lean` gives Definition 5.18's *bounds* at every hierarchy
cut.  What §7 actually consumes (Claim 7.4, Lemma 7.3's Case 1) is the
**structural** clause: whenever a hierarchy cut `d ⊊ U` already carries almost
all of a side — `x(δ(d) ∩ δ(U)) ≥ 1 − ε₁` — one of `A`, `B` lies over
`δ(d) ∩ δ(U)` and the other misses `δ(d)` entirely.  In the simple-edge model
that is `DegreePartition.ControlsDescendants` (`HappyEvents.lean`), carried as a
hypothesis because it could not be constructed there.

This file starts its construction on pieces.  KKO build `A`, `B` by cases on the
inclusion-minimal qualifying descendants (KKO21 lines 3155-3170): none, one, or
two.  In the one- and two-qualifier cases a side is taken to be **exactly** the
pieces over a qualifier's outward edges — not seeded and then greedily grown,
since adding any piece outside `δ(a) ∩ δ(U)` breaks the clause at `d = a`.  For
that to be legitimate the seeded side must already have mass in
`[1 − ε₁, 1 + ε_η]`, and that is the **mass gate** proved here: the lower bound
is the qualifying condition, and the upper bound is KKO21 Lemma 2.7
(`pairSum_le_of_subset`) — `x(E(d, Uᶜ)) ≤ 1 + ε_η` for nested near-minimum cuts
— transferred to pieces by `sum_piecesOver`.

## Main results

* `EdgeRefinement.DegreePartitionOn.ControlsDescendants` — the clause on pieces.
* `EdgeRefinement.qualifyingPieces_weight_bounds` — the mass gate.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

/-- **Definition 5.18's descendant clause on pieces.**  For every hierarchy cut
`d ⊊ U` carrying almost all of a side, one of `A`, `B` lies over `δ(d) ∩ δ(U)`
and the other has no piece over `δ(d)`.  Both the contained side and the
avoided cut pull back through `piecesOver`; the antecedent stays in base-edge
form, which `sum_piecesOver` makes equivalent to the piece-weight form. -/
def DegreePartitionOn.ControlsDescendants {R : EdgeRefinement x D ε₁}
    {εη : ℝ} {U : Finset (Fin n)} (P : R.DegreePartitionOn εη U)
    {e₀ : RootEdge n} (H : Hierarchy x e₀ εη) : Prop :=
  ∀ d ∈ H.cuts, d ⊂ U → 1 - ε₁ ≤ ∑ e ∈ cutEdges d ∩ cutEdges U, x e →
    (P.A ⊆ R.piecesOver (cutEdges d ∩ cutEdges U) ∧
        Disjoint P.B (R.piecesOver (cutEdges d)))
      ∨ (P.B ⊆ R.piecesOver (cutEdges d ∩ cutEdges U) ∧
        Disjoint P.A (R.piecesOver (cutEdges d)))

variable (R : EdgeRefinement x D ε₁)

/-- The outward edges of a nested cut: `δ(d) ∩ δ(U) = E(d, Uᶜ)` when `d ⊆ U`. -/
theorem cutEdges_inter_cutEdges_of_subset {d U : Finset (Fin n)} (hdU : d ⊆ U) :
    cutEdges d ∩ cutEdges U = betweenEdges d Uᶜ := by
  rw [← cutEdges_compl U]
  exact cutEdges_inter_cutEdges (Disjoint.mono_left hdU disjoint_compl_right)

/-- **The mass gate.**  A qualifying descendant's pieces already carry weight in
`[1 − ε₁, 1 + ε_η]`: the lower bound is the qualifying condition itself, and the
upper bound is KKO21 Lemma 2.7, since for nested near-minimum cuts
`x(E(d, Uᶜ)) ≤ 1 + ε_η`.  So a side seeded with *all* of them cannot overshoot,
and the greedy remainder accounting of `exists_degreePartitionOn` applies to
the other side unchanged. -/
theorem qualifyingPieces_weight_bounds {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    {εη : ℝ} {d U : Finset (Fin n)} (hU0 : AvoidsRootEdge e₀ U)
    (hd : IsNearMinCut x εη d) (hU : IsNearMinCut x εη U) (hdU : d ⊂ U)
    (hq : 1 - ε₁ ≤ ∑ e ∈ cutEdges d ∩ cutEdges U, x e) :
    1 - ε₁ ≤ ∑ p ∈ R.piecesOver (cutEdges d ∩ cutEdges U), R.weight p ∧
      ∑ p ∈ R.piecesOver (cutEdges d ∩ cutEdges U), R.weight p ≤ 1 + εη := by
  classical
  have hsub : cutEdges d ∩ cutEdges U ⊆ edgeFinset n :=
    Finset.inter_subset_left.trans (cutEdges_subset_edgeFinset d)
  rw [R.sum_piecesOver hsub]
  refine ⟨hq, ?_⟩
  have hdisj : Disjoint d Uᶜ := Disjoint.mono_left hdU.subset disjoint_compl_right
  rw [cutEdges_inter_cutEdges_of_subset hdU.subset, sum_betweenEdges x hdisj]
  have hne : (U \ d).Nonempty := by
    obtain ⟨v, hvU, hvd⟩ := Finset.exists_of_ssubset hdU
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvU, hvd⟩⟩
  have := hx.pairSum_le_of_subset hd hU hdU.subset hne hU0
  linarith

/-! ### Qualifying descendants and their inclusion-minimal members -/

end EdgeRefinement

section Qualifiers

variable {e₀ : RootEdge n} {εη : ℝ}

/-- Membership in a cut's edge set, unpacked. -/
theorem mem_cutEdges_iff_pair {S : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ cutEdges S ↔ ∃ u ∈ S, ∃ v ∈ Sᶜ, e = s(u, v) := by
  simp [cutEdges]

/-- **A qualifying descendant** of `U`: a hierarchy cut strictly inside `U`
that already carries almost all of a side, `x(δ(d) ∩ δ(U)) ≥ 1 − ε₁`. -/
def IsQualifier (H : Hierarchy x e₀ εη) (ε₁ : ℝ) (U d : Finset (Fin n)) : Prop :=
  d ∈ H.cuts ∧ d ⊂ U ∧ 1 - ε₁ ≤ ∑ e ∈ cutEdges d ∩ cutEdges U, x e

/-- The qualifiers at `U`, as a finset of `H.cuts`. -/
noncomputable def qualifiers (H : Hierarchy x e₀ εη) (ε₁ : ℝ) (U : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  H.cuts.filter fun d => d ⊂ U ∧ 1 - ε₁ ≤ ∑ e ∈ cutEdges d ∩ cutEdges U, x e

theorem mem_qualifiers {H : Hierarchy x e₀ εη} {ε₁ : ℝ} {U d : Finset (Fin n)} :
    d ∈ qualifiers H ε₁ U ↔ IsQualifier H ε₁ U d := by
  simp [qualifiers, IsQualifier]

/-- An **inclusion-minimal** qualifier: the ones KKO's Definition 5.18 actually
selects. -/
def IsMinQualifier (H : Hierarchy x e₀ εη) (ε₁ : ℝ) (U d : Finset (Fin n)) : Prop :=
  IsQualifier H ε₁ U d ∧ ∀ d', IsQualifier H ε₁ U d' → d' ⊆ d → d' = d

/-- Every qualifier contains an inclusion-minimal one: take a qualifier inside
it of least cardinality. -/
theorem exists_minQualifier_subset {H : Hierarchy x e₀ εη} {ε₁ : ℝ} {U d : Finset (Fin n)}
    (hd : IsQualifier H ε₁ U d) : ∃ m, IsMinQualifier H ε₁ U m ∧ m ⊆ d := by
  classical
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image
    ((qualifiers H ε₁ U).filter fun d' => d' ⊆ d) Finset.card
    ⟨d, Finset.mem_filter.mpr ⟨mem_qualifiers.mpr hd, Finset.Subset.refl _⟩⟩
  obtain ⟨hmq, hmd⟩ := Finset.mem_filter.mp hm
  refine ⟨m, ⟨mem_qualifiers.mp hmq, fun d' hd' hd'm => ?_⟩, hmd⟩
  have hd'f : d' ∈ (qualifiers H ε₁ U).filter fun d' => d' ⊆ d :=
    Finset.mem_filter.mpr ⟨mem_qualifiers.mpr hd', hd'm.trans hmd⟩
  exact Finset.eq_of_subset_of_card_le hd'm (hmin d' hd'f)

/-- Distinct minimal qualifiers are disjoint: laminarity makes two hierarchy
cuts nested or disjoint, and nesting contradicts minimality. -/
theorem minQualifier_disjoint {H : Hierarchy x e₀ εη} {ε₁ : ℝ} {U a b : Finset (Fin n)}
    (ha : IsMinQualifier H ε₁ U a) (hb : IsMinQualifier H ε₁ U b) (hab : a ≠ b) :
    Disjoint a b := by
  rcases H.laminar a ha.1.1 b hb.1.1 with h | h | h
  · exact absurd (hb.2 a ha.1 h) hab
  · exact absurd (ha.2 b hb.1 h).symm hab
  · exact h

/-! ### Outward edges -/

/-- Outward edges are monotone in the inner set: `a ⊆ d ⊆ U` gives
`E(a, Uᶜ) ⊆ E(d, Uᶜ)`. -/
theorem betweenEdges_compl_mono {a d U : Finset (Fin n)} (had : a ⊆ d) :
    betweenEdges a Uᶜ ⊆ betweenEdges d Uᶜ := by
  intro e he
  rw [betweenEdges, Finset.mem_filter] at he ⊢
  obtain ⟨-, u, hu, v, hv, rfl⟩ := he
  exact ⟨Finset.mem_univ _, u, had hu, v, hv, rfl⟩

/-- Disjoint inner sets have disjoint outward edges. -/
theorem betweenEdges_compl_disjoint {a b U : Finset (Fin n)} (hab : Disjoint a b)
    (haU : a ⊆ U) :
    Disjoint (betweenEdges a Uᶜ) (betweenEdges b Uᶜ) := by
  rw [Finset.disjoint_left]
  intro e hea heb
  rw [betweenEdges, Finset.mem_filter] at hea heb
  obtain ⟨-, u, hu, v, hv, rfl⟩ := hea
  obtain ⟨-, u', hu', v', hv', h⟩ := heb
  rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Finset.disjoint_left.mp hab hu hu'
  · exact (Finset.mem_compl.mp hv') (haU hu)

/-- An edge of `δ(U)` that avoids `δ(a')` avoids `δ(d)` for every `d ⊆ a' ⊆ U`:
its `U`-endpoint would have to lie in `d ⊆ a'`, putting the edge in `δ(a')`. -/
theorem notMem_cutEdges_of_subset {d a' U : Finset (Fin n)} (hda : d ⊆ a') (haU : a' ⊆ U)
    {e : Sym2 (Fin n)} (heU : e ∈ cutEdges U) (hea : e ∉ cutEdges a') :
    e ∉ cutEdges d := by
  intro hed
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_cutEdges_iff_pair.mp heU
  obtain ⟨u', hu', v', hv', h⟩ := mem_cutEdges_iff_pair.mp hed
  apply hea
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact mem_cutEdges_iff_pair.mpr
      ⟨u, hda hu', v, Finset.mem_compl.mpr fun hv' => (Finset.mem_compl.mp hv) (haU hv'), rfl⟩
  · exact absurd (haU (hda hu')) (Finset.mem_compl.mp hv)

/-- An outward edge of `b` misses `δ(d)` when `b` and `d` are disjoint subsets
of `U`: neither endpoint lies in `d`. -/
theorem notMem_cutEdges_of_disjoint {b d U : Finset (Fin n)} (hbd : Disjoint b d) (hdU : d ⊆ U)
    {e : Sym2 (Fin n)} (heb : e ∈ betweenEdges b Uᶜ) : e ∉ cutEdges d := by
  intro hed
  rw [betweenEdges, Finset.mem_filter] at heb
  obtain ⟨-, u, hu, v, hv, rfl⟩ := heb
  obtain ⟨u', hu', v', hv', h⟩ := mem_cutEdges_iff_pair.mp hed
  rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact Finset.disjoint_left.mp hbd hu hu'
  · exact (Finset.mem_compl.mp hv) (hdU hu')

/-! ### What the parameter separation buys -/

/-- Outward mass of a nested cut, in the form the counting arguments use. -/
theorem outward_mass_bounds (hx : IsRestrictedLP e₀ x) {εη : ℝ} {d U : Finset (Fin n)}
    (hU0 : AvoidsRootEdge e₀ U)
    (hd : IsNearMinCut x εη d) (hU : IsNearMinCut x εη U) (hdU : d ⊂ U) :
    ∑ e ∈ betweenEdges d Uᶜ, x e ≤ 1 + εη := by
  have hdisj : Disjoint d Uᶜ := Disjoint.mono_left hdU.subset disjoint_compl_right
  rw [sum_betweenEdges x hdisj]
  have hne : (U \ d).Nonempty := by
    obtain ⟨v, hvU, hvd⟩ := Finset.exists_of_ssubset hdU
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvU, hvd⟩⟩
  have := hx.pairSum_le_of_subset hd hU hdU.subset hne hU0
  linarith

/-- The qualifying condition, in outward-edge form. -/
theorem qualifier_outward_ge {H : Hierarchy x e₀ εη} {ε₁ : ℝ} {U d : Finset (Fin n)}
    (hd : IsQualifier H ε₁ U d) : 1 - ε₁ ≤ ∑ e ∈ betweenEdges d Uᶜ, x e := by
  have := hd.2.2
  rwa [EdgeRefinement.cutEdges_inter_cutEdges_of_subset hd.2.1.subset] at this

/-- **A qualifier contains exactly one minimal qualifier.**  Two distinct ones
would be disjoint, so their outward masses — each at least `1 − ε₁` — would
add up inside `E(d, Uᶜ)`, which Lemma 2.7 caps at `1 + ε_η`; the separation
`2 + ε_η < 3(1 − ε₁)` rules that out. -/
theorem minQualifier_unique_of_subset (hx : IsRestrictedLP e₀ x) {H : Hierarchy x e₀ εη}
    {ε₁ : ℝ} (hε₁0 : 0 ≤ ε₁) (hsep : 2 + εη < 3 * (1 - ε₁))
    {U d a b : Finset (Fin n)} (hU : U ∈ H.cuts) (hd : IsQualifier H ε₁ U d)
    (ha : IsMinQualifier H ε₁ U a) (hb : IsMinQualifier H ε₁ U b)
    (had : a ⊆ d) (hbd : b ⊆ d) : a = b := by
  classical
  by_contra hab
  have hdisj := minQualifier_disjoint ha hb hab
  have hEdisj := betweenEdges_compl_disjoint (U := U) hdisj ha.1.2.1.subset
  have hsubA := betweenEdges_compl_mono (U := U) had
  have hsubB := betweenEdges_compl_mono (U := U) hbd
  have hunion : betweenEdges a Uᶜ ∪ betweenEdges b Uᶜ ⊆ betweenEdges d Uᶜ :=
    Finset.union_subset hsubA hsubB
  have hsum : ∑ e ∈ betweenEdges a Uᶜ, x e + ∑ e ∈ betweenEdges b Uᶜ, x e
      ≤ ∑ e ∈ betweenEdges d Uᶜ, x e := by
    rw [← Finset.sum_union hEdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hunion fun e _ _ => hx.nonneg e
  have hA := qualifier_outward_ge ha.1
  have hB := qualifier_outward_ge hb.1
  have hcap := outward_mass_bounds hx (H.avoids U hU) (H.nearMin d hd.1) (H.nearMin U hU) hd.2.1
  linarith

/-- **At most two minimal qualifiers.**  Three pairwise-distinct ones are
pairwise disjoint with disjoint outward edge sets inside `δ(U)`, so their
masses — each at least `1 − ε₁` — would exceed `x(δ(U)) ≤ 2 + ε_η`. -/
theorem minQualifier_not_three (hx : IsRestrictedLP e₀ x) {H : Hierarchy x e₀ εη}
    {ε₁ : ℝ} (hsep : 2 + εη < 3 * (1 - ε₁))
    {U a b c : Finset (Fin n)} (hU : U ∈ H.cuts)
    (ha : IsMinQualifier H ε₁ U a) (hb : IsMinQualifier H ε₁ U b) (hc : IsMinQualifier H ε₁ U c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  classical
  have hAB := betweenEdges_compl_disjoint (U := U) (minQualifier_disjoint ha hb hab) ha.1.2.1.subset
  have hAC := betweenEdges_compl_disjoint (U := U) (minQualifier_disjoint ha hc hac) ha.1.2.1.subset
  have hBC := betweenEdges_compl_disjoint (U := U) (minQualifier_disjoint hb hc hbc) hb.1.2.1.subset
  -- all three outward sets sit inside δ(U)
  have hin : ∀ {s : Finset (Fin n)}, s ⊆ U → betweenEdges s Uᶜ ⊆ cutEdges U := by
    intro s hs
    rw [← EdgeRefinement.cutEdges_inter_cutEdges_of_subset hs]
    exact Finset.inter_subset_right
  have hunion : (betweenEdges a Uᶜ ∪ betweenEdges b Uᶜ) ∪ betweenEdges c Uᶜ ⊆ cutEdges U :=
    Finset.union_subset (Finset.union_subset (hin ha.1.2.1.subset) (hin hb.1.2.1.subset))
      (hin hc.1.2.1.subset)
  have hABC : Disjoint (betweenEdges a Uᶜ ∪ betweenEdges b Uᶜ) (betweenEdges c Uᶜ) :=
    Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hsum : ∑ e ∈ betweenEdges a Uᶜ, x e + ∑ e ∈ betweenEdges b Uᶜ, x e
      + ∑ e ∈ betweenEdges c Uᶜ, x e ≤ cutSum x U := by
    rw [← Finset.sum_union hAB, ← Finset.sum_union hABC, cutSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hunion fun e _ _ => hx.nonneg e
  have hA := qualifier_outward_ge ha.1
  have hB := qualifier_outward_ge hb.1
  have hC := qualifier_outward_ge hc.1
  have hcap := (H.nearMin U hU).cut_le
  linarith

end Qualifiers

/-! ### The construction -/

namespace EdgeRefinement

variable {e₀ : RootEdge n} {εη : ℝ} (R : EdgeRefinement x D ε₁)

theorem piecesOver_mono {F G : Finset (Sym2 (Fin n))} (h : F ⊆ G) :
    R.piecesOver F ⊆ R.piecesOver G :=
  fun _ hp => R.mem_piecesOver.mpr (h (R.mem_piecesOver.mp hp))

theorem piecesOver_disjoint {F G : Finset (Sym2 (Fin n))} (h : Disjoint F G) :
    Disjoint (R.piecesOver F) (R.piecesOver G) :=
  Finset.disjoint_left.mpr fun _ hF hG =>
    Finset.disjoint_left.mp h (R.mem_piecesOver.mp hF) (R.mem_piecesOver.mp hG)

/-- **Assembling a partition from its two sides.**  Any two disjoint sets of
pieces over `δ(U)`, each of weight in `[1 − ε₁, 1 + ε_η]`, are the `A` and `B`
of a `DegreePartitionOn`: `C` is what is left, and its budget
`(2 + ε_η) − 2(1 − ε₁) = 2ε₁ + ε_η` is exactly what two lower bounds leave of
the near-minimum cut. -/
theorem mkPartition {U : Finset (Fin n)} (hU : IsNearMinCut x εη U)
    {A B : Finset R.Piece}
    (hAPU : A ⊆ R.piecesOver (cutEdges U)) (hBPU : B ⊆ R.piecesOver (cutEdges U))
    (hAB : Disjoint A B)
    (hA1 : 1 - ε₁ ≤ ∑ p ∈ A, R.weight p) (hA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hB1 : 1 - ε₁ ≤ ∑ p ∈ B, R.weight p) (hB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη) :
    ∃ P : R.DegreePartitionOn εη U, P.A = A ∧ P.B = B := by
  classical
  set PU := R.piecesOver (cutEdges U) with hPU
  have htot : ∑ p ∈ PU, R.weight p = cutSum x U :=
    R.sum_piecesOver (cutEdges_subset_edgeFinset U)
  have hBsub : B ⊆ PU \ A := fun p hp =>
    Finset.mem_sdiff.mpr ⟨hBPU hp, fun hpA => Finset.disjoint_left.mp hAB hpA hp⟩
  have hsplitA : ∑ p ∈ PU \ A, R.weight p = cutSum x U - ∑ p ∈ A, R.weight p := by
    have h := Finset.sum_sdiff (f := R.weight) hAPU; rw [htot] at h; linarith
  have hsplitB : ∑ p ∈ (PU \ A) \ B, R.weight p
      = (∑ p ∈ PU \ A, R.weight p) - ∑ p ∈ B, R.weight p := by
    have h := Finset.sum_sdiff (f := R.weight) hBsub; linarith
  refine ⟨{ A := A, B := B, C := (PU \ A) \ B, part := ?_, disjAB := hAB,
            disjAC := ?_, disjBC := ?_, xA1 := hA1, xA2 := hA2, xB1 := hB1, xB2 := hB2,
            xC := ?_ }, rfl, rfl⟩
  · apply Finset.Subset.antisymm
    · intro p hp
      by_cases hA : p ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hA)
      · by_cases hB : p ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hB)
        · exact Finset.mem_union_right _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hp, hA⟩, hB⟩)
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact hAPU h
        · exact hBPU h
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
  · exact Finset.disjoint_left.mpr fun p hA hC =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hC).1).2 hA
  · exact Finset.disjoint_left.mpr fun p hB hC => (Finset.mem_sdiff.mp hC).2 hB
  · rw [hsplitB, hsplitA]; have := hU.cut_le; linarith

/-- A qualifier's outward pieces lie over `δ(U)`. -/
theorem outwardPieces_subset {a U : Finset (Fin n)} (haU : a ⊆ U) :
    R.piecesOver (betweenEdges a Uᶜ) ⊆ R.piecesOver (cutEdges U) := by
  refine R.piecesOver_mono ?_
  rw [← cutEdges_inter_cutEdges_of_subset haU]
  exact Finset.inter_subset_right

/-- **Definition 5.18 with its descendant clause, on pieces.**  For every
hierarchy cut `U` whose edges the refinement splits, a partition exists that
controls its descendants.  KKO's construction, by cases on the inclusion-minimal
qualifying descendants:

* **none** — any partition will do; the clause is vacuous;
* **one, `a`** — `A` is *exactly* the pieces over `E(a, Uᶜ)` (the mass gate says
  that is already in range), and `B` is packed greedily inside the reservoir
  `δ(U) ∖ δ(a')`, `a'` the child of `U` containing `a`; every qualifier
  contains `a` and lies inside `a'`, so `A` sits over its outward edges and `B`
  misses its cut entirely;
* **two, `a` and `b`** — `A` and `B` are exactly the pieces over `E(a, Uᶜ)` and
  `E(b, Uᶜ)`; a qualifier contains exactly one of them and is disjoint from
  the other;
* **three** — impossible under the separation.

The separation `2 + ε_η < 3(1 − ε₁)` is what KKO's case split silently needs;
`ε_η ≤ ε₁` is what makes the reservoir in the one-qualifier case large enough. -/
theorem exists_degreePartitionOn_controls (hx : IsRestrictedLP e₀ x)
    (H : Hierarchy x e₀ εη) {U : Finset (Fin n)} (hU : U ∈ H.cuts)
    (hD : cutEdges U ⊆ D)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη) (hεη₁ : εη ≤ ε₁)
    (hsep : 2 + εη < 3 * (1 - ε₁)) :
    ∃ P : R.DegreePartitionOn εη U, P.ControlsDescendants H := by
  classical
  have hUnm := H.nearMin U hU
  have hU0 := H.avoids U hU
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hlow : 2 ≤ cutSum x U := H.two_le_cutSum hx hU
  set PU := R.piecesOver (cutEdges U) with hPU
  have hsmall : ∀ p ∈ PU, R.weight p ≤ ε₁ :=
    fun p hp => R.weight_le_of_mem (hD (R.mem_piecesOver.mp hp))
  have hwnn : ∀ p ∈ PU, 0 ≤ R.weight p := fun p _ => R.weight_nonneg hx0 p
  -- ── Case 0: no qualifier ────────────────────────────────────────────────
  by_cases h0 : ∃ d, IsQualifier H ε₁ U d
  swap
  · push Not at h0
    obtain ⟨P⟩ := R.exists_degreePartitionOn hx0 hlow hε₁0 hε₁1 hεη0
      hUnm.cut_le hD
    exact ⟨P, fun d hd hdU hq => absurd ⟨hd, hdU, hq⟩ (h0 d)⟩
  obtain ⟨d₀, hd₀⟩ := h0
  obtain ⟨a, ha, -⟩ := exists_minQualifier_subset hd₀
  -- `a`'s outward pieces, and their mass
  have hAmass := R.qualifyingPieces_weight_bounds hx hU0 (H.nearMin a ha.1.1) hUnm ha.1.2.1
    ha.1.2.2
  rw [cutEdges_inter_cutEdges_of_subset ha.1.2.1.subset] at hAmass
  have hAPU := R.outwardPieces_subset ha.1.2.1.subset
  -- ── Case 1: `a` is the only minimal qualifier ────────────────────────────
  by_cases h1 : ∀ m, IsMinQualifier H ε₁ U m → m = a
  · obtain ⟨a', ha'child, haa'⟩ := H.exists_child_superset ha.1.1 hU ha.1.2.1
    have ha'cuts : a' ∈ H.cuts := ha'child.1
    have ha'U : a' ⊂ U := ha'child.2.2.1
    -- the reservoir `δ(U) ∖ δ(a')` and its mass
    set S := R.piecesOver (cutEdges U \ cutEdges a') with hS
    have hSPU : S ⊆ PU := R.piecesOver_mono Finset.sdiff_subset
    have hSmass : 1 - εη ≤ ∑ p ∈ S, R.weight p := by
      rw [R.sum_piecesOver (Finset.sdiff_subset.trans (cutEdges_subset_edgeFinset U))]
      have heq : cutEdges U \ cutEdges a' = cutEdges U \ (cutEdges U ∩ cutEdges a') :=
        (Finset.sdiff_inter_self_left _ _).symm
      rw [heq]
      have hsd := Finset.sum_sdiff (f := x)
        (Finset.inter_subset_left : cutEdges U ∩ cutEdges a' ⊆ cutEdges U)
      have hcap : ∑ e ∈ cutEdges U ∩ cutEdges a', x e ≤ 1 + εη := by
        rw [Finset.inter_comm, cutEdges_inter_cutEdges_of_subset ha'U.subset]
        exact outward_mass_bounds hx hU0 (H.nearMin a' ha'cuts) hUnm ha'U
      have : ∑ e ∈ cutEdges U, x e = cutSum x U := rfl
      linarith
    -- pack `B` inside the reservoir
    obtain ⟨B, hBS, hB1, hB2⟩ :=
      exists_subset_sum_mem_Icc (w := R.weight) (δ := ε₁) hε₁0 S
        (fun p hp => hwnn p (hSPU hp)) (fun p hp => hsmall p (hSPU hp))
        (1 - ε₁) (by linarith) (by linarith)
    -- `a`'s outward edges lie in `δ(a')`, so `A` and the reservoir are disjoint
    have hAa' : betweenEdges a Uᶜ ⊆ cutEdges a' := by
      refine (betweenEdges_compl_mono haa').trans ?_
      rw [← cutEdges_inter_cutEdges_of_subset ha'U.subset]
      exact Finset.inter_subset_left
    have hAS : Disjoint (R.piecesOver (betweenEdges a Uᶜ)) S :=
      R.piecesOver_disjoint (Finset.disjoint_left.mpr fun e he he' =>
        (Finset.mem_sdiff.mp he').2 (hAa' he))
    obtain ⟨P, hPA, hPB⟩ := R.mkPartition hUnm hAPU (hBS.trans hSPU)
      (hAS.mono_right hBS) hAmass.1 hAmass.2 hB1 (by linarith)
    refine ⟨P, fun d hd hdU hq => ?_⟩
    have hdq : IsQualifier H ε₁ U d := ⟨hd, hdU, hq⟩
    obtain ⟨m, hm, hmd⟩ := exists_minQualifier_subset hdq
    rw [h1 m hm] at hmd
    -- every qualifier lies inside the child `a'`
    have hda' : d ⊆ a' := by
      rcases H.laminar d hd a' ha'cuts with h | h | h
      · exact h
      · by_cases heq : a' = d
        · exact heq ▸ Finset.Subset.refl _
        · exact absurd hdU (ha'child.2.2.2 d hd (Finset.ssubset_iff_subset_ne.mpr ⟨h, heq⟩))
      · exfalso
        obtain ⟨v, hv⟩ := (H.nearMin a ha.1.1).nonempty
        exact Finset.disjoint_left.mp h (hmd hv) (haa' hv)
    left
    refine ⟨?_, ?_⟩
    · rw [hPA, cutEdges_inter_cutEdges_of_subset hdU.subset]
      exact R.piecesOver_mono (betweenEdges_compl_mono hmd)
    · rw [hPB]
      refine Disjoint.mono_left hBS (R.piecesOver_disjoint (Finset.disjoint_left.mpr
        fun e he hed => ?_))
      exact notMem_cutEdges_of_subset hda' ha'U.subset (Finset.mem_sdiff.mp he).1
        (Finset.mem_sdiff.mp he).2 hed
  -- ── at least two minimal qualifiers ─────────────────────────────────────
  push Not at h1
  obtain ⟨b, hb, hba⟩ := h1
  by_cases h2 : ∀ m, IsMinQualifier H ε₁ U m → m = a ∨ m = b
  swap
  · -- ── three: impossible ──
    push Not at h2
    obtain ⟨c, hc, hca, hcb⟩ := h2
    exact (minQualifier_not_three hx hsep hU ha hb hc hba.symm hca.symm hcb.symm).elim
  -- ── Case 2: exactly `a` and `b` ─────────────────────────────────────────
  have hBmass := R.qualifyingPieces_weight_bounds hx hU0 (H.nearMin b hb.1.1) hUnm hb.1.2.1
    hb.1.2.2
  rw [cutEdges_inter_cutEdges_of_subset hb.1.2.1.subset] at hBmass
  have hBPU := R.outwardPieces_subset hb.1.2.1.subset
  have hab : Disjoint a b := minQualifier_disjoint ha hb hba.symm
  have hAB : Disjoint (R.piecesOver (betweenEdges a Uᶜ)) (R.piecesOver (betweenEdges b Uᶜ)) :=
    R.piecesOver_disjoint (betweenEdges_compl_disjoint hab ha.1.2.1.subset)
  obtain ⟨P, hPA, hPB⟩ := R.mkPartition hUnm hAPU hBPU hAB
    hAmass.1 hAmass.2 hBmass.1 hBmass.2
  refine ⟨P, fun d hd hdU hq => ?_⟩
  have hdq : IsQualifier H ε₁ U d := ⟨hd, hdU, hq⟩
  obtain ⟨m, hm, hmd⟩ := exists_minQualifier_subset hdq
  -- the *other* minimal qualifier is disjoint from `d`
  have hother : ∀ {p q : Finset (Fin n)}, IsMinQualifier H ε₁ U p → IsMinQualifier H ε₁ U q →
      p ≠ q → p ⊆ d → Disjoint q d := by
    intro p q hp hq hpq hpd
    rcases H.laminar q hq.1.1 d hd with h | h | h
    · exact absurd (minQualifier_unique_of_subset hx hε₁0 hsep hU hdq hp hq hpd h) hpq
    · exfalso
      obtain ⟨v, hv⟩ := (H.nearMin p hp.1.1).nonempty
      exact Finset.disjoint_left.mp (minQualifier_disjoint hp hq hpq) hv (h (hpd hv))
    · exact h
  rcases h2 m hm with hma | hmb
  · rw [hma] at hmd
    left
    refine ⟨?_, ?_⟩
    · rw [hPA, cutEdges_inter_cutEdges_of_subset hdU.subset]
      exact R.piecesOver_mono (betweenEdges_compl_mono hmd)
    · rw [hPB]
      exact R.piecesOver_disjoint (Finset.disjoint_left.mpr fun e he hed =>
        notMem_cutEdges_of_disjoint (hother ha hb hba.symm hmd) hdU.subset he hed)
  · rw [hmb] at hmd
    right
    refine ⟨?_, ?_⟩
    · rw [hPB, cutEdges_inter_cutEdges_of_subset hdU.subset]
      exact R.piecesOver_mono (betweenEdges_compl_mono hmd)
    · rw [hPA]
      exact R.piecesOver_disjoint (Finset.disjoint_left.mpr fun e he hed =>
        notMem_cutEdges_of_disjoint (hother hb ha hba hmd) hdU.subset he hed)

end EdgeRefinement

/-- **The headline, with the descendant clause.**  For every hierarchy, and
every `ε₁` and `ε_η` satisfying the displayed parameter conditions —
`0 < ε₁ ≤ 1`, `0 ≤ ε_η ≤ ε₁`, and the separation `2 + ε_η < 3(1 − ε₁)` — there
is a refinement on which Definition 5.18's partition exists at every cut *and*
controls that cut's descendants: the full input `lemma_7_3`'s `hctrl` asks for,
on pieces.  The conditions hold with wide margin at KKO's constants. -/
theorem exists_refinement_degreePartitions_controls {e₀ : RootEdge n} {εη : ℝ}
    (H : Hierarchy x e₀ εη)
    (hx : IsRestrictedLP e₀ x) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη)
    (hεη₁ : εη ≤ ε₁) (hsep : 2 + εη < 3 * (1 - ε₁)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) ε₁,
      ∀ U ∈ H.cuts, ∃ P : R.DegreePartitionOn εη U, P.ControlsDescendants H := by
  classical
  obtain ⟨R⟩ := exists_edgeRefinement x (H.cuts.biUnion cutEdges) hε₁
  exact ⟨R, fun U hU => R.exists_degreePartitionOn_controls hx H hU
    (Finset.subset_biUnion_of_mem cutEdges hU) hε₁.le hε₁1 hεη0 hεη₁ hsep⟩

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundlePolygonReduction
import TSPGap.RefinedPolygonTopCases

/-!
# Actual polygon cases with the full retained side mass

The wrong piece side and the residual degree part cover the complement of
the retained polygon side. Charging their union once avoids counting the
polygon C part a second time. The cases use the actual thinning event and
both wrong-side inequalities on the supplied piece partition.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}

namespace EdgeRefinement

open Classical in
/-- The complement of a retained polygon side is charged to the other piece side and C. -/
theorem sum_sdiff_le_of_piece_side {u : Finset (Fin n)} (hx : ∀ e, 0 ≤ x e)
    {X X' C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (X ∪ X') ∪ C)
    {Y E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u)
    (hX' : X' ⊆ R.piecesOver Y) {c : ℝ}
    (hc : ∑ q ∈ R.piecesOver E ∩ X, R.weight q ≤ c) :
    ∑ g ∈ E \ Y, x g ≤ c + ∑ q ∈ C, R.weight q := by
  have hwnn : ∀ q, 0 ≤ R.weight q := R.weight_nonneg hx
  rw [← R.sum_piecesOver (Finset.sdiff_subset.trans (hE.trans (cutEdges_subset_edgeFinset u)))]
  have hsub : R.piecesOver (E \ Y) ⊆ (R.piecesOver E ∩ X) ∪ C := by
    intro q hq
    have hqEY := Finset.mem_sdiff.mp (R.mem_piecesOver.mp hq)
    have hqE : q ∈ R.piecesOver E := R.mem_piecesOver.mpr hqEY.1
    have hqcut : q ∈ R.piecesOver (cutEdges u) := R.mem_piecesOver.mpr (hE hqEY.1)
    rw [hpart] at hqcut
    rcases Finset.mem_union.mp hqcut with hXX | hC
    · rcases Finset.mem_union.mp hXX with hX | hqX'
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hqE, hX⟩)
      · exact (hqEY.2 (R.mem_piecesOver.mp (hX' hqX'))).elim
    · exact Finset.mem_union_right _ hC
  calc ∑ q ∈ R.piecesOver (E \ Y), R.weight q
      ≤ ∑ q ∈ (R.piecesOver E ∩ X) ∪ C, R.weight q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hwnn q
    _ ≤ (∑ q ∈ R.piecesOver E ∩ X, R.weight q) + ∑ q ∈ C, R.weight q := by
      have hs := Finset.sum_union_inter (s₁ := R.piecesOver E ∩ X) (s₂ := C) (f := R.weight)
      have hn : 0 ≤ ∑ q ∈ (R.piecesOver E ∩ X) ∩ C, R.weight q :=
        Finset.sum_nonneg fun q _ => hwnn q
      linarith only [hs, hn]
    _ ≤ c + ∑ q ∈ C, R.weight q := by linarith only [hc]

open Classical in
/-- Both orientations retain the entire correct-side mass with a single degree-C loss. -/
theorem DegreePartitionOn.PolygonCompatible.sum_sdiff_side_le
    {u : Finset (Fin n)} {P : R.DegreePartitionOn eta u} {N : NearCycle x eta}
    (hcomp : P.PolygonCompatible N) (hx : ∀ e, 0 ≤ x e)
    {E F : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) (hF : F ⊆ cutEdges u)
    {c c' : ℝ} (hcB : ∑ q ∈ R.piecesOver E ∩ P.B, R.weight q ≤ c)
    (hcA : ∑ q ∈ R.piecesOver F ∩ P.A, R.weight q ≤ c') :
    ((∑ g ∈ E \ N.partA, x g ≤ c + (2 * eps + eta) ∧
        ∑ g ∈ F \ N.partB, x g ≤ c' + (2 * eps + eta)) ∨
      (∑ g ∈ E \ N.partB, x g ≤ c + (2 * eps + eta) ∧
        ∑ g ∈ F \ N.partA, x g ≤ c' + (2 * eps + eta))) := by
  have hC := P.xC
  rcases hcomp.1 with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · left
    constructor
    · have hh := sum_sdiff_le_of_piece_side hx (X := P.B) (X' := P.A) (C := P.C)
        (by rw [P.part, Finset.union_comm P.A P.B]) hE hA hcB
      linarith only [hh, hC]
    · have hh := sum_sdiff_le_of_piece_side hx (X := P.A) (X' := P.B) (C := P.C)
        P.part hF hB hcA
      linarith only [hh, hC]
  · right
    constructor
    · have hh := sum_sdiff_le_of_piece_side hx (X := P.B) (X' := P.A) (C := P.C)
        (by rw [P.part, Finset.union_comm P.A P.B]) hE hA hcB
      linarith only [hh, hC]
    · have hh := sum_sdiff_le_of_piece_side hx (X := P.A) (X' := P.B) (C := P.C)
        P.part hF hB hcA
      linarith only [hh, hC]

end EdgeRefinement


namespace BundleGoodnessPolicy
variable {G : BundleGoodnessPolicy} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {p : ℝ} {P : R.DegreePartitionsOn H}

open Classical in
/-- A nonzero thinning sits on the support of the lifted law. -/
theorem TopThinningsOn.liftProb_ne_zero_of_thin_ne_zero {Ŝ : Finset (Fin n)}
    (Θ : G.TopThinningsOn R H μ Ŝ p P) {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.thin u u' Ť ≠ 0) : R.liftProb μ Ť ≠ 0 := by
  intro h0
  apply h
  exact le_antisymm (h0 ▸ Θ.thin_le u u' Ť) (Θ.thin_nonneg u u' Ť)

open Classical in
/-- A tree carrying density at a good pair lies in the pair's event, and is a
transversal. -/
theorem TopThinningsOn.event_of_rho_ne_zero {Ŝ : Finset (Fin n)}
    (Θ : G.TopThinningsOn R H μ Ŝ p P) {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.rho u u' Ť ≠ 0) : Θ.event u u' Ť ∧ R.IsTransversal Ť := by
  have hthin := Θ.thin_ne_zero_of_rho_ne_zero h
  have hgp := Θ.goodPair_of_thin_ne_zero hthin
  exact ⟨(Θ.uniform u hgp.1 u' hgp.2.1 hgp.2.2.1 hgp.2.2.2).support Ť hthin,
    (R.liftProb_ne_zero μ (Θ.liftProb_ne_zero_of_thin_ne_zero hthin)).1⟩

open Classical in
/-- **The provenance of the top densities at the polygon cut `S`**, child of
the degree cut `Ŝ` carrying the thinnings `Θ`, against the near-cycle `N`
presenting `S`. -/
inductive PolygonTopCases {Ŝ : Finset (Fin n)} (Θ : G.TopThinningsOn R H μ Ŝ p P)
    (S : Finset (Fin n)) (N : NearCycle x eta) : Prop
  /-- Case 1: the bad half bundles at `S` carry mass `≥ 1/2 − G.halfWidth`. -/
  | bad (h : G.BadCase H μ Ŝ S)
  /-- Case 2: a set of siblings carrying mass `≥ 1/2 − G.halfWidth − ε_η` whose bundles,
  whenever reduced at `S`, make the polygon happy on the projection. -/
  | twoOneOne (Dset : Finset (Finset (Fin n))) (hsub : Dset ⊆ H.siblings Ŝ S)
      (hmass : 1 / 2 - G.halfWidth - eta ≤ ∑ u ∈ Dset, pairSum x S u)
      (hhappy : ∀ u ∈ Dset, ∀ Ť, Θ.rho S u Ť ≠ 0 → N.Happy (R.project Ť))
  /-- Case 3: two half bundles `e ≠ f` at `S`, reduced at `S` by the same density,
  supported on the 2-2-2 happy event on the projection. The complement of each
  retained polygon side has mass at most `G.halfWidth + 2*eps + eta`, in one
  of the two orientations; this includes the C-part loss once. -/
  | twoTwoTwo (e f : Finset (Fin n)) (he : e ∈ H.siblings Ŝ S) (hf : f ∈ H.siblings Ŝ S)
      (hef : e ≠ f) (hhe : IsHalfBundle x G.halfWidth S e) (hhf : IsHalfBundle x G.halfWidth S f)
      (hsupp : ∀ Ť, Θ.rho S e Ť ≠ 0 → TwoTwoTwoHappy e S f (R.project Ť))
      (heq : Θ.rho S f = Θ.rho S e)
      (hside : (∑ g ∈ betweenEdges S e \ N.partA, x g ≤ G.halfWidth + (2 * eps + eta)
            ∧ ∑ g ∈ betweenEdges S f \ N.partB, x g ≤ G.halfWidth + (2 * eps + eta))
          ∨ (∑ g ∈ betweenEdges S e \ N.partB, x g ≤ G.halfWidth + (2 * eps + eta)
            ∧ ∑ g ∈ betweenEdges S f \ N.partA, x g ≤ G.halfWidth + (2 * eps + eta)))


namespace ReductionDataOn
variable (D : G.ReductionDataOn R H μ p P)

open Classical in
/-- **The sidecar, built from `D.top`.**  No Theorem 5.28 constant is needed:
the split is by excluded middle on `BadCase` and on the piece 2-1-1 case at
`p`, and the third branch is the top thinnings' own coherence. -/
theorem polygonTopCases (hx : ∀ e, 0 ≤ x e) (heta₁ : eta ≤ eps) (heps1 : eps < 1)
    (hctrl : P.ControlsDescendants) {Ŝ S : Finset (Fin n)} (hdeg : DegreeCutData H Ŝ)
    (hS : S ∈ H.children Ŝ) {N : NearCycle x eta} (hN : H.Presents N S) :
    PolygonTopCases (D.top Ŝ hdeg) S N := by
  classical
  have hScut : S ∈ H.cuts := H.mem_cuts_of_mem_children hS
  have hcomp : (P.get S hScut).PolygonCompatible N :=
    (P.get S hScut).polygonCompatible_of_controls (hctrl S hScut) hN hx heta₁ heps1
  by_cases hbad : G.BadCase H μ Ŝ S
  · exact .bad hbad
  by_cases h211 : R.TwoOneOneCaseOn H μ G.halfWidth Ŝ S p (P.get S hScut)
  · refine .twoOneOne ((H.siblings Ŝ S).filter
      (fun u => R.IsTwoOneOneGoodOn μ p S u (P.get S hScut).A (P.get S hScut).B
        (P.get S hScut).C)) (Finset.filter_subset _ _) h211 ?_
    intro u hu Ť hrho
    obtain ⟨-, hgood211⟩ := Finset.mem_filter.mp hu
    obtain ⟨hev, htr⟩ := (D.top Ŝ hdeg).event_of_rho_ne_zero hrho
    have hgp := (D.top Ŝ hdeg).goodPair_of_thin_ne_zero
      ((D.top Ŝ hdeg).thin_ne_zero_of_rho_ne_zero hrho)
    have hhw := (D.top Ŝ hdeg).event_happy S hS u hgp.2.1 hgp.2.2.1 Ť hev
    rcases hhw.2 with ⟨-, hhappy⟩ | ⟨hn, -⟩
    · exact hcomp.happy_of_twoOneOneHappyOn hN htr hhappy
    · exact absurd hgood211 hn
  · obtain ⟨e, he, f, hf, hef, hhe, hhf, hxB, hxA, hiffe, -, hthin⟩ :=
      (D.top Ŝ hdeg).coherent S hS hbad h211
    have hdisje : Disjoint S e :=
      H.children_disjoint (H.mem_children.mp hS) (H.mem_siblings.mp he).2
        (Ne.symm (H.mem_siblings.mp he).1)
    have hdisjf : Disjoint S f :=
      H.children_disjoint (H.mem_children.mp hS) (H.mem_siblings.mp hf).2
        (Ne.symm (H.mem_siblings.mp hf).1)
    refine .twoTwoTwo e f he hf hef hhe hhf ?_ ?_
      (hcomp.sum_sdiff_side_le hx (betweenEdges_subset_cutEdges_left hdisje)
        (betweenEdges_subset_cutEdges_left hdisjf) hxB hxA)
    · intro Ť hrho
      obtain ⟨hev, htr⟩ := (D.top Ŝ hdeg).event_of_rho_ne_zero hrho
      rw [← R.twoTwoTwoHappyOn_iff htr]
      exact (hiffe Ť).mp hev
    · funext Ť
      unfold TopThinningsOn.rho
      rw [hthin]


end ReductionDataOn
end BundleGoodnessPolicy
end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedPolygonCompatibility
import TSPGap.RefinedReductionPush

/-!
# The provenance of the top densities at a polygon cut

KKO21's Lemma 7.8 bounds the increase of a polygon cut `S` whose parent `Ŝ` is
a degree cut by the cases of Theorem 5.28 at `S`: a bad half bundle, a set of
2-1-1 good edges of mass `≥ 1/2 − ε₂ − ε_η` on which a reduced tree makes the
polygon happy, or the two 2-2-2 good half bundles of case (iii) with equal
reduction densities at `S` and small wrong-side masses.  The pushed
certificate cannot carry the last two (the case-2 identification and the
wrong-side masses are stated against the degree partition), so this
**sidecar** reads them directly off the piece top thinnings `D.top Ŝ`:

* `PolygonTopCases Θ S N` — the three alternatives, with everything the
  consumer needs already on the base: the 2-1-1 case with `N.Happy` on the
  projection of every tree carrying density (through the degree/polygon
  compatibility), and the case-(iii) pair with `TwoTwoTwoHappy` on the
  projection, equal densities, and the wrong-side masses against the polygon
  partition in the orientation the compatibility fixes, at the honest
  `ε₂ + 2ε₁ + ε_η`.
* `ReductionDataOn.polygonTopCases` — the trichotomy is by excluded middle on
  `BadCase` and on the piece 2-1-1 case **at the thinning's own `p`**, the
  third branch being `TopThinningsOn.coherent` itself, so no Theorem 5.28
  constants enter; the witnesses are the coherence's own, never the
  existentials of the pushed certificate.
-/

namespace TSPGap

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H}

/-- A nonzero thinning sits on the support of the lifted law. -/
theorem TopThinningsOn.liftProb_ne_zero_of_thin_ne_zero {Ŝ : Finset (Fin n)}
    (Θ : R.TopThinningsOn H μ Ŝ ε₂ p P) {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.thin u u' Ť ≠ 0) : R.liftProb μ Ť ≠ 0 := by
  intro h0
  apply h
  exact le_antisymm (h0 ▸ Θ.thin_le u u' Ť) (Θ.thin_nonneg u u' Ť)

/-- A tree carrying density at a good pair lies in the pair's event, and is a
transversal. -/
theorem TopThinningsOn.event_of_rho_ne_zero {Ŝ : Finset (Fin n)}
    (Θ : R.TopThinningsOn H μ Ŝ ε₂ p P) {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.rho u u' Ť ≠ 0) : Θ.event u u' Ť ∧ R.IsTransversal Ť := by
  have hthin := Θ.thin_ne_zero_of_rho_ne_zero h
  have hgp := Θ.goodPair_of_thin_ne_zero hthin
  exact ⟨(Θ.uniform u hgp.1 u' hgp.2.1 hgp.2.2.1 hgp.2.2.2).support Ť hthin,
    (R.liftProb_ne_zero μ (Θ.liftProb_ne_zero_of_thin_ne_zero hthin)).1⟩

/-- **The provenance of the top densities at the polygon cut `S`**, child of
the degree cut `Ŝ` carrying the thinnings `Θ`, against the near-cycle `N`
presenting `S`. -/
inductive PolygonTopCases {Ŝ : Finset (Fin n)} (Θ : R.TopThinningsOn H μ Ŝ ε₂ p P)
    (S : Finset (Fin n)) (N : NearCycle x εη) : Prop
  /-- Case 1: the bad half bundles at `S` carry mass `≥ 1/2 − ε₂`. -/
  | bad (h : BadCase H μ ε₂ Ŝ S)
  /-- Case 2: a set of siblings carrying mass `≥ 1/2 − ε₂ − ε_η` whose bundles,
  whenever reduced at `S`, make the polygon happy on the projection. -/
  | twoOneOne (Dset : Finset (Finset (Fin n))) (hsub : Dset ⊆ H.siblings Ŝ S)
      (hmass : 1 / 2 - ε₂ - εη ≤ ∑ u ∈ Dset, pairSum x S u)
      (hhappy : ∀ u ∈ Dset, ∀ Ť, Θ.rho S u Ť ≠ 0 → N.Happy (R.project Ť))
  /-- Case 3: two half bundles `e ≠ f` at `S`, reduced at `S` by the same density,
  supported on the 2-2-2 happy event on the projection, with the wrong-side
  masses against the polygon partition at most `ε₂ + 2ε₁ + ε_η`, in one of the
  two orientations. -/
  | twoTwoTwo (e f : Finset (Fin n)) (he : e ∈ H.siblings Ŝ S) (hf : f ∈ H.siblings Ŝ S)
      (hef : e ≠ f) (hhe : IsHalfBundle x ε₂ S e) (hhf : IsHalfBundle x ε₂ S f)
      (hsupp : ∀ Ť, Θ.rho S e Ť ≠ 0 → TwoTwoTwoHappy e S f (R.project Ť))
      (heq : Θ.rho S f = Θ.rho S e)
      (hside : (∑ g ∈ betweenEdges S e ∩ N.partB, x g ≤ ε₂ + (2 * ε₁ + εη)
            ∧ ∑ g ∈ betweenEdges S f ∩ N.partA, x g ≤ ε₂ + (2 * ε₁ + εη))
          ∨ (∑ g ∈ betweenEdges S e ∩ N.partA, x g ≤ ε₂ + (2 * ε₁ + εη)
            ∧ ∑ g ∈ betweenEdges S f ∩ N.partB, x g ≤ ε₂ + (2 * ε₁ + εη)))

end EdgeRefinement

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- **The sidecar, built from `D.top`.**  No Theorem 5.28 constant is needed:
the split is by excluded middle on `BadCase` and on the piece 2-1-1 case at
`p`, and the third branch is the top thinnings' own coherence. -/
theorem polygonTopCases (hx : ∀ e, 0 ≤ x e) (hεη₁ : εη ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hctrl : P.ControlsDescendants) {Ŝ S : Finset (Fin n)} (hdeg : DegreeCutData H Ŝ)
    (hS : S ∈ H.children Ŝ) {N : NearCycle x εη} (hN : H.Presents N S) :
    EdgeRefinement.PolygonTopCases (D.top Ŝ hdeg) S N := by
  classical
  have hScut : S ∈ H.cuts := H.mem_cuts_of_mem_children hS
  have hcomp : (P.get S hScut).PolygonCompatible N :=
    (P.get S hScut).polygonCompatible_of_controls (hctrl S hScut) hN hx hεη₁ hε₁1
  by_cases hbad : BadCase H μ ε₂ Ŝ S
  · exact .bad hbad
  by_cases h211 : R.TwoOneOneCaseOn H μ ε₂ Ŝ S p (P.get S hScut)
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
      (hcomp.sum_inter_side_le hN hx (betweenEdges_subset_edgeFinset hdisje)
        (betweenEdges_subset_edgeFinset hdisjf) hxB hxA)
    · intro Ť hrho
      obtain ⟨hev, htr⟩ := (D.top Ŝ hdeg).event_of_rho_ne_zero hrho
      rw [← R.twoTwoTwoHappyOn_iff htr]
      exact (hiffe Ť).mp hev
    · funext Ť
      unfold EdgeRefinement.TopThinningsOn.rho
      rw [hthin]

end ReductionDataOn

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NestedRectangular
import TSPGap.RefinedClaim75

/-!
# Rectangularity descends to a nested cut, on pieces

The piece form of `NestedRectangular.lean`.  Outside-determinacy in the piece
sense descends from `U` to `S ⊆ U` because the pieces outside `U` are already
visible among the pieces outside `S` (`outsidePieces_nested`); the graph
content is the base `InducesTree.glue_nested` read on the projection, since
equal outside pieces project to equal outside parts (`project_outsidePieces`).
The failure term is the base one: "`S` fails to induce a tree in the
projection" is a projected event, so its mass at the piece face is its mass at
the base face (`weightMass_refinedTreeFace_project`).  `claim_7_5_nested'_on`
is the paper-facing form with neither premise exposed.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### Outside-determinacy descends -/

/-- For `S ⊆ U` the pieces outside `U` are already visible among those outside `S`. -/
theorem outsidePieces_nested {S U : Finset (Fin n)} (hSU : S ⊆ U) (Ť : Finset R.Piece) :
    R.outsidePieces U Ť = R.outsidePieces U (R.outsidePieces S Ť) := by
  classical
  unfold outsidePieces
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · intro hU
    exact ⟨fun hS => hU fun w hw => hSU (hS w hw), hU⟩
  · rintro ⟨-, hU⟩
    exact hU

variable {R}

/-- Outside-determinacy at `U` implies outside-determinacy at any `S ⊆ U`. -/
theorem RefinedOutsideDetermined.descend {S U : Finset (Fin n)} (hSU : S ⊆ U)
    {P : Finset R.Piece → Prop} (h : R.RefinedOutsideDetermined U P) :
    R.RefinedOutsideDetermined S P := by
  intro Ť Ť' hTT'
  refine h Ť Ť' ?_
  rw [R.outsidePieces_nested hSU Ť, R.outsidePieces_nested hSU Ť', hTT']

/-! ### The nested rectangularity -/

/-- **Rectangularity descends to a nested cut on pieces**, once the inner tree
event (in the projection) is conjoined.  The witness reads only the pieces
outside `S`; that it is implied by `InducesTree U (project Ť)` is the base
`glue_nested`, through `project_outsidePieces`. -/
theorem IsRectangularAtOn.nested {S U : Finset (Fin n)} (hSU : S ⊆ U)
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn U E) :
    R.IsRectangularAtOn S (fun Ť => E Ť ∧ InducesTree S (R.project Ť)) := by
  obtain ⟨Q, hQ, hEQ⟩ := hE
  refine ⟨fun Ť => (∀ Ť', InducesTree S (R.project Ť') →
      R.outsidePieces S Ť' = R.outsidePieces S Ť → InducesTree U (R.project Ť')) ∧ Q Ť, ?_, ?_⟩
  · refine RefinedOutsideDetermined.and ?_ (hQ.descend hSU)
    intro Ť₁ Ť₂ h12
    constructor
    · exact fun h Ť' hT' hout => h Ť' hT' (by rw [hout, h12])
    · exact fun h Ť' hT' hout => h Ť' hT' (by rw [hout, ← h12])
  · intro Ť
    constructor
    · rintro ⟨hET, hS⟩
      obtain ⟨hU, hQT⟩ := (hEQ Ť).mp hET
      refine ⟨hS, fun Ť' hT' hout => InducesTree.glue_nested hSU hU hS hT' ?_, hQT⟩
      rw [← R.project_outsidePieces, ← R.project_outsidePieces, hout]
    · rintro ⟨hS, hall, hQT⟩
      exact ⟨(hEQ Ť).mpr ⟨hall Ť hS rfl, hQT⟩, hS⟩

variable (R)

/-! ### The failure term -/

/-- **Under the piece tree face of `U`, an inner cut `S ⊆ U` fails to induce a
tree in the projection on at most `ε_η/2` of the mass** — the base bound, the
event being projected. -/
theorem refinedTreeFace_not_inducesTree_le {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {εη : ℝ} {S U : Finset (Fin n)} (hSU : S ⊆ U)
    (hSne : S.Nonempty) (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U)
    (hScut : cutSum x S ≤ 2 + εη) (hUcut : cutSum x U ≤ 2 + εη) (hεηcap : εη ≤ 1e-10) :
    weightMass (R.refinedTreeFace (R.liftProb μ) U) (fun Ť => ¬ InducesTree S (R.project Ť))
      ≤ εη / 2 := by
  rw [R.weightMass_refinedTreeFace_project μ U (fun T => ¬ InducesTree S T)]
  exact treeFace_not_inducesTree_le hx μ hμ hSU hSne hUne hU0 hScut hUcut hεηcap

/-! ### The paper-facing nested claim -/

set_option maxHeartbeats 400000 in
-- both premises of the low-level form are discharged here
/-- **Claim 7.5 on pieces at a nested cut**, with neither premise exposed. -/
theorem claim_7_5_nested'_on {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {S u U : Finset (Fin n)} (hSne : S.Nonempty) (hune : u.Nonempty) (huS : u ⊂ S)
    (huniv : u ≠ Finset.univ) (hScut : cutSum x S ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hSU : S ⊆ U) (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hUcut : cutSum x U ≤ 2 + εη)
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn U E)
    {v : Finset R.Piece → ℝ} {p : ℝ} (hv : IsUniformThinning (R.liftProb μ) v E p)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges S, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges S, x g) ≤ 1 - ε) :
    weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) + p * (εη / 2) := by
  classical
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsupU := hbase.face_sup hUne
  have hdefU : faceDeficiency μ.prob (internalEdges U) (U.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hUne hU0]; linarith
  have hmassU : 0 <
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges U)) (U.card - 1)) := by
    have := hbase.law.face_mass_ge hsupU; linarith
  refine R.claim_7_5_nested_on hx hμ hεη hεηcap hSne (hU0.mono hSU) hune huS huniv hScut hucut
    (hE.nested hSU) hv ?_ hε0 hclo hchi
  have hins : R.RefinedInsideDetermined U (fun Ť => ¬ InducesTree S (R.project Ť)) :=
    fun Ť Ť' hTT' => not_congr (R.refinedInsideDetermined_inducesTree hSU Ť Ť' hTT')
  exact hE.thin_weightMass_le μ hμ hUne hmassU hv hins
    (R.refinedTreeFace_not_inducesTree_le hx μ hμ hSU hSne hUne hU0 hScut hUcut hεηcap)

end EdgeRefinement

end TSPGap

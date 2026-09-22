/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeFaces
import TSPGap.Lemma523Indexed
import TSPGap.TreeDistSetup
import TSPGap.RefinedTreeFace
import TSPGap.RefinementStability

/-!
# The §5 setup on the refined model

What a §5 lemma over a fiber tree model asks of its ambient weight, supplied
for the lifted tree law `R.liftProb μ` on the refined model `R.model`:

* the package — stability (`refinedTreeRealStable`), the tree rank in the
  `k + 1` form, nonnegativity, total mass one;
* transversal spanning support (`treeSupport_liftProb`), hence every count
  certificate by `ofSupport`;
* the expected counts: over a piece set they are the **piece weights**
  (`expCard_liftProb_eq_sum_weight`, from the lifted marginal), and over the
  pieces of an edge set they are the base expected counts
  (`expCard_liftWeight`), so the near-min-cut degrees, the bundle mass and
  the face deficiencies of `PairData` and `TripleData` transfer unchanged
  (`RefinedPairData`, `RefinedTripleData`);
* **KKO21 Eq. (24) transfers** (`eqTwentyFourAlt_liftProb`): the three-atom
  face law of the lift is the lift of the base face law, avoiding the pieces
  of a bundle is the lift of avoiding the bundle, and expected counts and
  masses over fiber-saturated sets are the base ones — so the base
  `eq_24_alternative` *is* the certificate on the refined model.

Nothing here is re-proved: each field is a base fact read through one of the
lift/commutation identities.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### Expected counts under the lifted law -/

/-- **The expected number of pieces of a piece set is its weight**: the
lifted marginal of a piece is `x (base p) · q p`. -/
theorem expCard_liftProb_eq_sum_weight (μ : TreeDist n x) (A : Finset R.Piece) :
    expCard (R.liftProb μ) A = ∑ p ∈ A, R.weight p := by
  classical
  rw [expCard_eq_sum_marginal]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [weightMass_eq_filter_sum]
  exact R.lift_marginal μ p

/-- Expected counts over the pieces of an edge set are the base ones. -/
theorem expCard_liftProb_piecesOver (μ : TreeDist n x) (F : Finset (Sym2 (Fin n))) :
    expCard (R.liftProb μ) (R.piecesOver F) = expCard μ.prob F := by
  rw [R.liftProb_eq_liftWeight]
  exact R.expCard_liftWeight μ.weightSupportedOn_edgeFinset F

/-- The face deficiency of the lifted law at the pieces of a face is the
base one. -/
theorem faceDeficiency_liftProb (μ : TreeDist n x) (K : Finset (Sym2 (Fin n))) (m : ℕ) :
    faceDeficiency (R.liftProb μ) (R.piecesOver K) m = faceDeficiency μ.prob K m := by
  rw [R.liftProb_eq_liftWeight]
  exact R.faceDeficiency_liftWeight μ.weightSupportedOn_edgeFinset K m

/-- The lifted law is a probability law. -/
theorem liftProb_totalMass (μ : TreeDist n x) : totalMass (R.liftProb μ) = 1 :=
  R.lift_total μ

/-- The lifted law in the `k + 1` rank form of the §5 lemmas. -/
theorem liftProb_fixedRankWeight_succ (μ : TreeDist n x) {u v : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v) :
    FixedRankWeight (n - 2 + 1) (R.liftProb μ) :=
  R.fixedRankWeight_liftWeight (fixedRankWeight_prob_succ μ hune hvne huv)

/-! ### The pair data on the refined model -/

/-- **The pair data of the lifted law** on the refined model: every field of
`PairData` read through the lift, plus the two-atom count certificate. -/
structure RefinedPairData (μ : TreeDist n x) (ε : ℝ) (u v : Finset (Fin n)) : Prop where
  stable : IsRealStable (genPoly (R.liftProb μ))
  rank : FixedRankWeight (n - 2 + 1) (R.liftProb μ)
  support : R.model.TreeSupport (R.liftProb μ)
  count : R.model.TwoAtomCountData (R.liftProb μ) u v
  une : u.Nonempty
  vne : v.Nonempty
  disj : Disjoint u v
  du1 : 2 ≤ expCard (R.liftProb μ) (R.piecesOver (cutEdges u))
  du2 : expCard (R.liftProb μ) (R.piecesOver (cutEdges u)) ≤ 2 + ε
  dv1 : 2 ≤ expCard (R.liftProb μ) (R.piecesOver (cutEdges v))
  dv2 : expCard (R.liftProb μ) (R.piecesOver (cutEdges v)) ≤ 2 + ε
  deficiency : faceDeficiency (R.liftProb μ) (R.piecesOver (twoAtomInternal u v))
    (twoAtomBudget u v) ≤ ε
  bundle : expCard (R.liftProb μ) (R.piecesOver (betweenEdges u v)) = pairSum x u v

/-- **The refined pair data from the base pair data.** -/
theorem refinedPairData {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {ε : ℝ}
    {u v : Finset (Fin n)} (P : PairData μ ε u v) : R.RefinedPairData μ ε u v where
  stable := hμ.refinedTreeRealStable R
  rank := R.liftProb_fixedRankWeight_succ μ P.une P.vne P.disj
  support := R.treeSupport_liftProb μ
  count := FiberTreeModel.TwoAtomCountData.ofSupport (R.treeSupport_liftProb μ) P.une P.vne P.disj
  une := P.une
  vne := P.vne
  disj := P.disj
  du1 := by rw [R.expCard_liftProb_piecesOver]; exact P.du1
  du2 := by rw [R.expCard_liftProb_piecesOver]; exact P.du2
  dv1 := by rw [R.expCard_liftProb_piecesOver]; exact P.dv1
  dv2 := by rw [R.expCard_liftProb_piecesOver]; exact P.dv2
  deficiency := by rw [R.faceDeficiency_liftProb]; exact P.deficiency
  bundle := by rw [R.expCard_liftProb_piecesOver]; exact P.bundle

/-! ### The triple data, and Eq. (24) on the refined model -/

/-- Support inside the genuine edges survives a face. -/
theorem _root_.TSPGap.weightSupportedOn_faceDist {w : Finset (Sym2 (Fin n)) → ℝ}
    {K : Finset (Sym2 (Fin n))} (hw : WeightSupportedOn w K) (c : Sym2 (Fin n) → ℕ) (m : ℕ) :
    WeightSupportedOn (faceDist w c m) K :=
  fun T hT => hw T (faceDist_ne_zero_weight hT)

/-- Support inside the genuine edges survives avoiding a set. -/
theorem _root_.TSPGap.weightSupportedOn_avoidWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    {K : Finset (Sym2 (Fin n))} (hw : WeightSupportedOn w K) (D : Finset (Sym2 (Fin n))) :
    WeightSupportedOn (avoidWeight w D) K := by
  intro T hT
  rw [avoidWeight_apply] at hT
  split_ifs at hT with hc
  · exact hw T hT
  · exact absurd rfl hT

theorem piecesOver_sdiff (F G : Finset (Sym2 (Fin n))) :
    R.piecesOver (F \ G) = R.piecesOver F \ R.piecesOver G := by
  rw [← R.model_fiberOver, ← R.model_fiberOver, ← R.model_fiberOver]
  exact R.model.fiberOver_sdiff F G

/-- The three-atom face law of the lift is the lift of the base face law. -/
theorem tau3_liftProb (μ : TreeDist n x) (u v z : Finset (Fin n)) :
    R.model.tau3 (R.liftProb μ) u v z
      = R.liftWeight (faceDist μ.prob (indicatorCost (threeAtomInternal u v z))
          (atomBudget u v z)) := by
  unfold FiberTreeModel.tau3
  rw [R.model_fiberOver, R.liftProb_eq_liftWeight]
  exact R.faceDist_liftWeight μ.weightSupportedOn_edgeFinset _ _

/-- **Eq. (24) on the refined model** is the base `eq_24_alternative`, read
through the lift. -/
theorem eqTwentyFourAlt_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hsmall : ε₂ + 3 * εη ≤ 1 / 1000) :
    R.model.EqTwentyFourAlt (R.liftProb μ) u v z (R.piecesOver (betweenEdges u v))
      (R.piecesOver (betweenEdges v z)) := by
  have D := H.tripleData hx μ hμ hu hv hz huv hvz huz
  have hbase := eq_24_alternative D.uv.stable D.uv.rank μ.weightNonneg μ.total D.uv.tree
    D.uv.une D.uv.vne D.vz.vne D.uv.disj D.vz.disj D.uz.disj (Finset.Subset.refl _)
    (Finset.Subset.refl _) hεη hε₂ (by linarith [D.deficiency3])
    (by rw [D.uv.bundle]; exact hxE) (by rw [D.vz.bundle]; exact hxF) hsmall
  have hν₀ : WeightSupportedOn (faceDist μ.prob (indicatorCost (threeAtomInternal u v z))
      (atomBudget u v z)) (edgeFinset n) :=
    weightSupportedOn_faceDist μ.weightSupportedOn_edgeFinset _ _
  have hνE := weightSupportedOn_avoidWeight hν₀ (betweenEdges u v)
  have hνF := weightSupportedOn_avoidWeight hν₀ (betweenEdges v z)
  unfold FiberTreeModel.EqTwentyFourAlt
  rw [R.tau3_liftProb]
  simp only [R.model_fiberOver, ← R.piecesOver_sdiff, R.avoidWeight_liftWeight,
    R.expCard_liftWeight hν₀, R.expCard_liftWeight hνE, R.expCard_liftWeight hνF,
    R.totalMass_liftWeight hνE, R.totalMass_liftWeight hνF]
  exact hbase

/-- **The triple data of the lifted law** on the refined model. -/
structure RefinedTripleData (μ : TreeDist n x) (ε : ℝ) (u v z : Finset (Fin n)) : Prop where
  uv : R.RefinedPairData μ ε u v
  vz : R.RefinedPairData μ ε v z
  uz : R.RefinedPairData μ ε u z
  count : R.model.ThreeAtomOneHotData (R.liftProb μ) u v z
  deficiency3 : faceDeficiency (R.liftProb μ) (R.piecesOver (threeAtomInternal u v z))
    (atomBudget u v z) ≤ 3 * ε / 2

/-- **The refined triple data from the base triple data.** -/
theorem refinedTripleData {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {ε : ℝ}
    {u v z : Finset (Fin n)} (T : TripleData μ ε u v z) : R.RefinedTripleData μ ε u v z where
  uv := R.refinedPairData hμ T.uv
  vz := R.refinedPairData hμ T.vz
  uz := R.refinedPairData hμ T.uz
  count := FiberTreeModel.ThreeAtomOneHotData.ofSupport (R.treeSupport_liftProb μ) T.uv.une
    T.uv.vne T.vz.vne T.uv.disj T.vz.disj T.uz.disj
  deficiency3 := by rw [R.faceDeficiency_liftProb]; exact T.deficiency3

end EdgeRefinement

end TSPGap

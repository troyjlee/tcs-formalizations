/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedSection5Setup
import TSPGap.Lemma527Indexed
import TSPGap.RefinedHappyEvents

/-!
# KKO21 Lemma 5.27 on pieces

The lifted-piece instance of `lemma_5_27_indexed`: for three children
`u`, `v`, `z` of a hierarchy cut with `e = E(u,v)`, `f = E(v,z)` good top
half bundles at `v`, a piece partition `A ⊔ B ⊔ C` of the pieces over
`δ(v)` with Definition 5.18's weight bounds and `x(e ∩ B), x(f ∩ A) ≤ ε₂`,
if neither `e` nor `f` is 2-1-1 good w.r.t. `v` under the lifted law, then
`e, f` are 2-2-2 happy on pieces (`TwoTwoTwoHappyOn`) with lifted
probability at least `0.005`.  The three certificates come from the lifted
law's transversal spanning support; the sides are arbitrary piece sets.

`lemma_5_27_gurvits_liftProb` is the enlarged-threshold instance:
not-good at `0.02ε₂²` gives `0.0005` fallback mass, with the same
arbitrary piece sides and no projection of their partition.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- **Lemma 5.27 for the lifted law, with piece sides.** -/
theorem lemma_5_27_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    (hxEB : ∑ p ∈ R.piecesOver (betweenEdges u v) ∩ B, R.weight p ≤ ε₂)
    (hxFA : ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂)
    (hgoodE : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v u)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v z)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2))
    (hnotgoodE : weightMass (R.liftProb μ) (fun Ť =>
      (Ť ∩ A).card = 1 ∧ (Ť ∩ B).card = 1 ∧ (Ť ∩ C).card = 0
        ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2
        ∧ InducesTree v (R.project Ť) ∧ InducesTree u (R.project Ť)) < 0.005 * ε₂ ^ 2)
    (hnotgoodF : weightMass (R.liftProb μ) (fun Ť =>
      (Ť ∩ B).card = 1 ∧ (Ť ∩ A).card = 1 ∧ (Ť ∩ C).card = 0
        ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2
        ∧ InducesTree v (R.project Ť) ∧ InducesTree z (R.project Ť)) < 0.005 * ε₂ ^ 2) :
    0.005 ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  classical
  have T0 := H.tripleData hx μ hμ hu hv hz huv hvz huz
  have T := R.refinedTripleData hμ T0
  have hsupp := R.treeSupport_liftProb μ
  have hcert3 : R.model.ThreeAtomUzData (R.liftProb μ) u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp T0.uv.une T0.uv.vne T0.vz.vne T0.uv.disj
      T0.vz.disj T0.uz.disj
  have hcertE : R.model.TwoAtomCrossData (R.liftProb μ) v u :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp T0.uv.vne T0.uv.une T0.uv.disj.symm
      T0.uv.symm.proper
  have hcertF : R.model.TwoAtomCrossData (R.liftProb μ) v z :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp T0.vz.une T0.vz.vne T0.vz.disj T0.vz.proper
  have h := lemma_5_27_indexed R.model T.uv.stable T.uv.rank (R.liftProb_weightNonneg μ)
    (R.liftProb_totalMass μ) T0.uv.une T0.uv.vne T0.vz.vne T0.uv.disj T0.vz.disj T0.uz.disj
    T0.uv.symm.proper T0.vz.proper hcert3 hcertE hcertF (A := A) (B := B) (C := C)
    (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    (by rw [R.model_fiberOver]; linarith [T.deficiency3])
    (by rw [R.model_fiberOver, twoAtomInternal_comm v u, twoAtomBudget_comm v u]
        linarith [T.uv.deficiency])
    (by rw [R.model_fiberOver]; linarith [T.vz.deficiency])
    (by rw [R.model_fiberOver, T.uv.bundle]; exact hxE)
    (by rw [R.model_fiberOver, T.vz.bundle]; exact hxF)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxC)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxEB)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxFA)
    (by rw [R.model_fiberOver]; exact T.uv.du1) (by rw [R.model_fiberOver]; exact T.uv.du2)
    (by rw [R.model_fiberOver]; exact T.vz.dv1) (by rw [R.model_fiberOver]; exact T.vz.dv2)
    (by simpa only [R.model_fiberOver] using hgoodE)
    (by simpa only [R.model_fiberOver] using hgoodF)
    (by simpa only [R.model_fiberOver, R.model_project] using hnotgoodE)
    (by simpa only [R.model_fiberOver, R.model_project] using hnotgoodF)
  unfold EdgeRefinement.TwoTwoTwoHappyOn
  simpa only [R.model_fiberOver, R.model_project] using h

/-- Lemma 5.27 with the increased `0.02 ε₂²` not-good threshold and
an absolute `0.0005` coherent fallback mass. -/
theorem lemma_5_27_gurvits_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    (hxEB : ∑ p ∈ R.piecesOver (betweenEdges u v) ∩ B, R.weight p ≤ ε₂)
    (hxFA : ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂)
    (hgoodE : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v u)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v z)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2))
    (hnotgoodE : weightMass (R.liftProb μ) (fun Ť =>
      (Ť ∩ A).card = 1 ∧ (Ť ∩ B).card = 1 ∧ (Ť ∩ C).card = 0
        ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2
        ∧ InducesTree v (R.project Ť) ∧ InducesTree u (R.project Ť)) < 0.02 * ε₂ ^ 2)
    (hnotgoodF : weightMass (R.liftProb μ) (fun Ť =>
      (Ť ∩ B).card = 1 ∧ (Ť ∩ A).card = 1 ∧ (Ť ∩ C).card = 0
        ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2
        ∧ InducesTree v (R.project Ť) ∧ InducesTree z (R.project Ť)) < 0.02 * ε₂ ^ 2) :
    0.0005 ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  classical
  have T0 := H.tripleData hx μ hμ hu hv hz huv hvz huz
  have T := R.refinedTripleData hμ T0
  have hsupp := R.treeSupport_liftProb μ
  have hcert3 : R.model.ThreeAtomUzData (R.liftProb μ) u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp T0.uv.une T0.uv.vne T0.vz.vne T0.uv.disj
      T0.vz.disj T0.uz.disj
  have hcertE : R.model.TwoAtomCrossData (R.liftProb μ) v u :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp T0.uv.vne T0.uv.une T0.uv.disj.symm
      T0.uv.symm.proper
  have hcertF : R.model.TwoAtomCrossData (R.liftProb μ) v z :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp T0.vz.une T0.vz.vne T0.vz.disj T0.vz.proper
  have h := lemma_5_27_gurvits_indexed R.model T.uv.stable T.uv.rank (R.liftProb_weightNonneg μ)
    (R.liftProb_totalMass μ) T0.uv.une T0.uv.vne T0.vz.vne T0.uv.disj T0.vz.disj T0.uz.disj
    T0.uv.symm.proper T0.vz.proper hcert3 hcertE hcertF (A := A) (B := B) (C := C)
    (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    (by rw [R.model_fiberOver]; linarith [T.deficiency3])
    (by rw [R.model_fiberOver, twoAtomInternal_comm v u, twoAtomBudget_comm v u]
        linarith [T.uv.deficiency])
    (by rw [R.model_fiberOver]; linarith [T.vz.deficiency])
    (by rw [R.model_fiberOver, T.uv.bundle]; exact hxE)
    (by rw [R.model_fiberOver, T.vz.bundle]; exact hxF)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxC)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxEB)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxFA)
    (by rw [R.model_fiberOver]; exact T.uv.du1) (by rw [R.model_fiberOver]; exact T.uv.du2)
    (by rw [R.model_fiberOver]; exact T.vz.dv1) (by rw [R.model_fiberOver]; exact T.vz.dv2)
    (by simpa only [R.model_fiberOver] using hgoodE)
    (by simpa only [R.model_fiberOver] using hgoodF)
    (by simpa only [R.model_fiberOver, R.model_project] using hnotgoodE)
    (by simpa only [R.model_fiberOver, R.model_project] using hnotgoodF)
  unfold EdgeRefinement.TwoTwoTwoHappyOn
  simpa only [R.model_fiberOver, R.model_project] using h

end TSPGap

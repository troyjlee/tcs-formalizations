/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedSection5Setup
import TSPGap.Lemma522Indexed
import TSPGap.RefinedHappyEvents

/-!
# Capacity-strengthened Lemma 5.22 on pieces

The `_capacity` export gives `0.026ε₂²`, by instantiating
`lemma_5_22_indexed_capacity` at the refined fiber tree model.
The sides are arbitrary piece sets; no projection of their partition is used.

The original `0.005ε₂²` statement is retained as a weakening wrapper.
This local improvement does not change the global thinning parameter.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- **Lemma 5.22 for the lifted law, with piece sides.** -/
theorem lemma_5_22_liftProb_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : 1 / 2 + ε₂ ≤ pairSum x u v)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη) :
    R.IsTwoOneOneGoodOn μ (0.026 * ε₂ ^ 2) u v A B C := by
  have P := R.refinedPairData hμ (H.pairData hx μ hμ hu hv huv)
  have hcount : R.model.TwoAtomOneHotData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomOneHotData.ofSupport P.support P.une P.vne P.disj
  have h := lemma_5_22_indexed_capacity R.model P.stable P.rank (R.liftProb_weightNonneg μ)
    (R.liftProb_totalMass μ) P.une P.vne P.disj hcount (A := A) (B := B) (C := C)
    (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    (by rw [R.model_fiberOver]; linarith [P.deficiency])
    (by rw [R.model_fiberOver, P.bundle]; exact hxE)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxC)
    (by rw [R.model_fiberOver]; exact P.dv1) (by rw [R.model_fiberOver]; exact P.dv2)
  unfold EdgeRefinement.IsTwoOneOneGoodOn EdgeRefinement.TwoOneOneHappyOn
  simpa only [R.model_fiberOver, R.model_project] using h

/-- The original threshold, with its public statement unchanged. -/
theorem lemma_5_22_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : 1 / 2 + ε₂ ≤ pairSum x u v)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη) :
    R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) u v A B C := by
  have h := lemma_5_22_liftProb_capacity hx μ hμ H R hu hv huv
    hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxE hxA1 hxA2 hxB1 hxB2 hxC
  unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
  nlinarith only [h, sq_nonneg ε₂]

end TSPGap

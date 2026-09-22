/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma523Budget
import TSPGap.RefinedLemma523

/-!
# The stronger 5.23/A.1 budget on arbitrary piece sides

The indexed A.1 proof applies directly to the lifted law. Only topology and
full-bundle counts are read on the projection; the partition and tail remain
on pieces. Combining with the already proved piece 5.23 alternative gives
0.1187 epsilon^2 happy mass for one of the two orientations. The shared
thinning parameter and the published gap are not changed.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- A.1 at the two-percent tail under the lifted law, for arbitrary piece sides. -/
theorem lemma_A1_liftProb_of_tail_two_percent {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.0002) (hεηsq : εη ≤ ε ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε / 6 + εη)
    (hxBE : ∑ p ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight p ≤ ε)
    (hgood : 3 * ε ≤ weightMass (R.model.tau (R.liftProb μ) u v)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges u)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges v)).card = 2))
    (htail : (0.02 : ℝ) ≤ weightMass (R.liftProb μ) (fun Ť =>
      (Ť ∩ (A \ R.piecesOver (betweenEdges u v))).card
        + (Ť ∩ (R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v))).card ≤ 1)) :
    R.IsTwoOneOneGoodOn μ (0.1187 * ε ^ 2) u v A B C := by
  have P0 := H.pairData hx μ hμ hu hv huv
  have P := R.refinedPairData hμ P0
  have hcount : R.model.TwoAtomCrossData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomCrossData.ofSupport P.support P.une P.vne P.disj P0.proper
  have hSC : R.model.SupportComplete (R.liftProb μ) (R.piecesOver (betweenEdges u v)) u v := by
    refine ⟨?_, fun T _ => ?_⟩
    · rw [R.model_fiberOver]
    · rw [R.model_fiberOver]; exact Finset.inter_subset_right
  have h := lemma_A1_indexed_of_tail_two_percent R.model P.stable P.rank (R.liftProb_weightNonneg μ)
    (R.liftProb_totalMass μ) P.une P.vne P.disj P0.proper hcount
    (E := R.piecesOver (betweenEdges u v)) (A := A) (B := B) (C := C) hSC
    (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC hεη hε0 hεcap hεηsq
    (by rw [R.model_fiberOver]; linarith [P.deficiency])
    (by rw [P.bundle]; exact hxE)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxC)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxBE)
    (by rw [R.model_fiberOver]; exact P.dv1) (by rw [R.model_fiberOver]; exact P.dv2)
    (by simpa only [R.model_fiberOver] using hgood)
    (by simpa only [R.model_fiberOver] using htail)
  unfold EdgeRefinement.IsTwoOneOneGoodOn EdgeRefinement.TwoOneOneHappyOn
  simpa only [R.model_fiberOver, R.model_project] using h

/-- **Lemma 5.23's happy-event conclusion at the enlarged budget.**
Both bundles have small B-parts and are 2-2 good. The existing tail
alternative followed by A.1 gives the stronger conclusion in either
orientation. The common partition is never swapped implicitly. -/
theorem lemma_5_23_happy_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : |pairSum x v u - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    (hxBE : ∑ p ∈ B ∩ R.piecesOver (betweenEdges v u), R.weight p ≤ ε₂)
    (hxBF : ∑ p ∈ B ∩ R.piecesOver (betweenEdges v z), R.weight p ≤ ε₂)
    (hD : ∑ p ∈ (A \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z), R.weight p ≤ 0.00201)
    (hgoodE : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v u)
      (fun T => (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧ (T ∩ R.piecesOver (cutEdges u)).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v z)
      (fun T => (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧ (T ∩ R.piecesOver (cutEdges z)).card = 2)) :
    R.IsTwoOneOneGoodOn μ (0.1187 * ε₂ ^ 2) v u A B C
      ∨ R.IsTwoOneOneGoodOn μ (0.1187 * ε₂ ^ 2) v z A B C := by
  have hεηcap : εη ≤ 0.0000005 := by nlinarith
  have hA : A ⊆ R.piecesOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hxE' : |pairSum x u v - 1 / 2| ≤ ε₂ := by
    rw [pairSum_comm x u v]; exact hxE
  rcases lemma_5_23_liftProb hx μ hμ H R hu hv hz huv hvz huz hA hεη hε₂
    hεηcap (by linarith) hxE' hxF hD with hE | hF
  · left
    rw [betweenEdges_comm u v] at hE
    exact lemma_A1_liftProb_of_tail_two_percent hx μ hμ H R hv hu huv.symm
      hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE hgoodE hE
  · right
    exact lemma_A1_liftProb_of_tail_two_percent hx μ hμ H R hv hz hvz
      hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxF hxA1 hxA2 hxB1 hxB2 hxC hxBF hgoodF hF


end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedSection5Setup
import TSPGap.LemmaA1Indexed
import TSPGap.RefinedHappyEvents

/-!
# KKO21 Lemma A.1 on pieces

The lifted-piece instance of `lemma_A1_indexed`: for two children `u`, `v`
of a hierarchy cut with `|x_e − 1/2| ≤ ε`, a piece partition `A ⊔ B ⊔ C` of
the pieces over `δ(u)` with Definition 5.18's weight bounds and
`x(B ∩ e) ≤ ε`, the 2-2 good hypothesis under the two-atom face of the
lifted law, and the ambient tail on pieces, the bundle is 2-1-1 good w.r.t.
`u` under the lifted law at `0.005ε²` (`IsTwoOneOneGoodOn`).  The half
bundle is the full set of pieces over `E(u,v)` — support-complete by
definition — and the certificate with the union crossing comes from the
lifted law's transversal spanning support (`RefinedPairData.support`) and
the base pair data's properness.  The sides are arbitrary piece sets.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- **Lemma A.1 for the lifted law, with piece sides and the paper's `5ε` tail.** -/
theorem lemma_A1_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001) (hεηsq : εη ≤ ε ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε / 6 + εη)
    (hxBE : ∑ p ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight p ≤ ε)
    (hgood : 3 * ε ≤ weightMass (R.model.tau (R.liftProb μ) u v)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges u)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges v)).card = 2))
    (htail : 5 * ε ≤ weightMass (R.liftProb μ) (fun Ť =>
      (Ť ∩ (A \ R.piecesOver (betweenEdges u v))).card
        + (Ť ∩ (R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v))).card ≤ 1)) :
    R.IsTwoOneOneGoodOn μ (0.005 * ε ^ 2) u v A B C := by
  have P0 := H.pairData hx μ hμ hu hv huv
  have P := R.refinedPairData hμ P0
  have hcount : R.model.TwoAtomCrossData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomCrossData.ofSupport P.support P.une P.vne P.disj P0.proper
  have hSC : R.model.SupportComplete (R.liftProb μ) (R.piecesOver (betweenEdges u v)) u v := by
    refine ⟨?_, fun T _ => ?_⟩
    · rw [R.model_fiberOver]
    · rw [R.model_fiberOver]; exact Finset.inter_subset_right
  have h := lemma_A1_indexed R.model P.stable P.rank (R.liftProb_weightNonneg μ)
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

end TSPGap

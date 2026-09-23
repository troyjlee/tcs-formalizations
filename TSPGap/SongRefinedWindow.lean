/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRefinedGoodness
import TSPGap.RefinedLemma523

/-!
# Song's window and two-bundle tail under the actual lifted law

The window producer is instantiated at the actual hierarchy pair data and
Song's goodness policy. The existing 5.23 alternative supplies an original
tail of at least 0.02, which exceeds the required `K*h` at Song's parameters.
All side events remain on arbitrary piece sets.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- Song's window producer at the lifted law, with all conditioned inputs constructed. -/
theorem lemma_A1_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    (hxBE : ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q ≤ h)
    (hgood : goodness.IsGood μ u v)
    (htail : K * h ≤ weightMass (R.liftProb μ) (fun T =>
      (T ∩ (A \ R.piecesOver (betweenEdges u v))).card +
        (T ∩ (R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v))).card ≤ 1)) :
    p < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) := by
  have P0 := H.pairData hx μ hμ hu hv huv
  have P := R.refinedPairData hμ P0
  have hw : LawData (R.liftProb μ) (n - 2 + 1) :=
    ⟨P.stable, P.rank, R.liftProb_weightNonneg μ, R.liftProb_totalMass μ⟩
  have hc : R.model.TwoAtomCrossData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomCrossData.ofSupport P.support P.une P.vne P.disj P0.proper
  have hSC : R.model.SupportComplete (R.liftProb μ)
      (R.piecesOver (betweenEdges u v)) u v := by
    refine ⟨?_, fun T _ => ?_⟩
    · rw [R.model_fiberOver]
    · rw [R.model_fiberOver]; exact inter_subset_right
  have hmass := window_happy_indexed R.model hw P.disj hc hSC
    (A := A) (B := B) (C := C) (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC
    (by rw [R.model_fiberOver]; linarith only [P.deficiency, heta, hcap])
    (by rw [P.bundle]; exact hxE)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact ⟨hxA.1, by linarith only [hxA.2, hcap]⟩)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact ⟨hxB.1, by linarith only [hxB.2, hcap]⟩)
    (by rw [R.expCard_liftProb_eq_sum_weight]; linarith only [hxC, hcap])
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxBE)
    (by rw [R.model_fiberOver]; exact ⟨P.du1, by linarith only [P.du2, hcap]⟩)
    (by rw [R.model_fiberOver]; exact ⟨P.dv1, by linarith only [P.dv2, hcap]⟩)
    (by simpa only [R.model_fiberOver] using mass_liftProb_of_good R hgood hxE)
    (by simpa only [R.model_fiberOver] using htail)
  unfold EdgeRefinement.TwoOneOneHappyOn
  simpa only [R.model_fiberOver, R.model_project] using hmass

/-- The existing 5.23 tail alternative exceeds Song's required window budget. -/
theorem lemma_5_23_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges v))
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h)
    (hD : ∑ q ∈ (A \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z),
      R.weight q ≤ 0.00201) :
    (K * h < weightMass (R.liftProb μ) (fun T =>
      (T ∩ (A \ R.piecesOver (betweenEdges u v))).card +
        (T ∩ (R.piecesOver (cutEdges u) \ R.piecesOver (betweenEdges u v))).card ≤ 1)) ∨
    (K * h < weightMass (R.liftProb μ) (fun T =>
      (T ∩ (A \ R.piecesOver (betweenEdges v z))).card +
        (T ∩ (R.piecesOver (cutEdges z) \ R.piecesOver (betweenEdges v z))).card ≤ 1)) := by
  have hbudget : K * h < 0.02 := by norm_num [K, h]
  have htail := TSPGap.lemma_5_23_liftProb hx μ hμ H R hu hv hz huv hvz huz hA
    heta (by norm_num [h]) (hcap.trans (by norm_num [d₀]))
    (by norm_num [h]) hxE hxF hD
  exact htail.imp (hbudget.trans_le ·) (hbudget.trans_le ·)

end TSPGap.Song

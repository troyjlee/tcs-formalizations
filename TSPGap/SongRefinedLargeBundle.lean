/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongLargeBundle
import TSPGap.RefinedSection5Setup
import TSPGap.RefinedHappyEvents

/-!
# Large bundles under the actual tree and lifted laws

Hierarchy pair data supplies the stability, tree support, face deficiency
and opposite-cut means required by the large-bundle producer. The refined
instance keeps arbitrary piece sides and gives the common probability `p`.
The final wrapper uses the actual hierarchy error `7*t`, including the
endpoint `t = Song.H`.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- The large-bundle event for sibling atoms under the actual tree law. -/
theorem lemma_5_22_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : 1 / 2 + h ≤ pairSum x u v)
    (hxA : 1 - r ≤ ∑ e ∈ A, x e ∧ ∑ e ∈ A, x e ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ e ∈ B, x e ∧ ∑ e ∈ B, x e ≤ 1 + eta)
    (hxC : ∑ e ∈ C, x e ≤ 2 * r + eta) :
    p + 1.47e-16 < μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have P := H.pairData hx μ hμ hu hv huv
  have hw : LawData μ.prob (n - 2 + 1) := ⟨P.stable, P.rank, μ.weightNonneg, μ.total⟩
  have hcount : (FiberTreeModel.id n).TwoAtomOneHotData μ.prob u v :=
    FiberTreeModel.TwoAtomOneHotData.ofSupport (FiberTreeModel.treeSupport_id P.tree)
      P.une P.vne P.disj
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  have hmass := lemma_5_22_indexed (FiberTreeModel.id n) hw P.disj hcount
    (A := A) (B := B) (C := C) (by rw [FiberTreeModel.id_fiberOver]; exact hpart)
    hAB hAC hBC heta hcap
    (by rw [FiberTreeModel.id_fiberOver]; linarith only [P.deficiency, heta])
    (by rw [FiberTreeModel.id_fiberOver, P.bundle]; exact hxE)
    (by rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA)
    (by rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB)
    (by rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC)
    (by rw [FiberTreeModel.id_fiberOver]; exact ⟨P.dv1, P.dv2⟩)
  rw [← weightMass_treeDist]
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using hmass

/-- The lifted large-bundle bound retains an explicit strict surplus over `p`. -/
theorem lemma_5_22_liftProb_margin {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : 1 / 2 + h ≤ pairSum x u v)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta) :
    p + 1.47e-16 < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) := by
  have P := R.refinedPairData hμ (H.pairData hx μ hμ hu hv huv)
  have hw : LawData (R.liftProb μ) (n - 2 + 1) :=
    ⟨P.stable, P.rank, R.liftProb_weightNonneg μ, R.liftProb_totalMass μ⟩
  have hcount : R.model.TwoAtomOneHotData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomOneHotData.ofSupport P.support P.une P.vne P.disj
  have hmass := lemma_5_22_indexed R.model hw P.disj hcount
    (A := A) (B := B) (C := C) (by rw [R.model_fiberOver]; exact hpart)
    hAB hAC hBC heta hcap
    (by rw [R.model_fiberOver]; linarith only [P.deficiency, heta])
    (by rw [R.model_fiberOver, P.bundle]; exact hxE)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxC)
    (by rw [R.model_fiberOver]; exact ⟨P.dv1, P.dv2⟩)
  unfold EdgeRefinement.TwoOneOneHappyOn
  simpa only [R.model_fiberOver, R.model_project] using hmass

/-- A large bundle is two-one-one good at Song's common probability. -/
theorem lemma_5_22_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : 1 / 2 + h ≤ pairSum x u v)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta) :
    R.IsTwoOneOneGoodOn μ p u v A B C := by
  have hmass := lemma_5_22_liftProb_margin hx μ hμ H heta hcap R hu hv huv
    hpart hAB hAC hBC hxE hxA hxB hxC
  unfold EdgeRefinement.IsTwoOneOneGoodOn
  linarith only [hmass]

/-- The common probability at the actual seven-times hierarchy error. -/
theorem lemma_5_22_liftProb_seven_mul {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : 1 / 2 + h ≤ pairSum x u v)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * s)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * s)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * s) :
    R.IsTwoOneOneGoodOn μ p u v A B C := by
  have hcap : 7 * s ≤ d₀ / 2 := by
    have hH : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
    linarith only [hsH, hH]
  exact lemma_5_22_liftProb hx μ hμ H (by positivity) hcap R hu hv huv
    hpart hAB hAC hBC hxE hxA hxB hxC

end TSPGap.Song

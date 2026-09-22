/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDistSetup
import TSPGap.Lemma521
import TSPGap.Lemma522

/-!
# Lemmas 5.21 and 5.22 for a max-entropy tree distribution

The `TreeDist`-facing instances over `PairData`: a top bundle `e = E(v,u)`
between two children of a hierarchy cut that is not a half bundle is 2-1-1
happy with respect to `v` with probability `≥ 0.005ε₂²` (`x_e ≤ 1/2 − ε₂`)
or `≥ 0.005ε₂²` (`x_e ≥ 1/2 + ε₂`).  Together (`non_half_two_one_one`) they
discharge Theorem 5.28's input `h2122` at `p = 0.005ε₂²`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- **Lemma 5.21 for a max-entropy tree distribution.** -/
theorem lemma_5_21_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : pairSum x u v ≤ 1 / 2 - ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    0.005 * ε₂ ^ 2 ≤ μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have D := H.pairData hx μ hμ hu hv huv
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist]
  refine lemma_5_21 D.stable D.rank μ.weightNonneg μ.total D.tree D.une D.vne D.disj hpart hAB
    hAC hBC hεη hε₂ hε₂cap hεηsq (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE)
    ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC

/-- **Lemma 5.22 for a max-entropy tree distribution.** -/
theorem lemma_5_22_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : 1 / 2 + ε₂ ≤ pairSum x u v)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    0.005 * ε₂ ^ 2 ≤ μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have D := H.pairData hx μ hμ hu hv huv
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist]
  refine lemma_5_22 D.stable D.rank μ.weightNonneg μ.total D.tree D.une D.vne D.disj hpart hAB
    hAC hBC hεη hε₂ hε₂cap hεηsq (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE)
    ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC

/-- Capacity-strengthened hierarchy instance; the old statement is unchanged. -/
theorem lemma_5_21_treeDist_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : pairSum x u v ≤ 1 / 2 - ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    0.04 * ε₂ ^ 2 ≤ μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have D := H.pairData hx μ hμ hu hv huv
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist]
  refine lemma_5_21_capacity D.stable D.rank μ.weightNonneg μ.total D.tree D.une D.vne D.disj hpart hAB
    hAC hBC hεη hε₂ hε₂cap hεηsq (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE)
    ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC

/-- Capacity-strengthened hierarchy instance; the old statement is unchanged. -/
theorem lemma_5_22_treeDist_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : 1 / 2 + ε₂ ≤ pairSum x u v)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    0.026 * ε₂ ^ 2 ≤ μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have D := H.pairData hx μ hμ hu hv huv
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist]
  refine lemma_5_22_capacity D.stable D.rank μ.weightNonneg μ.total D.tree D.une D.vne D.disj hpart hAB
    hAC hBC hεη hε₂ hε₂cap hεηsq (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE)
    ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC

end TSPGap

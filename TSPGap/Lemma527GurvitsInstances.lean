/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDistInstances

/-!
# Lemma 5.27 at the first Gurvits budget: hierarchy instances

The ordinary-tree instance of the enlarged-threshold theorem. The piece
instance lives separately in `RefinedLemma527`; this file does not import
the piece/thinning setup. The old instances remain unchanged. No global
thinning mass or gap constant is selected here.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- The enlarged not-good threshold `0.02 ε₂²` has fallback happy mass
at least `0.0005` for three children of a hierarchy cut. -/
theorem lemma_5_27_gurvits_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    (hxEB : ∑ e ∈ betweenEdges u v ∩ B, x e ≤ ε₂)
    (hxFA : ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂)
    (hgoodE : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2))
    (hnotgoodE : μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges u).card = 2 ∧ InducesTree v T ∧ InducesTree u T) < 0.02 * ε₂ ^ 2)
    (hnotgoodF : μ.probEvent (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges z).card = 2 ∧ InducesTree v T ∧ InducesTree z T) < 0.02 * ε₂ ^ 2) :
    0.0005 ≤ μ.probEvent (fun T =>
      (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
        ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T) := by
  have D := H.tripleData hx μ hμ hu hv hz huv hvz huz
  have hAcut : A ⊆ cutEdges v := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges v := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges v := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist] at hnotgoodE hnotgoodF
  rw [← weightMass_treeDist]
  refine lemma_5_27_gurvits D.uv.stable D.uv.rank μ.weightNonneg μ.total D.uv.tree D.uv.une D.uv.vne
    D.vz.vne D.uv.disj D.vz.disj D.uz.disj D.uv.symm.proper D.vz.proper hpart hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq (by linarith [D.deficiency3]) (by linarith [D.uv.symm.deficiency])
    (by linarith [D.vz.deficiency]) (by rw [D.uv.bundle]; exact hxE)
    (by rw [D.vz.bundle]; exact hxF) ?_ ?_ ?_ ?_ ?_ ?_ ?_ D.uv.du1 D.uv.du2 D.vz.dv1 D.vz.dv2
    hgoodE hgoodF hnotgoodE hnotgoodF
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC
  · rw [expCard_prob_of_subset_cut μ (Finset.inter_subset_right.trans hBcut)]; exact hxEB
  · rw [expCard_prob_of_subset_cut μ (Finset.inter_subset_right.trans hAcut)]; exact hxFA

end TSPGap

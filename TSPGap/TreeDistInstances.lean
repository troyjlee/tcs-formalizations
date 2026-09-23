/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDistSetup
import TSPGap.Lemma517
import TSPGap.Lemma523
import TSPGap.LemmaA1Assembly
import TSPGap.Lemma524Assembly
import TSPGap.Lemma527

/-!
# Lemmas 5.17, 5.23, 5.24, 5.27 and A.1 for a max-entropy tree distribution

The `TreeDist`-facing instances of the §5 lemmas, each for a subtour-LP point
`x`, a max-entropy limit `μ : TreeDist n x`, a hierarchy `H` at near-min-cut
parameter `ε_η`, and children of a cut `S ∈ H` as the atoms, with the bundle
between two children being the **full** between set.  Everything the abstract
lemmas ask of the law is drawn from `PairData`/`TripleData`
(`TreeDistSetup.lean`), so the instances are pure assembly.

What remains paper-side is Definition 5.18 (the degree partitioning
`A ⊔ B ⊔ C` with its `x`-bounds), which enters 5.23, 5.24, 5.27 and A.1 as
explicit hypotheses in `∑ x` form, and the goodness / non-goodness inputs
(Lemmas 5.15–5.17, 5.23) of 5.24, 5.27 and A.1.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- **Lemma 5.17 for a max-entropy tree distribution.** -/
theorem lemma_5_17_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0005)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂) :
    (0.0015 : ℝ) ≤ weightMass
      (faceDist μ.prob (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z))
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)
    ∨ (0.0015 : ℝ) ≤ weightMass
      (faceDist μ.prob (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z))
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2) := by
  have D := H.tripleData hx μ hμ hu hv hz huv hvz huz
  refine lemma_5_17 D.uv.stable D.uv.rank μ.weightNonneg μ.total D.uv.tree D.uv.une D.uv.vne
    D.vz.vne D.uv.disj D.vz.disj D.uz.disj (supportComplete_betweenEdges μ.prob u v)
    (supportComplete_betweenEdges μ.prob v z) hεη hε₂ hεηcap hε₂cap (by linarith [D.deficiency3])
    (by rw [D.uv.bundle]; exact hxE) (by rw [D.vz.bundle]; exact hxF)
    D.uv.du1 D.uv.du2 D.uv.dv1 D.uv.dv2 D.vz.dv1 D.vz.dv2

/-- **Lemma 5.23's tail layer for a max-entropy tree distribution.** -/
theorem lemma_5_23_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A : Finset (Sym2 (Fin n))} (hA : A ⊆ cutEdges v)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0005)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hD : ∑ e ∈ (A \ betweenEdges u v) \ betweenEdges v z, x e ≤ 0.00201) :
    (0.02 : ℝ) ≤ μ.probEvent (fun T =>
        (T ∩ (A \ betweenEdges u v)).card + (T ∩ (cutEdges u \ betweenEdges u v)).card ≤ 1)
    ∨ (0.02 : ℝ) ≤ μ.probEvent (fun T =>
        (T ∩ (A \ betweenEdges v z)).card + (T ∩ (cutEdges z \ betweenEdges v z)).card ≤ 1) := by
  have D := H.tripleData hx μ hμ hu hv hz huv hvz huz
  rw [← weightMass_treeDist, ← weightMass_treeDist]
  refine lemma_5_23_core D.uv.stable D.uv.rank μ.weightNonneg μ.total D.uv.tree D.uv.une D.uv.vne
    D.vz.vne D.uv.disj D.vz.disj D.uz.disj (Finset.Subset.refl _) (Finset.Subset.refl _) hA
    hεη hε₂ hεηcap hε₂cap (by linarith [D.deficiency3]) (by rw [D.uv.bundle]; exact hxE)
    (by rw [D.vz.bundle]; exact hxF) D.uv.du2 D.vz.dv2 ?_
  rw [expCard_prob_of_subset_cut μ (Finset.sdiff_subset.trans (Finset.sdiff_subset.trans hA))]
  exact hD

/-- **Lemma A.1 for a max-entropy tree distribution, with the paper's `5ε` tail.** -/
theorem lemma_A1_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001) (hεηsq : εη ≤ ε ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε / 6 + εη)
    (hxBE : ∑ e ∈ B ∩ betweenEdges u v, x e ≤ ε)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (htail : 5 * ε ≤ μ.probEvent (fun T =>
      (T ∩ (A \ betweenEdges u v)).card + (T ∩ (cutEdges v \ betweenEdges u v)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have D := H.pairData hx μ hμ hu hv huv
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist] at htail
  rw [← weightMass_treeDist]
  refine lemma_A1 D.stable D.rank μ.weightNonneg μ.total D.tree D.une D.vne D.disj D.proper
    (supportComplete_betweenEdges μ.prob u v) hpart hAB hAC hBC hεη hε0 hεcap hεηsq
    (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE) ?_ ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2
    hgood htail
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC
  · rw [expCard_prob_of_subset_cut μ (Finset.inter_subset_left.trans hBcut)]; exact hxBE

/-- **Lemma 5.24 for a max-entropy tree distribution.** -/
theorem lemma_5_24_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001) (hεηsq : εη ≤ ε ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε / 6 + εη)
    (hxAEge : ε ≤ ∑ e ∈ A ∩ betweenEdges u v, x e)
    (hxBEge : ε ≤ ∑ e ∈ B ∩ betweenEdges u v, x e)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) :
    0.02 * ε ^ 2 ≤ μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have D := H.pairData hx μ hμ hu hv huv
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  rw [← weightMass_treeDist]
  refine lemma_5_24 μ hμ D.tree D.rank D.une D.vne D.disj D.proper
    (supportComplete_betweenEdges μ.prob u v) (Finset.Subset.refl _) hpart hAB hAC hBC
    hεη hε0 hεcap hεηsq (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2 hgood
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC
  · rw [expCard_prob_of_subset_cut μ (Finset.inter_subset_left.trans hAcut)]; exact hxAEge
  · rw [expCard_prob_of_subset_cut μ (Finset.inter_subset_left.trans hBcut)]; exact hxBEge

/-- **Lemma 5.27 for a max-entropy tree distribution.**  Atoms `u, v, z` are
children of a cut of the hierarchy, `e = E(u,v)`, `f = E(v,z)`, and
`δ(v) = A ⊔ B ⊔ C` is the degree partition. -/
theorem lemma_5_27_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
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
        ∧ (T ∩ cutEdges u).card = 2 ∧ InducesTree v T ∧ InducesTree u T) < 0.005 * ε₂ ^ 2)
    (hnotgoodF : μ.probEvent (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges z).card = 2 ∧ InducesTree v T ∧ InducesTree z T) < 0.005 * ε₂ ^ 2) :
    0.005 ≤ μ.probEvent (fun T =>
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
  refine lemma_5_27 D.uv.stable D.uv.rank μ.weightNonneg μ.total D.uv.tree D.uv.une D.uv.vne
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

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDistInstances
import TSPGap.Theorem528Defs

/-!
# Lemma 5.23's stronger happy-event budget

Lemma 5.23 already supplies an ambient small-count tail of 0.02.
At epsilon <= 0.0002 this meets the parameterized Lemma A.1 hypothesis
with ell = 99.75, giving 0.1187 epsilon^2 happy mass. No mean or
conditioning estimate is changed. Both orientations retain the full
A.1 assumptions; the tail alone does not imply the happy event.

The old public declarations are untouched. This module does not change
the common thinning probability or the end-to-end gap constant.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- The constant tail from 5.23 supplies the A.1 budget at the full epsilon cap. -/
theorem lemma_A1_two_percent_tail_budget {ε : ℝ} (hε : ε ≤ 0.0002) :
    (99.75 + 0.25) * ε ≤ 0.02 := by
  linarith

/-- The parameterized A.1 conclusion clears the rounded happy coefficient. -/
theorem lemma_A1_two_percent_happy_budget (ε : ℝ) :
    0.1187 * ε ^ 2 ≤ 0.00119 * 99.75 * ε ^ 2 := by
  nlinarith only [sq_nonneg ε]

/-- A.1 with the two-percent tail furnished by 5.23, on any fiber model. -/
theorem lemma_A1_indexed_of_tail_two_percent {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    (hcount : M.TwoAtomCrossData w u v)
    {E A B C : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.0002)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v)))
    (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : (0.02 : ℝ) ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    0.1187 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  have h := lemma_A1_indexed_budget M hst hr hnn htot hune hvne huv huvp hcount hSC
    hpart hAB hAC hBC hεη hε0 (by linarith) (ℓ := 99.75) (by norm_num) (by norm_num)
    hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE hdv1 hdv2 hgood
    (le_trans (lemma_A1_two_percent_tail_budget hεcap) htail)
  exact (lemma_A1_two_percent_happy_budget ε).trans h

/-- The ordinary-edge instance, retaining all topology and support hypotheses. -/
theorem lemma_A1_of_tail_two_percent {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    {E A B C : Finset (Sym2 (Fin n))} (hSC : SupportComplete w E u v)
    (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.0002)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (cutEdges v)) (hdv2 : expCard w (cutEdges v) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau w u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (htail : (0.02 : ℝ) ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (cutEdges v \ E)).card ≤ 1)) :
    0.1187 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcount : (FiberTreeModel.id n).TwoAtomCrossData w u v :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hune hvne huv huvp
  have h := lemma_A1_indexed_of_tail_two_percent (FiberTreeModel.id n) hst hr hnn htot hune hvne huv huvp hcount
    (E := E) (A := A) (B := B) (C := C) (FiberTreeModel.supportComplete_id hSC)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε0 hεcap hεηsq
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef) hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE
    (by rw [FiberTreeModel.id_fiberOver]; exact hdv1) (by rw [FiberTreeModel.id_fiberOver]; exact hdv2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgood)
    (by simpa only [FiberTreeModel.id_fiberOver] using htail)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

variable {x : Sym2 (Fin n) → ℝ}

/-- A.1 at the two-percent tail for a max-entropy tree law. -/
theorem lemma_A1_treeDist_of_tail_two_percent {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.0002) (hεηsq : εη ≤ ε ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε / 6 + εη)
    (hxBE : ∑ e ∈ B ∩ betweenEdges u v, x e ≤ ε)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (htail : (0.02 : ℝ) ≤ μ.probEvent (fun T =>
      (T ∩ (A \ betweenEdges u v)).card + (T ∩ (cutEdges v \ betweenEdges u v)).card ≤ 1)) :
    0.1187 * ε ^ 2 ≤ μ.probEvent (fun T =>
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
  refine lemma_A1_of_tail_two_percent D.stable D.rank μ.weightNonneg μ.total D.tree D.une D.vne D.disj D.proper
    (supportComplete_betweenEdges μ.prob u v) hpart hAB hAC hBC hεη hε0 hεcap hεηsq
    (by linarith [D.deficiency]) (by rw [D.bundle]; exact hxE) ?_ ?_ ?_ ?_ ?_ ?_ D.dv1 D.dv2
    hgood htail
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA1
  · rw [expCard_prob_of_subset_cut μ hAcut]; exact hxA2
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB1
  · rw [expCard_prob_of_subset_cut μ hBcut]; exact hxB2
  · rw [expCard_prob_of_subset_cut μ hCcut]; exact hxC
  · rw [expCard_prob_of_subset_cut μ (Finset.inter_subset_left.trans hBcut)]; exact hxBE

/-- **Lemma 5.23's happy-event conclusion at the enlarged budget.**
Both bundles have small B-parts and are 2-2 good. The existing tail
alternative followed by A.1 gives the stronger conclusion in either
orientation. The common partition is never swapped implicitly. -/
theorem lemma_5_23_happy_treeDist {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2)
    (hxE : |pairSum x v u - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    (hxBE : ∑ e ∈ B ∩ betweenEdges v u, x e ≤ ε₂)
    (hxBF : ∑ e ∈ B ∩ betweenEdges v z, x e ≤ ε₂)
    (hD : ∑ e ∈ (A \ betweenEdges u v) \ betweenEdges v z, x e ≤ 0.00201)
    (hgoodE : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2)) :
    IsTwoOneOneGood μ (0.1187 * ε₂ ^ 2) v u A B C
      ∨ IsTwoOneOneGood μ (0.1187 * ε₂ ^ 2) v z A B C := by
  have hεηcap : εη ≤ 0.0000005 := by nlinarith
  have hA : A ⊆ cutEdges v := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hxE' : |pairSum x u v - 1 / 2| ≤ ε₂ := by
    rw [pairSum_comm x u v]; exact hxE
  rcases lemma_5_23_treeDist hx μ hμ H hu hv hz huv hvz huz hA hεη hε₂
    hεηcap (by linarith) hxE' hxF hD with hE | hF
  · left
    rw [betweenEdges_comm u v] at hE
    exact lemma_A1_treeDist_of_tail_two_percent hx μ hμ H hv hu huv.symm
      hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE hgoodE hE
  · right
    exact lemma_A1_treeDist_of_tail_two_percent hx μ hμ H hv hz hvz
      hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxF hxA1 hxA2 hxB1 hxB2 hxC hxBF hgoodF hF

end TSPGap

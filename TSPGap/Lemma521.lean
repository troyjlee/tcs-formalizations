/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma521Indexed

/-!
# Capacity-strengthened Lemma 5.21

The `_capacity` export gives `0.04ε₂²`, by instantiating
`lemma_5_21_indexed_capacity` at the identity fiber tree model.
Spanning-tree support supplies the two-atom count certificate.

The original `0.005ε₂²` statement is retained as a weakening wrapper.
This local improvement does not change the global thinning parameter.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- **KKO21 Lemma 5.21.** -/
theorem lemma_5_21_capacity {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : expCard w (betweenEdges u v) ≤ 1 / 2 - ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hdv1 : 2 ≤ expCard w (cutEdges v)) (hdv2 : expCard w (cutEdges v) ≤ 2 + εη) :
    0.04 * ε₂ ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcount : (FiberTreeModel.id n).TwoAtomCountData w u v :=
    FiberTreeModel.TwoAtomCountData.ofSupport hsupp hune hvne huv
  have h := lemma_5_21_indexed_capacity (FiberTreeModel.id n) hst hr hnn htot hune hvne huv hcount
    (A := A) (B := B) (C := C) (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq (by rw [FiberTreeModel.id_fiberOver]; exact hdef)
    (by rw [FiberTreeModel.id_fiberOver]; exact hxE) hxA1 hxA2 hxB1 hxB2 hxC
    (by rw [FiberTreeModel.id_fiberOver]; exact hdv1) (by rw [FiberTreeModel.id_fiberOver]; exact hdv2)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

/-- The original threshold, with its public statement unchanged. -/
theorem lemma_5_21 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : expCard w (betweenEdges u v) ≤ 1 / 2 - ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hdv1 : 2 ≤ expCard w (cutEdges v)) (hdv2 : expCard w (cutEdges v) ≤ 2 + εη) :
    0.005 * ε₂ ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  have h := lemma_5_21_capacity hst hr hnn htot htree hune hvne huv
    hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hdv1 hdv2
  nlinarith only [h, sq_nonneg ε₂]

end TSPGap

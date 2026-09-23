/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527SetupIndexed
import TSPGap.Lemma524Indexed
import TSPGap.Lemma527BudgetCore

/-!
# KKO21 Lemma 5.27, the `Z`-absent case, over a fiber tree model

The second checkpoint of Lemma 5.27's port: `lemma_5_27_absent_indexed`, the
`Z`-absent case for a weight on `Finset ι` over a fiber tree model `M`.  The
laws are the three-atom face `M.tau3`, then `M.l527Sigma` (the avoided set
`M.l527R = Z ∪ C ∪ e(B) ∪ f` read through `M.fiberOver`), then `M.l527Law`
(`e` present).  The graph is read only through the certificate
`ThreeAtomUzData`: the face count and its count-to-tree conversion, and the
one-hot property of `e` under three trees. The `_of_defect` version allows
`ε' ≤ 38ε₂` and keeps the conditioning masses and failure bounds
cross-multiplied. The original `lemma_5_27_absent_indexed` is a wrapper at
the old defect cap, retaining its `0.005` conclusion. `Lemma527Absent.lean`
is the identity-model instance, with its original statement unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

namespace FiberTreeModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)

/-- The avoided set of Lemma 5.27: `Z ∪ C ∪ e(B) ∪ f`. -/
def l527R (B C : Finset ι) (u v z : Finset (Fin n)) : Finset ι :=
  M.fiberOver (betweenEdges u z) ∪ C ∪ (M.fiberOver (betweenEdges u v) ∩ B)
    ∪ M.fiberOver (betweenEdges v z)

/-- The three-atom face law with `Z ∪ C ∪ e(B) ∪ f` avoided. -/
noncomputable def l527Sigma (w : Finset ι → ℝ) (B C : Finset ι) (u v z : Finset (Fin n)) :
    Finset ι → ℝ :=
  avoidDist (M.tau3 w u v z) (M.l527R B C u v z)

/-- The law `E` of Lemma 5.27: additionally `e` present. -/
noncomputable def l527Law (w : Finset ι → ℝ) (B C : Finset ι) (u v z : Finset (Fin n)) :
    Finset ι → ℝ :=
  faceDist (M.l527Sigma w B C u v z) (indicatorCost (M.fiberOver (betweenEdges u v))) 1

end FiberTreeModel

set_option maxHeartbeats 16000000 in
-- One declaration carries the whole chain (three laws, sandwich, core, unwinding).
/-- **Lemma 5.27, the `Z`-absent case, over a fiber tree model.** -/
theorem lemma_5_27_absent_indexed_of_defect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hcert : M.ThreeAtomUzData w u v z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ ε' : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2) (hε' : 0 ≤ ε') (hε'cap : ε' ≤ 38 * ε₂)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z)) (atomBudget u v z) ≤ 3 * εη)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ ε₂)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ ε₂)
    (h56U : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2))
    (h56W : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2))
    (hZ : expCard (M.tau3 w u v z) (M.fiberOver (betweenEdges u z)) ≤ 3 * ε') :
    0.068 * ((0.4995 - 3 * ε') * 0.4995) - 2 * ε' ≤ weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) := by
  classical
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hε'cap' : ε' ≤ 0.0076 := by linarith
  have hxE' := abs_le.mp hxE
  have hxF' := abs_le.mp hxF
  /- ### Sets -/
  have hAcv : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcv : B ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcv : C ⊆ M.fiberOver (cutEdges v) := by rw [hpart]; exact Finset.subset_union_right
  have hEcu : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEcv : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hFcv : M.fiberOver (betweenEdges v z) ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left hvz)
  have hFcz : M.fiberOver (betweenEdges v z) ⊆ M.fiberOver (cutEdges z) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges hvz)
  have hZcu : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huz)
  have hZcz : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges z) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huz)
  have hZv : Disjoint (M.fiberOver (betweenEdges u z)) (M.fiberOver (cutEdges v)) :=
    M.disjoint_fiberOver (betweenEdges_disjoint_cutEdges huv hvz.symm)
  have hEz : Disjoint (M.fiberOver (betweenEdges u v)) (M.fiberOver (cutEdges z)) :=
    M.disjoint_fiberOver (betweenEdges_disjoint_cutEdges huz hvz)
  have hFu : Disjoint (M.fiberOver (betweenEdges v z)) (M.fiberOver (cutEdges u)) :=
    M.disjoint_fiberOver (betweenEdges_disjoint_cutEdges huv.symm huz.symm)
  have hEF : Disjoint (M.fiberOver (betweenEdges u v)) (M.fiberOver (betweenEdges v z)) :=
    M.disjoint_fiberOver (bundle_disjoint huv huz)
  have hZE : Disjoint (M.fiberOver (betweenEdges u z)) (M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_right hEcv hZv
  have hZF : Disjoint (M.fiberOver (betweenEdges u z)) (M.fiberOver (betweenEdges v z)) :=
    Finset.disjoint_of_subset_right hFcv hZv
  have hZC : Disjoint (M.fiberOver (betweenEdges u z)) C := Finset.disjoint_of_subset_right hCcv hZv
  have hZA : Disjoint (M.fiberOver (betweenEdges u z)) A := Finset.disjoint_of_subset_right hAcv hZv
  have hZB : Disjoint (M.fiberOver (betweenEdges u z)) B := Finset.disjoint_of_subset_right hBcv hZv
  have hcuv : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := (Finset.mem_sdiff.mp he)
    have h2 := (Finset.mem_sdiff.mp he')
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  have hczv : Disjoint (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges v z)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := (Finset.mem_sdiff.mp he)
    have h2 := (Finset.mem_sdiff.mp he')
    exact h1.2 (by rw [← cutEdges_inter_cutEdges hvz, M.fiberOver_inter, Finset.inter_comm]; exact Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  -- the four cells
  have hUA : Disjoint (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
      (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))) := by
    refine Finset.disjoint_of_subset_left ?_ (Finset.disjoint_of_subset_right ?_ hcuv)
    · intro e he; obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨h1, fun h => h2 (Finset.mem_union_left _ h)⟩
    · intro e he; obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨hAcv h1, fun h => h2 (Finset.mem_union_left _ h)⟩
  have hWB : Disjoint (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
      (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))) := by
    refine Finset.disjoint_of_subset_left ?_ (Finset.disjoint_of_subset_right ?_ hczv)
    · intro e he; obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨h1, fun h => h2 (Finset.mem_union_left _ h)⟩
    · intro e he; obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨hBcv h1, fun h => h2 (Finset.mem_union_left _ h)⟩
  have hA''B'' : Disjoint (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))
      (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset hAB)
  -- cells versus the avoided set and the bundle `e`
  have hRsub : ∀ S : Finset ι, Disjoint S (M.fiberOver (betweenEdges u z)) → Disjoint S C →
      Disjoint S (M.fiberOver (betweenEdges u v) ∩ B) → Disjoint S (M.fiberOver (betweenEdges v z)) →
      Disjoint S (M.l527R B C u v z) := fun S h1 h2 h3 h4 =>
    Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨h1, h2⟩, h3⟩, h4⟩
  have hU''R : Disjoint (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z))) (M.l527R B C u v z) := by
    refine hRsub _ ?_ ?_ ?_ ?_
    · refine Finset.disjoint_left.mpr fun e he hz => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ hz)
    · refine Finset.disjoint_left.mpr fun e he hc => ?_
      have h1 := Finset.mem_sdiff.mp he
      exact h1.2 (Finset.mem_union_left _ (by
        rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, hCcv hc⟩))
    · refine Finset.disjoint_left.mpr fun e he hc => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ (Finset.mem_inter.mp hc).1)
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hFu.symm
  have hA''R : Disjoint (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))) (M.l527R B C u v z) := by
    refine hRsub _ ?_ ?_ ?_ ?_
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hZA.symm
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hAC
    · refine Finset.disjoint_left.mpr fun e he hc => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ (Finset.mem_inter.mp hc).1)
    · refine Finset.disjoint_left.mpr fun e he hf => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ hf)
  have hW''R : Disjoint (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z))) (M.l527R B C u v z) := by
    refine hRsub _ ?_ ?_ ?_ ?_
    · refine Finset.disjoint_left.mpr fun e he hz => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ hz)
    · refine Finset.disjoint_left.mpr fun e he hc => ?_
      have h1 := Finset.mem_sdiff.mp he
      exact h1.2 (Finset.mem_union_left _ (by
        rw [← cutEdges_inter_cutEdges hvz, M.fiberOver_inter, Finset.inter_comm]
        exact Finset.mem_inter.mpr ⟨h1.1, hCcv hc⟩))
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hEz.symm)
    · refine Finset.disjoint_left.mpr fun e he hf => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hf)
  have hB''R : Disjoint (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))) (M.l527R B C u v z) := by
    refine hRsub _ ?_ ?_ ?_ ?_
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hZB.symm
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hBC
    · refine Finset.disjoint_left.mpr fun e he hc => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ (Finset.mem_inter.mp hc).1)
    · refine Finset.disjoint_left.mpr fun e he hf => ?_
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hf)
  have hU''E : Disjoint (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z))) (M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ h)
  have hA''E : Disjoint (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))) (M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ h)
  have hW''E : Disjoint (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z))) (M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hEz.symm
  have hB''E : Disjoint (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))) (M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ h)
  have hEAR : Disjoint (M.fiberOver (betweenEdges u v) ∩ A) (M.l527R B C u v z) := by
    refine hRsub _ ?_ ?_ ?_ ?_
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_left hZE.symm
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right hAC
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB)
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_left hEF
  -- the complement of the internal edges
  have hcu : M.fiberOver (cutEdges u) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom (cutEdges_disjoint_internalEdges_self u)
      (cutEdges_disjoint_internalEdges huv) (cutEdges_disjoint_internalEdges huz))
  have hcv : M.fiberOver (cutEdges v) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom (cutEdges_disjoint_internalEdges huv.symm)
      (cutEdges_disjoint_internalEdges_self v) (cutEdges_disjoint_internalEdges hvz))
  have hcz : M.fiberOver (cutEdges z) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom (cutEdges_disjoint_internalEdges huz.symm)
      (cutEdges_disjoint_internalEdges hvz.symm) (cutEdges_disjoint_internalEdges_self z))
  /- ### `x`-level facts -/
  -- `x(e ∩ A) ≥ x(e) − x(e ∩ B) − x(C)`
  have hEsplit : M.fiberOver (betweenEdges u v) ⊆ (M.fiberOver (betweenEdges u v) ∩ A) ∪ (M.fiberOver (betweenEdges u v) ∩ B) ∪ C := by
    intro e he
    have := hEcv he
    rw [hpart] at this
    rcases Finset.mem_union.mp this with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, h⟩))
    · exact Finset.mem_union_right _ h
  have hxEA : 1 / 2 - 2 * ε₂ - ε₂ / 6 - εη ≤ expCard w (M.fiberOver (betweenEdges u v) ∩ A) := by
    have h1 := expCard_mono hnn hEsplit
    have h2 := expCard_union_le hnn ((M.fiberOver (betweenEdges u v) ∩ A) ∪ (M.fiberOver (betweenEdges u v) ∩ B)) C
    have h3 := expCard_union_le hnn (M.fiberOver (betweenEdges u v) ∩ A) (M.fiberOver (betweenEdges u v) ∩ B)
    linarith
  have hFsplit : M.fiberOver (betweenEdges v z) ⊆ (M.fiberOver (betweenEdges v z) ∩ A) ∪ (M.fiberOver (betweenEdges v z) ∩ B) ∪ C := by
    intro e he
    have := hFcv he
    rw [hpart] at this
    rcases Finset.mem_union.mp this with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, h⟩))
    · exact Finset.mem_union_right _ h
  have hxFB : 1 / 2 - 2 * ε₂ - ε₂ / 6 - εη ≤ expCard w (M.fiberOver (betweenEdges v z) ∩ B) := by
    have h1 := expCard_mono hnn hFsplit
    have h2 := expCard_union_le hnn ((M.fiberOver (betweenEdges v z) ∩ A) ∪ (M.fiberOver (betweenEdges v z) ∩ B)) C
    have h3 := expCard_union_le hnn (M.fiberOver (betweenEdges v z) ∩ A) (M.fiberOver (betweenEdges v z) ∩ B)
    linarith
  -- `x(A ∖ e) ≤ 1/2 + 2.17ε₂ + 2εη`, `x(B ∖ f)` likewise
  have hxAe : expCard w (A \ M.fiberOver (betweenEdges u v)) ≤ 1 / 2 + 2.17 * ε₂ + 2 * εη := by
    have h : A \ M.fiberOver (betweenEdges u v) = A \ (A ∩ M.fiberOver (betweenEdges u v)) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left, Finset.inter_comm]
    linarith
  have hxBf : expCard w (B \ M.fiberOver (betweenEdges v z)) ≤ 1 / 2 + 2.17 * ε₂ + 2 * εη := by
    have h : B \ M.fiberOver (betweenEdges v z) = B \ (B ∩ M.fiberOver (betweenEdges v z)) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left, Finset.inter_comm]
    linarith
  -- `x(A ∖ (e ∪ f)) ≥ 1/2 − 2.09ε₂`
  have hxA'' : 1 / 2 - 2.09 * ε₂ ≤ expCard w (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))) := by
    have h : A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))
        = A \ ((A ∩ M.fiberOver (betweenEdges u v)) ∪ (A ∩ M.fiberOver (betweenEdges v z))) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]; tauto
    rw [h, expCard_sdiff_of_subset _ (Finset.union_subset Finset.inter_subset_left
      Finset.inter_subset_left)]
    have h1 := expCard_union_le hnn (A ∩ M.fiberOver (betweenEdges u v)) (A ∩ M.fiberOver (betweenEdges v z))
    have h2 := expCard_mono hnn (Finset.inter_subset_right (s₁ := A) (s₂ := M.fiberOver (betweenEdges u v)))
    have h3 : expCard w (A ∩ M.fiberOver (betweenEdges v z)) ≤ ε₂ := by rw [Finset.inter_comm]; exact hxFA
    linarith
  /- ### The face law `ν` -/
  have hsup : ∀ S, w S ≠ 0 →
      (S ∩ M.fiberOver (threeAtomInternal u v z)).card ≤ atomBudget u v z := fun S hS =>
    hcert.le S hS
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w
      (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) := by linarith
  have hnorm := fixedRankNormalized_faceDist (r := k + 1) hr hnn hmass
  have hνst : IsRealStable (genPoly (M.tau3 w u v z)) :=
    isRealStable_genPoly_maxFaceDist hst hr hnn hsup hmass
  have hνnn : WeightNonneg (M.tau3 w u v z) := hnorm.nonneg
  have hνtot : totalMass (M.tau3 w u v z) = 1 := hnorm.total
  have hνrank : FixedRankWeight (k + 1) (M.tau3 w u v z) := fun S hS => by
    by_contra hc; exact hS (hnorm.supported S hc)
  have hνw : ∀ S, M.tau3 w u v z S ≠ 0 → w S ≠ 0 := by
    intro S hS
    have hface := faceDist_ne_zero hS
    rw [faceWeight_indicatorCost_apply] at hface
    by_contra hc
    exact hface (by split <;> simp [hc])
  have hνsupp : ∀ T, M.tau3 w u v z T ≠ 0 → w T ≠ 0 ∧ InducesTree u (M.project T)
      ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T) := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hwT : w T ≠ 0 := hνw T hT
    have hcard : (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    exact ⟨hwT, (hcert.eq_iff T hwT).mp hcard⟩
  have hτ : ∀ S : Finset ι, S ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ →
      |expCard (M.tau3 w u v z) S - expCard w S| ≤ 3 * εη := fun S hS =>
    le_trans (abs_expCard_faceDist_sub_le hst hr hnn htot hsup hmass hS) hdef
  have hνoneE : ∀ S, M.tau3 w u v z S ≠ 0 → (S ∩ M.fiberOver (betweenEdges u v)).card ≤ 1 := fun S hS =>
    hcert.one_hot_uv S (hνsupp S hS).1 (hνsupp S hS).2.1 (hνsupp S hS).2.2.1
  -- unwinding at `ν`
  have hνunwind : ∀ P : Finset ι → Prop,
      weightMass (M.tau3 w u v z) P
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
      = weightMass w (fun T => P T
          ∧ (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z) := by
    intro P
    change weightMass (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) P
      * _ = _
    rw [weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_face]
  have hMface : 0.9999 ≤ totalMass (faceWeight w
      (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) := by linarith
  -- the (56) events at `ν`: `δ_ν = 1.001 ε'`
  have hν56U : 1 - 1.001 * ε' ≤ weightMass (M.tau3 w u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2) := by
    have h := cond_near_certain hnn hνtot hνunwind (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have h2 := weightMass_not_le hnn htot (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have h3 := weightMass_le_one hνnn hνtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    nlinarith
  have hν56W : 1 - 1.001 * ε' ≤ weightMass (M.tau3 w u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2) := by
    have h := cond_near_certain hnn hνtot hνunwind (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have h2 := weightMass_not_le hnn htot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have h3 := weightMass_le_one hνnn hνtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    nlinarith
  /- ### The avoided law `σ` -/
  have hνR : expCard (M.tau3 w u v z) (M.l527R B C u v z)
      ≤ 3 * ε' + (ε₂ / 6 + εη + 3 * εη) + (ε₂ + 3 * εη) + (1 / 2 + ε₂ + 3 * εη) := by
    have h1 := expCard_union_le hνnn ((M.fiberOver (betweenEdges u z) ∪ C) ∪ (M.fiberOver (betweenEdges u v) ∩ B))
      (M.fiberOver (betweenEdges v z))
    have h2 := expCard_union_le hνnn (M.fiberOver (betweenEdges u z) ∪ C) (M.fiberOver (betweenEdges u v) ∩ B)
    have h3 := expCard_union_le hνnn (M.fiberOver (betweenEdges u z)) C
    have hC' := abs_le.mp (hτ C (hCcv.trans hcv))
    have hEB' := abs_le.mp (hτ (M.fiberOver (betweenEdges u v) ∩ B) ((Finset.inter_subset_left.trans hEcv).trans hcv))
    have hF' := abs_le.mp (hτ (M.fiberOver (betweenEdges v z)) (hFcv.trans hcv))
    change expCard (M.tau3 w u v z)
      (((M.fiberOver (betweenEdges u z) ∪ C) ∪ (M.fiberOver (betweenEdges u v) ∩ B)) ∪ M.fiberOver (betweenEdges v z)) ≤ _
    linarith
  have hσMsharp : 0.49955 - 3 * ε' ≤ totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z)) := by
    rw [totalMass_avoidWeight]
    have := weightMass_eq_zero_ge hνnn hνtot (M.l527R B C u v z)
    linarith
  have hσM : 0.4767 ≤ totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z)) := by
    rw [totalMass_avoidWeight]
    have := weightMass_eq_zero_ge hνnn hνtot (M.l527R B C u v z)
    linarith
  have hσmass : 0 < totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z)) := by linarith
  have hσnorm := fixedRankNormalized_avoidDist hνrank hνnn hσmass
  have hσst : IsRealStable (genPoly (M.l527Sigma w B C u v z)) :=
    isRealStable_genPoly_avoidDist hνst hνrank hνnn hσmass
  have hσnn : WeightNonneg (M.l527Sigma w B C u v z) := hσnorm.nonneg
  have hσtot : totalMass (M.l527Sigma w B C u v z) = 1 := hσnorm.total
  have hσrank : FixedRankWeight (k + 1) (M.l527Sigma w B C u v z) := fun S hS => by
    by_contra hc; exact hS (hσnorm.supported S hc)
  have hσsupp : ∀ T, M.l527Sigma w B C u v z T ≠ 0 →
      M.tau3 w u v z T ≠ 0 ∧ (T ∩ M.l527R B C u v z).card = 0 := fun T hT =>
    avoidDist_ne_zero_imp hT
  have hσge : ∀ S : Finset ι, Disjoint S (M.l527R B C u v z) →
      expCard (M.tau3 w u v z) S ≤ expCard (M.l527Sigma w B C u v z) S := fun S hS =>
    expCard_avoidDist_ge hνst hνrank hνnn hνtot hS hσmass
  have hσunwind : ∀ P : Finset ι → Prop,
      weightMass (M.l527Sigma w B C u v z) P
        * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
          * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)))
      = weightMass w (fun T => P T ∧ ((T ∩ M.l527R B C u v z).card = 0
          ∧ (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z)) := by
    intro P
    rw [← mul_assoc]
    change weightMass (avoidDist (M.tau3 w u v z) (M.l527R B C u v z)) P * _ * _ = _
    rw [weightMass_avoidDist_mul hσmass, hνunwind]
    exact weightMass_congr fun T => by tauto
  have hMσsharp : 0.4995 - 3 * ε' ≤ totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) := by
    have hmul := mul_le_mul hσMsharp hMface (by norm_num)
      (show 0 ≤ totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        from hσmass.le)
    nlinarith only [hmul, hε']
  have hMσ : 0.4766 ≤ totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) := by
    linarith only [hMσsharp, hε'cap']
  -- support facts at `σ`
  have hσparts : ∀ T, M.l527Sigma w B C u v z T ≠ 0 →
      (T ∩ M.fiberOver (betweenEdges u z)).card = 0 ∧ (T ∩ C).card = 0
        ∧ (T ∩ (M.fiberOver (betweenEdges u v) ∩ B)).card = 0 ∧ (T ∩ M.fiberOver (betweenEdges v z)).card = 0 := by
    intro T hT
    have h := (hσsupp T hT).2
    have hZ0 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (show M.fiberOver (betweenEdges u z) ⊆ M.l527R B C u v z from
        Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)))
    have hC0 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (show C ⊆ M.l527R B C u v z from
        Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)))
    have hEB0 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (show M.fiberOver (betweenEdges u v) ∩ B ⊆ M.l527R B C u v z from
        Finset.subset_union_right.trans Finset.subset_union_left))
    have hF0 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (show M.fiberOver (betweenEdges v z) ⊆ M.l527R B C u v z from Finset.subset_union_right))
    omega
  -- the (56) events at `σ`, in cell form: `δ_σ = 2.10 ε'`
  have hσ56U : 1 - 2.10 * ε' ≤ weightMass (M.l527Sigma w B C u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2) := by
    have h := cond_near_certain hnn hσtot hσunwind (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have h2 := weightMass_not_le hnn htot (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have h3 := weightMass_le_one hσnn hσtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have hc : weightMass (M.l527Sigma w B C u v z) (fun T =>
        (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
        = weightMass (M.l527Sigma w B C u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
            + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2) := by
      refine weightMass_congr_of_support fun T hT => ?_
      obtain ⟨hZ0, -, -, hF0⟩ := hσparts T hT
      rw [inter_sdiff_union_eq_of_card_inter_zero hZ0, inter_sdiff_union_eq_of_card_inter_zero hF0]
    rw [← hc]
    nlinarith
  have hσ56W : 1 - 2.10 * ε' ≤ weightMass (M.l527Sigma w B C u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 2) := by
    have h := cond_near_certain hnn hσtot hσunwind (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have h2 := weightMass_not_le hnn htot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have h3 := weightMass_le_one hσnn hσtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have hc : weightMass (M.l527Sigma w B C u v z) (fun T =>
        (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
        = weightMass (M.l527Sigma w B C u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
            + (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 2) := by
      refine weightMass_congr_of_support fun T hT => ?_
      obtain ⟨hZ0, -, hEB0, -⟩ := hσparts T hT
      rw [inter_sdiff_union_eq_of_card_inter_zero hZ0]
      rw [inter_sdiff_union_eq_of_card_inter_inter_zero hEB0]
    rw [← hc]
    nlinarith
  /- ### The law `L`: `e` present -/
  have hσoneE : ∀ S, M.l527Sigma w B C u v z S ≠ 0 → (S ∩ M.fiberOver (betweenEdges u v)).card ≤ 1 :=
    fun S hS => hνoneE S (hσsupp S hS).1
  have hLM : totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      = expCard (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)) :=
    totalMass_presentWeight_eq_expCard hσoneE
  have hσE : 0.4995 ≤ expCard (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)) := by
    have h1 := expCard_mono hσnn (Finset.inter_subset_left (s₁ := M.fiberOver (betweenEdges u v)) (s₂ := A))
    have h2 := hσge _ hEAR
    have h3 := abs_le.mp (hτ (M.fiberOver (betweenEdges u v) ∩ A)
      ((Finset.inter_subset_left.trans hEcv).trans hcv))
    linarith
  have hLmass : 0 < totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v))) := by
    rw [hLM]; linarith
  have hLmass' : 0 < totalMass (faceWeight (M.l527Sigma w B C u v z)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) := hLmass
  have hLnorm := fixedRankNormalized_faceDist (r := k + 1) hσrank hσnn hLmass'
  have hLst : IsRealStable (genPoly (M.l527Law w B C u v z)) :=
    isRealStable_genPoly_maxFaceDist hσst hσrank hσnn hσoneE hLmass'
  have hLnn : WeightNonneg (M.l527Law w B C u v z) := hLnorm.nonneg
  have hLtot : totalMass (M.l527Law w B C u v z) = 1 := hLnorm.total
  have hLrank : FixedRankWeight (k + 1) (M.l527Law w B C u v z) := fun S hS => by
    by_contra hc; exact hS (hLnorm.supported S hc)
  have hLsupp : ∀ T, M.l527Law w B C u v z T ≠ 0 →
      M.l527Sigma w B C u v z T ≠ 0 ∧ (T ∩ M.fiberOver (betweenEdges u v)).card = 1 := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    by_cases hc : (T ∩ M.fiberOver (betweenEdges u v)).card = 1
    · rw [if_pos hc] at hface; exact ⟨hface, hc⟩
    · rw [if_neg hc] at hface; exact absurd rfl hface
  have hLle : ∀ S : Finset ι, Disjoint S (M.fiberOver (betweenEdges u v)) →
      expCard (M.l527Law w B C u v z) S ≤ expCard (M.l527Sigma w B C u v z) S := fun S hS =>
    expCard_presentDist_le hσst hσrank hσnn hσtot hσoneE hS hLmass
  have hLunwind : ∀ P : Finset ι → Prop,
      weightMass (M.l527Law w B C u v z) P
        * (totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
          * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
            * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
              (atomBudget u v z))))
      = weightMass w (fun T => P T ∧ ((T ∩ M.fiberOver (betweenEdges u v)).card = 1
          ∧ ((T ∩ M.l527R B C u v z).card = 0
            ∧ (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z))) := by
    intro P
    rw [← mul_assoc]
    change weightMass (faceDist (M.l527Sigma w B C u v z) (indicatorCost (M.fiberOver (betweenEdges u v))) 1) P
      * _ * _ = _
    rw [weightMass_faceDist, presentWeight, div_mul_cancel₀ _ (by
      rw [← presentWeight]; exact hLmass.ne'), weightMass_face, hσunwind]
    exact weightMass_congr fun T => by tauto
  have hMLsharp : (0.4995 - 3 * ε') * 0.4995 ≤ totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
          (atomBudget u v z))) := by
    rw [hLM, mul_comm (0.4995 - 3 * ε')]
    exact mul_le_mul hσE hMσsharp (by linarith only [hε'cap'])
      (by linarith only [hσE])
  have hML : 0.238 ≤ totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
          (atomBudget u v z))) := by
    rw [hLM]
    have hmul := mul_le_mul hσE hMσ (by norm_num) (by linarith only [hσE])
    nlinarith only [hmul]
  -- the (56) events at `L`: `δ_L = 4.21 ε'`
  have hL56Uraw : (totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
          (atomBudget u v z)))) * (1 - weightMass (M.l527Law w B C u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2)) ≤ ε' := by
    have h := cond_near_certain hnn hLtot hLunwind (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have h2 := weightMass_not_le hnn htot (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
    have hc : weightMass (M.l527Law w B C u v z) (fun T =>
        (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
        = weightMass (M.l527Law w B C u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
            + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2) := by
      refine weightMass_congr_of_support fun T hT => ?_
      obtain ⟨hZ0, -, -, hF0⟩ := hσparts T (hLsupp T hT).1
      rw [inter_sdiff_union_eq_of_card_inter_zero hZ0, inter_sdiff_union_eq_of_card_inter_zero hF0]
    rw [← hc]
    nlinarith only [h, h2, h56U]
  have hL56U : 1 - 4.21 * ε' ≤ weightMass (M.l527Law w B C u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2) := by
    have hle := weightMass_le_one hLnn hLtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2)
    have hmul := mul_le_mul_of_nonneg_right hML (sub_nonneg.mpr hle)
    linarith only [hL56Uraw, hmul, hle]

  have hL56Wraw : (totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
          (atomBudget u v z)))) * (1 - weightMass (M.l527Law w B C u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 2)) ≤ ε' := by
    have h := cond_near_certain hnn hLtot hLunwind (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have h2 := weightMass_not_le hnn htot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have hc : weightMass (M.l527Law w B C u v z) (fun T =>
        (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
        = weightMass (M.l527Law w B C u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
            + (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 2) := by
      refine weightMass_congr_of_support fun T hT => ?_
      obtain ⟨hZ0, -, hEB0, -⟩ := hσparts T (hLsupp T hT).1
      rw [inter_sdiff_union_eq_of_card_inter_zero hZ0,
        inter_sdiff_union_eq_of_card_inter_inter_zero hEB0]
    rw [← hc]
    nlinarith only [h, h2, h56W]
  have hL56W : 1 - 4.21 * ε' ≤ weightMass (M.l527Law w B C u v z) (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 2) := by
    have hle := weightMass_le_one hLnn hLtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
        + (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 2)
    have hmul := mul_le_mul_of_nonneg_right hML (sub_nonneg.mpr hle)
    linarith only [hL56Wraw, hmul, hle]

  /- ### The sandwich at `σ` -/
  have hσ2U : 1 - 2.10 * ε' ≤ weightMass (M.l527Sigma w B C u v z) (fun T =>
      (T ∩ ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))))).card = 2) :=
    hσ56U.trans (le_of_eq (weightMass_congr fun T => by
      rw [card_inter_union_of_disjoint hUA T]))
  have hσ3U : weightMass (M.l527Sigma w B C u v z) (fun T =>
      (T ∩ ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))))).card = 3) ≤ 2.10 * ε' := by
    have h := weightMass_not_le hσnn hσtot (fun T =>
      (T ∩ ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))))).card = 2)
    have h2 := weightMass_mono hσnn (A := fun T =>
      (T ∩ ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))))).card = 3)
      (B := fun T => ¬ (T ∩ ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))))).card = 2) fun T h => by omega
    linarith
  have hσmeanU := expCard_le_two_add_of_concentrated hσst hσrank hσnn hσtot _
    (by positivity) (by linarith) hσ2U hσ3U
  rw [expCard_union_of_disjoint _ hUA] at hσmeanU
  have hσ2W : 1 - 2.10 * ε' ≤ weightMass (M.l527Sigma w B C u v z) (fun T =>
      (T ∩ ((M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))))).card = 2) :=
    hσ56W.trans (le_of_eq (weightMass_congr fun T => by
      rw [card_inter_union_of_disjoint hWB T]))
  have hσ3W : weightMass (M.l527Sigma w B C u v z) (fun T =>
      (T ∩ ((M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))))).card = 3) ≤ 2.10 * ε' := by
    have h := weightMass_not_le hσnn hσtot (fun T =>
      (T ∩ ((M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))))).card = 2)
    have h2 := weightMass_mono hσnn (A := fun T =>
      (T ∩ ((M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))))).card = 3)
      (B := fun T => ¬ (T ∩ ((M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))))).card = 2) fun T h => by omega
    linarith
  have hσmeanW := expCard_le_two_add_of_concentrated hσst hσrank hσnn hσtot _
    (by positivity) (by linarith) hσ2W hσ3W
  rw [expCard_union_of_disjoint _ hWB] at hσmeanW
  -- the lower bounds at `ν`
  have hdUA : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) (A \ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_right (Finset.sdiff_subset_sdiff hAcv (Finset.Subset.refl _)) hcuv
  have hdWB : Disjoint (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) (B \ M.fiberOver (betweenEdges v z)) :=
    Finset.disjoint_of_subset_right (Finset.sdiff_subset_sdiff hBcv (Finset.Subset.refl _)) hczv
  have hνmeanU : 2 * (1 - 1.001 * ε')
      ≤ expCard (M.tau3 w u v z) (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))
        + expCard (M.tau3 w u v z) (A \ M.fiberOver (betweenEdges u v)) := by
    have h := mul_weightMass_eq_le_expCard hνnn
      ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (A \ M.fiberOver (betweenEdges u v))) 2
    rw [expCard_union_of_disjoint _ hdUA] at h
    have hc : weightMass (M.tau3 w u v z) (fun T =>
        (T ∩ ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (A \ M.fiberOver (betweenEdges u v)))).card = 2)
        = weightMass (M.tau3 w u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2) :=
      weightMass_congr fun T => by rw [card_inter_union_of_disjoint hdUA T]
    rw [hc] at h
    push_cast at h
    linarith
  have hνmeanW : 2 * (1 - 1.001 * ε')
      ≤ expCard (M.tau3 w u v z) (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))
        + expCard (M.tau3 w u v z) (B \ M.fiberOver (betweenEdges v z)) := by
    have h := mul_weightMass_eq_le_expCard hνnn
      ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) ∪ (B \ M.fiberOver (betweenEdges v z))) 2
    rw [expCard_union_of_disjoint _ hdWB] at h
    have hc : weightMass (M.tau3 w u v z) (fun T =>
        (T ∩ ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) ∪ (B \ M.fiberOver (betweenEdges v z)))).card = 2)
        = weightMass (M.tau3 w u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2) :=
      weightMass_congr fun T => by rw [card_inter_union_of_disjoint hdWB T]
    rw [hc] at h
    push_cast at h
    linarith
  have hνU'' : expCard (M.tau3 w u v z) (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
      = expCard (M.tau3 w u v z) (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))
        - expCard (M.tau3 w u v z) (M.fiberOver (betweenEdges u z)) := by
    have h : M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z))
        = (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    have hZsub : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v) := fun e he =>
      Finset.mem_sdiff.mpr ⟨hZcu he, fun h => Finset.disjoint_left.mp hZE he h⟩
    rw [h, expCard_sdiff_of_subset _ hZsub]
  have hνW'' : expCard (M.tau3 w u v z) (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
      = expCard (M.tau3 w u v z) (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))
        - expCard (M.tau3 w u v z) (M.fiberOver (betweenEdges u z)) := by
    have h : M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z))
        = (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    have hZsub : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z) := fun e he =>
      Finset.mem_sdiff.mpr ⟨hZcz he, fun h => Finset.disjoint_left.mp hZF he h⟩
    rw [h, expCard_sdiff_of_subset _ hZsub]
  have hσA''le : expCard (M.l527Sigma w B C u v z) (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))
      ≤ expCard (M.tau3 w u v z) (A \ M.fiberOver (betweenEdges u v))
        + 3.6 * (2.10 * ε') + 2 * (1.001 * ε') + 3 * ε' := by
    have h1 := hσge _ hU''R
    linarith
  have hσB''le : expCard (M.l527Sigma w B C u v z) (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))
      ≤ expCard (M.tau3 w u v z) (B \ M.fiberOver (betweenEdges v z))
        + 3.6 * (2.10 * ε') + 2 * (1.001 * ε') + 3 * ε' := by
    have h1 := hσge _ hW''R
    linarith
  /- ### The means at `L` -/
  have hνAe := abs_le.mp (hτ (A \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans (hAcv.trans hcv)))
  have hνBf := abs_le.mp (hτ (B \ M.fiberOver (betweenEdges v z)) (Finset.sdiff_subset.trans (hBcv.trans hcv)))
  have hLA2 : expCard (M.l527Law w B C u v z) (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))) ≤ 0.66 := by
    have := hLle _ hA''E
    linarith
  have hLB2 : expCard (M.l527Law w B C u v z) (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v))) ≤ 0.66 := by
    have := hLle _ hB''E
    linarith
  have hLA1 : 0.33 ≤ expCard (M.l527Law w B C u v z) (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))) := by
    have h := mul_weightMass_eq_le_expCard hLnn
      ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
        ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))) 2
    have hc : weightMass (M.l527Law w B C u v z) (fun T =>
        (T ∩ ((M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
          ∪ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z))))).card = 2)
        = weightMass (M.l527Law w B C u v z) (fun T =>
          (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
            + (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 2) :=
      weightMass_congr fun T => by rw [card_inter_union_of_disjoint hUA T]
    rw [hc, expCard_union_of_disjoint _ hUA] at h
    push_cast at h
    have h1 := hLle _ hU''E
    have h2 := hσge _ hA''R
    have h3 := abs_le.mp (hτ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))
      (Finset.sdiff_subset.trans (hAcv.trans hcv)))
    linarith
  /- ### The core -/
  have hcore := lemma_5_27_core_scaled hLst hLrank hLnn hLtot hA''B''
    (tU := 2) (tW := 2)
    (by linarith : 0 ≤ (totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
          (atomBudget u v z)))))
    hL56Uraw hL56Wraw hLA1 hLA2 hLB2
  /- ### Unwinding and the happy event -/
  have hkey := hLunwind (fun T =>
    (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 1
      ∧ (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 0
      ∧ (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card + 1 = 2
      ∧ (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card = 2)
  have himp : weightMass w (fun T =>
      ((T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card = 1
        ∧ (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card = 0
        ∧ (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card + 1 = 2
        ∧ (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card = 2)
      ∧ ((T ∩ M.fiberOver (betweenEdges u v)).card = 1
        ∧ ((T ∩ M.l527R B C u v z).card = 0
          ∧ (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z)))
      ≤ weightMass w (fun T =>
        (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2
          ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) := by
    refine weightMass_mono_of_support hnn fun T hT h => ?_
    obtain ⟨⟨hA1', hB0', hU1', hW2'⟩, hE1, hR0, hface⟩ := h
    obtain ⟨hu, hv, hz⟩ := (hcert.eq_iff T hT).mp hface
    -- the parts of `R` are absent
    have hZ0 : (T ∩ M.fiberOver (betweenEdges u z)).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (show M.fiberOver (betweenEdges u z) ⊆ M.l527R B C u v z from
          Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)))
      omega
    have hC0 : (T ∩ C).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (show C ⊆ M.l527R B C u v z from
          Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)))
      omega
    have hEB0 : (T ∩ (M.fiberOver (betweenEdges u v) ∩ B)).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (show M.fiberOver (betweenEdges u v) ∩ B ⊆ M.l527R B C u v z from
          Finset.subset_union_right.trans Finset.subset_union_left))
      omega
    have hF0 : (T ∩ M.fiberOver (betweenEdges v z)).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (show M.fiberOver (betweenEdges v z) ⊆ M.l527R B C u v z from Finset.subset_union_right))
      omega
    -- `δ(u) = U'' ⊔ Z ⊔ e`
    have hcuU : (T ∩ M.fiberOver (cutEdges u)).card
        = (T ∩ (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card
          + ((T ∩ M.fiberOver (betweenEdges u z)).card + (T ∩ M.fiberOver (betweenEdges u v)).card) := by
      have h1 : M.fiberOver (cutEdges u) = (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
          ∪ (M.fiberOver (betweenEdges u z) ∪ M.fiberOver (betweenEdges u v)) := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff, not_or]
        constructor
        · intro he
          by_cases hE : e ∈ M.fiberOver (betweenEdges u v)
          · exact Or.inr (Or.inr hE)
          by_cases hZ' : e ∈ M.fiberOver (betweenEdges u z)
          · exact Or.inr (Or.inl hZ')
          · exact Or.inl ⟨he, hE, hZ'⟩
        · rintro (h | h | h)
          · exact h.1
          · exact hZcu h
          · exact hEcu h
      have hd : Disjoint (M.fiberOver (cutEdges u) \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))
          (M.fiberOver (betweenEdges u z) ∪ M.fiberOver (betweenEdges u v)) :=
        Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (by
          rcases Finset.mem_union.mp h with h | h
          · exact Finset.mem_union_right _ h
          · exact Finset.mem_union_left _ h)
      conv_lhs => rw [h1]
      rw [card_inter_union_of_disjoint hd T, card_inter_union_of_disjoint hZE T]
    -- `δ(z) = W'' ⊔ Z ⊔ f`
    have hczW : (T ∩ M.fiberOver (cutEdges z)).card
        = (T ∩ (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card
          + ((T ∩ M.fiberOver (betweenEdges u z)).card + (T ∩ M.fiberOver (betweenEdges v z)).card) := by
      have h1 : M.fiberOver (cutEdges z) = (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
          ∪ (M.fiberOver (betweenEdges u z) ∪ M.fiberOver (betweenEdges v z)) := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff, not_or]
        constructor
        · intro he
          by_cases hF : e ∈ M.fiberOver (betweenEdges v z)
          · exact Or.inr (Or.inr hF)
          by_cases hZ' : e ∈ M.fiberOver (betweenEdges u z)
          · exact Or.inr (Or.inl hZ')
          · exact Or.inl ⟨he, hF, hZ'⟩
        · rintro (h | h | h)
          · exact h.1
          · exact hZcz h
          · exact hFcz h
      have hd : Disjoint (M.fiberOver (cutEdges z) \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))
          (M.fiberOver (betweenEdges u z) ∪ M.fiberOver (betweenEdges v z)) :=
        Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (by
          rcases Finset.mem_union.mp h with h | h
          · exact Finset.mem_union_right _ h
          · exact Finset.mem_union_left _ h)
      conv_lhs => rw [h1]
      rw [card_inter_union_of_disjoint hd T, card_inter_union_of_disjoint hZF T]
    -- `δ(v) = A ⊔ B ⊔ C`, with `A = A'' ⊔ (A ∩ e) ⊔ (A ∩ f)` and `B` likewise
    have hcvS : (T ∩ M.fiberOver (cutEdges v)).card = ((T ∩ A).card + (T ∩ B).card) + (T ∩ C).card := by
      rw [hpart, card_inter_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩) T,
        card_inter_union_of_disjoint hAB T]
    have hAsplit : (T ∩ A).card = (T ∩ (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))).card
        + ((T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card + (T ∩ (A ∩ M.fiberOver (betweenEdges v z))).card) := by
      have h1 : A = (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))
          ∪ ((A ∩ M.fiberOver (betweenEdges u v)) ∪ (A ∩ M.fiberOver (betweenEdges v z))) := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, not_or]
        tauto
      have hd : Disjoint (A \ (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges v z)))
          ((A ∩ M.fiberOver (betweenEdges u v)) ∪ (A ∩ M.fiberOver (betweenEdges v z))) :=
        Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (by
          rcases Finset.mem_union.mp h with h | h
          · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).2
          · exact Finset.mem_union_right _ (Finset.mem_inter.mp h).2)
      have hd2 : Disjoint (A ∩ M.fiberOver (betweenEdges u v)) (A ∩ M.fiberOver (betweenEdges v z)) :=
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF)
      conv_lhs => rw [h1]
      rw [card_inter_union_of_disjoint hd T, card_inter_union_of_disjoint hd2 T]
    have hBsplit : (T ∩ B).card = (T ∩ (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))).card
        + ((T ∩ (B ∩ M.fiberOver (betweenEdges v z))).card + (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card) := by
      have h1 : B = (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))
          ∪ ((B ∩ M.fiberOver (betweenEdges v z)) ∪ (B ∩ M.fiberOver (betweenEdges u v))) := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, not_or]
        tauto
      have hd : Disjoint (B \ (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u v)))
          ((B ∩ M.fiberOver (betweenEdges v z)) ∪ (B ∩ M.fiberOver (betweenEdges u v))) :=
        Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (by
          rcases Finset.mem_union.mp h with h | h
          · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).2
          · exact Finset.mem_union_right _ (Finset.mem_inter.mp h).2)
      have hd2 : Disjoint (B ∩ M.fiberOver (betweenEdges v z)) (B ∩ M.fiberOver (betweenEdges u v)) :=
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF.symm)
      conv_lhs => rw [h1]
      rw [card_inter_union_of_disjoint hd T, card_inter_union_of_disjoint hd2 T]
    -- the bundle edge of `e` lies in `A`
    have hAf : (T ∩ (A ∩ M.fiberOver (betweenEdges v z))).card ≤ (T ∩ M.fiberOver (betweenEdges v z)).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    have hBf : (T ∩ (B ∩ M.fiberOver (betweenEdges v z))).card ≤ (T ∩ M.fiberOver (betweenEdges v z)).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    have hBe : (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card = 0 := by
      rw [Finset.inter_comm B]; exact hEB0
    have hEle : (T ∩ M.fiberOver (betweenEdges u v)).card
        ≤ (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card + (T ∩ (M.fiberOver (betweenEdges u v) ∩ B)).card
          + (T ∩ C).card := by
      have hsub : M.fiberOver (betweenEdges u v)
          ⊆ ((A ∩ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (betweenEdges u v) ∩ B)) ∪ C := by
        intro e he
        have := hEsplit he
        rcases Finset.mem_union.mp this with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by
              rw [Finset.inter_comm]; exact h))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ h
      have h1 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hsub)
      rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left] at h1
      have h2 := Finset.card_union_le ((T ∩ (A ∩ M.fiberOver (betweenEdges u v))) ∪ (T ∩ (M.fiberOver (betweenEdges u v) ∩ B)))
        (T ∩ C)
      have h3 := Finset.card_union_le (T ∩ (A ∩ M.fiberOver (betweenEdges u v))) (T ∩ (M.fiberOver (betweenEdges u v) ∩ B))
      omega
    have hAe : (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card ≤ (T ∩ M.fiberOver (betweenEdges u v)).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    exact ⟨by omega, by omega, by omega, hu, hv, hz⟩
  -- Pin the two events before rounding the conditioning mass.
  have hprod := hcore
  conv_rhs at hprod => rw [mul_comm]
  rw [hkey] at hprod
  calc 0.068 * ((0.4995 - 3 * ε') * 0.4995) - 2 * ε' ≤
      0.068 * (totalMass (presentWeight (M.l527Sigma w B C u v z) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau3 w u v z) (M.l527R B C u v z))
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
          (atomBudget u v z)))) - 2 * ε' := by nlinarith only [hMLsharp]
    _ ≤ _ := hprod
    _ ≤ _ := himp

/-- The original bound, retained at the original defect budget. -/
theorem lemma_5_27_absent_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hcert : M.ThreeAtomUzData w u v z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ ε' : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2) (hε' : 0 ≤ ε') (hε'cap : ε' ≤ 27.2 * ε₂)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z)) (atomBudget u v z) ≤ 3 * εη)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ ε₂)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ ε₂)
    (h56U : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2))
    (h56W : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2))
    (hZ : expCard (M.tau3 w u v z) (M.fiberOver (betweenEdges u z)) ≤ 3 * ε') :
    0.005 ≤ weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) := by
  have h := lemma_5_27_absent_indexed_of_defect M hst hr hnn htot hune hvne hzne huv hvz huz hcert
    hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hε' (by linarith) hdef hxE hxF
    hxA1 hxA2 hxB1 hxB2 hxC hxEB hxFA h56U h56W hZ
  exact (lemma527_absent_budget_old hε' (by linarith : ε' ≤ 0.00544)).trans h

end TSPGap

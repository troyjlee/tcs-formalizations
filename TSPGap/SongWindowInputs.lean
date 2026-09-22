/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowFace
import TSPGap.SongWindowMeans

/-!
# Sanitized fiber-tree inputs to the Song window kernel

All eleven conditional means follow from original-law means on arbitrary
piece sides. Sanitization preserves those means by support completeness,
while making the disjointness required by the analytic kernel literal.
The last theorem identifies the kernel's three cells with the original
happy event, including both endpoint-tree clauses.

The original decreasing-tail hypothesis still has to be transferred and
matched to the kernel before this becomes a non-goodness/rank theorem.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The conditional mean packet, instantiated without projection of piece sides. -/
theorem window_means_indexed (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v : Finset (Fin n)}
    (huv : Disjoint u v) (hc : M.TwoAtomOneHotData w u v) {A B C E : Finset ι}
    (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) k)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀) :
    WindowMeanBounds
      (largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v)
        E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))))
      (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)))
      (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))
      (E \ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) := by
  have hout := window_cut_outside M huv
  have hbtwu := M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hbtwv := M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hA : A ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]
    exact subset_union_left.trans subset_union_left
  have hB : B ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]
    exact subset_union_right.trans subset_union_left
  have hC : C ⊆ M.fiberOver (cutEdges u) := by rw [hpart]; exact subset_union_right
  have hs : ∀ X, bundleSanitizeOn X E (M.fiberOver (betweenEdges u v)) ⊆ X :=
    fun X => bundleSanitizeOn_subset X E _
  have hsan : ∀ X, expCard w (bundleSanitizeOn X E (M.fiberOver (betweenEdges u v))) =
      expCard w X := fun X => expCard_congr_of_support' fun T hT => by
        rw [inter_bundleSanitizeOn_eq_of_supportCompleteOn (A := X) hSC hT]
  have hEV : expCard w (E ∪
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) =
        expCard w (M.fiberOver (cutEdges v)) := by
    have hb : expCard w (M.fiberOver (betweenEdges u v)) = expCard w E :=
      expCard_congr_of_support' fun T hT => by
        rw [inter_bundle_eq_of_supportCompleteOn hSC hT]
    rw [expCard_union_of_disjoint w (sdiff_disjoint.mono_right hSC.1).symm,
      expCard_sdiff_of_subset w hbtwv, hb]
    ring
  apply window_mean_bounds hw D
  · intro T hT hface
    obtain ⟨hu, hv⟩ := (hc.eq_iff T hT).mp hface
    exact (card_le_card (inter_subset_inter_left hSC.1)).trans (hc.one_hot T hT hu hv)
  · exact disjoint_bundleSanitizeOn hAB
  · exact disjoint_bundleSanitizeOn hAC
  · exact disjoint_bundleSanitizeOn hBC
  · exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨M.disjoint_bundleSanitizeOn_puncturedCut hA hSC.1 huv,
       M.disjoint_bundleSanitizeOn_puncturedCut hB hSC.1 huv⟩,
      M.disjoint_bundleSanitizeOn_puncturedCut hC hSC.1 huv⟩
  · apply window_sanitized_cover
    rw [← hpart]
    exact hSC.1.trans hbtwu
  · exact union_subset (union_subset
      (union_subset ((hs A).trans (hA.trans hout.1)) ((hs B).trans (hB.trans hout.1)))
      ((hs C).trans (hC.trans hout.1))) (sdiff_subset.trans hout.2)
  · exact hxE
  · simpa only [hsan] using hxA
  · simpa only [hsan] using hxB
  · simpa only [hsan] using hxC
  · simpa only [bundleSanitizeOn_inter_bundle hSC.1] using hxBE
  · simpa only [hEV] using hxv

/-- Three kernel cells imply the original happy event on the actual
restriction's support. Both induced-tree clauses come from the tight face. -/
theorem window_happy_of_cells (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {k : ℕ} {u v : Finset (Fin n)} {A B C E T : Finset ι} (huv : Disjoint u v)
    (hc : M.TwoAtomCountData w u v) (hSC : M.SupportComplete w E u v)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) k)
    (hT : largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v)
      E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) T ≠ 0)
    (hcell : (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) :
    (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
      InducesTree u (M.project T) ∧ InducesTree v (M.project T) := by
  obtain ⟨hτ, he, hz⟩ := D.clean.supp T hT
  obtain ⟨hw, hf⟩ := D.face.supp T hτ
  have hs := fun X => inter_bundleSanitizeOn_eq_of_supportCompleteOn (A := X) hSC hw
  rw [hs A, hs B] at hcell
  rw [hs C] at hz
  have hv := card_split_of_supportCompleteOn hSC
    (M.fiberOver_mono (betweenEdges_subset_cutEdges huv)) hw
  exact ⟨hcell.1, hcell.2.1, hz, by omega, (hc.eq_iff T hw).mp hf⟩

end TSPGap.Song

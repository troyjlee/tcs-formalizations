/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowGeometry
import TSPGap.SongWindowTails

/-!
# The fiber-tree face and goodness tail for Song's window

The maximum face, one-hot bundle and crossing baseline come from the
existing two-atom certificates. Original cut means supply the punctured
mean interval. The outside-face upper comparison has no deficiency loss;
this preserves the `3 + 2.01h` ceiling needed by the four-h tail argument.

The goodness premise is explicitly four h in the two-atom face law.
This file does not obtain it from the old three-h goodness definition.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Instantiate the actual window restriction at a two-atom fiber-tree face. -/
theorem window_conditioning_indexed (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v : Finset (Fin n)}
    (huv : Disjoint u v) (hc : M.TwoAtomOneHotData w u v) {E C : Finset ι}
    (hE : E ⊆ M.fiberOver (betweenEdges u v)) (hC : C ⊆ M.fiberOver (cutEdges u))
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (hxE : 1 / 2 - h ≤ expCard w E) (hxC : expCard w C ≤ 2 * r + d₀) :
    WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E C k := by
  have hout := window_cut_outside M huv
  refine window_conditioning hw hc.le ?_
    ((hE.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv))).trans hout.1)
    (hC.trans hout.1) hdef hxE hxC
  intro T hT hface
  obtain ⟨hu, hv⟩ := (hc.eq_iff T hT).mp hface
  exact (card_le_card (inter_subset_inter_left hE)).trans (hc.one_hot T hT hu hv)

/-- Original cut means and the half-bundle marginal imply the sharp
punctured mean interval in the actual atom-face law. -/
theorem window_puncture_means (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {k : ℕ} {u v : Finset (Fin n)} {E C : Finset ι} (huv : Disjoint u v)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E C k) (hSC : M.SupportComplete w E u v)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀) :
    2.4966 ≤ expCard (M.tau w u v) (windowPuncture M u v) ∧
      expCard (M.tau w u v) (windowPuncture M u v) ≤ 3 + 2.01 * h := by
  have hout := window_cut_outside M huv
  have hJo : windowPuncture M u v ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ :=
    union_subset (sdiff_subset.trans hout.1) (sdiff_subset.trans hout.2)
  have hlo := D.lower _ hJo
  have hhi := D.upper _ hJo
  change expCard w _ - 2 * d₀ ≤ expCard (M.tau w u v) _ at hlo
  change expCard (M.tau w u v) _ ≤ expCard w _ at hhi
  rw [window_puncture_expCard M huv hSC] at hlo hhi
  obtain ⟨heL, heU⟩ := abs_le.mp hxE
  have hnumL : (2.4966 : ℝ) ≤ 3 - 2 * h - 2 * d₀ := by norm_num [h, d₀]
  have hnumU : 2 * d₀ ≤ 0.01 * h := by norm_num [h, d₀]
  constructor
  · linarith only [hlo, hxu.1, hxv.1, heU, hnumL]
  · linarith only [hhi, hxu.2, hxv.2, heL, hnumU]

/-- The four-h two-two goodness premise supplies the 0.399h tail in the
actual face / clean-present / avoidance law. -/
theorem window_low_tail_indexed (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {k : ℕ} {u v : Finset (Fin n)} {E C : Finset ι} (huv : Disjoint u v)
    (hc : M.TwoAtomCrossData w u v)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E C k) (hSC : M.SupportComplete w E u v)
    (hC : C ⊆ M.fiberOver (cutEdges u))
    (hxE : |expCard w E - 1 / 2| ≤ h) (hxC : expCard w C ≤ 2 * r + d₀)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hgood : 4 * h ≤ weightMass (M.tau w u v) (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2)) :
    0.399 * h ≤ weightMass (largeBundleLaw w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E C) (fun T => (T ∩ windowPuncture M u v).card ≤ 2) := by
  have hout := window_cut_outside M huv
  have hEo := (hSC.1.trans (M.fiberOver_mono
    (betweenEdges_subset_cutEdges_left huv))).trans hout.1
  have he : 1 / 2 - h - 2 * d₀ ≤ expCard (M.tau w u v) E := by
    have hh := D.lower E hEo
    change expCard w E - 2 * d₀ ≤ expCard (M.tau w u v) E at hh
    have heL := (abs_le.mp hxE).1
    linarith only [hh, heL]
  have hτC : expCard (M.tau w u v) C ≤ 2 * r + d₀ :=
    (D.upper C (hC.trans hout.1)).trans hxC
  have hτSC : M.SupportComplete (M.tau w u v) E u v :=
    ⟨hSC.1, fun T hT => hSC.2 T (D.face.supp T hT).1⟩
  have hone : ∀ T, M.tau w u v T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun _ hT => M.tau_oneHot hc.toTwoAtomOneHotData hSC.1 hT
  have hJE : Disjoint (windowPuncture M u v) E :=
    disjoint_union_left.mpr
      ⟨sdiff_disjoint.mono_right hSC.1, sdiff_disjoint.mono_right hSC.1⟩
  have hm := window_puncture_means M huv D hSC hxE hxu hxv
  exact window_clean_low_tail D.face.law hone he hτC hJE
    (fun _ hT => window_puncture_baseline M hc (D.face.supp _ hT).1) hm.1 hm.2
    (window_good_tail M D.face.law.nn huv hτSC hone hgood)

/-- Put the tail in the exact bundle-free event required by the analytic
kernel. The C-side here is sanitized; only its supported count is used. -/
theorem window_kernel_low_tail (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {k : ℕ} {u v : Finset (Fin n)} {A B C E : Finset ι}
    (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) k)
    (htail : 0.399 * h ≤ weightMass
      (largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v)
        E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))))
      (fun T => (T ∩ windowPuncture M u v).card ≤ 2)) :
    0.399 * h ≤ weightMass
      (largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v)
        E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))))
      (fun T => (T ∩ (((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪
        bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \
          (E \ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)))) ∪
            (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card ≤ 2) := by
  convert htail using 1
  apply weightMass_congr_of_support
  intro T hT
  have hν := D.clean.supp T hT
  rw [window_sanitized_away M hSC hpart (D.face.supp T hν.1).1 hν.2.2]

end TSPGap.Song

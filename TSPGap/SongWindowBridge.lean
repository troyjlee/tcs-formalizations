/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowInputs

/-!
# The second window tail and original-space happy-event bridge

The original sum-of-counts tail implies a tail for the ambient punctured
union. This decreasing event gains under the atom face and loses at most
the C mean under clean conditioning. Adding back a one-hot bundle then
gives the exact kernel event. No equality of overlapping sets is assumed.

The final bridge unwinds at the original law, using its support and the
explicit restriction event; it never divides by a conditional probability.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

omit [Fintype ι] in
/-- Replacing E by a larger ambient bundle can only decrease the punctured count. -/
theorem window_punctured_union_le {A V E Bd T : Finset ι} (hE : E ⊆ Bd) :
    (T ∩ ((A \ Bd) ∪ (V \ Bd))).card ≤
      (T ∩ (A \ E)).card + (T ∩ (V \ E)).card := by
  have hs : (A \ Bd) ∪ (V \ Bd) ⊆ (A \ E) ∪ (V \ E) :=
    union_subset_union (sdiff_subset_sdiff (Subset.refl _) hE)
      (sdiff_subset_sdiff (Subset.refl _) hE)
  refine (card_le_card (inter_subset_inter_left hs)).trans ?_
  rw [inter_union_distrib_left]
  exact card_union_le _ _

omit [Fintype ι] in
/-- Restoring a sanitized side adds at most the bundle count. -/
theorem window_restore_bundle_le (A V E Bd T : Finset ι) :
    (T ∩ (bundleSanitizeOn A E Bd ∪ (V \ Bd))).card ≤
      (T ∩ ((A \ Bd) ∪ (V \ Bd))).card + (T ∩ E).card := by
  have heq : bundleSanitizeOn A E Bd ∪ (V \ Bd) =
      ((A \ Bd) ∪ (V \ Bd)) ∪ (A ∩ E) := by
    ext e
    simp only [bundleSanitizeOn, mem_union, mem_sdiff, mem_inter]
    tauto
  rw [heq, inter_union_distrib_left]
  exact (card_union_le _ _).trans (Nat.add_le_add_left
    (card_le_card (inter_subset_inter_left inter_subset_right)) _)

/-- The remaining original tail supplies the kernel's A-plus-V tail.
Support completeness is not needed for this one-way implication. -/
theorem window_kernel_original_tail (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v : Finset (Fin n)}
    (huv : Disjoint u v) (hc : M.TwoAtomOneHotData w u v) {A E C : Finset ι}
    (hE : E ⊆ M.fiberOver (betweenEdges u v))
    (hA : A ⊆ M.fiberOver (cutEdges u)) (hC : C ⊆ M.fiberOver (cutEdges u))
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E C k)
    (hxE : 1 / 2 - h ≤ expCard w E) (hxC : expCard w C ≤ 2 * r + d₀)
    (htail : K * h ≤ weightMass w (fun T =>
      (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    (K - 0.51) * h ≤ weightMass
      (largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) E C)
      (fun T => (T ∩ (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪
        (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card ≤ 2) := by
  let J := (A \ M.fiberOver (betweenEdges u v)) ∪
    (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))
  let ν := largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) E C
  have hout := window_cut_outside M huv
  have hJo : J ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ :=
    union_subset (sdiff_subset.trans (hA.trans hout.1)) (sdiff_subset.trans hout.2)
  have hJF : Disjoint J (M.fiberOver (twoAtomInternal u v)) :=
    disjoint_left.mpr fun _ hJ hF => (mem_compl.mp (hJo hJ)) hF
  have hJE : Disjoint J E := disjoint_union_left.mpr
    ⟨sdiff_disjoint.mono_right hE, sdiff_disjoint.mono_right hE⟩
  have hJ : K * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 1) := by
    refine htail.trans (weightMass_mono hw.nn fun T hT => ?_)
    exact (window_punctured_union_le hE).trans hT
  have hone : ∀ T, w T ≠ 0 →
      (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v →
        (T ∩ E).card ≤ 1 := by
    intro T hT hf
    obtain ⟨hu, hv⟩ := (hc.eq_iff T hT).mp hf
    exact (card_le_card (inter_subset_inter_left hE)).trans (hc.one_hot T hT hu hv)
  have ht := window_original_tail hw D hc.le hone
    ((hE.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv))).trans hout.1)
    (hC.trans hout.1) hxE hxC (antitone_card_le J 1)
    (eventDependsOn_card_le J 1) hJF hJE hJ
  change (K - 0.51) * h ≤ weightMass ν (fun T => (T ∩ J).card ≤ 1) at ht
  refine ht.trans ?_
  have heq : weightMass ν (fun T => (T ∩ J).card ≤ 1) =
      weightMass ν (fun T => (T ∩ J).card ≤ 1 ∧
        (T ∩ (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪
          (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card ≤ 2) := by
    apply weightMass_congr_of_support
    intro T hT
    have ho := (D.clean.supp T hT).2.1
    have hb := window_restore_bundle_le A (M.fiberOver (cutEdges v)) E
      (M.fiberOver (betweenEdges u v)) T
    change _ ≤ (T ∩ J).card + (T ∩ E).card at hb
    omega
  rw [heq]
  exact weightMass_mono D.clean.law.nn fun _ hT => hT.2

/-- The raw restriction event and the three cells give happiness, without
having to reconstruct a nonzero normalized density. -/
theorem window_happy_of_raw_cells (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {u v : Finset (Fin n)} {A B C E T : Finset ι} (huv : Disjoint u v)
    (hc : M.TwoAtomOneHotData w u v) (hSC : M.SupportComplete w E u v) (hT : w T ≠ 0)
    (hf : (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)
    (ha : (T ∩ (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)) \ E)).card = 0)
    (hp : (T ∩ (E \ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)))).card = 1)
    (hcell : (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) :
    (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
      InducesTree u (M.project T) ∧ InducesTree v (M.project T) := by
  obtain ⟨hu, hv⟩ := (hc.eq_iff T hT).mp hf
  have hone := (card_le_card (inter_subset_inter_left hSC.1)).trans
    (hc.one_hot T hT hu hv)
  obtain ⟨he, hz⟩ := clean_present_avoid_support hone hp ha
  have hs := fun X => inter_bundleSanitizeOn_eq_of_supportCompleteOn (A := X) hSC hT
  rw [hs A, hs B] at hcell
  rw [hs C] at hz
  have hvCount := card_split_of_supportCompleteOn hSC
    (M.fiberOver_mono (betweenEdges_subset_cutEdges huv)) hT
  exact ⟨hcell.1, hcell.2.1, hz, by omega, hu, hv⟩

/-- Pay the actual face-times-clean mass and return to the original law. -/
theorem window_unwind_cells (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {k : ℕ} (hnn : WeightNonneg w) {u v : Finset (Fin n)} {A B C E : Finset ι}
    (huv : Disjoint u v) (hc : M.TwoAtomOneHotData w u v)
    (hSC : M.SupportComplete w E u v)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) k)
    (hp : p < 0.499 * weightMass
      (largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v)
        E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))))
      (fun T => (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1 ∧
        (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1 ∧
        (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)) :
    p < weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  let R := fun T =>
    (T ∩ (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)) \ E)).card = 0 ∧
      (T ∩ (E \ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)))).card = 1 ∧
      (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v
  refine window_reused_unwind (C := R) hnn hp D.mass_ge ?_ ?_
  · rw [D.unwind]
    apply weightMass_congr
    intro T
    dsimp [R]
    tauto
  · intro T hT hP
    exact window_happy_of_raw_cells M huv hc hSC hT hP.2.2.2 hP.2.1 hP.2.2.1 hP.1

end TSPGap.Song

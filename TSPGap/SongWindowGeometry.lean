/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Indexed

/-!
# Supported count geometry for Song's half-bundle window

The puncture is taken against the whole ambient bundle. Its two sides
are literally disjoint, even when the chosen support-complete bundle
omits zero-marginal coordinates. Equalities involving that chosen bundle
are asserted only on the support. No probability estimate enters here.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Both endpoint cuts with the ambient bundle removed. -/
def windowPuncture (M : FiberTreeModel ι n) (u v : Finset (Fin n)) : Finset ι :=
  (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪
    (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))

/-- The two cuts are outside the simultaneous internal-edge face. -/
theorem window_cut_outside (M : FiberTreeModel ι n) {u v : Finset (Fin n)}
    (huv : Disjoint u v) :
    M.fiberOver (cutEdges u) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ ∧
      M.fiberOver (cutEdges v) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
  constructor
  · rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom
      (cutEdges_disjoint_internalEdges_self u) (cutEdges_disjoint_internalEdges huv))
  · rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom
      (cutEdges_disjoint_internalEdges huv.symm) (cutEdges_disjoint_internalEdges_self v))

/-- Ambient punctures are disjoint as sets, not merely on the support. -/
theorem window_punctures_disjoint (M : FiberTreeModel ι n) {u v : Finset (Fin n)}
    (huv : Disjoint u v) :
    Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
  rw [← M.fiberOver_sdiff, ← M.fiberOver_sdiff]
  exact M.disjoint_fiberOver (disjoint_punctured_cuts huv)

/-- The division-free count identity, with the bundle counted at both ends. -/
theorem window_puncture_card (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {u v : Finset (Fin n)} {E T : Finset ι} (huv : Disjoint u v)
    (hSC : M.SupportComplete w E u v) (hT : w T ≠ 0) :
    (T ∩ windowPuncture M u v).card + 2 * (T ∩ E).card =
      (T ∩ M.fiberOver (cutEdges u)).card + (T ∩ M.fiberOver (cutEdges v)).card := by
  have hu := card_split_of_supportCompleteOn hSC
    (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)) hT
  have hv := card_split_of_supportCompleteOn hSC
    (M.fiberOver_mono (betweenEdges_subset_cutEdges huv)) hT
  rw [windowPuncture, card_inter_union_of_disjoint (window_punctures_disjoint M huv) T]
  omega

/-- The same identity in means. Nonnegativity and normalization are not needed. -/
theorem window_puncture_expCard (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {u v : Finset (Fin n)} {E : Finset ι} (huv : Disjoint u v)
    (hSC : M.SupportComplete w E u v) :
    expCard w (windowPuncture M u v) = expCard w (M.fiberOver (cutEdges u)) +
      expCard w (M.fiberOver (cutEdges v)) - 2 * expCard w E := by
  have hb : expCard w (M.fiberOver (betweenEdges u v)) = expCard w E :=
    expCard_congr_of_support' fun T hT => by
      rw [inter_bundle_eq_of_supportCompleteOn hSC hT]
  rw [windowPuncture, expCard_union_of_disjoint w (window_punctures_disjoint M huv),
    expCard_sdiff_of_subset w (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)),
    expCard_sdiff_of_subset w (M.fiberOver_mono (betweenEdges_subset_cutEdges huv)), hb]
  ring

/-- The union cut supplies the baseline without any conditioning. -/
theorem window_puncture_baseline (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {u v : Finset (Fin n)} (hc : M.TwoAtomCrossData w u v)
    {T : Finset ι} (hT : w T ≠ 0) : 1 ≤ (T ∩ windowPuncture M u v).card := by
  refine (hc.cut_union T hT).trans (card_le_card (inter_subset_inter_left ?_))
  have hh := M.fiberOver_mono (cutEdges_union_subset_punctured (v := u) (z := v))
  simpa only [M.fiberOver_union, M.fiberOver_sdiff, windowPuncture] using hh

/-- A two-two event on a one-hot support lies below three or above three.
The coefficient is arbitrary: Song's caller supplies four h, not the old three h. -/
theorem window_good_tail (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) {u v : Finset (Fin n)} {E : Finset ι}
    (huv : Disjoint u v) (hSC : M.SupportComplete w E u v)
    (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1) {g : ℝ}
    (hgood : g ≤ weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2)) :
    g ≤ weightMass w (fun T => (T ∩ windowPuncture M u v).card ≤ 2) +
      weightMass w (fun T => 4 ≤ (T ∩ windowPuncture M u v).card) := by
  let P := fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
    (T ∩ M.fiberOver (cutEdges v)).card = 2
  let Q := fun T => (T ∩ windowPuncture M u v).card ≤ 2 ∨
    4 ≤ (T ∩ windowPuncture M u v).card
  have heq : weightMass w P = weightMass w (fun T => P T ∧ Q T) := by
    apply weightMass_congr_of_support
    intro T hT
    have hh := window_puncture_card M huv hSC hT
    have ho := hone T hT
    dsimp [P, Q]
    omega
  have hle : weightMass w P ≤ weightMass w Q := by
    rw [heq]
    exact weightMass_mono hnn fun _ hT => hT.2
  have hor := weightMass_or w (fun T => (T ∩ windowPuncture M u v).card ≤ 2)
    (fun T => 4 ≤ (T ∩ windowPuncture M u v).card)
  have hnn' := weightMass_nonneg hnn (fun T =>
    (T ∩ windowPuncture M u v).card ≤ 2 ∧ 4 ≤ (T ∩ windowPuncture M u v).card)
  change g ≤ weightMass w P at hgood
  change weightMass w Q + _ = _ at hor
  linarith only [hgood, hle, hor, hnn']

omit [Fintype ι] in
/-- Every chosen bundle coordinate survives sanitization of its partition cell. -/
theorem window_sanitized_cover {A B C E Bd : Finset ι} (hE : E ⊆ (A ∪ B) ∪ C) :
    E ⊆ (bundleSanitizeOn A E Bd ∪ bundleSanitizeOn B E Bd) ∪
      bundleSanitizeOn C E Bd := by
  intro e he
  have hh := hE he
  simp only [bundleSanitizeOn, mem_union, mem_inter, mem_sdiff] at hh ⊢
  tauto

/-- After C avoidance, the kernel's bundle-free count is the ambient puncture.
This is a supported intersection identity, not an unconditional set equality. -/
theorem window_sanitized_away (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {u v : Finset (Fin n)} {A B C E T : Finset ι}
    (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C) (hT : w T ≠ 0)
    (hC : (T ∩ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))).card = 0) :
    T ∩ (((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪
      bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \
        (E \ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)))) ∪
          (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) =
      T ∩ windowPuncture M u v := by
  have hSan := fun X => inter_bundleSanitizeOn_eq_of_supportCompleteOn (A := X) hSC hT
  have hzero : T ∩ C = ∅ := by
    rw [hSan C] at hC
    exact card_eq_zero.mp hC
  have hb := inter_bundle_eq_of_supportCompleteOn hSC hT
  ext e
  by_cases he : e ∈ T
  · have hnotC : e ∉ C := fun hc => by
      have hh : e ∈ T ∩ C := mem_inter.mpr ⟨he, hc⟩
      rw [hzero] at hh
      exact notMem_empty e hh
    have hSA : e ∈ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ↔ e ∈ A := by
      simpa only [mem_inter, he, true_and] using Iff.of_eq (congrArg (e ∈ ·) (hSan A))
    have hSB : e ∈ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)) ↔ e ∈ B := by
      simpa only [mem_inter, he, true_and] using Iff.of_eq (congrArg (e ∈ ·) (hSan B))
    have hSC' : e ∈ bundleSanitizeOn C E (M.fiberOver (betweenEdges u v)) ↔ e ∈ C := by
      simpa only [mem_inter, he, true_and] using Iff.of_eq (congrArg (e ∈ ·) (hSan C))
    have hE : e ∈ E ↔ e ∈ M.fiberOver (betweenEdges u v) := by
      simpa only [mem_inter, he, true_and] using Iff.of_eq (congrArg (e ∈ ·) hb)
    simp only [windowPuncture, mem_inter, mem_union, mem_sdiff, he, true_and,
      hSA, hSB, hSC', hnotC, not_false_eq_true, and_true, hE, hpart]
    simp only [or_false]
  · simp [he]

end TSPGap.Song

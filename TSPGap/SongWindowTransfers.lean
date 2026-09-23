/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongLargeBundleMeans
import TSPGap.SongWindowReuse

/-!
# Actual conditioning and mass for Song's half-bundle window

The definitions `largeBundleLaw` and `largeBundleMass` are shared with the
large-bundle calculation, but impose no large-bundle hypothesis. Here the
bundle has mean in `1/2 ± h`. We construct its maximum-face / clean-present /
avoidance law, retaining the face factor in the original-space mass.

The decreasing-event transfer and the small bundle-part bound below are
generic. In particular they do not assume that the window tails have
already been proved.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction can only discard a one-hot sub-bundle's unnormalized mean. -/
theorem clean_bundle_part_mean {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {E C X : Finset ι} (D : CleanBundleData w E C k)
    (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1) (hX : X ⊆ E) :
    expCard (cleanBundleLaw w E C) X * cleanBundleMass w E C ≤ expCard w X := by
  have hwo : ∀ T, w T ≠ 0 → (T ∩ X).card ≤ 1 := fun T hT =>
    (card_le_card (inter_subset_inter_left hX)).trans (hone T hT)
  have hno : ∀ T, cleanBundleLaw w E C T ≠ 0 → (T ∩ X).card ≤ 1 := fun T hT =>
    (card_le_card (inter_subset_inter_left hX)).trans (D.supp T hT).2.1.le
  rw [expCard_eq_weightMass_one hno, D.unwind, expCard_eq_weightMass_one hwo]
  exact weightMass_mono hw.nn fun _ hT => hT.1.1

/-- Presenting away from a decreasing event only helps; the subsequent
avoidance costs at most the original mean of C. Overlap of E and C is allowed. -/
theorem clean_bundle_antitone {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {E C : Finset ι} (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hc : expCard w C < 1) (hec : expCard w C < expCard w E)
    {Q : Finset ι → Prop} {J : Finset ι} (hQ : Antitone Q)
    (hdep : EventDependsOn Q J) (hJE : Disjoint J E) :
    weightMass w Q - expCard w C ≤ weightMass (cleanBundleLaw w E C) Q := by
  have hone' : ∀ T, w T ≠ 0 → (T ∩ (E \ C)).card ≤ 1 := fun T hT =>
    (card_le_card (inter_subset_inter_left sdiff_subset)).trans (hone T hT)
  have hsplit := expCard_split w E C
  have hEC := expCard_mono hw.nn (inter_subset_right (s₁ := E) (s₂ := C))
  have hp : 0 < totalMass (presentWeight w (E \ C)) := by
    rw [totalMass_presentWeight_eq_expCard hone']
    linarith only [hsplit, hEC, hec]
  have hwp : LawData (cleanPresent w E C) k := hw.present hone' hp
  have hpc : expCard (cleanPresent w E C) (C \ E) ≤ expCard w (C \ E) :=
    hw.present_le hone' (disjoint_of_subset_right sdiff_subset sdiff_disjoint) hp
  have hCm := expCard_mono hw.nn (sdiff_subset (s := C) (t := E))
  have ha : 0 < totalMass (avoidWeight (cleanPresent w E C) (C \ E)) := by
    have hh := hwp.avoid_mass_ge (C \ E)
    linarith only [hh, hpc, hCm, hc]
  have hfirst := weightMass_faceDist_ge_of_antitone hw.st hw.rank hw.nn hw.tot
    hone' hp hQ hdep (hJE.mono_right sdiff_subset)
  have hsecond := weightMass_avoidDist_ge_sub_expCard hwp.nn hwp.tot ha Q
  change weightMass w Q ≤ weightMass (cleanPresent w E C) Q at hfirst
  change _ ≤ weightMass (cleanBundleLaw w E C) Q at hsecond
  linarith only [hfirst, hsecond, hpc, hCm]

/-- The constructed face and clean restriction, with the sharp mass and
signed outside-face comparisons. All bounds refer to actual defined laws. -/
structure WindowConditioningData (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ)
    (E C : Finset ι) (k : ℕ) : Prop where
  face : FaceLawData w F m k d₀
  clean : CleanBundleData (faceDist w (indicatorCost F) m) E C k
  clean_mass_ge : 0.499 ≤ cleanBundleMass (faceDist w (indicatorCost F) m) E C
  mass_ge : 0.499 ≤ largeBundleMass w F m E C
  lower : ∀ S, S ⊆ Fᶜ → expCard w S - 2 * d₀ ≤
    expCard (faceDist w (indicatorCost F) m) S
  upper : ∀ S, S ⊆ Fᶜ → expCard (faceDist w (indicatorCost F) m) S ≤ expCard w S

/-- The 0.499 floor follows from the original half-bundle marginal and
small C mean, without silently discarding the atom-face mass. -/
theorem window_conditioning {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {F : Finset ι} {m : ℕ} (hsup : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ m)
    {E C : Finset ι}
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card = m → (T ∩ E).card ≤ 1)
    (hEo : E ⊆ Fᶜ) (hCo : C ⊆ Fᶜ) (hdef : faceDeficiency w F m ≤ 2 * d₀)
    (hxE : 1 / 2 - h ≤ expCard w E) (hxC : expCard w C ≤ 2 * r + d₀) :
    WindowConditioningData w F m E C k := by
  have hf := faceLawData hw.st hw.rank hw.nn hw.tot hsup
    (by norm_num [d₀] : 0 ≤ d₀) (by norm_num [d₀] : d₀ ≤ 0.001) hdef
  let τ := faceDist w (indicatorCost F) m
  have hlo : ∀ S, S ⊆ Fᶜ → expCard w S - 2 * d₀ ≤ expCard τ S := by
    intro S hS
    have hh := hw.face_outside_ge hsup hf.mass hS
    change expCard w S - faceDeficiency w F m ≤ expCard τ S at hh
    linarith only [hh, hdef]
  have hhi : ∀ S, S ⊆ Fᶜ → expCard τ S ≤ expCard w S :=
    fun _ hS => hw.face_outside_le hsup hf.mass hS
  have hτone : ∀ T, τ T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => hone T (hf.supp T hT).1 (hf.supp T hT).2
  have hc : expCard τ C < 1 := by
    have ht := hhi C hCo
    have hn : 2 * r + d₀ < 1 := by norm_num [r, h, d₀]
    linarith only [ht, hxC, hn]
  have hec : expCard τ C < expCard τ E := by
    have hl := hlo E hEo
    have hu := hhi C hCo
    have hn : 0 < 1 / 2 - h - 2 * r - 3 * d₀ := by norm_num [r, h, d₀]
    linarith only [hl, hu, hxE, hxC, hn]
  have D := cleanBundleData hf.law hτone hc hec
  have hcm : 1 / 2 - h - 2 * r - 3 * d₀ ≤ cleanBundleMass τ E C := by
    linarith only [D.mass_ge, hlo E hEo, hhi C hCo, hxE, hxC]
  have hcm' : 0.499 ≤ cleanBundleMass τ E C :=
    (by norm_num [h, r, d₀] : (0.499 : ℝ) ≤ 1 / 2 - h - 2 * r - 3 * d₀).trans hcm
  have hm : 0.499 ≤ largeBundleMass w F m E C := by
    have hh := mul_le_mul hf.massGe hcm
      (by norm_num [h, r, d₀] : 0 ≤ 1 / 2 - h - 2 * r - 3 * d₀) hf.mass.le
    change _ ≤ cleanBundleMass τ E C * totalMass (faceWeight w (indicatorCost F) m)
    rw [mul_comm]
    exact window_reuse_mass_budget.le.trans hh
  exact ⟨hf, D, hcm', hm, hlo, hhi⟩

/-- Unwind all three restrictions back into the original law. -/
theorem WindowConditioningData.unwind {w : Finset ι → ℝ} {F E C : Finset ι} {m k : ℕ}
    (D : WindowConditioningData w F m E C k) (Q : Finset ι → Prop) :
    weightMass (largeBundleLaw w F m E C) Q * largeBundleMass w F m E C =
      weightMass w (fun T =>
        ((Q T ∧ (T ∩ (C \ E)).card = 0) ∧ (T ∩ (E \ C)).card = 1) ∧
          (T ∩ F).card = m) := by
  change weightMass (cleanBundleLaw (faceDist w (indicatorCost F) m) E C) Q *
    (cleanBundleMass (faceDist w (indicatorCost F) m) E C *
      totalMass (faceWeight w (indicatorCost F) m)) = _
  rw [← mul_assoc, D.clean.unwind]
  exact D.face.unwind _

end TSPGap.Song

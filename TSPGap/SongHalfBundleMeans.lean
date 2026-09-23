/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowMeans
import TSPGap.Lemma524Kernel

/-!
# Means and probability budget for Song's balanced half bundles

The two punctured sets satisfy the existing 5.24 kernel's mean bounds at
Song's wider partition tolerance `r = h/4`. Presenting the clean bundle
rescales each bundle part; subsequent C avoidance only increases it.
The analytic error is `windowError`, so the available `0.399*h` tail
matches the kernel's `0.22*windowError` premise exactly.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A clean bundle part retains its presence-rescaled mean after avoidance. -/
theorem clean_bundle_part_lower {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {E C Z : Finset ι} (D : CleanBundleData w E C k)
    (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hZE : Z ⊆ E) (hZC : Disjoint Z C) :
    expCard w Z / expCard w (E \ C) ≤ expCard (cleanBundleLaw w E C) Z := by
  have hone' : ∀ T, w T ≠ 0 → (T ∩ (E \ C)).card ≤ 1 := fun T hT =>
    (card_le_card (inter_subset_inter_left sdiff_subset)).trans (hone T hT)
  have hmass := D.mass_pos
  unfold cleanBundleMass at hmass
  have hnn : 0 ≤ totalMass (presentWeight w (E \ C)) :=
    totalMass_nonneg (weightNonneg_faceWeight hw.nn _ _)
  obtain ⟨hp, ha⟩ := (mul_pos_iff.mp hmass).resolve_right
    (fun hh => not_lt_of_ge hnn hh.1)
  have hwp : LawData (cleanPresent w E C) k := hw.present hone' hp
  have hz : Z ⊆ E \ C := fun z hz =>
    mem_sdiff.mpr ⟨hZE hz, disjoint_left.mp hZC hz⟩
  have heq := expCard_presentDist_of_subset hone' hz
  have hlo := hwp.avoid_ge (hZC.mono_right sdiff_subset) ha
  change expCard (cleanPresent w E C) Z ≤ expCard (cleanBundleLaw w E C) Z at hlo
  rw [cleanPresent, heq] at hlo
  exact hlo

/-- A bundle part of original mean at least h has conditional mean at least 1.99h. -/
theorem window_bundle_part_lower {w : Finset ι → ℝ} {F E C Z : Finset ι} {m k : ℕ}
    (D : WindowConditioningData w F m E C k)
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card = m → (T ∩ E).card ≤ 1)
    (hEo : E ⊆ Fᶜ) (hZE : Z ⊆ E) (hZC : Disjoint Z C)
    (hxE : expCard w E ≤ 1 / 2 + h) (hxZ : h ≤ expCard w Z) :
    1.99 * h ≤ expCard (largeBundleLaw w F m E C) Z := by
  let τ := faceDist w (indicatorCost F) m
  have hτone : ∀ T, τ T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => hone T (D.face.supp T hT).1 (D.face.supp T hT).2
  have hz : Z ⊆ E \ C := fun z hz =>
    mem_sdiff.mpr ⟨hZE hz, disjoint_left.mp hZC hz⟩
  have hlo : h - 2 * d₀ ≤ expCard τ Z := by
    linarith only [D.lower Z (hZE.trans hEo), hxZ]
  have hden : 0 < expCard τ (E \ C) :=
    ((by norm_num [h, d₀] : 0 < h - 2 * d₀).trans_le hlo).trans_le
      (expCard_mono D.face.law.nn hz)
  have hhi : expCard τ (E \ C) ≤ 1 / 2 + h :=
    ((expCard_mono D.face.law.nn sdiff_subset).trans (D.upper E hEo)).trans hxE
  have hnum : 1.99 * h * (1 / 2 + h) ≤ h - 2 * d₀ := by norm_num [h, d₀]
  have hmul := mul_le_mul_of_nonneg_left hhi (by norm_num [h] : 0 ≤ 1.99 * h)
  exact ((le_div_iff₀ hden).mpr (hmul.trans (hnum.trans hlo))).trans
    (clean_bundle_part_lower D.face.law D.clean hτone hZE hZC)

/-- The six means needed by the punctured two-cell kernel. -/
structure HalfBundleMeanBounds (ν : Finset ι → ℝ) (X V : Finset ι) : Prop where
  X_lower : 0.997 ≤ expCard ν X
  X_upper : expCard ν X ≤ 1.51
  V_lower : 0.997 ≤ expCard ν V
  V_upper : expCard ν V ≤ 1.51
  union_lower : 2.4966 ≤ expCard ν (X ∪ V)
  union_upper : expCard ν (X ∪ V) ≤ 3.0025

/-- Original marginal bounds imply the punctured means, with no small wrong-side premise. -/
theorem half_bundle_mean_bounds {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {F : Finset ι} {m : ℕ} {E A B C V : Finset ι}
    (D : WindowConditioningData w F m E C k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hUV : Disjoint ((A ∪ B) ∪ C) V) (hEU : E ⊆ (A ∪ B) ∪ C)
    (hout : ((A ∪ B) ∪ C) ∪ V ⊆ Fᶜ)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxEV : 2 ≤ expCard w (E ∪ V) ∧ expCard w (E ∪ V) ≤ 2 + d₀) :
    HalfBundleMeanBounds (largeBundleLaw w F m E C) ((A ∪ B) \ E) V := by
  classical
  let ν := largeBundleLaw w F m E C
  have hνnn : WeightNonneg ν := D.clean.law.nn
  have hνtot : totalMass ν = 1 := D.clean.law.tot
  have hAo : A ⊆ Fᶜ :=
    (subset_union_left.trans (subset_union_left.trans subset_union_left)).trans hout
  have hBo : B ⊆ Fᶜ :=
    (subset_union_right.trans (subset_union_left.trans subset_union_left)).trans hout
  have hCo : C ⊆ Fᶜ := (subset_union_right.trans subset_union_left).trans hout
  have hVo : V ⊆ Fᶜ := subset_union_right.trans hout
  have hEo : E ⊆ Fᶜ := (hEU.trans subset_union_left).trans hout
  have hABC : Disjoint (A ∪ B) C := disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hAV : Disjoint A V := hUV.mono_left (subset_union_left.trans subset_union_left)
  have hBV : Disjoint B V := hUV.mono_left (subset_union_right.trans subset_union_left)
  have hCV : Disjoint C V := hUV.mono_left subset_union_right
  have hEV : Disjoint E V := hUV.mono_left hEU
  have hEAB : E \ C ⊆ A ∪ B := by
    intro e he
    exact (mem_union.mp (hEU (mem_sdiff.mp he).1)).resolve_right (mem_sdiff.mp he).2
  have hνE : expCard ν E = 1 := by
    rw [← hνtot]
    unfold expCard totalMass
    apply sum_congr rfl
    intro T _
    by_cases hz : ν T = 0
    · simp [hz]
    · rw [(D.clean.supp T hz).2.1, Nat.cast_one, mul_one]
  have hνC : expCard ν C = 0 :=
    expCard_eq_zero_of_support fun T hT => (D.clean.supp T hT).2.2
  have hνEC : expCard ν (E \ C) = 1 := by
    have hs := expCard_split ν E C
    have hl := expCard_nonneg hνnn (E ∩ C)
    have hu := expCard_mono hνnn (inter_subset_right (s₁ := E) (s₂ := C))
    linarith only [hs, hl, hu, hνE, hνC]
  have hlo : ∀ S, S ⊆ Fᶜ → Disjoint S C →
      expCard w S + expCard w E - expCard w C - 4 * d₀ - 1 ≤ expCard ν S := by
    intro S hS hSC
    have ht := D.clean.mean_lower S hSC
    change _ ≤ expCard ν S at ht
    linarith only [ht, D.lower S hS, D.lower E hEo, D.upper C hCo]
  have hdis : ∀ S, S ⊆ Fᶜ → Disjoint S C → Disjoint S E →
      expCard ν S ≤ expCard w S + expCard w C := by
    intro S hS hSC hSE
    have ht := D.clean.disjoint_upper S hSC hSE
    change expCard ν S ≤ _ at ht
    linarith only [ht, D.upper S hS, D.upper C hCo]
  have hcontains : expCard ν (A ∪ B) ≤
      1 + expCard w (((A ∪ B) ∪ C) \ E) := by
    have ht := D.clean.contains_upper (A ∪ B) hABC hEAB
    change expCard ν (A ∪ B) ≤ _ at ht
    have hu := D.upper (((A ∪ B) ∪ C) \ E)
      (sdiff_subset.trans (subset_union_left.trans hout))
    linarith only [ht, hu]
  have hrawE := abs_le.mp hxE
  have hxAB := expCard_union_of_disjoint w hAB
  have hxU := expCard_union_of_disjoint w hABC
  have hxV := expCard_union_of_disjoint w hEV
  have hxUV := expCard_union_of_disjoint w hUV
  have hxUm := expCard_sdiff_of_subset w hEU
  have hxUVm := expCard_sdiff_of_subset w
    (hEU.trans (subset_union_left (s₁ := (A ∪ B) ∪ C) (s₂ := V)))
  have hVlo : 0.997 ≤ expCard ν V := by
    have ht := hlo V hVo hCV.symm
    have hn : (0.997 : ℝ) ≤ 1 - 2 * r - 5 * d₀ := by norm_num [h, r, d₀]
    linarith only [ht, hxV, hxEV.1, hxC, hn]
  have hVhi : expCard ν V ≤ 1.502 := by
    have ht := hdis V hVo hCV.symm hEV.symm
    have hn : (1.5 : ℝ) + h + 2 * r + 2 * d₀ ≤ 1.502 := by norm_num [h, r, d₀]
    linarith only [ht, hxV, hxEV.2, hrawE.1, hxC, hn]
  have hABlo : 1.9989 ≤ expCard ν (A ∪ B) := by
    have ht := D.clean.contains_lower (A ∪ B) hABC hEAB
    change _ ≤ expCard ν (A ∪ B) at ht
    have hl := D.lower (A ∪ B) (union_subset hAo hBo)
    have hn : (1.9989 : ℝ) ≤ 2 - 2 * r - 2 * d₀ := by norm_num [h, r, d₀]
    linarith only [ht, hl, hxAB, hxA.1, hxB.1, hn]
  have hABhi : expCard ν (A ∪ B) ≤ 2.502 := by
    have hn : (2.5 : ℝ) + h + 2 * r + 3 * d₀ ≤ 2.502 := by norm_num [h, r, d₀]
    linarith only [hcontains, hxUm, hxU, hxAB, hxA.2, hxB.2, hxC, hrawE.1, hn]
  have hABsame : (A ∪ B) \ (E \ C) = (A ∪ B) \ E := by
    ext e
    have hn : e ∈ A ∪ B → e ∉ C := fun he => disjoint_left.mp hABC he
    simp only [mem_sdiff]
    tauto
  have hX := expCard_sdiff_of_subset ν hEAB
  rw [hABsame, hνEC] at hX
  let Y := ((A ∪ B) \ E) ∪ V
  have hYo : Y ⊆ Fᶜ := union_subset (sdiff_subset.trans (union_subset hAo hBo)) hVo
  have hYC : Disjoint Y C := disjoint_union_left.mpr
    ⟨hABC.mono_left sdiff_subset, hCV.symm⟩
  have hYE : Disjoint Y E := disjoint_union_left.mpr ⟨sdiff_disjoint, hEV.symm⟩
  have hYeq : expCard w Y = expCard w ((A ∪ B) \ E) + expCard w V :=
    expCard_union_of_disjoint w
      ((disjoint_union_left.mpr ⟨hAV, hBV⟩).mono_left sdiff_subset)
  have hABsplit := expCard_split w (A ∪ B) E
  have hABcap := expCard_mono hw.nn (inter_subset_right (s₁ := A ∪ B) (s₂ := E))
  have hYsub : Y ⊆ (((A ∪ B) ∪ C) ∪ V) \ E := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_sdiff.mpr ⟨mem_union_left _ (mem_union_left _ (mem_sdiff.mp he).1),
        (mem_sdiff.mp he).2⟩
    · exact mem_sdiff.mpr ⟨mem_union_right _ he, disjoint_left.mp hEV.symm he⟩
  have hYlo : 2.4966 ≤ expCard ν Y := by
    have ht := hlo Y hYo hYC
    have hn : (2.4966 : ℝ) ≤ 2.5 - h - 4 * r - 5 * d₀ := by norm_num [h, r, d₀]
    linarith only [ht, hYeq, hABsplit, hABcap, hxAB, hxA.1, hxB.1,
      hxV, hxEV.1, hrawE.2, hxC, hn]
  have hYhi : expCard ν Y ≤ 3.0025 := by
    have ht := hdis Y hYo hYC hYE
    have hy := expCard_mono hw.nn hYsub
    have hn : (3 : ℝ) + 2 * h + 4 * r + 5 * d₀ ≤ 3.0025 := by norm_num [h, r, d₀]
    linarith only [ht, hy, hxUVm, hxUV, hxU, hxAB, hxV, hxA.2, hxB.2,
      hxEV.2, hrawE.1, hxC, hn]
  exact ⟨by linarith only [hX, hABlo], by linarith only [hX, hABhi],
    hVlo, by linarith only [hVhi], hYlo, hYhi⟩

/-- Reuse 5.24's analytic kernel at the error matching the four-h goodness tail. -/
theorem half_bundle_kernel {ν : Finset ι → ℝ} {k : ℕ} (hν : LawData ν k)
    {X V : Finset ι} (hXV : Disjoint X V)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (X ∪ V)).card)
    (hm : HalfBundleMeanBounds ν X V)
    (htail : 0.399 * h ≤ weightMass ν (fun T => (T ∩ (X ∪ V)).card ≤ 2)) :
    0.0238 * windowError ≤ weightMass ν (fun T =>
      (T ∩ X).card = 1 ∧ (T ∩ V).card = 1) := by
  have hp := window_reuse_parameters
  exact lemma_5_24_kernel hν.st hν.rank hν.nn hν.tot hXV hp.1 hp.2.1 hbase
    hm.union_lower hm.union_upper (by rwa [hp.2.2.2.2.1])
    hm.X_lower hm.X_upper hm.V_lower hm.V_upper

/-- The original-law probability retained by the balanced half-bundle construction. -/
noncomputable def halfBundleProbability : ℝ := 0.499 * (1.99 * h) * (0.0238 * windowError)

/-- The reused kernel clears the common p with more than 1.03e-9 to spare. -/
theorem half_bundle_probability_gt : p + 1.03e-9 < halfBundleProbability := by
  norm_num [halfBundleProbability, windowError, p, h]

end TSPGap.Song

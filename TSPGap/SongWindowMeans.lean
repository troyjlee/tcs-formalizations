/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowTransfers

/-!
# Window means from the original marginal bounds

The eleven means of `WindowMeanBounds` are derived for the actual
face-present-avoid law. All input means belong to the original law.
The geometry is coordinate-generic, so sanitized fiber-tree sides can
instantiate it without projecting arbitrary piece partitions.

The kernel's present bundle is `E \ C`, literally contained in `A ∪ B`.
The support still meets the original bundle E exactly once and avoids C.
The two tail inputs of the kernel remain separate obligations.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Original-law means supply the entire fixed numerical mean packet. -/
theorem window_mean_bounds {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {F : Finset ι} {m : ℕ} {E A B C V : Finset ι}
    (D : WindowConditioningData w F m E C k)
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card = m → (T ∩ E).card ≤ 1)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hUV : Disjoint ((A ∪ B) ∪ C) V) (hEU : E ⊆ (A ∪ B) ∪ C)
    (hout : ((A ∪ B) ∪ C) ∪ V ⊆ Fᶜ)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxEV : 2 ≤ expCard w (E ∪ V) ∧ expCard w (E ∪ V) ≤ 2 + d₀) :
    WindowMeanBounds (largeBundleLaw w F m E C) A B V (E \ C) := by
  classical
  let τ := faceDist w (indicatorCost F) m
  let ν := largeBundleLaw w F m E C
  have hνnn : WeightNonneg ν := D.clean.law.nn
  have hνtot : totalMass ν = 1 := D.clean.law.tot
  have hτone : ∀ T, τ T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => hone T (D.face.supp T hT).1 (D.face.supp T hT).2
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
  have hsE : ∀ T, ν T ≠ 0 → (T ∩ E).card = 1 := fun T hT => (D.clean.supp T hT).2.1
  have hsC : ∀ T, ν T ≠ 0 → (T ∩ C).card = 0 := fun T hT => (D.clean.supp T hT).2.2
  have hνE : expCard ν E = 1 := by
    rw [← hνtot]
    unfold expCard totalMass
    apply sum_congr rfl
    intro T _
    by_cases hz : ν T = 0
    · simp [hz]
    · rw [hsE T hz, Nat.cast_one, mul_one]
  have hνC : expCard ν C = 0 := expCard_eq_zero_of_support hsC
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
  -- The small wrong-side mean is paid in unnormalized mass first.
  have hBE : expCard ν (B ∩ E) ≤ 0.001 := by
    have ht := clean_bundle_part_mean D.face.law D.clean hτone
      (inter_subset_right (s₁ := B) (s₂ := E))
    change expCard ν (B ∩ E) * _ ≤ _ at ht
    have hu := D.upper (B ∩ E) (inter_subset_left.trans hBo)
    have hn := expCard_nonneg hνnn (B ∩ E)
    have hm := mul_le_mul_of_nonneg_left D.clean_mass_ge hn
    have hsmall : h < (0.499 : ℝ) * 0.001 := by norm_num [h]
    nlinarith only [ht, hu, hxBE, hm, hsmall]
  have hEsplit : E ⊆ ((A ∩ E) ∪ (B ∩ E)) ∪ C := by
    intro e he
    have ht := hEU he
    simp only [mem_union, mem_inter] at ht ⊢
    tauto
  have hEνle := (expCard_mono hνnn hEsplit).trans
    (expCard_union_le hνnn ((A ∩ E) ∪ (B ∩ E)) C)
  have hEνle' := expCard_union_le hνnn (A ∩ E) (B ∩ E)
  have hAνsub := expCard_mono hνnn (inter_subset_left (s₁ := A) (s₂ := E))
  have hAlo : 0.997 ≤ expCard ν A := by
    linarith only [hEνle, hEνle', hνE, hνC, hBE, hAνsub]
  have hEwle := (expCard_mono hw.nn hEsplit).trans
    (expCard_union_le hw.nn ((A ∩ E) ∪ (B ∩ E)) C)
  have hEwle' := expCard_union_le hw.nn (A ∩ E) (B ∩ E)
  have hAsplit := expCard_split w A E
  have hAway : expCard ν (A \ E) ≤ 0.5024 := by
    have ht := hdis (A \ E) (sdiff_subset.trans hAo) (hAC.mono_left sdiff_subset)
      sdiff_disjoint
    have hn : (1 / 2 : ℝ) + 2 * h + 4 * r + 3 * d₀ ≤ 0.5024 := by
      norm_num [h, r, d₀]
    linarith only [ht, hAsplit, hEwle, hEwle', hrawE.1, hxBE, hxC, hxA.2, hn]
  have hBlo : 0.4977 ≤ expCard ν B := by
    have ht := hlo B hBo hBC
    have hn : (0.4977 : ℝ) ≤ 1 / 2 - h - 3 * r - 5 * d₀ := by norm_num [h, r, d₀]
    linarith only [ht, hxB.1, hrawE.1, hxC, hn]
  have hBhi : expCard ν B ≤ 1.0026 := by
    have ht := hdis (B \ E) (sdiff_subset.trans hBo) (hBC.mono_left sdiff_subset)
      sdiff_disjoint
    have hs := expCard_split ν B E
    have hb := expCard_mono hw.nn (sdiff_subset (s := B) (t := E))
    have hn : (1.001 : ℝ) + 2 * r + 2 * d₀ ≤ 1.0026 := by norm_num [h, r, d₀]
    linarith only [ht, hs, hb, hBE, hxB.2, hxC, hn]
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
  have hAsame : A \ (E \ C) = A \ E := by
    ext e
    have hn : e ∈ A → e ∉ C := fun he => disjoint_left.mp hAC he
    simp only [mem_sdiff]
    tauto
  have hABsame : (A ∪ B) \ (E \ C) = (A ∪ B) \ E := by
    ext e
    have hn : e ∈ A ∪ B → e ∉ C := fun he => disjoint_left.mp hABC he
    simp only [mem_sdiff]
    tauto
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
  refine ⟨hAlo, ?_, hBlo, hBhi, hVlo, hVhi, hABlo, hABhi, ?_, ?_, ?_⟩
  · rw [hAsame]; exact hAway
  · rw [expCard_union_of_disjoint _ hBV]
    linarith only [hBhi, hVhi]
  · rw [hABsame]; exact hYlo
  · rw [hABsame]; exact hYhi

end TSPGap.Song

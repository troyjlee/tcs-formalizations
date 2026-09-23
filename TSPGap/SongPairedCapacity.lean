/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeCountZero
import TSPGap.SongPairedTables
import TSPGap.SongArithmetic

/-!
# Coefficient extraction from Song's paired mean tables

The absent target `(1,1,2)` uses a support baseline of one in W, at cost
`exp(-3)`. The present target `(1,0,1)` uses the zero-count adapter, at cost
`exp(-2)`. These are probabilities in the final conditioned law; the
restriction mass and the original happy-event identification remain separate.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The absent table shifted by its sure W baseline. -/
theorem paired_absent_mean_profile {w : Finset ι → ℝ} {A U W : Finset ι}
    (hAU : Disjoint A U) (hAW : Disjoint A W) (hUW : Disjoint U W)
    (hm : PairedAbsentMeans w A U W) :
    ThreeMeanProfile ![expCard w A, expCard w U, expCard w W - 1]
      ![0.1098, 0.1098, 0.1098] := by
  obtain ⟨ha, hu, hw, hau, haw, huw, hauw⟩ := hm
  rw [expCard_union_of_disjoint w hAU] at hau
  rw [expCard_union_of_disjoint w hAW] at haw
  rw [expCard_union_of_disjoint w hUW] at huw
  rw [expCard_union_of_disjoint w (disjoint_union_left.mpr ⟨hAW, hUW⟩),
    expCard_union_of_disjoint w hAU] at hauw
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

/-- Add one to the zero-target middle marker, not to the original law. -/
theorem paired_present_mean_profile {w : Finset ι → ℝ} {A U W : Finset ι}
    (hAU : Disjoint A U) (hAW : Disjoint A W) (hUW : Disjoint U W)
    (hm : PairedPresentMeans w A U W) :
    ThreeMeanProfile ![expCard w A, expCard w U + 1, expCard w W]
      ![0.1354, 0.1354, 0.1354] := by
  obtain ⟨ha, hu, hw, hau, haw, huw, hauw⟩ := hm
  rw [expCard_union_of_disjoint w hAU] at hau
  rw [expCard_union_of_disjoint w hAW] at haw
  rw [expCard_union_of_disjoint w hUW] at huw
  rw [expCard_union_of_disjoint w (disjoint_union_left.mpr ⟨hAW, hUW⟩),
    expCard_union_of_disjoint w hAU] at hauw
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

/-- Absent-Z coefficient bound. The sure count is explicit and cannot be
deduced merely from the mean of W. -/
theorem paired_absent_counts {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
    {A U W : Finset ι} (hAU : Disjoint A U) (hAW : Disjoint A W)
    (hUW : Disjoint U W) (hm : PairedAbsentMeans w A U W)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ W).card) :
    (2 / 55 : ℝ) * 0.1098 ^ 3 ≤
      weightMass w (fun T => (T ∩ A).card = 1 ∧ (T ∩ U).card = 1 ∧
        (T ∩ W).card = 2) := by
  have hp := paired_absent_mean_profile hAU hAW hUW hm
  have hprof : ThreeMeanProfile
      (fun j => expCard w (threeBlock A U W j) - if j = 2 then ((2 - 1 : ℕ) : ℝ) else 0)
      ![0.1098, 0.1098, 0.1098] := by
    convert hp using 1
    funext j
    fin_cases j <;> norm_num [threeBlock, Matrix.cons_val_two] <;> decide
  have hb : ∀ j : Fin 3, (0 : ℝ) ≤ ![0.1098, 0.1098, 0.1098] j ∧
      ![0.1098, 0.1098, 0.1098] j ≤ (1 : ℝ) := by
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_two]
  have hh := three_counts_ge_of_mean_profile hw.st hw.rank hw.nn hw.tot A U W
    hAU hAW hUW (Or.inr rfl) hbase hb hprof
  have he : (2 / 55 : ℝ) ≤ Real.exp (-3) := by linarith only [exp_neg_three_gt]
  calc
    _ ≤ Real.exp (-3) * (0.1098 * 0.1098 * 0.1098) := by
      nlinarith only [he]
    _ ≤ _ := hh

theorem exp_neg_two_ge_eighth : (1 / 8 : ℝ) ≤ Real.exp (-2) := by
  have he : Real.exp (2 : ℝ) ≤ 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    exact (mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_d9.le).trans
      (by norm_num)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos 2) he

/-- Present-Z coefficient bound. The U count is zero, not an omitted
constraint or a sure coordinate in the original law. -/
theorem paired_present_counts {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
    {A U W : Finset ι} (hAU : Disjoint A U) (hAW : Disjoint A W)
    (hUW : Disjoint U W) (hm : PairedPresentMeans w A U W) :
    (1 / 8 : ℝ) * 0.1354 ^ 3 ≤
      weightMass w (fun T => (T ∩ A).card = 1 ∧ (T ∩ U).card = 0 ∧
        (T ∩ W).card = 1) := by
  have hp := paired_present_mean_profile hAU hAW hUW hm
  have hprof : ThreeMeanProfile
      (fun j => expCard w (threeBlock A U W j) + if j = 1 then 1 else 0)
      ![0.1354, 0.1354, 0.1354] := by
    convert hp using 1
    funext j
    fin_cases j <;> norm_num [threeBlock, Matrix.cons_val_two]
  have hb : ∀ j : Fin 3, (0 : ℝ) ≤ ![0.1354, 0.1354, 0.1354] j ∧
      ![0.1354, 0.1354, 0.1354] j ≤ (1 : ℝ) := by
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_two]
  have hh := three_counts_zero_ge_of_mean_profile hw.st hw.rank hw.nn hw.tot A U W
    hAU hAW hUW hb hprof
  calc
    _ ≤ Real.exp (-2) * (0.1354 * 0.1354 * 0.1354) := by
      nlinarith only [exp_neg_two_ge_eighth]
    _ ≤ _ := hh

end TSPGap.Song

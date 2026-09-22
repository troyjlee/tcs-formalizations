/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeMeanCapacity

/-!
# Capacity kernels for Lemmas 5.21 and 5.22

The seven mean intervals already available at the conditioned laws suffice.
The 5.21 kernel uses only the supported baseline on its final count; the
5.22 kernel needs no baseline. Both include zero epsilon. These are local
probability improvements, not a change to the global thinning parameter.
-/

namespace TSPGap

/-- A convenient rational lower bound for the three-extraction factor. -/
theorem one_div_twentyone_le_exp_neg_three : (1 : ℝ) / 21 ≤ Real.exp (-3) := by
  have he : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    ring
  have hc : Real.exp (3 : ℝ) ≤ 21 := by
    rw [he]
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by
           gcongr
           exact Real.exp_one_lt_d9.le
         _ ≤ 21 := by norm_num
  simpa only [Real.exp_neg, one_div] using
    one_div_le_one_div_of_le (Real.exp_pos 3) hc

/-- The shifted profile retains the full original 5.21 range `ε ≤ 0.001`. -/
theorem lemma521_capacity_profile_of_le_milli {a b v ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 0.001)
    (ha : 0.5 ≤ a ∧ a ≤ 1.5) (hb : 0.5 ≤ b ∧ b ≤ 1.5)
    (hv : 1.5 ≤ v ∧ v ≤ 2.01)
    (hab : 1.499 ≤ a + b ∧ a + b ≤ 2.01)
    (hav : 2 + 1.9 * ε ≤ a + v ∧ a + v ≤ 3.01)
    (hbv : 2 + 1.9 * ε ≤ b + v ∧ b + v ≤ 3.01)
    (habv : 3 + 1.8 * ε ≤ a + b + v ∧ a + b + v ≤ 4.01) :
    ThreeMeanProfile ![a, b, v - 1] ![0.499, 1.9 * ε, 1.8 * ε] := by
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Capacity bound for the normalized law in Lemma 5.21. -/
theorem lemma_5_21_kernel_capacity {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (h1 : totalMass w = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 0.001)
    (hbase : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ V).card)
    (ha : 0.5 ≤ expCard w A ∧ expCard w A ≤ 1.5)
    (hb : 0.5 ≤ expCard w B ∧ expCard w B ≤ 1.5)
    (hv : 1.5 ≤ expCard w V ∧ expCard w V ≤ 2.01)
    (hab : 1.499 ≤ expCard w (A ∪ B) ∧ expCard w (A ∪ B) ≤ 2.01)
    (hav : 2 + 1.9 * ε ≤ expCard w (A ∪ V) ∧ expCard w (A ∪ V) ≤ 3.01)
    (hbv : 2 + 1.9 * ε ≤ expCard w (B ∪ V) ∧ expCard w (B ∪ V) ≤ 3.01)
    (habv : 3 + 1.8 * ε ≤ expCard w ((A ∪ B) ∪ V) ∧ expCard w ((A ∪ B) ∪ V) ≤ 4.01) :
    0.081 * ε ^ 2 ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ V).card = 2) := by
  rw [expCard_union_of_disjoint w hAB] at hab
  rw [expCard_union_of_disjoint w hAV] at hav
  rw [expCard_union_of_disjoint w hBV] at hbv
  rw [expCard_union_of_disjoint w (Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩),
    expCard_union_of_disjoint w hAB] at habv
  have hp := lemma521_capacity_profile_of_le_milli
    hε0 hε ha hb hv hab hav hbv habv
  have hprofile : ThreeMeanProfile
      (fun j => expCard w (threeBlock A B V j) -
        if j = 2 then ((2 - 1 : ℕ) : ℝ) else 0) ![0.499, 1.9 * ε, 1.8 * ε] := by
    convert hp using 1
    funext j
    fin_cases j <;> norm_num [threeBlock, Matrix.cons_val_two]
    all_goals decide
  have hbounds : ∀ j : Fin 3,
      0 ≤ ![0.499, 1.9 * ε, 1.8 * ε] j ∧ ![0.499, 1.9 * ε, 1.8 * ε] j ≤ 1 := by
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_two] <;> constructor <;> linarith
  have h := three_counts_ge_of_mean_profile hst hr hnn h1 A B V hAB hAV hBV
    (k := 2) (Or.inr rfl) hbase hbounds hprofile
  change Real.exp (-3) * (0.499 * (1.9 * ε) * (1.8 * ε)) ≤ _ at h
  have hprod : 0 ≤ 0.499 * (1.9 * ε) * (1.8 * ε) := by positivity
  calc 0.081 * ε ^ 2 ≤ (1 / 21) * (0.499 * (1.9 * ε) * (1.8 * ε)) := by
         nlinarith only [sq_nonneg ε]
       _ ≤ _ := mul_le_mul_of_nonneg_right one_div_twentyone_le_exp_neg_three hprod
       _ ≤ _ := h

/-- Capacity bound for the normalized law in Lemma 5.22. -/
theorem lemma_5_22_kernel_capacity {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (h1 : totalMass w = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 0.0002)
    (ha : 0.4977 ≤ expCard w A ∧ expCard w A ≤ 1.5)
    (hb : 0.4977 ≤ expCard w B ∧ expCard w B ≤ 1.5)
    (hv : 0.9989 ≤ expCard w V ∧ expCard w V ≤ 1.502)
    (hab : 1.9989 ≤ expCard w (A ∪ B) ∧ expCard w (A ∪ B) ≤ 2.502)
    (hav : 1.99 ≤ expCard w (A ∪ V) ∧ expCard w (A ∪ V) ≤ 3 - 1.49 * ε)
    (hbv : 1.99 ≤ expCard w (B ∪ V) ∧ expCard w (B ∪ V) ≤ 3 - 1.49 * ε)
    (habv : 2.99 ≤ expCard w ((A ∪ B) ∪ V) ∧ expCard w ((A ∪ B) ∪ V) ≤ 4 - 1.6 * ε) :
    0.0522 * ε ^ 2 ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ V).card = 1) := by
  rw [expCard_union_of_disjoint w hAB] at hab
  rw [expCard_union_of_disjoint w hAV] at hav
  rw [expCard_union_of_disjoint w hBV] at hbv
  rw [expCard_union_of_disjoint w (Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩),
    expCard_union_of_disjoint w hAB] at habv
  have hp := lemma522_capacity_profile
    hε0 hε ha hb hv hab hav hbv habv
  have hprofile : ThreeMeanProfile
      (fun j => expCard w (threeBlock A B V j) -
        if j = 2 then ((1 - 1 : ℕ) : ℝ) else 0) ![0.497, 1.49 * ε, 1.49 * ε] := by
    convert hp using 1
    funext j
    fin_cases j <;> norm_num [threeBlock, Matrix.cons_val_two]
  have hbounds : ∀ j : Fin 3,
      0 ≤ ![0.497, 1.49 * ε, 1.49 * ε] j ∧ ![0.497, 1.49 * ε, 1.49 * ε] j ≤ 1 := by
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_two] <;> constructor <;> linarith
  have h := three_counts_ge_of_mean_profile hst hr hnn h1 A B V hAB hAV hBV
    (k := 1) (Or.inl rfl) (by intro S hS; exact Nat.zero_le _) hbounds hprofile
  change Real.exp (-3) * (0.497 * (1.49 * ε) * (1.49 * ε)) ≤ _ at h
  have hprod : 0 ≤ 0.497 * (1.49 * ε) * (1.49 * ε) := by positivity
  calc 0.0522 * ε ^ 2 ≤ (1 / 21) * (0.497 * (1.49 * ε) * (1.49 * ε)) := by
         nlinarith only [sq_nonneg ε]
       _ ≤ _ := mul_le_mul_of_nonneg_right one_div_twentyone_le_exp_neg_three hprod
       _ ≤ _ := h

end TSPGap

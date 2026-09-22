/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Package
import TSPGap.Lemma517Counts

/-!
# The Poisson-branch tails of KKO21 Lemmas 5.21 and 5.22

Both lemmas need point-mass lower bounds on a Bernoulli count at a level
where the mass is of order `ε`.  All of them are instances of Lemma 2.21
(`poi_le_probCount`), no Hoeffding extremal is needed:

* `probCount_two_ge_small`: at mean `p ∈ [1 + η, 2.01]`, `P[X = 2] ≥ 0.97η`
  — the `l = 1` branch `(p−1)e^{−(p−1)}` is the binding one (KKO's
  "`(1.75ε)e^{−1.75ε} ≥ 1.7ε`").  Through the residual shift this gives
  `P[X = 3] ≥ 0.97η` at baseline `1` and `P[X = 4] ≥ 0.97η` at baseline `2`
  (Lemma 5.21's `P[A+B+V = 4] ≥ 1.7ε` and `P[B+V ≥ 3] ≥ 1.75ε`).
* `probCount_two_ge_high`: at mean `p ∈ [1.99, 3 − 1.6ε]`, `P[X = 2] ≥ 0.08ε`
  — here the target is *below* the mean and the `l = 0` branch
  `e^{−p}p²/2 · (1 − p/3)^{p−2}` binds; this is Lemma 5.22's
  `P[A+B+V = 3]`, where KKO's `≥ ε` uses the Hoeffding extremal
  (Theorem 2.15) and costs a factor `≈ 10` here.
-/

namespace TSPGap
open Finset

/-! ### Exponential constants -/

theorem exp_201_le : Real.exp 2.01 ≤ 7.47 := by
  have h1 : Real.exp 2 ≤ 7.39 := exp_two_le
  have h2 : Real.exp 0.01 ≤ 1.0102 := by
    refine le_trans (exp_le_inv_one_sub (by norm_num)) ?_
    norm_num
  have hsplit : Real.exp 2.01 = Real.exp 2 * Real.exp 0.01 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  linarith

theorem exp_101_le : Real.exp 1.01 ≤ 2.747 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h2 : Real.exp 0.01 ≤ 1.0102 := by
    refine le_trans (exp_le_inv_one_sub (by norm_num)) ?_
    norm_num
  have hsplit : Real.exp 1.01 = Real.exp 1 * Real.exp 0.01 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  linarith

theorem exp_three_le : Real.exp 3 ≤ 20.09 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le h1 3
    _ ≤ 20.09 := by norm_num

theorem exp_one_le' : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)

/-! ### The two point-mass bounds at the Bernoulli level -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P[X = 2] ≥ 0.97η` at mean `p ∈ [1 + η, 2.01]`, `η ≤ 0.01`. -/
theorem probCount_two_ge_small {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 0.01)
    (h1 : 1 + η ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 2.01) :
    0.97 * η ≤ Bernoulli.probCount q 2 := by
  obtain ⟨l, hl, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 2
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  set p : ℝ := ∑ i, q i with hp
  have hp1 : 1 + η ≤ p := h1
  have hp2 : p ≤ 2.01 := h2
  have ht0 : 0 ≤ max (p - ((2 : ℕ) : ℝ)) 0 := le_max_right _ _
  have ht1 : max (p - ((2 : ℕ) : ℝ)) 0 ≤ 0.01 :=
    max_le (by push_cast; linarith) (by norm_num)
  interval_cases l
  · -- `l = 0`: `e^{−p} p²/2 · (1 − p/3)^{(p−2)⁺}`, a constant
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, Nat.cast_ofNat]
    have hb0 : (0 : ℝ) < 1 - p / (2 + 1) := by linarith
    have hb1 : 1 - p / (2 + 1) ≤ 1 := by linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - p / (2 + 1)) ≤ 3.04 := by
      rw [div_le_iff₀ hb0]; linarith
    have hone : 1 ≤ 1 / (1 - p / (2 + 1)) := one_le_one_div hb0 hb1
    have hfac' : (0.979 : ℝ) ≤ (1 - p / (2 + 1)) ^ max (p - 2) 0 := by
      have : max (p - ((2 : ℕ) : ℝ)) 0 * (1 / (1 - p / (2 + 1)) - 1) ≤ 0.01 * 2.04 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      push_cast at this hfac
      linarith
    have hpoi : (0.0669 : ℝ) ≤ Bernoulli.poi p 2 := by
      have hexp : 1 / 7.47 ≤ Real.exp (-p) := inv_le_exp_neg hp2 exp_201_le
      have hpow : (1 : ℝ) ≤ p ^ 2 := by nlinarith
      have hf : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [Bernoulli.poi, hf, le_div_iff₀ (by norm_num)]
      nlinarith [hexp, hpow, Real.exp_pos (-p)]
    have hpoinn : 0 ≤ Bernoulli.poi p 2 := by
      rw [Bernoulli.poi]; positivity
    calc 0.97 * η ≤ 0.0669 * 0.979 := by nlinarith
      _ ≤ Bernoulli.poi p 2 * (1 - p / (2 + 1)) ^ max (p - 2) 0 :=
        mul_le_mul hpoi hfac' (by norm_num) hpoinn
  · -- `l = 1`: `e^{−(p−1)} (p−1) · (1 − (p−1)/2)^{(p−2)⁺}`, the binding branch
    simp only [Nat.cast_one]
    have hf : ((2 - 1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
    have hpw : (p - 1) ^ (2 - 1 : ℕ) = p - 1 := by norm_num
    have hpoi_eq : Bernoulli.poi (p - 1) (2 - 1) = Real.exp (-(p - 1)) * (p - 1) := by
      rw [Bernoulli.poi, hf, hpw, div_one]
    have hb0 : (0 : ℝ) < 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ≤ 2.03 := by
      rw [div_le_iff₀ hb0]; norm_num; linarith
    have hone : 1 ≤ 1 / (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) := one_le_one_div hb0 hb1
    have hfac' : (0.989 : ℝ)
        ≤ (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      have : max (p - ((2 : ℕ) : ℝ)) 0
          * (1 / (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) - 1) ≤ 0.01 * 1.03 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 1) (2 - 1) := by
      rw [hpoi_eq]
      have : (0 : ℝ) ≤ p - 1 := by linarith
      positivity
    rcases le_or_gt p 2 with hp2' | hp2'
    · -- `p ≤ 2`: the factor is `1`
      have hmax : max (p - ((2 : ℕ) : ℝ)) 0 = 0 := max_eq_right (by push_cast; linarith)
      rw [hmax, Real.rpow_zero, mul_one, hpoi_eq]
      rcases le_or_gt (p - 1) 0.027 with ht | ht
      · have he : 1 - (p - 1) ≤ Real.exp (-(p - 1)) := by
          have := Real.add_one_le_exp (-(p - 1)); linarith
        nlinarith [Real.exp_pos (-(p - 1))]
      · have he : Real.exp (-1) ≤ Real.exp (-(p - 1)) := Real.exp_le_exp.mpr (by linarith)
        have he1 : 1 / 2.72 ≤ Real.exp (-1) := inv_le_exp_neg le_rfl exp_one_le'
        nlinarith [Real.exp_pos (-(p - 1))]
    · -- `2 < p ≤ 2.01`
      have he : 1 / 2.747 ≤ Real.exp (-(p - 1)) :=
        inv_le_exp_neg (show p - 1 ≤ 1.01 by linarith) exp_101_le
      have hpoi : (0.364 : ℝ) ≤ Bernoulli.poi (p - 1) (2 - 1) := by
        rw [hpoi_eq]; nlinarith [Real.exp_pos (-(p - 1))]
      calc 0.97 * η ≤ 0.364 * 0.989 := by nlinarith
        _ ≤ _ := mul_le_mul hpoi hfac' (by norm_num) hpoinn
  · -- `l = 2`: `e^{−(p−2)} (3 − p)^{(p−2)⁺}`, essentially one
    push_cast at hlp
    simp only [Nat.cast_ofNat, Nat.sub_self]
    have hb0 : (0 : ℝ) < 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ≤ 1.02 := by
      rw [div_le_iff₀ hb0]; norm_num; linarith
    have hone : 1 ≤ 1 / (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) := one_le_one_div hb0 hb1
    have hfac' : (0.999 : ℝ)
        ≤ (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      have : max (p - ((2 : ℕ) : ℝ)) 0
          * (1 / (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) - 1) ≤ 0.01 * 0.02 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      linarith
    have hpoi : (0.99 : ℝ) ≤ Bernoulli.poi (p - 2) 0 := by
      rw [Bernoulli.poi]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have := Real.add_one_le_exp (-(p - 2)); linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 2) 0 := by
      rw [Bernoulli.poi]
      have : (0 : ℝ) ≤ p - 2 := by linarith
      positivity
    calc 0.97 * η ≤ 0.99 * 0.999 := by nlinarith
      _ ≤ _ := mul_le_mul hpoi hfac' (by norm_num) hpoinn

/-- `P[X = 2] ≥ 0.08ε` at mean `p ∈ [1.99, 3 − 1.6ε]`, `0 < ε ≤ 0.0002` — the
below-the-mean regime of Lemma 5.22. -/
theorem probCount_two_ge_high {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 0.0002)
    (h1 : 1.99 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 3 - 1.6 * ε) :
    0.08 * ε ≤ Bernoulli.probCount q 2 := by
  obtain ⟨l, hl, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 2
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  set p : ℝ := ∑ i, q i with hp
  have hp1 : 1.99 ≤ p := h1
  have hp2 : p ≤ 3 - 1.6 * ε := h2
  have ht0 : 0 ≤ max (p - ((2 : ℕ) : ℝ)) 0 := le_max_right _ _
  have ht1 : max (p - ((2 : ℕ) : ℝ)) 0 ≤ 1 := max_le (by push_cast; linarith) (by norm_num)
  interval_cases l
  · -- `l = 0`: `e^{−p} p²/2 · (1 − p/3)^{(p−2)⁺}`, the binding branch
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, Nat.cast_ofNat]
    have hb0 : (0 : ℝ) < 1 - p / (2 + 1) := by linarith
    have hb1 : 1 - p / (2 + 1) ≤ 1 := by linarith
    -- the base is at most one and the exponent at most one, so `b^t ≥ b`
    have hfac : 1 - p / (2 + 1) ≤ (1 - p / (2 + 1)) ^ max (p - 2) 0 := by
      have h := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (show max (p - 2) 0 ≤ 1 by
        push_cast at ht1; exact ht1)
      rw [Real.rpow_one] at h
      exact h
    have hpoinn : 0 ≤ Bernoulli.poi p 2 := by rw [Bernoulli.poi]; positivity
    have hf : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rcases le_or_gt p 2.5 with hp25 | hp25
    · -- `p ≤ 2.5`: a constant
      have hfac2 : (1 / 6 : ℝ) ≤ (1 - p / (2 + 1)) ^ max (p - 2) 0 := by
        refine le_trans ?_ hfac; linarith
      have hpoi : (0.098 : ℝ) ≤ Bernoulli.poi p 2 := by
        have hexp : 1 / 20.09 ≤ Real.exp (-p) :=
          inv_le_exp_neg (show p ≤ 3 by linarith) exp_three_le
        have hpow : (3.96 : ℝ) ≤ p ^ 2 := by nlinarith
        rw [Bernoulli.poi, hf, le_div_iff₀ (by norm_num)]
        nlinarith [hexp, hpow, Real.exp_pos (-p)]
      calc 0.08 * ε ≤ 0.098 * (1 / 6) := by nlinarith
        _ ≤ _ := mul_le_mul hpoi hfac2 (by norm_num) hpoinn
    · -- `2.5 < p ≤ 3 − 1.6ε`: the factor is at least `0.533ε`
      have hfac2 : (0.5333 : ℝ) * ε ≤ (1 - p / (2 + 1)) ^ max (p - 2) 0 := by
        refine le_trans ?_ hfac; linarith
      have hpoi : (0.1555 : ℝ) ≤ Bernoulli.poi p 2 := by
        have hexp : 1 / 20.09 ≤ Real.exp (-p) :=
          inv_le_exp_neg (show p ≤ 3 by linarith) exp_three_le
        have hpow : (6.25 : ℝ) ≤ p ^ 2 := by nlinarith
        rw [Bernoulli.poi, hf, le_div_iff₀ (by norm_num)]
        nlinarith [hexp, hpow, Real.exp_pos (-p)]
      calc 0.08 * ε ≤ 0.1555 * (0.5333 * ε) := by nlinarith
        _ ≤ _ := mul_le_mul hpoi hfac2 (by positivity) hpoinn
  · -- `l = 1`: `e^{−(p−1)} (p−1) · ((3−p)/2)^{(p−2)⁺}`
    simp only [Nat.cast_one]
    have hf : ((2 - 1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
    have hpw : (p - 1) ^ (2 - 1 : ℕ) = p - 1 := by norm_num
    have hpoi_eq : Bernoulli.poi (p - 1) (2 - 1) = Real.exp (-(p - 1)) * (p - 1) := by
      rw [Bernoulli.poi, hf, hpw, div_one]
    have hb0 : (0 : ℝ) < 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac : 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)
        ≤ (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      have h := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 ht1
      rw [Real.rpow_one] at h
      exact h
    have hfac2 : (0.8 : ℝ) * ε
        ≤ (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      refine le_trans ?_ hfac; norm_num; linarith
    have hpoi : (0.133 : ℝ) ≤ Bernoulli.poi (p - 1) (2 - 1) := by
      rw [hpoi_eq]
      have hexp : 1 / 7.39 ≤ Real.exp (-(p - 1)) :=
        inv_le_exp_neg (show p - 1 ≤ 2 by linarith) exp_two_le
      nlinarith [Real.exp_pos (-(p - 1))]
    have hpoinn : 0 ≤ Bernoulli.poi (p - 1) (2 - 1) := by
      rw [hpoi_eq]
      have : (0 : ℝ) ≤ p - 1 := by linarith
      positivity
    calc 0.08 * ε ≤ 0.133 * (0.8 * ε) := by nlinarith
      _ ≤ _ := mul_le_mul hpoi hfac2 (by positivity) hpoinn
  · -- `l = 2`: `e^{−(p−2)} (3 − p)^{(p−2)⁺}`
    push_cast at hlp
    simp only [Nat.cast_ofNat, Nat.sub_self]
    have hb0 : (0 : ℝ) < 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac : 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)
        ≤ (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      have h := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 ht1
      rw [Real.rpow_one] at h
      exact h
    have hfac2 : (1.6 : ℝ) * ε
        ≤ (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      refine le_trans ?_ hfac; norm_num; linarith
    have hpoi : (0.36 : ℝ) ≤ Bernoulli.poi (p - 2) 0 := by
      rw [Bernoulli.poi]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have hexp : 1 / 2.72 ≤ Real.exp (-(p - 2)) :=
        inv_le_exp_neg (show p - 2 ≤ 1 by linarith) exp_one_le'
      linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 2) 0 := by
      rw [Bernoulli.poi]
      have : (0 : ℝ) ≤ p - 2 := by linarith
      positivity
    calc 0.08 * ε ≤ 0.36 * (1.6 * ε) := by nlinarith
      _ ≤ _ := mul_le_mul hpoi hfac2 (by positivity) hpoinn

/-! ### The weight-level versions, through the rank law and the residual shift -/

/-- Baseline `1` forces a sure coordinate, whose removal shifts the count. -/
theorem exists_shift_of_baseline {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) :
    ∃ (m : ℕ) (q : Fin m → ℝ), (∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
      ∧ ∑ i, q i = expCard w F - 1
      ∧ ∀ k, weightMass w (fun T => (T ∩ F).card = k + 1) = Bernoulli.probCount q k := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hq' : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨(hq i).1.le, (hq i).2⟩
  have h0 : Bernoulli.probCount q 0 = 0 := by
    rw [← hlaw 0]
    refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans (weightMass_false w)
    intro S hS
    have := hbase S hS
    exact ⟨fun h => by omega, fun h => h.elim⟩
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero h0
  refine ⟨m, Function.update q j 0, update_zero_mem_Icc hq' j, ?_, fun k => ?_⟩
  · rw [sum_update_zero, hj, hmean]
  · rw [hlaw (k + 1), probCount_succ_update_zero hj k]

/-- `P[X = 3] ≥ 0.97η` at baseline `1` and mean `∈ [2 + η, 3.01]`. -/
theorem weightMass_eq_three_ge_of_baseline_small {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 0.01)
    (hm1 : 2 + η ≤ expCard w F) (hm2 : expCard w F ≤ 3.01) :
    0.97 * η ≤ weightMass w (fun T => (T ∩ F).card = 3) := by
  rcases eq_or_lt_of_le hη0 with hη0' | hηpos
  · rw [← hη0']; simp only [mul_zero]; exact weightMass_nonneg hnn _
  obtain ⟨m, q, hq, hsum, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  rw [show (3 : ℕ) = 2 + 1 from rfl, hlaw 2]
  exact probCount_two_ge_small hq hηpos hη (by rw [hsum]; linarith) (by rw [hsum]; linarith)

/-- `P[X = 4] ≥ 0.97η` at baseline `2` and mean `∈ [3 + η, 4.01]`. -/
theorem weightMass_eq_four_ge_of_baseline_two {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 2 ≤ (T ∩ F).card) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 0.01)
    (hm1 : 3 + η ≤ expCard w F) (hm2 : expCard w F ≤ 4.01) :
    0.97 * η ≤ weightMass w (fun T => (T ∩ F).card = 4) := by
  classical
  rcases eq_or_lt_of_le hη0 with hη0' | hηpos
  · rw [← hη0']; simp only [mul_zero]; exact weightMass_nonneg hnn _
  obtain ⟨m, q, hq, hsum, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot
    (fun T hT => le_trans (by norm_num) (hbase T hT))
  -- the residual still has a sure coordinate
  have h0 : Bernoulli.probCount q 0 = 0 := by
    rw [← hlaw 0]
    refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans (weightMass_false w)
    intro S hS
    have := hbase S hS
    exact ⟨fun h => by omega, fun h => h.elim⟩
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero h0
  rw [show (4 : ℕ) = 2 + 1 + 1 from rfl, hlaw (2 + 1), probCount_succ_update_zero hj 2]
  refine probCount_two_ge_small (update_zero_mem_Icc hq j) hηpos hη ?_ ?_
  · rw [sum_update_zero, hj, hsum]; linarith
  · rw [sum_update_zero, hj, hsum]; linarith

/-- `P[X = 3] ≥ 0.08ε` at baseline `1` and mean `∈ [2.99, 4 − 1.6ε]`. -/
theorem weightMass_eq_three_ge_of_baseline_high {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 0.0002)
    (hm1 : 2.99 ≤ expCard w F) (hm2 : expCard w F ≤ 4 - 1.6 * ε) :
    0.08 * ε ≤ weightMass w (fun T => (T ∩ F).card = 3) := by
  rcases eq_or_lt_of_le hε0 with hε0' | hεpos
  · rw [← hε0']; simp only [mul_zero]; exact weightMass_nonneg hnn _
  obtain ⟨m, q, hq, hsum, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  rw [show (3 : ℕ) = 2 + 1 from rfl, hlaw 2]
  exact probCount_two_ge_high hq hεpos hε (by rw [hsum]; linarith) (by rw [hsum]; linarith)

/-! ### A Markov bound at a baseline -/

/-- `(k − b) · P[X ≥ k] ≤ E[X] − b` on a support with `X ≥ b`. -/
theorem mul_weightMass_ge_le_of_baseline {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {F : Finset ι} {b k : ℕ} (hbk : b ≤ k) (hbase : ∀ T, w T ≠ 0 → b ≤ (T ∩ F).card) :
    ((k : ℝ) - b) * weightMass w (fun T => k ≤ (T ∩ F).card)
      ≤ expCard w F - b * totalMass w := by
  classical
  rw [weightMass, expCard, totalMass, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  by_cases hT : w T = 0
  · simp [hT]
  have hw := hnn T
  have hb := hbase T hT
  split_ifs with hk
  · have : (k : ℝ) ≤ (T ∩ F).card := by exact_mod_cast hk
    nlinarith
  · have : (b : ℝ) ≤ (T ∩ F).card := by exact_mod_cast hb
    nlinarith

end TSPGap

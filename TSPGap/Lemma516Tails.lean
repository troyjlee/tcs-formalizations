/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma2122Tails

/-!
# Tails for KKO21 Lemma 5.16

Two further instances of Lemma 2.21 (`Bernoulli.poi_le_probCount`), for the
case split of Lemma 5.16's kernel on the sum count `Z = δ↑(u)_T + δ(v)_T`
(baseline `1` from `δ(v)`), and their baseline-`1` shifts:

* `P[Y = 1] ≥ 0.25` at mean `∈ [1, 1.1]` (`probCount_one_ge_low`) — the
  `P[X + Y = 1] ≥ 0.25` of KKO's Case 2;
* `P[Y = 2] ≥ 0.036` at mean `∈ [1.1, 2.5]` (`probCount_two_ge_mid`) — above
  the Case 2 window the layer `Z = 3` is at least a constant, so Case 1 applies.

The rpow factors are handled with `b^t ≥ b^{1/2} = √b` for `t ≤ 1/2`, `b ≤ 1`.
-/

namespace TSPGap
open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Exponential bounds -/

theorem exp_le_one_div_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h := Real.add_one_le_exp (-x)
  have hpos : 0 < 1 - x := by linarith
  rw [le_div_iff₀ hpos]
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

theorem exp_25_le : Real.exp 2.5 ≤ 13.2 := by
  have h : Real.exp 2.5 = Real.exp 2 * Real.exp 0.5 := by
    rw [← Real.exp_add]; norm_num
  rw [h]
  have := exp_half_le
  nlinarith [exp_two_le, Real.exp_pos 2, Real.exp_pos 0.5]

theorem exp_15_le : Real.exp 1.5 ≤ 4.84 := by
  have h : Real.exp 1.5 = Real.exp 1 * Real.exp 0.5 := by
    rw [← Real.exp_add]; norm_num
  rw [h]
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have := exp_half_le
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.5]

theorem exp_11_le : Real.exp 1.1 ≤ 3.03 := by
  have h : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by
    rw [← Real.exp_add]; norm_num
  rw [h]
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h2 := exp_le_one_div_one_sub (show (0.1 : ℝ) < 1 by norm_num)
  norm_num at h2
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.1]

/-! ### `b^t ≥ √b` for `t ≤ 1/2` -/

theorem rpow_ge_sqrt {b t : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.sqrt b ≤ b ^ t := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hb0 hb1 ht

theorem sqrt_ge_of_ge {b c : ℝ} (hc : 0 ≤ c) (h : c ^ 2 ≤ b) : c ≤ Real.sqrt b :=
  Real.le_sqrt_of_sq_le h

/-! ### `P[Y = 1] ≥ 0.25` at mean in `[1, 1.1]` -/

theorem probCount_one_ge_low {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 1 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 1.1) :
    0.25 ≤ Bernoulli.probCount q 1 := by
  obtain ⟨l, hl, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 1
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  set p : ℝ := ∑ i, q i with hp
  have hp1 : 1 ≤ p := h1
  have hp2 : p ≤ 1.1 := h2
  have ht0 : 0 ≤ max (p - ((1 : ℕ) : ℝ)) 0 := le_max_right _ _
  have ht1 : max (p - ((1 : ℕ) : ℝ)) 0 ≤ 0.1 := max_le (by push_cast; linarith) (by norm_num)
  interval_cases l
  · -- `l = 0`: `e^{−p} p (1 − p/2)^{(p−1)⁺}`
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, Nat.cast_one]
    have hb0 : (0 : ℝ) < 1 - p / (1 + 1) := by linarith
    have hb1 : 1 - p / (1 + 1) ≤ 1 := by linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - p / (1 + 1)) ≤ 2.23 := by
      rw [div_le_iff₀ hb0]; linarith
    have hone : 1 ≤ 1 / (1 - p / (1 + 1)) := one_le_one_div hb0 hb1
    have hfac' : (0.877 : ℝ) ≤ (1 - p / (1 + 1)) ^ max (p - 1) 0 := by
      have : max (p - ((1 : ℕ) : ℝ)) 0 * (1 / (1 - p / (1 + 1)) - 1) ≤ 0.1 * 1.23 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      push_cast at this hfac
      linarith
    have hpoi : (0.33 : ℝ) ≤ Bernoulli.poi p 1 := by
      have hexp : 1 / 3.03 ≤ Real.exp (-p) := inv_le_exp_neg hp2 exp_11_le
      have hf : ((1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
      rw [Bernoulli.poi, hf, div_one, pow_one]
      nlinarith [hexp, Real.exp_pos (-p)]
    have hpoinn : 0 ≤ Bernoulli.poi p 1 := by
      rw [Bernoulli.poi]; positivity
    calc (0.25 : ℝ) ≤ 0.33 * 0.877 := by norm_num
      _ ≤ Bernoulli.poi p 1 * (1 - p / (1 + 1)) ^ max (p - 1) 0 :=
        mul_le_mul hpoi hfac' (by norm_num) hpoinn
  · -- `l = 1`: `e^{−(p−1)} (2 − p)^{(p−1)⁺}`
    push_cast at hlp
    simp only [Nat.cast_one, Nat.sub_self]
    have hb0 : (0 : ℝ) < 1 - (p - 1) / (((0 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 1) / (((0 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - (p - 1) / (((0 : ℕ) : ℝ) + 1)) ≤ 1.12 := by
      rw [div_le_iff₀ hb0]; norm_num; linarith
    have hone : 1 ≤ 1 / (1 - (p - 1) / (((0 : ℕ) : ℝ) + 1)) := one_le_one_div hb0 hb1
    have hfac' : (0.98 : ℝ)
        ≤ (1 - (p - 1) / (((0 : ℕ) : ℝ) + 1)) ^ max (p - 1) 0 := by
      have : max (p - ((1 : ℕ) : ℝ)) 0
          * (1 / (1 - (p - 1) / (((0 : ℕ) : ℝ) + 1)) - 1) ≤ 0.1 * 0.12 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      push_cast at this hfac
      linarith
    have hpoi : (0.9 : ℝ) ≤ Bernoulli.poi (p - 1) 0 := by
      rw [Bernoulli.poi]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have := Real.add_one_le_exp (-(p - 1)); linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 1) 0 := by
      rw [Bernoulli.poi]
      have : (0 : ℝ) ≤ p - 1 := by linarith
      positivity
    calc (0.25 : ℝ) ≤ 0.9 * 0.98 := by norm_num
      _ ≤ _ := mul_le_mul hpoi hfac' (by norm_num) hpoinn

/-! ### `P[Y = 2] ≥ 0.036` at mean in `[1.1, 2.5]` -/

theorem probCount_two_ge_mid {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 1.1 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 2.5) :
    0.036 ≤ Bernoulli.probCount q 2 := by
  obtain ⟨l, hl, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 2
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  set p : ℝ := ∑ i, q i with hp
  have hp1 : 1.1 ≤ p := h1
  have hp2 : p ≤ 2.5 := h2
  have ht0 : 0 ≤ max (p - ((2 : ℕ) : ℝ)) 0 := le_max_right _ _
  have ht1 : max (p - ((2 : ℕ) : ℝ)) 0 ≤ 1 / 2 := max_le (by push_cast; linarith) (by norm_num)
  have hexp25 : 1 / 13.2 ≤ Real.exp (-p) := inv_le_exp_neg hp2 exp_25_le
  interval_cases l
  · -- `l = 0`: `e^{−p} p²/2 · (1 − p/3)^{(p−2)⁺}`
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, Nat.cast_ofNat]
    have hb0 : (0 : ℝ) < 1 - p / (2 + 1) := by linarith
    have hb1 : 1 - p / (2 + 1) ≤ 1 := by linarith
    have hpoinn : 0 ≤ Bernoulli.poi p 2 := by
      rw [Bernoulli.poi]; positivity
    have hf : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rcases le_or_gt p 2 with hp2' | hp2'
    · -- `p ≤ 2`: the factor is `1`, `poi ≥ e^{−2} · 1.21/2`
      have hmax : max (p - ((2 : ℕ) : ℝ)) 0 = 0 := max_eq_right (by push_cast; linarith)
      push_cast at hmax
      rw [hmax, Real.rpow_zero, mul_one]
      have hexp : 1 / 7.39 ≤ Real.exp (-p) := inv_le_exp_neg hp2' exp_two_le
      have hpow : (1.21 : ℝ) ≤ p ^ 2 := by nlinarith
      rw [Bernoulli.poi, hf, le_div_iff₀ (by norm_num)]
      nlinarith [hexp, hpow, Real.exp_pos (-p)]
    · -- `2 < p ≤ 2.5`: `poi ≥ e^{−2.5} · 2`, factor `≥ √(1/6) ≥ 0.4`
      have hfac : Real.sqrt (1 - p / (2 + 1)) ≤ (1 - p / (2 + 1)) ^ max (p - 2) 0 := by
        have := rpow_ge_sqrt hb0 hb1 ht0 ht1
        push_cast at this
        exact this
      have hsq : (0.4 : ℝ) ≤ Real.sqrt (1 - p / (2 + 1)) :=
        sqrt_ge_of_ge (by norm_num) (by norm_num; linarith)
      have hpoi : (0.15 : ℝ) ≤ Bernoulli.poi p 2 := by
        have hpow : (4 : ℝ) ≤ p ^ 2 := by nlinarith
        rw [Bernoulli.poi, hf, le_div_iff₀ (by norm_num)]
        nlinarith [hexp25, hpow, Real.exp_pos (-p)]
      calc (0.036 : ℝ) ≤ 0.15 * 0.4 := by norm_num
        _ ≤ Bernoulli.poi p 2 * (1 - p / (2 + 1)) ^ max (p - 2) 0 :=
          mul_le_mul hpoi (hsq.trans hfac) (by norm_num) hpoinn
  · -- `l = 1`: `e^{−(p−1)} (p−1) · (1 − (p−1)/2)^{(p−2)⁺}`
    simp only [Nat.cast_one]
    have hf : ((2 - 1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
    have hpw : (p - 1) ^ (2 - 1 : ℕ) = p - 1 := by norm_num
    have hpoi_eq : Bernoulli.poi (p - 1) (2 - 1) = Real.exp (-(p - 1)) * (p - 1) := by
      rw [Bernoulli.poi, hf, hpw, div_one]
    have hb0 : (0 : ℝ) < 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 1) (2 - 1) := by
      rw [hpoi_eq]
      have : (0 : ℝ) ≤ p - 1 := by linarith
      positivity
    rcases le_or_gt p 2 with hp2' | hp2'
    · -- `p ≤ 2`: the factor is `1`, `e^{−(p−1)} (p−1) ≥ e^{−1} · 0.1`
      have hmax : max (p - ((2 : ℕ) : ℝ)) 0 = 0 := max_eq_right (by push_cast; linarith)
      rw [hmax, Real.rpow_zero, mul_one, hpoi_eq]
      have he1 : 1 / 2.72 ≤ Real.exp (-(p - 1)) :=
        inv_le_exp_neg (show p - 1 ≤ 1 by linarith) exp_one_le'
      nlinarith [Real.exp_pos (-(p - 1))]
    · -- `2 < p ≤ 2.5`: `e^{−(p−1)} ≥ e^{−1.5}`, `p − 1 ≥ 1`, factor `≥ √(1/4)`
      have hfac : Real.sqrt (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1))
          ≤ (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 :=
        rpow_ge_sqrt hb0 hb1 ht0 ht1
      have hsq : (0.5 : ℝ) ≤ Real.sqrt (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) :=
        sqrt_ge_of_ge (by norm_num) (by norm_num; linarith)
      have hpoi : (0.2 : ℝ) ≤ Bernoulli.poi (p - 1) (2 - 1) := by
        rw [hpoi_eq]
        have he : 1 / 4.84 ≤ Real.exp (-(p - 1)) :=
          inv_le_exp_neg (show p - 1 ≤ 1.5 by linarith) exp_15_le
        nlinarith [Real.exp_pos (-(p - 1))]
      calc (0.036 : ℝ) ≤ 0.2 * 0.5 := by norm_num
        _ ≤ _ := mul_le_mul hpoi (hsq.trans hfac) (by norm_num) hpoinn
  · -- `l = 2`: `e^{−(p−2)} (3 − p)^{(p−2)⁺} ≥ 0.5 · √0.5`
    push_cast at hlp
    simp only [Nat.cast_ofNat, Nat.sub_self]
    have hb0 : (0 : ℝ) < 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac : Real.sqrt (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1))
        ≤ (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 :=
      rpow_ge_sqrt hb0 hb1 ht0 ht1
    have hsq : (0.7 : ℝ) ≤ Real.sqrt (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) :=
      sqrt_ge_of_ge (by norm_num) (by norm_num; linarith)
    have hpoi : (0.5 : ℝ) ≤ Bernoulli.poi (p - 2) 0 := by
      rw [Bernoulli.poi]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have := Real.add_one_le_exp (-(p - 2)); linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 2) 0 := by
      rw [Bernoulli.poi]
      have : (0 : ℝ) ≤ p - 2 := by linarith
      positivity
    calc (0.036 : ℝ) ≤ 0.5 * 0.7 := by norm_num
      _ ≤ _ := mul_le_mul hpoi (hsq.trans hfac) (by norm_num) hpoinn

/-! ### The baseline-`1` shifts -/

/-- `P[Z = 2] ≥ 0.25` at `E[Z] ∈ [2, 2.1]` for a count with baseline `1`. -/
theorem weightMass_eq_two_ge_of_baseline_low {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hm1 : 2 ≤ expCard w F) (hm2 : expCard w F ≤ 2.1) :
    0.25 ≤ weightMass w (fun T => (T ∩ F).card = 2) := by
  obtain ⟨m, q, hq, hsum, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  have := hlaw 1
  rw [show (1 : ℕ) + 1 = 2 by norm_num] at this
  rw [this]
  exact probCount_one_ge_low hq (by rw [hsum]; linarith) (by rw [hsum]; linarith)

/-- `P[Z = 3] ≥ 0.036` at `E[Z] ∈ [2.1, 3.5]` for a count with baseline `1`. -/
theorem weightMass_eq_three_ge_of_baseline_mid {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hm1 : 2.1 ≤ expCard w F) (hm2 : expCard w F ≤ 3.5) :
    0.036 ≤ weightMass w (fun T => (T ∩ F).card = 3) := by
  obtain ⟨m, q, hq, hsum, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  have := hlaw 2
  rw [show (2 : ℕ) + 1 = 3 by norm_num] at this
  rw [this]
  exact probCount_two_ge_mid hq (by rw [hsum]; linarith) (by rw [hsum]; linarith)

end TSPGap

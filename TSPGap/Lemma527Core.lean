/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Package
import TSPGap.Lemma527Tools
import TSPGap.Lemma517

/-!
# The core of KKO21 Lemma 5.27, at the conditioned law

Once the law `E` of Lemma 5.27 is in place, what remains is one law with two
near-certain count events and a few means:

* `P[U'_T + A'_T = t_U] ≥ 1 − δ` and `P[W'_T + B'_T = t_W] ≥ 1 − δ` (KKO (58),
  with `t_U = t_W = 2` in the `E[Z] ≤ 3ε` case);
* `0.33 ≤ E[A'] ≤ 0.66` and `E[B'] ≤ 0.66` (KKO (59)).

Then `P[B' = 0] ≥ 0.34` (Markov), conditioning on `B' = 0` moves `E[A']` into
`[0.33, 1.32]`, the Bernoulli-sum bound gives `P[A' = 1 | B' = 0] ≥ 0.2`
(KKO's Lemma 2.21 at `k = 1`, `0.237` there), and the two near-certain
events pin `U'` and `W'` by a union bound:

`P[A' = 1 ∧ B' = 0 ∧ U' = t_U − 1 ∧ W' = t_W] ≥ 0.068 − 2δ`

(`lemma_5_27_core`).  KKO normalize the same union bound by `0.019`
("`1 − ε/0.009`"); subtracting is the same estimate, cross-multiplied.

The tail `weightMass_eq_one_ge_of_mean` is the only analytic input: at mean
`p ∈ [0.33, 1.32]` the count is `1` with probability at least `0.2`, from
`poi_le_probCount` with `e^{−x} ≥ (1 − c/16)^16` for `x ≤ c` on seven
subintervals, and `b^t ≥ b^{1/n} ≥ ` (an explicit root) for `t ≤ 1/n`.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Elementary estimates -/

/-- `e^{−x} ≥ (1 − c/n)^n` for `x ≤ c < n`. -/
theorem exp_neg_ge_pow {x c : ℝ} (n : ℕ) (hn : 0 < n) (hx : x ≤ c) (hc0 : 0 ≤ c)
    (hc : c < n) : (1 - c / n) ^ n ≤ Real.exp (-x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : c / n < 1 := by rw [div_lt_one hn']; exact hc
  have hcn0 : 0 ≤ c / n := div_nonneg hc0 hn'.le
  have h1 : Real.exp x ≤ Real.exp c := Real.exp_le_exp.mpr hx
  have h2 : Real.exp c = Real.exp (c / n) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp (c / n) ^ n ≤ (1 / (1 - c / n)) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_inv_one_sub hcn) n
  have h4 : Real.exp x ≤ (1 / (1 - c / n)) ^ n := by rw [← h2] at h3; exact h1.trans h3
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp x := Real.exp_pos x
  calc (1 - c / n) ^ n = ((1 / (1 - c / n)) ^ n)⁻¹ := by
        rw [one_div, inv_pow, inv_inv]
    _ ≤ (Real.exp x)⁻¹ := inv_anti₀ hpos h4

/-- `b^t ≥ b^{1/n} ≥ a` when `a^n ≤ b ≤ 1`, `0 ≤ t ≤ 1/n`. -/
theorem rpow_ge_of_root {a b t : ℝ} (n : ℕ) (hn : n ≠ 0) (ha0 : 0 ≤ a) (hab : a ^ n ≤ b)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (htn : t ≤ ((n : ℕ) : ℝ)⁻¹) : a ≤ b ^ t := by
  have h1 : b ^ (((n : ℕ) : ℝ)⁻¹) ≤ b ^ t :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 htn
  have h2 : (a ^ n) ^ (((n : ℕ) : ℝ)⁻¹) ≤ b ^ (((n : ℕ) : ℝ)⁻¹) :=
    Real.rpow_le_rpow (pow_nonneg ha0 n) hab (by positivity)
  rw [Real.pow_rpow_inv_natCast ha0 hn] at h2
  exact h2.trans h1

/-! ### Counting tails -/

/-- `P[¬Q] = 1 − P[Q]` at total mass one. -/
theorem weightMass_not_eq {w : Finset ι → ℝ} (_hnn : WeightNonneg w) (htot : totalMass w = 1)
    (Q : Finset ι → Prop) :
    weightMass w (fun T => ¬ Q T) = 1 - weightMass w Q := by
  have hor := weightMass_or w Q (fun T => ¬ Q T)
  have hand : weightMass w (fun T => Q T ∧ ¬ Q T) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    exact ⟨fun h => h.2 h.1, fun h => h.elim⟩
  have hall : weightMass w (fun T => Q T ∨ ¬ Q T) = 1 := by
    rw [← htot, ← weightMass_true]
    exact weightMass_congr fun T => ⟨fun _ => trivial, fun _ => em _⟩
  linarith

/-- `P[¬Q] ≤ 1 − P[Q]` at total mass one. -/
theorem weightMass_not_le {w : Finset ι → ℝ} (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (Q : Finset ι → Prop) :
    weightMass w (fun T => ¬ Q T) ≤ 1 - weightMass w Q :=
  (weightMass_not_eq hnn htot Q).le

/-- `P[X ≥ 1] ≤ E[X]`. -/
theorem weightMass_one_le_le_expCard {w : Finset ι → ℝ} (hnn : WeightNonneg w) (F : Finset ι) :
    weightMass w (fun T => 1 ≤ (T ∩ F).card) ≤ expCard w F := by
  unfold weightMass expCard
  refine Finset.sum_le_sum fun T _ => ?_
  split_ifs with h
  · have : (1 : ℝ) ≤ (T ∩ F).card := by exact_mod_cast h
    have := hnn T
    nlinarith
  · exact mul_nonneg (hnn T) (Nat.cast_nonneg _)

/-- `P[X = 0] ≥ 1 − E[X]`. -/
theorem weightMass_eq_zero_ge {w : Finset ι → ℝ} (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (F : Finset ι) : 1 - expCard w F ≤ weightMass w (fun T => (T ∩ F).card = 0) := by
  have h1 := weightMass_one_le_le_expCard hnn F
  have h2 := weightMass_not_eq hnn htot (fun T => 1 ≤ (T ∩ F).card)
  have h3 : weightMass w (fun T => ¬ 1 ≤ (T ∩ F).card)
      = weightMass w (fun T => (T ∩ F).card = 0) :=
    weightMass_congr fun T => by omega
  linarith

/-- **Lemma 2.21 at `k = 1`**: at mean `p ∈ [0.33, 1.32]`, `P[X = 1] ≥ 0.2`. -/
theorem weightMass_eq_one_ge_of_mean {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hm1 : 0.33 ≤ expCard w F) (hm2 : expCard w F ≤ 1.32) :
    (0.2 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card = 1) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean := expCard_eq_sum_of_rankLaw hlaw
  rw [hlaw]
  have hq' : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨(hq i).1.le, (hq i).2⟩
  have hk1 : ((1 : ℕ) : ℝ) - 1 < ∑ i, q i := by rw [← hmean]; push_cast; linarith
  have hk2 : ∑ i, q i < ((1 : ℕ) : ℝ) + 1 := by rw [← hmean]; push_cast; linarith
  obtain ⟨l, hl, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq' 1 hk1 hk2
  rw [← hmean] at hlp hbound
  refine le_trans ?_ hbound
  set p := expCard w F with hp
  interval_cases l
  · -- `l = 0`: `e^{−p} p (1 − p/2)^{max (p−1) 0}`
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, Bernoulli.poi, pow_one,
      Nat.factorial_one, Nat.cast_one, div_one]
    rcases le_or_gt p 1 with hp1 | hp1
    · -- `p ≤ 1`: the factor is `1`
      have hmax : max (p - 1) 0 = 0 := max_eq_right (by linarith)
      rw [hmax, Real.rpow_zero, mul_one]
      -- four subintervals, `e^{−p} ≥ e^{−c} ≥ (1 − c/16)^16`
      rcases le_or_gt p 0.4 with h4 | h4
      · have he := exp_neg_ge_pow 16 (by norm_num) h4 (by norm_num) (by norm_num)
        have : (0.6669 : ℝ) ≤ (1 - 0.4 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        nlinarith
      rcases le_or_gt p 0.5 with h5 | h5
      · have he := exp_neg_ge_pow 16 (by norm_num) h5 (by norm_num) (by norm_num)
        have : (0.601 : ℝ) ≤ (1 - 0.5 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        nlinarith
      rcases le_or_gt p 0.7 with h7 | h7
      · have he := exp_neg_ge_pow 16 (by norm_num) h7 (by norm_num) (by norm_num)
        have : (0.4888 : ℝ) ≤ (1 - 0.7 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        nlinarith
      · have he := exp_neg_ge_pow 16 (by norm_num) hp1 (by norm_num) (by norm_num)
        have : (0.356 : ℝ) ≤ (1 - 1 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        nlinarith
    · -- `1 < p ≤ 1.32`: the factor `(1 − p/2)^{p−1}` is at least an explicit root
      have hmax : max (p - 1) 0 = p - 1 := max_eq_left (by linarith)
      rw [hmax]
      have hb0 : (0 : ℝ) < 1 - p / (1 + 1) := by linarith
      have hb1 : 1 - p / (1 + 1) ≤ 1 := by linarith
      rcases le_or_gt p 1.16 with h16 | h16
      · have he := exp_neg_ge_pow 16 (by norm_num) h16 (by norm_num) (by norm_num)
        have h1 : (0.299 : ℝ) ≤ (1 - 1.16 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        have hf : (0.86 : ℝ) ≤ (1 - p / (1 + 1)) ^ (p - 1) :=
          rpow_ge_of_root 6 (by norm_num) (by norm_num) (by norm_num; linarith) hb0 hb1
            (by norm_num; linarith)
        have hpe : (0.299 : ℝ) * 1 ≤ Real.exp (-p) * p :=
          mul_le_mul (h1.trans he) hp1.le (by norm_num) (Real.exp_pos _).le
        nlinarith [mul_le_mul hpe hf (by norm_num) (by positivity)]
      rcases le_or_gt p 1.24 with h24 | h24
      · have he := exp_neg_ge_pow 16 (by norm_num) h24 (by norm_num) (by norm_num)
        have h1 : (0.274 : ℝ) ≤ (1 - 1.24 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        have hf : (0.78 : ℝ) ≤ (1 - p / (1 + 1)) ^ (p - 1) :=
          rpow_ge_of_root 4 (by norm_num) (by norm_num) (by norm_num; linarith) hb0 hb1
            (by norm_num; linarith)
        have hpe : (0.274 : ℝ) * 1.16 ≤ Real.exp (-p) * p :=
          mul_le_mul (h1.trans he) h16.le (by norm_num) (Real.exp_pos _).le
        nlinarith [mul_le_mul hpe hf (by norm_num) (by positivity)]
      · have he := exp_neg_ge_pow 16 (by norm_num) hm2 (by norm_num) (by norm_num)
        have h1 : (0.252 : ℝ) ≤ (1 - 1.32 / (16 : ℕ)) ^ (16 : ℕ) := by norm_num
        have hf : (0.69 : ℝ) ≤ (1 - p / (1 + 1)) ^ (p - 1) :=
          rpow_ge_of_root 3 (by norm_num) (by norm_num) (by norm_num; linarith) hb0 hb1
            (by norm_num; linarith)
        have hpe : (0.252 : ℝ) * 1.24 ≤ Real.exp (-p) * p :=
          mul_le_mul (h1.trans he) h24.le (by norm_num) (Real.exp_pos _).le
        nlinarith [mul_le_mul hpe hf (by norm_num) (by positivity)]
  · -- `l = 1`: `e^{−(p−1)} (2 − p)^{p−1}`, with `1 ≤ p`
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hlp
    have hmax : max (p - 1) 0 = p - 1 := max_eq_left (by linarith)
    rw [Nat.cast_one, Nat.sub_self, Nat.cast_zero, zero_add, div_one, hmax, Bernoulli.poi,
      pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
    have he : (0.68 : ℝ) ≤ Real.exp (-(p - 1)) := by
      have := Real.add_one_le_exp (-(p - 1)); linarith
    have hb0 : (0 : ℝ) < 1 - (p - 1) := by linarith
    have hb1 : 1 - (p - 1) ≤ 1 := by linarith
    have hf : (0.87 : ℝ) ≤ (1 - (p - 1)) ^ (p - 1) :=
      rpow_ge_of_root 3 (by norm_num) (by norm_num) (by norm_num; linarith) hb0 hb1
        (by norm_num; linarith)
    nlinarith [mul_le_mul he hf (by norm_num) (Real.exp_pos _).le]

/-! ### The core -/

/-- **The core of Lemma 5.27.** -/
theorem lemma_5_27_core {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {U' A' W' B' : Finset ι} (hAB : Disjoint A' B') {tU tW : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hUA : 1 - δ ≤ weightMass ν (fun T => (T ∩ U').card + (T ∩ A').card = tU))
    (hWB : 1 - δ ≤ weightMass ν (fun T => (T ∩ W').card + (T ∩ B').card = tW))
    (hA1 : 0.33 ≤ expCard ν A') (hA2 : expCard ν A' ≤ 0.66) (hB2 : expCard ν B' ≤ 0.66) :
    0.068 - 2 * δ ≤ weightMass ν (fun T =>
      (T ∩ A').card = 1 ∧ (T ∩ B').card = 0 ∧ (T ∩ U').card + 1 = tU ∧ (T ∩ W').card = tW) := by
  classical
  -- `P[B' = 0] ≥ 0.34`, and the law conditioned on it
  have hB0 : (0.34 : ℝ) ≤ weightMass ν (fun T => (T ∩ B').card = 0) := by
    have := weightMass_eq_zero_ge hnn htot B'; linarith
  have hmass : 0 < totalMass (avoidWeight ν B') := by
    rw [totalMass_avoidWeight]; linarith
  have hnorm := fixedRankNormalized_avoidDist hr hnn hmass
  have hσst := isRealStable_genPoly_avoidDist hst hr hnn hmass
  have hσnn : WeightNonneg (avoidDist ν B') := hnorm.nonneg
  have hσtot : totalMass (avoidDist ν B') = 1 := hnorm.total
  have hσrank : FixedRankWeight r (avoidDist ν B') := fun S hS => by
    by_contra hc; exact hS (hnorm.supported S hc)
  have hσA1 : 0.33 ≤ expCard (avoidDist ν B') A' :=
    hA1.trans (expCard_avoidDist_ge hst hr hnn htot hAB hmass)
  have hσA2 : expCard (avoidDist ν B') A' ≤ 1.32 :=
    (expCard_avoidDist_le hst hr hnn htot hAB hmass).trans (by linarith)
  have hσ1 := weightMass_eq_one_ge_of_mean hσst hσrank hσnn hσtot hσA1 hσA2
  -- unwind: `P[A' = 1 ∧ B' = 0] ≥ 0.2 · 0.34`
  have hjoint : (0.068 : ℝ) ≤ weightMass ν (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 0) := by
    rw [← weightMass_avoidDist_mul hmass, totalMass_avoidWeight]
    calc (0.068 : ℝ) = 0.2 * 0.34 := by norm_num
      _ ≤ _ := mul_le_mul hσ1 hB0 (by norm_num) (weightMass_nonneg hσnn _)
  -- pin `U'` and `W'` by the two near-certain events
  have hnot1 := weightMass_not_le hnn htot (fun T => (T ∩ U').card + (T ∩ A').card = tU)
  have hnot2 := weightMass_not_le hnn htot (fun T => (T ∩ W').card + (T ∩ B').card = tW)
  have h1 := weightMass_and_ge_sub hnn (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 0)
    (fun T => (T ∩ U').card + (T ∩ A').card = tU)
  have h2 := weightMass_and_ge_sub hnn
    (fun T => ((T ∩ A').card = 1 ∧ (T ∩ B').card = 0) ∧ (T ∩ U').card + (T ∩ A').card = tU)
    (fun T => (T ∩ W').card + (T ∩ B').card = tW)
  have hmono : weightMass ν (fun T =>
      (((T ∩ A').card = 1 ∧ (T ∩ B').card = 0) ∧ (T ∩ U').card + (T ∩ A').card = tU)
        ∧ (T ∩ W').card + (T ∩ B').card = tW)
      ≤ weightMass ν (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 0
          ∧ (T ∩ U').card + 1 = tU ∧ (T ∩ W').card = tW) :=
    weightMass_mono hnn fun T h => by omega
  linarith

end TSPGap

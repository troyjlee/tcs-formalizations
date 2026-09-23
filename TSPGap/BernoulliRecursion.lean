/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankSequence
import TSPGap.CountEstimates
import TSPGap.LogConcave
import TSPGap.RankTail
import TSPGap.Lemma527Core

/-!
# The Bernoulli recursion and `P[X ≥ 2]` at mean at least `1.99`

Splitting one coordinate off the Bernoulli generating polynomial
`∏ (q_i X + (1 − q_i))` gives the recursion

`P_q[k+1] = (1 − q_j) P_{q'}[k+1] + q_j P_{q'}[k]`,  `P_q[0] = (1 − q_j) P_{q'}[0]`,

where `q'` sets `q_j` to zero (`probCount_succ_split`, `probCount_zero_split`).
With it, `P[X ≤ 1] ≤ 0.76` whenever the mean is at least `1.99`
(`probCount_le_one_le_of_mean`): if some `q_j ≥ 1/2` the recursion gives
`P[X ≤ 1] ≤ (1 − q_j) + q_j e^{−(m − q_j)}`; otherwise
`P[X = 1] ≤ 2m · P[X = 0]` and `e^{−m}(1 + 2m) ≤ 0.74`.  This is the
`k = 2`, constant-level instance of KKO's Lemma 2.22 that Lemma 5.22's layer
tails need (KKO: `0.59`; here `0.24`), axiom-free.
-/

namespace TSPGap
open Polynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The recursion -/

theorem bernoulli_prod_split (q : ι → ℝ) (j : ι) :
    (∏ i : ι, (C (q i) * X + C (1 - q i)))
      = (C (q j) * X + C (1 - q j))
        * ∏ i : ι, (C (Function.update q j 0 i) * X + C (1 - Function.update q j 0 i)) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  rw [Function.update_self]
  have h1 : C (0 : ℝ) * X + C (1 - 0) = 1 := by simp
  rw [h1, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem probCount_zero_split (q : ι → ℝ) (j : ι) :
    Bernoulli.probCount q 0 = (1 - q j) * Bernoulli.probCount (Function.update q j 0) 0 := by
  rw [Bernoulli.probCount_eq_coeff, Bernoulli.probCount_eq_coeff, bernoulli_prod_split q j,
    coeff_bernoulli_mul_zero]

theorem probCount_succ_split (q : ι → ℝ) (j : ι) (k : ℕ) :
    Bernoulli.probCount q (k + 1)
      = (1 - q j) * Bernoulli.probCount (Function.update q j 0) (k + 1)
        + q j * Bernoulli.probCount (Function.update q j 0) k := by
  rw [Bernoulli.probCount_eq_coeff, Bernoulli.probCount_eq_coeff, Bernoulli.probCount_eq_coeff,
    bernoulli_prod_split q j, coeff_bernoulli_mul_succ]

/-! ### Positivity and the total mass -/

theorem atomProb_nonneg {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (t : Finset ι) :
    0 ≤ Bernoulli.atomProb q t := by
  unfold Bernoulli.atomProb
  exact mul_nonneg (Finset.prod_nonneg fun i _ => (hq i).1)
    (Finset.prod_nonneg fun i _ => by linarith [(hq i).2])

theorem probCount_nonneg {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ Bernoulli.probCount q k := by
  rw [Bernoulli.probCount_def]
  exact Finset.sum_nonneg fun t _ => atomProb_nonneg hq t

theorem probCount_zero_add_one_le_one {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) :
    Bernoulli.probCount q 0 + Bernoulli.probCount q 1 ≤ 1 := by
  have h := sum_range_probCount_eq_one q (N := Fintype.card ι + 1) (Nat.le_succ _)
  have h2 : ∑ j ∈ Finset.range 2, Bernoulli.probCount q j
      ≤ ∑ j ∈ Finset.range (Fintype.card ι + 1 + 1), Bernoulli.probCount q j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun j _ _ => probCount_nonneg hq j
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
  linarith

/-! ### `P[X = 1]` and the two-case bound -/

/-- `P[X = 1] = ∑ᵢ qᵢ ∏_{k ≠ i} (1 − q_k)`. -/
theorem probCount_one_eq (q : ι → ℝ) :
    Bernoulli.probCount q 1 = ∑ i, q i * ∏ k ∈ Finset.univ.erase i, (1 - q k) := by
  rw [Bernoulli.probCount_def, Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  unfold Bernoulli.atomProb
  rw [Finset.prod_singleton, Finset.sdiff_singleton_eq_erase]

/-- When every `qᵢ ≤ 1/2`, `P[X = 1] ≤ 2 (∑ qᵢ) P[X = 0]`. -/
theorem probCount_one_le_of_small {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ∀ i, q i ≤ 1 / 2) :
    Bernoulli.probCount q 1 ≤ 2 * (∑ i, q i) * Bernoulli.probCount q 0 := by
  rw [probCount_one_eq, probCount_zero_eq_prod, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hprod : ∏ k, (1 - q k) = (1 - q i) * ∏ k ∈ Finset.univ.erase i, (1 - q k) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have hnn : 0 ≤ ∏ k ∈ Finset.univ.erase i, (1 - q k) :=
    Finset.prod_nonneg fun k _ => by linarith [(hq k).2]
  have h1 : ∏ k ∈ Finset.univ.erase i, (1 - q k)
      ≤ 2 * (1 - q i) * ∏ k ∈ Finset.univ.erase i, (1 - q k) := by
    have : (1 : ℝ) ≤ 2 * (1 - q i) := by linarith [hsmall i]
    nlinarith
  rw [hprod]
  have := (hq i).1
  nlinarith

theorem exp_199_ge : (6.74 : ℝ) ≤ Real.exp 1.99 := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h2 : (2.48 : ℝ) ≤ Real.exp 0.99 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.99 by norm_num)
    linarith
  have hsplit : Real.exp 1.99 = Real.exp 1 * Real.exp 0.99 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.99]

/-- **`P[X ≤ 1] ≤ 0.76` at mean at least `1.99`.** -/
theorem probCount_le_one_le_of_mean {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (hm : 1.99 ≤ ∑ i, q i) :
    Bernoulli.probCount q 0 + Bernoulli.probCount q 1 ≤ 0.76 := by
  by_cases hbig : ∃ j, 1 / 2 ≤ q j
  · obtain ⟨j, hj⟩ := hbig
    have hq' := update_zero_mem_Icc hq j
    have h0 := probCount_zero_split q j
    have h1 := probCount_succ_split q j 0
    have hsum' : ∑ i, Function.update q j 0 i = (∑ i, q i) - q j := sum_update_zero q j
    have hle1 := probCount_zero_add_one_le_one hq'
    have hP'0 : Bernoulli.probCount (Function.update q j 0) 0
        ≤ Real.exp (-∑ i, Function.update q j 0 i) :=
      probCount_zero_le_exp _ fun i => (hq' i).2
    have hexp : Real.exp (-∑ i, Function.update q j 0 i) ≤ 1 / 1.99 := by
      rw [hsum']
      have hx : (1.99 : ℝ) ≤ Real.exp ((∑ i, q i) - q j) := by
        have := Real.add_one_le_exp ((∑ i, q i) - q j)
        linarith [(hq j).2]
      rw [Real.exp_neg]
      exact inv_le_of_inv_le₀ (by norm_num) (by rw [one_div, inv_inv]; exact hx)
    have hP'0' : Bernoulli.probCount (Function.update q j 0) 0 ≤ 1 / 1.99 := hP'0.trans hexp
    have hn0 := probCount_nonneg hq' 0
    have hn1 := probCount_nonneg hq' 1
    have hq0 := (hq j).1
    have hq1 := (hq j).2
    have e1 : (1 - q j) * (Bernoulli.probCount (Function.update q j 0) 0
        + Bernoulli.probCount (Function.update q j 0) 1) ≤ (1 - q j) * 1 :=
      mul_le_mul_of_nonneg_left hle1 (by linarith)
    have e2 : q j * Bernoulli.probCount (Function.update q j 0) 0 ≤ q j * (1 / 1.99) :=
      mul_le_mul_of_nonneg_left hP'0' hq0
    rw [h0, h1]
    nlinarith [e1, e2]
  · push_neg at hbig
    have hP1 := probCount_one_le_of_small hq fun i => (hbig i).le
    have hP0 := probCount_zero_le_exp q fun i => (hq i).2
    have hn0 := probCount_nonneg hq 0
    -- `e^{−m}(1 + 2m) ≤ 0.74` for `m ≥ 1.99`
    have hbound : Real.exp (-∑ i, q i) * (1 + 2 * ∑ i, q i) ≤ 0.74 := by
      set m := ∑ i, q i with hmdef
      have ht : 0 ≤ m - 1.99 := by linarith
      have hsplit : Real.exp (-m) = Real.exp (-1.99) * Real.exp (-(m - 1.99)) := by
        rw [← Real.exp_add]; ring_nf
      have h2 : Real.exp (-(m - 1.99)) * (1 + (m - 1.99)) ≤ 1 := by
        have := Real.add_one_le_exp (m - 1.99)
        have hpos := Real.exp_pos (m - 1.99)
        rw [Real.exp_neg]
        rw [inv_mul_le_iff₀ hpos]
        linarith
      have h3 : Real.exp (-1.99) ≤ 0.1484 := by
        rw [Real.exp_neg]
        exact inv_le_of_inv_le₀ (by norm_num) (le_trans (by norm_num) exp_199_ge)
      have h4 : 1 + 2 * m ≤ 4.98 * (1 + (m - 1.99)) := by linarith
      have hE := Real.exp_pos (-(m - 1.99))
      calc Real.exp (-m) * (1 + 2 * m)
          = Real.exp (-1.99) * (Real.exp (-(m - 1.99)) * (1 + 2 * m)) := by rw [hsplit]; ring
        _ ≤ Real.exp (-1.99) * (Real.exp (-(m - 1.99)) * (4.98 * (1 + (m - 1.99)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hE.le) (Real.exp_pos _).le
        _ = Real.exp (-1.99) * 4.98 * (Real.exp (-(m - 1.99)) * (1 + (m - 1.99))) := by ring
        _ ≤ 0.1484 * 4.98 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right h3 (by norm_num)) h2 (by positivity)
              (by norm_num)
        _ ≤ 0.74 := by norm_num
    have hm0 : 0 ≤ 1 + 2 * ∑ i, q i := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hP0 hm0]

/-- **Lemma 2.22 at `k = 2`, constant level**: `P[X ≥ 2] ≥ 0.24` at mean `≥ 1.99`. -/
theorem weightMass_two_le_ge_of_mean_199 {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hmean : 1.99 ≤ expCard w F) :
    (0.24 : ℝ) ≤ weightMass w (fun T => 2 ≤ (T ∩ F).card) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean' : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hq' : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨(hq i).1.le, (hq i).2⟩
  have h := probCount_le_one_le_of_mean hq' (by rw [← hmean']; exact hmean)
  rw [← hlaw 0, ← hlaw 1] at h
  have hor := weightMass_or w (fun T => (T ∩ F).card = 0) (fun T => (T ∩ F).card = 1)
  have hand : weightMass w (fun T => (T ∩ F).card = 0 ∧ (T ∩ F).card = 1) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    exact ⟨fun h => by omega, fun h => h.elim⟩
  have hall : weightMass w (fun T => (T ∩ F).card = 0 ∨ (T ∩ F).card = 1)
      = weightMass w (fun T => (T ∩ F).card ≤ 1) := weightMass_congr fun T => by omega
  have hne := weightMass_not_eq hnn htot (fun T => (T ∩ F).card ≤ 1)
  have hc : weightMass w (fun T => ¬ (T ∩ F).card ≤ 1) = weightMass w (fun T => 2 ≤ (T ∩ F).card) :=
    weightMass_congr fun T => by omega
  linarith

end TSPGap

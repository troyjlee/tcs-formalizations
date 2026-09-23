/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1KernelBudget
import TSPGap.LemmaA1Tails
import TSPGap.Lemma523

/-!
# The conditioned tail package for KKO21 Lemma A.1

`lemma_A1_conditioned_kernel_budget` consumes nine estimates on the conditioned law
`ν`.  This file derives all nine from **means** at `ν` and two **transferred
tails**, and chains the result into `lemma_A1_conditioned_budget`.
The legacy fixed-tail `lemma_A1_conditioned` statement is retained as a wrapper.

## The data

Cells `A`, `B`, `V` (pairwise disjoint), a bundle `E ⊆ A ∪ B` that is
one-hot present under `ν`, and the bundle-free set
`F' := ((A ∪ B) \ E) ∪ V`, on which a supported tree has at least one edge
(it crosses `u ∪ v`).  With `F := (A ∪ B) ∪ V`, `|T ∩ F| = |T ∩ F'| + 1` on
the support.

## Where each kernel hypothesis comes from

* `hm3` — the PF₂ bootstrap on `F'`: `P[F' = 3] ≥ 0.14` from the baseline
  and the mean (`weightMass_eq_three_ge_of_baseline`), and the transferred
  Lemma 5.15 tail `P[F' ≤ 2] ≥ 0.22ε`.
* `hXge`, `hXle`, `hVge`, `hVle` — one-cell tails from the means.
* `hAge`, `hBge` — Lemma 5.4 in product form (`layerProduct_le_of_ge_le`):
  `P[A ≥ 1] ≥ 0.63` (mean `≥ 0.997`, the bundle's own cell) times the Markov
  tail `P[B ∪ V ≤ 2] ≥ 0.1648`; and `P[B ≥ 1] ≥ 0.39` (mean `≥ 0.4977`)
  times the transferred tail `P[A ∪ V ≤ 2] ≥ ℓε`.
* `hAle`, `hBle` — 🔑 **not** the product form: the antitone layer
  monotonicity (`layer_le_anti` through `crossTail`) gives
  `P[Q | F = 3] ≥ P[Q] − P[F ≤ 2]` for a decreasing `Q`, and
  `P[F ≤ 2] = P[F' = 1] ≤ e^{−1.4966} ≤ 0.23` by the residual exponential.
  This avoids the `P[B ∪ V ≥ 2] ≥ 0.59` tail, which would need a Poisson
  comparison at means above `2`.

The last two estimates actually give `0.2676` and `0.268`. The budget
version retains `0.267` on both sides, instead of weakening them to the
original kernel's `0.147`. For `0 ≤ ℓ ≤ 100` it gives conditioned mass
`0.0024ℓε²`. The legacy fixed-tail wrapper specializes `ℓ = 7.75` and weakens
the result. The paper-facing assembly uses `ℓ = 4.75`, which suffices for
the original `5ε` ambient tail and `0.005ε²` happy-mass conclusion.

## Replacement estimates and the paper's ambient threshold

KKO's `P_ν[· ≥ 1 | A+B+V = 3] ≥ 3.02ε` is `0.63 · 4.8ε`, but `0.63` needs
mean `≥ 0.997`, which only the bundle's own cell has; the bundle-free cell
has mean `≥ 0.4977` and `P[≥ 1] ≥ 0.39`. The earlier fixed-tail proof
compensated with a transferred tail `7.75ε` and an ambient threshold `8ε`.
The budget theorem's stronger `0.267` bounds remove that extra requirement:
`ℓ = 4.75` yields `0.00119 × 4.75 = 0.0056525` after lifting, so the
exported Lemma A.1 now has the paper's `5ε` threshold. This replacement
does not rely on the disputed `0.63` estimate for the bundle-free cell.

The paper's `p₃ ≥ 1/4` is `0.2507` at the true residual mean `1.4966`;
the PF₂ bootstrap only needs `0.14`, which is what is proved.
-/

namespace TSPGap
open Finset

/-! ### Exponential bounds -/

theorem exp_half_ge : (1.6487 : ℝ) ≤ Real.exp 0.5 := by
  have h : Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := Real.exp_half 1
  have hnorm : (0.5 : ℝ) = 1 / 2 := by norm_num
  rw [hnorm, h, Real.le_sqrt (by positivity) (by positivity)]
  have := Real.exp_one_gt_d9
  norm_num
  linarith

theorem exp_997_ge : (2.7028 : ℝ) ≤ Real.exp 0.997 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (0.997 : ℝ) ≤ Real.exp (-0.003) := by
    have := Real.add_one_le_exp (-0.003 : ℝ)
    linarith
  have hsplit : Real.exp 0.997 = Real.exp 1 * Real.exp (-0.003) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
  linarith

theorem exp_4977_ge : (1.6394 : ℝ) ≤ Real.exp 0.4977 := by
  have h1 := exp_half_ge
  have h2 : (0.9977 : ℝ) ≤ Real.exp (-0.0023) := by
    have := Real.add_one_le_exp (-0.0023 : ℝ)
    linarith
  have hsplit : Real.exp 0.4977 = Real.exp 0.5 * Real.exp (-0.0023) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 0.5).le
  linarith

theorem exp_14966_ge : (4.35 : ℝ) ≤ Real.exp 1.4966 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (1.6199 : ℝ) ≤ Real.exp 0.4966 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.4966 by norm_num)
    norm_num at this
    linarith
  have hsplit : Real.exp 1.4966 = Real.exp 1 * Real.exp 0.4966 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
  linarith

theorem exp_20025_le : Real.exp 2.0025 ≤ 7.41 := by
  have h1 : Real.exp 2 ≤ 7.39 := exp_two_le
  have h2 : Real.exp 0.0025 ≤ 1.00251 := by
    refine le_trans (exp_le_inv_one_sub (by norm_num)) ?_
    norm_num
  have hsplit : Real.exp 2.0025 = Real.exp 2 * Real.exp 0.0025 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  linarith

theorem exp_10025_le : Real.exp 1.0025 ≤ 2.7252 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h2 : Real.exp 0.0025 ≤ 1.00251 := by
    refine le_trans (exp_le_inv_one_sub (by norm_num)) ?_
    norm_num
  have hsplit : Real.exp 1.0025 = Real.exp 1 * Real.exp 0.0025 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have := mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  linarith

/-- A small real power of a base in `(0, 1]` stays close to `1`. -/
theorem rpow_ge_one_sub_mul {b t : ℝ} (hb0 : 0 < b) (_hb1 : b ≤ 1) (ht0 : 0 ≤ t) :
    1 - t * (1 / b - 1) ≤ b ^ t := by
  rw [Real.rpow_def_of_pos hb0]
  have hlog : 1 - 1 / b ≤ Real.log b := by
    have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hb0)
    rw [Real.log_div (by norm_num) hb0.ne', Real.log_one, zero_sub] at h
    linarith
  have h1 := Real.add_one_le_exp (Real.log b * t)
  have h2 : (1 - 1 / b) * t ≤ Real.log b * t := mul_le_mul_of_nonneg_right hlog ht0
  nlinarith

/-! ### One-cell tails at the needed means -/

section Tails

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P[N ≥ 1] ≥ 0.63` at mean `≥ 0.997`. -/
theorem weightMass_one_le_ge_997 {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hmean : 0.997 ≤ expCard w F) :
    (0.63 : ℝ) ≤ weightMass w (fun T => 1 ≤ (T ∩ F).card) := by
  have h := one_sub_exp_le_weightMass_one_le hst hr hnn htot F
  have hle : Real.exp (-(expCard w F)) ≤ Real.exp (-0.997) :=
    Real.exp_le_exp.mpr (by linarith)
  have hval : Real.exp (-0.997) ≤ 0.37 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := exp_997_ge
    norm_num
    linarith
  linarith

/-- `P[N ≥ 1] ≥ 0.39` at mean `≥ 0.4977`. -/
theorem weightMass_one_le_ge_4977 {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hmean : 0.4977 ≤ expCard w F) :
    (0.39 : ℝ) ≤ weightMass w (fun T => 1 ≤ (T ∩ F).card) := by
  have h := one_sub_exp_le_weightMass_one_le hst hr hnn htot F
  have hle : Real.exp (-(expCard w F)) ≤ Real.exp (-0.4977) :=
    Real.exp_le_exp.mpr (by linarith)
  have hval : Real.exp (-0.4977) ≤ 0.61 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := exp_4977_ge
    norm_num
    linarith
  linarith

/-- Markov at three, no baseline: `3 · P[N ≥ 3] ≤ E[N]`. -/
theorem three_mul_weightMass_three_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) :
    3 * weightMass w (fun T => 3 ≤ (T ∩ F).card) ≤ expCard w F := by
  classical
  rw [weightMass, expCard, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases h : 3 ≤ (S ∩ F).card
  · rw [if_pos h]
    have h3 : (3 : ℝ) ≤ ((S ∩ F).card : ℝ) := by exact_mod_cast h
    nlinarith [hnn S]
  · rw [if_neg h, mul_zero]
    exact mul_nonneg (hnn S) (Nat.cast_nonneg _)

/-- `P[N ≤ 2] ≥ 0.1648` at mean `≤ 2.5054`, by Markov. -/
theorem weightMass_le_two_ge_of_mean {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) {F : Finset ι} (hmean : expCard w F ≤ 2.5054) :
    (0.1648 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card ≤ 2) := by
  have h := three_mul_weightMass_three_le hnn F
  have hnot := weightMass_not w (fun T => 3 ≤ (T ∩ F).card)
  have hcongr : weightMass w (fun T => ¬ 3 ≤ (T ∩ F).card)
      = weightMass w (fun T => (T ∩ F).card ≤ 2) :=
    weightMass_congr fun T => by omega
  rw [hcongr, htot] at hnot
  linarith

/-- **The three-count at baseline one**: `P[N = 3] ≥ 0.14` at mean in
`[2.4966, 3.0025]`, by the residual shift and the Poisson-type bound at
`k = 2`.  The residual mean may exceed `2` by up to `0.0025`, so the tail
factor of `poi_le_probCount` is bounded below by `rpow_ge_one_sub_mul`. -/
theorem weightMass_eq_three_ge_of_baseline {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hm1 : 2.4966 ≤ expCard w F) (hm2 : expCard w F ≤ 3.0025) :
    (0.14 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card = 3) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hq' : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨(hq i).1.le, (hq i).2⟩
  have h0 : Bernoulli.probCount q 0 = 0 := by
    rw [← hlaw 0]
    refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans
      (weightMass_false w)
    intro S hS
    have := hbase S hS
    constructor
    · intro h; omega
    · intro h; exact h.elim
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero h0
  rw [hlaw 3, probCount_succ_update_zero hj 2]
  have hq0 := update_zero_mem_Icc hq' j
  have hsum0 : ∑ i, Function.update q j 0 i = (∑ i, q i) - 1 := by
    rw [sum_update_zero, hj]
  have hs1 : 1.4966 ≤ ∑ i, Function.update q j 0 i := by
    rw [hsum0, ← hmean]; linarith
  have hs2 : ∑ i, Function.update q j 0 i ≤ 2.0025 := by
    rw [hsum0, ← hmean]; linarith
  obtain ⟨l, hl2, hlp, hbound⟩ := Bernoulli.poi_le_probCount _ hq0 2
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  set p : ℝ := ∑ i, Function.update q j 0 i with hp
  have hp1 : 1.4966 ≤ p := hs1
  have hp2 : p ≤ 2.0025 := hs2
  have ht0 : 0 ≤ max (p - ((2 : ℕ) : ℝ)) 0 := le_max_right _ _
  have ht1 : max (p - ((2 : ℕ) : ℝ)) 0 ≤ 0.0025 :=
    max_le (by push_cast; linarith) (by norm_num)
  interval_cases l
  · -- `l = 0`
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, Nat.cast_ofNat]
    have hb0 : (0 : ℝ) < 1 - p / (2 + 1) := by linarith
    have hb1 : 1 - p / (2 + 1) ≤ 1 := by linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - p / (2 + 1)) ≤ 3.01 := by
      rw [div_le_iff₀ hb0]; linarith
    have hone : 1 ≤ 1 / (1 - p / (2 + 1)) := one_le_one_div hb0 hb1
    have hfac' : (0.9949 : ℝ) ≤ (1 - p / (2 + 1)) ^ max (p - 2) 0 := by
      have : max (p - ((2 : ℕ) : ℝ)) 0 * (1 / (1 - p / (2 + 1)) - 1) ≤ 0.0025 * 2.01 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      push_cast at this hfac
      linarith
    have hpoi : (0.1511 : ℝ) ≤ Bernoulli.poi p 2 := by
      have hexp : 1 / 7.41 ≤ Real.exp (-p) := inv_le_exp_neg hp2 exp_20025_le
      have hpow : (1.4966 : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by norm_num) hp1 2
      have hf : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [Bernoulli.poi, hf, le_div_iff₀ (by norm_num)]
      nlinarith [hexp, hpow, Real.exp_pos (-p)]
    have hpoinn : 0 ≤ Bernoulli.poi p 2 := by
      rw [Bernoulli.poi]; positivity
    calc (0.14 : ℝ) ≤ 0.1511 * 0.9949 := by norm_num
      _ ≤ Bernoulli.poi p 2 * (1 - p / (2 + 1)) ^ max (p - 2) 0 :=
        mul_le_mul hpoi hfac' (by norm_num) hpoinn
  · -- `l = 1`
    simp only [Nat.cast_one]
    have hb0 : (0 : ℝ) < 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ≤ 2.01 := by
      rw [div_le_iff₀ hb0]; norm_num; linarith
    have hone : 1 ≤ 1 / (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) :=
      one_le_one_div hb0 hb1
    have hfac' : (0.9974 : ℝ)
        ≤ (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      have : max (p - ((2 : ℕ) : ℝ)) 0
          * (1 / (1 - (p - 1) / (((2 - 1 : ℕ) : ℝ) + 1)) - 1) ≤ 0.0025 * 1.01 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      linarith
    have hpoi : (0.182 : ℝ) ≤ Bernoulli.poi (p - 1) (2 - 1) := by
      have hexp : 1 / 2.7252 ≤ Real.exp (-(p - 1)) :=
        inv_le_exp_neg (show p - 1 ≤ 1.0025 by linarith) exp_10025_le
      have hf : ((2 - 1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
      have hpw : (p - 1) ^ (2 - 1 : ℕ) = p - 1 := by norm_num
      rw [Bernoulli.poi, hf, hpw, div_one]
      nlinarith [hexp, Real.exp_pos (-(p - 1))]
    have hpoinn : 0 ≤ Bernoulli.poi (p - 1) (2 - 1) := by
      rw [Bernoulli.poi]
      have : (0 : ℝ) ≤ p - 1 := by linarith
      positivity
    calc (0.14 : ℝ) ≤ 0.182 * 0.9974 := by norm_num
      _ ≤ _ := mul_le_mul hpoi hfac' (by norm_num) hpoinn
  · -- `l = 2`
    push_cast at hlp
    simp only [Nat.cast_ofNat, Nat.sub_self]
    have hb0 : (0 : ℝ) < 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) := by
      norm_num; linarith
    have hb1 : 1 - (p - 2) / (((0 : ℕ) : ℝ) + 1) ≤ 1 := by
      norm_num; linarith
    have hfac := rpow_ge_one_sub_mul hb0 hb1 ht0
    have hinv : 1 / (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ≤ 1.01 := by
      rw [div_le_iff₀ hb0]; norm_num; linarith
    have hone : 1 ≤ 1 / (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) :=
      one_le_one_div hb0 hb1
    have hfac' : (0.99 : ℝ)
        ≤ (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) ^ max (p - ((2 : ℕ) : ℝ)) 0 := by
      have : max (p - ((2 : ℕ) : ℝ)) 0
          * (1 / (1 - (p - 2) / (((0 : ℕ) : ℝ) + 1)) - 1) ≤ 0.0025 * 0.01 :=
        mul_le_mul ht1 (by linarith) (by linarith) (by norm_num)
      linarith
    have hpoi : (0.99 : ℝ) ≤ Bernoulli.poi (p - 2) 0 := by
      simp only [Bernoulli.poi, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
        div_one]
      have := Real.add_one_le_exp (-(p - 2))
      linarith
    have hpoinn : 0 ≤ Bernoulli.poi (p - 2) 0 := by
      simp only [Bernoulli.poi, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
        div_one]
      exact (Real.exp_pos _).le
    calc (0.14 : ℝ) ≤ 0.99 * 0.99 := by norm_num
      _ ≤ _ := mul_le_mul hpoi hfac' (by norm_num) hpoinn

end Tails

/-! ### The package -/

section Package

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
-- The nine derived hypotheses are elaborated against large event lambdas,
-- and the final kernel application unifies all of them at once.
/-- **The conditioned tail package.**  From means at `ν`, the one-hot present
bundle, the crossing baseline and the two transferred tails, the nine
hypotheses of `lemma_A1_conditioned_kernel_budget` follow, and hence the
`0.0024ℓε²` bound on the `(1,1,1)` event. -/
theorem lemma_A1_conditioned_budget {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V E : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) (hEsub : E ⊆ A ∪ B)
    (hpres : ∀ T, ν T ≠ 0 → (T ∩ E).card = 1)
    (hbaseF' : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (((A ∪ B) \ E) ∪ V)).card)
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hℓ0 : 0 ≤ ℓ) (hℓcap : ℓ ≤ 100)
    (hA1 : 0.997 ≤ expCard ν A) (hAE2 : expCard ν (A \ E) ≤ 0.5024)
    (hB1 : 0.4977 ≤ expCard ν B) (hB2 : expCard ν B ≤ 1.0026)
    (hV1 : 0.997 ≤ expCard ν V) (hV2 : expCard ν V ≤ 1.502)
    (hX1 : 1.9989 ≤ expCard ν (A ∪ B)) (hX2 : expCard ν (A ∪ B) ≤ 2.502)
    (hBV2 : expCard ν (B ∪ V) ≤ 2.5054)
    (hF'1 : 2.4966 ≤ expCard ν (((A ∪ B) \ E) ∪ V))
    (hF'2 : expCard ν (((A ∪ B) \ E) ∪ V) ≤ 3.0025)
    (hF'le2 : 0.22 * ε ≤ weightMass ν
      (fun T => (T ∩ (((A ∪ B) \ E) ∪ V)).card ≤ 2))
    (hAVle : ℓ * ε ≤ weightMass ν (fun T => (T ∩ (A ∪ V)).card ≤ 2)) :
    0.0024 * ℓ * ε ^ 2 ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
  classical
  have hXV : Disjoint (A ∪ B) V := Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩
  have hEV : Disjoint E V := hXV.mono_left hEsub
  -- the full set is the bundle-free set plus the bundle
  have hFsplit : (A ∪ B) ∪ V = (((A ∪ B) \ E) ∪ V) ∪ E := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have hE' : e ∈ E → e ∈ A ∨ e ∈ B := fun h => Finset.mem_union.mp (hEsub h)
    tauto
  have hdisjF' : Disjoint (((A ∪ B) \ E) ∪ V) E :=
    Finset.disjoint_union_left.mpr ⟨Finset.sdiff_disjoint, hEV.symm⟩
  have hcountF : ∀ T, ν T ≠ 0 →
      (T ∩ ((A ∪ B) ∪ V)).card = (T ∩ (((A ∪ B) \ E) ∪ V)).card + 1 := by
    intro T hT
    rw [hFsplit, card_inter_union_of_disjoint hdisjF' T, hpres T hT]
  -- the kernel's baseline
  have hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card := by
    intro T hT
    have h1 := hpres T hT
    have h2 : (T ∩ E).card ≤ (T ∩ (A ∪ B)).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hEsub)
    omega
  -- `hm3`: the PF₂ bootstrap on the bundle-free set
  have hp3 := weightMass_eq_three_ge_of_baseline hst hr hnn htot hbaseF' hF'1 hF'2
  have hp2 := weightMass_rank_two_ge hst hr hnn htot _ hε0 hεcap hp3 hF'le2
  have hm3 : 0.2 * ε ≤ weightMass ν
      (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) := by
    rw [weightMass_congr_of_support
      (B := fun T => (T ∩ (((A ∪ B) \ E) ∪ V)).card = 2)
      (fun T hT => by rw [hcountF T hT]; omega)]
    exact hp2
  -- the one-cell tails
  have hAge1 := weightMass_one_le_ge_997 hst hr hnn htot hA1
  have hBge1 := weightMass_one_le_ge_4977 hst hr hnn htot hB1
  have hBVle := weightMass_le_two_ge_of_mean hnn htot hBV2
  have hXge := weightMass_two_le_ge_of_baseline_19989 hst hr hnn htot hbase hX1
  have hXle := weightMass_le_two_ge_of_baseline_2502 hnn htot hbase hX2
  have hVge := weightMass_one_le_ge_997 hst hr hnn htot hV1
  have hVle := weightMass_le_one_ge hnn htot hV2
  have hm3nn := weightMass_nonneg hnn (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
  -- `hAge` and `hBge`: Lemma 5.4 in product form
  have hAge : 0.058 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ A).card) := by
    have hA_BV : Disjoint A (B ∪ V) := Finset.disjoint_union_right.mpr ⟨hAB, hAV⟩
    have h := layerProduct_le_of_ge_le hst hr hnn htot hA_BV 1 2
    rw [htot, one_mul, mul_one] at h
    have hc1 : weightMass ν (fun T => (T ∩ (A ∪ (B ∪ V))).card = 1 + 2)
        = weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) :=
      weightMass_congr fun T => by rw [← Finset.union_assoc]
    have hc2 : weightMass ν (fun T => (T ∩ (A ∪ (B ∪ V))).card = 1 + 2
          ∧ 1 ≤ (T ∩ A).card)
        = weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3
          ∧ 1 ≤ (T ∩ A).card) :=
      weightMass_congr fun T => by rw [← Finset.union_assoc]
    rw [hc1, hc2] at h
    have hprod := mul_le_mul hAge1 hBVle (by norm_num) (weightMass_nonneg hnn _)
    calc 0.058 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
        = weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) * 0.058 := mul_comm _ _
      _ ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * (weightMass ν (fun T => 1 ≤ (T ∩ A).card)
            * weightMass ν (fun T => (T ∩ (B ∪ V)).card ≤ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hm3nn
      _ ≤ _ := h
  have hBge : 0.39 * (ℓ * ε) * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ B).card) := by
    have hB_AV : Disjoint B (A ∪ V) :=
      Finset.disjoint_union_right.mpr ⟨hAB.symm, hBV⟩
    have h := layerProduct_le_of_ge_le hst hr hnn htot hB_AV 1 2
    rw [htot, one_mul, mul_one] at h
    have hc1 : weightMass ν (fun T => (T ∩ (B ∪ (A ∪ V))).card = 1 + 2)
        = weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) :=
      weightMass_congr fun T => by
        rw [Finset.union_left_comm, ← Finset.union_assoc]
    have hc2 : weightMass ν (fun T => (T ∩ (B ∪ (A ∪ V))).card = 1 + 2
          ∧ 1 ≤ (T ∩ B).card)
        = weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3
          ∧ 1 ≤ (T ∩ B).card) :=
      weightMass_congr fun T => by
        rw [Finset.union_left_comm, ← Finset.union_assoc]
    rw [hc1, hc2] at h
    have hprod := mul_le_mul hBge1 hAVle (by positivity) (weightMass_nonneg hnn _)
    calc 0.39 * (ℓ * ε) * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
        = weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) * (0.39 * (ℓ * ε)) := by ring
      _ ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * (weightMass ν (fun T => 1 ≤ (T ∩ B).card)
            * weightMass ν (fun T => (T ∩ (A ∪ V)).card ≤ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hm3nn
      _ ≤ _ := h
  -- `P[F ≤ 2] ≤ 0.23`: on the support it is `P[F' = 1]`, bounded by the
  -- residual exponential
  have hle2 : weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card ≤ 2) ≤ 0.23 := by
    have hc : weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card ≤ 2)
        = weightMass ν (fun T => (T ∩ (((A ∪ B) \ E) ∪ V)).card = 1) :=
      weightMass_congr_of_support fun T hT => by
        have := hcountF T hT
        have := hbaseF' T hT
        omega
    rw [hc]
    obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot
      (((A ∪ B) \ E) ∪ V)
    have hmean := expCard_eq_sum_of_rankLaw hlaw
    have h0 : Bernoulli.probCount q 0 = 0 := by
      rw [← hlaw 0]
      refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans
        (weightMass_false ν)
      intro S hS
      have := hbaseF' S hS
      constructor
      · intro h; omega
      · intro h; exact h.elim
    rw [hlaw 1]
    have hexp := probCount_one_le_exp_of_zero
      (fun i => ⟨(hq i).1.le, (hq i).2⟩) h0
    have hmono : Real.exp (-((∑ i, q i) - 1)) ≤ Real.exp (-1.4966) :=
      Real.exp_le_exp.mpr (by rw [← hmean]; linarith)
    have hval : Real.exp (-1.4966) ≤ 0.23 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := exp_14966_ge
      norm_num
      linarith
    linarith
  have htail1 : weightMass ν (fun T => 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card) ≤ 1 := by
    have := weightMass_mono hnn (B := fun _ : Finset ι => True)
      (A := fun T => 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card) (fun _ _ => trivial)
    rw [weightMass_true, htot] at this
    exact this
  -- the antitone layer route to `hAle` and `hBle`
  have hAF : A ⊆ (A ∪ B) ∪ V := fun i hi =>
    Finset.mem_union_left V (Finset.mem_union_left B hi)
  have hBF : B ⊆ (A ∪ B) ∪ V := fun i hi =>
    Finset.mem_union_left V (Finset.mem_union_right A hi)
  have hcross : ∀ (Q : Finset ι → Prop), Antitone Q →
      EventDependsOn Q ((A ∪ B) ∪ V) →
      weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * (weightMass ν Q - 0.23)
        ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ Q T) := by
    intro Q hQanti hQdep
    have hcomp : ∀ jj, 3 ≤ jj →
        weightMass (projLayer ν ((A ∪ B) ∪ V) jj) Q
            * totalMass (projLayer ν ((A ∪ B) ∪ V) 3)
          ≤ weightMass (projLayer ν ((A ∪ B) ∪ V) 3) Q
            * totalMass (projLayer ν ((A ∪ B) ∪ V) jj) :=
      fun jj hjj => layer_le_anti hst hr hnn htot _ hQanti hjj
    have h := crossTail ((A ∪ B) ∪ V) hQdep 3 (fun jj => 3 ≤ jj) hcomp
    have hand := weightMass_and_not ν Q
      (fun T => 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card)
    have hdrop : weightMass ν
        (fun T => Q T ∧ ¬ 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card)
        ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card ≤ 2) :=
      weightMass_mono hnn fun T hT => by omega
    have hjoint : weightMass ν Q - 0.23
        ≤ weightMass ν (fun T => Q T ∧ 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card) := by
      linarith
    have hnn3 := weightMass_nonneg hnn
      (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ Q T)
    calc weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * (weightMass ν Q - 0.23)
        ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * weightMass ν (fun T => Q T ∧ 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card) :=
          mul_le_mul_of_nonneg_left hjoint hm3nn
      _ ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ Q T)
          * weightMass ν (fun T => 3 ≤ (T ∩ ((A ∪ B) ∪ V)).card) := h
      _ ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ Q T) * 1 :=
          mul_le_mul_of_nonneg_left htail1 hnn3
      _ = _ := mul_one _
  have hAle : 0.267 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ A).card ≤ 1) := by
    -- `P[A ≤ 1] ≥ P[(A \ E) = 0] ≥ 1 − E[A \ E]`
    have hzero := le_weightMass_avoid hnn (A \ E)
    rw [htot] at hzero
    have hsub : weightMass ν (fun T => (T ∩ (A \ E)).card = 0)
        ≤ weightMass ν (fun T => (T ∩ A).card ≤ 1) := by
      rw [weightMass_congr_of_support
        (B := fun T => (T ∩ (A \ E)).card = 0 ∧ (T ∩ A).card ≤ 1)
        (fun T hT => by
          constructor
          · intro h
            refine ⟨h, ?_⟩
            have hp := hpres T hT
            have hsplit : (T ∩ A).card
                = (T ∩ (A \ E)).card + (T ∩ (A ∩ E)).card := by
              rw [← card_inter_union_of_disjoint
                (Finset.disjoint_sdiff_inter A E) T, Finset.sdiff_union_inter]
            have hAE : (T ∩ (A ∩ E)).card ≤ (T ∩ E).card :=
              Finset.card_le_card (Finset.inter_subset_inter
                (Finset.Subset.refl T) Finset.inter_subset_right)
            omega
          · exact fun h => h.1)]
      exact weightMass_mono hnn fun T hT => hT.2
    have hQ : 0.2676 ≤ weightMass ν (fun T => (T ∩ A).card ≤ 1) - 0.23 := by
      linarith
    have h := hcross (fun T => (T ∩ A).card ≤ 1) (antitone_card_le A 1)
      ((eventDependsOn_card_le A 1).mono hAF)
    calc 0.267 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
        ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * (weightMass ν (fun T => (T ∩ A).card ≤ 1) - 0.23) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith) hm3nn
      _ ≤ _ := h
  have hBle : 0.267 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ B).card ≤ 1) := by
    have hmark := two_mul_weightMass_le_one_ge hnn B
    rw [htot] at hmark
    have hQ : 0.268 ≤ weightMass ν (fun T => (T ∩ B).card ≤ 1) - 0.23 := by
      linarith
    have h := hcross (fun T => (T ∩ B).card ≤ 1) (antitone_card_le B 1)
      ((eventDependsOn_card_le B 1).mono hBF)
    calc 0.267 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
        ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
          * (weightMass ν (fun T => (T ∩ B).card ≤ 1) - 0.23) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith) hm3nn
      _ ≤ _ := h
  exact lemma_A1_conditioned_kernel_budget hst hr hnn htot hAB hAV hBV hε0 hεcap hℓ0 hℓcap hbase
    hm3 hXge hXle hVge hVle hAge hAle hBge hBle

/-- The legacy fixed-tail package, retained with its previous statement. -/
theorem lemma_A1_conditioned {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V E : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) (hEsub : E ⊆ A ∪ B)
    (hpres : ∀ T, ν T ≠ 0 → (T ∩ E).card = 1)
    (hbaseF' : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (((A ∪ B) \ E) ∪ V)).card)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hA1 : 0.997 ≤ expCard ν A) (hAE2 : expCard ν (A \ E) ≤ 0.5024)
    (hB1 : 0.4977 ≤ expCard ν B) (hB2 : expCard ν B ≤ 1.0026)
    (hV1 : 0.997 ≤ expCard ν V) (hV2 : expCard ν V ≤ 1.502)
    (hX1 : 1.9989 ≤ expCard ν (A ∪ B)) (hX2 : expCard ν (A ∪ B) ≤ 2.502)
    (hBV2 : expCard ν (B ∪ V) ≤ 2.5054)
    (hF'1 : 2.4966 ≤ expCard ν (((A ∪ B) \ E) ∪ V))
    (hF'2 : expCard ν (((A ∪ B) \ E) ∪ V) ≤ 3.0025)
    (hF'le2 : 0.22 * ε ≤ weightMass ν
      (fun T => (T ∩ (((A ∪ B) \ E) ∪ V)).card ≤ 2))
    (hAVle : 7.75 * ε ≤ weightMass ν (fun T => (T ∩ (A ∪ V)).card ≤ 2)) :
    0.01008 * ε ^ 2 ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
  have h := lemma_A1_conditioned_budget hst hr hnn htot hAB hAV hBV hEsub hpres hbaseF'
    hε0 hεcap (ℓ := 7.75) (by norm_num) (by norm_num)
    hA1 hAE2 hB1 hB2 hV1 hV2 hX1 hX2 hBV2 hF'1 hF'2 hF'le2 hAVle
  calc 0.01008 * ε ^ 2 ≤ 0.0024 * 7.75 * ε ^ 2 := by nlinarith [sq_nonneg ε]
    _ ≤ _ := h

end Package

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PoissonTailSharp
import TSPGap.CountEstimates

/-! # The 0.59 upper tail for Lemma 5.22

Every possible shifted Poisson comparison clears the target. There is no
upper bound on the mean and no selection of a preferred existential shift.
-/
namespace TSPGap
open Finset

/-- The needed exponential anchor, keeping more precision than the older tails. -/
theorem exp_199_ge_sharp : (7.315 : ℝ) ≤ Real.exp 1.99 := by
  have h2 : (7.389 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [pow_two, ← Real.exp_add]; norm_num
    rw [he]
    nlinarith [Real.exp_pos 1]
  have he := Real.add_one_le_exp (-0.01)
  have hm := mul_le_mul h2 (show (0.99 : ℝ) ≤ Real.exp (-0.01) by linarith)
    (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  linarith

/-- Both low-count Poisson terms together are at most 0.41 above mean 1.99. -/
theorem poisson_lower_two_le {p : ℝ} (hp : 1.99 ≤ p) :
    Real.exp (-p) * (1 + p) ≤ 0.41 := by
  have h := Real.add_one_le_exp (p - 1.99)
  have hm := mul_le_mul exp_199_ge_sharp h (by linarith) (Real.exp_pos _).le
  rw [← Real.exp_add] at hm
  have hadd : (1.99 : ℝ) + (p - 1.99) = p := by ring
  rw [hadd] at hm
  have hbound : 1 + p ≤ 0.41 * Real.exp p := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-p)).le
  have he : Real.exp (-p) * Real.exp p = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- The one-term shifted Poisson tail also clears 0.59. -/
theorem poisson_lower_one_le {p : ℝ} (hp : 1.99 ≤ p) :
    Real.exp (-(p - 1)) ≤ 0.41 := by
  have he : (2.69 : ℝ) ≤ Real.exp 0.99 := by
    have h := Real.add_one_le_exp (-0.01)
    have hm := mul_le_mul Real.exp_one_gt_d9.le
      (show (0.99 : ℝ) ≤ Real.exp (-0.01) by linarith)
      (by norm_num) (Real.exp_pos _).le
    rw [← Real.exp_add] at hm
    norm_num at hm
    linarith
  have hm : (2.69 : ℝ) ≤ Real.exp (p - 1) :=
    he.trans (Real.exp_le_exp.mpr (by linarith))
  have ht := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-(p - 1))).le
  have hex : Real.exp (-(p - 1)) * Real.exp (p - 1) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At mean at least 1.99, a Bernoulli sum is at least two with probability 0.59. -/
theorem Bernoulli.probGE_two_ge_sharp {q : ι → ℝ}
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hm : 1.99 ≤ ∑ i, q i) :
    (0.59 : ℝ) ≤ probGE q 2 := by
  obtain ⟨l, hl, _, hb⟩ := poi_tail_le_probGE_of_pred_lt q hq 2 (by push_cast; linarith)
  refine le_trans ?_ hb
  interval_cases l
  · norm_num [sum_range_succ, poi]
    have h := poisson_lower_two_le hm
    nlinarith
  · norm_num [sum_range_succ, poi]
    have h := poisson_lower_one_le hm
    rw [neg_sub] at h
    linarith
  · norm_num

/-- Stable-weight adapter, valid on simple edges and on refined pieces. -/
theorem weightMass_two_le_ge_of_mean_199_sharp {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hmean : 1.99 ≤ expCard w F) :
    (0.59 : ℝ) ≤ weightMass w (fun T => 2 ≤ (T ∩ F).card) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean' : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hq' : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨(hq i).1.le, (hq i).2⟩
  have h := Bernoulli.probGE_two_ge_sharp hq' (by rw [← hmean']; exact hmean)
  have hs := Bernoulli.sum_probCount_add_probGE q 2
  norm_num [sum_range_succ] at hs
  rw [← hlaw 0, ← hlaw 1] at hs
  have hor := weightMass_or w (fun T => (T ∩ F).card = 0) (fun T => (T ∩ F).card = 1)
  have hand : weightMass w (fun T => (T ∩ F).card = 0 ∧ (T ∩ F).card = 1) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    exact ⟨fun h => by omega, fun h => h.elim⟩
  have hall : weightMass w (fun T => (T ∩ F).card = 0 ∨ (T ∩ F).card = 1)
      = weightMass w (fun T => (T ∩ F).card ≤ 1) := weightMass_congr fun T => by omega
  have hne : weightMass w (fun T => ¬ (T ∩ F).card ≤ 1) +
      weightMass w (fun T => (T ∩ F).card ≤ 1) = 1 := by
    rw [← htot]
    unfold weightMass totalMass
    rw [← sum_add_distrib]
    refine sum_congr rfl fun T _ => ?_
    by_cases h : (T ∩ F).card ≤ 1 <;> simp [h]
  have hc : weightMass w (fun T => ¬ (T ∩ F).card ≤ 1) =
      weightMass w (fun T => 2 ≤ (T ∩ F).card) := weightMass_congr fun T => by omega
  linarith

end TSPGap

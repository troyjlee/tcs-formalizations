/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1

/-!
# Tail estimates for KKO21 Lemma A.1

These are the two one-cell estimates used by the first application of
Corollary 5.5 in Lemma A.1.  Both counts have an almost-sure baseline of one.

* At mean at least `1.9989`, real stability gives `P[N ≥ 2] ≥ 0.63` by
  deleting the deterministic Bernoulli coordinate forced by the baseline.
* At mean at most `2.502`, Markov's inequality on `N - 1` gives
  `P[N ≤ 2] ≥ 0.249`.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A baseline-one count of mean at least `1.9989` is at least two with
probability at least `0.63` under a stable fixed-rank probability law. -/
theorem weightMass_two_le_ge_of_baseline_19989 {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hmean : 1.9989 ≤ expCard w F) :
    (0.63 : ℝ) ≤ weightMass w (fun T ↦ 2 ≤ (T ∩ F).card) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmeanq : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have h0 : Bernoulli.probCount q 0 = 0 := by
    rw [← hlaw 0]
    refine (weightMass_congr_of_support (B := fun _ ↦ False) ?_).trans
      (weightMass_false w)
    intro S hS
    have hSbase := hbase S hS
    exact ⟨fun hc ↦ by omega, False.elim⟩
  have h1 := probCount_one_le_exp_of_zero
    (fun i ↦ ⟨(hq i).1.le, (hq i).2⟩) h0
  have hsplit : weightMass w (fun T ↦ 2 ≤ (T ∩ F).card)
      = 1 - Bernoulli.probCount q 0 - Bernoulli.probCount q 1 := by
    have hnot := weightMass_not w (fun T ↦ 2 ≤ (T ∩ F).card)
    have hlow : weightMass w (fun T ↦ ¬ 2 ≤ (T ∩ F).card)
        = weightMass w (fun T ↦ (T ∩ F).card = 0)
          + weightMass w (fun T ↦ (T ∩ F).card = 1) := by
      have hor := weightMass_or w (fun T ↦ (T ∩ F).card = 0)
        (fun T ↦ (T ∩ F).card = 1)
      have hand : weightMass w
          (fun T ↦ (T ∩ F).card = 0 ∧ (T ∩ F).card = 1) = 0 := by
        refine (weightMass_congr (B := fun _ ↦ False) fun T ↦ ?_).trans
          (weightMass_false w)
        exact ⟨fun h ↦ by omega, False.elim⟩
      have hcongr : weightMass w (fun T ↦ ¬ 2 ≤ (T ∩ F).card)
          = weightMass w
            (fun T ↦ (T ∩ F).card = 0 ∨ (T ∩ F).card = 1) :=
        weightMass_congr fun T ↦ by omega
      rw [hcongr]
      linarith
    rw [hlow, hlaw 0, hlaw 1] at hnot
    rw [htot] at hnot
    linarith
  have hexp : Real.exp (-((∑ i, q i) - 1)) ≤ 0.37 := by
    have hmono : Real.exp (-((∑ i, q i) - 1)) ≤ Real.exp (-(0.9989 : ℝ)) :=
      Real.exp_le_exp.mpr (by rw [← hmeanq]; linarith)
    have hlow : (2.7152 : ℝ) ≤ Real.exp 0.9989 := by
      have h1' : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h2 : (1 : ℝ) - 0.0011 ≤ Real.exp (-0.0011) := by
        have := Real.add_one_le_exp (-(0.0011 : ℝ))
        linarith
      have hsplit' : Real.exp 0.9989 = Real.exp 1 * Real.exp (-0.0011) := by
        rw [← Real.exp_add]
        norm_num
      have hmul := mul_le_mul h1'.le h2 (by norm_num : (0 : ℝ) ≤ 1 - 0.0011)
        (Real.exp_pos (1 : ℝ)).le
      rw [hsplit']
      nlinarith [hmul]
    have hval : Real.exp (-(0.9989 : ℝ)) ≤ 0.37 := by
      have h : 1 / Real.exp 0.9989 ≤ 1 / 2.7152 :=
        one_div_le_one_div_of_le (by norm_num) hlow
      have hnum : (1 : ℝ) / 2.7152 ≤ 0.37 := by norm_num
      rw [Real.exp_neg, ← one_div]
      linarith
    linarith
  rw [hsplit, h0]
  linarith

/-- A baseline-one count of mean at most `2.502` is at most two with
probability at least `0.249` under any nonnegative probability law. -/
theorem weightMass_le_two_ge_of_baseline_2502 {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hmean : expCard w F ≤ 2.502) :
    (0.249 : ℝ) ≤ weightMass w (fun T ↦ (T ∩ F).card ≤ 2) := by
  have htail := two_mul_weightMass_three_le hnn hbase
  rw [htot] at htail
  have hnot := weightMass_not w (fun T ↦ 3 ≤ (T ∩ F).card)
  have hcongr : weightMass w (fun T ↦ ¬ 3 ≤ (T ∩ F).card)
      = weightMass w (fun T ↦ (T ∩ F).card ≤ 2) :=
    weightMass_congr fun T ↦ by omega
  rw [hcongr, htot] at hnot
  linarith

end TSPGap

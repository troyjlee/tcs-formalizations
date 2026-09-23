/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountDeficit
import TSPGap.Lemma516Tails

/-! # Recovering Lemma 5.22's point mass

Below mean 2.5 the existing Poisson comparison gives a constant bound.
Above it, a constant mass at level three and PF2 turn the mean deficit
into mass at level two, avoiding the old real-power loss.
-/
namespace TSPGap
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The existing, stronger low-mean estimate already suffices for Lemma 5.22. -/
theorem probCount_two_ge_mid_sharp {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 1.99 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 2.5) :
    (0.01 : ℝ) ≤ Bernoulli.probCount q 2 :=
  le_trans (by norm_num) (probCount_two_ge_mid hq (by linarith) h2)

/-! ### The weight-level versions, through the rank law and the residual shift -/

/-- A uniform mass at level three on the high-mean interval. -/
theorem probCount_three_ge_high {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 2.5 ≤ ∑ i, q i) (h2 : ∑ i, q i < 3) :
    (0.1 : ℝ) ≤ Bernoulli.probCount q 3 := by
  obtain ⟨l, hl, hlp, hb⟩ := Bernoulli.poi_le_probCount q hq 3
    (by push_cast; linarith) (by push_cast; linarith)
  have hmax : max ((∑ i, q i) - (3 : ℕ)) 0 = 0 := max_eq_right (by push_cast; linarith)
  rw [hmax, Real.rpow_zero, mul_one] at hb
  have hpoi {y c : ℝ} {j : ℕ} (hy : 0 ≤ y) (hc : c ≤ Real.exp (-y))
      (hnum : (0.1 : ℝ) * j.factorial ≤ c * y ^ j) :
      (0.1 : ℝ) ≤ Bernoulli.poi y j := by
    rw [Bernoulli.poi, le_div_iff₀ (by positivity)]
    exact hnum.trans (mul_le_mul_of_nonneg_right hc (pow_nonneg hy j))
  refine le_trans ?_ hb
  interval_cases l
  · simp only [Nat.sub_zero, Nat.cast_zero, sub_zero]
    apply hpoi (by linarith) (inv_le_exp_neg h2.le exp_three_le)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.5) h1 3
    norm_num [Nat.factorial]
    nlinarith
  · simp only [Nat.cast_one]
    apply hpoi (by linarith) (inv_le_exp_neg (show (∑ i, q i) - 1 ≤ 2 by linarith) exp_two_le)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.5)
      (show 1.5 ≤ (∑ i, q i) - 1 by linarith) 2
    norm_num [Nat.factorial]
    nlinarith
  · simp only [Nat.cast_ofNat]
    apply hpoi (by linarith) (inv_le_exp_neg (show (∑ i, q i) - 2 ≤ 1 by linarith) exp_one_le')
    norm_num [Nat.factorial]
    linarith
  · norm_num at hlp
    linarith

/-- The recovered point mass at level two, including the zero-deficit corner. -/
theorem probCount_two_ge_high_sharp {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 0.0002)
    (h1 : 1.99 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 3 - 1.6 * ε) :
    ε ≤ Bernoulli.probCount q 2 := by
  have hnn : SeqNonneg (Bernoulli.probCount q) := by
    intro k
    rw [Bernoulli.probCount_eq_coeff]
    exact (pf2_bernoulli_prod q univ fun i _ => hq i).1 k
  rcases eq_or_lt_of_le hε0 with he | he
  · rw [← he]; exact hnn 2
  rcases le_or_gt (∑ i, q i) 2.5 with hm | hm
  · exact le_trans (by linarith) (probCount_two_ge_mid_sharp hq h1 hm)
  have h3 := probCount_three_ge_high hq hm.le (by linarith)
  have hpf := Bernoulli.pf2_probCount q hq
  have htotal := sum_range_probCount_eq_one q
    (show Fintype.card ι ≤ Fintype.card ι + 3 by omega)
  have hmean := sum_range_mul_probCount q
    (show Fintype.card ι ≤ Fintype.card ι + 3 by omega)
  have hdef := (deficit_three_bounds hnn (by omega : 4 ≤ Fintype.card ι + 3 + 1) htotal).1
  rw [hmean] at hdef
  have h := point_mass_two_ge_of_pf2_deficit (hnn 1) (hnn 2) h3
    (hpf 0 2 (by omega)) (by simpa [pow_two] using hpf 1 2 (by omega))
    hdef hε h2
  linarith

/-- Lemma 5.22's baseline-one layer mass, with its full coefficient restored. -/
theorem weightMass_eq_three_ge_of_baseline_high_sharp {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 0.0002)
    (hm1 : 2.99 ≤ expCard w F) (hm2 : expCard w F ≤ 4 - 1.6 * ε) :
    ε ≤ weightMass w (fun T => (T ∩ F).card = 3) := by
  obtain ⟨m, q, hq, hsum, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  rw [show (3 : ℕ) = 2 + 1 from rfl, hlaw 2]
  exact probCount_two_ge_high_sharp hq hε0 hε
    (by rw [hsum]; linarith) (by rw [hsum]; linarith)

end TSPGap

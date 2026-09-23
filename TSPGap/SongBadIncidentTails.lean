/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma516Tails
import TSPGap.SongParameters

/-!
# Point-mass and numerical estimates for Song's bad-incident kernel

In the thin-layer branch it is enough to sharpen the existing `0.97α`
point-mass bound to `0.99α` on the smaller mean interval `[1 + α, 1.1]`.
Together with the geometric tails of the sum count and a `0.39` Newton
bound, this exceeds the required `8h`.
-/

namespace TSPGap.Song
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sharp enough point mass on the thin-layer mean interval. -/
theorem probCount_two_ge_thin {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 0.009)
    (h1 : 1 + α ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 1.1) :
    0.99 * α ≤ Bernoulli.probCount q 2 := by
  obtain ⟨l, hl, hlp, hb⟩ := Bernoulli.poi_le_probCount q hq 2
    (by norm_num; linarith) (by norm_num; linarith)
  have he : max ((∑ i, q i) - ((2 : ℕ) : ℝ)) 0 = 0 :=
    max_eq_right (by norm_num; linarith)
  rw [he, Real.rpow_zero, mul_one] at hb
  refine le_trans ?_ hb
  interval_cases l
  · simp only [Nat.cast_zero, sub_zero, Nat.sub_zero]
    have hp : 1 ≤ (∑ i, q i) ^ 2 := by nlinarith
    have hx : 1 / 3.03 ≤ Real.exp (-(∑ i, q i)) := inv_le_exp_neg h2 exp_11_le
    norm_num [Bernoulli.poi, Nat.factorial]
    nlinarith [mul_le_mul hp hx (by norm_num : (0 : ℝ) ≤ 1 / 3.03)
      (sq_nonneg (∑ i, q i))]
  · norm_num [Bernoulli.poi, Nat.factorial]
    rw [← neg_sub]
    by_cases hsmall : (∑ i, q i) - 1 ≤ 0.01
    · have he := Real.add_one_le_exp (-((∑ i, q i) - 1))
      have hp : (0.99 : ℝ) ≤ Real.exp (-((∑ i, q i) - 1)) := by linarith
      nlinarith [mul_le_mul hp (show α ≤ (∑ i, q i) - 1 by linarith)
        hα0.le (Real.exp_pos _).le]
    · have he := Real.add_one_le_exp (-((∑ i, q i) - 1))
      have hp : (0.9 : ℝ) ≤ Real.exp (-((∑ i, q i) - 1)) := by linarith
      have hm := mul_le_mul hp (show (0.01 : ℝ) ≤ (∑ i, q i) - 1 by linarith)
        (by norm_num : (0 : ℝ) ≤ 0.01) (Real.exp_pos _).le
      linarith
  · norm_num at hlp
    linarith

/-- The point-mass bound after removing the one sure success. -/
theorem weightMass_eq_three_ge_thin {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 0.009)
    (h1 : 2 + α ≤ expCard w F) (h2 : expCard w F ≤ 2.1) :
    0.99 * α ≤ weightMass w (fun T => (T ∩ F).card = 3) := by
  obtain ⟨m, q, hq, hs, hl⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  rw [show (3 : ℕ) = 2 + 1 from rfl, hl 2]
  exact probCount_two_ge_thin hq hα0 hα (by rw [hs]; linarith) (by rw [hs]; linarith)

/-- Rational certificate for the nonzero-count tail. -/
theorem exp_neg_half_le : Real.exp (-(1 / 2 : ℝ)) ≤ 0.606531 := by
  have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hid : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]

/-- Exact arithmetic for the thin-layer proof, including its final margin. -/
theorem bad_incident_thin_constants :
    0 < 2 * kGood * h - 5 * d₀ ∧ 2 * kGood * h - 5 * d₀ ≤ 0.009 ∧
    63.02 * h ≤ 0.016651 ∧
    (0.016651 : ℝ) ≤ 0.066604 * 0.25 ∧
    0.016651 * (0.066604 / (1 - 0.066604)) ≤ (0.001189 : ℝ) ∧
    0.016651 * (2 * (1 - 0.066604)⁻¹ + 0.066604 / (1 - 0.066604) ^ 2)
      ≤ (0.036952 : ℝ) ∧
    0.464 ≤ 1 / 2 + kGood * h - 9 / 2 * d₀ - 0.036952 - 0.001189 ∧
    8 * h < 0.39 * (0.99 * (2 * kGood * h - 5 * d₀)) := by
  norm_num [h, kGood, d₀]

end TSPGap.Song

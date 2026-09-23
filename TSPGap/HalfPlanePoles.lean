/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Real poles of a half-plane rational function

The analytic prerequisite for the residue route to homogeneous
productization. A function with nonpositive imaginary part in the upper
half-plane cannot have a real pole of order greater than one, and its
residue at a genuine simple pole is positive.

The local statement needs only continuity of the numerator after the
pole is removed, not a general meromorphic-function API.
-/

namespace TSPGap

open Filter Topology

/-- Approach the pole on a ray and remove the positive real radial factor. -/
theorem im_div_pow_le_at_zero {g : ℂ → ℂ} {n : ℕ}
    (hg : ContinuousAt g 0)
    (hs : ∀ z : ℂ, 0 < z.im → (g z / z ^ n).im ≤ 0)
    {v : ℂ} (hv : 0 < v.im) : (g 0 / v ^ n).im ≤ 0 := by
  have hlim : Tendsto (fun t : ℝ => (g ((t : ℂ) * v) / v ^ n).im)
      (𝓝[>] 0) (𝓝 ((g 0 / v ^ n).im)) := by
    have hray : Tendsto (fun t : ℝ => (t : ℂ) * v) (𝓝[>] 0) (𝓝 0) := by
      have hc := (Complex.continuous_ofReal.mul_const v).tendsto (0 : ℝ)
      have hc0 : Tendsto (fun t : ℝ => (t : ℂ) * v) (𝓝 0) (𝓝 0) := by
        simpa using hc
      exact hc0.mono_left nhdsWithin_le_nhds
    exact (Complex.continuous_im.continuousAt.tendsto.comp
      ((hg.tendsto.comp hray).div_const _))
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have him : 0 < ((t : ℂ) * v).im := by simpa using mul_pos ht0 hv
  have h := hs ((t : ℂ) * v) him
  have heq : g ((t : ℂ) * v) / ((t : ℂ) * v) ^ n =
      (g ((t : ℂ) * v) / v ^ n) / (t ^ n : ℝ) := by
    push_cast
    rw [mul_pow]
    ring
  rw [heq, Complex.div_ofReal_im] at h
  simpa using (div_le_iff₀ (pow_pos ht0 n)).mp h

/-- A direction in the upper half-plane with prescribed power `I`. -/
theorem exists_upper_pow_eq_I {n : ℕ} (hn : 0 < n) :
    ∃ v : ℂ, 0 < v.im ∧ v ^ n = Complex.I := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  let θ : ℝ := Real.pi / (2 * n)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  refine ⟨Complex.exp ((θ : ℂ) * Complex.I), ?_, ?_⟩
  · simpa [Complex.exp_mul_I, ← Complex.ofReal_sin] using
      Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [← Complex.exp_nat_mul]
    have he : (n : ℂ) * ((θ : ℂ) * Complex.I) =
        (Real.pi : ℂ) / 2 * Complex.I := by
      dsimp [θ]
      push_cast
      field_simp [hnC]
    rw [he, Complex.exp_pi_div_two_mul_I]

/-- For order at least two there is also an upper direction with power `-I`. -/
theorem exists_upper_pow_eq_neg_I {n : ℕ} (hn : 2 ≤ n) :
    ∃ v : ℂ, 0 < v.im ∧ v ^ n = -Complex.I := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  let θ : ℝ := 3 * Real.pi / (2 * n)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith [Real.pi_pos]
  refine ⟨Complex.exp ((θ : ℂ) * Complex.I), ?_, ?_⟩
  · simpa [Complex.exp_mul_I, ← Complex.ofReal_sin] using
      Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [← Complex.exp_nat_mul]
    have he : (n : ℂ) * ((θ : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) / 2 * Complex.I := by
      dsimp [θ]
      push_cast
      field_simp [hnC]
      ring
    rw [he, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    ring

/-- The real leading coefficient of any pole is nonnegative. -/
theorem pole_coefficient_nonneg {g : ℂ → ℂ} {n : ℕ} {a : ℝ}
    (hg : ContinuousAt g 0) (ha : g 0 = (a : ℂ)) (hn : 0 < n)
    (hs : ∀ z : ℂ, 0 < z.im → (g z / z ^ n).im ≤ 0) : 0 ≤ a := by
  obtain ⟨v, hv, hpow⟩ := exists_upper_pow_eq_I hn
  have h := im_div_pow_le_at_zero hg hs hv
  simpa [ha, hpow, Complex.div_I] using h

/-- A genuine real pole is simple and has positive residue.
Repeated denominator roots are allowed: `n` is the order left after
cancelling the numerator's vanishing factor. -/
theorem pole_order_eq_one_and_residue_pos {g : ℂ → ℂ} {n : ℕ} {a : ℝ}
    (hg : ContinuousAt g 0) (ha : g 0 = (a : ℂ)) (ha0 : a ≠ 0) (hn : 0 < n)
    (hs : ∀ z : ℂ, 0 < z.im → (g z / z ^ n).im ≤ 0) :
    n = 1 ∧ 0 < a := by
  have ha_pos : 0 < a := lt_of_le_of_ne (pole_coefficient_nonneg hg ha hn hs) ha0.symm
  refine ⟨?_, ha_pos⟩
  by_contra hne
  have hn2 : 2 ≤ n := by omega
  obtain ⟨v, hv, hpow⟩ := exists_upper_pow_eq_neg_I hn2
  have h := im_div_pow_le_at_zero hg hs hv
  have : a ≤ 0 := by simpa [ha, hpow, div_neg, Complex.div_I] using h
  exact (not_le_of_gt ha_pos) this

end TSPGap

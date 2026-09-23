/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Polynomial

/-!
# One-variable coefficient extraction from a capacity bound

For a real-rooted polynomial with nonnegative coefficients, a uniform bound
`c * t ≤ p(t)` on the positive axis implies `exp(-1) * c ≤ p.coeff 1`.
The positive-constant-term case uses the product of the linear root factors
and `1 + t ≤ exp t`. A zero constant term is handled by continuity after
dividing by `X`, with the stronger conclusion `c ≤ p.coeff 1`.

No minimizer of `p(t)/t` is assumed, and neither normalization nor positive
capacity is required. Iterating this estimate on stable count polynomials is
a separate step.
-/

namespace TSPGap

open Polynomial Filter Topology

/-- Nonnegative coefficients give a lower bound by the constant term. -/
theorem constantCoeff_le_eval {p : Polynomial ℝ} (hp : ∀ k, 0 ≤ p.coeff k)
    {x : ℝ} (hx : 0 ≤ x) : p.coeff 0 ≤ p.eval x := by
  rw [eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ =>
    mul_nonneg (hp _) (pow_nonneg hx _))

private theorem prod_one_add_le_exp_sum (s : Multiset ℝ)
    (hs : ∀ a ∈ s, 0 ≤ a) : (s.map (fun a => 1 + a)).prod ≤ Real.exp s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, 0 ≤ b := fun b hb => hs b (by simp [hb])
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Real.exp_add]
      exact mul_le_mul (by simpa [add_comm] using Real.add_one_le_exp a)
        (ih ht) (Multiset.prod_nonneg fun b hb => by
          obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
          linarith [ht c hc]) (Real.exp_pos _).le

/-- A split polynomial with nonnegative coefficients and positive constant
term lies below its exponential tangent on the nonnegative axis. -/
theorem eval_le_exp_tangent {p : Polynomial ℝ} (hsplit : p.Splits)
    (hp : ∀ k, 0 ≤ p.coeff k) (h0 : 0 < p.coeff 0)
    {x : ℝ} (hx : 0 ≤ x) :
    p.eval x ≤ p.coeff 0 * Real.exp (x * (p.coeff 1 / p.coeff 0)) := by
  classical
  have hr : ∀ r ∈ p.roots, r < 0 := by
    intro r hr
    by_contra h
    have he := constantCoeff_le_eval hp (le_of_not_gt h)
    have hz : p.eval r = 0 := (mem_roots'.mp hr).2
    linarith
  have hprod0 : p.leadingCoeff * (p.roots.map fun r => -r).prod = p.coeff 0 := by
    simpa only [zero_sub, ← coeff_zero_eq_eval_zero] using (hsplit.eval_eq_prod_roots 0).symm
  have heval : p.eval x = p.coeff 0 * (p.roots.map fun r => 1 + x / (-r)).prod := by
    rw [hsplit.eval_eq_prod_roots]
    calc
      _ = p.leadingCoeff * (p.roots.map fun r => (-r) * (1 + x / (-r))).prod := by
        congr 2
        apply Multiset.map_congr rfl
        intro r hr'
        have hn : r ≠ 0 := (hr r hr').ne
        field_simp
        ring
      _ = p.coeff 0 * (p.roots.map fun r => 1 + x / (-r)).prod := by
        rw [Multiset.prod_map_mul, ← mul_assoc, hprod0]
  have hsum : (p.roots.map fun r => 1 / (-r)).sum = p.coeff 1 / p.coeff 0 := by
    have he := hsplit.eval_derivative_div_eval_of_ne_zero
      (x := 0) (by simpa only [← coeff_zero_eq_eval_zero] using h0.ne')
    simpa only [zero_sub, ← coeff_zero_eq_eval_zero, coeff_derivative, zero_add,
      Nat.cast_zero, Nat.cast_one, mul_one]
      using he.symm
  have hsumx : (p.roots.map fun r => x / (-r)).sum = x * (p.coeff 1 / p.coeff 0) := by
    rw [← hsum, ← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    ring
  have hb := prod_one_add_le_exp_sum (p.roots.map fun r => x / (-r)) (by
    intro a ha
    obtain ⟨r, hr', rfl⟩ := Multiset.mem_map.mp ha
    exact div_nonneg hx (neg_pos.mpr (hr r hr')).le)
  rw [Multiset.map_map, hsumx] at hb
  rw [heval]
  exact mul_le_mul_of_nonneg_left hb h0.le

/-- If the constant term vanishes, cancel `X` and approach zero from the
right. This includes the zero polynomial and multiple zero roots. -/
theorem coeff_one_ge_of_capacity_of_constant_zero {p : Polynomial ℝ} {c : ℝ}
    (h0 : p.coeff 0 = 0) (hcap : ∀ t : ℝ, 0 < t → c * t ≤ p.eval t) :
    c ≤ p.coeff 1 := by
  have heq : p.divX * X = p := by simpa [h0] using p.divX_mul_X_add
  have hlim : Tendsto (fun t : ℝ => p.divX.eval t) (𝓝[>] 0) (𝓝 (p.coeff 1)) := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_divX, zero_add] using
      (p.divX.continuous.tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have h := hcap t ht0
  rw [← heq, eval_mul, eval_X] at h
  exact (mul_le_mul_iff_left₀ ht0).mp h

/-- **One-variable capacity extraction.** One linear coefficient costs at
most a factor `exp(-1)`. No positivity of either coefficient or capacity is
assumed, and the bound is uniform rather than an attained infimum. -/
theorem coeff_one_ge_exp_neg_one_mul_capacity {p : Polynomial ℝ} {c : ℝ}
    (hsplit : p.Splits) (hp : ∀ k, 0 ≤ p.coeff k)
    (hcap : ∀ t : ℝ, 0 < t → c * t ≤ p.eval t) :
    Real.exp (-1) * c ≤ p.coeff 1 := by
  by_cases hc : c ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hc).trans (hp 1)
  have hcpos : 0 < c := lt_of_not_ge hc
  rcases (hp 0).eq_or_lt with h0 | h0
  · have hb := coeff_one_ge_of_capacity_of_constant_zero h0.symm hcap
    have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    exact (mul_le_of_le_one_left hcpos.le he).trans hb
  rcases (hp 1).eq_or_lt with h1 | h1
  · have ht : 0 < (p.coeff 0 + 1) / c := div_pos (by linarith) hcpos
    have hl := hcap _ ht
    have hu := eval_le_exp_tangent hsplit hp h0 ht.le
    rw [← h1, zero_div, mul_zero, Real.exp_zero, mul_one] at hu
    have heq : c * ((p.coeff 0 + 1) / c) = p.coeff 0 + 1 := by field_simp
    rw [heq] at hl
    linarith
  · have ht : 0 < p.coeff 0 / p.coeff 1 := div_pos h0 h1
    have hl := hcap _ ht
    have hu := eval_le_exp_tangent hsplit hp h0 ht.le
    have heq : p.coeff 0 / p.coeff 1 * (p.coeff 1 / p.coeff 0) = 1 := by
      field_simp
    rw [heq] at hu
    have hb : c ≤ Real.exp 1 * p.coeff 1 := by
      have h := mul_le_mul_of_nonneg_right (hl.trans hu) h1.le
      have heq' : c * (p.coeff 0 / p.coeff 1) * p.coeff 1 = p.coeff 0 * c := by
        field_simp
      rw [heq'] at h
      exact (mul_le_mul_iff_right₀ h0).mp (by nlinarith [h])
    have h := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-1)).le
    simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      using h

end TSPGap

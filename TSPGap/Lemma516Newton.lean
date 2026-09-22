/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankSequence

/-!
# Newton's inequality for a Bernoulli count supported on `{0, 1, 2}`

KKO's Lemma 5.16 (Case 2) conditions on the layer `X + Y = 2` and uses that
`X` is then "the number of successes in two independent Bernoulli trials":
with `P[X ≤ 1] ≥ a` and `P[X ≥ 1] ≥ a`, minimizing `P[X = 1]` gives `0.395`.
What that minimization actually uses is **Newton's inequality**
`p₁² ≥ 4 p₀ p₂` for the count law — strictly stronger than log-concavity
(`p₁² ≥ p₀ p₂`, which only yields `1/3`).

Here: the generating polynomial `∏ (qᵢ X + (1 − qᵢ))` of a Bernoulli count
with `P[X ≥ 3] = 0` is a quadratic `p₀ + p₁ X + p₂ X²`; it has a real root
(the root of any non-constant linear factor), so its discriminant
`p₁² − 4 p₂ p₀` is a square (`bernoulli_newton_two`).
-/

namespace TSPGap
open Finset Polynomial

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Newton's inequality** `4 p₀ p₂ ≤ p₁²` for a Bernoulli count supported
on `{0, 1, 2}`. -/
theorem bernoulli_newton_two (q : κ → ℝ)
    (h3 : ∀ k, 3 ≤ k → Bernoulli.probCount q k = 0) :
    4 * Bernoulli.probCount q 0 * Bernoulli.probCount q 2 ≤ Bernoulli.probCount q 1 ^ 2 := by
  classical
  set g : Polynomial ℝ := ∏ i : κ, (C (q i) * X + C (1 - q i)) with hg
  have hc : ∀ k, g.coeff k = Bernoulli.probCount q k :=
    fun k => (Bernoulli.probCount_eq_coeff q k).symm
  by_cases h2 : Bernoulli.probCount q 2 = 0
  · rw [h2]; nlinarith [sq_nonneg (Bernoulli.probCount q 1)]
  -- the polynomial is a quadratic
  have hdeg : g.natDegree < 3 := by
    rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [hc]
    exact h3 k hk
  -- some factor is non-constant
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hone : g = 1 := by
      rw [hg]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hall i]
      simp
    apply h2
    rw [← hc, hone, Polynomial.coeff_one]
    simp
  -- its root is a root of `g`
  set x₀ : ℝ := -(1 - q i) / q i with hx₀
  have hroot : g.eval x₀ = 0 := by
    rw [hg, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [hx₀]
    field_simp
    ring
  have heval := Polynomial.eval_eq_sum_range' hdeg x₀
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hroot] at heval
  simp only [hc, pow_zero, pow_one, mul_one] at heval
  have hquad : Bernoulli.probCount q 2 * (x₀ * x₀) + Bernoulli.probCount q 1 * x₀
      + Bernoulli.probCount q 0 = 0 := by
    rw [pow_two] at heval
    linarith
  have hd := (quadratic_eq_zero_iff_discrim_eq_sq h2 x₀).mp hquad
  rw [discrim] at hd
  nlinarith [sq_nonneg (2 * Bernoulli.probCount q 2 * x₀ + Bernoulli.probCount q 1)]

end TSPGap

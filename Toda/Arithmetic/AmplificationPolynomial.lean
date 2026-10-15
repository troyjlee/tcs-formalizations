import Toda.Arithmetic.Amplification
import Toda.Arithmetic.IterationBounds
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomials representing the amplification iterates

The integer amplification functions are evaluations of explicit integer
polynomials. Their degrees are exactly `3^k` after `k` rounds. At the
logarithmic round count used for parity counting, the degree is bounded by
`4 * (q + 1)^2`.

This degree bound does not assert a bound on coefficient size, evaluation
runtime, or membership of any function in GapP.
-/

namespace Toda.Arithmetic

open Polynomial

/-- The integer polynomial used for one amplification round. -/
noncomputable def amplifyPolynomial : Polynomial ℤ := 3 * X ^ 2 - 2 * X ^ 3

@[simp] theorem eval_amplifyPolynomial (m : ℤ) :
    amplifyPolynomial.eval m = amplify m := by
  simp [amplifyPolynomial, amplify]

@[simp] theorem natDegree_amplifyPolynomial : amplifyPolynomial.natDegree = 3 := by
  unfold amplifyPolynomial
  compute_degree!

/-- Iterated polynomial composition, with the identity polynomial at round zero. -/
noncomputable def amplifyIteratePolynomial : ℕ → Polynomial ℤ
  | 0 => X
  | k + 1 => amplifyPolynomial.comp (amplifyIteratePolynomial k)

@[simp] theorem amplifyIteratePolynomial_zero : amplifyIteratePolynomial 0 = X := rfl

@[simp] theorem amplifyIteratePolynomial_succ (k : ℕ) :
    amplifyIteratePolynomial (k + 1) =
      amplifyPolynomial.comp (amplifyIteratePolynomial k) := rfl

/-- Evaluation of the iterated polynomial is exactly integer amplification. -/
@[simp] theorem eval_amplifyIteratePolynomial (k : ℕ) (m : ℤ) :
    (amplifyIteratePolynomial k).eval m = amplifyIterate k m := by
  induction k with
  | zero => simp
  | succ k ih => simp [Polynomial.eval_comp, ih]

/-- Each composition multiplies the degree by three. -/
@[simp] theorem natDegree_amplifyIteratePolynomial (k : ℕ) :
    (amplifyIteratePolynomial k).natDegree = 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [Polynomial.natDegree_comp, ih, pow_succ']

/-- The actual amplification polynomial has quadratically bounded degree. -/
theorem natDegree_amplifyIteratePolynomial_amplificationRounds_le (q : ℕ) :
    (amplifyIteratePolynomial (amplificationRounds q)).natDegree ≤ 4 * (q + 1) ^ 2 := by
  rw [natDegree_amplifyIteratePolynomial]
  exact three_pow_amplificationRounds_le q

end Toda.Arithmetic

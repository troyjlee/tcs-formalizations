/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HalfPlaneRational
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# The logarithmic-derivative sign supplied by stability

At an interior point, a coordinate logarithmic derivative has nonpositive
imaginary part. The proof freezes all other coordinates, factors the
resulting complex univariate polynomial, and sums reciprocals of the root
differences. Constant slices and repeated roots are included.

The statement uses the raw zero-free predicate, so the existing
`IsRealStable` definition can supply it directly after complexification.
There is no multiaffinity or derivative-stability assumption.
-/

namespace TSPGap

/-- The univariate logarithmic derivative has the required sign even for
constant polynomials; in that case the roots multiset is empty. -/
theorem polynomial_logDeriv_im_nonpos (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0)
    {z : ℂ} (hz : 0 < z.im) : (p.derivative.eval z / p.eval z).im ≤ 0 := by
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp z hz)]
  change Complex.imAddGroupHom ((p.roots.map fun a => 1 / (z - a)).sum) ≤ 0
  rw [map_multiset_sum, Multiset.map_map]
  apply Multiset.sum_nonneg (α := OrderDual ℝ)
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
  have haim : a.im ≤ 0 := by
    by_contra h
    exact hp a (lt_of_not_ge h) ((Polynomial.mem_roots'.mp ha).2)
  change (1 / (z - a)).im ≤ 0
  rw [one_div, Complex.inv_im, Complex.sub_im]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Complex.normSq_nonneg _)

variable {ι : Type*} [DecidableEq ι]

/-- Freeze all coordinates except one, without identifying polynomial rings. -/
noncomputable def coordinateSlice (p : MvPolynomial ι ℂ) (z : ι → ℂ) (j : ι) :
    Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (Function.update (fun i => Polynomial.C (z i)) j Polynomial.X) p

/-- The slice evaluates at the corresponding updated coordinate vector. -/
theorem eval_coordinateSlice (p : MvPolynomial ι ℂ) (z : ι → ℂ) (j : ι) (t : ℂ) :
    (coordinateSlice p z j).eval t = MvPolynomial.eval (Function.update z j t) p := by
  have hhom : (Polynomial.evalRingHom t).comp
      (MvPolynomial.eval₂Hom Polynomial.C
        (Function.update (fun i => Polynomial.C (z i)) j Polynomial.X)) =
      MvPolynomial.eval (Function.update z j t) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      by_cases hi : i = j <;> simp [Function.update_apply, hi]
  exact DFunLike.congr_fun hhom p

/-- Differentiation commutes with the one-coordinate slice. -/
theorem derivative_coordinateSlice (p : MvPolynomial ι ℂ) (z : ι → ℂ) (j : ι) :
    (coordinateSlice p z j).derivative = coordinateSlice (MvPolynomial.pderiv j p) z j := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [coordinateSlice]
  | add p q hp hq =>
      simpa only [coordinateSlice, map_add, Polynomial.derivative_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      change (MvPolynomial.eval₂ Polynomial.C
        (Function.update (fun i => Polynomial.C (z i)) j Polynomial.X) p).derivative =
        MvPolynomial.eval₂ Polynomial.C
          (Function.update (fun i => Polynomial.C (z i)) j Polynomial.X)
          (MvPolynomial.pderiv j p) at hp
      by_cases hi : i = j
      · subst i
        simp [coordinateSlice, Polynomial.derivative_mul, hp, mul_comm]
      · simp [coordinateSlice, Polynomial.derivative_mul, hi, hp, mul_comm]

omit [DecidableEq ι] in
/-- Stability supplies the sign used by the residue construction, without
requiring the polynomial to be multiaffine. -/
theorem mvPolynomial_logDeriv_im_nonpos (p : MvPolynomial ι ℂ)
    (hp : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.eval z p ≠ 0)
    (z : ι → ℂ) (hz : ∀ i, 0 < (z i).im) (j : ι) :
    (MvPolynomial.eval z (MvPolynomial.pderiv j p) / MvPolynomial.eval z p).im ≤ 0 := by
  classical
  have hs : ∀ t : ℂ, 0 < t.im → (coordinateSlice p z j).eval t ≠ 0 := by
    intro t ht
    rw [eval_coordinateSlice]
    apply hp
    intro i
    by_cases hi : i = j <;> simp [hi, ht, hz]
  have h := polynomial_logDeriv_im_nonpos (coordinateSlice p z j) hs (hz j)
  rwa [derivative_coordinateSlice, eval_coordinateSlice, eval_coordinateSlice,
    Function.update_eq_self] at h

end TSPGap

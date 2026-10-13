/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Restriction
import Mathlib.Tactic.Ring

/-!
# One-coordinate degree reduction

`linearize i p = (1 - X i) * p[i := 0] + X i * p[i := 1]` preserves values
when coordinate `i` is Boolean and has degree at most one in that coordinate.
It does not increase other individual degrees. These operators are idempotent
and commute in distinct coordinates.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

/-- Interpolate between the two Boolean restrictions in coordinate `i`. -/
def linearize (i : σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  (1 - X i) * restrict i 0 p + X i * restrict i 1 p

theorem eval_linearize (x : σ → R) (i : σ) (p : MvPolynomial σ R) :
    eval x (linearize i p) =
      (1 - x i) * eval (Function.update x i 0) p +
        x i * eval (Function.update x i 1) p := by
  simp [linearize, eval_restrict]

/-- Linearization preserves evaluations whose selected coordinate is Boolean. -/
theorem eval_linearize_of_bool (x : σ → R) (i : σ) (p : MvPolynomial σ R)
    (h : x i = 0 ∨ x i = 1) : eval x (linearize i p) = eval x p := by
  rw [eval_linearize]
  rcases h with h | h
  · have hu : Function.update x i 0 = x := by rw [← h]; simp
    simp [h, hu]
  · have hu : Function.update x i 1 = x := by rw [← h]; simp
    simp [h, hu]

/-- Linearization reduces the degree of the selected coordinate to at most one. -/
theorem degreeOf_linearize_self [Nontrivial R] (i : σ) (p : MvPolynomial σ R) :
    (linearize i p).degreeOf i ≤ 1 := by
  unfold linearize
  apply (degreeOf_add_le i _ _).trans
  apply max_le
  · apply (degreeOf_mul_le i _ _).trans
    simpa [degreeOf_restrict_self] using degreeOf_sub_le i (1 : MvPolynomial σ R) (X i)
  · simpa [degreeOf_restrict_self] using
      degreeOf_mul_le i (X i : MvPolynomial σ R) (restrict i 1 p)

/-- Reducing one variable preserves the degree bound in every other variable. -/
theorem degreeOf_linearize_of_ne [Nontrivial R] (i j : σ) (p : MvPolynomial σ R)
    (h : j ≠ i) : (linearize i p).degreeOf j ≤ p.degreeOf j := by
  have hd : (1 - X i : MvPolynomial σ R).degreeOf j = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [degreeOf_X_of_ne h] using degreeOf_sub_le j (1 : MvPolynomial σ R) (X i)
  unfold linearize
  apply (degreeOf_add_le j _ _).trans
  apply max_le
  · apply (degreeOf_mul_le j _ _).trans
    simpa [hd] using degreeOf_restrict_le i j (0 : R) p
  · apply (degreeOf_mul_le j _ _).trans
    simpa [degreeOf_X_of_ne h] using degreeOf_restrict_le i j (1 : R) p

@[simp] theorem restrict_linearize_zero (i : σ) (p : MvPolynomial σ R) :
    restrict i 0 (linearize i p) = restrict i 0 p := by
  simp [linearize]

@[simp] theorem restrict_linearize_one (i : σ) (p : MvPolynomial σ R) :
    restrict i 1 (linearize i p) = restrict i 1 p := by
  simp [linearize]

/-- Once a coordinate has been linearized, repeating it makes no change. -/
@[simp] theorem linearize_idempotent (i : σ) (p : MvPolynomial σ R) :
    linearize i (linearize i p) = linearize i p := by
  conv_lhs => rw [linearize]
  rw [restrict_linearize_zero, restrict_linearize_one]
  rfl

theorem linearize_add (i : σ) (p q : MvPolynomial σ R) :
    linearize i (p + q) = linearize i p + linearize i q := by
  simp only [linearize, map_add]
  ring

/-- Coordinate linearizations commute, so their order is immaterial. -/
theorem linearize_comm (i j : σ) (p : MvPolynomial σ R) :
    linearize i (linearize j p) = linearize j (linearize i p) := by
  by_cases h : i = j
  · subst j
    rfl
  simp only [linearize, map_add, map_mul, map_sub, map_one,
    restrict_X_of_ne i j (0 : R) (Ne.symm h), restrict_X_of_ne i j (1 : R) (Ne.symm h),
    restrict_X_of_ne j i (0 : R) h, restrict_X_of_ne j i (1 : R) h]
  rw [restrict_comm i j 0 0 p h, restrict_comm i j 0 1 p h,
    restrict_comm i j 1 0 p h, restrict_comm i j 1 1 p h]
  ring

/-- Linearization leaves a polynomial unchanged when the variable is absent. -/
theorem linearize_eq_self_of_not_mem_vars (i : σ) (p : MvPolynomial σ R)
    (hi : i ∉ p.vars) : linearize i p = p := by
  rw [linearize, restrict_eq_self_of_not_mem_vars i 0 p hi,
    restrict_eq_self_of_not_mem_vars i 1 p hi]
  ring

/-- The interpolation factors do not introduce new variables after cancellation. -/
theorem vars_linearize_subset [Nontrivial R] (i : σ) (p : MvPolynomial σ R) :
    (linearize i p).vars ⊆ p.vars := by
  intro j hj
  by_contra hnot
  by_cases hji : j = i
  · subst j
    rw [linearize_eq_self_of_not_mem_vars i p hnot] at hj
    exact hnot hj
  · have hz : p.degreeOf j = 0 := by simpa [mem_vars_iff_degreeOf_ne_zero] using hnot
    exact (mem_vars_iff_degreeOf_ne_zero.mp hj)
      (Nat.eq_zero_of_le_zero (by simpa [hz] using degreeOf_linearize_of_ne i j p hji))

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Restriction
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Leaving one coordinate indeterminate

A round message describes the next polynomial with every coordinate fixed
except the one selected by the operator. This univariate slice has degree at
most the original polynomial's individual degree in that coordinate.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

/-- Substitute the assignment `x` in every coordinate except `i`, which becomes
the univariate indeterminate. -/
def univariateSlice (x : σ → R) (i : σ) : MvPolynomial σ R →+* Polynomial R :=
  eval₂Hom Polynomial.C (Function.update (fun j => Polynomial.C (x j)) i Polynomial.X)

@[simp] theorem univariateSlice_C (x : σ → R) (i : σ) (a : R) :
    univariateSlice x i (C a) = Polynomial.C a := by
  simp [univariateSlice]

@[simp] theorem univariateSlice_X_self (x : σ → R) (i : σ) :
    univariateSlice x i (X i) = Polynomial.X := by
  simp [univariateSlice]

@[simp] theorem univariateSlice_X_of_ne (x : σ → R) (i j : σ) (h : j ≠ i) :
    univariateSlice x i (X j) = Polynomial.C (x j) := by
  simp [univariateSlice, h]

/-- Evaluating a slice updates precisely its free coordinate. -/
theorem eval_univariateSlice (x : σ → R) (i : σ) (p : MvPolynomial σ R) (r : R) :
    (univariateSlice x i p).eval r = eval (Function.update x i r) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    by_cases h : j = i
    · subst j
      simp [map_mul, Polynomial.eval_mul, hp]
    · simp [map_mul, Polynomial.eval_mul, hp, univariateSlice_X_of_ne x i j h, h]

/-- A sliced monomial has degree at most its exponent in the selected coordinate. -/
theorem natDegree_univariateSlice_monomial_le [Nontrivial R] (x : σ → R) (i : σ)
    (s : σ →₀ ℕ) (a : R) : (univariateSlice x i (monomial s a)).natDegree ≤ s i := by
  rw [monomial_eq, Finsupp.prod, map_mul, univariateSlice_C, map_prod]
  simp only [map_pow]
  calc
    _ ≤ ∑ j ∈ s.support, (univariateSlice x i (X j) ^ s j).natDegree :=
      (Polynomial.natDegree_C_mul_le a _).trans (Polynomial.natDegree_prod_le _ _)
    _ ≤ ∑ j ∈ s.support, if j = i then s i else 0 := by
      apply Finset.sum_le_sum
      intro j _
      apply Polynomial.natDegree_pow_le.trans
      by_cases h : j = i
      · subst j
        simp
      · simp [univariateSlice_X_of_ne x i j h, h]
    _ ≤ s i := by
      simp only [Finset.sum_ite_eq']
      split <;> simp

/-- Specialization cannot increase the individual degree, even when terms cancel. -/
theorem natDegree_univariateSlice_le [Nontrivial R] (x : σ → R) (i : σ)
    (p : MvPolynomial σ R) : (univariateSlice x i p).natDegree ≤ p.degreeOf i := by
  calc
    _ = (∑ s ∈ p.support, univariateSlice x i (monomial s (p.coeff s))).natDegree := by
      rw [← map_sum, ← p.as_sum]
    _ ≤ p.degreeOf i := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro s hs
      exact (natDegree_univariateSlice_monomial_le x i s (p.coeff s)).trans
        (monomial_le_degreeOf i hs)

end IPPSPACE

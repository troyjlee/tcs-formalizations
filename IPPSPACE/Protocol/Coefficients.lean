/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.Round
import Mathlib.Data.List.OfFn

/-!
# Polynomial messages as coefficient lists

Coefficients are sent in increasing order of exponent. The executable evaluator
uses Horner's rule. A bounded length check rejects an oversized message after
inspecting at most `limit + 1` list constructors, without scanning its entire
tail. Polynomial interpretation and extraction of honest coefficients are used
only in the correctness proof, not by the verifier.
-/

namespace IPPSPACE

/-- Check a length limit and count inspected list constructors, including `nil`.
In particular, rejecting an arbitrarily long list takes bounded work. -/
def lengthCheckWithCost {α : Type*} : ℕ → List α → Bool × ℕ
  | _, [] => (true, 1)
  | 0, _ :: _ => (false, 1)
  | n + 1, _ :: xs =>
      let rest := lengthCheckWithCost n xs
      (rest.1, rest.2 + 1)

theorem lengthCheckWithCost_value {α : Type*} (n : ℕ) (xs : List α) :
    (lengthCheckWithCost n xs).1 = decide (xs.length ≤ n) := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [lengthCheckWithCost]
  | succ n ih => cases xs <;> simp [lengthCheckWithCost, ih]

theorem lengthCheckWithCost_cost_le {α : Type*} (n : ℕ) (xs : List α) :
    (lengthCheckWithCost n xs).2 ≤ n + 1 := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [lengthCheckWithCost]
  | succ n ih =>
    cases xs with
    | nil => simp [lengthCheckWithCost]
    | cons x xs => simpa [lengthCheckWithCost] using Nat.add_le_add_right (ih xs) 1

variable {R : Type*} [CommRing R]

/-- Horner evaluation, with one addition and multiplication per coefficient. -/
def coefficientsEvalWithCost (x : R) : List R → R × ℕ
  | [] => (0, 0)
  | a :: as =>
      let rest := coefficientsEvalWithCost x as
      (a + x * rest.1, rest.2 + 2)

theorem coefficientsEvalWithCost_cost (x : R) (as : List R) :
    (coefficientsEvalWithCost x as).2 = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [coefficientsEvalWithCost, ih, Nat.mul_add]

noncomputable section

/-- The semantic polynomial associated with a coefficient list. -/
def coefficientsPolynomial : List R → Polynomial R
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * coefficientsPolynomial as

theorem coefficientsPolynomial_coeff (as : List R) (i : ℕ) :
    (coefficientsPolynomial as).coeff i = as[i]?.getD 0 := by
  induction as generalizing i with
  | nil => simp [coefficientsPolynomial]
  | cons a as ih =>
    cases i <;> simp [coefficientsPolynomial, Polynomial.coeff_X_mul, ih]

theorem coefficientsEvalWithCost_value (x : R) (as : List R) :
    (coefficientsEvalWithCost x as).1 = (coefficientsPolynomial as).eval x := by
  induction as with
  | nil => simp [coefficientsEvalWithCost, coefficientsPolynomial]
  | cons a as ih => simp [coefficientsEvalWithCost, coefficientsPolynomial, ih]

/-- Bounding message length enforces the degree limit even with trailing zeros. -/
theorem coefficientsPolynomial_natDegree_le (d : ℕ) (as : List R)
    (h : as.length ≤ d + 1) : (coefficientsPolynomial as).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coefficientsPolynomial_coeff, List.getElem?_eq_none (by omega)]
  rfl

/-- Honest replies use exactly `d + 1` coefficients, including trailing zeros. -/
def polynomialCoefficients (d : ℕ) (p : Polynomial R) : List R :=
  List.ofFn (fun i : Fin (d + 1) => p.coeff i)

@[simp] theorem length_polynomialCoefficients (d : ℕ) (p : Polynomial R) :
    (polynomialCoefficients d p).length = d + 1 := by
  simp [polynomialCoefficients]

/-- Every polynomial within the degree limit is represented exactly. -/
theorem coefficientsPolynomial_polynomialCoefficients (d : ℕ) (p : Polynomial R)
    (hp : p.natDegree ≤ d) :
    coefficientsPolynomial (polynomialCoefficients d p) = p := by
  ext i
  rw [coefficientsPolynomial_coeff]
  by_cases hi : i < d + 1
  · simp only [polynomialCoefficients, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (show p.natDegree < i by omega)
    simp only [polynomialCoefficients, List.getElem?_ofFn, dite_eq_right hi, Option.getD_none, hz]

end

end IPPSPACE

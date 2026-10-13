/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.QBF
import IPPSPACE.Arithmetization.Multilinearization

/-!
# QBF arithmetization with degree reduction at every node

Each node combines already multilinear child polynomials and then linearizes
all occurring variables. Its raw polynomial has individual degree at most two,
as does every partial linearization; the final output is multilinear. Boolean
semantics agree with the upstream QBF evaluation, including both quantifiers.

This is a symbolic specification. It does not supply a compact representation,
a polynomial-length verifier schedule, or a polynomial-time evaluation algorithm.
The separate `Schedule` module constructs an operator chain for prenex inputs.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial Complexity

variable {σ R : Type*} [CommRing R]

/-- Taking the Boolean complement does not increase individual degree. -/
theorem degreeOf_one_sub_le (i : σ) (p : MvPolynomial σ R) :
    (1 - p).degreeOf i ≤ p.degreeOf i := by
  simpa using degreeOf_sub_le i (1 : MvPolynomial σ R) p

/-- The arithmetic OR gate has degree at most the sum of its input degrees. -/
theorem degreeOf_or_le (i : σ) (p q : MvPolynomial σ R) :
    (1 - (1 - p) * (1 - q)).degreeOf i ≤ p.degreeOf i + q.degreeOf i :=
  (degreeOf_one_sub_le i _).trans
    ((degreeOf_mul_le i _ _).trans
      (Nat.add_le_add (degreeOf_one_sub_le i p) (degreeOf_one_sub_le i q)))

variable [DecidableEq σ]

/-- Universal quantification doubles individual degree at worst. -/
theorem degreeOf_forall_le [Nontrivial R] (i j : σ) (p : MvPolynomial σ R) :
    (restrict i 0 p * restrict i 1 p).degreeOf j ≤ p.degreeOf j + p.degreeOf j :=
  (degreeOf_mul_le j _ _).trans
    (Nat.add_le_add (degreeOf_restrict_le i j 0 p) (degreeOf_restrict_le i j 1 p))

/-- Existential quantification also doubles individual degree at worst. -/
theorem degreeOf_exists_le [Nontrivial R] (i j : σ) (p : MvPolynomial σ R) :
    (1 - (1 - restrict i 0 p) * (1 - restrict i 1 p)).degreeOf j ≤
      p.degreeOf j + p.degreeOf j :=
  (degreeOf_or_le j _ _).trans
    (Nat.add_le_add (degreeOf_restrict_le i j 0 p) (degreeOf_restrict_le i j 1 p))

/-- Specialization of Boolean-cube preservation to embedded Boolean assignments. -/
theorem eval_multilinearize_bit (x : σ → Bool) (p : MvPolynomial σ R) :
    eval (fun i => bit (R := R) (x i)) (multilinearize p) =
      eval (fun i => bit (x i)) p := by
  apply eval_multilinearize
  intro i
  cases x i <;> simp

/-- Arithmetize a QBF, reducing all individual degrees after each syntax node. -/
def reducedArithmetize : QBF → MvPolynomial ℕ R
  | .var i => multilinearize (X i)
  | .tru => multilinearize 1
  | .fls => multilinearize 0
  | .neg φ => multilinearize (1 - reducedArithmetize φ)
  | .conj φ ψ => multilinearize (reducedArithmetize φ * reducedArithmetize ψ)
  | .disj φ ψ => multilinearize (1 - (1 - reducedArithmetize φ) * (1 - reducedArithmetize ψ))
  | .ex i φ => multilinearize (1 - (1 - restrict i 0 (reducedArithmetize φ)) *
      (1 - restrict i 1 (reducedArithmetize φ)))
  | .all i φ => multilinearize
      (restrict i 0 (reducedArithmetize φ) * restrict i 1 (reducedArithmetize φ))

/-- The raw polynomial at a node, after its children have already been reduced. -/
def reducedStep : QBF → MvPolynomial ℕ R
  | .var i => X i
  | .tru => 1
  | .fls => 0
  | .neg φ => 1 - reducedArithmetize φ
  | .conj φ ψ => reducedArithmetize φ * reducedArithmetize ψ
  | .disj φ ψ => 1 - (1 - reducedArithmetize φ) * (1 - reducedArithmetize ψ)
  | .ex i φ => 1 - (1 - restrict i 0 (reducedArithmetize φ)) *
      (1 - restrict i 1 (reducedArithmetize φ))
  | .all i φ => restrict i 0 (reducedArithmetize φ) * restrict i 1 (reducedArithmetize φ)

theorem reducedArithmetize_eq (φ : QBF) :
    reducedArithmetize (R := R) φ = multilinearize (reducedStep φ) := by
  cases φ <;> rfl

/-- All outputs, including outputs at internal nodes, are multilinear. -/
theorem isMultilinear_reducedArithmetize [Nontrivial R] (φ : QBF) :
    IsMultilinear (reducedArithmetize (R := R) φ) := by
  rw [reducedArithmetize_eq]
  exact isMultilinear_multilinearize _

/-- Every raw arithmetic step has individual degree at most two. -/
theorem degreeOf_reducedStep_le_two [Nontrivial R] (φ : QBF) (j : ℕ) :
    (reducedStep (R := R) φ).degreeOf j ≤ 2 := by
  cases φ with
  | var i => simp [reducedStep, degreeOf_X]; split <;> decide
  | tru => simp [reducedStep]
  | fls => simp [reducedStep]
  | neg φ =>
    exact ((degreeOf_one_sub_le j _).trans
      (isMultilinear_reducedArithmetize φ j)).trans (by decide)
  | conj φ ψ =>
    exact (degreeOf_mul_le j _ _).trans
      (Nat.add_le_add (isMultilinear_reducedArithmetize φ j)
        (isMultilinear_reducedArithmetize ψ j))
  | disj φ ψ =>
    exact (degreeOf_or_le j _ _).trans
      (Nat.add_le_add (isMultilinear_reducedArithmetize φ j)
        (isMultilinear_reducedArithmetize ψ j))
  | ex i φ =>
    exact (degreeOf_exists_le i j _).trans
      (Nat.add_le_add (isMultilinear_reducedArithmetize φ j)
        (isMultilinear_reducedArithmetize φ j))
  | all i φ =>
    exact (degreeOf_forall_le i j _).trans
      (Nat.add_le_add (isMultilinear_reducedArithmetize φ j)
        (isMultilinear_reducedArithmetize φ j))

/-- The degree-two bound holds during reduction, for every partial list. -/
theorem degreeOf_reducedStep_partial_le_two [Nontrivial R] (φ : QBF)
    (is : List ℕ) (j : ℕ) :
    (linearizeMany is (reducedStep (R := R) φ)).degreeOf j ≤ 2 :=
  degreeOf_linearizeMany_le is j _ (by decide) (degreeOf_reducedStep_le_two φ j)

/-- Degree reduction does not change the Boolean truth value of a QBF. -/
theorem eval_reducedArithmetize (φ : QBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i)) (reducedArithmetize φ) = bit (φ.eval x) := by
  induction φ generalizing x with
  | var i => simp [reducedArithmetize, eval_multilinearize_bit]
  | tru => simp [reducedArithmetize, eval_multilinearize_bit]
  | fls => simp [reducedArithmetize, eval_multilinearize_bit]
  | neg φ ih =>
    rw [reducedArithmetize, eval_multilinearize_bit]
    simp [QBF.eval, bit_not, ih]
  | conj φ ψ ihφ ihψ =>
    rw [reducedArithmetize, eval_multilinearize_bit]
    simp [QBF.eval, bit_and, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    rw [reducedArithmetize, eval_multilinearize_bit]
    simp [QBF.eval, bit_or, ihφ, ihψ]
  | ex i φ ih =>
    rw [reducedArithmetize, eval_multilinearize_bit]
    simp only [map_sub, map_one, map_mul, eval_restrict]
    rw [← bit_false (R := R), ← bit_true (R := R), ← bit_update, ← bit_update, ih, ih]
    exact (bit_or _ _).symm
  | all i φ ih =>
    rw [reducedArithmetize, eval_multilinearize_bit]
    simp only [map_mul, eval_restrict]
    rw [← bit_false (R := R), ← bit_true (R := R), ← bit_update, ← bit_update, ih, ih]
    exact (bit_and _ _).symm

/-- On Boolean points the naive and degree-reduced translations agree. -/
theorem eval_reducedArithmetize_eq_eval_arithmetize (φ : QBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i)) (reducedArithmetize φ) =
      eval (fun i => bit (x i)) (arithmetize φ) := by
  rw [eval_reducedArithmetize, eval_arithmetize]

theorem eval_reducedArithmetize_eq_one_iff [Nontrivial R] (φ : QBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i)) (reducedArithmetize φ) = 1 ↔ φ.eval x = true := by
  rw [eval_reducedArithmetize]
  cases φ.eval x <;> simp

end IPPSPACE

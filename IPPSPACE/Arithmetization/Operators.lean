/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Support
import IPPSPACE.QBF.Prenex

/-!
# Lists of algebraic operators

Operators are finite syntactic descriptions; their action on polynomials is a
semantic specification. List heads act outermost, so deleting heads exposes
successive claims as a verifier works toward the matrix polynomial.
-/

namespace IPPSPACE

open MvPolynomial Complexity

/-- The two kinds of steps in the arithmetization of a quantifier prefix. -/
inductive AlgebraicOperator where
  | reduce (index : ℕ)
  | quantify (quantifier : Quantifier)
  deriving DecidableEq

noncomputable section

variable {R : Type*} [CommRing R]

/-- The arithmetic interpretation of a single quantifier. -/
def Quantifier.act : Quantifier → MvPolynomial ℕ R → MvPolynomial ℕ R
  | .ex i, p => 1 - (1 - restrict i 0 p) * (1 - restrict i 1 p)
  | .all i, p => restrict i 0 p * restrict i 1 p

def AlgebraicOperator.act : AlgebraicOperator → MvPolynomial ℕ R → MvPolynomial ℕ R
  | .reduce i, p => linearize i p
  | .quantify q, p => q.act p

/-- Interpret a list of operators as a composition, with the head outermost. -/
def applyOperators : List AlgebraicOperator → MvPolynomial ℕ R → MvPolynomial ℕ R
  | [], p => p
  | op :: ops, p => op.act (applyOperators ops p)

@[simp] theorem applyOperators_nil (p : MvPolynomial ℕ R) : applyOperators [] p = p := rfl

@[simp] theorem applyOperators_cons (op : AlgebraicOperator) (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) : applyOperators (op :: ops) p = op.act (applyOperators ops p) := rfl

theorem applyOperators_append (ops more : List AlgebraicOperator) (p : MvPolynomial ℕ R) :
    applyOperators (ops ++ more) p = applyOperators ops (applyOperators more p) := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp only [List.cons_append, applyOperators_cons, ih]

theorem applyOperators_map_reduce (is : List ℕ) (p : MvPolynomial ℕ R) :
    applyOperators (is.map AlgebraicOperator.reduce) p = linearizeMany is p := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [AlgebraicOperator.act, ih]

theorem vars_quantifier_act_subset [Nontrivial R] (q : Quantifier) (p : MvPolynomial ℕ R) :
    (q.act p).vars ⊆ p.vars := by
  cases q with
  | ex i => exact (vars_exists_subset i p).trans (Finset.erase_subset i p.vars)
  | all i => exact (vars_forall_subset i p).trans (Finset.erase_subset i p.vars)

theorem vars_operator_act_subset [Nontrivial R] (op : AlgebraicOperator)
    (p : MvPolynomial ℕ R) : (op.act p).vars ⊆ p.vars := by
  cases op with
  | reduce i => exact vars_linearize_subset i p
  | quantify q => exact vars_quantifier_act_subset q p

theorem vars_applyOperators_subset [Nontrivial R] (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) : (applyOperators ops p).vars ⊆ p.vars := by
  induction ops with
  | nil => exact Finset.Subset.refl _
  | cons op ops ih => exact (vars_operator_act_subset op _).trans ih

theorem degreeOf_quantifier_act_le_two [Nontrivial R] (q : Quantifier)
    (p : MvPolynomial ℕ R) (hp : IsMultilinear p) (j : ℕ) : (q.act p).degreeOf j ≤ 2 := by
  cases q with
  | ex i => exact (degreeOf_exists_le i j p).trans (Nat.add_le_add (hp j) (hp j))
  | all i => exact (degreeOf_forall_le i j p).trans (Nat.add_le_add (hp j) (hp j))

/-- Quantifier semantics are preserved whenever the input agrees on every Boolean point. -/
theorem eval_quantifier_act (q : Quantifier) (p : MvPolynomial ℕ R) (φ : QBF)
    (hp : ∀ x : ℕ → Bool, eval (fun i => bit (x i)) p = bit (φ.eval x)) (x : ℕ → Bool) :
    eval (fun i => bit (x i)) (q.act p) = bit ((q.bind φ).eval x) := by
  cases q with
  | ex i =>
    simp only [Quantifier.act, map_sub, map_one, map_mul, eval_restrict]
    rw [← bit_false (R := R), ← bit_true (R := R), ← bit_update, ← bit_update, hp, hp]
    exact (bit_or _ _).symm
  | all i =>
    simp only [Quantifier.act, map_mul, eval_restrict]
    rw [← bit_false (R := R), ← bit_true (R := R), ← bit_update, ← bit_update, hp, hp]
    exact (bit_and _ _).symm

/-- Every polynomial in the operator chain, including its starting polynomial,
has individual degree at most `d`. -/
def DegreeBoundedChain : List AlgebraicOperator → MvPolynomial ℕ R → ℕ → Prop
  | [], p, d => ∀ j, p.degreeOf j ≤ d
  | op :: ops, p, d =>
      (∀ j, (op.act (applyOperators ops p)).degreeOf j ≤ d) ∧ DegreeBoundedChain ops p d

theorem DegreeBoundedChain.degreeOf_output {ops : List AlgebraicOperator}
    {p : MvPolynomial ℕ R} {d : ℕ} (h : DegreeBoundedChain ops p d) (j : ℕ) :
    (applyOperators ops p).degreeOf j ≤ d := by
  cases ops with
  | nil => exact h j
  | cons op ops => exact h.1 j

/-- Dropping any number of outer operators selects a polynomial covered by the invariant. -/
theorem DegreeBoundedChain.degreeOf_drop {ops : List AlgebraicOperator}
    {p : MvPolynomial ℕ R} {d : ℕ} (h : DegreeBoundedChain ops p d) (k j : ℕ) :
    (applyOperators (ops.drop k) p).degreeOf j ≤ d := by
  induction ops generalizing k with
  | nil => simpa only [List.drop_nil, applyOperators_nil] using h j
  | cons op ops ih =>
    cases k with
    | zero => exact h.1 j
    | succ k => exact ih h.2 k

theorem degreeBoundedChain_append (ops more : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) (d : ℕ)
    (hops : DegreeBoundedChain ops (applyOperators more p) d)
    (hmore : DegreeBoundedChain more p d) : DegreeBoundedChain (ops ++ more) p d := by
  induction ops with
  | nil => exact hmore
  | cons op ops ih =>
    refine ⟨?_, ih hops.2⟩
    intro j
    change (op.act (applyOperators (ops ++ more) p)).degreeOf j ≤ d
    rw [applyOperators_append]
    exact hops.1 j

/-- A block of degree reductions preserves every uniform bound of at least one,
including at intermediate points within the block. -/
theorem degreeBoundedChain_map_reduce [Nontrivial R] (is : List ℕ)
    (p : MvPolynomial ℕ R) {d : ℕ} (hd : 1 ≤ d) (hp : ∀ j, p.degreeOf j ≤ d) :
    DegreeBoundedChain (is.map AlgebraicOperator.reduce) p d := by
  induction is with
  | nil => exact hp
  | cons i is ih =>
    refine ⟨?_, ih⟩
    intro j
    change (linearize i (applyOperators (is.map AlgebraicOperator.reduce) p)).degreeOf j ≤ d
    rw [applyOperators_map_reduce]
    exact degreeOf_linearizeMany_le (i :: is) j p hd (hp j)

end

end IPPSPACE

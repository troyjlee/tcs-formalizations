/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.SAT.QBF
import IPPSPACE.Arithmetization.Restriction

/-!
# Faithful arithmetization of Complexitylib's quantified Boolean formulas

This first translation is semantic: its degree can grow exponentially.
Linearization and a compact representation are separate obligations before
this can serve as a polynomial-time interactive verifier.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial Complexity

variable {R : Type*} [CommRing R]

/-- Embed the two Boolean values as zero and one. -/
def bit (b : Bool) : R := if b then 1 else 0

@[simp] theorem bit_false : bit (R := R) false = 0 := rfl
@[simp] theorem bit_true : bit (R := R) true = 1 := rfl

theorem bit_not (b : Bool) : bit (R := R) (!b) = 1 - bit b := by
  cases b <;> simp

theorem bit_and (a b : Bool) : bit (R := R) (a && b) = bit a * bit b := by
  cases a <;> cases b <;> simp

theorem bit_or (a b : Bool) :
    bit (R := R) (a || b) = 1 - (1 - bit a) * (1 - bit b) := by
  cases a <;> cases b <;> simp

/-- Boolean embedding commutes with a bound-variable assignment update. -/
theorem bit_update (x : ℕ → Bool) (i : ℕ) (b : Bool) :
    (fun j => bit (R := R) (Function.update x i b j)) =
      Function.update (fun j => bit (x j)) i (bit b) := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- The usual arithmetic interpretation of all eight upstream QBF constructors. -/
def arithmetize : QBF → MvPolynomial ℕ R
  | .var i => X i
  | .tru => 1
  | .fls => 0
  | .neg φ => 1 - arithmetize φ
  | .conj φ ψ => arithmetize φ * arithmetize ψ
  | .disj φ ψ => 1 - (1 - arithmetize φ) * (1 - arithmetize ψ)
  | .ex i φ => 1 - (1 - restrict i 0 (arithmetize φ)) *
      (1 - restrict i 1 (arithmetize φ))
  | .all i φ => restrict i 0 (arithmetize φ) * restrict i 1 (arithmetize φ)

/-- Faithfulness on every Boolean assignment, including under quantifiers. -/
theorem eval_arithmetize (φ : QBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i)) (arithmetize φ) = bit (φ.eval x) := by
  induction φ generalizing x with
  | var i => simp [arithmetize]
  | tru => simp [arithmetize]
  | fls => simp [arithmetize]
  | neg φ ih => simp [arithmetize, QBF.eval, bit_not, ih]
  | conj φ ψ ihφ ihψ => simp [arithmetize, QBF.eval, bit_and, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [arithmetize, QBF.eval, bit_or, ihφ, ihψ]
  | ex i φ ih =>
    simp only [arithmetize, map_sub, map_one, map_mul, eval_restrict]
    rw [← bit_false (R := R), ← bit_true (R := R), ← bit_update, ← bit_update,
      ih, ih]
    exact (bit_or _ _).symm
  | all i φ ih =>
    simp only [arithmetize, map_mul, eval_restrict]
    rw [← bit_false (R := R), ← bit_true (R := R), ← bit_update, ← bit_update,
      ih, ih]
    exact (bit_and _ _).symm

/-- Over a nontrivial ring, evaluation to one detects the Boolean truth value. -/
theorem eval_arithmetize_eq_one_iff [Nontrivial R] (φ : QBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i)) (arithmetize φ) = 1 ↔ φ.eval x = true := by
  rw [eval_arithmetize]
  cases φ.eval x <;> simp

end IPPSPACE

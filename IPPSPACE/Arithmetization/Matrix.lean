/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Schedule

/-!
# Direct arithmetic evaluation of the terminal matrix

The evaluator traverses quantifier-free syntax, rather than expanding a
multivariate polynomial. Its second output counts ring additions/subtractions
and multiplications, treating each as one operation. Variable lookup, field
encoding, allocation, and bit complexity are outside this arithmetic cost model.
-/

namespace IPPSPACE

open MvPolynomial Complexity

variable {R : Type*} [CommRing R]

/-- Evaluate a quantifier-free matrix and count ring operations. The proof
argument rules out quantifiers; both children of a binary gate are evaluated once. -/
def matrixEvalWithCost (x : ℕ → R) : (φ : QBF) → φ.QuantifierFree → R × ℕ
  | .var i, _ => (x i, 0)
  | .tru, _ => (1, 0)
  | .fls, _ => (0, 0)
  | .neg φ, h =>
    let a := matrixEvalWithCost x φ h
    (1 - a.1, a.2 + 1)
  | .conj φ ψ, h =>
    let a := matrixEvalWithCost x φ (QBF.quantifierFree_conj.mp h).1
    let b := matrixEvalWithCost x ψ (QBF.quantifierFree_conj.mp h).2
    (a.1 * b.1, a.2 + b.2 + 1)
  | .disj φ ψ, h =>
    let hs : φ.QuantifierFree ∧ ψ.QuantifierFree := by
      simpa [QBF.QuantifierFree, QBF.quantDepth] using h
    let a := matrixEvalWithCost x φ hs.1
    let b := matrixEvalWithCost x ψ hs.2
    (1 - (1 - a.1) * (1 - b.1), a.2 + b.2 + 4)
  | .ex _ φ, h => False.elim (Nat.succ_ne_zero φ.quantDepth h)
  | .all _ φ, h => False.elim (Nat.succ_ne_zero φ.quantDepth h)

/-- Direct syntax evaluation agrees at arbitrary ring points with polynomial evaluation. -/
theorem matrixEvalWithCost_value (x : ℕ → R) (φ : QBF) (hφ : φ.QuantifierFree) :
    (matrixEvalWithCost x φ hφ).1 = eval x (arithmetize φ) := by
  induction φ with
  | var i => simp [matrixEvalWithCost, arithmetize]
  | tru => simp [matrixEvalWithCost, arithmetize]
  | fls => simp [matrixEvalWithCost, arithmetize]
  | neg φ ih =>
    simp only [matrixEvalWithCost, arithmetize, map_sub, map_one]
    exact congrArg (fun a : R => 1 - a) (ih hφ)
  | conj φ ψ ihφ ihψ => simp [matrixEvalWithCost, arithmetize, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [matrixEvalWithCost, arithmetize, ihφ, ihψ]
  | ex i φ _ => exact False.elim (Nat.succ_ne_zero φ.quantDepth hφ)
  | all i φ _ => exact False.elim (Nat.succ_ne_zero φ.quantDepth hφ)

/-- The evaluator uses at most four ring operations per syntax node. -/
theorem matrixEvalWithCost_cost_le (x : ℕ → R) (φ : QBF) (hφ : φ.QuantifierFree) :
    (matrixEvalWithCost x φ hφ).2 ≤ 4 * nodeCount φ := by
  induction φ with
  | var i => simp [matrixEvalWithCost, nodeCount]
  | tru => simp [matrixEvalWithCost, nodeCount]
  | fls => simp [matrixEvalWithCost, nodeCount]
  | neg φ ih =>
    have ha := ih hφ
    simp only [matrixEvalWithCost, nodeCount]
    omega
  | conj φ ψ ihφ ihψ =>
    have ha := ihφ (QBF.quantifierFree_conj.mp hφ).1
    have hb := ihψ (QBF.quantifierFree_conj.mp hφ).2
    simp only [matrixEvalWithCost, nodeCount]
    omega
  | disj φ ψ ihφ ihψ =>
    have hs : φ.QuantifierFree ∧ ψ.QuantifierFree := by
      simpa [QBF.QuantifierFree, QBF.quantDepth] using hφ
    have ha := ihφ hs.1
    have hb := ihψ hs.2
    simp only [matrixEvalWithCost, nodeCount]
    omega
  | ex i φ _ => exact False.elim (Nat.succ_ne_zero φ.quantDepth hφ)
  | all i φ _ => exact False.elim (Nat.succ_ne_zero φ.quantDepth hφ)

/-- The last claim in a prenex operator chain can be checked directly from its matrix. -/
theorem PrenexQBF.eval_terminal (φ : PrenexQBF) (x : ℕ → R) :
    eval x (applyOperators (φ.schedule.drop φ.schedule.length) (arithmetize φ.matrix)) =
      (matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree).1 := by
  simp only [List.drop_length, applyOperators_nil]
  exact (matrixEvalWithCost_value x φ.matrix φ.matrix_quantifierFree).symm

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.SAT.QBF

/-!
# Syntactic bounds for the upstream QBF representation

The variable list is computed directly from syntax and may contain duplicates.
Its length is bounded by the number of syntax nodes, independently of the
numeric values of variable names. An encoded bit-length bound is a later step.
-/

namespace IPPSPACE

open Complexity

/-- Count syntax nodes, with one node for each constructor. -/
def nodeCount : QBF → ℕ
  | .var _ | .tru | .fls => 1
  | .neg φ | .ex _ φ | .all _ φ => nodeCount φ + 1
  | .conj φ ψ | .disj φ ψ => nodeCount φ + nodeCount ψ + 1

/-- An executable list of free variable occurrences; no polynomial inspection is needed. -/
def freeVarList : QBF → List ℕ
  | .var i => [i]
  | .tru | .fls => []
  | .neg φ => freeVarList φ
  | .conj φ ψ | .disj φ ψ => freeVarList φ ++ freeVarList ψ
  | .ex i φ | .all i φ => (freeVarList φ).filter (fun j => j != i)

@[simp] theorem mem_freeVarList (i : ℕ) (φ : QBF) :
    i ∈ freeVarList φ ↔ i ∈ φ.freeVars := by
  induction φ <;> simp_all [freeVarList, QBF.freeVars]

theorem nodeCount_pos (φ : QBF) : 0 < nodeCount φ := by
  cases φ <;> simp [nodeCount]

/-- The variable list has at most one entry per syntax node. -/
theorem freeVarList_length_le (φ : QBF) : (freeVarList φ).length ≤ nodeCount φ := by
  induction φ with
  | var i => simp [freeVarList, nodeCount]
  | tru => simp [freeVarList, nodeCount]
  | fls => simp [freeVarList, nodeCount]
  | neg φ ih => exact ih.trans (Nat.le_add_right _ _)
  | conj φ ψ ihφ ihψ =>
    simpa [freeVarList, nodeCount] using
      (Nat.add_le_add ihφ ihψ).trans (Nat.le_add_right _ 1)
  | disj φ ψ ihφ ihψ =>
    simpa [freeVarList, nodeCount] using
      (Nat.add_le_add ihφ ihψ).trans (Nat.le_add_right _ 1)
  | ex i φ ih =>
    exact (List.length_filter_le _ _).trans (ih.trans (Nat.le_add_right _ _))
  | all i φ ih =>
    exact (List.length_filter_le _ _).trans (ih.trans (Nat.le_add_right _ _))

end IPPSPACE

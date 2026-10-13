/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ScopedRenamingFP

/-!
# An explicit worklist machine for the exact prenex converter

Visits carry persistent lexical environments; assembly tasks consume completed
subformulas. The counter is global, so a right sibling starts after all names
allocated by its left sibling while retaining its own lexical environment.
This module proves exact completion with at most two steps per source node.
Encoded step runtime and storage bounds are separate obligations.
-/

namespace IPPSPACE

open Complexity

inductive PrenexTask where
  | visit (formula : QBF) (env : List (ℕ × ℕ))
  | neg
  | binary (op : QBFConnective)
  | quantify (q : Quantifier) (fresh : ℕ)

structure PrenexMachineState where
  tasks : List PrenexTask
  values : List ScopedPrenexData
  next : ℕ

/-- Failed assembly is terminal. Canonical executions never use this branch. -/
def PrenexMachineState.fail (state : PrenexMachineState) : PrenexMachineState :=
  ⟨[], [], state.next⟩

/-- One total transition. The value stack holds the right child above the left
child when a binary assembly task is reached. Empty worklists stutter. -/
def prenexMachineStep (state : PrenexMachineState) : PrenexMachineState :=
  match state.tasks with
  | [] => state
  | .visit formula env :: tasks =>
      match formula with
      | .var name =>
          ⟨tasks, ⟨[], .var (scopedNameLookup env name), state.next⟩ :: state.values, state.next⟩
      | .tru => ⟨tasks, ⟨[], .tru, state.next⟩ :: state.values, state.next⟩
      | .fls => ⟨tasks, ⟨[], .fls, state.next⟩ :: state.values, state.next⟩
      | .neg body => ⟨.visit body env :: .neg :: tasks, state.values, state.next⟩
      | .conj left right =>
          ⟨.visit left env :: .visit right env :: .binary .conj :: tasks, state.values, state.next⟩
      | .disj left right =>
          ⟨.visit left env :: .visit right env :: .binary .disj :: tasks, state.values, state.next⟩
      | .ex name body =>
          ⟨.visit body ((name, state.next) :: env) :: .quantify (.ex name) state.next :: tasks,
            state.values, state.next + 1⟩
      | .all name body =>
          ⟨.visit body ((name, state.next) :: env) :: .quantify (.all name) state.next :: tasks,
            state.values, state.next + 1⟩
  | .neg :: tasks =>
      match state.values with
      | value :: values => ⟨tasks, value.neg :: values, state.next⟩
      | [] => state.fail
  | .binary op :: tasks =>
      match state.values with
      | right :: left :: values => ⟨tasks, left.binary op right :: values, state.next⟩
      | _ => state.fail
  | .quantify q fresh :: tasks =>
      match state.values with
      | child :: values => ⟨tasks, child.quantify q fresh :: values, state.next⟩
      | [] => state.fail

def prenexMachineRun (steps : ℕ) (state : PrenexMachineState) : PrenexMachineState :=
  prenexMachineStep^[steps] state

@[simp] theorem prenexMachineRun_zero (state : PrenexMachineState) :
    prenexMachineRun 0 state = state := rfl

theorem prenexMachineRun_succ (steps : ℕ) (state : PrenexMachineState) :
    prenexMachineRun (steps + 1) state = prenexMachineRun steps (prenexMachineStep state) := by
  exact Function.iterate_succ_apply _ _ _

theorem prenexMachineRun_succ_last (steps : ℕ) (state : PrenexMachineState) :
    prenexMachineRun (steps + 1) state = prenexMachineStep (prenexMachineRun steps state) := by
  exact Function.iterate_succ_apply' _ _ _

theorem prenexMachineRun_add (first second : ℕ) (state : PrenexMachineState) :
    prenexMachineRun (first + second) state =
      prenexMachineRun second (prenexMachineRun first state) := by
  change prenexMachineStep^[first + second] state = _
  rw [Nat.add_comm, Function.iterate_add_apply]
  rfl

@[simp] theorem prenexMachineRun_terminal (steps : ℕ) (values : List ScopedPrenexData) (next : ℕ) :
    prenexMachineRun steps ⟨[], values, next⟩ = ⟨[], values, next⟩ := by
  induction steps with
  | zero => rfl
  | succ steps ih => simpa only [prenexMachineRun_succ, prenexMachineStep] using ih

/-- Exact number of visit and assembly transitions. -/
def prenexMachineWork : QBF → ℕ
  | .var _ | .tru | .fls => 1
  | .neg body | .ex _ body | .all _ body => prenexMachineWork body + 2
  | .conj left right | .disj left right => prenexMachineWork left + prenexMachineWork right + 2

theorem prenexMachineWork_le (formula : QBF) : prenexMachineWork formula ≤ 2 * nodeCount formula := by
  induction formula <;> simp_all only [prenexMachineWork, nodeCount] <;> omega

/-- Exact compositional execution: arbitrary outer tasks and values are
preserved, and the completed result carries exactly the global next counter. -/
theorem prenexMachineRun_visit (formula : QBF) (env : List (ℕ × ℕ))
    (tasks : List PrenexTask) (values : List ScopedPrenexData) (start : ℕ) :
    prenexMachineRun (prenexMachineWork formula) ⟨.visit formula env :: tasks, values, start⟩ =
      ⟨tasks, scopedPrenexAux formula env start :: values, (scopedPrenexAux formula env start).next⟩ := by
  induction formula generalizing env tasks values start with
  | var name | tru | fls => rfl
  | neg body ih =>
    rw [prenexMachineWork, prenexMachineRun_succ, prenexMachineRun_succ_last]
    change prenexMachineStep
      (prenexMachineRun (prenexMachineWork body) ⟨.visit body env :: .neg :: tasks, values, start⟩) = _
    rw [ih]
    rfl
  | conj left right ihleft ihright =>
    rw [prenexMachineWork, prenexMachineRun_succ, prenexMachineRun_succ_last]
    change prenexMachineStep
      (prenexMachineRun (prenexMachineWork left + prenexMachineWork right)
        ⟨.visit left env :: .visit right env :: .binary .conj :: tasks, values, start⟩) = _
    rw [prenexMachineRun_add, ihleft, ihright]
    rfl
  | disj left right ihleft ihright =>
    rw [prenexMachineWork, prenexMachineRun_succ, prenexMachineRun_succ_last]
    change prenexMachineStep
      (prenexMachineRun (prenexMachineWork left + prenexMachineWork right)
        ⟨.visit left env :: .visit right env :: .binary .disj :: tasks, values, start⟩) = _
    rw [prenexMachineRun_add, ihleft, ihright]
    rfl
  | ex name body ih =>
    rw [prenexMachineWork, prenexMachineRun_succ, prenexMachineRun_succ_last]
    change prenexMachineStep
      (prenexMachineRun (prenexMachineWork body)
        ⟨.visit body ((name, start) :: env) :: .quantify (.ex name) start :: tasks,
          values, start + 1⟩) = _
    rw [ih]
    rfl
  | all name body ih =>
    rw [prenexMachineWork, prenexMachineRun_succ, prenexMachineRun_succ_last]
    change prenexMachineStep
      (prenexMachineRun (prenexMachineWork body)
        ⟨.visit body ((name, start) :: env) :: .quantify (.all name) start :: tasks,
          values, start + 1⟩) = _
    rw [ih]
    rfl

/-- The machine initialized with the exact existing fresh-name start. -/
def prenexMachineInitial (formula : QBF) : PrenexMachineState :=
  ⟨[.visit formula []], [], qbfMaxVar formula + 1⟩

/-- The fixed linear ruler is sufficient, and completed executions stutter
through any remaining padding steps. -/
theorem prenexMachineRun_initial (formula : QBF) (steps : ℕ)
    (hsteps : prenexMachineWork formula ≤ steps) :
    prenexMachineRun steps (prenexMachineInitial formula) =
      ⟨[], [scopedPrenexAux formula [] (qbfMaxVar formula + 1)],
        (scopedPrenexAux formula [] (qbfMaxVar formula + 1)).next⟩ := by
  have he : steps = prenexMachineWork formula + (steps - prenexMachineWork formula) := by omega
  rw [he, prenexMachineRun_add, prenexMachineInitial, prenexMachineRun_visit,
    prenexMachineRun_terminal]

theorem prenexMachineRun_twice_nodeCount (formula : QBF) :
    prenexMachineRun (2 * nodeCount formula) (prenexMachineInitial formula) =
      ⟨[], [scopedPrenexAux formula [] (qbfMaxVar formula + 1)],
        (scopedPrenexAux formula [] (qbfMaxVar formula + 1)).next⟩ :=
  prenexMachineRun_initial formula _ (prenexMachineWork_le formula)

/-- Write the top completed payload as ordinary QBF syntax. The fallback only
makes this projection total; initialized executions always have one value. -/
def prenexMachineOutput (state : PrenexMachineState) : QBF :=
  match state.values with
  | [] => .fls
  | result :: _ => prefixQBF result.prefix result.matrix

/-- Exact output identity, including capture-safe fresh names and quantifier
dualization. The theorem adds no runtime assumption about the converter. -/
theorem prenexMachineOutput_eq_toPrenex (formula : QBF) :
    prenexMachineOutput (prenexMachineRun (2 * nodeCount formula) (prenexMachineInitial formula)) =
      (toPrenex formula).toQBF := by
  rw [prenexMachineRun_twice_nodeCount]
  have he := scopedPrenexAux_toPrenex formula
  exact congrArg₂ prefixQBF he.1 he.2

end IPPSPACE

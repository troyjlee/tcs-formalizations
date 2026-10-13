/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexMachine
import IPPSPACE.QBF.PrenexAssemblyFP

/-!
# Binary encoding of the prenex worklist machine

Task and value stacks use upstream pairs with the tail stored once. All names
and fresh-name counters retain their canonical binary representations.
-/

namespace IPPSPACE

open Complexity

/-- Fixed tags separate visits, negation, binary assembly, and binder assembly. -/
def encodePrenexTask : PrenexTask → List Bool
  | .visit formula env => [false, false, false] ++ pair (encodeQBF formula) (encodeNameEnvironment env)
  | .neg => [false, false, true]
  | .binary .conj => [false, true, false]
  | .binary .disj => [false, true, true]
  | .quantify q fresh => [true, false, false] ++ pair q.token.encode fresh.bits

def encodePrenexTasks : List PrenexTask → List Bool
  | [] => []
  | task :: tasks => pair (encodePrenexTask task) (encodePrenexTasks tasks)

def encodePrenexValues : List ScopedPrenexData → List Bool
  | [] => []
  | value :: values => pair (encodeScopedPrenexData value) (encodePrenexValues values)

def encodePrenexMachineState (state : PrenexMachineState) : List Bool :=
  pair state.next.bits (pair (encodePrenexTasks state.tasks) (encodePrenexValues state.values))

@[simp] theorem encodePrenexTasks_nil : encodePrenexTasks [] = [] := rfl
@[simp] theorem encodePrenexValues_nil : encodePrenexValues [] = [] := rfl

@[simp] theorem length_encodePrenexTask_visit (formula : QBF) (env : List (ℕ × ℕ)) :
    (encodePrenexTask (.visit formula env)).length =
      2 * (encodeQBF formula).length + (encodeNameEnvironment env).length + 5 := by
  simp [encodePrenexTask]
  omega

@[simp] theorem length_encodePrenexTask_neg : (encodePrenexTask .neg).length = 3 := rfl

@[simp] theorem length_encodePrenexTask_binary (op : QBFConnective) :
    (encodePrenexTask (.binary op)).length = 3 := by cases op <;> rfl

@[simp] theorem length_encodePrenexTask_quantify (q : Quantifier) (fresh : ℕ) :
    (encodePrenexTask (.quantify q fresh)).length =
      2 * q.token.encode.length + fresh.bits.length + 5 := by
  simp [encodePrenexTask]
  omega

@[simp] theorem length_encodePrenexTasks_cons (task : PrenexTask) (tasks : List PrenexTask) :
    (encodePrenexTasks (task :: tasks)).length =
      2 * (encodePrenexTask task).length + 2 + (encodePrenexTasks tasks).length := by
  simp [encodePrenexTasks]

@[simp] theorem length_encodePrenexValues_cons (value : ScopedPrenexData) (values : List ScopedPrenexData) :
    (encodePrenexValues (value :: values)).length =
      2 * (encodeScopedPrenexData value).length + 2 + (encodePrenexValues values).length := by
  simp [encodePrenexValues]

@[simp] theorem length_encodePrenexMachineState (state : PrenexMachineState) :
    (encodePrenexMachineState state).length = 2 * state.next.bits.length +
      2 * (encodePrenexTasks state.tasks).length + (encodePrenexValues state.values).length + 4 := by
  simp [encodePrenexMachineState]
  omega

/-- Raw projections have the exact canonical values on every encoded state. -/
def prenexStateNextBits (bits : List Bool) : List Bool := pairFst bits
def prenexStateTasks (bits : List Bool) : List Bool := pairFst (pairSnd bits)
def prenexStateValues (bits : List Bool) : List Bool := pairSnd (pairSnd bits)

@[simp] theorem prenexStateNextBits_encode (state : PrenexMachineState) :
    prenexStateNextBits (encodePrenexMachineState state) = state.next.bits := by
  simp [prenexStateNextBits, encodePrenexMachineState]

@[simp] theorem prenexStateTasks_encode (state : PrenexMachineState) :
    prenexStateTasks (encodePrenexMachineState state) = encodePrenexTasks state.tasks := by
  simp [prenexStateTasks, encodePrenexMachineState]

@[simp] theorem prenexStateValues_encode (state : PrenexMachineState) :
    prenexStateValues (encodePrenexMachineState state) = encodePrenexValues state.values := by
  simp [prenexStateValues, encodePrenexMachineState]

def packPrenexMachineState (next tasks values : List Bool) : List Bool :=
  pair next (pair tasks values)

@[simp] theorem packPrenexMachineState_encode (next : ℕ)
    (tasks : List PrenexTask) (values : List ScopedPrenexData) :
    packPrenexMachineState next.bits (encodePrenexTasks tasks) (encodePrenexValues values) =
      encodePrenexMachineState ⟨tasks, values, next⟩ := rfl

end IPPSPACE

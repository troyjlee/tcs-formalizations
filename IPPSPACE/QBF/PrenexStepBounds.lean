/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexPayloadBounds
import IPPSPACE.QBF.PrenexMachineBounds

/-!
# One-step encoded storage growth for the prenex machine

No invariant on the value stack is needed: assembly consumes the child
payloads it combines, and each stack tail is encoded once. Source syntax,
lexical environments, and binary counter widths control all new storage.
-/

namespace IPPSPACE

open Complexity

theorem prenexMachineStep_length_le {state : PrenexMachineState} {L E B : ℕ}
    (h : state.ControlBound L E B) :
    (encodePrenexMachineState (prenexMachineStep state)).length ≤
      (encodePrenexMachineState state).length + 128 * (L + E + B + 1) := by
  rcases state with ⟨tasks, values, next⟩
  cases tasks with
  | nil => simp [prenexMachineStep]
  | cons task tasks =>
    have hn : next.bits.length ≤ B := h.1
    have hh := h.2 task (by simp)
    cases task with
    | visit formula env =>
      change (encodeQBF formula).length ≤ L ∧ (encodeNameEnvironment env).length ≤ E at hh
      cases formula with
      | var name =>
        have hl := scopedNameLookup_bits_length_le env name
        simp only [encodeQBF, encodeNatName, length_frameNameBits, List.length_append,
          List.length_cons, List.length_nil] at hh
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_visit,
          length_encodePrenexValues_cons, length_encodeScopedPrenexData_var,
          encodeQBF, encodeNatName, length_frameNameBits, List.length_append,
          List.length_cons, List.length_nil]
        omega
      | tru | fls =>
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_visit,
          length_encodePrenexValues_cons, length_encodeScopedPrenexData_tru,
          length_encodeScopedPrenexData_fls, encodeQBF,
          List.length_cons, List.length_nil]
        omega
      | neg body =>
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_visit,
          length_encodePrenexTask_neg, encodeQBF,
          List.length_append, List.length_cons, List.length_nil]
        omega
      | conj left right | disj left right =>
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_visit,
          length_encodePrenexTask_binary, encodeQBF,
          List.length_append, List.length_cons, List.length_nil]
        omega
      | ex name body | all name body =>
        have hs := successor_bits_length_le next
        simp only [encodeQBF, encodeNatName, length_frameNameBits, List.length_append,
          List.length_cons, List.length_nil] at hh
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_visit,
          length_encodePrenexTask_quantify, encodeNameEnvironment_cons_length,
          Quantifier.token, SyntaxToken.encode, encodeQBF, encodeNatName,
          length_frameNameBits, List.length_append, List.length_cons, List.length_nil]
        omega
    | neg =>
      cases values with
      | nil =>
        simp only [prenexMachineStep, PrenexMachineState.fail, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_neg,
          encodePrenexTasks_nil, encodePrenexValues_nil, List.length_nil]
        omega
      | cons value values =>
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_neg,
          length_encodePrenexValues_cons, length_encodeScopedPrenexData_neg]
        omega
    | binary op =>
      cases values with
      | nil =>
        simp only [prenexMachineStep, PrenexMachineState.fail, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_binary,
          encodePrenexTasks_nil, encodePrenexValues_nil, List.length_nil]
        omega
      | cons right values =>
        cases values with
        | nil =>
          simp only [prenexMachineStep, PrenexMachineState.fail, length_encodePrenexMachineState,
            length_encodePrenexTasks_cons, length_encodePrenexTask_binary,
            length_encodePrenexValues_cons, encodePrenexTasks_nil, encodePrenexValues_nil,
            List.length_nil]
          omega
        | cons left values =>
          have hb := length_encodeScopedPrenexData_binary_le op left right
          simp only [prenexMachineStep, length_encodePrenexMachineState,
            length_encodePrenexTasks_cons, length_encodePrenexTask_binary,
            length_encodePrenexValues_cons]
          omega
    | quantify q fresh =>
      change q.token.encode.length ≤ L ∧ fresh.bits.length ≤ B at hh
      cases values with
      | nil =>
        simp only [prenexMachineStep, PrenexMachineState.fail, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_quantify,
          encodePrenexTasks_nil, encodePrenexValues_nil, List.length_nil]
        omega
      | cons child values =>
        simp only [prenexMachineStep, length_encodePrenexMachineState,
          length_encodePrenexTasks_cons, length_encodePrenexTask_quantify,
          length_encodePrenexValues_cons, length_encodeScopedPrenexData_quantify]
        omega

end IPPSPACE

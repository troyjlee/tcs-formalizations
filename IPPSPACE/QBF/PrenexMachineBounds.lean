/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexPayloadBounds

/-!
# Polynomial storage for prenex conversion

The bounds count binary digits, including those of source names and fresh
counters. Stack tails are stored once; assembly consumes its child payloads.
-/

namespace IPPSPACE

open Complexity

def PrenexTask.ControlBound (L E B : ℕ) : PrenexTask → Prop
  | .visit formula env => (encodeQBF formula).length ≤ L ∧ (encodeNameEnvironment env).length ≤ E
  | .quantify q fresh => q.token.encode.length ≤ L ∧ fresh.bits.length ≤ B
  | _ => True

def PrenexMachineState.ControlBound (L E B : ℕ) (state : PrenexMachineState) : Prop :=
  state.next.bits.length ≤ B ∧ ∀ task ∈ state.tasks, task.ControlBound L E B

theorem PrenexTask.ControlBound.mono {task : PrenexTask} {L E B E' B' : ℕ}
    (h : task.ControlBound L E B) (he : E ≤ E') (hb : B ≤ B') :
    task.ControlBound L E' B' := by
  cases task <;> simp only [PrenexTask.ControlBound] at *
  all_goals first | trivial | exact ⟨h.1, h.2.trans he⟩ | exact ⟨h.1, h.2.trans hb⟩

theorem PrenexMachineState.ControlBound.mono {state : PrenexMachineState} {L E B E' B' : ℕ}
    (h : state.ControlBound L E B) (he : E ≤ E') (hb : B ≤ B') :
    state.ControlBound L E' B' :=
  ⟨h.1.trans hb, fun task ht => (h.2 task ht).mono he hb⟩

theorem prenexMachineStep_controlBound {state : PrenexMachineState} {L E B : ℕ}
    (h : state.ControlBound L E B) :
    (prenexMachineStep state).ControlBound L (E + 4 * L + 2 * B + 6) (B + 2) := by
  rcases state with ⟨tasks, values, next⟩
  cases tasks with
  | nil => exact h.mono (by omega) (by omega)
  | cons task tasks =>
    have hn : next.bits.length ≤ B := h.1
    have hh := h.2 task (by simp)
    have ht : ∀ task ∈ tasks, task.ControlBound L (E + 4 * L + 2 * B + 6) (B + 2) :=
      fun task hm => (h.2 task (by simp [hm])).mono (by omega) (by omega)
    have hs := successor_bits_length_le next
    cases task with
    | visit formula env =>
      cases formula <;>
        simp only [PrenexTask.ControlBound, encodeQBF, List.length_append,
          List.length_cons, List.length_nil, encodeNatName, length_frameNameBits] at hh <;>
        simp only [prenexMachineStep, PrenexMachineState.ControlBound, List.mem_cons,
          forall_eq_or_imp, PrenexTask.ControlBound, encodeNameEnvironment_cons_length,
          Quantifier.token, SyntaxToken.encode, encodeNatName, length_frameNameBits,
          List.length_append, List.length_cons, List.length_nil] <;>
        (refine ⟨by omega, ?_⟩; repeat' (first | exact ht | omega | constructor))
    | neg =>
      cases values <;>
        simp only [prenexMachineStep, PrenexMachineState.fail, PrenexMachineState.ControlBound,
          List.not_mem_nil, false_implies, implies_true, and_true] <;>
        first | exact ⟨by omega, ht⟩ | omega
    | binary op =>
      cases values with
      | nil => simpa [prenexMachineStep, PrenexMachineState.fail, PrenexMachineState.ControlBound] using (show next.bits.length ≤ B + 2 by omega)
      | cons right values =>
        cases values <;>
          simp only [prenexMachineStep, PrenexMachineState.fail, PrenexMachineState.ControlBound,
            List.not_mem_nil, false_implies, implies_true, and_true] <;>
          first | exact ⟨by omega, ht⟩ | omega
    | quantify q fresh =>
      cases values <;>
        simp only [prenexMachineStep, PrenexMachineState.fail, PrenexMachineState.ControlBound,
          List.not_mem_nil, false_implies, implies_true, and_true] <;>
        first | exact ⟨by omega, ht⟩ | omega

end IPPSPACE

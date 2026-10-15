import Toda.Oracle.FunctionModel.Frame
import Toda.Oracle.Batch.Defs

/-! # Streaming full binary oracle queries and encoded full answers -/

namespace Toda.Oracle.FunctionBatch

open Complexity
open Batch (QueryPrefix query_idle output_write_blank binary)

inductive Phase where
  | boot | tag | data | query | answerBoot | answerTag | answerData | rewind | halt
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.boot, .tag, .data, .query, .answerBoot, .answerTag, .answerData, .rewind, .halt}
  complete := by intro q; cases q <;> simp

/-- The answer tape is disposable outside the answer-copying states. -/
def discardStep (t : Tape) : Tape := t.writeAndMove Γ.blank .right

def transition (q : Phase) (inp query answer out : Γ) : FunctionLocalTransition 0 Phase where
  nextState := match q with
    | .boot => .tag
    | .tag => if inp = .one then .data else if inp = .zero then .query else .halt
    | .data => if binary inp then .tag else .halt
    | .query => .query
    | .answerBoot => .answerTag
    | .answerTag => if binary answer then .answerData else .rewind
    | .answerData => .answerTag
    | .rewind => if query = .start then .tag else .rewind
    | .halt => .halt
  queryWrite := if q = .data then TM.readBackWrite inp else TM.readBackWrite query
  answerWrite := if q = .answerTag ∨ q = .answerData then TM.readBackWrite answer else .blank
  workWrites := fun _ => .blank
  outputWrite := if q = .answerTag then (if binary answer then .one else .zero)
    else if q = .answerData then TM.readBackWrite answer else .blank
  inputDir := if q = .boot ∨ ((q = .tag ∨ q = .data) ∧ binary inp) then .right
    else TM.idleDir inp
  queryDir := if q = .boot ∨ (q = .data ∧ binary inp) then .right else
    if q = .rewind then (if query = .start then .right else .left) else TM.idleDir query
  answerDir := if q = .answerTag then TM.idleDir answer else .right
  workDirs := fun _ => .right
  outputDir := if q = .answerTag ∨ q = .answerData then .right else TM.idleDir out

/-- This constant-state machine takes an encoded list of queries and emits
an encoded list of their complete canonical binary answers. -/
def machine : FunctionTM 0 where
  Q := Phase
  qstart := .boot
  qhalt := .halt
  queryTransition := fun q => if q = .query then some .answerBoot else none
  localTransition := fun q inp query answer _ out => transition q inp query answer out
  localTransition_right_of_start := by
    intro q inp query answer work out
    refine ⟨?_, ?_, ?_, fun _ _ => rfl, ?_⟩
    · intro h; subst inp; cases q <;> simp [transition, binary, TM.idleDir]
    · intro h; subst query; cases q <;> simp [transition, binary, TM.idleDir]
    · intro h; subst answer; cases q <;> simp [transition, TM.idleDir]
    · intro h; subst out; cases q <;> simp [transition, TM.idleDir]

/-- Exact runtime from the tag-reading state. Each returned answer bit takes
two ordinary output writes, in addition to the oracle transition itself. -/
def costFrom (oracle : FunctionOracle) (pending : List Bool) : List Bool → ℕ
  | [] => 1
  | false :: rest => pending.length + 2 * (oracle pending).bits.length + 6 +
      costFrom oracle [] rest
  | true :: [] => 2
  | true :: bit :: rest => 2 + costFrom oracle (pending ++ [bit]) rest

/-- The exact encoded output of the total input-stream decoder. -/
def answers (oracle : FunctionOracle) (stream : List Bool) : List Bool :=
  Batch.encode ((Batch.decode stream).map fun query => (oracle query).bits)

end Toda.Oracle.FunctionBatch

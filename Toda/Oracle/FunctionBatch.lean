import Toda.Oracle.FunctionBatch.Run
import Toda.Oracle.FunctionBatch.Bounds

/-!
# A full-answer counting-oracle batch machine

The machine accepts the ordinary binary encoding `Batch.encode queries`. It
constructs and delimits each query with local tape operations, receives the
complete canonical binary answer on its dedicated answer tape, and writes
`Batch.encode` of all answers to its ordinary output. Old query data beyond
the current head is ignored; every rewind and every answer write is charged.
The decoder is total, including incomplete trailing input fragments.
-/

namespace Toda.Oracle.FunctionBatch

open Complexity

/-- Exact ordinary-input execution, including initialization of all heads. -/
theorem run (oracle : FunctionOracle) (stream : List Bool) :
    ∃ final, machine.reachesIn oracle (costFrom oracle [] stream + 1)
        (machine.initCfg stream) final ∧ machine.halted final ∧
      final.output.HasBinaryPrefix (answers oracle stream) := by
  let next : FunctionCfg 0 machine.Q :=
    { state := .tag
      input := (Tape.init (stream.map Γ.ofBool)).move .right
      query := (Tape.init []).move .right
      answer := (Tape.init []).move .right
      work := fun _ => (Tape.init []).move .right
      output := (Tape.init []).move .right }
  have hstep : machine.step oracle (machine.initCfg stream) = some next := by
    simp [FunctionTM.step, machine, transition, next, Tape.read, Tape.init,
      TM.readBackWrite, TM.idleDir, Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨final, hrun, hhalt, hout⟩ :=
    runsFrom oracle stream [] [] next rfl (Tape.init_move_right_hasBinarySuffix stream)
      ⟨rfl, by simp⟩ (Tape.StartInvariant.init_nil.move .right)
      Tape.init_nil_move_right_hasBinaryPrefix_nil
  exact ⟨final, .step hstep hrun, hhalt, by simpa [answers, Batch.decode] using hout⟩

/-- All complete binary answers are returned in the original query order. -/
theorem run_encoded (oracle : FunctionOracle) (queries : List (List Bool)) :
    ∃ final, machine.reachesIn oracle (costFrom oracle [] (Batch.encode queries) + 1)
        (machine.initCfg (Batch.encode queries)) final ∧ machine.halted final ∧
      final.output.HasBinaryPrefix (Batch.encode (queries.map fun query => (oracle query).bits)) := by
  simpa [answers] using run oracle (Batch.encode queries)

end Toda.Oracle.FunctionBatch

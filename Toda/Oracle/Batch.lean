import Toda.Oracle.Batch.Run

/-!
# A costed nonadaptive batch-query oracle machine

Each query bit is prefixed by true; false terminates a query. The machine
streams this ordinary binary input, appends each oracle answer to its output,
and rewinds its dedicated query tape between requests. It overwrites old
query cells without assuming a free erase. Cells beyond the query head are
outside the oracle query and therefore need no cleanup.

Every input, including malformed trailing fragments, halts in at most
`5 * input.length + 2` steps. On encoded query lists the output is exactly the
list of answers, in order.
-/

namespace Toda.Oracle.Batch

open Complexity

/-- Exact ordinary-input execution of the total stream decoder. -/
theorem run (oracle : BooleanOracle) (stream : List Bool) :
    ∃ final, machine.reachesIn oracle (costFrom [] stream + 1)
        (machine.initCfg stream) final ∧ machine.halted final ∧
      final.output.HasBinaryPrefix ((decode stream).map oracle) := by
  let next : OracleCfg 0 machine.Q :=
    { state := .tag
      input := (Tape.init (stream.map Γ.ofBool)).move .right
      query := (Tape.init []).move .right
      work := fun _ => (Tape.init []).move .right
      output := (Tape.init []).move .right }
  have hstep : machine.step oracle (machine.initCfg stream) = some next := by
    simp [OracleTM.step, machine, transition, next, Tape.read, Tape.init,
      TM.readBackWrite, TM.idleDir, Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨final, hrun, hhalt, hout⟩ :=
    runsFrom oracle stream [] [] next rfl (Tape.init_move_right_hasBinarySuffix stream)
      ⟨rfl, by simp⟩ (Tape.StartInvariant.init_nil.move .right)
      Tape.init_nil_move_right_hasBinaryPrefix_nil
  exact ⟨final, .step hstep hrun, hhalt, by simpa [decode] using hout⟩

/-- A total linear-time contract, including malformed streams. Incomplete
trailing queries are discarded according to `decode`. -/
theorem run_linear (oracle : BooleanOracle) (stream : List Bool) :
    ∃ final elapsed, elapsed ≤ 5 * stream.length + 2 ∧
      machine.reachesIn oracle elapsed (machine.initCfg stream) final ∧
      machine.halted final ∧ final.output.HasOutput ((decode stream).map oracle) := by
  obtain ⟨final, hrun, hhalt, hout⟩ := run oracle stream
  have hbound := costFrom_le stream []
  exact ⟨final, costFrom [] stream + 1, by simpa using Nat.add_le_add_right hbound 1,
    hrun, hhalt, hout.hasOutput⟩

/-- One answer is emitted per query, with an exact cost that charges every
data bit, delimiter, lookup, answer write, and query-head rewind. -/
theorem run_encoded (oracle : BooleanOracle) (queries : List (List Bool)) :
    ∃ final, machine.reachesIn oracle
        (2 + (queries.map (fun query => 3 * query.length + 5)).sum)
        (machine.initCfg (encode queries)) final ∧ machine.halted final ∧
      final.output.HasBinaryPrefix (queries.map oracle) := by
  obtain ⟨final, hrun, hhalt, hout⟩ := run oracle (encode queries)
  refine ⟨final, ?_, hhalt, by simpa using hout⟩
  convert hrun using 1
  rw [costFrom_encode]
  omega

end Toda.Oracle.Batch

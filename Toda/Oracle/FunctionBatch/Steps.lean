import Toda.Oracle.FunctionBatch.Rewind

/-! # Framed stream-reading transitions -/

namespace Toda.Oracle.FunctionBatch

open Complexity
open Batch (QueryPrefix query_idle output_write_blank binary)

theorem tag_step (oracle : FunctionOracle) (pending answers rest : List Bool)
    (tag : Bool) (cfg : FunctionCfg 0 machine.Q) (hs : cfg.state = .tag)
    (hin : cfg.input.HasBinarySuffix (tag :: rest))
    (hq : QueryPrefix cfg.query pending) (hi : cfg.query.StartInvariant)
    (ho : cfg.output.HasBinaryPrefix answers) :
    machine.step oracle cfg = some
      { cfg with state := if tag then .data else .query, input := cfg.input.move .right, answer := discardStep cfg.answer } := by
  have hir := hin.read_cons
  have hqr : cfg.query.read ≠ .start := hi.read_ne_start (by rw [hq.1]; omega)
  have hqw : cfg.query.write (TM.readBackWrite cfg.query.read) = cfg.query := by
    simpa [TM.transitionTape, TM.idleDir, hqr, Tape.move] using query_idle hi hq
  have how := output_write_blank ho
  cases tag <;>
    simp [FunctionTM.step, machine, transition, hs, hir, Γ.ofBool, binary,
      TM.idleDir, hqr, ho.read_blank, how, discardStep, Tape.move] <;>
    exact ⟨hqw, Subsingleton.elim _ _⟩

theorem data_step (oracle : FunctionOracle) (answers rest : List Bool)
    (bit : Bool) (cfg : FunctionCfg 0 machine.Q) (hs : cfg.state = .data)
    (hin : cfg.input.HasBinarySuffix (bit :: rest))
    (ho : cfg.output.HasBinaryPrefix answers) :
    machine.step oracle cfg = some
      { cfg with state := .tag, input := cfg.input.move .right, query := cfg.query.writeAndMove (Γ.ofBool bit) .right, answer := discardStep cfg.answer } := by
  have hir := hin.read_cons
  have how := output_write_blank ho
  cases bit <;>
    simp [FunctionTM.step, machine, transition, hs, hir, Γ.ofBool, binary,
      TM.readBackWrite, TM.idleDir, ho.read_blank, how, discardStep, Tape.move] <;>
    exact Subsingleton.elim _ _

theorem halt_step (oracle : FunctionOracle) (pending answers : List Bool)
    (inData : Bool) (cfg : FunctionCfg 0 machine.Q)
    (hs : cfg.state = if inData then .data else .tag)
    (hin : cfg.input.read = .blank)
    (hq : QueryPrefix cfg.query pending) (hi : cfg.query.StartInvariant)
    (ho : cfg.output.HasBinaryPrefix answers) :
    ∃ final, machine.step oracle cfg = some final ∧ machine.halted final ∧
      final.output = cfg.output := by
  have hqr : cfg.query.read ≠ .start := hi.read_ne_start (by rw [hq.1]; omega)
  have hqw : cfg.query.write (TM.readBackWrite cfg.query.read) = cfg.query := by
    simpa [TM.transitionTape, TM.idleDir, hqr, Tape.move] using query_idle hi hq
  have how := output_write_blank ho
  cases inData with
  | false =>
    let final : FunctionCfg 0 machine.Q := { cfg with state := .halt, answer := discardStep cfg.answer }
    refine ⟨final, ?_, rfl, rfl⟩
    simp [FunctionTM.step, machine, transition, hs, hin, final, binary,
      TM.idleDir, hqr, ho.read_blank, how, discardStep, Tape.move]
    exact ⟨hqw, Subsingleton.elim _ _⟩
  | true =>
    let final : FunctionCfg 0 machine.Q :=
      { cfg with state := .halt, query := cfg.query.write Γ.blank, answer := discardStep cfg.answer }
    refine ⟨final, ?_, rfl, rfl⟩
    simp [FunctionTM.step, machine, transition, hs, hin, final, binary,
      TM.readBackWrite, TM.idleDir, hqr, ho.read_blank, how, discardStep, Tape.move]
    exact Subsingleton.elim _ _

end Toda.Oracle.FunctionBatch

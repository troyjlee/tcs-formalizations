import Toda.Oracle.FunctionBatch.Defs

/-! # One streaming lookup, answer append, and query-head reset -/

namespace Toda.Oracle.FunctionBatch

open Complexity
open Batch (QueryPrefix query_idle output_write_blank binary)

theorem rewind_run (oracle : FunctionOracle) (height : ℕ) :
    ∀ (cfg : FunctionCfg 0 machine.Q) (answers : List Bool),
      cfg.state = .rewind → cfg.query.head = height → cfg.query.StartInvariant →
      cfg.input.read ≠ .start → cfg.output.HasBinaryPrefix answers →
      ∃ final, machine.reachesIn oracle (height + 1) cfg final ∧
        final.state = .tag ∧ final.query.head = 1 ∧ final.query.StartInvariant ∧
        final.input = cfg.input ∧ final.output = cfg.output := by
  induction height with
  | zero =>
    intro cfg answers hs hh hi hin ho
    have hr : cfg.query.read = .start := by simp [Tape.read, hh, hi.1]
    have hwrite : cfg.query.write Γ.blank = cfg.query := by simp [Tape.write, hh]
    have houtput := output_write_blank ho
    let final : FunctionCfg 0 machine.Q :=
      { cfg with state := .tag, query := cfg.query.move .right, answer := discardStep cfg.answer }
    have hstep : machine.step oracle cfg = some final := by
      simp [FunctionTM.step, machine, transition, hs, hr, final, hin,
        TM.readBackWrite, TM.idleDir, houtput, discardStep, Tape.writeAndMove, hwrite,
        ho.read_blank, Tape.move]
      exact Subsingleton.elim _ _
    refine ⟨final, .step hstep .zero, rfl, ?_, ?_, rfl, rfl⟩
    · simp [final, Tape.move, hh]
    · exact hi.move .right
  | succ height ih =>
    intro cfg answers hs hh hi hin ho
    have hr : cfg.query.read ≠ .start := hi.read_ne_start (by omega)
    let query := cfg.query.writeAndMove (TM.readBackWrite cfg.query.read) .left
    let next : FunctionCfg 0 machine.Q := { cfg with state := .rewind, query := query, answer := discardStep cfg.answer }
    have houtput := output_write_blank ho
    have hstep : machine.step oracle cfg = some next := by
      simp [FunctionTM.step, machine, transition, hs, hr, next, query, hin,
        TM.idleDir, houtput, ho.read_blank, discardStep, Tape.move]
      exact Subsingleton.elim _ _
    have hhead : next.query.head = height := by
      simp [next, query, Tape.move, Tape.write_head, hh]
    have hinv : next.query.StartInvariant :=
      hi.writeAndMove (TM.readBackWrite cfg.query.read) .left
    obtain ⟨final, hrun, hstate, hhead', hi', hinput, hout⟩ :=
      ih next answers rfl hhead hinv hin ho
    exact ⟨final, .step hstep hrun, hstate, hhead', hi', hinput, hout⟩


end Toda.Oracle.FunctionBatch

import Toda.Oracle.Batch.Defs
import Toda.Oracle.Preprocess.Defs

/-! # One streaming lookup, answer append, and query-head reset -/

namespace Toda.Oracle.Batch

open Complexity

theorem rewind_run (oracle : BooleanOracle) (height : ℕ) :
    ∀ (cfg : OracleCfg 0 machine.Q) (answers : List Bool),
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
    let final : OracleCfg 0 machine.Q :=
      { cfg with state := .tag, query := cfg.query.move .right }
    have hstep : machine.step oracle cfg = some final := by
      simp [OracleTM.step, machine, transition, hs, hr, final, hin,
        TM.readBackWrite, TM.idleDir, houtput, Tape.writeAndMove, hwrite,
        ho.read_blank, Tape.move]
      exact Subsingleton.elim _ _
    refine ⟨final, .step hstep .zero, rfl, ?_, ?_, rfl, rfl⟩
    · simp [final, Tape.move, hh]
    · exact hi.move .right
  | succ height ih =>
    intro cfg answers hs hh hi hin ho
    have hr : cfg.query.read ≠ .start := hi.read_ne_start (by omega)
    let query := cfg.query.writeAndMove (TM.readBackWrite cfg.query.read) .left
    let next : OracleCfg 0 machine.Q := { cfg with state := .rewind, query := query }
    have houtput := output_write_blank ho
    have hstep : machine.step oracle cfg = some next := by
      simp [OracleTM.step, machine, transition, hs, hr, next, query, hin,
        TM.idleDir, houtput, ho.read_blank, Tape.move]
      exact Subsingleton.elim _ _
    have hhead : next.query.head = height := by
      simp [next, query, Tape.move, Tape.write_head, hh]
    have hinv : next.query.StartInvariant :=
      hi.writeAndMove (TM.readBackWrite cfg.query.read) .left
    obtain ⟨final, hrun, hstate, hhead', hi', hinput, hout⟩ :=
      ih next answers rfl hhead hinv hin ho
    exact ⟨final, .step hstep hrun, hstate, hhead', hi', hinput, hout⟩

theorem answer_step (oracle : BooleanOracle) (pending answers : List Bool)
    (cfg : OracleCfg 0 machine.Q) (hs : cfg.state = .query)
    (hq : QueryPrefix cfg.query pending) (hi : cfg.query.StartInvariant)
    (hin : cfg.input.read ≠ .start) (ho : cfg.output.HasBinaryPrefix answers) :
    ∃ next, machine.reachesIn oracle 2 cfg next ∧ next.state = .rewind ∧
      next.query = cfg.query ∧ next.input = cfg.input ∧
      next.output.HasBinaryPrefix (answers ++ [oracle pending]) := by
  have hquery := hq.oracleQuery
  have hkeep := query_idle hi hq
  have hread : cfg.query.read ≠ .start := hi.read_ne_start (by rw [hq.1]; omega)
  cases hb : oracle pending with
  | false =>
    let answered : OracleCfg 0 machine.Q := { cfg with state := .no }
    let next : OracleCfg 0 machine.Q :=
      { cfg with state := .rewind, output := cfg.output.writeAndMove Γ.zero .right }
    refine ⟨next, .step (middle := answered) ?_ (.step ?_ .zero), rfl, rfl, rfl, ?_⟩
    · exact machine.step_query_false (yesState := .yes)
        (by simp [hs, machine]) (by simp [hs, machine]) (by simpa [hquery] using hb)
    · simp [OracleTM.step, machine, transition, answered, next, hin,
        TM.idleDir, hread, Tape.move]
      have hwrite : cfg.query.write (TM.readBackWrite cfg.query.read) = cfg.query := by
        simpa [TM.transitionTape, TM.idleDir, hread, Tape.move] using hkeep
      exact ⟨hwrite, Subsingleton.elim _ _⟩
    · simpa [next, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit false ho
  | true =>
    let answered : OracleCfg 0 machine.Q := { cfg with state := .yes }
    let next : OracleCfg 0 machine.Q :=
      { cfg with state := .rewind, output := cfg.output.writeAndMove Γ.one .right }
    refine ⟨next, .step (middle := answered) ?_ (.step ?_ .zero), rfl, rfl, rfl, ?_⟩
    · exact machine.step_query_true (noState := .no)
        (by simp [hs, machine]) (by simp [hs, machine]) (by simpa [hquery] using hb)
    · simp [OracleTM.step, machine, transition, answered, next, hin,
        TM.idleDir, hread, Tape.move]
      have hwrite : cfg.query.write (TM.readBackWrite cfg.query.read) = cfg.query := by
        simpa [TM.transitionTape, TM.idleDir, hread, Tape.move] using hkeep
      exact ⟨hwrite, Subsingleton.elim _ _⟩
    · simpa [next, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit true ho

/-- Lookup and append take two steps; rewinding takes `|pending|+2`.
Old query cells are preserved but cease to be part of the delimited query. -/
theorem ask_reset (oracle : BooleanOracle) (pending answers : List Bool)
    (cfg : OracleCfg 0 machine.Q) (hs : cfg.state = .query)
    (hq : QueryPrefix cfg.query pending) (hi : cfg.query.StartInvariant)
    (hin : cfg.input.read ≠ .start) (ho : cfg.output.HasBinaryPrefix answers) :
    ∃ final, machine.reachesIn oracle (pending.length + 4) cfg final ∧
      final.state = .tag ∧ QueryPrefix final.query [] ∧ final.query.StartInvariant ∧
      final.input = cfg.input ∧
      final.output.HasBinaryPrefix (answers ++ [oracle pending]) := by
  obtain ⟨next, hquery, hs', hq', hin', hout⟩ :=
    answer_step oracle pending answers cfg hs hq hi hin ho
  have hhead : next.query.head = pending.length + 1 := by rw [hq']; exact hq.1
  obtain ⟨final, hreset, htag, hhead', hi', hinput, houtput⟩ :=
    rewind_run oracle (pending.length + 1) next (answers ++ [oracle pending]) hs'
      hhead (by rwa [hq']) (by rwa [hin']) hout
  refine ⟨final, ?_, htag, ?_, hi', hinput.trans hin', ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Preprocess.reachesIn_trans hquery hreset
  · exact ⟨hhead', by simp⟩
  · rwa [houtput]

end Toda.Oracle.Batch

import Toda.Oracle.FunctionBatch.Rewind

/-! # Copying full binary answers with every output write charged -/

namespace Toda.Oracle.FunctionBatch

open Complexity
open Batch (QueryPrefix query_idle output_write_blank binary)

private theorem write_readBack {t : Tape} (h : t.read ≠ Γ.start) :
    t.write (TM.readBackWrite t.read) = t := by
  simpa [TM.transitionTape, TM.idleDir, h, Tape.move] using
    TM.transitionTape_eq_self h

/-- Copy one complete answer using the self-delimiting batch encoding. -/
theorem copy_answer (oracle : FunctionOracle) (bits : List Bool) :
    ∀ (pending answers : List Bool) (cfg : FunctionCfg 0 machine.Q),
      cfg.state = .answerTag → cfg.answer.HasBinarySuffix bits →
      QueryPrefix cfg.query pending → cfg.query.StartInvariant →
      cfg.input.read ≠ .start → cfg.output.HasBinaryPrefix answers →
      ∃ final, machine.reachesIn oracle (2 * bits.length + 1) cfg final ∧
        final.state = .rewind ∧ final.query = cfg.query ∧ final.input = cfg.input ∧
        final.output.HasBinaryPrefix (answers ++ Batch.encodeQuery bits) := by
  induction bits with
  | nil =>
    intro pending answers cfg hs ha hq hi hin ho
    have hqr : cfg.query.read ≠ .start := hi.read_ne_start (by rw [hq.1]; omega)
    have hqw := write_readBack hqr
    have haw := write_readBack ha.read_ne_start
    let final : FunctionCfg 0 machine.Q :=
      { cfg with state := .rewind, output := cfg.output.writeAndMove Γ.zero .right }
    have hstep : machine.step oracle cfg = some final := by
      simp [FunctionTM.step, machine, transition, hs, ha.read_nil, binary,
        final, TM.idleDir, hin, hqr, ho.read_blank, Tape.move]
      exact ⟨hqw, by simpa [ha.read_nil, TM.readBackWrite] using haw, Subsingleton.elim _ _⟩
    refine ⟨final, .step hstep .zero, rfl, rfl, rfl, ?_⟩
    simpa [final, Batch.encodeQuery, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit false ho
  | cons bit bits ih =>
    intro pending answers cfg hs ha hq hi hin ho
    have hqr : cfg.query.read ≠ .start := hi.read_ne_start (by rw [hq.1]; omega)
    have hqw := write_readBack hqr
    have haw := write_readBack ha.read_ne_start
    let tagged : FunctionCfg 0 machine.Q :=
      { cfg with state := .answerData, output := cfg.output.writeAndMove Γ.one .right }
    have htag : machine.step oracle cfg = some tagged := by
      cases bit <;>
        simp [FunctionTM.step, machine, transition, hs, ha.read_cons, binary,
          tagged, TM.idleDir, hin, hqr, Γ.ofBool, Tape.move] <;>
        exact ⟨hqw, by simpa [ha.read_cons, Γ.ofBool, TM.readBackWrite] using haw,
          Subsingleton.elim _ _⟩
    have houtTag : tagged.output.HasBinaryPrefix (answers ++ [true]) :=
      Tape.hasBinaryPrefix_write_bit true ho
    let next : FunctionCfg 0 machine.Q :=
      { tagged with
        state := .answerTag
        answer := cfg.answer.move .right
        output := tagged.output.writeAndMove (Γ.ofBool bit) .right }
    have hdata : machine.step oracle tagged = some next := by
      cases bit <;>
        simp [FunctionTM.step, machine, transition, tagged, next, ha.read_cons, binary,
          TM.idleDir, hin, hqr, Γ.ofBool, TM.readBackWrite] <;>
        exact ⟨by simp [Tape.move],
          by simpa [TM.transitionTape, TM.readBackWrite, TM.idleDir, hqr] using query_idle hi hq,
          by simpa [Tape.writeAndMove, ha.read_cons, Γ.ofBool, TM.readBackWrite] using
            congrArg (fun t : Tape => t.move .right) haw,
          Subsingleton.elim _ _⟩
    have houtNext : next.output.HasBinaryPrefix (answers ++ [true] ++ [bit]) :=
      Tape.hasBinaryPrefix_write_bit bit houtTag
    obtain ⟨final, hrest, hstate, hquery, hinput, houtput⟩ :=
      ih pending (answers ++ [true] ++ [bit]) next rfl ha.move_right_cons hq hi hin houtNext
    refine ⟨final, ?_, hstate, hquery, hinput, ?_⟩
    · convert FunctionTM.reachesIn.step htag (.step hdata hrest) using 1
    · simpa [Batch.encodeQuery, List.append_assoc] using houtput

/-- One query step supplies the answer; one local step moves its head past
the marker; then every data bit and its encoding tag are copied locally. -/
theorem answer_step (oracle : FunctionOracle) (pending answers : List Bool)
    (cfg : FunctionCfg 0 machine.Q) (hs : cfg.state = .query)
    (hq : QueryPrefix cfg.query pending) (hi : cfg.query.StartInvariant)
    (hin : cfg.input.read ≠ .start) (ho : cfg.output.HasBinaryPrefix answers) :
    ∃ next, machine.reachesIn oracle (2 * (oracle pending).bits.length + 3) cfg next ∧
      next.state = .rewind ∧ next.query = cfg.query ∧ next.input = cfg.input ∧
      next.output.HasBinaryPrefix (answers ++ Batch.encodeQuery (oracle pending).bits) := by
  let queried : FunctionCfg 0 machine.Q :=
    { cfg with state := .answerBoot, answer := FunctionTM.answerTape (oracle pending) }
  have hquery : machine.step oracle cfg = some queried := by
    simpa [queried, hq.oracleQuery] using
      FunctionTM.step_query (machine := machine) (oracle := oracle)
        (cfg := cfg) (next := .answerBoot) (by simp [machine, hs]) (by simp [machine, hs])
  let copying : FunctionCfg 0 machine.Q :=
    { queried with
      state := .answerTag
      answer := (FunctionTM.answerTape (oracle pending)).move .right }
  have hqr : cfg.query.read ≠ .start := hi.read_ne_start (by rw [hq.1]; omega)
  have hqw := write_readBack hqr
  have hboot : machine.step oracle queried = some copying := by
    simp [FunctionTM.step, machine, transition, queried, copying, FunctionTM.answerTape,
      TM.idleDir, hin, hqr, ho.read_blank, Tape.init, Tape.writeAndMove, Tape.write, Tape.move]
    exact ⟨by simpa [Tape.write] using hqw, Subsingleton.elim _ _,
      by simpa [Tape.write] using output_write_blank ho⟩
  obtain ⟨next, hcopy, hstate, hquery', hinput, houtput⟩ :=
    copy_answer oracle (oracle pending).bits pending answers copying rfl
      (Tape.init_move_right_hasBinarySuffix _) hq hi hin ho
  refine ⟨next, ?_, hstate, hquery', hinput, houtput⟩
  convert FunctionTM.reachesIn.step hquery (.step hboot hcopy) using 1

/-- Full answer copying followed by a costed rewind of the query head. -/
theorem ask_reset (oracle : FunctionOracle) (pending answers : List Bool)
    (cfg : FunctionCfg 0 machine.Q) (hs : cfg.state = .query)
    (hq : QueryPrefix cfg.query pending) (hi : cfg.query.StartInvariant)
    (hin : cfg.input.read ≠ .start) (ho : cfg.output.HasBinaryPrefix answers) :
    ∃ final, machine.reachesIn oracle (pending.length + 2 * (oracle pending).bits.length + 5)
      cfg final ∧ final.state = .tag ∧ QueryPrefix final.query [] ∧
      final.query.StartInvariant ∧ final.input = cfg.input ∧
      final.output.HasBinaryPrefix (answers ++ Batch.encodeQuery (oracle pending).bits) := by
  obtain ⟨next, hanswer, hs', hq', hin', hout⟩ :=
    answer_step oracle pending answers cfg hs hq hi hin ho
  have hhead : next.query.head = pending.length + 1 := by rw [hq']; exact hq.1
  obtain ⟨final, hreset, htag, hhead', hi', hinput, houtput⟩ :=
    rewind_run oracle (pending.length + 1) next
      (answers ++ Batch.encodeQuery (oracle pending).bits) hs' hhead
      (by rwa [hq']) (by rwa [hin']) hout
  refine ⟨final, ?_, htag, ⟨hhead', by simp⟩, hi', hinput.trans hin', ?_⟩
  · convert FunctionTM.reachesIn_trans hanswer hreset using 1
    omega
  · rwa [houtput]

end Toda.Oracle.FunctionBatch

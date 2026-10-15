import Toda.Oracle.Batch.Steps

/-! # Exact execution of the total stream decoder -/

namespace Toda.Oracle.Batch

open Complexity

/-- Prepared streaming contract, permitting already appended answers and an
arbitrary partial query whose unused suffix may contain old query data. -/
def RunsFrom (oracle : BooleanOracle) (stream : List Bool) : Prop :=
  ∀ (pending answers : List Bool) (cfg : OracleCfg 0 machine.Q),
    cfg.state = .tag → cfg.input.HasBinarySuffix stream →
    QueryPrefix cfg.query pending → cfg.query.StartInvariant →
    cfg.output.HasBinaryPrefix answers →
    ∃ final, machine.reachesIn oracle (costFrom pending stream) cfg final ∧
      machine.halted final ∧
      final.output.HasBinaryPrefix (answers ++ (decodeFrom pending stream).map oracle)

theorem run_nil (oracle : BooleanOracle) : RunsFrom oracle [] := by
  intro pending answers cfg hs hin hq hi ho
  obtain ⟨final, hstep, hhalt, hout⟩ :=
    halt_step oracle pending answers false cfg hs hin.read_nil hq hi ho
  refine ⟨final, .step hstep .zero, hhalt, ?_⟩
  simpa [decodeFrom, hout] using ho

theorem run_false (oracle : BooleanOracle) (rest : List Bool)
    (hrec : RunsFrom oracle rest) : RunsFrom oracle (false :: rest) := by
  intro pending answers cfg hs hin hq hi ho
  let querying : OracleCfg 0 machine.Q :=
    { cfg with state := .query, input := cfg.input.move .right }
  have hstep : machine.step oracle cfg = some querying :=
    tag_step oracle pending answers rest false cfg hs hin hq hi ho
  have hremaining : querying.input.HasBinarySuffix rest := hin.move_right_cons
  obtain ⟨next, hreset, htag, hqnext, hinext, hinextinput, hout⟩ :=
    ask_reset oracle pending answers querying rfl hq hi hremaining.read_ne_start ho
  have hnextinput : next.input.HasBinarySuffix rest := by rwa [hinextinput]
  obtain ⟨final, hrun, hhalt, houtput⟩ :=
    hrec [] (answers ++ [oracle pending]) next htag hnextinput hqnext hinext hout
  refine ⟨final, ?_, hhalt, ?_⟩
  · simpa [costFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Preprocess.reachesIn_trans (OracleTM.reachesIn.step hstep hreset) hrun
  · simpa [decodeFrom, List.append_assoc] using houtput

theorem run_trailing_tag (oracle : BooleanOracle) : RunsFrom oracle [true] := by
  intro pending answers cfg hs hin hq hi ho
  let dataCfg : OracleCfg 0 machine.Q :=
    { cfg with state := .data, input := cfg.input.move .right }
  have hstep : machine.step oracle cfg = some dataCfg :=
    tag_step oracle pending answers [] true cfg hs hin hq hi ho
  have hremaining : dataCfg.input.HasBinarySuffix [] := hin.move_right_cons
  obtain ⟨final, hfinish, hhalt, hout⟩ :=
    halt_step oracle pending answers true dataCfg rfl hremaining.read_nil hq hi ho
  refine ⟨final, .step hstep (.step hfinish .zero), hhalt, ?_⟩
  simpa [decodeFrom, hout, dataCfg] using ho

theorem run_true_bit (oracle : BooleanOracle) (bit : Bool) (rest : List Bool)
    (hrec : RunsFrom oracle rest) : RunsFrom oracle (true :: bit :: rest) := by
  intro pending answers cfg hs hin hq hi ho
  let dataCfg : OracleCfg 0 machine.Q :=
    { cfg with state := .data, input := cfg.input.move .right }
  have htag : machine.step oracle cfg = some dataCfg :=
    tag_step oracle pending answers (bit :: rest) true cfg hs hin hq hi ho
  have hremaining : dataCfg.input.HasBinarySuffix (bit :: rest) := hin.move_right_cons
  let next : OracleCfg 0 machine.Q :=
    { dataCfg with state := .tag, input := dataCfg.input.move .right, query := dataCfg.query.writeAndMove (Γ.ofBool bit) .right }
  have hbit : machine.step oracle dataCfg = some next :=
    data_step oracle answers rest bit dataCfg rfl hremaining ho
  have hnextinput : next.input.HasBinarySuffix rest := hremaining.move_right_cons
  have hnextquery : QueryPrefix next.query (pending ++ [bit]) := hq.write_bit bit
  have hnextinv : next.query.StartInvariant := by
    have hwrite := hi.writeAndMove (Γw.ofBool bit) .right
    cases bit <;> simpa [next, dataCfg, Γw.ofBool, Γ.ofBool] using hwrite
  obtain ⟨final, hrun, hhalt, houtput⟩ :=
    hrec (pending ++ [bit]) answers next rfl hnextinput hnextquery hnextinv ho
  refine ⟨final, ?_, hhalt, houtput⟩
  convert OracleTM.reachesIn.step htag (OracleTM.reachesIn.step hbit hrun) using 1
  simp only [costFrom]
  omega

/-- The machine implements the total decoder on every binary input suffix. -/
theorem runsFrom (oracle : BooleanOracle) (stream : List Bool) : RunsFrom oracle stream := by
  induction stream using List.twoStepInduction with
  | nil => exact run_nil oracle
  | singleton bit =>
    cases bit with
    | false => exact run_false oracle [] (run_nil oracle)
    | true => exact run_trailing_tag oracle
  | cons_cons tag bit rest ih ih' =>
    cases tag with
    | false => exact run_false oracle (bit :: rest) (ih' bit)
    | true => exact run_true_bit oracle bit rest ih

end Toda.Oracle.Batch

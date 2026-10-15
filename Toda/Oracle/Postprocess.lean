import Toda.Oracle.Postprocess.Normalize

/-! # Ordinary FP postprocessing after a Boolean-oracle computation -/

namespace Toda.Oracle.Postprocess

open Complexity

variable {n k : ℕ}

theorem entry_eq (N : TM k) (realInput stream : Tape) (bits : List Bool)
    (hh : stream.head = 1) (hc : stream.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    entry N realInput stream = TM.retargetInputStartedCfg N bits realInput := by
  have hs : stream = (Tape.init (bits.map Γ.ofBool)).move .right := Tape.ext hh hc
  subst stream
  congr 1

/-- A complete source oracle run followed by an ordinary machine, with fresh
scratch and a charged rewind of the answer tape. -/
theorem run (M : OracleTM n) (N : TM k) (oracle : BooleanOracle)
    {post : List Bool → List Bool} {S : ℕ → ℕ} (hpost : N.ComputesInTime post S)
    (input answers : List Bool) {cfg : OracleCfg n M.Q} {time : ℕ}
    (hsource : M.reachesIn oracle time (M.initCfg input) cfg) (hhalt : M.halted cfg)
    (hout : cfg.output.HasBinaryPrefix answers) :
    ∃ final elapsed, elapsed ≤ time + answers.length + 3 + S answers.length ∧
      (machine M N).reachesIn oracle elapsed ((machine M N).initCfg input) final ∧
      (machine M N).halted final ∧ final.output.HasOutput (post answers) := by
  have hinv := oracle_reachesIn_startInvariant hsource
    (Tape.StartInvariant.init_ofBool input) Tape.StartInvariant.init_nil
    (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil
  let realInput := TM.transitionInput cfg.input
  let query := TM.transitionTape cfg.query
  let scratch : Fin n → Tape := fun i => TM.transitionTape (cfg.work i)
  have hreal : realInput.read ≠ .start :=
    PrepareBatch.transitionInput_read_ne_start cfg.input hinv.1
  have hquery : query.read ≠ .start :=
    PrepareBatch.transitionTape_read_ne_start cfg.query hinv.2.1
  have hscratch : ∀ i, (scratch i).read ≠ .start := fun i =>
    PrepareBatch.transitionTape_read_ne_start (cfg.work i) (hinv.2.2.1 i)
  obtain ⟨parked, hsourceLift⟩ := source_run M N oracle hsource false
  have hboundary := boundary_step M N oracle cfg parked hhalt hout.read_blank
  obtain ⟨ready, hrewind, hh, hc⟩ := rewind_run M N oracle realInput query scratch
    hreal hquery hscratch cfg.output.head cfg.output rfl hinv.2.2.2
  have hentry := entry_eq N realInput ready answers hh
    (hc.trans (hout.cells_eq_init hinv.2.2.2.1))
  obtain ⟨postFinal, postTime, hpostTime, hpostRun, hpostHalt, hpostOut⟩ :=
    TM.retargetInputStarted_computesVirtual N hpost answers realInput
  have hpostLift := post_run M N oracle query scratch hquery hscratch hpostRun
  rw [← hentry] at hpostLift
  have htail := Preprocess.reachesIn_trans (OracleTM.reachesIn.step hboundary hrewind) hpostLift
  have hrun := Preprocess.reachesIn_trans hsourceLift htail
  refine ⟨postCfg M N query scratch postFinal,
    time + (cfg.output.head + 2 + postTime), ?_, ?_, ?_, hpostOut⟩
  · have := hout.1
    omega
  · simpa using hrun
  · exact congrArg (fun q => Sum.inr (some q)) hpostHalt

end Toda.Oracle.Postprocess

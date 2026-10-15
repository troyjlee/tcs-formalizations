import Toda.Oracle.PrepareBatch.Normalize
import Toda.Oracle.Classes

/-!
# Polynomial-time preparation and execution of a nonadaptive query batch

Preparation writes its stream onto a fresh work tape. After a charged rewind,
the batch evaluator reads that tape, retaining the source's parked scratch
without reusing it as clean storage. The actual oracle machine returns exactly
the decoded batch's answers and runs within `7 * T(n) + 4` steps.
-/

namespace Toda.Oracle.PrepareBatch

open Complexity

variable {n : ℕ}

theorem transitionInput_read_ne_start (t : Tape) (hi : t.StartInvariant) :
    (TM.transitionInput t).read ≠ .start := by
  exact (hi.move (TM.idleDir t.read)).read_ne_start
    (TM.transitionInput_head_ge t hi.1)

theorem transitionTape_read_ne_start (t : Tape) (hi : t.StartInvariant) :
    (TM.transitionTape t).read ≠ .start := by
  exact (hi.writeAndMove (TM.readBackWrite t.read) (TM.idleDir t.read)).read_ne_start
    (TM.one_le_head_transitionTape t hi.1)

/-- End-to-end ordinary-input execution. The output prefix invariant includes
its append position and blank tail, not just its decoded value. -/
theorem run (M : TM n) {prepare : List Bool → List Bool} {T : ℕ → ℕ}
    (hprepare : M.ComputesInTime prepare T) (oracle : BooleanOracle)
    (input : List Bool) :
    ∃ final elapsed, elapsed ≤ 7 * T input.length + 4 ∧
      (machine M).reachesIn oracle elapsed ((machine M).initCfg input) final ∧
      (machine M).halted final ∧
      final.output.HasBinaryPrefix ((Batch.decode (prepare input)).map oracle) := by
  obtain ⟨cfg, time, htime, hsource, hhalt, hout, hblank, hblankhead⟩ :=
    TM.retargetOutput_computesInTime_boundary M hprepare input
  have hinvariants := TM.reachesIn_startInvariant hsource
    (Tape.StartInvariant.init_ofBool input) (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil
  let realInput := TM.transitionInput cfg.input
  let scratch : Fin n → Tape := fun i => TM.transitionTape (cfg.work (Fin.castSucc i))
  let stream := TM.transitionTape (cfg.work (Fin.last n))
  have hreal : realInput.read ≠ .start :=
    transitionInput_read_ne_start cfg.input hinvariants.1
  have hscratch : ∀ i, (scratch i).read ≠ .start := fun i =>
    transitionTape_read_ne_start (cfg.work (Fin.castSucc i)) (hinvariants.2.1 _)
  have hstreamInv : stream.StartInvariant :=
    (hinvariants.2.1 (Fin.last n)).writeAndMove
      (TM.readBackWrite (cfg.work (Fin.last n)).read)
      (TM.idleDir (cfg.work (Fin.last n)).read)
  have hstreamCells : stream.cells = (cfg.work (Fin.last n)).cells :=
    TM.transitionTape_cells (cfg.work (Fin.last n)) (hinvariants.2.1 _).2
  have hstreamOut : stream.HasOutput (prepare input) :=
    (Tape.hasOutput_congr hstreamCells _).mpr hout
  have hhead : stream.head ≤ time + 1 := by
    apply TM.head_transitionTape_le (hinvariants.2.1 _).1
    simpa using M.retargetOutput.work_head_reachesIn_bound hsource (Fin.last n)
  have hboundary : (machine M).step oracle (liftCfg M time cfg) =
      some (rewindCfg M realInput scratch stream) :=
    boundary_step M oracle time cfg hhalt (transitionTape_blank cfg.output hblank hblankhead)
  obtain ⟨ready, hrewind, hreadyHead, hreadyCells⟩ :=
    rewind_run M oracle realInput scratch hreal hscratch stream.head stream rfl hstreamInv
  have hreadyInv : ready.StartInvariant := by
    simpa only [Tape.StartInvariant, hreadyCells] using hstreamInv
  have hreadyOut : ready.HasOutput (prepare input) :=
    (Tape.hasOutput_congr hreadyCells _).mpr hstreamOut
  have hsuffix : ready.HasBinarySuffix (prepare input) :=
    hreadyOut.hasBinarySuffix hreadyHead hreadyInv
  obtain ⟨batchFinal, hbatch, hbatchHalt, hanswers⟩ :=
    Batch.runsFrom oracle (prepare input) [] [] (readerCfg ready) rfl hsuffix
      ⟨rfl, by simp⟩ (Tape.StartInvariant.init_nil.move .right)
      Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hbatchLift := batch_lift_run M oracle realInput scratch hreal hscratch hbatch
    hreadyInv (by change 1 ≤ ready.head; omega)
  have htail := Preprocess.reachesIn_trans (OracleTM.reachesIn.step hboundary hrewind)
    hbatchLift
  have hfirst : (machine M).reachesIn oracle time ((machine M).initCfg input)
      (liftCfg M time cfg) := by simpa using lift_run M oracle hsource 0
  refine ⟨batchCfg M realInput scratch batchFinal,
    time + (stream.head + 2 + Batch.costFrom [] (prepare input)), ?_,
    Preprocess.reachesIn_trans hfirst htail, ?_, ?_⟩
  · have hlength := hprepare.output_length_le input
    have hcost := Batch.costFrom_le (prepare input) []
    simp only [List.length_nil] at hcost
    omega
  · change Sum.inr (some batchFinal.state) = Sum.inr (some Batch.Phase.halt)
    exact congrArg (fun q => Sum.inr (some q)) hbatchHalt
  · simpa [Batch.decode, batchCfg] using hanswers

/-- The prepared stream may be any FP function; its decoded answer sequence
is produced by one actual polynomial-time oracle machine. -/
theorem exists_polynomial_machine {prepare : List Bool → List Bool}
    (hprepare : prepare ∈ FP) :
    ∃ (tapes : ℕ) (M : OracleTM tapes) (time : ℕ → ℕ), PolyBound time ∧
      ∀ oracle input, ∃ final elapsed, elapsed ≤ time input.length ∧
        M.reachesIn oracle elapsed (M.initCfg input) final ∧ M.halted final ∧
        final.output.HasBinaryPrefix ((Batch.decode (prepare input)).map oracle) := by
  obtain ⟨degree, tapes, M, T, hcompute, htime⟩ := hprepare
  exact ⟨tapes + 1, machine M, fun length => 7 * T length + 4,
    ((PolyBound.const 7).mul (BigO.pow_polynomial_bound htime)).add (PolyBound.const 4),
    run M hcompute⟩

end Toda.Oracle.PrepareBatch

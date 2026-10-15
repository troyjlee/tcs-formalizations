import Toda.Oracle.Preprocess.Normalize
import Toda.Oracle.Classes

/-!
# Polynomial-time preparation of one Boolean-oracle query

The ordinary preparation machine writes directly onto the dedicated query
tape. Its output head can finish anywhere: an explicit rewind and scan find
the output delimiter before the lookup. The complete machine has clock
`3 * T(n) + 6`, including source execution, head normalization, lookup, and
normalized verdict writing. No preloaded query or assumed oracle compiler
is used.
-/

namespace Toda.Oracle.Preprocess

open Complexity

variable {n : ℕ}

/-- Compile one complete ordinary-machine run, charging for both its output
head position and its output length before consulting the oracle. -/
theorem run_of_source_run (M : TM n) (oracle : BooleanOracle)
    (input bits : List Bool) {time : ℕ} {cfg : Cfg n M.Q}
    (hreach : M.reachesIn time (M.initCfg input) cfg)
    (hhalt : M.halted cfg) (hout : cfg.output.HasOutput bits) :
    ∃ final elapsed, elapsed ≤ 3 * time + 6 ∧
      (machine M).reachesIn oracle elapsed ((machine M).initCfg input) final ∧
      (machine M).halted final ∧ final.query.oracleQuery = bits ∧
      final.output.HasOutput [oracle bits] := by
  have hinvariants := TM.reachesIn_startInvariant hreach
    (Tape.StartInvariant.init_ofBool input) (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil
  have hsourceInv := hinvariants.2.2
  have hsourceHead : cfg.output.head ≤ time := by
    simpa using M.output_head_reachesIn_bound hreach
  have hlength : bits.length ≤ time := TM.output_length_le_of_reachesIn hreach hout
  let boundary := tailCfg M (liftCfg M time cfg) .rewind
    (TM.transitionTape cfg.output) TM.parkedBlank
  have hboundary : (machine M).step oracle (liftCfg M time cfg) = some boundary :=
    boundary_step M oracle time cfg hhalt
  have hcells : boundary.query.cells = cfg.output.cells :=
    TM.transitionTape_cells cfg.output hsourceInv.2
  have hinv : boundary.query.StartInvariant := by
    simpa only [Tape.StartInvariant, hcells] using hsourceInv
  have hhead : boundary.query.head ≤ time + 1 :=
    TM.head_transitionTape_le hsourceInv.1 hsourceHead
  obtain ⟨scanning, hrewind, hstate, hheadScan, hscanCells, hscanOut⟩ :=
    rewind_run M oracle boundary.query.head boundary rfl rfl hinv rfl
  have hscanOutput : scanning.query.HasOutput bits :=
    (Tape.hasOutput_congr (hscanCells.trans hcells) bits).mpr hout
  obtain ⟨final, hscan, hfinal, hquery, houtput⟩ :=
    scan_run M oracle bits scanning hstate hheadScan hscanOutput hscanOut
  have hlift : (machine M).reachesIn oracle time ((machine M).initCfg input)
      (liftCfg M time cfg) := by
    simpa using lift_run M oracle hreach 0
  have htail := reachesIn_trans (OracleTM.reachesIn.step hboundary hrewind) hscan
  refine ⟨final, time + (boundary.query.head + 2 + (bits.length + 3)), ?_, ?_,
    hfinal, hquery, houtput⟩
  · omega
  · exact reachesIn_trans hlift htail

/-- Ordinary input preparation, head normalization, and one query execute in
polynomial overhead over the preparation machine's time bound. -/
theorem run (M : TM n) {prepare : List Bool → List Bool} {T : ℕ → ℕ}
    (hprepare : M.ComputesInTime prepare T) (oracle : BooleanOracle)
    (input : List Bool) :
    ∃ final elapsed, elapsed ≤ 3 * T input.length + 6 ∧
      (machine M).reachesIn oracle elapsed ((machine M).initCfg input) final ∧
      (machine M).halted final ∧ final.query.oracleQuery = prepare input ∧
      final.output.HasOutput [oracle (prepare input)] := by
  obtain ⟨cfg, time, htime, hreach, hhalt, hout⟩ := hprepare input
  obtain ⟨final, elapsed, helapsed, hrun, hfinal, hquery, houtput⟩ :=
    run_of_source_run M oracle input (prepare input) hreach hhalt hout
  exact ⟨final, elapsed, by omega, hrun, hfinal, hquery, houtput⟩

/-- The compiled machine decides the preimage of the oracle's characteristic
language, including all query-construction and head-positioning costs. -/
theorem decidesInTime (M : TM n) {prepare : List Bool → List Bool} {T : ℕ → ℕ}
    (hprepare : M.ComputesInTime prepare T) (oracle : BooleanOracle) :
    (machine M).DecidesInTime oracle {input | oracle (prepare input) = true}
      (fun length => 3 * T length + 6) := by
  intro input
  obtain ⟨final, time, htime, hrun, hhalt, _, hout⟩ := run M hprepare oracle input
  refine ⟨final, time, htime, hrun, hhalt, ?_, ?_⟩
  · intro h
    change oracle (prepare input) = true at h
    simpa [h, Γ.ofBool] using hout.1 0 (by simp)
  · intro h
    have hf : oracle (prepare input) = false := by simpa using h
    simpa [hf, Γ.ofBool] using hout.1 0 (by simp)

end Preprocess

open Complexity

/-- Any FP preparation function can feed one actual Boolean-oracle lookup in
polynomial time. The oracle itself is unrestricted. -/
theorem oracle_preimage_mem_pWithOracle (oracle : BooleanOracle)
    {prepare : List Bool → List Bool} (hprepare : prepare ∈ FP) :
    {input | oracle (prepare input) = true} ∈ PWithOracle oracle := by
  obtain ⟨degree, tapes, machine, T, hcompute, htime⟩ := hprepare
  exact ⟨tapes, Preprocess.machine machine, fun length => 3 * T length + 6,
    Preprocess.decidesInTime machine hcompute oracle,
    ((PolyBound.const 3).mul (BigO.pow_polynomial_bound htime)).add
      (PolyBound.const 6)⟩

end Toda.Oracle

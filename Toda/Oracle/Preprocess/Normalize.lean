import Toda.Oracle.Preprocess.Defs

/-! # Costed query-head normalization and lookup -/

namespace Toda.Oracle.Preprocess

open Complexity

variable {n : ℕ}

/-- The non-query finishing phases idle every tape except the query cursor
and the final verdict cell. -/
def tailCfg (M : TM n) (cfg : OracleCfg n (machine M).Q)
    (phase : Phase) (query output : Tape) : OracleCfg n (machine M).Q where
  state := .inr phase
  input := TM.transitionInput cfg.input
  query := query
  work := fun i => TM.transitionTape (cfg.work i)
  output := output

theorem blank_parked_step :
    TM.parkedBlank.writeAndMove Γ.blank (TM.idleDir TM.parkedBlank.read) =
      TM.parkedBlank := by
  simp [TM.parkedBlank, TM.idleDir, Tape.read, Tape.init,
    Tape.writeAndMove, Tape.write, Tape.move]

theorem boundary_step (M : TM n) (oracle : BooleanOracle) (clock : ℕ)
    (cfg : Cfg n M.Q) (hhalt : cfg.state = M.qhalt) :
    (machine M).step oracle (liftCfg M clock cfg) =
      some (tailCfg M (liftCfg M clock cfg) .rewind
        (TM.transitionTape cfg.output) TM.parkedBlank) := by
  simp [OracleTM.step, machine, liftCfg, localTransition, hhalt,
    finishTransition, tailCfg, TM.transitionInput, TM.transitionTape,
    blankOutput_step]
  simp [blankOutput]

theorem rewind_run (M : TM n) (oracle : BooleanOracle) (height : ℕ) :
    ∀ (cfg : OracleCfg n (machine M).Q), cfg.state = .inr .rewind →
      cfg.query.head = height → cfg.query.StartInvariant →
      cfg.output = TM.parkedBlank →
      ∃ final, (machine M).reachesIn oracle (height + 1) cfg final ∧
        final.state = .inr .scan ∧ final.query.head = 1 ∧
        final.query.cells = cfg.query.cells ∧ final.output = TM.parkedBlank := by
  induction height with
  | zero =>
    intro cfg hs hh hi ho
    have hr : cfg.query.read = .start := by simp [Tape.read, hh, hi.1]
    let next := tailCfg M cfg .scan (cfg.query.move .right) TM.parkedBlank
    have hw : cfg.query.write Γ.blank = cfg.query := by simp [Tape.write, hh]
    have hstep : (machine M).step oracle cfg = some next := by
      simp [OracleTM.step, machine, localTransition, finishTransition, hs,
        hr, next, tailCfg, TM.transitionInput, TM.transitionTape,
        TM.readBackWrite, ho, blank_parked_step, Tape.writeAndMove, hw]
    exact ⟨next, .step hstep .zero, rfl, by simp [next, tailCfg, Tape.move, hh],
      rfl, rfl⟩
  | succ height ih =>
    intro cfg hs hh hi ho
    have hr : cfg.query.read ≠ .start := hi.read_ne_start (by omega)
    let query := cfg.query.writeAndMove (TM.readBackWrite cfg.query.read) .left
    let next := tailCfg M cfg .rewind query TM.parkedBlank
    have hstep : (machine M).step oracle cfg = some next := by
      simp [OracleTM.step, machine, localTransition, finishTransition, hs,
        hr, next, tailCfg, query, TM.transitionInput, TM.transitionTape,
        ho, blank_parked_step]
    have hcells : next.query.cells = cfg.query.cells :=
      TM.tape_readBackWrite_preserves cfg.query .left (Or.inr hr)
    have hhead : next.query.head = height := by
      simp [next, tailCfg, query, Tape.move, Tape.write_head, hh]
    have hinv : next.query.StartInvariant := by
      simpa only [Tape.StartInvariant, hcells] using hi
    obtain ⟨final, hrun, hstate, hhead', hcells', hout⟩ :=
      ih next rfl hhead hinv rfl
    exact ⟨final, .step hstep hrun, hstate, hhead', hcells'.trans hcells, hout⟩

theorem oracleQuery_eq_of_hasOutput {t : Tape} {bits : List Bool}
    (h : t.HasOutput bits) (hhead : t.head = bits.length + 1) :
    t.oracleQuery = bits := by
  apply List.ext_getElem
  · simp [hhead]
  · intro i hi hj
    simp only [Tape.oracleQuery, List.getElem_ofFn]
    rw [h.1 i hj]
    cases bits[i] <;> rfl

theorem query_and_write (M : TM n) (oracle : BooleanOracle) (bits : List Bool)
    (cfg : OracleCfg n (machine M).Q) (hs : cfg.state = .inr .query)
    (hquery : cfg.query.oracleQuery = bits) (hr : cfg.query.read = .blank)
    (ho : cfg.output = TM.parkedBlank) :
    ∃ final, (machine M).reachesIn oracle 2 cfg final ∧
      (machine M).halted final ∧ final.query.oracleQuery = bits ∧
      final.output.HasOutput [oracle bits] := by
  have hkeep := TM.transitionTape_eq_self (t := cfg.query) (by simp [hr])
  cases hb : oracle bits with
  | false =>
    let answered : OracleCfg n (machine M).Q := { cfg with state := .inr .no }
    let final := tailCfg M answered .halt (TM.transitionTape cfg.query)
      (TM.parkedBlank.writeAndMove Γ.zero .stay)
    refine ⟨final, .step (middle := answered) ?_ (.step ?_ .zero), rfl, ?_, ?_⟩
    · exact (machine M).step_query_false (yesState := .inr .yes)
        (by simp [hs, machine]) (by simp [hs, machine]) (by simpa [hquery] using hb)
    · simp [OracleTM.step, machine, localTransition, finishTransition,
        answered, final, tailCfg, TM.transitionInput, TM.transitionTape,
        ho, TM.parkedBlank, TM.idleDir, Tape.read, Tape.init, Tape.move]
      exact ⟨rfl, rfl, rfl⟩
    · simpa [final, tailCfg, hkeep] using hquery
    · simp [final, tailCfg, TM.parkedBlank, Tape.HasOutput,
        Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Γ.ofBool]
  | true =>
    let answered : OracleCfg n (machine M).Q := { cfg with state := .inr .yes }
    let final := tailCfg M answered .halt (TM.transitionTape cfg.query)
      (TM.parkedBlank.writeAndMove Γ.one .stay)
    refine ⟨final, .step (middle := answered) ?_ (.step ?_ .zero), rfl, ?_, ?_⟩
    · exact (machine M).step_query_true (noState := .inr .no)
        (by simp [hs, machine]) (by simp [hs, machine]) (by simpa [hquery] using hb)
    · simp [OracleTM.step, machine, localTransition, finishTransition,
        answered, final, tailCfg, TM.transitionInput, TM.transitionTape,
        ho, TM.parkedBlank, TM.idleDir, Tape.read, Tape.init, Tape.move]
      exact ⟨rfl, rfl, rfl⟩
    · simpa [final, tailCfg, hkeep] using hquery
    · simp [final, tailCfg, TM.parkedBlank, Tape.HasOutput,
        Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Γ.ofBool]

theorem scan_loop (M : TM n) (oracle : BooleanOracle) (bits : List Bool) :
    ∀ remaining position (cfg : OracleCfg n (machine M).Q),
      remaining = bits.length - position → position ≤ bits.length →
      cfg.state = .inr .scan → cfg.query.head = position + 1 →
      cfg.query.HasOutput bits → cfg.output = TM.parkedBlank →
      ∃ final, (machine M).reachesIn oracle (remaining + 3) cfg final ∧
        (machine M).halted final ∧ final.query.oracleQuery = bits ∧
        final.output.HasOutput [oracle bits] := by
  intro remaining
  induction remaining with
  | zero =>
    intro position cfg hr hp hs hh hq ho
    have heq : position = bits.length := by omega
    subst position
    have hread : cfg.query.read = .blank := by rw [Tape.read, hh]; exact hq.2
    have hkeep := TM.transitionTape_eq_self (t := cfg.query) (by simp [hread])
    let next := tailCfg M cfg .query (TM.transitionTape cfg.query) TM.parkedBlank
    have hstep : (machine M).step oracle cfg = some next := by
      simp [OracleTM.step, machine, localTransition, finishTransition, hs,
        hread, next, tailCfg, TM.transitionInput, TM.transitionTape,
        ho, blank_parked_step]
    have hquery := oracleQuery_eq_of_hasOutput hq hh
    obtain ⟨final, hrun, hhalt, hquery', hout⟩ :=
      query_and_write M oracle bits next rfl
        (by simpa [next, tailCfg, hkeep] using hquery)
        (by simpa [next, tailCfg, hkeep] using hread) rfl
    exact ⟨final, .step hstep hrun, hhalt, hquery', hout⟩
  | succ remaining ih =>
    intro position cfg hr hp hs hh hq ho
    have hpos : position < bits.length := by omega
    have hread : cfg.query.read = Γ.ofBool (bits[position]'hpos) := by
      rw [Tape.read, hh]
      exact hq.1 position hpos
    have hns : cfg.query.read ≠ .start := by rw [hread]; exact Γ.ofBool_ne_start _
    have hnb : cfg.query.read ≠ .blank := by rw [hread]; exact Γ.ofBool_ne_blank _
    let query := cfg.query.writeAndMove (TM.readBackWrite cfg.query.read) .right
    let next := tailCfg M cfg .scan query TM.parkedBlank
    have hstep : (machine M).step oracle cfg = some next := by
      simp [OracleTM.step, machine, localTransition, finishTransition, hs,
        hnb, next, tailCfg, query, TM.transitionInput, TM.transitionTape,
        ho, blank_parked_step]
    have hcells : next.query.cells = cfg.query.cells :=
      TM.tape_readBackWrite_preserves cfg.query .right (Or.inr hns)
    have hhead : next.query.head = (position + 1) + 1 := by
      simp [next, tailCfg, query, Tape.move, Tape.write_head, hh]
    have houtput : next.query.HasOutput bits :=
      (Tape.hasOutput_congr hcells bits).mpr hq
    obtain ⟨final, hrun, hhalt, hquery, hout⟩ :=
      ih (position + 1) next (by omega) (by omega) rfl hhead houtput rfl
    exact ⟨final, .step hstep hrun, hhalt, hquery, hout⟩

theorem scan_run (M : TM n) (oracle : BooleanOracle) (bits : List Bool)
    (cfg : OracleCfg n (machine M).Q) (hs : cfg.state = .inr .scan)
    (hh : cfg.query.head = 1) (hq : cfg.query.HasOutput bits)
    (ho : cfg.output = TM.parkedBlank) :
    ∃ final, (machine M).reachesIn oracle (bits.length + 3) cfg final ∧
      (machine M).halted final ∧ final.query.oracleQuery = bits ∧
      final.output.HasOutput [oracle bits] :=
  scan_loop M oracle bits bits.length 0 cfg (by simp) (by omega) hs hh hq ho

end Toda.Oracle.Preprocess

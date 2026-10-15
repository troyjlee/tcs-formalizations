import Complexitylib.Models.TuringMachine.Oracle
import Complexitylib.Models.TuringMachine.Tape.Encoding
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# A costed ordinary-input Boolean oracle lookup

The machine copies its whole ordinary input onto the dedicated query tape,
performs one lookup, and writes a normalized answer. Copying and positioning
are included in the exact runtime `input.length + 4`; no query string is
assumed to be preloaded.
-/

namespace Toda.Oracle

open Complexity

theorem oracleQuery_eq_of_hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : t.oracleQuery = bits := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i hi hj
    simp only [Tape.oracleQuery, List.getElem_ofFn]
    rw [h.2.1 i hj]
    cases bits[i] <;> rfl

namespace DirectQuery

inductive Phase where
  | boot | copying | query | yes | no | halt
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.boot, .copying, .query, .yes, .no, .halt}
  complete := by intro q; cases q <;> simp

private def transition (q : Phase) (inp query out : Γ) :
    OracleLocalTransition 0 Phase where
  nextState := match q with
    | .boot => .copying
    | .copying => if inp = .blank then .query else .copying
    | .yes | .no => .halt
    | .query => .query
    | .halt => .halt
  queryWrite := if q = .copying then TM.readBackWrite inp else TM.readBackWrite query
  workWrites := fun _ => .blank
  outputWrite := if q = .yes then .one else if q = .no then .zero
    else TM.readBackWrite out
  inputDir := if q = .boot ∨ (q = .copying ∧ inp ≠ .blank) then .right
    else TM.idleDir inp
  queryDir := if q = .boot ∨ (q = .copying ∧ inp ≠ .blank) then .right
    else TM.idleDir query
  workDirs := fun _ => .right
  outputDir := TM.idleDir out

/-- An actual deterministic oracle machine that asks its ordinary input. -/
def machine : OracleTM 0 where
  Q := Phase
  qstart := .boot
  qhalt := .halt
  queryTransition := fun q => if q = .query then some (.yes, .no) else none
  localTransition := fun q inp query _ out => transition q inp query out
  localTransition_right_of_start := by
    intro q inp query work out
    refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
    · intro h; subst inp; cases q <;> simp [transition, TM.idleDir]
    · intro h; subst query; cases q <;> simp [transition, TM.idleDir]
    · intro h; simp [transition, TM.idleDir, h]

private theorem finish (oracle : BooleanOracle) (bits : List Bool)
    (cfg : OracleCfg 0 machine.Q) (hstate : cfg.state = .copying)
    (hin : cfg.input.read = .blank) (hq : cfg.query.HasBinaryPrefix bits)
    (hout : cfg.output = (Tape.init []).move .right) :
    ∃ final, machine.reachesIn oracle 3 cfg final ∧ machine.halted final ∧
      final.query.oracleQuery = bits ∧ final.output.HasOutput [oracle bits] := by
  have hqr := hq.read_blank
  have hquery := oracleQuery_eq_of_hasBinaryPrefix hq
  have hqkeep : cfg.query.write Γ.blank = cfg.query := by
    simpa [TM.transitionTape, hqr, TM.readBackWrite, TM.idleDir, Tape.move] using
      TM.transitionTape_eq_self (t := cfg.query) (by simp [hqr])
  have hor : cfg.output.read = .blank := by simp [hout]
  have how : cfg.output.write Γ.blank = cfg.output := by
    simpa [TM.transitionTape, hor, TM.readBackWrite, TM.idleDir, Tape.move] using
      TM.transitionTape_eq_self (t := cfg.output) (by simp [hor])
  let asked : OracleCfg 0 machine.Q := { cfg with state := .query }
  have hstep : machine.step oracle cfg = some asked := by
    simp [OracleTM.step, machine, hstate, transition, hin, hqr, hor, asked,
      TM.readBackWrite, TM.idleDir, Tape.move, hqkeep, how]
    exact Subsingleton.elim _ _
  cases hb : oracle bits with
  | false =>
      let answered : OracleCfg 0 machine.Q := { asked with state := .no }
      let final : OracleCfg 0 machine.Q :=
        { answered with state := .halt, output := answered.output.writeAndMove Γ.zero .stay }
      refine ⟨final, .step hstep (.step (middle := answered) ?_ (.step ?_ .zero)), rfl, hquery, ?_⟩
      · exact machine.step_query_false (yesState := Phase.yes) (by simp [asked, machine])
          (by simp [machine, asked]) (by simpa [asked, hquery] using hb)
      · simp [OracleTM.step, machine, answered, asked, transition,
          hqr, hin, hor, TM.idleDir, TM.readBackWrite, final,
          Tape.move, hqkeep]
        exact Subsingleton.elim _ _
      · simp [final, answered, asked, hout, Tape.HasOutput,
          Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Γ.ofBool]
  | true =>
      let answered : OracleCfg 0 machine.Q := { asked with state := .yes }
      let final : OracleCfg 0 machine.Q :=
        { answered with state := .halt, output := answered.output.writeAndMove Γ.one .stay }
      refine ⟨final, .step hstep (.step (middle := answered) ?_ (.step ?_ .zero)), rfl, hquery, ?_⟩
      · exact machine.step_query_true (noState := Phase.no) (by simp [asked, machine])
          (by simp [machine, asked]) (by simpa [asked, hquery] using hb)
      · simp [OracleTM.step, machine, answered, asked, transition,
          hqr, hin, hor, TM.idleDir, TM.readBackWrite, final,
          Tape.move, hqkeep]
        exact Subsingleton.elim _ _
      · simp [final, answered, asked, hout, Tape.HasOutput,
          Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Γ.ofBool]

private theorem copy_loop (oracle : BooleanOracle) (remaining : List Bool) :
    ∀ (acc : List Bool) (cfg : OracleCfg 0 machine.Q),
      cfg.state = .copying → cfg.input.HasBinarySuffix remaining →
      cfg.query.HasBinaryPrefix acc →
      cfg.output = (Tape.init []).move .right →
      ∃ final, machine.reachesIn oracle (remaining.length + 3) cfg final ∧
        machine.halted final ∧ final.query.oracleQuery = acc ++ remaining ∧
        final.output.HasOutput [oracle (acc ++ remaining)] := by
  induction remaining with
  | nil =>
      intro acc cfg hstate hin hq hout
      simpa using finish oracle acc cfg hstate hin.read_nil hq hout
  | cons bit remaining ih =>
      intro acc cfg hstate hin hq hout
      have hir := hin.read_cons
      have hqr := hq.read_blank
      have hor : cfg.output.read = .blank := by simp [hout]
      have how : cfg.output.write Γ.blank = cfg.output := by
        simpa [TM.transitionTape, hor, TM.readBackWrite, TM.idleDir, Tape.move] using
          TM.transitionTape_eq_self (t := cfg.output) (by simp [hor])
      let next : OracleCfg 0 machine.Q :=
        { cfg with state := .copying, input := cfg.input.move .right, query := cfg.query.writeAndMove (Γ.ofBool bit) .right }
      have hstep : machine.step oracle cfg = some next := by
        cases bit <;>
          simp [OracleTM.step, machine, hstate, transition, hir, hor, Γ.ofBool,
            TM.readBackWrite, TM.idleDir, next, how, Tape.move] <;>
            exact Subsingleton.elim _ _
      obtain ⟨final, hrun, hhalt, hquery, houtput⟩ :=
        ih (acc ++ [bit]) next rfl hin.move_right_cons
          (Tape.hasBinaryPrefix_write_bit bit hq) hout
      refine ⟨final, ?_, hhalt, ?_, ?_⟩
      · simpa [Nat.add_assoc] using OracleTM.reachesIn.step hstep hrun
      · simpa [List.append_assoc] using hquery
      · simpa [List.append_assoc] using houtput

/-- Exact execution from the ordinary initial configuration, including input
copying, the one-step lookup, and writing the one-bit output. -/
theorem run (oracle : BooleanOracle) (input : List Bool) :
    ∃ final, machine.reachesIn oracle (input.length + 4)
        (machine.initCfg input) final ∧ machine.halted final ∧
      final.query.oracleQuery = input ∧ final.output.HasOutput [oracle input] := by
  let next : OracleCfg 0 machine.Q :=
    { state := .copying
      input := (Tape.init (input.map Γ.ofBool)).move .right
      query := (Tape.init []).move .right
      work := fun _ => (Tape.init []).move .right
      output := (Tape.init []).move .right }
  have hstep : machine.step oracle (machine.initCfg input) = some next := by
    simp [OracleTM.step, machine, transition, next, Tape.read, Tape.init,
      TM.readBackWrite, TM.idleDir, Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨final, hrun, hhalt, hquery, houtput⟩ :=
    copy_loop oracle input [] next rfl (Tape.init_move_right_hasBinarySuffix input)
      Tape.init_nil_move_right_hasBinaryPrefix_nil rfl
  refine ⟨final, ?_, hhalt, ?_, ?_⟩
  · simpa [Nat.add_assoc] using OracleTM.reachesIn.step hstep hrun
  · simpa using hquery
  · simpa using houtput

/-- Every Boolean oracle's characteristic language is decided by a fixed
ordinary-input machine in linear time. -/
theorem decidesInTime (oracle : BooleanOracle) :
    machine.DecidesInTime oracle {input | oracle input = true}
      (fun length => length + 4) := by
  intro input
  obtain ⟨final, hrun, hhalt, _, houtput⟩ := run oracle input
  refine ⟨final, input.length + 4, le_rfl, hrun, hhalt, ?_, ?_⟩
  · intro h
    change oracle input = true at h
    have hone := houtput.1 0 (by simp)
    simpa [h, Γ.ofBool] using hone
  · intro h
    have hone := houtput.1 0 (by simp)
    have hf : oracle input = false := by simpa using h
    simpa [hf, Γ.ofBool] using hone

end DirectQuery

end Toda.Oracle

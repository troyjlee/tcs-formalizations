/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineConfiguration
import IPPSPACE.QBF.MachineWindow

/-!
# The finite configuration graph of the actual upstream machine

Reconstruct the source configuration, perform the actual `TM.step`, and reject
moves outside the prescribed head bounds before re-encoding. This is executable
on the finite upstream `Code` product. Its reachability and accepting states
agree exactly with actual machine execution under the all-reachable space bound.
No polynomial-size Boolean formula for the complete transition table, machine
runtime bound, or complexity-class inclusion is assumed here.
-/

namespace IPPSPACE

open Complexity

/-- Head-space checking is a finite, executable predicate. -/
def machineSpaceDecidable {Q : Type} {tapes : ℕ} (c : Cfg tapes Q)
    (inputLength space : ℕ) : Decidable (c.WithinDecisionSpace inputLength space) := by
  unfold Cfg.WithinDecisionSpace Cfg.WithinAuxSpace
  infer_instance

/-- A real machine step on finite codes, rejecting exits rather than clamping
the moved head back into the window. -/
def machineCodeStep {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (code : Code tm.Q tapes input.length space) : Option (Code tm.Q tapes input.length space) :=
  match tm.step (machineConfigurationOfCode input space code) with
  | none => none
  | some next =>
    letI := machineSpaceDecidable next input.length space
    if next.WithinDecisionSpace input.length space then some (cfgCode input.length space next)
    else none

/-- No transition information is lost on the finite representation. -/
theorem machineCodeStep_eq_some_iff {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (source target : Code tm.Q tapes input.length space) :
    machineCodeStep tm input space source = some target ↔
      tm.step (machineConfigurationOfCode input space source) =
        some (machineConfigurationOfCode input space target) := by
  constructor
  · intro h
    cases hs : tm.step (machineConfigurationOfCode input space source) with
    | none => simp [machineCodeStep, hs] at h
    | some next =>
      by_cases hb : next.WithinDecisionSpace input.length space
      · have heq : cfgCode input.length space next = target := by
          simpa [machineCodeStep, hs, hb] using h
        have hw := windowed_machine_step (windowed_machineConfigurationOfCode input space source)
          hs (withinDecisionSpace_machineConfigurationOfCode input space source)
        have hnext : machineConfigurationOfCode input space target = next := by
          rw [← heq]
          exact machineConfigurationOfCode_cfgCode input space next hw hb
        rw [hnext]
      · simp [machineCodeStep, hs, hb] at h
  · intro h
    simp [machineCodeStep, h, withinDecisionSpace_machineConfigurationOfCode]

/-- Edges of the finite graph are successful executions of the actual step. -/
def machineCodeEdge {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (source target : Code tm.Q tapes input.length space) : Prop :=
  machineCodeStep tm input space source = some target

/-- The finite graph stores the actual halt state and verdict cell. -/
def machineCodeAccepts {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (code : Code tm.Q tapes input.length space) : Prop :=
  tm.halted (machineConfigurationOfCode input space code) ∧
    (machineConfigurationOfCode input space code).output.cells 1 = Γ.one

/-- Every graph path reconstructs an actual machine path. -/
theorem machineCode_reachable_sound {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (source target : Code tm.Q tapes input.length space)
    (h : Relation.ReflTransGen (machineCodeEdge tm input space) source target) :
    tm.reaches (machineConfigurationOfCode input space source)
      (machineConfigurationOfCode input space target) :=
  Relation.ReflTransGen.lift (machineConfigurationOfCode input space)
    (fun a b hab => (machineCodeStep_eq_some_iff tm input space a b).mp hab) source target h

/-- All actual paths from the initial configuration occur in the finite graph,
provided the prescribed space bound holds along those paths. -/
theorem machineCode_reachable_complete {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (hspace : ∀ c, tm.reaches (tm.initCfg input) c → c.WithinDecisionSpace input.length space)
    (target : Cfg tapes tm.Q) (h : tm.reaches (tm.initCfg input) target) :
    Relation.ReflTransGen (machineCodeEdge tm input space)
      (cfgCode input.length space (tm.initCfg input)) (cfgCode input.length space target) := by
  induction h with
  | refl => exact .refl
  | @tail previous target hprefix hstep ih =>
    apply ih.tail
    apply (machineCodeStep_eq_some_iff tm input space _ _).mpr
    rw [machineConfigurationOfCode_cfgCode input space previous
      (windowed_of_machine_reaches tm input space hspace previous hprefix) (hspace previous hprefix),
      machineConfigurationOfCode_cfgCode input space target
        (windowed_of_machine_reaches tm input space hspace target (hprefix.tail hstep))
        (hspace target (hprefix.tail hstep))]
    exact hstep

/-- The initial code reconstructs the actual starting configuration. -/
theorem machineConfigurationOfCode_initial {tapes : ℕ} (tm : TM tapes)
    (input : List Bool) (space : ℕ) :
    machineConfigurationOfCode input space (cfgCode input.length space (tm.initCfg input)) =
      tm.initCfg input := by
  apply machineConfigurationOfCode_cfgCode input space _ (windowed_init _ _ _)
  simp [Cfg.WithinDecisionSpace, Cfg.WithinAuxSpace, Tape.init]

/-- Exact accepting reachability in the finite graph, with neither a bounded-time
assumption nor a hypothesis of correctness of an unconstructed Boolean formula. -/
theorem machineCode_accepts_iff {tapes : ℕ} (tm : TM tapes) (input : List Bool) (space : ℕ)
    (hspace : ∀ c, tm.reaches (tm.initCfg input) c → c.WithinDecisionSpace input.length space) :
    (∃ target, machineCodeAccepts tm input space target ∧
      Relation.ReflTransGen (machineCodeEdge tm input space)
        (cfgCode input.length space (tm.initCfg input)) target) ↔ tm.Accepts input := by
  constructor
  · rintro ⟨target, haccept, hreach⟩
    have hactual := machineCode_reachable_sound tm input space _ target hreach
    rw [machineConfigurationOfCode_initial] at hactual
    exact ⟨machineConfigurationOfCode input space target, hactual, haccept⟩
  · rintro ⟨target, hreach, hhalt, houtput⟩
    refine ⟨cfgCode input.length space target, ?_,
      machineCode_reachable_complete tm input space hspace target hreach⟩
    unfold machineCodeAccepts
    rw [machineConfigurationOfCode_cfgCode input space target
      (windowed_of_machine_reaches tm input space hspace target hreach) (hspace target hreach)]
    exact ⟨hhalt, houtput⟩

/-- The actual upstream space-decider specification supplies exact language
membership through the executable finite configuration graph. -/
theorem machine_decider_codeGraph_iff {tapes : ℕ} {tm : TM tapes}
    {language : Language} {space : ℕ → ℕ} (hdec : tm.DecidesInSpace language space)
    (input : List Bool) :
    (∃ target, machineCodeAccepts tm input (space input.length) target ∧
      Relation.ReflTransGen (machineCodeEdge tm input (space input.length))
        (cfgCode input.length (space input.length) (tm.initCfg input)) target) ↔ input ∈ language :=
  (machineCode_accepts_iff tm input _ (hdec.1 input)).trans (machine_decider_accepts_iff hdec input)

end IPPSPACE

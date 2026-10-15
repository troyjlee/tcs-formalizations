import Toda.Oracle.Batch
import Complexitylib.Models.TuringMachine.Lift
import Mathlib.Data.Fintype.Option

/-! # Ordinary preparation followed by a batch oracle computation -/

namespace Toda.Oracle.PrepareBatch

open Complexity

variable {n : ℕ}

abbrev State (M : TM n) := M.retargetOutput.Q ⊕ Option Batch.Phase

def idleTransition (M : TM n) (state : State M) (inp query : Γ)
    (work : Fin (n + 1) → Γ) (out : Γ) : OracleLocalTransition (n + 1) (State M) where
  nextState := state
  queryWrite := TM.readBackWrite query
  workWrites := fun i => TM.readBackWrite (work i)
  outputWrite := .blank
  inputDir := TM.idleDir inp
  queryDir := TM.idleDir query
  workDirs := fun i => TM.idleDir (work i)
  outputDir := TM.idleDir out

def localTransition (M : TM n) (state : State M) (inp query : Γ)
    (work : Fin (n + 1) → Γ) (out : Γ) : OracleLocalTransition (n + 1) (State M) :=
  match state with
  | .inl q =>
    if q = M.retargetOutput.qhalt then idleTransition M (.inr none) inp query work out else
      let (next, writes, output, inputDir, workDirs, outputDir) :=
        M.retargetOutput.δ q inp work query
      { nextState := .inl next
        queryWrite := output
        workWrites := writes
        outputWrite := .blank
        inputDir := inputDir
        queryDir := outputDir
        workDirs := workDirs
        outputDir := TM.idleDir out }
  | .inr none =>
    { idleTransition M (.inr none) inp query work out with
      nextState := if work (Fin.last n) = .start then .inr (some .tag) else .inr none
      workDirs := fun i => if i = Fin.last n then
        (if work i = .start then .right else .left) else TM.idleDir (work i) }
  | .inr (some phase) =>
    let t := Batch.transition phase (work (Fin.last n)) query out
    { nextState := .inr (some t.nextState)
      queryWrite := t.queryWrite
      workWrites := fun i => TM.readBackWrite (work i)
      outputWrite := t.outputWrite
      inputDir := TM.idleDir inp
      queryDir := t.queryDir
      workDirs := fun i => if i = Fin.last n then t.inputDir else TM.idleDir (work i)
      outputDir := t.outputDir }

/-- The source output is a fresh work tape; the dedicated query tape stays
available for the subsequent batch computation. -/
def machine (M : TM n) : OracleTM (n + 1) where
  Q := State M
  qstart := .inl M.retargetOutput.qstart
  qhalt := .inr (some .halt)
  queryTransition := fun state => match state with
    | .inr (some .query) => some (.inr (some .yes), .inr (some .no))
    | _ => none
  localTransition := localTransition M
  localTransition_right_of_start := by
    intro state inp query work out
    have hidle : ∀ q, let t := idleTransition M q inp query work out
        (inp = Γ.start → t.inputDir = .right) ∧
        (query = Γ.start → t.queryDir = .right) ∧
        (∀ i, work i = Γ.start → t.workDirs i = .right) ∧
        (out = Γ.start → t.outputDir = .right) := by
      intro q
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; simp [idleTransition, TM.idleDir, h]
      · intro h; simp [idleTransition, TM.idleDir, h]
      · intro i h; simp [idleTransition, TM.idleDir, h]
      · intro h; simp [idleTransition, TM.idleDir, h]
    cases state with
    | inl q =>
      by_cases hq : q = M.retargetOutput.qhalt
      · simpa only [localTransition, hq, ↓reduceIte] using hidle (.inr none)
      · have hsource := M.retargetOutput.δ_right_of_start q inp work query
        generalize ht : M.retargetOutput.δ q inp work query = t at hsource
        obtain ⟨next, writes, output, inputDir, workDirs, outputDir⟩ := t
        simp only at hsource
        simp only [localTransition, hq, ↓reduceIte, ht]
        exact ⟨hsource.1, hsource.2.2, hsource.2.1,
          fun h => by simp [TM.idleDir, h]⟩
    | inr phase =>
      cases phase with
      | none =>
        refine ⟨(hidle (.inr none)).1, (hidle (.inr none)).2.1, ?_, (hidle (.inr none)).2.2.2⟩
        intro i h
        simp [localTransition, idleTransition, h, TM.idleDir]
      | some phase =>
        have hbatch := Batch.machine.localTransition_right_of_start
          phase (work (Fin.last n)) query (fun _ => .blank) out
        refine ⟨fun h => by simp [localTransition, TM.idleDir, h],
          hbatch.2.1, ?_, hbatch.2.2.2⟩
        intro i h
        by_cases heq : i = Fin.last n
        · subst i
          simpa only [localTransition, ↓reduceIte, Batch.machine] using hbatch.1 h
        · simp [localTransition, heq, TM.idleDir, h]

def liftCfg (M : TM n) (clock : ℕ) (cfg : Cfg (n + 1) M.retargetOutput.Q) :
    OracleCfg (n + 1) (machine M).Q where
  state := .inl cfg.state
  input := cfg.input
  query := cfg.output
  work := cfg.work
  output := Preprocess.blankOutput clock

@[simp] theorem liftCfg_init (M : TM n) (input : List Bool) :
    liftCfg M 0 (M.retargetOutput.initCfg input) = (machine M).initCfg input := rfl

theorem lift_step (M : TM n) (oracle : BooleanOracle) (clock : ℕ)
    {cfg next : Cfg (n + 1) M.retargetOutput.Q} (hstep : M.retargetOutput.step cfg = some next) :
    (machine M).step oracle (liftCfg M clock cfg) =
      some (liftCfg M (clock + 1) next) := by
  have hhalt : cfg.state ≠ M.retargetOutput.qhalt := by
    intro h
    simp [TM.step, TM.retargetOutput, h] at hstep
  simp only [TM.step, hhalt, ↓reduceIte, Option.some.injEq] at hstep
  rw [← hstep]
  generalize ht : M.retargetOutput.δ cfg.state cfg.input.read
    (fun i => (cfg.work i).read) cfg.output.read = t
  obtain ⟨next, writes, output, inputDir, workDirs, outputDir⟩ := t
  simp [OracleTM.step, machine, liftCfg, localTransition, hhalt, ht,
    Preprocess.blankOutput_step]

theorem lift_run (M : TM n) (oracle : BooleanOracle)
    {time : ℕ} {cfg final : Cfg (n + 1) M.retargetOutput.Q}
    (hreach : M.retargetOutput.reachesIn time cfg final) (clock : ℕ) :
    (machine M).reachesIn oracle time (liftCfg M clock cfg)
      (liftCfg M (clock + time) final) := by
  induction hreach generalizing clock with
  | zero => simpa using OracleTM.reachesIn.zero (machine := machine M)
  | step hone _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      OracleTM.reachesIn.step (lift_step M oracle clock hone) (ih (clock + 1))

end Toda.Oracle.PrepareBatch

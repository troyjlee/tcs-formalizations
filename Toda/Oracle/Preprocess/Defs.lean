import Toda.Oracle.Machine
import Complexitylib.Models.TuringMachine.Frame
import Complexitylib.Models.TuringMachine.OutputBounds

/-! # Compiling an ordinary query-preparation machine into an oracle machine -/

namespace Toda.Oracle.Preprocess

open Complexity

inductive Phase where
  | rewind | scan | query | yes | no | halt
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.rewind, .scan, .query, .yes, .no, .halt}
  complete := by intro q; cases q <;> simp

variable {n : ℕ}

def finishTransition (M : TM n) (phase : Phase) (inp query : Γ)
    (work : Fin n → Γ) (out : Γ) : OracleLocalTransition n (M.Q ⊕ Phase) where
  nextState := .inr (match phase with
    | .rewind => if query = .start then .scan else .rewind
    | .scan => if query = .blank then .query else .scan
    | .query => .query
    | .yes | .no | .halt => .halt)
  queryWrite := TM.readBackWrite query
  workWrites := fun i => TM.readBackWrite (work i)
  outputWrite := if phase = .yes then .one else if phase = .no then .zero else .blank
  inputDir := TM.idleDir inp
  queryDir := match phase with
    | .rewind => if query = .start then .right else .left
    | .scan => if query = .blank then TM.idleDir query else .right
    | _ => TM.idleDir query
  workDirs := fun i => TM.idleDir (work i)
  outputDir := TM.idleDir out

def localTransition (M : TM n) (state : M.Q ⊕ Phase) (inp query : Γ)
    (work : Fin n → Γ) (out : Γ) : OracleLocalTransition n (M.Q ⊕ Phase) :=
  match state with
  | .inl q =>
    if q = M.qhalt then
      { finishTransition M .query inp query work out with nextState := .inr .rewind }
    else
      let (next, writes, output, inputDir, workDirs, outputDir) := M.δ q inp work query
      { nextState := .inl next
        queryWrite := output
        workWrites := writes
        outputWrite := .blank
        inputDir := inputDir
        queryDir := outputDir
        workDirs := workDirs
        outputDir := TM.idleDir out }
  | .inr phase => finishTransition M phase inp query work out

/-- Simulate the source output on the dedicated query tape, normalize its
head by rewinding and scanning, perform one lookup, and write its answer. -/
def machine (M : TM n) : OracleTM n where
  Q := M.Q ⊕ Phase
  qstart := .inl M.qstart
  qhalt := .inr .halt
  queryTransition := fun state => match state with
    | .inr .query => some (.inr .yes, .inr .no)
    | _ => none
  localTransition := localTransition M
  localTransition_right_of_start := by
    intro state inp query work out
    have hfinish : ∀ p, let t := finishTransition M p inp query work out
        (inp = Γ.start → t.inputDir = .right) ∧
        (query = Γ.start → t.queryDir = .right) ∧
        (∀ i, work i = Γ.start → t.workDirs i = .right) ∧
        (out = Γ.start → t.outputDir = .right) := by
      intro p
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; simp [finishTransition, TM.idleDir, h]
      · intro h; cases p <;> simp [finishTransition, TM.idleDir, h]
      · intro i h; simp [finishTransition, TM.idleDir, h]
      · intro h; simp [finishTransition, TM.idleDir, h]
    cases state with
    | inr phase => exact hfinish phase
    | inl q =>
      by_cases hq : q = M.qhalt
      · simpa only [localTransition, hq, ↓reduceIte] using hfinish .query
      · have hsource := M.δ_right_of_start q inp work query
        generalize ht : M.δ q inp work query = t at hsource
        obtain ⟨next, writes, output, inputDir, workDirs, outputDir⟩ := t
        simp only at hsource
        simp only [localTransition, hq, ↓reduceIte, ht]
        exact ⟨hsource.1, hsource.2.2, hsource.2.1,
          fun h => by simp [TM.idleDir, h]⟩

/-- The verdict tape stays blank while source transitions execute. -/
def blankOutput (clock : ℕ) : Tape :=
  if clock = 0 then Tape.init [] else TM.parkedBlank

theorem blankOutput_step (clock : ℕ) :
    (blankOutput clock).writeAndMove Γ.blank (TM.idleDir (blankOutput clock).read) =
      blankOutput (clock + 1) := by
  cases clock <;> simp [blankOutput, TM.parkedBlank, TM.idleDir,
    Tape.writeAndMove, Tape.write, Tape.move, Tape.read, Tape.init]

/-- Source configurations map their output to the query tape. The extra
clock only describes the blank verdict tape before and after its first step. -/
def liftCfg (M : TM n) (clock : ℕ) (cfg : Cfg n M.Q) :
    OracleCfg n (machine M).Q where
  state := .inl cfg.state
  input := cfg.input
  query := cfg.output
  work := cfg.work
  output := blankOutput clock

@[simp] theorem liftCfg_init (M : TM n) (input : List Bool) :
    liftCfg M 0 (M.initCfg input) = (machine M).initCfg input := rfl

theorem lift_step (M : TM n) (oracle : BooleanOracle) (clock : ℕ)
    {cfg next : Cfg n M.Q} (hstep : M.step cfg = some next) :
    (machine M).step oracle (liftCfg M clock cfg) =
      some (liftCfg M (clock + 1) next) := by
  have hhalt : cfg.state ≠ M.qhalt := by
    intro h
    simp [TM.step, h] at hstep
  simp only [TM.step, hhalt, ↓reduceIte, Option.some.injEq] at hstep
  rw [← hstep]
  generalize ht : M.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
    cfg.output.read = t
  obtain ⟨next, writes, output, inputDir, workDirs, outputDir⟩ := t
  simp [OracleTM.step, machine, liftCfg, localTransition, hhalt, ht,
    blankOutput_step]

theorem lift_run (M : TM n) (oracle : BooleanOracle)
    {time : ℕ} {cfg final : Cfg n M.Q} (hreach : M.reachesIn time cfg final)
    (clock : ℕ) :
    (machine M).reachesIn oracle time (liftCfg M clock cfg)
      (liftCfg M (clock + time) final) := by
  induction hreach generalizing clock with
  | zero => simpa using OracleTM.reachesIn.zero (machine := machine M)
  | step hone _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      OracleTM.reachesIn.step (lift_step M oracle clock hone) (ih (clock + 1))

theorem reachesIn_trans {M : OracleTM n} {oracle : BooleanOracle}
    {first second : ℕ} {start middle final : OracleCfg n M.Q}
    (hfirst : M.reachesIn oracle first start middle)
    (hsecond : M.reachesIn oracle second middle final) :
    M.reachesIn oracle (first + second) start final := by
  induction hfirst with
  | zero => simpa using hsecond
  | step hone _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      OracleTM.reachesIn.step hone (ih hsecond)

end Toda.Oracle.Preprocess

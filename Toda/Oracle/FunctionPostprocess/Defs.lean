import Toda.Oracle.Postprocess
import Toda.Oracle.FunctionModel.Frame
import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute

/-! # Fresh-bank ordinary postprocessing of an oracle computation -/

namespace Toda.Oracle.FunctionPostprocess

open Complexity

variable {n k : ℕ}

abbrev State (M : FunctionTM n) (N : TM k) := M.Q ⊕ Option (TM.retargetInputStarted N).Q

def left (work : Fin (n + (k + 1)) → Γ) : Fin n → Γ :=
  fun i => work (Fin.castAdd (k + 1) i)

def right (work : Fin (n + (k + 1)) → Γ) : Fin (k + 1) → Γ :=
  fun i => work (Fin.natAdd n i)

def idle (M : FunctionTM n) (N : TM k) (state : State M N)
    (inp query answer : Γ) (work : Fin (n + (k + 1)) → Γ) (out : Γ) :
    FunctionLocalTransition (n + (k + 1)) (State M N) where
  nextState := state
  queryWrite := TM.readBackWrite query
  answerWrite := TM.readBackWrite answer
  workWrites := fun i => TM.readBackWrite (work i)
  outputWrite := .blank
  inputDir := TM.idleDir inp
  queryDir := TM.idleDir query
  answerDir := TM.idleDir answer
  workDirs := fun i => TM.idleDir (work i)
  outputDir := TM.idleDir out

def localTransition (M : FunctionTM n) (N : TM k) (state : State M N)
    (inp query answer : Γ) (work : Fin (n + (k + 1)) → Γ) (out : Γ) :
    FunctionLocalTransition (n + (k + 1)) (State M N) :=
  match state with
  | .inl q =>
    if q = M.qhalt then idle M N (.inr none) inp query answer work out else
    let t := M.localTransition q inp query answer (left work) (right work (Fin.last k))
    { nextState := .inl t.nextState
      queryWrite := t.queryWrite
      answerWrite := t.answerWrite
      workWrites := Fin.append t.workWrites
        (Fin.snoc (fun i => TM.readBackWrite (right work i.castSucc)) t.outputWrite)
      outputWrite := .blank
      inputDir := t.inputDir
      queryDir := t.queryDir
      answerDir := t.answerDir
      workDirs := Fin.append t.workDirs
        (Fin.snoc (fun i => TM.idleDir (right work i.castSucc)) t.outputDir)
      outputDir := TM.idleDir out }
  | .inr none =>
    { idle M N (.inr none) inp query answer work out with
      nextState := if right work (Fin.last k) = .start then
        .inr (some (TM.retargetInputStarted N).qstart) else .inr none
      workDirs := Fin.append (fun i => TM.idleDir (left work i))
        (Fin.snoc (fun i => TM.idleDir (right work i.castSucc))
          (if right work (Fin.last k) = .start then .right else .left)) }
  | .inr (some q) =>
    let (next, writes, output, inputDir, workDirs, outputDir) :=
      (TM.retargetInputStarted N).δ q inp (right work) out
    { nextState := .inr (some next)
      queryWrite := TM.readBackWrite query
      answerWrite := TM.readBackWrite answer
      workWrites := Fin.append (fun i => TM.readBackWrite (left work i)) writes
      outputWrite := output
      inputDir := inputDir
      queryDir := TM.idleDir query
      answerDir := TM.idleDir answer
      workDirs := Fin.append (fun i => TM.idleDir (left work i)) workDirs
      outputDir := outputDir }

def machine (M : FunctionTM n) (N : TM k) : FunctionTM (n + (k + 1)) where
  Q := State M N
  qstart := .inl M.qstart
  qhalt := .inr (some (TM.retargetInputStarted N).qhalt)
  queryTransition := fun state => match state with
    | .inl q => if q = M.qhalt then none else
        (M.queryTransition q).map Sum.inl
    | _ => none
  localTransition := localTransition M N
  localTransition_right_of_start := by
    intro state inp query answer work out
    cases state with
    | inl q =>
      by_cases hq : q = M.qhalt
      · simp [localTransition, hq, idle, TM.idleDir]
      · have h := M.localTransition_right_of_start q inp query answer (left work)
          (right work (Fin.last k))
        simp only [localTransition, hq, ↓reduceIte]
        refine ⟨h.1, h.2.1, h.2.2.1, ?_, fun ho => by simp [TM.idleDir, ho]⟩
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left, left] using h.2.2.2.1 j
        · refine Fin.lastCases ?_ (fun j' => ?_) j
          · simpa only [Fin.append_right, Fin.snoc_last, right] using h.2.2.2.2
          · simp only [Fin.append_right, Fin.snoc_castSucc, right, TM.idleDir]
            intro hj; simp [hj]
    | inr phase =>
      cases phase with
      | none =>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [localTransition, idle, TM.idleDir]
        · simp [localTransition, idle, TM.idleDir]
        · simp [localTransition, idle, TM.idleDir]
        · intro i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · simp only [localTransition, Fin.append_left, left, TM.idleDir]
            intro hj; simp [hj]
          · refine Fin.lastCases ?_ (fun j' => ?_) j <;>
              simp only [localTransition, Fin.append_right, Fin.snoc_last, Fin.snoc_castSucc, right, TM.idleDir] <;>
              (intro hj; try simp only [Fin.natAdd_last] at hj
               simp [hj])
        · simp [localTransition, idle, TM.idleDir]
      | some q =>
        have h := (TM.retargetInputStarted N).δ_right_of_start q inp (right work) out
        generalize ht : (TM.retargetInputStarted N).δ q inp (right work) out = t at h
        obtain ⟨next, writes, output, inputDir, workDirs, outputDir⟩ := t
        simp only at h
        simp only [localTransition, ht]
        refine ⟨h.1, fun hq => by simp [TM.idleDir, hq],
          fun ha => by simp [TM.idleDir, ha], ?_, h.2.2⟩
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, left, TM.idleDir]
          intro hj; simp [hj]
        · simpa only [Fin.append_right, right] using h.2.1 j

abbrev fresh := Postprocess.fresh

def sourceCfg (M : FunctionTM n) (N : TM k) (cfg : FunctionCfg n M.Q) (parked : Bool) :
    FunctionCfg (n + (k + 1)) (machine M N).Q where
  state := .inl cfg.state
  input := cfg.input
  query := cfg.query
  answer := cfg.answer
  work := Fin.append cfg.work (Fin.snoc (fun _ => fresh parked) cfg.output)
  output := fresh parked

def postCfg (M : FunctionTM n) (N : TM k) (query answer : Tape) (scratch : Fin n → Tape)
    (cfg : Cfg (k + 1) (TM.retargetInputStarted N).Q) :
    FunctionCfg (n + (k + 1)) (machine M N).Q where
  state := .inr (some cfg.state)
  input := cfg.input
  query := query
  answer := answer
  work := Fin.append scratch cfg.work
  output := cfg.output

end Toda.Oracle.FunctionPostprocess

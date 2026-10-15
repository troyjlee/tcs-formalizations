import Toda.Oracle.FunctionPostprocess.Simulate

namespace Toda.Oracle.FunctionPostprocess

open Complexity
open Postprocess (fresh_step fresh_readBack)

variable {n k : ℕ}

def entry (N : TM k) (realInput stream : Tape) : Cfg (k + 1) (TM.retargetInputStarted N).Q where
  state := (TM.retargetInputStarted N).qstart
  input := realInput
  work := Fin.snoc (fun _ => TM.parkedBlank) stream
  output := TM.parkedBlank

def rewindCfg (M : FunctionTM n) (N : TM k) (realInput query answer : Tape)
    (scratch : Fin n → Tape) (stream : Tape) : FunctionCfg (n + (k + 1)) (machine M N).Q :=
  { postCfg M N query answer scratch (entry N realInput stream) with state := .inr none }

theorem rewind_step (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    (realInput query answer : Tape) (scratch : Fin n → Tape) (stream : Tape)
    (hin : realInput.read ≠ .start) (hq : query.read ≠ .start) (ha : answer.read ≠ .start)
    (hw : ∀ i, (scratch i).read ≠ .start) :
    (machine M N).step oracle (rewindCfg M N realInput query answer scratch stream) =
      some (if stream.read = .start then
        postCfg M N query answer scratch (entry N realInput
          (stream.writeAndMove (TM.readBackWrite stream.read) .right))
      else rewindCfg M N realInput query answer scratch
          (stream.writeAndMove (TM.readBackWrite stream.read) .left)) := by
  have hquery : query.writeAndMove (TM.readBackWrite query.read) (TM.idleDir query.read) = query :=
    TM.transitionTape_eq_self hq
  have hanswer : answer.writeAndMove (TM.readBackWrite answer.read) (TM.idleDir answer.read) = answer :=
    TM.transitionTape_eq_self ha
  have hscratch : (fun i => (scratch i).writeAndMove (TM.readBackWrite (scratch i).read)
      (TM.idleDir (scratch i).read)) = scratch := by
    funext i; exact TM.transitionTape_eq_self (hw i)
  by_cases hs : stream.read = .start <;>
    simp only [FunctionTM.step, machine, rewindCfg, postCfg, entry,
      ↓reduceIte, localTransition, idle, left, right, Fin.append_left, Fin.append_right,
      Fin.snoc_last, Fin.snoc_castSucc, hs, ↓reduceIte, hquery, hanswer]
  all_goals
    have hi : realInput.move (TM.idleDir realInput.read) = realInput := by
      simp [TM.idleDir, hin, Tape.move]
    rw [hi]
    apply congrArg some
    congr 1
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact TM.transitionTape_eq_self (hw j)
      · simp only [Fin.append_right]
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · simp only [Fin.snoc_last, hs]
        · simp only [Fin.snoc_castSucc]
          exact TM.transitionTape_eq_self (t := TM.parkedBlank) (by decide)
    · exact fresh_step true

theorem rewind_run (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    (realInput query answer : Tape) (scratch : Fin n → Tape)
    (hin : realInput.read ≠ .start) (hq : query.read ≠ .start) (ha : answer.read ≠ .start)
    (hw : ∀ i, (scratch i).read ≠ .start) (height : ℕ) :
    ∀ stream, stream.head = height → stream.StartInvariant →
      ∃ finalStream, (machine M N).reachesIn oracle (height + 1)
          (rewindCfg M N realInput query answer scratch stream)
          (postCfg M N query answer scratch (entry N realInput finalStream)) ∧
        finalStream.head = 1 ∧ finalStream.cells = stream.cells := by
  induction height with
  | zero =>
    intro stream hh hi
    have hr : stream.read = .start := by simp [Tape.read, hh, hi.1]
    have hstep := rewind_step M N oracle realInput query answer scratch stream hin hq ha hw
    simp only [hr, ↓reduceIte] at hstep
    refine ⟨stream.writeAndMove (TM.readBackWrite Γ.start) .right, .step hstep .zero, ?_, ?_⟩
    · simp [Tape.move, Tape.write_head, hh]
    · simpa only [hr] using TM.tape_readBackWrite_preserves stream .right (Or.inl hh)
  | succ height ih =>
    intro stream hh hi
    have hr := hi.read_ne_start (by omega : 1 ≤ stream.head)
    let next := stream.writeAndMove (TM.readBackWrite stream.read) .left
    have hnext : next.head = height := by simp [next, Tape.move, Tape.write_head, hh]
    obtain ⟨finalStream, hrun, hhead, hcells⟩ :=
      ih next hnext (hi.writeAndMove _ _)
    have hstep := rewind_step M N oracle realInput query answer scratch stream hin hq ha hw
    simp only [hr, ↓reduceIte] at hstep
    exact ⟨finalStream, .step hstep hrun, hhead,
      hcells.trans (TM.tape_readBackWrite_preserves stream .left (Or.inr hr))⟩

theorem boundary_step (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    (cfg : FunctionCfg n M.Q) (parked : Bool) (hhalt : cfg.state = M.qhalt)
    (hr : cfg.output.read = .blank) :
    (machine M N).step oracle (sourceCfg M N cfg parked) = some
      (rewindCfg M N (TM.transitionInput cfg.input) (TM.transitionTape cfg.query) (TM.transitionTape cfg.answer)
        (fun i => TM.transitionTape (cfg.work i)) cfg.output) := by
  have hout := TM.transitionTape_eq_self (t := cfg.output) (by simp [hr])
  simp only [FunctionTM.step, machine, sourceCfg, reduceCtorEq, ↓reduceIte, hhalt,
    localTransition, idle, rewindCfg, postCfg, entry]
  change some ({ state := Sum.inr none, input := TM.transitionInput cfg.input, query := TM.transitionTape cfg.query, answer := TM.transitionTape cfg.answer, work := fun i => TM.transitionTape (Fin.append cfg.work (Fin.snoc (fun _ => fresh parked) cfg.output) i), output := (fresh parked).writeAndMove Γ.blank (TM.idleDir (fresh parked).read) } : FunctionCfg (n + (k + 1)) (machine M N).Q) = _
  rw [fresh_step]
  apply congrArg some
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simpa only [Fin.snoc_last] using hout
    · simp only [Fin.snoc_castSucc, TM.transitionTape, fresh_readBack]
      exact fresh_step parked

end Toda.Oracle.FunctionPostprocess

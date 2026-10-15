import Toda.Oracle.FunctionPrepareBatch.Simulate

/-! # Rewinding a prepared stream while preserving the batch tape frame -/

namespace Toda.Oracle.FunctionPrepareBatch

open Complexity

variable {n : ℕ}

def readerCfg (stream : Tape) : FunctionCfg 0 FunctionBatch.machine.Q where
  state := .tag
  input := stream
  query := TM.parkedBlank
  answer := TM.parkedBlank
  work := fun _ => TM.parkedBlank
  output := TM.parkedBlank

def rewindCfg (M : TM n) (realInput : Tape) (scratch : Fin n → Tape) (stream : Tape) :
    FunctionCfg (n + 1) (machine M).Q :=
  { batchCfg M realInput scratch (readerCfg stream) with state := .inr none }

theorem rewind_zero_step (M : TM n) (oracle : FunctionOracle)
    (realInput : Tape) (scratch : Fin n → Tape) (stream : Tape)
    (hreal : realInput.read ≠ .start) (hscratch : ∀ i, (scratch i).read ≠ .start)
    (hh : stream.head = 0) (hi : stream.StartInvariant) :
    (machine M).step oracle (rewindCfg M realInput scratch stream) =
      some (batchCfg M realInput scratch (readerCfg (stream.move .right))) := by
  have hr : stream.read = .start := by simp [Tape.read, hh, hi.1]
  have hblank : TM.parkedBlank.write Γ.blank = TM.parkedBlank :=
    Batch.output_write_blank Tape.init_nil_move_right_hasBinaryPrefix_nil
  simp [FunctionTM.step, machine, localTransition, idleTransition, rewindCfg,
    batchCfg, readerCfg, Fin.snoc_last, hr, hreal,
    show TM.parkedBlank.read = Γ.blank from rfl, TM.idleDir, TM.readBackWrite,
    Tape.move, hblank]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last, hr, Tape.writeAndMove, Tape.write, Tape.move, hh]
  · simp only [Fin.snoc_castSucc, Fin.castSucc_ne_last, ↓reduceIte]
    change TM.transitionTape (scratch j) = scratch j
    exact TM.transitionTape_eq_self (hscratch j)

theorem rewind_positive_step (M : TM n) (oracle : FunctionOracle)
    (realInput : Tape) (scratch : Fin n → Tape) (stream : Tape)
    (hreal : realInput.read ≠ .start) (hscratch : ∀ i, (scratch i).read ≠ .start)
    (hr : stream.read ≠ .start) :
    (machine M).step oracle (rewindCfg M realInput scratch stream) =
      some (rewindCfg M realInput scratch
        (stream.writeAndMove (TM.readBackWrite stream.read) .left)) := by
  have hblank : TM.parkedBlank.write Γ.blank = TM.parkedBlank :=
    Batch.output_write_blank Tape.init_nil_move_right_hasBinaryPrefix_nil
  simp [FunctionTM.step, machine, localTransition, idleTransition, rewindCfg,
    batchCfg, readerCfg, Fin.snoc_last, hr, hreal,
    show TM.parkedBlank.read = Γ.blank from rfl, TM.idleDir, TM.readBackWrite,
    Tape.move, hblank]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, hr, ↓reduceIte]
    rfl
  · simp only [Fin.snoc_castSucc, Fin.castSucc_ne_last, ↓reduceIte]
    change TM.transitionTape (scratch j) = scratch j
    exact TM.transitionTape_eq_self (hscratch j)

theorem rewind_run (M : TM n) (oracle : FunctionOracle)
    (realInput : Tape) (scratch : Fin n → Tape)
    (hreal : realInput.read ≠ .start) (hscratch : ∀ i, (scratch i).read ≠ .start)
    (height : ℕ) : ∀ stream : Tape, stream.head = height → stream.StartInvariant →
      ∃ finalStream, (machine M).reachesIn oracle (height + 1)
          (rewindCfg M realInput scratch stream)
          (batchCfg M realInput scratch (readerCfg finalStream)) ∧
        finalStream.head = 1 ∧ finalStream.cells = stream.cells := by
  induction height with
  | zero =>
    intro stream hh hi
    exact ⟨stream.move .right,
      .step (rewind_zero_step M oracle realInput scratch stream hreal hscratch hh hi) .zero,
      by simp [Tape.move, hh], rfl⟩
  | succ height ih =>
    intro stream hh hi
    have hr := hi.read_ne_start (by omega : 1 ≤ stream.head)
    let next := stream.writeAndMove (TM.readBackWrite stream.read) .left
    have hhead : next.head = height := by simp [next, Tape.move, Tape.write_head, hh]
    have hinv : next.StartInvariant := hi.writeAndMove (TM.readBackWrite stream.read) .left
    obtain ⟨finalStream, hrun, hhead', hcells⟩ := ih next hhead hinv
    refine ⟨finalStream, .step (rewind_positive_step M oracle realInput scratch stream
      hreal hscratch hr) hrun, hhead', ?_⟩
    exact hcells.trans (TM.tape_readBackWrite_preserves stream .left (Or.inr hr))

theorem transitionTape_blank (t : Tape) (hcells : t.cells = (Tape.init []).cells)
    (hhead : t.head ≤ 1) : TM.transitionTape t = TM.parkedBlank := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hhead with hz | ho
  · have heq : t = Tape.init [] := Tape.ext hz hcells
    subst t
    rfl
  · have heq : t = TM.parkedBlank := Tape.ext ho hcells
    subst t
    exact TM.transitionTape_eq_self (by decide)

theorem boundary_step (M : TM n) (oracle : FunctionOracle) (clock : ℕ)
    (cfg : Cfg (n + 1) M.retargetOutput.Q) (hhalt : cfg.state = M.retargetOutput.qhalt)
    (hout : TM.transitionTape cfg.output = TM.parkedBlank) :
    (machine M).step oracle (liftCfg M clock cfg) = some
      (rewindCfg M (TM.transitionInput cfg.input)
        (fun i => TM.transitionTape (cfg.work (Fin.castSucc i)))
        (TM.transitionTape (cfg.work (Fin.last n)))) := by
  simp only [FunctionTM.step, machine, liftCfg, reduceCtorEq,
    ↓reduceIte, localTransition, hhalt, idleTransition, rewindCfg, batchCfg, readerCfg]
  change some ({
    state := Sum.inr none
    input := TM.transitionInput cfg.input
    query := TM.transitionTape cfg.output
    answer := (Preprocess.blankOutput clock).writeAndMove Γ.blank
      (TM.idleDir (Preprocess.blankOutput clock).read)
    work := fun i => TM.transitionTape (cfg.work i)
    output := (Preprocess.blankOutput clock).writeAndMove Γ.blank
      (TM.idleDir (Preprocess.blankOutput clock).read) } :
    FunctionCfg (n + 1) (machine M).Q) = _
  rw [hout]
  simp only [Preprocess.blankOutput_step]
  simp only [Preprocess.blankOutput, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte]
  have hw : (fun i => TM.transitionTape (cfg.work i)) =
      Fin.snoc (fun i => TM.transitionTape (cfg.work (Fin.castSucc i)))
        (TM.transitionTape (cfg.work (Fin.last n))) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hw]
  rfl

end Toda.Oracle.FunctionPrepareBatch

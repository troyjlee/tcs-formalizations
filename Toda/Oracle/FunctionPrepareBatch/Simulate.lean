import Toda.Oracle.FunctionPrepareBatch.Defs

/-! # Retargeting the batch reader to its prepared stream work tape -/

namespace Toda.Oracle.FunctionPrepareBatch

open Complexity

variable {n : ℕ}

def batchCfg (M : TM n) (realInput : Tape) (scratch : Fin n → Tape)
    (cfg : FunctionCfg 0 FunctionBatch.machine.Q) : FunctionCfg (n + 1) (machine M).Q where
  state := .inr (some cfg.state)
  input := realInput
  query := cfg.query
  answer := cfg.answer
  work := Fin.snoc scratch cfg.input
  output := cfg.output

theorem readBackWrite_move (t : Tape) (dir : Dir3) (h : t.read ≠ .start) :
    t.writeAndMove (TM.readBackWrite t.read) dir = t.move dir := by
  rw [Tape.writeAndMove, TM.toΓ_readBackWrite_of_ne_start h]
  have hw : t.write t.read = t := by
    simp [Tape.write, Tape.read, Function.update_eq_self]
  rw [hw]

theorem batch_input_step {oracle : FunctionOracle} {cfg next : FunctionCfg 0 FunctionBatch.machine.Q}
    (hstep : FunctionBatch.machine.step oracle cfg = some next)
    (hi : cfg.input.StartInvariant) (hh : 1 ≤ cfg.input.head) :
    next.input.StartInvariant ∧ 1 ≤ next.input.head := by
  simp only [FunctionTM.step] at hstep
  split at hstep
  · simp at hstep
  · cases hq : FunctionBatch.machine.queryTransition cfg.state with
    | some states =>
      rw [hq] at hstep
      simp only [Option.some.injEq] at hstep
      rw [← hstep]
      exact ⟨hi, hh⟩
    | none =>
      rw [hq] at hstep
      simp only [Option.some.injEq] at hstep
      rw [← hstep]
      refine ⟨hi.move _, ?_⟩
      change 1 ≤ (cfg.input.move (FunctionBatch.transition cfg.state cfg.input.read
        cfg.query.read cfg.answer.read cfg.output.read).inputDir).head
      simp only [FunctionBatch.transition]
      split
      · simp [Tape.move]
      · unfold TM.idleDir
        split <;> simp_all [Tape.move]

theorem batch_lift_step (M : TM n) (oracle : FunctionOracle)
    (realInput : Tape) (scratch : Fin n → Tape)
    (hreal : realInput.read ≠ .start) (hscratch : ∀ i, (scratch i).read ≠ .start)
    {cfg next : FunctionCfg 0 FunctionBatch.machine.Q} (hin : cfg.input.read ≠ .start)
    (hstep : FunctionBatch.machine.step oracle cfg = some next) :
    (machine M).step oracle (batchCfg M realInput scratch cfg) =
      some (batchCfg M realInput scratch next) := by
  have hhalt : cfg.state ≠ FunctionBatch.Phase.halt := by
    intro h
    simp [FunctionTM.step, FunctionBatch.machine, h] at hstep
  by_cases hquery : cfg.state = FunctionBatch.Phase.query
  · simp [FunctionTM.step, FunctionBatch.machine, hquery] at hstep
    have heq := Option.some.inj hstep
    rw [← heq]
    simp [FunctionTM.step, machine, batchCfg, hquery]
  · have hnone : FunctionBatch.machine.queryTransition cfg.state = none := by
      cases hs : cfg.state <;> simp_all [FunctionBatch.machine]
    have hnone' : (machine M).queryTransition
        (batchCfg M realInput scratch cfg).state = none := by
      cases hs : cfg.state <;> simp_all [machine, batchCfg]
      exact hquery rfl
    have hnothalt : (batchCfg M realInput scratch cfg).state ≠ (machine M).qhalt := by
      intro heq
      exact hhalt (Option.some.inj (Sum.inr.inj heq))
    have hsourcehalt : cfg.state ≠ FunctionBatch.machine.qhalt := hhalt
    simp only [FunctionTM.step, hsourcehalt, ↓reduceIte, hnone, Option.some.injEq] at hstep
    rw [← hstep]
    simp only [FunctionTM.step, hnothalt, ↓reduceIte, hnone']
    simp only [machine, batchCfg, localTransition, Fin.snoc_last, FunctionBatch.machine]
    congr 2
    · exact TM.transitionInput_eq_self hreal
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, ↓reduceIte]
        exact readBackWrite_move cfg.input _ hin
      · simp only [Fin.snoc_castSucc, Fin.castSucc_ne_last, ↓reduceIte]
        exact TM.transitionTape_eq_self (hscratch j)

theorem batch_lift_run (M : TM n) (oracle : FunctionOracle)
    (realInput : Tape) (scratch : Fin n → Tape)
    (hreal : realInput.read ≠ .start) (hscratch : ∀ i, (scratch i).read ≠ .start)
    {time : ℕ} {cfg final : FunctionCfg 0 FunctionBatch.machine.Q}
    (hreach : FunctionBatch.machine.reachesIn oracle time cfg final)
    (hinv : cfg.input.StartInvariant) (hhead : 1 ≤ cfg.input.head) :
    (machine M).reachesIn oracle time (batchCfg M realInput scratch cfg)
      (batchCfg M realInput scratch final) := by
  induction hreach with
  | zero => exact .zero
  | step hone _ ih =>
    obtain ⟨hi', hh'⟩ := batch_input_step hone hinv hhead
    exact .step (batch_lift_step M oracle realInput scratch hreal hscratch
      (hinv.read_ne_start hhead) hone) (ih hi' hh')

end Toda.Oracle.FunctionPrepareBatch

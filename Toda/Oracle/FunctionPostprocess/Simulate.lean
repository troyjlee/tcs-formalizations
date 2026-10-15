import Toda.Oracle.FunctionPostprocess.Source

namespace Toda.Oracle.FunctionPostprocess

open Complexity
open Postprocess (write_append)

variable {n k : ℕ}

theorem post_step (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    (query answer : Tape) (scratch : Fin n → Tape)
    (hq : query.read ≠ .start) (ha : answer.read ≠ .start) (hw : ∀ i, (scratch i).read ≠ .start)
    {cfg next : Cfg (k + 1) (TM.retargetInputStarted N).Q}
    (hstep : (TM.retargetInputStarted N).step cfg = some next) :
    (machine M N).step oracle (postCfg M N query answer scratch cfg) =
      some (postCfg M N query answer scratch next) := by
  have hn : cfg.state ≠ (TM.retargetInputStarted N).qhalt := by
    intro h; simp [TM.step, h] at hstep
  simp only [TM.step, hn, ↓reduceIte, Option.some.injEq] at hstep
  rw [← hstep]
  simp only [FunctionTM.step, machine, postCfg, Sum.inr.injEq, Option.some.injEq,
    hn, ↓reduceIte, localTransition, left, Fin.append_left]
  have hquery : query.writeAndMove (TM.readBackWrite query.read)
      (TM.idleDir query.read) = query := TM.transitionTape_eq_self hq
  have hanswer : answer.writeAndMove (TM.readBackWrite answer.read)
      (TM.idleDir answer.read) = answer := TM.transitionTape_eq_self ha
  have hscratch : (fun i => (scratch i).writeAndMove (TM.readBackWrite (scratch i).read)
      (TM.idleDir (scratch i).read)) = scratch := by
    funext i; exact TM.transitionTape_eq_self (hw i)
  rw [hquery, hanswer, write_append, hscratch, read_right_append]

theorem post_run (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    (query answer : Tape) (scratch : Fin n → Tape)
    (hq : query.read ≠ .start) (ha : answer.read ≠ .start) (hw : ∀ i, (scratch i).read ≠ .start)
    {elapsed : ℕ} {cfg final : Cfg (k + 1) (TM.retargetInputStarted N).Q}
    (hreach : (TM.retargetInputStarted N).reachesIn elapsed cfg final) :
    (machine M N).reachesIn oracle elapsed (postCfg M N query answer scratch cfg)
      (postCfg M N query answer scratch final) := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (post_step M N oracle query answer scratch hq ha hw hstep) ih

end Toda.Oracle.FunctionPostprocess

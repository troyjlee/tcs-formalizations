import Toda.Oracle.Postprocess.Source

namespace Toda.Oracle.Postprocess

open Complexity

variable {n k : ℕ}

theorem post_step (M : OracleTM n) (N : TM k) (oracle : BooleanOracle)
    (query : Tape) (scratch : Fin n → Tape)
    (hq : query.read ≠ .start) (hw : ∀ i, (scratch i).read ≠ .start)
    {cfg next : Cfg (k + 1) (TM.retargetInputStarted N).Q}
    (hstep : (TM.retargetInputStarted N).step cfg = some next) :
    (machine M N).step oracle (postCfg M N query scratch cfg) =
      some (postCfg M N query scratch next) := by
  have hn : cfg.state ≠ (TM.retargetInputStarted N).qhalt := by
    intro h; simp [TM.step, h] at hstep
  simp only [TM.step, hn, ↓reduceIte, Option.some.injEq] at hstep
  rw [← hstep]
  simp only [OracleTM.step, machine, postCfg, Sum.inr.injEq, Option.some.injEq,
    hn, ↓reduceIte, localTransition, left, Fin.append_left]
  have hquery : query.writeAndMove (TM.readBackWrite query.read)
      (TM.idleDir query.read) = query := TM.transitionTape_eq_self hq
  have hscratch : (fun i => (scratch i).writeAndMove (TM.readBackWrite (scratch i).read)
      (TM.idleDir (scratch i).read)) = scratch := by
    funext i; exact TM.transitionTape_eq_self (hw i)
  rw [hquery, write_append, hscratch, read_right_append]

theorem post_run (M : OracleTM n) (N : TM k) (oracle : BooleanOracle)
    (query : Tape) (scratch : Fin n → Tape)
    (hq : query.read ≠ .start) (hw : ∀ i, (scratch i).read ≠ .start)
    {elapsed : ℕ} {cfg final : Cfg (k + 1) (TM.retargetInputStarted N).Q}
    (hreach : (TM.retargetInputStarted N).reachesIn elapsed cfg final) :
    (machine M N).reachesIn oracle elapsed (postCfg M N query scratch cfg)
      (postCfg M N query scratch final) := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (post_step M N oracle query scratch hq hw hstep) ih

end Toda.Oracle.Postprocess

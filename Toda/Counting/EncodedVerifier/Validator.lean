import Complexitylib.Models.TuringMachine.Subroutines.PairValidate

/-!
# Validator output shape and erasing the verdict

The initialized pair validator writes only output cell one. Its remaining
output cells stay blank, so a single transition erases the verdict and restores
the exact blank output tape needed by the witness verifier.
-/

namespace Toda.Counting.EncodedVerifier

open Complexity

set_option backward.isDefEq.respectTransparency false

private def OutputShape (t : Tape) : Prop :=
  t.StartInvariant ∧ t.head ≤ 1 ∧ ∀ j, 2 ≤ j → t.cells j = Γ.blank

private theorem tail_write (t : Tape) (s : Γw) (d : Dir3)
    (hh : t.head ≤ 1) (ht : ∀ j, 2 ≤ j → t.cells j = Γ.blank) :
    ∀ j, 2 ≤ j → (t.writeAndMove s.toΓ d).cells j = Γ.blank := by
  intro j hj
  have hne : j ≠ t.head := by omega
  by_cases hzero : t.head = 0 <;>
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hzero, hne, ht j hj]

private theorem shape_idle (t : Tape) (s : Γw) (h : OutputShape t) :
    OutputShape (t.writeAndMove s.toΓ (TM.idleDir t.read)) := by
  refine ⟨h.1.writeAndMove s _, ?_, tail_write t s _ h.2.1 h.2.2⟩
  by_cases hzero : t.head = 0
  · have hr : t.read = Γ.start := by simpa [Tape.read, hzero] using h.1.1
    simp [Tape.writeAndMove, Tape.move, Tape.write_head, TM.idleDir, hr, hzero]
  · have hr := h.1.read_ne_start (by omega)
    simpa [Tape.writeAndMove, Tape.move, Tape.write_head, TM.idleDir, hr] using h.2.1

private def ValidatorInvariant (k : ℕ)
    (c : Cfg (0 + k) (TM.pairValidateTM.liftTM k).Q) : Prop :=
  OutputShape c.output ∧ (c.state = TM.ScannerPhase.start → c.output.head = 0)

private theorem validator_step_invariant (k : ℕ)
    {c c' : Cfg (0 + k) (TM.pairValidateTM.liftTM k).Q}
    (hs : (TM.pairValidateTM.liftTM k).step c = some c')
    (h : ValidatorInvariant k c) : ValidatorInvariant k c' := by
  rcases h with ⟨hshape, hstart⟩
  cases hq : c.state with
  | start =>
    have hh : c.output.head = 0 := hstart hq
    simp only [TM.step, TM.liftTM, TM.pairValidateTM, TM.scannerTM, hq,
      reduceCtorEq, ite_false, Option.some.injEq] at hs
    subst c'
    refine ⟨⟨hshape.1.writeAndMove .blank .right, ?_,
      tail_write _ .blank .right hshape.2.1 hshape.2.2⟩, ?_⟩
    · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hh]
    · intro heq
      cases heq
  | scan s =>
    by_cases hi : c.input.read = Γ.blank
    · simp only [TM.step, TM.liftTM, TM.pairValidateTM, TM.scannerTM, hq,
        reduceCtorEq, ite_false, hi, ite_true, Option.some.injEq] at hs
      subst c'
      exact ⟨shape_idle _ _ hshape, by intro heq; cases heq⟩
    · simp only [TM.step, TM.liftTM, TM.pairValidateTM, TM.scannerTM, hq,
        reduceCtorEq, ite_false, hi, Option.some.injEq] at hs
      subst c'
      exact ⟨shape_idle _ _ hshape, by intro heq; cases heq⟩
  | done =>
    simp [TM.step, TM.liftTM, TM.pairValidateTM, TM.scannerTM, hq] at hs

private theorem validator_reaches_invariant (k : ℕ)
    {c c' : Cfg (0 + k) (TM.pairValidateTM.liftTM k).Q} {t : ℕ}
    (hr : (TM.pairValidateTM.liftTM k).reachesIn t c c') :
    ValidatorInvariant k c → ValidatorInvariant k c' := by
  induction hr with
  | zero => exact id
  | step hs _ ih => exact fun h => ih (validator_step_invariant k hs h)

/-- Every initialized validator run leaves cells after its verdict blank. -/
theorem validator_output_tail (k : ℕ) (bits : List Bool)
    {c : Cfg (0 + k) (TM.pairValidateTM.liftTM k).Q} {t : ℕ}
    (hr : (TM.pairValidateTM.liftTM k).reachesIn t
      ((TM.pairValidateTM.liftTM k).initCfg bits) c) :
    ∀ j, 2 ≤ j → c.output.cells j = Γ.blank := by
  apply (validator_reaches_invariant k hr ?_).1.2.2
  refine ⟨⟨Tape.StartInvariant.init_nil, Nat.zero_le 1, ?_⟩, fun _ => rfl⟩
  intro j hj
  simp [Tape.init, show j ≠ 0 by omega]

/-- The initialized validator specification with the blank output tail exposed.
It has the same linear runtime as the unchanged upstream validator. -/
theorem validator_hoareTime (k : ℕ) (bits : List Bool) :
    (TM.pairValidateTM.liftTM k).HoareTime
      (fun inp work out =>
        inp = Tape.init (bits.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        TM.AllTapesWF inp work out ∧
        inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
        inp.head ≤ bits.length + 2 ∧
        (∀ i, work i = (Tape.init []).move Dir3.right) ∧
        out.head ≤ bits.length + 2 ∧
        (bits ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (bits ∉ validPairEncoding → out.cells 1 = Γ.zero) ∧
        (∀ j, 2 ≤ j → out.cells j = Γ.blank))
      (bits.length + 2) := by
  intro inp work out hp
  obtain ⟨c, t, ht, hr, hh, hwf, hic, hih, hw, hoh, hy, hn⟩ :=
    TM.pairValidateTM_lift_hoareTime k bits inp work out hp
  rcases hp with ⟨rfl, rfl, rfl⟩
  exact ⟨c, t, ht, hr, hh, hwf, hic, hih, hw, hoh, hy, hn,
    validator_output_tail k bits hr⟩

/-- Erase the output cell under the head in one transition, preserving every
other tape away from the start marker. -/
def cleanVerdict (k : ℕ) : TM k where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ i w o :=
    (true, fun j => TM.readBackWrite (w j), .blank,
      TM.idleDir i, fun j => TM.idleDir (w j), TM.idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
      TM.idleDir_right_of_start⟩

private theorem idle_preserves (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read) = t := by
  rw [TM.writeAndMove_readBack _ h]
  simp [TM.idleDir, h, Tape.move]

private theorem clean_output (out : Tape) (hh : out.head = 1)
    (hi : out.StartInvariant) (ht : ∀ j, 2 ≤ j → out.cells j = Γ.blank) :
    out.writeAndMove Γ.blank (TM.idleDir out.read) = (Tape.init []).move .right := by
  have hr := hi.read_ne_start (by omega)
  apply Tape.ext
  · simp [Tape.writeAndMove, Tape.move, Tape.write_head, TM.idleDir, hr, hh]
  · funext j
    simp only [Tape.writeAndMove, Tape.move_cells]
    by_cases hj0 : j = 0
    · subst j
      simp [Tape.write, hh, hi.1, Tape.init]
    · by_cases hj1 : j = 1
      · subst j
        simp [Tape.write, hh, Tape.init]
      · have hj : 2 ≤ j := by omega
        simp [Tape.write, hh, hj1, Tape.init, hj0, ht j hj]

/-- At the branch boundary, erase the validator's verdict and recover the
exact started blank output, while preserving input and work tapes. -/
theorem cleanVerdict_hoareTime (k : ℕ) (inp : Tape) (work : Fin k → Tape)
    (hi : inp.read ≠ Γ.start) (hw : ∀ j, (work j).read ≠ Γ.start) :
    (cleanVerdict k).HoareTime
      (fun inp' work' out => inp' = inp ∧ work' = work ∧
        out.head = 1 ∧ out.StartInvariant ∧ ∀ j, 2 ≤ j → out.cells j = Γ.blank)
      (fun inp' work' out => inp' = inp ∧ work' = work ∧
        out = (Tape.init []).move .right) 1 := by
  intro inp' work' out h
  rcases h with ⟨hip, hwp, hh, ho, ht⟩
  subst inp'
  subst work'
  let c : Cfg k (cleanVerdict k).Q :=
    { state := true, input := inp, work := work, output := (Tape.init []).move .right }
  refine ⟨c, 1, le_rfl, TM.reachesIn.step ?_ TM.reachesIn.zero, rfl, rfl, rfl, rfl⟩
  simp only [TM.step, cleanVerdict, Bool.false_eq_true, ite_false, Option.some.injEq]
  apply Cfg.ext
  · rfl
  · simp [c, TM.idleDir, hi, Tape.move]
  · exact funext fun j => idle_preserves _ (hw j)
  · exact clean_output out hh ho ht

end Toda.Counting.EncodedVerifier

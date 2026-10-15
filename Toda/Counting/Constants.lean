import Toda.Counting.CanonicalWitness
import Toda.Counting.PolynomialClock

/-!
# Constant counting functions

A finite countdown machine has exactly `value` accepting leaves on every
input. Its first transition has one productive branch and one rejecting
branch; each positive countdown state contributes one accepting leaf and
continues the countdown on the other branch. This realizes constants in the
unchanged machine-based classes #P and GapP.
-/

namespace Toda.Counting

open Complexity

private abbrev ConstantState (value : ℕ) := Option (Option (Fin (value + 1)))

private def constantAction (value : ℕ) (state : ConstantState value) (bit : Bool) :
    ConstantState value × Γw :=
  match state with
  | none => (if bit then some none else some (some ⟨value, by omega⟩), .blank)
  | some none => (some none, .zero)
  | some (some remaining) =>
      if hzero : remaining.val = 0 then (some none, .zero)
      else if bit then
        (some (some ⟨remaining.val - 1, by omega⟩), .zero)
      else (some none, .one)

/-- A finite, input-independent NTM with exactly `value` accepting leaves. -/
def constantCountingMachine (value : ℕ) : NTM 0 where
  Q := ConstantState value
  qstart := none
  qhalt := some none
  δ := fun bit state _ _ outputHead =>
    let action := constantAction value state bit
    (action.1, fun _ => Γw.blank, action.2, .right, fun _ => .right,
      if outputHead = Γ.start then .right else .stay)
  δ_right_of_start := by
    intro bit state inputHead workHeads outputHead
    exact ⟨fun _ => rfl, fun _ _ => rfl, fun h => by simp [h]⟩

private theorem constant_run_halts (value remaining : ℕ) (hr : remaining < value + 1)
    (cfg : Cfg 0 (constantCountingMachine value).Q)
    (hstate : cfg.state = some (some ⟨remaining, hr⟩))
    (choices : Fin (remaining + 1) → Bool) :
    (constantCountingMachine value).halted
      ((constantCountingMachine value).trace (remaining + 1) choices cfg) := by
  induction remaining generalizing cfg with
  | zero =>
      simp [NTM.trace, NTM.halted, Cfg.isHalted, constantCountingMachine,
        constantAction, hstate]
  | succ remaining ih =>
      rw [trace_succ_eq]
      cases hbit : choices 0 with
      | false =>
          have hhalt : (constantCountingMachine value).halted
              ((constantCountingMachine value).trace 1 (fun _ => false) cfg) := by
            simp [NTM.trace, NTM.halted, Cfg.isHalted, constantCountingMachine,
              constantAction, hstate]
          rw [(constantCountingMachine value).trace_halted _ _ hhalt]
          exact hhalt
      | true =>
          apply ih (by omega)
          simp [NTM.trace, constantCountingMachine, constantAction, hstate]

private theorem constant_run_count (value remaining : ℕ) (hr : remaining < value + 1)
    (cfg : Cfg 0 (constantCountingMachine value).Q)
    (hstate : cfg.state = some (some ⟨remaining, hr⟩))
    (hhead : cfg.output.head = 1) (hmarker : cfg.output.cells 1 ≠ Γ.start) :
    (constantCountingMachine value).acceptLeafCountFrom (remaining + 1) cfg =
      remaining := by
  induction remaining generalizing cfg with
  | zero =>
      simp [NTM.acceptLeafCountFrom, NTM.trace, NTM.halted, Cfg.isHalted,
        constantCountingMachine, constantAction, hstate, Tape.writeAndMove,
        Tape.write, Tape.move, Tape.read, hhead, hmarker]
  | succ remaining ih =>
      have hnot : ¬ (constantCountingMachine value).halted cfg := by
        simp [NTM.halted, Cfg.isHalted, constantCountingMachine, hstate]
      rw [NTM.acceptLeafCountFrom, ite_eq_right hnot]
      have hfalse : (constantCountingMachine value).halted
          ((constantCountingMachine value).trace 1 (fun _ => false) cfg) := by
        simp [NTM.trace, NTM.halted, Cfg.isHalted, constantCountingMachine,
          constantAction, hstate]
      have hout : ((constantCountingMachine value).trace 1
          (fun _ => false) cfg).output.cells 1 = Γ.one := by
        simp [NTM.trace, constantCountingMachine, constantAction, hstate,
          Tape.writeAndMove, Tape.write, Tape.move, Tape.read, hhead, hmarker]
      have hcount : (constantCountingMachine value).acceptLeafCountFrom
          (remaining + 1)
          ((constantCountingMachine value).trace 1 (fun _ => false) cfg) = 1 := by
        simp [NTM.acceptLeafCountFrom, hfalse, hout]
      rw [hcount]
      have htrue := ih (by omega)
        ((constantCountingMachine value).trace 1 (fun _ => true) cfg)
      have heq : (constantCountingMachine value).acceptLeafCountFrom
          (remaining + 1)
          ((constantCountingMachine value).trace 1 (fun _ => true) cfg) = remaining := by
        apply htrue
        · simp [NTM.trace, constantCountingMachine, constantAction, hstate]
        · simp [NTM.trace, constantCountingMachine, constantAction, hstate,
            Tape.writeAndMove, Tape.write, Tape.move, Tape.read, hhead, hmarker]
        · simp [NTM.trace, constantCountingMachine, constantAction, hstate,
            Tape.writeAndMove, Tape.write, Tape.move, Tape.read, hhead, hmarker]
      omega

/-- Every branch halts within a constant clock depending only on the desired
count. No computation on the input is needed. -/
theorem constantCountingMachine_allPathsHaltIn (value : ℕ) :
    (constantCountingMachine value).AllPathsHaltIn (fun _ => value + 2) := by
  intro x choices
  change (constantCountingMachine value).halted
    ((constantCountingMachine value).trace ((value + 1) + 1) choices
      ((constantCountingMachine value).initCfg x))
  rw [trace_succ_eq]
  cases hbit : choices 0 with
  | false =>
      apply constant_run_halts value value (by omega)
      simp [NTM.trace, constantCountingMachine, constantAction]
  | true =>
      have hhalt : (constantCountingMachine value).halted
          ((constantCountingMachine value).trace 1 (fun _ => true)
            ((constantCountingMachine value).initCfg x)) := by
        simp [NTM.trace, NTM.halted, Cfg.isHalted, constantCountingMachine,
          constantAction]
      rw [(constantCountingMachine value).trace_halted _ _ hhalt]
      exact hhalt

/-- The clocked accepting-leaf count is exactly the requested constant. -/
theorem constantCountingMachine_acceptLeafCount (value : ℕ) (x : List Bool) :
    (constantCountingMachine value).acceptLeafCount x (value + 2) = value := by
  rw [NTM.acceptLeafCount, show value + 2 = (value + 1) + 1 by omega,
    NTM.acceptLeafCountFrom]
  simp only [NTM.halted, Cfg.isHalted, NTM.initCfg, Cfg.init,
    constantCountingMachine, reduceCtorEq, ite_false]
  have hfalse : (constantCountingMachine value).acceptLeafCountFrom (value + 1)
      ((constantCountingMachine value).trace 1 (fun _ => false)
        ((constantCountingMachine value).initCfg x)) = value := by
    apply constant_run_count value value (by omega)
    · simp [NTM.trace, constantCountingMachine, constantAction]
    · simp [NTM.trace, constantCountingMachine, constantAction,
        Tape.writeAndMove, Tape.write, Tape.move, Tape.read, Tape.init]
    · simp [NTM.trace, constantCountingMachine, constantAction,
        Tape.writeAndMove, Tape.write, Tape.move, Tape.read, Tape.init]
  have htrue : (constantCountingMachine value).acceptLeafCountFrom (value + 1)
      ((constantCountingMachine value).trace 1 (fun _ => true)
        ((constantCountingMachine value).initCfg x)) = 0 := by
    simp [NTM.acceptLeafCountFrom, NTM.trace, NTM.halted, Cfg.isHalted,
      constantCountingMachine, constantAction,
      Tape.writeAndMove, Tape.write, Tape.move, Tape.read, Tape.init]
  change (constantCountingMachine value).acceptLeafCountFrom (value + 1)
      ((constantCountingMachine value).trace 1 (fun _ => false)
        ((constantCountingMachine value).initCfg x)) +
    (constantCountingMachine value).acceptLeafCountFrom (value + 1)
      ((constantCountingMachine value).trace 1 (fun _ => true)
        ((constantCountingMachine value).initCfg x)) = value
  rw [hfalse, htrue, Nat.add_zero]

/-- Every constant natural-valued function belongs to canonical #P. -/
theorem sharpP_const (value : ℕ) : (fun _ : List Bool => value) ∈ SharpP := by
  refine ⟨0, constantCountingMachine value, fun _ => value + 2, 0,
    constantCountingMachine_allPathsHaltIn value, BigO.const_le_pow _ _, ?_⟩
  intro x
  exact (constantCountingMachine_acceptLeafCount value x).symm

/-- Every constant integer-valued function belongs to canonical GapP. -/
theorem gapP_const (value : ℤ) : (fun _ : List Bool => value) ∈ GapP := by
  refine ⟨fun _ => value.toNat, fun _ => (-value).toNat,
    sharpP_const _, sharpP_const _, fun _ => ?_⟩
  change value = (value.toNat : ℤ) - ((-value).toNat : ℤ)
  omega

end Toda.Counting

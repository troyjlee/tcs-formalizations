/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Troy Lee
-/
import Complexitylib.Classes.Containments.Internal.ConfigCount
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Window invariants for the actual upstream machine

The one-step window proof is adapted from `Windowed.step` in the pinned upstream
`Classes/Containments/Internal/PSPACESubsetEXP.lean` (Apache-2.0). Induction over
actual machine reachability then supplies both conditions needed by `cfgCode_inj`.
The acceptance lemma uses deterministic halting uniqueness, so both directions
of language membership hold for a `TM.DecidesInSpace` witness.
-/

namespace IPPSPACE

open Complexity

/-- Bounded source heads cannot change cells outside the fixed window. -/
theorem windowed_machine_step {tapes : ℕ} {tm : TM tapes} {input : List Bool}
    {space : ℕ} {c c' : Cfg tapes tm.Q}
    (hw : Windowed input space c) (hstep : tm.step c = some c')
    (hspace : c.WithinDecisionSpace input.length space) : Windowed input space c' := by
  rw [TM.step, ite_eq_right (TM.state_ne_qhalt_of_step hstep)] at hstep
  injection hstep with hstep
  subst hstep
  refine ⟨?_, ?_, ?_⟩
  · show (c.input.move _).cells = _
    rw [Tape.move_cells]
    exact hw.input
  · intro i p hp
    have hhead : (c.work i).head ≤ space := hspace.1.1 i
    show ((c.work i).writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.work i p hp
  · intro p hp
    have hhead : c.output.head ≤ space + 1 := hspace.2
    show (c.output.writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.output p hp

/-- A bound on every reachable head position entails a bound on all tape
contents that can differ from their initial values. -/
theorem windowed_of_machine_reaches {tapes : ℕ} (tm : TM tapes) (input : List Bool)
    (space : ℕ)
    (hspace : ∀ c, tm.reaches (tm.initCfg input) c → c.WithinDecisionSpace input.length space)
    (c : Cfg tapes tm.Q) (hreach : tm.reaches (tm.initCfg input) c) :
    Windowed input space c := by
  induction hreach with
  | refl => exact windowed_init tm.qstart input space
  | @tail c c' hprefix hstep ih =>
    exact windowed_machine_step ih hstep (hspace c hprefix)

/-- The actual space-decider hypothesis gives the complete finite-code invariant. -/
theorem machine_decider_reachable_invariant {tapes : ℕ} {tm : TM tapes}
    {language : Language} {space : ℕ → ℕ} (hdec : tm.DecidesInSpace language space)
    (input : List Bool) (c : Cfg tapes tm.Q) (hreach : tm.reaches (tm.initCfg input) c) :
    Windowed input (space input.length) c ∧ c.WithinDecisionSpace input.length (space input.length) :=
  ⟨windowed_of_machine_reaches tm input _ (hdec.1 input) c hreach, hdec.1 input c hreach⟩

/-- Halting configurations have no outgoing machine transition. -/
theorem machine_reaches_from_halted {tapes : ℕ} {tm : TM tapes} {a b : Cfg tapes tm.Q}
    (hhalt : tm.halted a) (hreach : tm.reaches a b) : b = a := by
  apply (Relation.reflTransGen_iff_eq (r := tm.stepRel) (a := a) (b := b) ?_).mp hreach
  intro c
  simp [TM.stepRel, TM.step, show a.state = tm.qhalt from hhalt]

/-- Two halted endpoints of a deterministic run must be the same configuration. -/
theorem machine_halted_endpoint_unique {tapes : ℕ} {tm : TM tapes}
    {initial a b : Cfg tapes tm.Q} (ha : tm.reaches initial a) (hb : tm.reaches initial b)
    (hhaltA : tm.halted a) (hhaltB : tm.halted b) : a = b := by
  have hdet : Relator.RightUnique tm.stepRel := by
    intro c d e hd he
    exact Option.some.inj (hd.symm.trans he)
  rcases Relation.ReflTransGen.total_of_right_unique hdet ha hb with hab | hba
  · exact (machine_reaches_from_halted hhaltA hab).symm
  · exact machine_reaches_from_halted hhaltB hba

/-- The deciding specification rules out other accepting halts on nonmembers. -/
theorem machine_decider_accepts_iff {tapes : ℕ} {tm : TM tapes}
    {language : Language} {space : ℕ → ℕ} (hdec : tm.DecidesInSpace language space)
    (input : List Bool) : tm.Accepts input ↔ input ∈ language := by
  obtain ⟨final, hreach, hhalt, hyes, hno⟩ := hdec.2 input
  constructor
  · rintro ⟨other, hother, hotherHalt, haccept⟩
    have heq := machine_halted_endpoint_unique hother hreach hotherHalt hhalt
    subst other
    by_contra hn
    have hzero := hno hn
    rw [hzero] at haccept
    cases haccept
  · intro hin
    exact ⟨final, hreach, hhalt, hyes hin⟩

end IPPSPACE

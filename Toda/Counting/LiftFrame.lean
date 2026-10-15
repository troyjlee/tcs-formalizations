import Complexitylib.Models.TuringMachine.Lift
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# Lifting deterministic Hoare specifications through extra work tapes

A lifted machine preserves arbitrary extra tapes whose heads do not read a
start marker. The extra tapes need not be blank or have any prescribed
contents. Simulation and Hoare specifications retain the source time bound.
-/

namespace Toda.Counting.LiftFrame

open Complexity

set_option backward.isDefEq.respectTransparency false

variable {k e : ℕ}

/-- Exact simulation through the arbitrary, stable extra-tape frame. -/
theorem liftTM_reachesIn_liftCfgWith (M : TM k) (e : ℕ) (extras : Fin e → Tape)
    (hex : ∀ j, (extras j).read ≠ Γ.start) {time : ℕ} {c c' : Cfg k M.Q}
    (h : M.reachesIn time c c') :
    (M.liftTM e).reachesIn time (M.liftCfgWith e extras c) (M.liftCfgWith e extras c') :=
  TM.reachesIn_map' (tm' := M.liftTM e) (M.liftCfgWith e extras)
    (fun a a' ha => by rw [TM.liftTM_step_liftCfgWith M e hex, ha]; rfl) h

@[simp] theorem liftCfgWith_work_castAdd (M : TM k) (e : ℕ)
    (extras : Fin e → Tape) (c : Cfg k M.Q) (i : Fin k) :
    (M.liftCfgWith e extras c).work (Fin.castAdd e i) = c.work i := by
  exact M.liftCfgWith_work_lt e extras c (Fin.castAdd e i) i.isLt

@[simp] theorem liftCfgWith_work_natAdd (M : TM k) (e : ℕ)
    (extras : Fin e → Tape) (c : Cfg k M.Q) (i : Fin e) :
    (M.liftCfgWith e extras c).work (Fin.natAdd k i) = extras i := by
  rw [TM.liftCfgWith_work_ge M e extras c (Fin.natAdd k i) (by simp)]
  congr 1
  apply Fin.ext
  simp [TM.extraIdx]

/-- Reconstruct an arbitrary larger work family from its original and extra
indices. This is the actual entry configuration of the lifted machine. -/
theorem liftCfgWith_partition (M : TM k) (e : ℕ) (state : M.Q)
    (inp out : Tape) (work : Fin (k + e) → Tape) :
    M.liftCfgWith e (fun j => work (Fin.natAdd k j))
      ⟨state, inp, (fun i => work (Fin.castAdd e i)), out⟩ =
      ⟨state, inp, work, out⟩ := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext i
  by_cases hi : i.val < k
  · rw [TM.liftCfgWith_work_lt M e _ _ i hi]
    rfl
  · rw [TM.liftCfgWith_work_ge M e _ _ i (by omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.natAdd_mk, TM.extraIdx]
    omega

/-- A Hoare triple lifts at no time cost while preserving each named extra
tape exactly. The extra-tape side condition is only local non-marker reading. -/
theorem liftTM_hoareTime_frame (M : TM k) (e : ℕ)
    {pre post : TapePred k} {bound : ℕ}
    (h : M.HoareTime pre post bound) (extras : Fin e → Tape)
    (hex : ∀ j, (extras j).read ≠ Γ.start) :
    (M.liftTM e).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd e i)) out ∧
        ∀ j, work (Fin.natAdd k j) = extras j)
      (fun inp work out => post inp (fun i => work (Fin.castAdd e i)) out ∧
        ∀ j, work (Fin.natAdd k j) = extras j)
      bound := by
  intro inp work out hp
  obtain ⟨c, time, ht, hr, hh, hpost⟩ := h inp (fun i => work (Fin.castAdd e i)) out hp.1
  have hextras : (fun j => work (Fin.natAdd k j)) = extras := funext hp.2
  have hstart : M.liftCfgWith e extras
      ⟨M.qstart, inp, (fun i => work (Fin.castAdd e i)), out⟩ =
      ⟨(M.liftTM e).qstart, inp, work, out⟩ := by
    rw [← hextras]
    exact liftCfgWith_partition M e M.qstart inp out work
  refine ⟨M.liftCfgWith e extras c, time, ht, ?_, hh, ?_, ?_⟩
  · erw [← hstart]
    exact liftTM_reachesIn_liftCfgWith M e extras hex hr
  · simpa only [TM.liftCfgWith_input, TM.liftCfgWith_output, liftCfgWith_work_castAdd] using hpost
  · exact liftCfgWith_work_natAdd M e extras c

/-- A source Hoare triple lifts unchanged when arbitrary extra work tapes
initially read non-marker symbols. No assumptions are made on their contents. -/
theorem liftTM_hoareTime_stable (M : TM k) (e : ℕ)
    {pre post : TapePred k} {bound : ℕ}
    (h : M.HoareTime pre post bound) :
    (M.liftTM e).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd e i)) out ∧
        ∀ j : Fin e, (work (Fin.natAdd k j)).read ≠ Γ.start)
      (fun inp work out => post inp (fun i => work (Fin.castAdd e i)) out)
      bound := by
  intro inp work out hp
  obtain ⟨c, time, ht, hr, hh, hpost, _⟩ :=
    liftTM_hoareTime_frame M e h (fun j => work (Fin.natAdd k j)) hp.2
      inp work out ⟨hp.1, fun _ => rfl⟩
  exact ⟨c, time, ht, hr, hh, hpost⟩

/-- Any source run lifts with unchanged runtime even when the extra tapes
start at arbitrary heads. Their contents may change through idle actions, but
the projected source configuration is preserved exactly. -/
theorem liftTM_reachesIn_exists_frame (M : TM k) (e : ℕ)
    (extras : Fin e → Tape) {time : ℕ} {c c' : Cfg k M.Q}
    (h : M.reachesIn time c c') :
    ∃ extras', (M.liftTM e).reachesIn time
      (M.liftCfgWith e extras c) (M.liftCfgWith e extras' c') := by
  let R : Cfg k M.Q → Cfg (k + e) (M.liftTM e).Q → Prop :=
    fun inner outer => ∃ frame, outer = M.liftCfgWith e frame inner
  have hstep : ∀ {a a' b}, R a b → M.step a = some a' →
      ∃ b', (M.liftTM e).step b = some b' ∧ R a' b' := by
    rintro a a' b ⟨frame, rfl⟩ ha
    let frame' : Fin e → Tape := fun j => (frame j).writeAndMove
      (TM.readBackWrite (frame j).read) (TM.idleDir (frame j).read)
    refine ⟨M.liftCfgWith e frame' a', ?_, frame', rfl⟩
    rw [TM.liftTM_step_liftCfgWith_frame, ha]
    rfl
  obtain ⟨b', hr, frame', rfl⟩ := TM.reachesIn_transport R hstep h
    (show R c (M.liftCfgWith e extras c) from ⟨extras, rfl⟩)
  exact ⟨frame', hr⟩

/-- A source Hoare triple lifts at the same cost with entirely arbitrary extra
tapes. This form only promises the source postcondition; it does not promise
that the ignored extra tapes are preserved. -/
theorem liftTM_hoareTime (M : TM k) (e : ℕ)
    {pre post : TapePred k} {bound : ℕ}
    (h : M.HoareTime pre post bound) :
    (M.liftTM e).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd e i)) out)
      (fun inp work out => post inp (fun i => work (Fin.castAdd e i)) out)
      bound := by
  intro inp work out hp
  obtain ⟨c, time, ht, hr, hh, hpost⟩ := h inp (fun i => work (Fin.castAdd e i)) out hp
  obtain ⟨extras', hlift⟩ := liftTM_reachesIn_exists_frame M e
    (fun j => work (Fin.natAdd k j)) hr
  erw [liftCfgWith_partition] at hlift
  refine ⟨M.liftCfgWith e extras' c, time, ht, hlift, hh, ?_⟩
  simpa only [TM.liftCfgWith_input, TM.liftCfgWith_output, liftCfgWith_work_castAdd] using hpost

end Toda.Counting.LiftFrame

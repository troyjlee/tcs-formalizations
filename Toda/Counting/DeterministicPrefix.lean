import Toda.Counting.SelectiveBranch
import Complexitylib.Models.TuringMachine.Combinators.Internal.Seq
import Complexitylib.Asymptotics.PolyBound

/-!
# Deterministic preparation before a counting machine

An actual sequential machine runs a deterministic tape-preparation phase and
then a nondeterministic continuation. The selective-branch wrapper suppresses
duplicate paths throughout preparation, including the phase transition.
The transition has the same head-at-marker convention as upstream `seqTM`.
-/

namespace Toda.Counting.DeterministicPrefix

open Complexity

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- Fix one transition choice, retaining the source state type. -/
def choiceTM (N : NTM n) (b : Bool) : TM n where
  Q := N.Q
  qstart := N.qstart
  qhalt := N.qhalt
  δ := N.δ b
  δ_right_of_start := N.δ_right_of_start b

/-- Sequential composition before duplicate deterministic branches are removed. -/
def source (M : TM n) (N : NTM n) : NTM n where
  Q := Sum M.Q N.Q
  qstart := .inl M.qstart
  qhalt := .inr N.qhalt
  δ := fun b => (TM.seqTM M (choiceTM N b)).δ
  δ_right_of_start := fun b => (TM.seqTM M (choiceTM N b)).δ_right_of_start

/-- Only the continuation phase has genuine nondeterministic choices. -/
def branch (M : TM n) (N : NTM n) : SelectiveBranch.BranchTest (source M N) :=
  fun q _ _ _ => match q with | .inl _ => false | .inr _ => true

def machine (M : TM n) (N : NTM n) : NTM n :=
  SelectiveBranch.machine (source M N) (branch M N)

def first (M : TM n) (N : NTM n) (c : Cfg n M.Q) : Cfg n (source M N).Q :=
  ⟨.inl c.state, c.input, c.work, c.output⟩

def second (M : TM n) (N : NTM n) (c : Cfg n N.Q) : Cfg n (source M N).Q :=
  ⟨.inr c.state, c.input, c.work, c.output⟩

/-- The continuation entry configuration, including upstream's marker-head shift. -/
def continuation (M : TM n) (N : NTM n) (c : Cfg n M.Q) : Cfg n N.Q :=
  ⟨N.qstart, TM.transitionInput c.input,
    fun i => TM.transitionTape (c.work i), TM.transitionTape c.output⟩

@[simp] theorem not_halted_first (M : TM n) (N : NTM n) (c : Cfg n M.Q) :
    ¬ (source M N).halted (first M N c) := by
  simp [source, first, NTM.halted, Cfg.isHalted]

@[simp] theorem halted_second (M : TM n) (N : NTM n) (c : Cfg n N.Q) :
    (source M N).halted (second M N c) ↔ N.halted c := by
  simp [source, second, NTM.halted, Cfg.isHalted]

@[simp] theorem branching_first (M : TM n) (N : NTM n) (c : Cfg n M.Q) :
    SelectiveBranch.branching (source M N) (branch M N) (first M N c) = false := rfl

@[simp] theorem branching_second (M : TM n) (N : NTM n) (c : Cfg n N.Q) :
    SelectiveBranch.branching (source M N) (branch M N) (second M N c) = true := rfl

theorem trace_one_first (M : TM n) (N : NTM n) {c c' : Cfg n M.Q}
    (hs : M.step c = some c') (b : Bool) :
    (source M N).trace 1 (fun _ => b) (first M N c) = first M N c' := by
  have hn := TM.state_ne_qhalt_of_step hs
  simp only [TM.step, hn, ite_false, Option.some.injEq] at hs
  subst c'
  simp [NTM.trace, source, first, TM.seqTM, choiceTM, hn]

theorem trace_one_transition (M : TM n) (N : NTM n) (c : Cfg n M.Q)
    (hh : M.halted c) (b : Bool) :
    (source M N).trace 1 (fun _ => b) (first M N c) =
      second M N (continuation M N c) := by
  change c.state = M.qhalt at hh
  simp [NTM.trace, source, first, second, continuation, TM.seqTM, choiceTM, hh,
    TM.transitionInput, TM.transitionTape]

theorem trace_one_second (M : TM n) (N : NTM n) (c : Cfg n N.Q) (b : Bool) :
    (source M N).trace 1 (fun _ => b) (second M N c) =
      second M N (N.trace 1 (fun _ => b) c) := by
  by_cases hh : c.state = N.qhalt <;>
    simp [NTM.trace, source, second, TM.seqTM, choiceTM, hh]

theorem trace_second (M : TM n) (N : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n N.Q) :
    (source M N).trace T choices (second M N c) = second M N (N.trace T choices c) := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    rw [trace_succ_eq (source M N) T, trace_one_second, trace_succ_eq N T, ih]

theorem trace_first (M : TM n) (N : NTM n) {t : ℕ} {c d : Cfg n M.Q}
    (hr : M.reachesIn t c d) (choices : Fin t → Bool) :
    (source M N).trace t choices (first M N c) = first M N d := by
  induction hr with
  | zero => rfl
  | step hs hr ih =>
    rw [trace_succ_eq, trace_one_first M N hs]
    exact ih (Fin.tail choices)

theorem branchCount_second (M : TM n) (N : NTM n) (T : ℕ) (c : Cfg n N.Q) :
    SelectiveBranch.branchCount (source M N) (branch M N) T (second M N c) =
      N.acceptLeafCountFrom T c := by
  induction T generalizing c with
  | zero =>
    simp only [SelectiveBranch.branchCount, NTM.acceptLeafCountFrom, halted_second]
    rfl
  | succ T ih =>
    by_cases hh : N.halted c
    · rw [SelectiveBranch.branchCount, NTM.acceptLeafCountFrom,
        ite_eq_left ((halted_second M N c).mpr hh), ite_eq_left hh]
      rfl
    · simp only [SelectiveBranch.branchCount, NTM.acceptLeafCountFrom,
        halted_second, hh, ite_false, trace_one_second]
      rw [branching_second, ite_eq_left rfl]
      rw [ih, ih]

/-- Preparation and the one-step handoff contribute no extra accepting copies. -/
theorem branchCount_first (M : TM n) (N : NTM n) {t : ℕ} {c d : Cfg n M.Q}
    (hr : M.reachesIn t c d) (hh : M.halted d) (U : ℕ) :
    SelectiveBranch.branchCount (source M N) (branch M N) (t + 1 + U) (first M N c) =
      N.acceptLeafCountFrom U (continuation M N d) := by
  induction hr with
  | zero =>
    rw [show 0 + 1 + U = U + 1 by omega, SelectiveBranch.branchCount]
    simp only [not_halted_first, ite_false, branching_first,
      Bool.false_eq_true, ite_false, Nat.add_zero]
    rw [trace_one_transition M N _ hh, branchCount_second]
  | @step c e t d hs hr ih =>
    rw [show (t + 1) + 1 + U = (t + 1 + U) + 1 by omega,
      SelectiveBranch.branchCount]
    simp only [not_halted_first, ite_false, branching_first,
      Bool.false_eq_true, ite_false, Nat.add_zero]
    rw [trace_one_first M N hs]
    exact ih hh

/-- Exact accepting-leaf count for the concrete wrapped machine. -/
theorem acceptLeafCountFrom_first (M : TM n) (N : NTM n) {t : ℕ}
    {c d : Cfg n M.Q} (hr : M.reachesIn t c d) (hh : M.halted d)
    (hi : c.output.StartInvariant) (U : ℕ) :
    (machine M N).acceptLeafCountFrom (t + 1 + U)
      (SelectiveBranch.embed (source M N) (first M N c)) =
      N.acceptLeafCountFrom U (continuation M N d) := by
  change (SelectiveBranch.machine (source M N) (branch M N)).acceptLeafCountFrom _ _ = _
  rw [SelectiveBranch.acceptLeafCountFrom_embed _ _ _ _ hi,
    branchCount_first M N hr hh]

/-- Every source branch reaches the continuation after the same preparation. -/
theorem source_halted_trace (M : TM n) (N : NTM n) {t : ℕ} {c d : Cfg n M.Q}
    (hr : M.reachesIn t c d) (hh : M.halted d) (U : ℕ)
    (hcont : ∀ choices : Fin U → Bool,
      N.halted (N.trace U choices (continuation M N d))) :
    ∀ choices : Fin (t + 1 + U) → Bool,
      (source M N).halted ((source M N).trace (t + 1 + U) choices (first M N c)) := by
  rw [show t + 1 + U = t + (U + 1) by omega]
  intro choices
  rw [NTM.trace_add, trace_first M N hr, trace_succ_eq (source M N) U,
    trace_one_transition M N _ hh, trace_second, halted_second]
  exact hcont _

/-- A sufficient clock also covers every rejecting branch of the wrapper. -/
theorem halted_trace_first (M : TM n) (N : NTM n) {t : ℕ} {c d : Cfg n M.Q}
    (hr : M.reachesIn t c d) (hh : M.halted d) (hi : c.output.StartInvariant) (U : ℕ)
    (hcont : ∀ choices : Fin U → Bool,
      N.halted (N.trace U choices (continuation M N d))) :
    ∀ choices : Fin (2 * (t + 1 + U) + c.output.head + 2) → Bool,
      (machine M N).halted ((machine M N).trace
        (2 * (t + 1 + U) + c.output.head + 2) choices
        (SelectiveBranch.embed (source M N) (first M N c))) :=
  SelectiveBranch.halted_trace_embed _ _ _ _ hi (source_halted_trace M N hr hh U hcont)

/-- A larger preparation budget leaves the continuation count unchanged. -/
theorem branchCount_first_of_le (M : TM n) (N : NTM n) {t S : ℕ}
    {c d : Cfg n M.Q} (hr : M.reachesIn t c d) (hh : M.halted d) (hle : t ≤ S)
    (U : ℕ) (hcont : ∀ choices : Fin U → Bool,
      N.halted (N.trace U choices (continuation M N d))) :
    SelectiveBranch.branchCount (source M N) (branch M N) (S + 1 + U) (first M N c) =
      N.acceptLeafCountFrom U (continuation M N d) := by
  rw [SelectiveBranch.branchCount_eq_of_le_of_allChoicesHalt _ _
    (show t + 1 + U ≤ S + 1 + U by omega) _ (source_halted_trace M N hr hh U hcont)]
  exact branchCount_first M N hr hh U

/-- Deterministic polynomial-time tape preparation followed by a polynomially
bounded counting continuation gives membership in the unchanged machine #P class.
Both phases are actual machines; the premise specifies their verified behavior. -/
theorem mem_sharpP (M : TM n) (N : NTM n) (f : List Bool → ℕ)
    (S U : ℕ → ℕ) (hS : PolyBound S) (hU : PolyBound U)
    (hsetup : ∀ x, ∃ t d, t ≤ S x.length ∧ M.reachesIn t (M.initCfg x) d ∧ M.halted d ∧
      (∀ choices : Fin (U x.length) → Bool,
        N.halted (N.trace (U x.length) choices (continuation M N d))) ∧
      f x = N.acceptLeafCountFrom (U x.length) (continuation M N d)) :
    f ∈ SharpP := by
  have hclock : (source M N).AllPathsHaltIn (fun k => S k + 1 + U k) := by
    intro x choices
    obtain ⟨t, d, ht, hr, hh, hcont, _⟩ := hsetup x
    have hsmall := source_halted_trace M N hr hh (U x.length) hcont
    let choicePrefix : Fin (t + 1 + U x.length) → Bool :=
      fun i => choices ⟨i.val, by dsimp; omega⟩
    change (source M N).halted ((source M N).trace _ choices (first M N (M.initCfg x)))
    rw [(source M N).trace_mono (show t + 1 + U x.length ≤ S x.length + 1 + U x.length by omega)
      (choices := choicePrefix) (fun _ => rfl) (hsmall choicePrefix)]
    exact hsmall choicePrefix
  obtain ⟨degree, hpoly⟩ := ((hS.add (PolyBound.const 1)).add hU).bigO
  have hmem := SelectiveBranch.branchCount_mem_sharpP
    (source M N) (branch M N) (fun k => S k + 1 + U k) degree hclock hpoly
  have heq : f = fun x => SelectiveBranch.branchCount (source M N) (branch M N)
      (S x.length + 1 + U x.length) ((source M N).initCfg x) := by
    funext x
    obtain ⟨t, d, ht, hr, hh, hcont, hf⟩ := hsetup x
    exact hf.trans (branchCount_first_of_le M N hr hh ht (U x.length) hcont).symm
  rwa [heq]

end Toda.Counting.DeterministicPrefix

import Toda.Counting.GuessBits
import Toda.Counting.DeterministicBranch

/-!
# Count-preserving guessing followed by deterministic verification

This composes two actual machine constructions: guess each fixed-width string
once, then run a deterministic verifier with a single productive branch.
The exact accepting-leaf count is the number of guessed strings accepted by
the verifier at the specified clock.

The theorem starts with prepared tapes, including a unary guessing counter.
Loading these tapes from a standard input, computing the counter, and moving
the verifier's heads to its desired starting positions remain separate work.
-/

namespace Toda.Counting.GuessAndVerify

open Complexity
open scoped BigOperators

variable {n : ℕ}

/-- The concrete guess-and-verify NTM, before its input preparation is supplied. -/
def machine (M : TM n) (witness counter : Fin n) : NTM n :=
  GuessBits.machine (DeterministicBranch.machine M) witness counter

/-- Enter the guessing phase with the supplied tape contents and positions. -/
def enter (M : TM n) (witness counter : Fin n) (c : Cfg n M.Q) :
    Cfg n (machine M witness counter).Q :=
  GuessBits.enter (DeterministicBranch.machine M) witness counter
    (DeterministicBranch.embed M c)

/-- The deterministic verifier starts after the guessed bits have been written.
Its witness head is at the end of the generated block; a verifier may rewind it. -/
def verifierCfg (M : TM n) (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n M.Q) : Cfg n M.Q :=
  { GuessBits.afterChoices witness counter T choices c with state := M.qstart }

/-- Acceptance of a particular generated string by the deterministic verifier. -/
def AcceptsWitness (M : TM n) (witness counter : Fin n) (T U : ℕ)
    (c : Cfg n M.Q) (choices : Fin T → Bool) : Prop :=
  let final := M.toNTM.trace U (fun _ => false) (verifierCfg M witness counter T choices c)
  M.toNTM.halted final ∧ final.output.cells 1 = .one

instance (M : TM n) (witness counter : Fin n) (T U : ℕ) (c : Cfg n M.Q) :
    DecidablePred (AcceptsWitness M witness counter T U c) := by
  intro choices
  unfold AcceptsWitness
  infer_instance

theorem prepared_embed (M : TM n) (c : Cfg n M.Q) (hc : GuessBits.Prepared c) :
    GuessBits.Prepared (DeterministicBranch.embed M c) :=
  ⟨hc.input_nonstart, hc.work_invariant, hc.work_positive,
    hc.output_nonstart, hc.output_zero⟩

theorem afterChoices_embed (M : TM n) (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n M.Q) :
    GuessBits.afterChoices witness counter T choices (DeterministicBranch.embed M c) =
      DeterministicBranch.embed M (GuessBits.afterChoices witness counter T choices c) := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    simp only [GuessBits.afterChoices]
    rw [show GuessBits.writeGuess witness counter (choices 0) (DeterministicBranch.embed M c) =
      DeterministicBranch.embed M (GuessBits.writeGuess witness counter (choices 0) c) from rfl]
    exact ih (Fin.tail choices) _

theorem afterChoices_output {Q : Type} (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) :
    (GuessBits.afterChoices witness counter T choices c).output = c.output := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih => exact ih (Fin.tail choices) _

/-- The actual guessing and verification machine counts each accepted string
once, including when the deterministic verifier halts early. -/
theorem acceptLeafCountFrom_eq_card (M : TM n) (witness counter : Fin n)
    (hne : witness ≠ counter) (T U : ℕ) (c : Cfg n M.Q)
    (hc : GuessBits.Prepared c) (hcounter : GuessBits.CounterRemaining counter c T)
    (hi : c.output.StartInvariant) :
    (machine M witness counter).acceptLeafCountFrom (T + 1 + U) (enter M witness counter c) =
      (Finset.univ.filter (AcceptsWitness M witness counter T U c)).card := by
  change (GuessBits.machine (DeterministicBranch.machine M) witness counter).acceptLeafCountFrom
    (T + 1 + U) (GuessBits.enter _ _ _ (DeterministicBranch.embed M c)) = _
  rw [GuessBits.acceptLeafCountFrom_eq_sum _ _ _ hne T U _ (prepared_embed M c hc) hcounter]
  have hsum : (∑ choices : Fin T → Bool,
      (DeterministicBranch.machine M).acceptLeafCountFrom U
        { GuessBits.afterChoices witness counter T choices (DeterministicBranch.embed M c)
          with state := (DeterministicBranch.machine M).qstart }) =
      ∑ choices : Fin T → Bool, if AcceptsWitness M witness counter T U c choices
        then (1 : ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro choices _
    rw [afterChoices_embed]
    change (DeterministicBranch.machine M).acceptLeafCountFrom U
      (DeterministicBranch.embed M (verifierCfg M witness counter T choices c)) = _
    rw [DeterministicBranch.acceptLeafCountFrom_embed]
    · rfl
    · simpa only [verifierCfg, afterChoices_output] using hi
  rw [hsum]
  simp

/-- Padding the verifier clock past a halt preserves its acceptance verdict. -/
theorem acceptsWitness_iff_of_le (M : TM n) (witness counter : Fin n)
    (T U V : ℕ) (c : Cfg n M.Q) (choices : Fin T → Bool) (hle : U ≤ V)
    (hh : M.toNTM.halted
      (M.toNTM.trace U (fun _ => false) (verifierCfg M witness counter T choices c))) :
    AcceptsWitness M witness counter T V c choices ↔
      AcceptsWitness M witness counter T U c choices := by
  have heq := M.toNTM.trace_mono hle (choices' := fun _ => false) (fun _ => rfl) hh
  exact congrArg (fun final => M.toNTM.halted final ∧ final.output.cells 1 = .one) heq |>.to_iff

/-- All branches of the prepared guess-and-verify machine halt, including the
rejecting duplicates created while the deterministic verifier runs. -/
theorem halted_trace_enter (M : TM n) (witness counter : Fin n)
    (hne : witness ≠ counter) (T U : ℕ) (c : Cfg n M.Q)
    (hc : GuessBits.Prepared c) (hcounter : GuessBits.CounterRemaining counter c T)
    (hi : c.output.StartInvariant)
    (hh : ∀ choices : Fin T → Bool, M.toNTM.halted
      (M.toNTM.trace U (fun _ => false) (verifierCfg M witness counter T choices c))) :
    ∀ choices : Fin (T + 1 + (2 * U + c.output.head + 2)) → Bool,
      (machine M witness counter).halted
        ((machine M witness counter).trace (T + 1 + (2 * U + c.output.head + 2))
          choices (enter M witness counter c)) := by
  apply GuessBits.halted_trace_enter _ _ _ hne T _ _ (prepared_embed M c hc) hcounter
  intro bits choices
  rw [afterChoices_embed]
  change (DeterministicBranch.machine M).halted
    ((DeterministicBranch.machine M).trace _ choices
      (DeterministicBranch.embed M (verifierCfg M witness counter T bits c)))
  have hout : (verifierCfg M witness counter T bits c).output = c.output :=
    afterChoices_output witness counter T bits c
  have hrun := DeterministicBranch.halted_trace_embed M U
    (verifierCfg M witness counter T bits c) (hout.symm ▸ hi) (hh bits)
  have hhead : (verifierCfg M witness counter T bits c).output.head = c.output.head :=
    congrArg Tape.head hout
  rw [hhead] at hrun
  exact hrun choices

/-- The clock that covers every cleanup branch still counts exactly the
witnesses accepted at the original deterministic verifier clock. -/
theorem acceptLeafCountFrom_totalClock_eq_card (M : TM n) (witness counter : Fin n)
    (hne : witness ≠ counter) (T U : ℕ) (c : Cfg n M.Q)
    (hc : GuessBits.Prepared c) (hcounter : GuessBits.CounterRemaining counter c T)
    (hi : c.output.StartInvariant)
    (hh : ∀ choices : Fin T → Bool, M.toNTM.halted
      (M.toNTM.trace U (fun _ => false) (verifierCfg M witness counter T choices c))) :
    (machine M witness counter).acceptLeafCountFrom
      (T + 1 + (2 * U + c.output.head + 2)) (enter M witness counter c) =
      (Finset.univ.filter (AcceptsWitness M witness counter T U c)).card := by
  rw [acceptLeafCountFrom_eq_card M witness counter hne T _ c hc hcounter hi]
  congr 1
  apply Finset.filter_congr
  intro choices _
  exact acceptsWitness_iff_of_le M witness counter T U _ c choices (by omega) (hh choices)

end Toda.Counting.GuessAndVerify

import Toda.Counting.CanonicalWitness

/-!
# Expanding accepting-leaf counts over a finite prefix

If no computation branch halts before depth `prefixLength`, the accepting-leaf
count splits into a sum over all choice prefixes of that length. A general
version also permits early halting: it sums only over prefixes with canonical
false padding, so an early-halting leaf is counted exactly once.
-/

namespace Toda.Counting

open Complexity
open scoped BigOperators

variable {n : ℕ}

/-- Every computation branch is still running at every depth strictly below
the indicated prefix length. Halting exactly at that length is allowed. -/
def NoHaltBefore (tm : NTM n) (prefixLength : ℕ) (c : Cfg n tm.Q) : Prop :=
  ∀ length < prefixLength, ∀ choices : Fin length → Bool,
    ¬ tm.halted (tm.trace length choices c)

@[simp] theorem noHaltBefore_zero (tm : NTM n) (c : Cfg n tm.Q) :
    NoHaltBefore tm 0 c := by
  intro length hlength
  omega

/-- A nonhalting-prefix bound also holds for every shorter prefix. -/
theorem NoHaltBefore.mono {tm : NTM n} {shorter longer : ℕ} {c : Cfg n tm.Q}
    (h : NoHaltBefore tm longer c) (hle : shorter ≤ longer) :
    NoHaltBefore tm shorter c := by
  intro length hlength choices
  exact h length (lt_of_lt_of_le hlength hle) choices

/-- Nonhalting through a positive prefix means the root is not halted and
the same condition holds below each of its two immediate branches. -/
theorem noHaltBefore_succ_iff (tm : NTM n) (prefixLength : ℕ) (c : Cfg n tm.Q) :
    NoHaltBefore tm (prefixLength + 1) c ↔
      ¬ tm.halted c ∧ ∀ bit : Bool,
        NoHaltBefore tm prefixLength (tm.trace 1 (fun _ => bit) c) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [NTM.trace] using h 0 (by omega) (fun _ => false)
    · intro bit length hlength choices
      have hnext := h (length + 1) (by omega) (Fin.cons bit choices)
      rw [trace_succ_eq] at hnext
      simpa only [Fin.cons_zero, Fin.tail_cons] using hnext
  · rintro ⟨hroot, hbranch⟩ length hlength choices
    cases length with
    | zero => simpa only [NTM.trace] using hroot
    | succ length =>
        rw [trace_succ_eq]
        exact hbranch (choices 0) length (by omega) (Fin.tail choices)

private def prefixChoicesSuccEquiv (length : ℕ) :
    (Fin (length + 1) → Bool) ≃ Bool × (Fin length → Bool) where
  toFun choices := (choices 0, Fin.tail choices)
  invFun choices := Fin.cons choices.1 choices.2
  left_inv choices := Fin.cons_self_tail choices
  right_inv choices := by rcases choices with ⟨bit, rest⟩; simp

/-- Split a sum over Boolean choice tapes into its false and true first-bit
branches. This is valid for any additive commutative monoid. -/
theorem sum_bool_choices_succ {M : Type*} [AddCommMonoid M] (length : ℕ)
    (f : (Fin (length + 1) → Bool) → M) :
    (∑ choices, f choices) =
      (∑ rest, f (Fin.cons false rest)) + (∑ rest, f (Fin.cons true rest)) := by
  calc
    (∑ choices, f choices) =
        ∑ choices : Bool × (Fin length → Bool),
          f (Fin.cons choices.1 choices.2) :=
      (Equiv.sum_comp (prefixChoicesSuccEquiv length).symm _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      exact add_comm _ _

instance instDecidableZeroPaddedFrom (tm : NTM n) (length : ℕ) :
    ∀ c choices, Decidable (zeroPaddedFrom tm length c choices) := by
  induction length with
  | zero => intro c choices; unfold zeroPaddedFrom; infer_instance
  | succ length ih =>
      intro c choices
      unfold zeroPaddedFrom
      letI := ih (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)
      infer_instance

/-- Before any branch can halt, every choice prefix satisfies the canonical
padding condition, because there are no unused choices yet. -/
theorem zeroPaddedFrom_of_noHaltBefore (tm : NTM n) (prefixLength : ℕ)
    (c : Cfg n tm.Q) (h : NoHaltBefore tm prefixLength c)
    (choices : Fin prefixLength → Bool) :
    zeroPaddedFrom tm prefixLength c choices := by
  induction prefixLength generalizing c with
  | zero => trivial
  | succ prefixLength ih =>
      obtain ⟨hroot, hbranch⟩ := (noHaltBefore_succ_iff tm prefixLength c).mp h
      rw [zeroPaddedFrom, ite_eq_right hroot]
      exact ih _ (hbranch (choices 0)) (Fin.tail choices)

/-- Expand a leaf count through a finite prefix, retaining only canonical
prefixes when early halting leaves unused choices. No nonhalting assumption
is needed for this form. -/
theorem acceptLeafCountFrom_prefix_expansion_canonical (tm : NTM n)
    (prefixLength suffixLength : ℕ) (c : Cfg n tm.Q) :
    tm.acceptLeafCountFrom (prefixLength + suffixLength) c =
      ∑ choices : Fin prefixLength → Bool,
        if zeroPaddedFrom tm prefixLength c choices then
          tm.acceptLeafCountFrom suffixLength (tm.trace prefixLength choices c)
        else 0 := by
  induction prefixLength generalizing c with
  | zero => simp [zeroPaddedFrom, NTM.trace]
  | succ prefixLength ih =>
      by_cases hhalt : tm.halted c
      · have hcount (length : ℕ) : tm.acceptLeafCountFrom length c =
            if c.output.cells 1 = Γ.one then 1 else 0 := by
          cases length with
          | zero =>
              simp only [NTM.acceptLeafCountFrom, NTM.halted, Cfg.isHalted] at *
              simp only [hhalt, true_and]
          | succ length => rw [NTM.acceptLeafCountFrom, ite_eq_left hhalt]
        have htrace (choices : Fin (prefixLength + 1) → Bool) :
            tm.trace (prefixLength + 1) choices c = c := tm.trace_halted _ _ hhalt
        simp only [zeroPaddedFrom, ite_eq_left hhalt, htrace, hcount]
        simp
      · rw [Nat.succ_add, NTM.acceptLeafCountFrom, ite_eq_right hhalt,
          sum_bool_choices_succ, ih, ih]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro choices _
          rw [trace_succ_eq tm prefixLength c (Fin.cons false choices)]
          simp only [zeroPaddedFrom, ite_eq_right hhalt, Fin.cons_zero, Fin.tail_cons]
        · apply Finset.sum_congr rfl
          intro choices _
          rw [trace_succ_eq tm prefixLength c (Fin.cons true choices)]
          simp only [zeroPaddedFrom, ite_eq_right hhalt, Fin.cons_zero, Fin.tail_cons]

/-- If every branch runs through a finite prefix, its accepting-leaf count is
the sum of the suffix counts over all Boolean prefixes, with no multiplicity
correction. Halting at the prefix boundary is permitted. -/
theorem acceptLeafCountFrom_prefix_expansion (tm : NTM n)
    (prefixLength suffixLength : ℕ) (c : Cfg n tm.Q)
    (h : NoHaltBefore tm prefixLength c) :
    tm.acceptLeafCountFrom (prefixLength + suffixLength) c =
      ∑ choices : Fin prefixLength → Bool,
        tm.acceptLeafCountFrom suffixLength (tm.trace prefixLength choices c) := by
  rw [acceptLeafCountFrom_prefix_expansion_canonical]
  apply Finset.sum_congr rfl
  intro choices _
  rw [ite_eq_left (zeroPaddedFrom_of_noHaltBefore tm prefixLength c h choices)]

end Toda.Counting

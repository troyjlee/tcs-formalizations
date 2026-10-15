import Complexitylib.Classes.SharpP
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Canonical fixed-width witnesses for accepting NTM leaves

A halted accepting computation contributes one leaf even when its clock has
unused steps. We represent that leaf by its actual choices followed by false
bits. Requiring this unique padding removes the multiplicity of fixed-clock
random tapes without changing the upstream accepting-leaf convention.

This file proves the exact finite counting identity and its trace semantics.
It does not yet prove that the witness predicate has a polynomial-time verifier.
-/

namespace Toda.Counting

open Complexity
open scoped BigOperators

variable {n : ℕ}

/-- Accepting choice tapes with the unique all-false padding after early halt. -/
def canonicalWitnessFrom (tm : NTM n) :
    (T : ℕ) → Cfg n tm.Q → (Fin T → Bool) → Prop
  | 0, c, _ => tm.halted c ∧ c.output.cells 1 = Γ.one
  | T + 1, c, choices =>
      if tm.halted c then
        c.output.cells 1 = Γ.one ∧ choices = fun _ => false
      else
        canonicalWitnessFrom tm T (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)

instance instDecidableCanonicalWitnessFrom (tm : NTM n) (T : ℕ) :
    ∀ c choices, Decidable (canonicalWitnessFrom tm T c choices) := by
  induction T with
  | zero => intro c choices; unfold canonicalWitnessFrom; infer_instance
  | succ T ih =>
      intro c choices
      unfold canonicalWitnessFrom
      letI := ih (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)
      infer_instance

/-- All choices remaining when the machine first halts must be false. -/
def zeroPaddedFrom (tm : NTM n) :
    (T : ℕ) → Cfg n tm.Q → (Fin T → Bool) → Prop
  | 0, _, _ => True
  | T + 1, c, choices =>
      if tm.halted c then choices = fun _ => false
      else zeroPaddedFrom tm T (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)

/-- Factor the upstream trace into its first choice and remaining choices. -/
theorem trace_succ_eq (tm : NTM n) (T : ℕ) (c : Cfg n tm.Q)
    (choices : Fin (T + 1) → Bool) :
    tm.trace (T + 1) choices c =
      tm.trace T (Fin.tail choices) (tm.trace 1 (fun _ => choices 0) c) := by
  by_cases hc : tm.halted c
  · rw [tm.trace_halted _ _ hc, tm.trace_halted _ _ hc, tm.trace_halted _ _ hc]
  · simp only [NTM.trace, hc, ite_false]
    rfl

/-- The recursive witness predicate is standard trace acceptance plus padding. -/
theorem canonicalWitnessFrom_iff_trace (tm : NTM n) (T : ℕ)
    (c : Cfg n tm.Q) (choices : Fin T → Bool) :
    canonicalWitnessFrom tm T c choices ↔
      tm.halted (tm.trace T choices c) ∧
      (tm.trace T choices c).output.cells 1 = Γ.one ∧
      zeroPaddedFrom tm T c choices := by
  induction T generalizing c with
  | zero => simp [canonicalWitnessFrom, zeroPaddedFrom, NTM.trace]
  | succ T ih =>
      by_cases hc : tm.halted c
      · rw [canonicalWitnessFrom, ite_eq_left hc, zeroPaddedFrom, ite_eq_left hc,
          tm.trace_halted _ _ hc]
        exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
      · rw [trace_succ_eq]
        simpa only [canonicalWitnessFrom, zeroPaddedFrom, hc, ite_false] using
          ih (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)

/-- Replace only the unused choices after the first halt by false bits. -/
def canonicalizeChoicesFrom (tm : NTM n) :
    (T : ℕ) → Cfg n tm.Q → (Fin T → Bool) → (Fin T → Bool)
  | 0, _, choices => choices
  | T + 1, c, choices =>
      if tm.halted c then fun _ => false
      else Fin.cons (choices 0)
        (canonicalizeChoicesFrom tm T (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices))

/-- Removing unused random bits does not change the upstream trace. -/
theorem trace_canonicalizeChoicesFrom (tm : NTM n) (T : ℕ)
    (c : Cfg n tm.Q) (choices : Fin T → Bool) :
    tm.trace T (canonicalizeChoicesFrom tm T c choices) c = tm.trace T choices c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      by_cases hc : tm.halted c
      · exact (tm.trace_halted _ _ hc).trans (tm.trace_halted _ _ hc).symm
      · rw [canonicalizeChoicesFrom, ite_eq_right hc,
          trace_succ_eq tm T, trace_succ_eq tm T]
        simp only [Fin.cons_zero, Fin.tail_cons]
        exact ih (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)

/-- Canonicalization always produces the required unique padding. -/
theorem zeroPaddedFrom_canonicalizeChoicesFrom (tm : NTM n) (T : ℕ)
    (c : Cfg n tm.Q) (choices : Fin T → Bool) :
    zeroPaddedFrom tm T c (canonicalizeChoicesFrom tm T c choices) := by
  induction T generalizing c with
  | zero => trivial
  | succ T ih =>
      by_cases hc : tm.halted c
      · rw [zeroPaddedFrom, ite_eq_left hc, canonicalizeChoicesFrom, ite_eq_left hc]
      · rw [zeroPaddedFrom, ite_eq_right hc, canonicalizeChoicesFrom, ite_eq_right hc]
        simpa only [Fin.cons_zero, Fin.tail_cons] using
          ih (tm.trace 1 (fun _ => choices 0) c) (Fin.tail choices)

/-- Every accepting tape becomes a canonical accepting witness, and conversely. -/
theorem canonicalWitnessFrom_canonicalizeChoicesFrom_iff (tm : NTM n) (T : ℕ)
    (c : Cfg n tm.Q) (choices : Fin T → Bool) :
    canonicalWitnessFrom tm T c (canonicalizeChoicesFrom tm T c choices) ↔
      tm.halted (tm.trace T choices c) ∧ (tm.trace T choices c).output.cells 1 = Γ.one := by
  rw [canonicalWitnessFrom_iff_trace, trace_canonicalizeChoicesFrom]
  simp only [zeroPaddedFrom_canonicalizeChoicesFrom, and_true]

/-- The finite set of canonical tapes encoding accepting leaves below a clock. -/
def canonicalWitnessesFrom (tm : NTM n) (T : ℕ) (c : Cfg n tm.Q) :
    Finset (Fin T → Bool) := Finset.univ.filter (canonicalWitnessFrom tm T c)

@[simp] theorem mem_canonicalWitnessesFrom (tm : NTM n) (T : ℕ)
    (c : Cfg n tm.Q) (choices : Fin T → Bool) :
    choices ∈ canonicalWitnessesFrom tm T c ↔ canonicalWitnessFrom tm T c choices := by
  simp [canonicalWitnessesFrom]

private def choicesSuccEquiv (T : ℕ) :
    (Fin (T + 1) → Bool) ≃ Bool × (Fin T → Bool) where
  toFun choices := (choices 0, Fin.tail choices)
  invFun choices := Fin.cons choices.1 choices.2
  left_inv choices := Fin.cons_self_tail choices
  right_inv choices := by rcases choices with ⟨b, rest⟩; simp

private theorem card_filter_choices_succ (T : ℕ) (p : (Fin (T + 1) → Bool) → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter fun rest => p (Fin.cons false rest)).card +
      (Finset.univ.filter fun rest => p (Fin.cons true rest)).card := by
  have hsum {α : Type} [Fintype α] (r : α → Prop) [DecidablePred r] :
      (Finset.univ.filter r).card = ∑ a, if r a then (1 : ℕ) else 0 := by
    simp
  rw [hsum p, hsum (fun rest => p (Fin.cons false rest)),
    hsum (fun rest => p (Fin.cons true rest))]
  calc
    (∑ choices, if p choices then 1 else 0) =
        ∑ choices : Bool × (Fin T → Bool), if p (Fin.cons choices.1 choices.2) then 1 else 0 :=
      (Equiv.sum_comp (choicesSuccEquiv T).symm _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      exact Nat.add_comm _ _

/-- Canonical padded witnesses count each upstream accepting leaf exactly once. -/
theorem card_canonicalWitnessesFrom (tm : NTM n) (T : ℕ) (c : Cfg n tm.Q) :
    (canonicalWitnessesFrom tm T c).card = tm.acceptLeafCountFrom T c := by
  induction T generalizing c with
  | zero =>
      by_cases hc : c.state = tm.qhalt <;> by_cases hout : c.output.cells 1 = Γ.one <;>
        simp only [canonicalWitnessesFrom, canonicalWitnessFrom, NTM.acceptLeafCountFrom,
          NTM.halted, Cfg.isHalted, hc, hout, and_self, and_false, and_true, ite_true,
          ite_false] <;> simp
  | succ T ih =>
      by_cases hc : c.state = tm.qhalt
      · by_cases hout : c.output.cells 1 = Γ.one
        · simp only [canonicalWitnessesFrom, canonicalWitnessFrom, NTM.acceptLeafCountFrom,
            NTM.halted, Cfg.isHalted, hc, hout, ite_true, true_and]
          simp [Finset.filter_eq']
        · simp only [canonicalWitnessesFrom, canonicalWitnessFrom, NTM.acceptLeafCountFrom,
            NTM.halted, Cfg.isHalted, hc, hout, ite_true, ite_false, false_and]
          simp
      · rw [canonicalWitnessesFrom, card_filter_choices_succ]
        simp only [canonicalWitnessFrom, NTM.halted, Cfg.isHalted, hc, ite_false,
          Fin.cons_zero, Fin.tail_cons,
          NTM.acceptLeafCountFrom]
        exact congrArg₂ (· + ·) (ih _) (ih _)

/-- Canonical accepting witnesses for an input, at a fixed witness width. -/
def canonicalWitnesses (tm : NTM n) (x : List Bool) (T : ℕ) :
    Finset (Fin T → Bool) := canonicalWitnessesFrom tm T (tm.initCfg x)

/-- Exact input-level bridge to the unchanged `NTM.acceptLeafCount` definition. -/
theorem card_canonicalWitnesses (tm : NTM n) (x : List Bool) (T : ℕ) :
    (canonicalWitnesses tm x T).card = tm.acceptLeafCount x T :=
  card_canonicalWitnessesFrom tm T (tm.initCfg x)

/-- A canonical witness gives an accepting trace within its fixed width. -/
theorem acceptsInTime_of_mem_canonicalWitnesses (tm : NTM n) (x : List Bool) (T : ℕ)
    (choices : Fin T → Bool) (h : choices ∈ canonicalWitnesses tm x T) :
    tm.AcceptsInTime x T := by
  have hc := (canonicalWitnessFrom_iff_trace tm T (tm.initCfg x) choices).mp
    ((mem_canonicalWitnessesFrom tm T (tm.initCfg x) choices).mp h)
  exact ⟨choices, hc.1, hc.2.1⟩

/-- Canonical tapes represent exactly the accepting computations within the clock. -/
theorem canonicalWitnesses_nonempty_iff (tm : NTM n) (x : List Bool) (T : ℕ) :
    (canonicalWitnesses tm x T).Nonempty ↔ tm.AcceptsInTime x T := by
  constructor
  · rintro ⟨choices, hchoices⟩
    exact acceptsInTime_of_mem_canonicalWitnesses tm x T choices hchoices
  · rintro ⟨choices, hhalt, hout⟩
    refine ⟨canonicalizeChoicesFrom tm T (tm.initCfg x) choices, ?_⟩
    apply (mem_canonicalWitnessesFrom tm T (tm.initCfg x) _).mpr
    exact (canonicalWitnessFrom_canonicalizeChoicesFrom_iff tm T (tm.initCfg x) choices).mpr
      ⟨hhalt, hout⟩

/-- The same canonical witnesses encoded as ordinary binary words. -/
def canonicalWitnessLists (tm : NTM n) (x : List Bool) (T : ℕ) : Finset (List Bool) :=
  (canonicalWitnesses tm x T).image List.ofFn

/-- Encoding finite tapes as words preserves the accepting-leaf count exactly. -/
theorem card_canonicalWitnessLists (tm : NTM n) (x : List Bool) (T : ℕ) :
    (canonicalWitnessLists tm x T).card = tm.acceptLeafCount x T := by
  rw [canonicalWitnessLists, Finset.card_image_of_injective _ List.ofFn_injective,
    card_canonicalWitnesses]

/-- Every canonical binary word has the prescribed witness length. -/
theorem length_of_mem_canonicalWitnessLists (tm : NTM n) (x : List Bool) (T : ℕ)
    (w : List Bool) (hw : w ∈ canonicalWitnessLists tm x T) : w.length = T := by
  obtain ⟨choices, _, rfl⟩ := Finset.mem_image.mp hw
  exact List.length_ofFn

end Toda.Counting

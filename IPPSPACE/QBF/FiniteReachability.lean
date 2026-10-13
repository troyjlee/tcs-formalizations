/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Finite-state bounds for reachability

Every reachable state in a finite graph can be reached using at most the number
of states. Allowing idle steps pads such a path to any larger exact length.
This is the finite-state ingredient for a configuration-reachability reduction;
it does not supply a Turing-machine configuration encoding.
-/

namespace IPPSPACE

/-- A path containing exactly `n` edges of the given relation. -/
def pathLength {α : Type*} (edge : α → α → Prop) : ℕ → α → α → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ c, pathLength edge n a c ∧ edge c b

/-- Permit the computation to idle without changing its state. -/
def stutterEdge {α : Type*} (edge : α → α → Prop) (a b : α) : Prop :=
  a = b ∨ edge a b

theorem pathLength_add {α : Type*} (edge : α → α → Prop) (n m : ℕ) (a b : α) :
    pathLength edge (n + m) a b ↔
      ∃ c, pathLength edge n a c ∧ pathLength edge m c b := by
  induction m generalizing b with
  | zero => simp [pathLength]
  | succ m ih =>
    change (∃ d, pathLength edge (n + m) a d ∧ edge d b) ↔
      ∃ c, pathLength edge n a c ∧ ∃ d, pathLength edge m c d ∧ edge d b
    constructor
    · rintro ⟨d, had, hdb⟩
      obtain ⟨c, hac, hcd⟩ := (ih d).mp had
      exact ⟨c, hac, d, hcd, hdb⟩
    · rintro ⟨c, hac, d, hcd, hdb⟩
      exact ⟨d, (ih d).mpr ⟨c, hac, hcd⟩, hdb⟩

theorem pathLength_stutter_refl {α : Type*} (edge : α → α → Prop) (n : ℕ) (a : α) :
    pathLength (stutterEdge edge) n a a := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨a, ih, Or.inl rfl⟩

theorem pathLength_stutter_mono {α : Type*} (edge : α → α → Prop) (a b : α)
    {n m : ℕ} (hnm : n ≤ m) :
    pathLength (stutterEdge edge) n a b → pathLength (stutterEdge edge) m a b := by
  have hm : Monotone (fun k => pathLength (stutterEdge edge) k a b) :=
    monotone_nat_of_le_succ (fun k h => ⟨b, h, Or.inl rfl⟩)
  exact hm hnm

theorem pathLength_stutter_reachable {α : Type*} (edge : α → α → Prop)
    (n : ℕ) (a b : α) (h : pathLength (stutterEdge edge) n a b) :
    Relation.ReflTransGen edge a b := by
  induction n generalizing b with
  | zero => cases h; exact .refl
  | succ n ih =>
    obtain ⟨c, hac, hcb⟩ := h
    rcases hcb with rfl | hcb
    · exact ih c hac
    · exact (ih c hac).tail hcb

private theorem pathLength_stable_reachable {α : Type*} (edge : α → α → Prop)
    (n : ℕ) (a : α)
    (hstable : ∀ b, pathLength (stutterEdge edge) (n + 1) a b →
      pathLength (stutterEdge edge) n a b) (b : α)
    (h : Relation.ReflTransGen edge a b) : pathLength (stutterEdge edge) n a b := by
  induction h with
  | refl => exact pathLength_stutter_refl edge n a
  | @tail b c _ hbc ih => exact hstable c ⟨b, ih, Or.inr hbc⟩

/-- The finite reachability saturation bound, proved by counting strictly
growing reachable sets until they stabilize. -/
theorem reachable_pathLength_card {α : Type*} [Fintype α] (edge : α → α → Prop)
    (a b : α) (h : Relation.ReflTransGen edge a b) :
    pathLength (stutterEdge edge) (Fintype.card α) a b := by
  classical
  let states (n : ℕ) := Finset.univ.filter (pathLength (stutterEdge edge) n a)
  have hmem (n : ℕ) (c : α) : c ∈ states n ↔ pathLength (stutterEdge edge) n a c := by
    simp [states]
  have hsub (n : ℕ) : states n ⊆ states (n + 1) := by
    intro c hc
    exact (hmem _ _).mpr (pathLength_stutter_mono edge a c (by omega) ((hmem _ _).mp hc))
  by_contra hnot
  have hstrict (n : ℕ) (hn : n < Fintype.card α) : (states n).card < (states (n + 1)).card := by
    apply Finset.card_lt_card
    refine ⟨hsub n, ?_⟩
    intro hrev
    have hstable : ∀ c, pathLength (stutterEdge edge) (n + 1) a c →
        pathLength (stutterEdge edge) n a c := by
      intro c hc
      exact (hmem _ _).mp (hrev ((hmem _ _).mpr hc))
    exact hnot (pathLength_stutter_mono edge a b (by omega)
      (pathLength_stable_reachable edge n a hstable b h))
  have hcard (n : ℕ) (hn : n ≤ Fintype.card α) : n + 1 ≤ (states n).card := by
    induction n with
    | zero =>
      have hpos := Finset.card_pos.mpr (show (states 0).Nonempty from
        ⟨a, (hmem 0 a).mpr rfl⟩)
      omega
    | succ n ih =>
      have hprev := ih (by omega)
      have hnext := hstrict n (by omega)
      omega
  have hlarge := hcard (Fintype.card α) le_rfl
  have hsmall := Finset.card_le_univ (states (Fintype.card α))
  omega

/-- Any larger exact horizon suffices once idle steps are permitted. -/
theorem reachable_iff_pathLength {α : Type*} [Fintype α] (edge : α → α → Prop)
    (a b : α) (T : ℕ) (hT : Fintype.card α ≤ T) :
    Relation.ReflTransGen edge a b ↔ pathLength (stutterEdge edge) T a b := by
  constructor
  · intro h
    exact pathLength_stutter_mono edge a b hT (reachable_pathLength_card edge a b h)
  · exact pathLength_stutter_reachable edge T a b

/-- A `w`-bit configuration space needs at most `2^w` stuttering steps. -/
theorem bitStates_reachable_iff_pathLength (w : ℕ)
    (edge : (Fin w → Bool) → (Fin w → Bool) → Prop) (a b : Fin w → Bool) :
    Relation.ReflTransGen edge a b ↔ pathLength (stutterEdge edge) (2 ^ w) a b := by
  apply reachable_iff_pathLength
  simp

end IPPSPACE

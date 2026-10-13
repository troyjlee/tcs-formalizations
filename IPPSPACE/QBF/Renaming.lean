/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Encoding
import Mathlib.Data.Finset.Image

/-!
# Capture-safe renaming of upstream QBF syntax

Uniform injective renaming transports assignments exactly, including all bound
variables. The finite set and maximum below include binders as well as variable
occurrences, so a fresh name cannot introduce variable capture.
-/

namespace IPPSPACE

open Complexity

/-- All variable names, including names that occur only as binders. -/
def qbfNames : QBF → Finset ℕ
  | .var i => {i}
  | .tru | .fls => ∅
  | .neg φ => qbfNames φ
  | .conj φ ψ | .disj φ ψ => qbfNames φ ∪ qbfNames ψ
  | .ex i φ | .all i φ => insert i (qbfNames φ)

theorem freeVars_subset_qbfNames (φ : QBF) : φ.freeVars ⊆ qbfNames φ := by
  induction φ with
  | var i => exact Finset.Subset.refl _
  | tru => exact Finset.Subset.refl _
  | fls => exact Finset.Subset.refl _
  | neg φ ih => exact ih
  | conj φ ψ ihφ ihψ => exact Finset.union_subset_union ihφ ihψ
  | disj φ ψ ihφ ihψ => exact Finset.union_subset_union ihφ ihψ
  | ex i φ ih => exact (Finset.sdiff_subset).trans (ih.trans (Finset.subset_insert _ _))
  | all i φ ih => exact (Finset.sdiff_subset).trans (ih.trans (Finset.subset_insert _ _))

theorem qbfNames_eq_freeVars_of_quantifierFree (φ : QBF) (hφ : φ.QuantifierFree) :
    qbfNames φ = φ.freeVars := by
  induction φ with
  | var i => rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => exact ih hφ
  | conj φ ψ ihφ ihψ =>
    have hs := QBF.quantifierFree_conj.mp hφ
    simp [qbfNames, QBF.freeVars, ihφ hs.1, ihψ hs.2]
  | disj φ ψ ihφ ihψ =>
    have hs : φ.QuantifierFree ∧ ψ.QuantifierFree := by
      simpa [QBF.QuantifierFree, QBF.quantDepth, Nat.max_eq_zero_iff] using hφ
    simp [qbfNames, QBF.freeVars, ihφ hs.1, ihψ hs.2]
  | ex i φ => simp [QBF.QuantifierFree, QBF.quantDepth] at hφ
  | all i φ => simp [QBF.QuantifierFree, QBF.quantDepth] at hφ

/-- The largest name in the syntax; the empty-name cases use zero. -/
def qbfMaxVar : QBF → ℕ
  | .var i => i
  | .tru | .fls => 0
  | .neg φ => qbfMaxVar φ
  | .conj φ ψ | .disj φ ψ => max (qbfMaxVar φ) (qbfMaxVar ψ)
  | .ex i φ | .all i φ => max i (qbfMaxVar φ)

theorem le_qbfMaxVar_of_mem (φ : QBF) (i : ℕ) (hi : i ∈ qbfNames φ) :
    i ≤ qbfMaxVar φ := by
  induction φ with
  | var j =>
    have : i = j := Finset.mem_singleton.mp hi
    subst i
    exact Nat.le_refl _
  | tru => simp [qbfNames] at hi
  | fls => simp [qbfNames] at hi
  | neg φ ih => exact ih hi
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (ihφ hi).trans (Nat.le_max_left _ _)
    · exact (ihψ hi).trans (Nat.le_max_right _ _)
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (ihφ hi).trans (Nat.le_max_left _ _)
    · exact (ihψ hi).trans (Nat.le_max_right _ _)
  | ex j φ ih =>
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Nat.le_max_left _ _
    · exact (ih hi).trans (Nat.le_max_right _ _)
  | all j φ ih =>
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Nat.le_max_left _ _
    · exact (ih hi).trans (Nat.le_max_right _ _)

theorem not_mem_qbfNames_of_max_lt (φ : QBF) (i : ℕ) (hi : qbfMaxVar φ < i) :
    i ∉ qbfNames φ := fun h => Nat.not_le_of_gt hi (le_qbfMaxVar_of_mem φ i h)

theorem qbfMaxVar_le_of_name_bound (φ : QBF) (B : ℕ)
    (h : ∀ i ∈ qbfNames φ, i ≤ B) : qbfMaxVar φ ≤ B := by
  induction φ with
  | var i => exact h i (Finset.mem_singleton_self _)
  | tru => exact Nat.zero_le _
  | fls => exact Nat.zero_le _
  | neg φ ih => exact ih h
  | conj φ ψ ihφ ihψ =>
    exact max_le (ihφ (fun i hi => h i (Finset.mem_union_left _ hi)))
      (ihψ (fun i hi => h i (Finset.mem_union_right _ hi)))
  | disj φ ψ ihφ ihψ =>
    exact max_le (ihφ (fun i hi => h i (Finset.mem_union_left _ hi)))
      (ihψ (fun i hi => h i (Finset.mem_union_right _ hi)))
  | ex i φ ih =>
    exact max_le (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
  | all i φ ih =>
    exact max_le (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Rename every variable occurrence and binder using one map. -/
def renameQBF (f : ℕ → ℕ) : QBF → QBF
  | .var i => .var (f i)
  | .tru => .tru
  | .fls => .fls
  | .neg φ => .neg (renameQBF f φ)
  | .conj φ ψ => .conj (renameQBF f φ) (renameQBF f ψ)
  | .disj φ ψ => .disj (renameQBF f φ) (renameQBF f ψ)
  | .ex i φ => .ex (f i) (renameQBF f φ)
  | .all i φ => .all (f i) (renameQBF f φ)

@[simp] theorem nodeCount_renameQBF (f : ℕ → ℕ) (φ : QBF) :
    nodeCount (renameQBF f φ) = nodeCount φ := by
  induction φ <;> simp_all [renameQBF, nodeCount]

@[simp] theorem quantDepth_renameQBF (f : ℕ → ℕ) (φ : QBF) :
    (renameQBF f φ).quantDepth = φ.quantDepth := by
  induction φ <;> simp_all [renameQBF, QBF.quantDepth]

@[simp] theorem qbfNames_renameQBF (f : ℕ → ℕ) (φ : QBF) :
    qbfNames (renameQBF f φ) = (qbfNames φ).image f := by
  induction φ <;> simp_all [renameQBF, qbfNames, Finset.image_union]

/-- Injectivity prevents a renamed binder from capturing a different variable. -/
theorem eval_renameQBF (f : ℕ → ℕ) (hf : Function.Injective f) (φ : QBF) (x : ℕ → Bool) :
    (renameQBF f φ).eval x = φ.eval (x ∘ f) := by
  induction φ generalizing x with
  | var i => rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp [renameQBF, ih]
  | conj φ ψ ihφ ihψ => simp [renameQBF, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [renameQBF, ihφ, ihψ]
  | ex i φ ih =>
    simp only [renameQBF, QBF.eval, ih, Function.update_comp_eq_of_injective x hf]
  | all i φ ih =>
    simp only [renameQBF, QBF.eval, ih, Function.update_comp_eq_of_injective x hf]

/-- Quantifier-free formulas can use noninjective maps because they have no binders. -/
theorem eval_renameQBF_quantifierFree (f : ℕ → ℕ) (φ : QBF) (hφ : φ.QuantifierFree)
    (x : ℕ → Bool) : (renameQBF f φ).eval x = φ.eval (x ∘ f) := by
  induction φ with
  | var i => rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => exact congrArg Bool.not (ih hφ)
  | conj φ ψ ihφ ihψ =>
    have hs : φ.QuantifierFree ∧ ψ.QuantifierFree := QBF.quantifierFree_conj.mp hφ
    simp [renameQBF, ihφ hs.1, ihψ hs.2]
  | disj φ ψ ihφ ihψ =>
    have hs : φ.QuantifierFree ∧ ψ.QuantifierFree := by
      simpa [QBF.QuantifierFree, QBF.quantDepth, Nat.max_eq_zero_iff] using hφ
    simp [renameQBF, ihφ hs.1, ihψ hs.2]
  | ex i φ => simp [QBF.QuantifierFree, QBF.quantDepth] at hφ
  | all i φ => simp [QBF.QuantifierFree, QBF.quantDepth] at hφ

end IPPSPACE

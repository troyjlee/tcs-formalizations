/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Blocks
import IPPSPACE.QBF.Renaming

/-!
# Finite Boolean formula builders

Conjunctions and disjunctions over explicit lists and finite tuples are
executable upstream QBF syntax. These lemmas track semantics, absence of
quantifiers, names, and node counts for configuration-test constructions.
-/

namespace IPPSPACE

open Complexity

def qbfAll : List QBF → QBF
  | [] => .tru
  | φ :: rest => .conj φ (qbfAll rest)

def qbfAny : List QBF → QBF
  | [] => .fls
  | φ :: rest => .disj φ (qbfAny rest)

@[simp] theorem eval_qbfAll (formulas : List QBF) (assignment : ℕ → Bool) :
    (qbfAll formulas).eval assignment = true ↔ ∀ φ ∈ formulas, φ.eval assignment = true := by
  induction formulas <;> simp_all [qbfAll]

@[simp] theorem eval_qbfAny (formulas : List QBF) (assignment : ℕ → Bool) :
    (qbfAny formulas).eval assignment = true ↔ ∃ φ ∈ formulas, φ.eval assignment = true := by
  induction formulas <;> simp_all [qbfAny]

theorem quantifierFree_qbfAll (formulas : List QBF)
    (h : ∀ φ ∈ formulas, φ.QuantifierFree) : (qbfAll formulas).QuantifierFree := by
  induction formulas with
  | nil => rfl
  | cons φ rest ih =>
    exact QBF.quantifierFree_conj.mpr ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

theorem quantifierFree_qbfAny (formulas : List QBF)
    (h : ∀ φ ∈ formulas, φ.QuantifierFree) : (qbfAny formulas).QuantifierFree := by
  induction formulas with
  | nil => rfl
  | cons φ rest ih =>
    have hφ := h φ (by simp)
    have hr := ih (fun ψ hψ => h ψ (by simp [hψ]))
    exact Nat.max_eq_zero_iff.mpr ⟨hφ, hr⟩

theorem nodeCount_qbfAll_le (formulas : List QBF) (N : ℕ)
    (h : ∀ φ ∈ formulas, nodeCount φ ≤ N) :
    nodeCount (qbfAll formulas) ≤ (N + 1) * formulas.length + 1 := by
  induction formulas with
  | nil => simp [qbfAll, nodeCount]
  | cons φ rest ih =>
    have hφ := h φ (by simp)
    have hr := ih (fun ψ hψ => h ψ (by simp [hψ]))
    simp only [qbfAll, nodeCount, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem nodeCount_qbfAny_le (formulas : List QBF) (N : ℕ)
    (h : ∀ φ ∈ formulas, nodeCount φ ≤ N) :
    nodeCount (qbfAny formulas) ≤ (N + 1) * formulas.length + 1 := by
  induction formulas with
  | nil => simp [qbfAny, nodeCount]
  | cons φ rest ih =>
    have hφ := h φ (by simp)
    have hr := ih (fun ψ hψ => h ψ (by simp [hψ]))
    simp only [qbfAny, nodeCount, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem qbfNames_qbfAll_lt (formulas : List QBF) (B : ℕ)
    (h : ∀ φ ∈ formulas, ∀ i ∈ qbfNames φ, i < B) :
    ∀ i ∈ qbfNames (qbfAll formulas), i < B := by
  induction formulas with
  | nil => simp [qbfAll, qbfNames]
  | cons φ rest ih =>
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h φ (by simp) i hi
    · exact ih (fun ψ hψ => h ψ (by simp [hψ])) i hi

theorem qbfNames_qbfAny_lt (formulas : List QBF) (B : ℕ)
    (h : ∀ φ ∈ formulas, ∀ i ∈ qbfNames φ, i < B) :
    ∀ i ∈ qbfNames (qbfAny formulas), i < B := by
  induction formulas with
  | nil => simp [qbfAny, qbfNames]
  | cons φ rest ih =>
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h φ (by simp) i hi
    · exact ih (fun ψ hψ => h ψ (by simp [hψ])) i hi

def qbfAllFin (n : ℕ) (body : Fin n → QBF) : QBF := qbfAll (List.ofFn body)
def qbfAnyFin (n : ℕ) (body : Fin n → QBF) : QBF := qbfAny (List.ofFn body)

@[simp] theorem eval_qbfAllFin (n : ℕ) (body : Fin n → QBF) (assignment : ℕ → Bool) :
    (qbfAllFin n body).eval assignment = true ↔ ∀ i, (body i).eval assignment = true := by
  simp [qbfAllFin]

@[simp] theorem eval_qbfAnyFin (n : ℕ) (body : Fin n → QBF) (assignment : ℕ → Bool) :
    (qbfAnyFin n body).eval assignment = true ↔ ∃ i, (body i).eval assignment = true := by
  simp [qbfAnyFin]

theorem quantifierFree_qbfAllFin (n : ℕ) (body : Fin n → QBF)
    (h : ∀ i, (body i).QuantifierFree) : (qbfAllFin n body).QuantifierFree := by
  apply quantifierFree_qbfAll
  simpa using h

theorem quantifierFree_qbfAnyFin (n : ℕ) (body : Fin n → QBF)
    (h : ∀ i, (body i).QuantifierFree) : (qbfAnyFin n body).QuantifierFree := by
  apply quantifierFree_qbfAny
  simpa using h

theorem nodeCount_qbfAllFin_le (n : ℕ) (body : Fin n → QBF) (N : ℕ)
    (h : ∀ i, nodeCount (body i) ≤ N) : nodeCount (qbfAllFin n body) ≤ (N + 1) * n + 1 := by
  simpa [qbfAllFin] using nodeCount_qbfAll_le (List.ofFn body) N (by simpa using h)

theorem nodeCount_qbfAnyFin_le (n : ℕ) (body : Fin n → QBF) (N : ℕ)
    (h : ∀ i, nodeCount (body i) ≤ N) : nodeCount (qbfAnyFin n body) ≤ (N + 1) * n + 1 := by
  simpa [qbfAnyFin] using nodeCount_qbfAny_le (List.ofFn body) N (by simpa using h)

theorem qbfNames_qbfAllFin_lt (n : ℕ) (body : Fin n → QBF) (B : ℕ)
    (h : ∀ j, ∀ i ∈ qbfNames (body j), i < B) :
    ∀ i ∈ qbfNames (qbfAllFin n body), i < B := by
  apply qbfNames_qbfAll_lt
  simpa using h

theorem qbfNames_qbfAnyFin_lt (n : ℕ) (body : Fin n → QBF) (B : ℕ)
    (h : ∀ j, ∀ i ∈ qbfNames (body j), i < B) :
    ∀ i ∈ qbfNames (qbfAnyFin n body), i < B := by
  apply qbfNames_qbfAny_lt
  simpa using h

@[simp] theorem quantifierFree_bitEquality (a b : ℕ) : (bitEquality a b).QuantifierFree := rfl

@[simp] theorem quantifierFree_bitValue (name : ℕ) (value : Bool) :
    (bitValue name value).QuantifierFree := by
  cases value <;> rfl

@[simp] theorem quantifierFree_blockEquality {width : ℕ} (a b : Fin width → ℕ) :
    (blockEquality a b).QuantifierFree := by
  induction width with
  | zero => rfl
  | succ width ih => exact QBF.quantifierFree_conj.mpr ⟨quantifierFree_bitEquality _ _, ih _ _⟩

@[simp] theorem quantifierFree_blockValues {width : ℕ} (names : Fin width → ℕ)
    (values : Fin width → Bool) : (blockValues names values).QuantifierFree := by
  induction width with
  | zero => rfl
  | succ width ih => exact QBF.quantifierFree_conj.mpr ⟨quantifierFree_bitValue _ _, ih _ _⟩

@[simp] theorem mem_qbfNames_qbfAll (formulas : List QBF) (i : ℕ) :
    i ∈ qbfNames (qbfAll formulas) ↔ ∃ φ ∈ formulas, i ∈ qbfNames φ := by
  induction formulas <;> simp_all [qbfAll, qbfNames]

@[simp] theorem mem_qbfNames_qbfAny (formulas : List QBF) (i : ℕ) :
    i ∈ qbfNames (qbfAny formulas) ↔ ∃ φ ∈ formulas, i ∈ qbfNames φ := by
  induction formulas <;> simp_all [qbfAny, qbfNames]

@[simp] theorem mem_qbfNames_qbfAllFin (n : ℕ) (body : Fin n → QBF) (i : ℕ) :
    i ∈ qbfNames (qbfAllFin n body) ↔ ∃ j, i ∈ qbfNames (body j) := by
  simp [qbfAllFin]

@[simp] theorem mem_qbfNames_qbfAnyFin (n : ℕ) (body : Fin n → QBF) (i : ℕ) :
    i ∈ qbfNames (qbfAnyFin n body) ↔ ∃ j, i ∈ qbfNames (body j) := by
  simp [qbfAnyFin]

end IPPSPACE

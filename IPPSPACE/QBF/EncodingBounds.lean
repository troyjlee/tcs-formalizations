/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Renaming
import Mathlib.Tactic

/-!
# Binary-size bounds for QBF transformations

Node bounds alone do not bound an encoding with natural-number variable names.
These lemmas account for every occurrence and binder, using binary name widths.
They allow freshness constructions to be bounded in actual input bit length.
-/

namespace IPPSPACE

open Complexity

theorem qbfNameBitCost_le (φ : QBF) (B : ℕ)
    (h : ∀ i ∈ qbfNames φ, i.size ≤ B) :
    qbfNameBitCost φ ≤ nodeCount φ * (2 * B + 1) := by
  induction φ with
  | var i => have hi := h i (by simp [qbfNames]); simp [qbfNameBitCost, nodeCount]; omega
  | tru => simp [qbfNameBitCost, nodeCount]
  | fls => simp [qbfNameBitCost, nodeCount]
  | neg φ ih =>
    have hφ := ih h
    simp only [qbfNameBitCost, nodeCount, Nat.add_mul, Nat.one_mul]
    omega
  | conj φ ψ ihφ ihψ =>
    have hφ := ihφ (fun i hi => h i (Finset.mem_union_left _ hi))
    have hψ := ihψ (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [qbfNameBitCost, nodeCount, Nat.add_mul, Nat.one_mul]
    omega
  | disj φ ψ ihφ ihψ =>
    have hφ := ihφ (fun i hi => h i (Finset.mem_union_left _ hi))
    have hψ := ihψ (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [qbfNameBitCost, nodeCount, Nat.add_mul, Nat.one_mul]
    omega
  | ex i φ ih =>
    have hi := h i (Finset.mem_insert_self _ _)
    have hφ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simp only [qbfNameBitCost, nodeCount, Nat.add_mul, Nat.one_mul]
    omega
  | all i φ ih =>
    have hi := h i (Finset.mem_insert_self _ _)
    have hφ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simp only [qbfNameBitCost, nodeCount, Nat.add_mul, Nat.one_mul]
    omega

/-- Three tag bits plus at most `2B + 1` name bits per node. -/
theorem length_encodeQBF_le_of_name_size (φ : QBF) (B : ℕ)
    (h : ∀ i ∈ qbfNames φ, i.size ≤ B) :
    (encodeQBF φ).length ≤ nodeCount φ * (2 * B + 4) := by
  rw [length_encodeQBF]
  have := qbfNameBitCost_le φ B h
  nlinarith

theorem length_encodeQBF_le_of_maxVar (φ : QBF) (B : ℕ) (h : qbfMaxVar φ ≤ B) :
    (encodeQBF φ).length ≤ nodeCount φ * (2 * B.size + 4) := by
  apply length_encodeQBF_le_of_name_size
  intro i hi
  exact Nat.size_le_size ((le_qbfMaxVar_of_mem φ i hi).trans h)

private theorem nat_size_max (a b : ℕ) : (max a b).size = max a.size b.size := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.size_le_size h)]
  · rw [max_eq_left h, max_eq_left (Nat.size_le_size h)]

theorem qbfMaxVar_size_le_nameCost (φ : QBF) : (qbfMaxVar φ).size ≤ qbfNameBitCost φ := by
  induction φ <;>
    simp_all only [qbfMaxVar, qbfNameBitCost, nat_size_max, Nat.size_zero] <;> omega

theorem qbfMaxVar_size_le_encoding (φ : QBF) : (qbfMaxVar φ).size ≤ (encodeQBF φ).length := by
  rw [length_encodeQBF]
  exact (qbfMaxVar_size_le_nameCost φ).trans (Nat.le_add_left _ _)

/-- Adding a fresh-name offset grows binary width by at most the two widths plus one. -/
theorem nat_size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (a.size + b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2 ^ (a.size + b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]
  omega

/-- A coarse bound convenient when the number of new names is polynomial. -/
theorem nat_size_le_self (n : ℕ) : n.size ≤ n := by
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- Size-preserving syntax transformations with linearly many fresh names have
a quadratic binary-encoding bound, even if original variable values are huge. -/
theorem length_encodeQBF_le_quadratic (φ ψ : QBF)
    (hnodes : nodeCount ψ ≤ nodeCount φ)
    (hnames : qbfMaxVar ψ ≤ qbfMaxVar φ + (nodeCount φ + 1)) :
    (encodeQBF ψ).length ≤ (encodeQBF φ).length * (4 * (encodeQBF φ).length + 8) := by
  have hnode := nodeCount_le_length_encodeQBF φ
  have hwidth := qbfMaxVar_size_le_encoding φ
  have hadd := nat_size_add_le (qbfMaxVar φ) (nodeCount φ + 1)
  have hoffset := nat_size_le_self (nodeCount φ + 1)
  have hsize : (qbfMaxVar φ + (nodeCount φ + 1)).size ≤ 2 * (encodeQBF φ).length + 2 := by
    omega
  apply (length_encodeQBF_le_of_maxVar ψ _ hnames).trans
  have hmul := Nat.mul_le_mul (hnodes.trans hnode) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsize) 4)
  nlinarith

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityLeaves
import Mathlib.Data.Fintype.BigOperators

/-!
# Row and column deletion for the capacity induction

Deletion changes the finite index types. Rigidity is transported by extending
a perturbation by zero, not by confusing a subtype matrix with an ambient one.
The value and marginal identities retain the removed row explicitly.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- The marginal attached to a column. -/
noncomputable def columnSum (A : R → C → ℝ) (j : C) : ℝ := ∑ i, A i j

/-- Remove one row, without renumbering the others. -/
def eraseRow (A : R → C → ℝ) (r : R) : {i // i ≠ r} → C → ℝ :=
  fun i j => A i.val j

/-- Remove one column, without renumbering the others. -/
def eraseColumn (A : R → C → ℝ) (c : C) : R → {j // j ≠ c} → ℝ :=
  fun i j => A i j.val

theorem columnSum_nonneg {A : R → C → ℝ} (hA : IsStochastic A) (j : C) :
    0 ≤ columnSum A j := Finset.sum_nonneg (fun i _ => hA.1 i j)

theorem entry_le_columnSum {A : R → C → ℝ} (hA : IsStochastic A) (i : R) (j : C) :
    A i j ≤ columnSum A j :=
  Finset.single_le_sum (fun k _ => hA.1 k j) (Finset.mem_univ i)

omit [Fintype R] in
theorem entry_le_one {A : R → C → ℝ} (hA : IsStochastic A) (i : R) (j : C) :
    A i j ≤ 1 := by
  rw [← hA.2 i]
  exact Finset.single_le_sum (fun k _ => hA.1 i k) (Finset.mem_univ j)

theorem IsRigid.eraseRow [DecidableEq R] {A : R → C → ℝ} (hA : IsRigid A) (r : R) :
    IsRigid (eraseRow A r) := by
  classical
  intro D hD hs
  let E : R → C → ℝ := fun i j => if h : i = r then 0 else D ⟨i, h⟩ j
  have her (j : C) : E r j = 0 := by simp [E]
  have hei (i : {i // i ≠ r}) (j : C) : E i.val j = D i j := by
    simp [E, i.property]
  have hb : IsBalanced E := by
    constructor
    · intro i
      by_cases hi : i = r
      · subst i
        simp [her]
      · simpa only [E, dif_neg hi] using hD.1 ⟨i, hi⟩
    · intro j
      rw [Fintype.sum_eq_add_sum_subtype_ne _ r, her, zero_add]
      simp_rw [hei]
      exact hD.2 j
  have hsupport : SupportedBy E A := by
    intro i j hij
    by_cases hi : i = r
    · subst i
      exact her j
    · exact (hei ⟨i, hi⟩ j).trans (hs ⟨i, hi⟩ j hij)
  have he := hA E hb hsupport
  funext i j
  simpa only [hei, Pi.zero_apply] using congrFun (congrFun he i.val) j

theorem IsRigid.eraseColumn [DecidableEq C] {A : R → C → ℝ} (hA : IsRigid A) (c : C) :
    IsRigid (eraseColumn A c) :=
  (hA.transpose.eraseRow c).transpose

omit [Fintype R] in
theorem IsStochastic.eraseRow {A : R → C → ℝ} (hA : IsStochastic A) (r : R) :
    IsStochastic (eraseRow A r) := ⟨fun i => hA.1 i.val, fun i => hA.2 i.val⟩

omit [Fintype C] in
theorem columnSum_eq_entry_add_eraseRow [DecidableEq R] (A : R → C → ℝ) (r : R) (j : C) :
    columnSum A j = A r j + columnSum (eraseRow A r) j := by
  classical
  exact Fintype.sum_eq_add_sum_subtype_ne (fun i => A i j) r

theorem value_eq_row_mul_eraseRow [DecidableEq R] (A : R → C → ℝ) (r : R) (x : C → ℝ) :
    value A x = (∑ j, A r j * x j) * value (eraseRow A r) x := by
  classical
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun i => ∑ j, A i j * x j) r

omit [Fintype R] in
theorem rowSum_eraseColumn [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A) (i : R) (c : C) :
    (∑ j : {j // j ≠ c}, A i j.val) = 1 - A i c := by
  classical
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun j => A i j) c
  rw [hA.2 i] at h
  linarith

omit [Fintype R] in
theorem rowSubset_le_one_sub {A : R → C → ℝ} (hA : IsStochastic A)
    (i : R) (c : C) (S : Finset {j // j ≠ c}) :
    (∑ j ∈ S, A i j.val) ≤ 1 - A i c := by
  classical
  rw [← rowSum_eraseColumn hA i c]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun j _ _ => hA.1 i j.val)

theorem value_nonneg {A : R → C → ℝ} (hA : IsStochastic A)
    {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) : 0 ≤ value A x :=
  Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hA.1 i j) (hx j)))

omit [Fintype R] in
/-- A column already zero on every row can be discarded exactly. -/
theorem IsStochastic.eraseColumn_of_zero [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A)
    (c : C) (hc : ∀ i, A i c = 0) : IsStochastic (eraseColumn A c) := by
  constructor
  · exact fun i j => hA.1 i j.val
  · intro i
    simpa only [eraseColumn, hc i, sub_zero] using rowSum_eraseColumn hA i c

theorem value_eraseColumn_of_zero [DecidableEq C] (A : R → C → ℝ) (c : C)
    (hc : ∀ i, A i c = 0) (x : C → ℝ) :
    value (eraseColumn A c) (fun j => x j.val) = value A x := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun j => A i j * x j) c
  simpa only [eraseColumn, hc i, zero_mul, zero_add] using h.symm

end TSPGap.CapacityMatrix

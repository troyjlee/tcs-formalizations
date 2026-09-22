/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityRestriction

/-!
# Removing a target-one leaf column

Remove the unique incident row together with the column. The product loses
at most the column mass times its variable; remaining subset marginals fall
by at most one minus that mass. These pointwise facts supply GKL Lemma 5.10
without a derivative or capacity-infimum argument. Deterministic rows are
also removed exactly, for the separate row-descent branch of Theorem 5.11.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- The matrix with the incident row and its leaf column removed. -/
def eraseLeaf (A : R → C → ℝ) (r : R) (c : C) :
    {i // i ≠ r} → {j // j ≠ c} → ℝ := eraseColumn (eraseRow A r) c

omit [Fintype C] in
/-- Only support outside the nominated row matters for this identity. -/
theorem columnSum_eq_of_leaf {A : R → C → ℝ} {r : R} {c : C}
    (hc : ∀ i, i ≠ r → A i c = 0) : columnSum A c = A r c := by
  classical
  exact Finset.sum_eq_single r (fun i _ hi => hc i hi)
    (fun h => (h (Finset.mem_univ r)).elim)

omit [Fintype R] in
theorem IsStochastic.eraseLeaf [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A) {r : R} {c : C}
    (hc : ∀ i, i ≠ r → A i c = 0) : IsStochastic (eraseLeaf A r c) :=
  (hA.eraseRow r).eraseColumn_of_zero c (fun i => hc i.val i.property)

theorem IsRigid.eraseLeaf [DecidableEq R] [DecidableEq C] {A : R → C → ℝ}
    (hA : IsRigid A) (r : R) (c : C) :
    IsRigid (eraseLeaf A r c) := (hA.eraseRow r).eraseColumn c

omit [Fintype C] in
theorem columnSum_eraseLeaf [DecidableEq R] (A : R → C → ℝ) (r : R) (c : C) (j : {j // j ≠ c}) :
    columnSum (eraseLeaf A r c) j = columnSum A j.val - A r j.val := by
  have h := columnSum_eq_entry_add_eraseRow A r j.val
  change columnSum (eraseRow A r) j.val = _
  linarith

/-- The exact remaining product after factoring out the incident row. -/
theorem value_eq_row_mul_eraseLeaf [DecidableEq R] [DecidableEq C] {A : R → C → ℝ} {r : R} {c : C}
    (hc : ∀ i, i ≠ r → A i c = 0) (x : C → ℝ) :
    value A x = (∑ j, A r j * x j) * value (eraseLeaf A r c) (fun j => x j.val) := by
  rw [value_eq_row_mul_eraseRow A r x]
  rw [← value_eraseColumn_of_zero (eraseRow A r) c
    (fun i => hc i.val i.property) x]
  rfl

/-- Pointwise leaf removal; even a zero leaf mass or zero coordinate is safe. -/
theorem eraseLeaf_value_le [DecidableEq R] [DecidableEq C] {A : R → C → ℝ}
    (hA : IsStochastic A) {r : R} {c : C}
    (hc : ∀ i, i ≠ r → A i c = 0) {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) :
    columnSum A c * x c * value (eraseLeaf A r c) (fun j => x j.val) ≤ value A x := by
  rw [columnSum_eq_of_leaf hc, value_eq_row_mul_eraseLeaf hc x]
  apply mul_le_mul_of_nonneg_right
  · exact Finset.single_le_sum (fun j _ => mul_nonneg (hA.1 r j) (hx j))
      (Finset.mem_univ c)
  · exact value_nonneg (hA.eraseLeaf hc) (fun j => hx j.val)

/-- The precise change in a remaining subset of column marginals. -/
theorem eraseLeaf_subset_deficit [DecidableEq R] {A : R → C → ℝ} (hA : IsStochastic A)
    {r : R} {c : C} (hc : ∀ i, i ≠ r → A i c = 0) (S : Finset {j // j ≠ c}) :
    0 ≤ (∑ j ∈ S, columnSum A j.val) - (∑ j ∈ S, columnSum (eraseLeaf A r c) j) ∧
    (∑ j ∈ S, columnSum A j.val) - (∑ j ∈ S, columnSum (eraseLeaf A r c) j) ≤
      1 - columnSum A c := by
  simp_rw [columnSum_eraseLeaf]
  have he : (∑ j ∈ S, columnSum A j.val) -
      (∑ j ∈ S, (columnSum A j.val - A r j.val)) = ∑ j ∈ S, A r j.val := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [he, columnSum_eq_of_leaf hc]
  exact ⟨Finset.sum_nonneg (fun j _ => hA.1 r j.val), rowSubset_le_one_sub hA r c S⟩

/-- A deterministic row factors as a single coordinate, at every real vector. -/
theorem value_eq_coord_mul_eraseRow [DecidableEq R] {A : R → C → ℝ} {r : R} {c : C}
    (hc : A r c = 1) (hz : ∀ j, j ≠ c → A r j = 0) (x : C → ℝ) :
    value A x = x c * value (eraseRow A r) x := by
  classical
  rw [value_eq_row_mul_eraseRow A r x]
  congr 1
  rw [Finset.sum_eq_single c]
  · rw [hc, one_mul]
  · intro j _ hj
    rw [hz j hj, zero_mul]
  · simp

omit [Fintype C] in
/-- The target and marginal may both be decreased by the same unit vector. -/
theorem columnSum_eraseRow_of_deterministic [DecidableEq R] [DecidableEq C]
    {A : R → C → ℝ} {r : R} {c : C}
    (hc : A r c = 1) (hz : ∀ j, j ≠ c → A r j = 0) (j : C) :
    columnSum (eraseRow A r) j = columnSum A j - if j = c then 1 else 0 := by
  have h := columnSum_eq_entry_add_eraseRow A r j
  by_cases hj : j = c
  · subst j
    rw [hc] at h
    simp only [ite_true]
    linarith
  · rw [hz j hj] at h
    simpa only [if_neg hj, sub_zero, zero_add] using h.symm

end TSPGap.CapacityMatrix

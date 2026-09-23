/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityRestriction

/-!
# Removing a target-zero column

The matrix is normalized row by row after deletion. At every nonnegative
evaluation, the old product dominates the new product times one minus the
deleted column mass. Remaining subset marginals increase, by at most that
mass. These are the pointwise and mean parts of GKL Lemma 5.9; no capacity
infimum, limiting evaluation at zero, or stability closure is used.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- Remove the column and rescale each surviving row to mass one. -/
noncomputable def normalizeEraseColumn (A : R → C → ℝ) (c : C) :
    R → {j // j ≠ c} → ℝ := fun i j => A i j.val / (1 - A i c)

theorem one_sub_entry_pos {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) (i : R) : 0 < 1 - A i c :=
  sub_pos.mpr ((entry_le_columnSum hA i c).trans_lt hc)

theorem IsStochastic.normalizeEraseColumn [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) : IsStochastic (normalizeEraseColumn A c) := by
  constructor
  · exact fun i j => div_nonneg (hA.1 i j.val) (one_sub_entry_pos hA hc i).le
  · intro i
    simp only [CapacityMatrix.normalizeEraseColumn, ← Finset.sum_div, rowSum_eraseColumn hA i c]
    exact div_self (one_sub_entry_pos hA hc i).ne'

/-- Numerical row scaling preserves support, even without a sign assumption. -/
theorem IsRigid.normalizeEraseColumn [DecidableEq C] {A : R → C → ℝ} (hA : IsRigid A) (c : C) :
    IsRigid (normalizeEraseColumn A c) := by
  apply (hA.eraseColumn c).of_supportedBy
  intro i j h
  simp only [CapacityMatrix.normalizeEraseColumn, CapacityMatrix.eraseColumn] at h ⊢
  rw [h, zero_div]

/-- The finite product/union inequality includes zero factors and the empty set. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have h0 := ha0 i (Finset.mem_insert_self _ _)
    have h1 := ha1 i (Finset.mem_insert_self _ _)
    have hs0 := fun j hj => ha0 j (Finset.mem_insert_of_mem hj)
    have hs1 := fun j hj => ha1 j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    calc
      1 - (a i + ∑ j ∈ s, a j) ≤ (1 - a i) * (1 - ∑ j ∈ s, a j) := by
        nlinarith [mul_nonneg h0 (Finset.sum_nonneg hs0)]
      _ ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
        mul_le_mul_of_nonneg_left (ih hs0 hs1) (sub_nonneg.mpr h1)

theorem normalizeEraseColumn_rowValue [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) (i : R) (x : C → ℝ) :
    (1 - A i c) * (∑ j, normalizeEraseColumn A c i j * x j.val) =
      ∑ j : {j // j ≠ c}, A i j.val * x j.val := by
  simp only [normalizeEraseColumn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [(one_sub_entry_pos hA hc i).ne']

/-- A pointwise bound is sufficient for the later capacity induction. -/
theorem normalizeEraseColumn_value_le [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) :
    (1 - columnSum A c) * value (normalizeEraseColumn A c) (fun j => x j.val) ≤
      value A x := by
  classical
  have hB := hA.normalizeEraseColumn hc
  have hb := value_nonneg hB (fun j => hx j.val)
  have hprod : 1 - columnSum A c ≤ ∏ i, (1 - A i c) :=
    one_sub_sum_le_prod_one_sub Finset.univ (fun i _ => hA.1 i c)
      (fun i _ => entry_le_one hA i c)
  refine (mul_le_mul_of_nonneg_right hprod hb).trans ?_
  have hrow (i : R) :
      (1 - A i c) * (∑ j, normalizeEraseColumn A c i j * x j.val) ≤ ∑ j, A i j * x j := by
    rw [normalizeEraseColumn_rowValue hA hc]
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => A i j * x j) c]
    exact le_add_of_nonneg_left (mul_nonneg (hA.1 i c) (hx c))
  have hp := Finset.prod_le_prod
    (fun i (_ : i ∈ Finset.univ) => mul_nonneg (one_sub_entry_pos hA hc i).le
      (Finset.sum_nonneg (fun j _ => mul_nonneg (hB.1 i j) (hx j.val))))
    (fun i _ => hrow i)
  simpa only [Finset.prod_mul_distrib, value] using hp

/-- The change of any remaining row sub-sum is between zero and the deleted entry. -/
theorem normalizeEraseColumn_row_increment {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) (i : R) (S : Finset {j // j ≠ c}) :
    0 ≤ ∑ j ∈ S, (normalizeEraseColumn A c i j - A i j.val) ∧
      (∑ j ∈ S, (normalizeEraseColumn A c i j - A i j.val)) ≤ A i c := by
  have hd := one_sub_entry_pos hA hc i
  have he : (∑ j ∈ S, (normalizeEraseColumn A c i j - A i j.val)) =
      (A i c / (1 - A i c)) * ∑ j ∈ S, A i j.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [normalizeEraseColumn]
    field_simp [hd.ne']
    ring
  rw [he]
  have hn := div_nonneg (hA.1 i c) hd.le
  refine ⟨mul_nonneg hn (Finset.sum_nonneg (fun j _ => hA.1 i j.val)), ?_⟩
  calc
    _ ≤ (A i c / (1 - A i c)) * (1 - A i c) :=
      mul_le_mul_of_nonneg_left (rowSubset_le_one_sub hA i c S) hn
    _ = A i c := div_mul_cancel₀ _ hd.ne'

/-- Remaining subset masses rise by at most the deleted column mass. -/
theorem normalizeEraseColumn_subset_increment {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) (S : Finset {j // j ≠ c}) :
    0 ≤ (∑ j ∈ S, columnSum (normalizeEraseColumn A c) j) -
      (∑ j ∈ S, columnSum A j.val) ∧
    (∑ j ∈ S, columnSum (normalizeEraseColumn A c) j) -
      (∑ j ∈ S, columnSum A j.val) ≤ columnSum A c := by
  have he : (∑ j ∈ S, columnSum (normalizeEraseColumn A c) j) -
      (∑ j ∈ S, columnSum A j.val) =
      ∑ i, ∑ j ∈ S, (normalizeEraseColumn A c i j - A i j.val) := by
    simp only [columnSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_comm
  rw [he]
  exact ⟨Finset.sum_nonneg (fun i _ => (normalizeEraseColumn_row_increment hA hc i S).1),
    Finset.sum_le_sum (fun i _ => (normalizeEraseColumn_row_increment hA hc i S).2)⟩

end TSPGap.CapacityMatrix

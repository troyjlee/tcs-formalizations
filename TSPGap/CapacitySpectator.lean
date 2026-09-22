/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityRestriction

/-!
# Leaf selection with an isolated spectator allowed

The active columns have positive mass. The spectator need not: when its
column is zero, remove it for the leaf-count argument only. The selected
leaf is still a column of the original matrix.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

omit [Fintype C] in
theorem columnDegree_pos_of_mass_pos {A : R → C → ℝ} {c : C}
    (hc : 0 < columnSum A c) : 0 < rowDegree (fun j i => A i j) c := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc.ne'
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem IsRigid.rows_lt_columns_of_no_leaf [Nonempty R] {A : R → C → ℝ}
    (hA : IsRigid A) (hs : IsStochastic A) (hn : ∀ i, rowDegree A i ≠ 1) :
    Fintype.card R < Fintype.card C := by
  classical
  have hz : rowLeaves A = ∅ := by ext i; simp [rowLeaves, hn i]
  have h := hA.card_add_one_le_columns_add_leaves hs.rowDegree_pos
  rw [hz, Finset.card_empty, add_zero] at h
  omega

omit [Fintype R] in
theorem rowDegree_erase_zero [DecidableEq C] {A : R → C → ℝ} (c : C)
    (hc : ∀ i, A i c = 0) (i : R) : rowDegree (eraseColumn A c) i = rowDegree A i := by
  classical
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun j => if A i j ≠ 0 then 1 else 0) c
  unfold rowDegree
  rw [Finset.card_filter, Finset.card_filter]
  simpa only [eraseColumn, hc i, ne_eq, not_true_eq_false,
    if_false, zero_add] using h.symm

/-- Without deterministic rows, some active column is a leaf. The only
possibly empty column is the spectator, and it requires no mass hypothesis. -/
theorem IsRigid.active_column_leaf [Nonempty R] {A : R → C → ℝ}
    (hA : IsRigid A) (hs : IsStochastic A) (s : C)
    (hn : ∀ i, rowDegree A i ≠ 1)
    (hc : ∀ j, j ≠ s → 0 < rowDegree (fun j i => A i j) j) :
    ∃ c, c ≠ s ∧ rowDegree (fun j i => A i j) c = 1 := by
  classical
  by_cases hz : ∀ i, A i s = 0
  · let B := CapacityMatrix.eraseColumn A s
    have hB : IsRigid B := hA.eraseColumn s
    have hsB : IsStochastic B := hs.eraseColumn_of_zero s hz
    have hnB : ∀ i, rowDegree B i ≠ 1 := by
      intro i
      simpa only [B, rowDegree_erase_zero s hz] using hn i
    have hsize := hB.rows_lt_columns_of_no_leaf hsB hnB
    haveI : Nonempty {j // j ≠ s} := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨c, hleaf⟩ := hB.exists_column_leaf (fun j => hc j.val j.property) hsize.le
    exact ⟨c.val, c.property, hleaf⟩
  · have hpos : ∀ j, 0 < rowDegree (fun j i => A i j) j := by
      intro j
      by_cases hj : j = s
      · subst j
        push Not at hz
        obtain ⟨i, hi⟩ := hz
        exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
      · exact hc j hj
    exact hA.exists_column_leaf_ne hpos (hA.rows_lt_columns_of_no_leaf hs hn) s

end TSPGap.CapacityMatrix

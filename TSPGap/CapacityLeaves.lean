/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacitySupportRank

/-!
# Leaf counts for the capacity induction

Rigidity gives the forest edge bound; summing row degrees gives the leaf
bound. At least one row is required for the `+1` version: the empty matrix
is deliberately not claimed to have a leaf. Isolated columns are allowed,
so deleting a zero spectator column can be handled separately by consumers.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- Number of nonzero entries in a row. -/
noncomputable def rowDegree (A : R → C → ℝ) (i : R) : ℕ :=
  (Finset.univ.filter (fun j => A i j ≠ 0)).card

/-- Rows incident to exactly one supported entry. -/
noncomputable def rowLeaves (A : R → C → ℝ) : Finset R :=
  Finset.univ.filter (fun i => rowDegree A i = 1)

theorem support_card_eq_sum_rowDegree (A : R → C → ℝ) :
    (support A).card = ∑ i, rowDegree A i := by
  classical
  simp only [support, rowDegree, Finset.card_filter, Fintype.sum_prod_type]

omit [Fintype R] in
theorem IsStochastic.rowDegree_pos {A : R → C → ℝ} (hA : IsStochastic A) (i : R) :
    0 < rowDegree A i := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hA.2 i]; norm_num)
  exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

/-- Counting degrees separates the leaves from the rows of degree at least two. -/
theorem twice_card_le_edges_add_leaves {A : R → C → ℝ}
    (hpos : ∀ i, 0 < rowDegree A i) :
    2 * Fintype.card R ≤ (support A).card + (rowLeaves A).card := by
  classical
  have h (i : R) : 2 ≤ rowDegree A i + if rowDegree A i = 1 then 1 else 0 := by
    split_ifs with he
    · omega
    · have := hpos i
      omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm (Fintype.card R) 2, ← support_card_eq_sum_rowDegree,
    ← Finset.card_filter, rowLeaves] using hs

/-- Gurvits--Klein--Leake Lemma 5.7 in algebraic-support form, with the
nonempty-row guard needed by the empty-forest corner. -/
theorem IsRigid.card_add_one_le_columns_add_leaves [Nonempty R]
    {A : R → C → ℝ} (hA : IsRigid A) (hpos : ∀ i, 0 < rowDegree A i) :
    Fintype.card R + 1 ≤ Fintype.card C + (rowLeaves A).card := by
  have hcard := hA.support_card_le
  have hdeg := twice_card_le_edges_add_leaves hpos
  have hr := Fintype.card_pos (α := R)
  omega

/-- If there are at least as many nonempty rows as columns, some row is a leaf. -/
theorem IsRigid.exists_row_leaf [Nonempty R] {A : R → C → ℝ}
    (hA : IsRigid A) (hpos : ∀ i, 0 < rowDegree A i)
    (hsize : Fintype.card C ≤ Fintype.card R) :
    ∃ i, rowDegree A i = 1 := by
  classical
  have h := hA.card_add_one_le_columns_add_leaves hpos
  have hp : 0 < (rowLeaves A).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

omit [Fintype R] in
/-- A stochastic leaf row is deterministic. -/
theorem IsStochastic.leaf_row {A : R → C → ℝ} (hA : IsStochastic A)
    {i : R} (hi : rowDegree A i = 1) :
    ∃ j, A i j = 1 ∧ ∀ k, k ≠ j → A i k = 0 := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hi
  have hz (k : C) (hk : k ≠ j) : A i k = 0 := by
    by_contra hn
    have hm : k ∈ Finset.univ.filter (fun l => A i l ≠ 0) := by simp [hn]
    rw [hj] at hm
    exact hk (Finset.mem_singleton.mp hm)
  refine ⟨j, ?_, hz⟩
  have hs : ∑ k, A i k = A i j := Finset.sum_eq_single j (fun k _ hk => hz k hk)
    (fun h => (h (Finset.mem_univ j)).elim)
  exact hs.symm.trans (hA.2 i)

/-- Transposing gives the column-leaf alternative, with no positivity
assumption on the numerical entries, only nonempty column support. -/
theorem IsRigid.exists_column_leaf [Nonempty C] {A : R → C → ℝ}
    (hA : IsRigid A) (hpos : ∀ j, 0 < rowDegree (fun j i => A i j) j)
    (hsize : Fintype.card R ≤ Fintype.card C) :
    ∃ j, rowDegree (fun j i => A i j) j = 1 :=
  hA.transpose.exists_row_leaf hpos hsize

/-- With strictly more nonempty columns than rows there are at least two
column leaves, so one can avoid the distinguished spectator column. -/
theorem IsRigid.exists_column_leaf_ne {A : R → C → ℝ} (hA : IsRigid A)
    (hpos : ∀ j, 0 < rowDegree (fun j i => A i j) j)
    (hsize : Fintype.card R < Fintype.card C) (spectator : C) :
    ∃ j, j ≠ spectator ∧ rowDegree (fun j i => A i j) j = 1 := by
  classical
  letI : Nonempty C := ⟨spectator⟩
  have h := hA.transpose.card_add_one_le_columns_add_leaves hpos
  by_contra hn
  push Not at hn
  have hs : rowLeaves (fun j i => A i j) ⊆ {spectator} := by
    intro j hj
    have hl := (Finset.mem_filter.mp hj).2
    exact Finset.mem_singleton.mpr (by by_contra he; exact hn j he hl)
  have hc := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  omega

end TSPGap.CapacityMatrix

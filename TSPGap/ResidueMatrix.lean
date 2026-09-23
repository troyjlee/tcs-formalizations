/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ResidueBasis
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-!
# Residue tables and their stochastic matrices

Nonnegative residues of proper quotients with one common split denominator
form a table. Polynomial derivative and Euler identities determine its row
and weighted-row sums; top coefficients determine its column sums. Repeating
each root row with the root's multiplicity and dividing by that multiplicity
produces a matrix with row sums one.

The inputs here are polynomial identities, not additional assumptions on a
probability theorem. `HomogeneousProductization` supplies them from the
homogeneous line construction before using this matrix for stable polynomials.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*}

/-- All numerators expressed against the original denominator's roots. -/
structure ResidueTable (q : Polynomial ℝ) (r : ι → Polynomial ℝ) where
  entry : ℝ → ι → ℝ
  nonneg : ∀ a j, 0 ≤ entry a j
  off_roots : ∀ a ∉ q.roots.toFinset, ∀ j, entry a j = 0
  expansion : ∀ j, r j = ∑ a ∈ q.roots.toFinset,
    C (entry a j) * (q /ₘ (X - C a))

/-- The analytic quotient theorem constructs every entry, including canceled
and zero columns; no row/column identities are postulated here. -/
theorem exists_residueTable {q : Polynomial ℝ} (hq : q.Monic) (hs : q.Splits)
    {r : ι → Polynomial ℝ} (hdeg : ∀ j, (r j).degree < q.degree)
    (him : ∀ j, HasNonposImaginaryQuotient (r j) q) : Nonempty (ResidueTable q r) := by
  classical
  choose c hc hz he using fun j =>
    nonnegative_residues_common_denominator hq hs (hdeg j) (him j)
  exact ⟨⟨fun a j => c j a, fun a j => hc j a,
    fun a ha j => hz j a ha, he⟩⟩

namespace ResidueTable

variable {q : Polynomial ℝ} {r : ι → Polynomial ℝ} (t : ResidueTable q r)

/-- Each column's sum is its numerator's top possible coefficient. -/
theorem column_sum (hq : q.Monic) (j : ι) :
    (∑ a ∈ q.roots.toFinset, t.entry a j) = (r j).coeff (q.natDegree - 1) :=
  sum_residues_eq_coeff hq (t.expansion j)

variable [Fintype ι]

/-- Finite weighted sums of numerators correspond to weighted sums of entries. -/
theorem weighted_expansion (u : ι → ℝ) :
    (∑ j, C (u j) * r j) = ∑ a ∈ q.roots.toFinset,
      C (∑ j, u j * t.entry a j) * (q /ₘ (X - C a)) := by
  classical
  simp_rw [t.expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, mul_assoc]

/-- The derivative identity fixes each row sum at the root's multiplicity. -/
theorem row_sum (hq : q.Monic) (hs : q.Splits) (hr : ∑ j, r j = q.derivative)
    {a : ℝ} (ha : a ∈ q.roots.toFinset) :
    (∑ j, t.entry a j) = q.roots.count a := by
  have h := t.weighted_expansion (fun _ => 1)
  simp only [map_one, one_mul] at h
  exact residues_unique hq.ne_zero
    (h.symm.trans (hr.trans (derivative_eq_sum_residues hq hs))) a ha

/-- Euler's identity fixes the weighted row sum at root times multiplicity. -/
theorem weighted_row_sum (hq : q.Monic) (hs : q.Splits) (u : ι → ℝ)
    (hr : ∑ j, C (u j) * r j = X * q.derivative - C (q.natDegree : ℝ) * q)
    {a : ℝ} (ha : a ∈ q.roots.toFinset) :
    (∑ j, u j * t.entry a j) = a * (q.roots.count a : ℝ) := by
  exact residues_unique hq.ne_zero
    ((t.weighted_expansion u).symm.trans
      (hr.trans (eulerRemainder_eq_sum_residues hq hs))) a ha

end ResidueTable

/-- One row for each occurrence of a root, not just each distinct root. -/
def RootOccurrence (q : Polynomial ℝ) :=
  Σ a : {a : ℝ // a ∈ q.roots.toFinset}, Fin (q.roots.count a.val)

noncomputable instance (q : Polynomial ℝ) : Fintype (RootOccurrence q) := by
  classical
  unfold RootOccurrence
  infer_instance

/-- The real root labeling a repeated row. -/
def RootOccurrence.value {q : Polynomial ℝ} (a : RootOccurrence q) : ℝ := a.1.val

/-- The row's multiplicity is positive by membership, not by a separate
nondegeneracy hypothesis. -/
theorem RootOccurrence.count_pos {q : Polynomial ℝ} (a : RootOccurrence q) :
    0 < q.roots.count a.value :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp a.1.property)

/-- The number of repeated rows is the denominator degree. -/
theorem card_rootOccurrence {q : Polynomial ℝ} (hs : q.Splits) :
    Fintype.card (RootOccurrence q) = q.natDegree := by
  classical
  change Fintype.card (Σ a : {a : ℝ // a ∈ q.roots.toFinset},
    Fin (q.roots.count a.val)) = q.natDegree
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_subtype q.roots.toFinset (fun _ => Iff.rfl) (fun a => q.roots.count a),
    Multiset.toFinset_sum_count_eq, hs.natDegree_eq_card_roots]

/-- Repeated rows reproduce products over the roots multiset. -/
theorem prod_rootOccurrence (q : Polynomial ℝ) (f : ℝ → ℝ) :
    (∏ a : RootOccurrence q, f a.value) = (q.roots.map f).prod := by
  classical
  change (∏ a : Σ a : {a : ℝ // a ∈ q.roots.toFinset}, Fin (q.roots.count a.val),
    f a.1.val) = _
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_subtype q.roots.toFinset (fun _ => Iff.rfl)
    (fun a => f a ^ q.roots.count a)]
  exact (Finset.prod_multiset_map_count q.roots f).symm

namespace ResidueTable

variable {q : Polynomial ℝ} {r : ι → Polynomial ℝ} (t : ResidueTable q r)

/-- Repeat a residue row with its multiplicity, dividing each copy by that
multiplicity. All actual rows have a positive divisor. -/
noncomputable def matrix (a : RootOccurrence q) (j : ι) : ℝ :=
  t.entry a.value j / q.roots.count a.value

theorem matrix_nonneg (a : RootOccurrence q) (j : ι) : 0 ≤ t.matrix a j :=
  div_nonneg (t.nonneg _ _) (Nat.cast_nonneg _)

/-- Repeating and normalizing rows preserves each column sum exactly. -/
theorem matrix_column_sum (hq : q.Monic) (j : ι) :
    (∑ a : RootOccurrence q, t.matrix a j) = (r j).coeff (q.natDegree - 1) := by
  classical
  change (∑ a : Σ a : {a : ℝ // a ∈ q.roots.toFinset}, Fin (q.roots.count a.val),
    t.entry a.1.val j / q.roots.count a.1.val) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    (∑ a : {a : ℝ // a ∈ q.roots.toFinset},
        (q.roots.count a.val : ℝ) * (t.entry a.val j / q.roots.count a.val)) =
        ∑ a : {a : ℝ // a ∈ q.roots.toFinset}, t.entry a.val j := by
      apply Finset.sum_congr rfl
      intro a ha
      have hpos : (0 : ℝ) < q.roots.count a.val := by
        exact_mod_cast (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp a.property))
      exact mul_div_cancel₀ _ hpos.ne'
    _ = _ := by
      rw [← Finset.sum_subtype q.roots.toFinset (fun _ => Iff.rfl) (fun a => t.entry a j)]
      exact t.column_sum hq j

variable [Fintype ι]

theorem matrix_row_sum (hq : q.Monic) (hs : q.Splits)
    (hr : ∑ j, r j = q.derivative) (a : RootOccurrence q) :
    (∑ j, t.matrix a j) = 1 := by
  simp only [matrix, RootOccurrence.value, ← Finset.sum_div]
  rw [t.row_sum hq hs hr a.1.property]
  exact div_self (by exact_mod_cast a.count_pos.ne')

theorem matrix_weighted_row_sum (hq : q.Monic) (hs : q.Splits) (u : ι → ℝ)
    (hr : ∑ j, C (u j) * r j = X * q.derivative - C (q.natDegree : ℝ) * q)
    (a : RootOccurrence q) : (∑ j, u j * t.matrix a j) = a.value := by
  simp only [matrix, RootOccurrence.value, ← mul_div_assoc, ← Finset.sum_div]
  rw [t.weighted_row_sum hq hs u hr a.1.property]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast a.count_pos.ne')

/-- The product of the matrix's linear forms has exactly the root product
prescribed by the denominator. The homogeneous-line bridge identifies
this product with the original multivariate polynomial's value. -/
theorem matrix_product (hq : q.Monic) (hs : q.Splits) (u : ι → ℝ)
    (hr : ∑ j, C (u j) * r j = X * q.derivative - C (q.natDegree : ℝ) * q) :
    (∏ a : RootOccurrence q, ∑ j, u j * t.matrix a j) = q.roots.prod := by
  simp_rw [t.matrix_weighted_row_sum hq hs u hr]
  simpa using prod_rootOccurrence q id

end ResidueTable

end TSPGap

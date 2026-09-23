/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HomogeneousLine
import TSPGap.ResidueMatrix

/-!
# Productization of a homogeneous stable polynomial

For every real evaluation vector, a normalized homogeneous stable polynomial
admits a nonnegative matrix whose rows sum to one, whose columns sum to its
gradient at one, and whose product of linear forms is the polynomial's value
at that vector. The matrix may depend on the evaluation vector.

The proof constructs, rather than assumes, the derivative and Euler residue
identities. Repeated roots give repeated rows, and zero gradient coordinates
are allowed. No distinct-root perturbation, multiaffinity, or positive
coefficient assumption is used. The stability hypothesis is the raw predicate
underlying `IsRealStable`, avoiding a dependency on the measure layer.

The capacity lower bound and coefficient extraction are separate theorems;
this module does not yet strengthen a probability or gap constant.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*} {p : MvPolynomial ι ℝ}

/-- Every translated diagonal line stays in the upper half-plane. -/
theorem aeval_diagonalLine_ne_zero
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (u : ι → ℝ) {t : ℂ} (ht : 0 < t.im) :
    aeval t (diagonalLine u p) ≠ 0 := by
  rw [aeval_diagonalLine]
  apply hst
  intro i
  simpa using ht

/-- Real coefficients exclude the lower half-plane by conjugation. -/
theorem im_eq_zero_of_aeval_diagonalLine
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (u : ι → ℝ) {t : ℂ} (ht : aeval t (diagonalLine u p) = 0) : t.im = 0 := by
  by_contra him
  rcases lt_or_gt_of_ne him with hlt | hgt
  · have hc : aeval ((starRingEnd ℂ) t) (diagonalLine u p) = 0 := by
      rw [aeval_conj, ht, map_zero]
    exact aeval_diagonalLine_ne_zero hst u (by simpa using neg_pos.mpr hlt) hc
  · exact aeval_diagonalLine_ne_zero hst u hgt ht

/-- The denominator splits over the reals, including repeated roots. -/
theorem splits_diagonalLine
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (u : ι → ℝ) : (diagonalLine u p).Splits := by
  apply Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
    Complex.ofReal_injective (IsAlgClosed.splits _)
  intro a ha
  have hz : aeval a (diagonalLine u p) = 0 := by
    simpa only [IsRoot, eval_map, aeval_def] using (mem_roots'.mp ha).2
  have hi := im_eq_zero_of_aeval_diagonalLine hst u hz
  refine ⟨a.re, ?_⟩
  apply Complex.ext <;> simp [hi]

/-- Stability supplies the quotient sign for every coordinate numerator. -/
theorem diagonalLine_pderiv_quotient
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (u : ι → ℝ) (j : ι) :
    HasNonposImaginaryQuotient (diagonalLine u (MvPolynomial.pderiv j p))
      (diagonalLine u p) := by
  intro t ht
  simp only [aeval_diagonalLine]
  have h := mvPolynomial_logDeriv_im_nonpos (p.map (algebraMap ℝ ℂ)) hst
    (fun i => t - (u i : ℂ)) (fun i => by simpa using ht) j
  rwa [MvPolynomial.pderiv_map] at h

/-- Differentiation lowers the degree enough to make every quotient proper,
even when a coordinate numerator is identically zero. -/
theorem degree_diagonalLine_pderiv_lt {d : ℕ} (hd : 0 < d)
    (hp : p.IsHomogeneous d) (h1 : MvPolynomial.eval (fun _ => 1) p = 1)
    (u : ι → ℝ) (j : ι) :
    (diagonalLine u (MvPolynomial.pderiv j p)).degree < (diagonalLine u p).degree := by
  obtain ⟨hq, hdeg⟩ := monic_diagonalLine u hp h1
  rw [degree_eq_natDegree hq.ne_zero, hdeg]
  exact (degree_le_of_natDegree_le (natDegree_diagonalLine_le u hp.pderiv)).trans_lt
    (by exact_mod_cast Nat.sub_lt hd (by decide : 0 < 1))

/-- The sign in the root product cancels the sign from evaluating at `-u`. -/
theorem roots_prod_diagonalLine {d : ℕ}
    (hp : p.IsHomogeneous d) (h1 : MvPolynomial.eval (fun _ => 1) p = 1)
    (u : ι → ℝ) (hs : (diagonalLine u p).Splits) :
    (diagonalLine u p).roots.prod = MvPolynomial.eval u p := by
  obtain ⟨hq, hdeg⟩ := monic_diagonalLine u hp h1
  have h := hs.coeff_zero_eq_prod_roots_of_monic hq
  rw [coeff_zero_eq_eval_zero, eval_diagonalLine, hdeg] at h
  have he := eval_scale_homogeneous hp (-1) u
  simp only [neg_one_mul, zero_sub] at he h
  rw [he] at h
  exact (mul_left_cancel₀ (pow_ne_zero d (by norm_num : (-1 : ℝ) ≠ 0)) h).symm

/-- The constructed residue table for a normalized homogeneous stable
polynomial; all analytic and polynomial-identity inputs are discharged. -/
theorem exists_diagonalLine_residueTable {d : ℕ} (hd : 0 < d)
    (hp : p.IsHomogeneous d) (h1 : MvPolynomial.eval (fun _ => 1) p = 1)
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (u : ι → ℝ) :
    Nonempty (ResidueTable (diagonalLine u p)
      (fun j => diagonalLine u (MvPolynomial.pderiv j p))) :=
  exists_residueTable (monic_diagonalLine u hp h1).1 (splits_diagonalLine hst u)
    (degree_diagonalLine_pderiv_lt hd hp h1 u) (diagonalLine_pderiv_quotient hst u)

variable [Fintype ι]

/-- Homogeneous productization at every real vector. The degree is positive;
the matrix has exactly `d` rows. Its column sums are the original gradient,
not an approximation, and its product identity is exact. -/
theorem homogeneous_productization {d : ℕ} (hd : 0 < d)
    (hp : p.IsHomogeneous d) (h1 : MvPolynomial.eval (fun _ => 1) p = 1)
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (u : ι → ℝ) :
    Fintype.card (RootOccurrence (diagonalLine u p)) = d ∧
    ∃ A : RootOccurrence (diagonalLine u p) → ι → ℝ,
      (∀ a j, 0 ≤ A a j) ∧
      (∀ a, ∑ j, A a j = 1) ∧
      (∀ j, ∑ a, A a j = MvPolynomial.eval (fun _ => 1) (MvPolynomial.pderiv j p)) ∧
      (∏ a, ∑ j, u j * A a j) = MvPolynomial.eval u p := by
  obtain ⟨hq, hdeg⟩ := monic_diagonalLine u hp h1
  have hs := splits_diagonalLine hst u
  obtain ⟨t⟩ := exists_diagonalLine_residueTable hd hp h1 hst u
  have he : ∑ j, C (u j) * diagonalLine u (MvPolynomial.pderiv j p) =
      X * (diagonalLine u p).derivative -
        C ((diagonalLine u p).natDegree : ℝ) * diagonalLine u p := by
    rw [hdeg]
    exact euler_diagonalLine u hp
  refine ⟨(card_rootOccurrence hs).trans hdeg, t.matrix, t.matrix_nonneg,
    t.matrix_row_sum hq hs (derivative_diagonalLine u p).symm, ?_, ?_⟩
  · intro j
    rw [t.matrix_column_sum hq, hdeg, coeff_diagonalLine_homogeneous u hp.pderiv]
  · exact (t.matrix_product hq hs u he).trans (roots_prod_diagonalLine hp h1 u hs)

end TSPGap

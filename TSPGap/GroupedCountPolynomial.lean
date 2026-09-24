/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Stable
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Grouped count polynomials with support baselines

An arbitrary map assigns each coordinate to a block. Subtracting a fixed
exponent vector records a count baseline, not a choice of deterministic
coordinates. Under a support lower bound the resulting polynomial is an exact
monomial quotient of the renamed generating polynomial. Its normalization,
gradient and homogeneous degree are computed directly from the finite sum.

The algebra allows signed weights; nonnegativity is needed only for the
coefficient-sign export. Stability follows by cancellation of the baseline
monomial, with no boundary specialization.
-/

namespace TSPGap

open MvPolynomial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- Count how many selected coordinates are assigned to each block. -/
noncomputable def groupedCountExponent (f : ι → κ) (S : Finset ι) : κ →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single (f i) 1

/-- Group the generating polynomial and subtract a prescribed count baseline.
The subtraction is meaningful as a quotient only under the support bound. -/
noncomputable def groupedCountPoly (w : Finset ι → ℝ) (f : ι → κ)
    (β : κ →₀ ℕ) : MvPolynomial κ ℝ :=
  ∑ S : Finset ι, monomial (groupedCountExponent f S - β) (w S)

omit [Fintype ι] [DecidableEq ι] in
theorem groupedCountExponent_apply (f : ι → κ) (S : Finset ι) (j : κ) :
    groupedCountExponent f S j = (S.filter (fun i => f i = j)).card := by
  simp [groupedCountExponent, Finsupp.single_apply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem degree_groupedCountExponent (f : ι → κ) (S : Finset ι) :
    (groupedCountExponent f S).degree = S.card := by
  simp [groupedCountExponent]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem monomial_groupedCountExponent (f : ι → κ) (S : Finset ι) :
    monomial (groupedCountExponent f S) (1 : ℝ) = ∏ i ∈ S, X (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [groupedCountExponent]
  | @insert i S hi ih =>
    rw [groupedCountExponent, Finset.sum_insert hi, Finset.prod_insert hi]
    rw [show (1 : ℝ) = 1 * 1 by ring, ← monomial_mul]
    change X (f i) * monomial (groupedCountExponent f S) 1 = _
    rw [ih]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Normalization survives grouping and subtraction of any baseline. -/
theorem eval_one_groupedCountPoly (w : Finset ι → ℝ) (f : ι → κ)
    (β : κ →₀ ℕ) :
    eval (fun _ => 1) (groupedCountPoly w f β) = ∑ S : Finset ι, w S := by
  simp [groupedCountPoly, eval_monomial]

omit [DecidableEq ι] [DecidableEq κ] in
/-- All coefficients are nonnegative when the original weights are. -/
theorem coeff_groupedCountPoly_nonneg {w : Finset ι → ℝ}
    (hw : ∀ S, 0 ≤ w S) (f : ι → κ) (β d : κ →₀ ℕ) :
    0 ≤ (groupedCountPoly w f β).coeff d := by
  classical
  rw [groupedCountPoly, coeff_sum]
  apply Finset.sum_nonneg
  intro S _
  rw [coeff_monomial]
  split_ifs
  · exact hw S
  · exact le_rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- The raw derivative formula retains truncated subtraction explicitly. -/
theorem eval_pderiv_groupedCountPoly (w : Finset ι → ℝ) (f : ι → κ)
    (β : κ →₀ ℕ) (j : κ) :
    eval (fun _ => 1) (pderiv j (groupedCountPoly w f β)) =
      ∑ S : Finset ι, w S * ((groupedCountExponent f S - β) j : ℝ) := by
  simp [groupedCountPoly, eval_monomial]

omit [DecidableEq ι] [DecidableEq κ] in
/-- A support baseline subtracts precisely that baseline times total mass
from each grouped first moment; no normalization is silently assumed. -/
theorem eval_pderiv_groupedCountPoly_of_support (w : Finset ι → ℝ) (f : ι → κ)
    (β : κ →₀ ℕ) (hβ : ∀ S, w S ≠ 0 → β ≤ groupedCountExponent f S) (j : κ) :
    eval (fun _ => 1) (pderiv j (groupedCountPoly w f β)) =
      (∑ S : Finset ι, w S * (groupedCountExponent f S j : ℝ)) -
        (β j : ℝ) * ∑ S : Finset ι, w S := by
  classical
  rw [eval_pderiv_groupedCountPoly, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : w S = 0
  · simp [hS]
  · rw [Finsupp.tsub_apply, Nat.cast_sub (hβ S hS j)]
    ring

omit [DecidableEq κ] in
/-- The shifted polynomial is an exact monomial quotient. The lower bound
is imposed only on sets carrying nonzero weight. -/
theorem monomial_mul_groupedCountPoly (w : Finset ι → ℝ) (f : ι → κ)
    (β : κ →₀ ℕ) (hβ : ∀ S, w S ≠ 0 → β ≤ groupedCountExponent f S) :
    monomial β (1 : ℝ) * groupedCountPoly w f β = rename f (genPoly w) := by
  classical
  rw [groupedCountPoly, Finset.mul_sum, genPoly, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : w S = 0
  · simp [hS]
  · rw [monomial_mul, one_mul, add_tsub_cancel_of_le (hβ S hS)]
    rw [map_mul, rename_C, map_prod]
    simp only [rename_X]
    rw [← monomial_groupedCountExponent]
    simp only [C_mul_monomial, mul_one]

omit [DecidableEq κ] in
theorem groupedCountPoly_zero (w : Finset ι → ℝ) (f : ι → κ) :
    groupedCountPoly w f 0 = rename f (genPoly w) := by
  simpa using monomial_mul_groupedCountPoly w f 0 (fun _ _ => zero_le)

omit [DecidableEq κ] in
/-- Grouping and removing a supported baseline preserve real stability. -/
theorem isRealStable_groupedCountPoly {w : Finset ι → ℝ}
    (hst : IsRealStable (genPoly w)) (f : ι → κ) (β : κ →₀ ℕ)
    (hβ : ∀ S, w S ≠ 0 → β ≤ groupedCountExponent f S) :
    IsRealStable (groupedCountPoly w f β) := by
  have h := hst.rename f
  rw [← monomial_mul_groupedCountPoly w f β hβ] at h
  intro z hz hzero
  have hne := h z hz
  simp only [map_mul, hzero, mul_zero] at hne
  exact hne rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- Fixed rank becomes homogeneous degree `r - degree β`. Zero weights
require no rank or baseline condition. -/
theorem isHomogeneous_groupedCountPoly {w : Finset ι → ℝ} {r : ℕ}
    (hr : ∀ S, w S ≠ 0 → S.card = r) (f : ι → κ) (β : κ →₀ ℕ)
    (hβ : ∀ S, w S ≠ 0 → β ≤ groupedCountExponent f S) :
    (groupedCountPoly w f β).IsHomogeneous (r - β.degree) := by
  classical
  apply IsHomogeneous.sum
  intro S _
  by_cases hS : w S = 0
  · simp only [hS, monomial_zero]
    exact isHomogeneous_zero (R := ℝ) _ _
  · apply isHomogeneous_monomial (w S)
    have hd := congrArg Finsupp.degree (add_tsub_cancel_of_le (hβ S hS))
    rw [map_add, degree_groupedCountExponent, hr S hS] at hd
    omega

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HomogeneousLine
import TSPGap.UnivariateCapacity

/-!
# A single coefficient-extraction step for homogeneous stable polynomials

Freeze all but one coordinate at positive real values. Homogeneous scaling
moves a hypothetical upper-half-plane root into the full open half-plane,
so the resulting univariate polynomial splits over the reals. Combining this
with the one-variable capacity estimate bounds the derivative evaluated with
the extracted coordinate set to zero.

This proves one extraction step, not closure under repeated extraction.
No assertion of general boundary-specialization stability is used.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*} [DecidableEq ι]

/-- Freeze the other coordinates over the real coefficient field. -/
noncomputable def realCoordinateSlice (x : ι → ℝ) (j : ι) :
    MvPolynomial ι ℝ →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom C (Function.update (fun i => C (x i)) j X)

/-- The real slice evaluates at the updated vector. -/
theorem eval_realCoordinateSlice (x : ι → ℝ) (j : ι) (p : MvPolynomial ι ℝ) (t : ℝ) :
    (realCoordinateSlice x j p).eval t = MvPolynomial.eval (Function.update x j t) p := by
  have hhom : (evalRingHom t).comp (realCoordinateSlice x j) =
      MvPolynomial.eval (Function.update x j t) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [realCoordinateSlice]
    · intro i
      by_cases hi : i = j <;> simp [realCoordinateSlice, Function.update_apply, hi]
  exact DFunLike.congr_fun hhom p

/-- Complex evaluation uses the same update, after complexification. -/
theorem aeval_realCoordinateSlice (x : ι → ℝ) (j : ι) (p : MvPolynomial ι ℝ) (t : ℂ) :
    aeval t (realCoordinateSlice x j p) =
      MvPolynomial.eval (Function.update (fun i => (x i : ℂ)) j t)
        (p.map (algebraMap ℝ ℂ)) := by
  have hhom : (aeval t).toRingHom.comp (realCoordinateSlice x j) =
      MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
        (Function.update (fun i => (x i : ℂ)) j t) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [realCoordinateSlice]
    · intro i
      by_cases hi : i = j <;> simp [realCoordinateSlice, Function.update_apply, hi]
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map] using
    DFunLike.congr_fun hhom p

/-- The formal derivative commutes with slicing. -/
theorem derivative_realCoordinateSlice (x : ι → ℝ) (j : ι) (p : MvPolynomial ι ℝ) :
    (realCoordinateSlice x j p).derivative =
      realCoordinateSlice x j (MvPolynomial.pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [realCoordinateSlice]
  | add p q hp hq => simpa only [map_add, derivative_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      change (MvPolynomial.eval₂ C
        (Function.update (fun i => C (x i)) j X) p).derivative =
        MvPolynomial.eval₂ C (Function.update (fun i => C (x i)) j X)
          (MvPolynomial.pderiv j p) at hp
      by_cases hi : i = j
      · subst i
        simp [realCoordinateSlice, derivative_mul, hp, mul_comm]
      · simp [realCoordinateSlice, derivative_mul, hi, hp, mul_comm]

/-- The first slice coefficient is the derivative at the zeroed coordinate. -/
theorem coeff_one_realCoordinateSlice (x : ι → ℝ) (j : ι) (p : MvPolynomial ι ℝ) :
    (realCoordinateSlice x j p).coeff 1 =
      MvPolynomial.eval (Function.update x j 0) (MvPolynomial.pderiv j p) := by
  rw [← eval_realCoordinateSlice, ← derivative_realCoordinateSlice,
    ← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

private theorem coeff_prod_nonneg {κ : Type*} (s : Finset κ) (f : κ → Polynomial ℝ)
    (hf : ∀ i ∈ s, ∀ k, 0 ≤ (f i).coeff k) (k : ℕ) :
    0 ≤ (∏ i ∈ s, f i).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simp only [Finset.prod_empty, coeff_one]; split_ifs <;> norm_num
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, coeff_mul]
      exact Finset.sum_nonneg fun b _ => mul_nonneg
        (hf a (by simp) b.1) (ih (fun i hi => hf i (by simp [hi])) b.2)

/-- Nonnegative multivariate coefficients remain nonnegative in a real
slice. The frozen value of the extracted coordinate is irrelevant. -/
theorem coeff_nonneg_realCoordinateSlice {p : MvPolynomial ι ℝ}
    (hp : ∀ m, 0 ≤ MvPolynomial.coeff m p) (x : ι → ℝ) (j : ι)
    (hx : ∀ i, i ≠ j → 0 ≤ x i) (k : ℕ) :
    0 ≤ (realCoordinateSlice x j p).coeff k := by
  classical
  change 0 ≤ (MvPolynomial.eval₂ C (Function.update (fun i => C (x i)) j X) p).coeff k
  rw [MvPolynomial.eval₂_eq, finsetSum_coeff]
  apply Finset.sum_nonneg
  intro m _
  rw [coeff_C_mul]
  apply mul_nonneg (hp m)
  apply coeff_prod_nonneg
  intro i _ l
  by_cases hi : i = j
  · simp only [Function.update_apply, hi, ite_true, coeff_X_pow]
    split_ifs <;> norm_num
  · simp only [Function.update_apply, hi, ite_false, ← map_pow, coeff_C]
    split_ifs
    · exact pow_nonneg (hx i hi) _
    · exact le_rfl

omit [DecidableEq ι] in
/-- Homogeneous scaling after complexification, with no normalization. -/
theorem eval_complex_scale_homogeneous {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : ℂ) (z : ι → ℂ) :
    MvPolynomial.eval (fun i => c * z i) (p.map (algebraMap ℝ ℂ)) =
      c ^ d * MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) := by
  classical
  simp only [MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, homogeneous_support_sum hp hm]
  ring

/-- Positive frozen coordinates permit a homogeneous tilt into the open
half-plane. This is not a general boundary-specialization theorem. -/
theorem aeval_realCoordinateSlice_ne_zero {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d)
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (x : ι → ℝ) (j : ι) (hx : ∀ i, i ≠ j → 0 < x i)
    {t : ℂ} (ht : 0 < t.im) : aeval t (realCoordinateSlice x j p) ≠ 0 := by
  intro hzero
  rw [aeval_realCoordinateSlice] at hzero
  let δ : ℝ := t.im / (2 * (|t.re| + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let lam : ℂ := 1 + (δ : ℂ) * Complex.I
  have hre : lam.re = 1 := by simp [lam]
  have him : lam.im = δ := by simp [lam]
  have hkey : 0 < t.im + δ * t.re := by
    have hmul : δ * (-|t.re|) ≤ δ * t.re :=
      mul_le_mul_of_nonneg_left (neg_abs_le t.re) hδ.le
    have heq : δ * (2 * (|t.re| + 1)) = t.im := by dsimp [δ]; field_simp
    nlinarith [mul_nonneg hδ.le (abs_nonneg t.re)]
  have hall : ∀ i : ι,
      0 < (lam * Function.update (fun i => (x i : ℂ)) j t i).im := by
    intro i
    by_cases hi : i = j
    · simp only [Function.update_apply, hi, ite_true, Complex.mul_im, hre, him, one_mul]
      linarith
    · simp only [Function.update_apply, hi, ite_false, Complex.mul_im, hre, him,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
      exact mul_pos hδ (hx i hi)
  apply hst _ hall
  rw [eval_complex_scale_homogeneous hp, hzero, mul_zero]

/-- The homogeneous slice splits over the real numbers, including constant
slices. Positivity is required only off the extracted coordinate. -/
theorem splits_realCoordinateSlice {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d)
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (x : ι → ℝ) (j : ι) (hx : ∀ i, i ≠ j → 0 < x i) :
    (realCoordinateSlice x j p).Splits := by
  apply Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
    Complex.ofReal_injective (IsAlgClosed.splits _)
  intro a ha
  have hz : aeval a (realCoordinateSlice x j p) = 0 := by
    simpa only [IsRoot, eval_map, aeval_def] using (mem_roots'.mp ha).2
  have hi : a.im = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hc : aeval ((starRingEnd ℂ) a) (realCoordinateSlice x j p) = 0 := by
        rw [aeval_conj, hz, map_zero]
      exact aeval_realCoordinateSlice_ne_zero hp hst x j hx (by simpa using neg_pos.mpr hlt) hc
    · exact aeval_realCoordinateSlice_ne_zero hp hst x j hx hgt hz
  refine ⟨a.re, ?_⟩
  apply Complex.ext <;> simp [hi]

/-- **One homogeneous extraction step.** A uniform linear lower bound in
one coordinate survives extracting its coefficient at a cost `exp(-1)`.
The scalar `c` may already contain a target monomial in the other variables. -/
theorem homogeneous_capacity_extraction_one {p : MvPolynomial ι ℝ} {d : ℕ} {c : ℝ}
    (hp : p.IsHomogeneous d) (hnn : ∀ m, 0 ≤ MvPolynomial.coeff m p)
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (x : ι → ℝ) (j : ι) (hx : ∀ i, i ≠ j → 0 < x i)
    (hcap : ∀ t : ℝ, 0 < t → c * t ≤ MvPolynomial.eval (Function.update x j t) p) :
    Real.exp (-1) * c ≤ MvPolynomial.eval (Function.update x j 0) (MvPolynomial.pderiv j p) := by
  rw [← coeff_one_realCoordinateSlice]
  exact coeff_one_ge_exp_neg_one_mul_capacity (splits_realCoordinateSlice hp hst x j hx)
    (coeff_nonneg_realCoordinateSlice hnn x j (fun i hi => (hx i hi).le))
    (fun t ht => by rw [eval_realCoordinateSlice]; exact hcap t ht)

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.StableLogDerivative
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Homogeneous polynomials on a translated diagonal line

Substitute `X - u_i` into every coordinate. Homogeneity makes the leading
coefficient the value at the all-one vector. The chain rule and Euler's
identity give the two polynomial identities consumed by `ResidueTable`.
These results do not require nonnegative coefficients or multiaffinity.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*}

/-- Restriction to the line `t ↦ t*1-u`, as a ring homomorphism. -/
noncomputable def diagonalLine (u : ι → ℝ) : MvPolynomial ι ℝ →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom C (fun i => X - C (u i))

@[simp] theorem diagonalLine_C (u : ι → ℝ) (c : ℝ) :
    diagonalLine u (MvPolynomial.C c) = C c := MvPolynomial.eval₂Hom_C _ _ _

@[simp] theorem diagonalLine_X (u : ι → ℝ) (i : ι) :
    diagonalLine u (MvPolynomial.X i) = X - C (u i) := by
  exact MvPolynomial.eval₂_X C (fun j => X - C (u j)) i

theorem eval_diagonalLine (u : ι → ℝ) (p : MvPolynomial ι ℝ) (t : ℝ) :
    (diagonalLine u p).eval t = MvPolynomial.eval (fun i => t - u i) p := by
  have hhom : (evalRingHom t).comp (diagonalLine u) =
      MvPolynomial.eval (fun i => t - u i) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp
  exact DFunLike.congr_fun hhom p

theorem aeval_diagonalLine (u : ι → ℝ) (p : MvPolynomial ι ℝ) (t : ℂ) :
    aeval t (diagonalLine u p) =
      MvPolynomial.eval (fun i => t - (u i : ℂ)) (p.map (algebraMap ℝ ℂ)) := by
  have hhom : (aeval t).toRingHom.comp (diagonalLine u) =
      MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) (fun i => t - (u i : ℂ)) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map] using
    DFunLike.congr_fun hhom p

/-- Exponent sum of a monomial on a homogeneous polynomial's support. -/
theorem homogeneous_support_sum {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) {m : ι →₀ ℕ} (hm : m ∈ p.support) :
    (∑ i ∈ m.support, m i) = d := by
  simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
    hp (MvPolynomial.mem_support_iff.mp hm)

/-- Every substituted monomial has its original total degree. -/
theorem diagonalMonomial_natDegree (u : ι → ℝ) (m : ι →₀ ℕ) :
    (∏ i ∈ m.support, (X - C (u i)) ^ m i).natDegree = ∑ i ∈ m.support, m i := by
  classical
  rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (u i)).pow (m i))]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]

theorem natDegree_diagonalLine_le (u : ι → ℝ) {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) : (diagonalLine u p).natDegree ≤ d := by
  classical
  change (MvPolynomial.eval₂ C (fun i => X - C (u i)) p).natDegree ≤ d
  rw [MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  exact (natDegree_C_mul_le _ _).trans
    ((diagonalMonomial_natDegree u m).trans (homogeneous_support_sum hp hm)).le

/-- Homogeneity identifies the top coefficient even when it vanishes. -/
theorem coeff_diagonalLine_homogeneous (u : ι → ℝ) {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (diagonalLine u p).coeff d = MvPolynomial.eval (fun _ => 1) p := by
  classical
  change (MvPolynomial.eval₂ C (fun i => X - C (u i)) p).coeff d = _
  rw [MvPolynomial.eval₂_eq, finsetSum_coeff, MvPolynomial.eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  apply Finset.sum_congr rfl
  intro m hm
  have hmonic : (∏ i ∈ m.support, (X - C (u i)) ^ m i).Monic :=
    monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (u i)).pow (m i))
  have hdeg := (diagonalMonomial_natDegree u m).trans (homogeneous_support_sum hp hm)
  rw [coeff_C_mul, ← hdeg, hmonic.coeff_natDegree, mul_one]

/-- Normalization prevents cancellation of the leading coefficient. -/
theorem monic_diagonalLine (u : ι → ℝ) {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (h1 : MvPolynomial.eval (fun _ => 1) p = 1) :
    (diagonalLine u p).Monic ∧ (diagonalLine u p).natDegree = d := by
  have hc : (diagonalLine u p).coeff d = 1 := (coeff_diagonalLine_homogeneous u hp).trans h1
  have hd := natDegree_eq_of_le_of_coeff_ne_zero (natDegree_diagonalLine_le u hp)
    (hc ▸ one_ne_zero)
  refine ⟨?_, hd⟩
  change (diagonalLine u p).coeff (diagonalLine u p).natDegree = 1
  rwa [hd]

/-- Scaling the evaluation vector uses only homogeneity, not stability. -/
theorem eval_scale_homogeneous {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : ℝ) (u : ι → ℝ) :
    MvPolynomial.eval (fun i => c * u i) p = c ^ d * MvPolynomial.eval u p := by
  classical
  simp only [MvPolynomial.eval_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, homogeneous_support_sum hp hm]
  ring

variable [Fintype ι]

/-- The diagonal chain rule, proved by polynomial induction. -/
theorem derivative_diagonalLine (u : ι → ℝ) (p : MvPolynomial ι ℝ) :
    (diagonalLine u p).derivative = ∑ j, diagonalLine u (MvPolynomial.pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p i hp =>
      have hx : (∑ j, diagonalLine u (MvPolynomial.pderiv j (MvPolynomial.X i))) = 1 := by
        simp [MvPolynomial.pderiv_X, Pi.single_apply]
      simp only [map_mul, diagonalLine_X, derivative_mul, derivative_X_sub_C, mul_one,
        MvPolynomial.pderiv_mul, map_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hx, mul_one, hp]

/-- Euler's identity on the translated diagonal line. -/
theorem euler_diagonalLine (u : ι → ℝ) {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (∑ j, C (u j) * diagonalLine u (MvPolynomial.pderiv j p)) =
      X * (diagonalLine u p).derivative - C (d : ℝ) * diagonalLine u p := by
  have h := congrArg (diagonalLine u) hp.sum_X_mul_pderiv
  simp only [map_sum, map_mul, diagonalLine_X, nsmul_eq_mul] at h
  simp_rw [sub_mul] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← derivative_diagonalLine] at h
  simp only [map_natCast] at h ⊢
  linear_combination -h

end TSPGap

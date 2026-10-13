/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Substituting a scalar for one polynomial variable

These are symbolic polynomials. No running-time claim is made about their
representation or evaluation; the verifier will need a separate implementation.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

/-- Substitute `a` for variable `i`, leaving the other variables unchanged. -/
def restrict (i : σ) (a : R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (Function.update X i (C a))

@[simp] theorem restrict_C (i : σ) (a b : R) : restrict i a (C b) = C b := by
  simp [restrict]

@[simp] theorem restrict_X_self (i : σ) (a : R) : restrict i a (X i) = C a := by
  simp [restrict]

@[simp] theorem restrict_X_of_ne (i j : σ) (a : R) (h : j ≠ i) :
    restrict i a (X j) = X j := by
  simp [restrict, h]

/-- Polynomial substitution agrees with updating an evaluation assignment. -/
theorem eval_restrict (x : σ → R) (i : σ) (a : R) (p : MvPolynomial σ R) :
    eval x (restrict i a p) = eval (Function.update x i a) p := by
  induction p using MvPolynomial.induction_on with
  | C b => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases h : j = i
    · subst j
      simp [map_mul, hp]
    · simp [map_mul, hp, restrict_X_of_ne i j a h, h]

/-- After substitution, the chosen variable has degree zero. -/
theorem degreeOf_restrict_self (i : σ) (a : R) (p : MvPolynomial σ R) :
    (restrict i a p).degreeOf i = 0 := by
  induction p using MvPolynomial.induction_on with
  | C b => simp
  | add p q hp hq =>
    rw [map_add]
    apply Nat.eq_zero_of_le_zero
    simpa [hp, hq] using degreeOf_add_le i (restrict i a p) (restrict i a q)
  | mul_X p j hp =>
    rw [map_mul]
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_mul_le i _ _).trans
    by_cases h : j = i
    · subst j
      simp [hp]
    · simp [hp, restrict_X_of_ne i j a h, degreeOf_X_of_ne (Ne.symm h)]

/-- A second substitution for an already removed variable has no effect. -/
@[simp] theorem restrict_restrict_same (i : σ) (a b : R) (p : MvPolynomial σ R) :
    restrict i a (restrict i b p) = restrict i b p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases h : j = i
    · subst j
      simp [map_mul, hp]
    · simp [map_mul, hp, restrict_X_of_ne i j a h, restrict_X_of_ne i j b h]

/-- Substitutions in distinct coordinates commute. -/
theorem restrict_comm (i j : σ) (a b : R) (p : MvPolynomial σ R) (h : i ≠ j) :
    restrict i a (restrict j b p) = restrict j b (restrict i a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    by_cases hki : k = i
    · subst k
      simp [map_mul, hp, restrict_X_of_ne j i b h]
    · by_cases hkj : k = j
      · subst k
        simp [map_mul, hp, restrict_X_of_ne i j a (Ne.symm h)]
      · simp [map_mul, hp, restrict_X_of_ne i k a hki, restrict_X_of_ne j k b hkj]

/-- A restricted monomial cannot have a higher exponent in any coordinate. -/
theorem degreeOf_restrict_monomial_le [Nontrivial R] (i j : σ) (a r : R)
    (s : σ →₀ ℕ) : (restrict i a (monomial s r)).degreeOf j ≤ s j := by
  rw [monomial_eq, Finsupp.prod, map_mul, restrict_C, map_prod]
  simp only [map_pow]
  calc
    _ ≤ ∑ k ∈ s.support, (restrict i a (X k) ^ s k).degreeOf j :=
      (degreeOf_C_mul_le _ j r).trans (degreeOf_prod_le j _ _)
    _ ≤ ∑ k ∈ s.support, if k = j then s j else 0 := by
      apply Finset.sum_le_sum
      intro k _
      apply (degreeOf_pow_le j _ _).trans
      by_cases hki : k = i
      · subst k
        simp
      · rw [restrict_X_of_ne i k a hki, degreeOf_X]
        by_cases hkj : k = j
        · subst k
          simp
        · simp [hkj, Ne.symm hkj]
    _ ≤ s j := by
      simp only [Finset.sum_ite_eq']
      split <;> simp

/-- Restriction never increases any individual degree, even when terms cancel. -/
theorem degreeOf_restrict_le [Nontrivial R] (i j : σ) (a : R)
    (p : MvPolynomial σ R) : (restrict i a p).degreeOf j ≤ p.degreeOf j := by
  calc
    _ = (∑ s ∈ p.support, restrict i a (monomial s (p.coeff s))).degreeOf j := by
      rw [← map_sum, ← p.as_sum]
    _ ≤ p.support.sup (fun s => s j) := by
      apply (degreeOf_sum_le j _ _).trans
      apply Finset.sup_le
      intro s hs
      exact (degreeOf_restrict_monomial_le i j a (p.coeff s) s).trans
        (Finset.le_sup (f := fun s : σ →₀ ℕ => s j) hs)
    _ = p.degreeOf j := (degreeOf_eq_sup j p).symm

/-- Restricting a variable absent from the polynomial is the identity. -/
theorem restrict_eq_self_of_not_mem_vars (i : σ) (a : R) (p : MvPolynomial σ R)
    (hi : i ∉ p.vars) : restrict i a p = p := by
  change restrict i a p = (RingHom.id (MvPolynomial σ R)) p
  apply hom_congr_vars (p₁ := p) (p₂ := p) ?_ ?_ rfl
  · ext r
    simp
  · intro j hj _
    have hji : j ≠ i := by rintro rfl; exact hi hj
    simpa using restrict_X_of_ne i j a hji

/-- Substitution removes its coordinate and cannot introduce a different one. -/
theorem vars_restrict_subset [Nontrivial R] (i : σ) (a : R) (p : MvPolynomial σ R) :
    (restrict i a p).vars ⊆ p.vars.erase i := by
  intro j hj
  have hd := mem_vars_iff_degreeOf_ne_zero.mp hj
  apply Finset.mem_erase.mpr
  constructor
  · rintro rfl
    exact hd (degreeOf_restrict_self j a p)
  · by_contra hnot
    have hz : p.degreeOf j = 0 := by simpa [mem_vars_iff_degreeOf_ne_zero] using hnot
    exact hd (Nat.eq_zero_of_le_zero (by simpa [hz] using degreeOf_restrict_le i j a p))

end IPPSPACE

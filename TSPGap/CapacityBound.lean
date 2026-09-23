/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityInduction
import TSPGap.RigidProductization

/-!
# Absolute-profile capacity bounds for stable polynomials

These are uniform pointwise lower bounds by the target monomial, with a
spectator evaluated at one. They need no capacity infimum or attainment.
Zero profile factors are included by nonnegativity, before strict induction.
Coefficient extraction and the probability applications are separate.
-/

namespace TSPGap
namespace CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

/-- Zero profile levels make the bound trivial, rather than invalidating it. -/
theorem rigid_profile_lower_bound_nonneg {A : R → C → ℝ}
    (hA : IsStochastic A) (hrig : IsRigid A) (s : C) (κ : C → ℕ) (b : ℕ → ℝ)
    (hκ : ∀ j, j ≠ s → κ j ≤ 1)
    (hb : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s).card → 0 ≤ b k ∧ b k ≤ 1)
    (hp : AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b)
    {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) (hs : x s = 1) :
    profileProduct b (Finset.univ.erase s).card * targetValue κ x ≤ value A x := by
  by_cases hpos : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s).card → 0 < b k
  · exact rigid_profile_lower_bound hA hrig s κ b hκ
      (fun k hk hn => ⟨hpos k hk hn, (hb k hk hn).2⟩) hp hx hs
  · push Not at hpos
    obtain ⟨k, hk, hn, hnonpos⟩ := hpos
    have hzero : b k = 0 := le_antisymm hnonpos (hb k hk hn).1
    have hprod : profileProduct b (Finset.univ.erase s).card = 0 := by
      apply Finset.prod_eq_zero (i := k - 1)
      · exact Finset.mem_range.mpr (by omega)
      · simpa only [Nat.sub_add_cancel hk] using hzero
    rw [hprod, zero_mul]
    exact value_nonneg hA hx

/-- Rigidity is constructed at the evaluation point, not a hypothesis on
the input stochastic matrix. -/
theorem stochastic_profile_lower_bound {A : R → C → ℝ}
    (hA : IsStochastic A) (s : C) (κ : C → ℕ) (b : ℕ → ℝ)
    (hκ : ∀ j, j ≠ s → κ j ≤ 1)
    (hb : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s).card → 0 ≤ b k ∧ b k ≤ 1)
    (hp : AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) (hs : x s = 1) :
    profileProduct b (Finset.univ.erase s).card * targetValue κ x ≤ value A x := by
  obtain ⟨B, hB, hcols, hval, hrig, _⟩ := exists_rigid_reduction hA hx
  have hpB : AtMostErrorProfile (fun j => columnSum B j - (κ j : ℝ))
      (Finset.univ.erase s) b := hp.congr (fun j _ => by simp only [columnSum, hcols j])
  exact (rigid_profile_lower_bound_nonneg hB hrig s κ b hκ hb hpB
    (fun j => (hx j).le) hs).trans hval

end CapacityMatrix

open CapacityMatrix

/-- The homogeneous stable-polynomial capacity bound in the zero/one target
case. The polynomial need not be multiaffine; the spectator mass may vanish. -/
theorem homogeneous_profile_lower_bound {C : Type*} [Fintype C] [DecidableEq C]
    {p : MvPolynomial C ℝ} {d : ℕ} (hd : 0 < d) (hp : p.IsHomogeneous d)
    (h1 : MvPolynomial.eval (fun _ => 1) p = 1)
    (hst : ∀ z : C → ℂ, (∀ j, 0 < (z j).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (s : C) (κ : C → ℕ) (b : ℕ → ℝ) (hκ : ∀ j, j ≠ s → κ j ≤ 1)
    (hb : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s).card → 0 ≤ b k ∧ b k ≤ 1)
    (hprof : AtMostErrorProfile
      (fun j => MvPolynomial.eval (fun _ => 1) (MvPolynomial.pderiv j p) - (κ j : ℝ))
      (Finset.univ.erase s) b)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) (hs : x s = 1) :
    profileProduct b (Finset.univ.erase s).card * targetValue κ x ≤ MvPolynomial.eval x p := by
  obtain ⟨_, B, hB, hcols, hrig, hval, _⟩ :=
    homogeneous_rigid_productization hd hp h1 hst x hx
  have hpB : AtMostErrorProfile (fun j => columnSum B j - (κ j : ℝ))
      (Finset.univ.erase s) b := hprof.congr (fun j _ => by rw [columnSum, hcols j])
  exact (rigid_profile_lower_bound_nonneg hB hrig s κ b hκ hb hpB
    (fun j => (hx j).le) hs).trans hval

end TSPGap

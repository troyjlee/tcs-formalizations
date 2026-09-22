/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Stable
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

/-!
# The marker calculus I: reflection and certified differentiation

The adjacent-layer bridge of BBL §4.3.2 works on polynomials in one **marker**
variable over multivariate coefficients.  Rather than a renamed `Option`-typed
multivariate polynomial, the Lean representation is
`Polynomial (MvPolynomial ι ℝ)`: the marker is `Polynomial.X`, the layers are
the coefficients, and Mathlib's `derivative` and `reflect` are the two
operators the extraction identities need.

* `MarkerStable` — nonvanishing whenever the coordinates *and* the marker
  lie in the open upper half-plane, evaluated through `coeffHom`.
* `markerReflect d P` — the signed reflection `y^d · P(−1/y)`, as
  `reflect d (P.comp (−X))`; stability transfers because `y ↦ −1/y`
  preserves the open upper half-plane (`MarkerStable.markerReflect`).
* `markerStableOrZero_derivative` — **certified differentiation**: if `P` is
  marker-stable and its leading coefficient is `IsRealStableOrZero`, then
  `derivative P` is marker-stable or zero.

⚠️ The certificate is not decoration.  Differentiation of a stable polynomial
is the one genuinely analytic closure: for fixed interior `z` the specialized
univariate polynomial has its roots in the closed lower half-plane, and
Gauss–Lucas puts the derivative's roots in their convex hull — *provided* the
specialization does not degenerate.  An interior `z` killing every
positive-degree coefficient would kill the leading one, and a stable leading
coefficient has no interior zero; that is all the certificate is for.  In the
layered application the certificates are explicit projected layers, supplied
by the face machinery, so no generic leading-coefficient calculus is needed.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficients to `ℂ`: complexify, then evaluate the coordinates at `z`. -/
noncomputable def coeffHom (z : ι → ℂ) : MvPolynomial ι ℝ →+* ℂ :=
  (MvPolynomial.eval z).comp (MvPolynomial.map (algebraMap ℝ ℂ))

omit [Fintype ι] [DecidableEq ι] in
theorem coeffHom_apply (z : ι → ℂ) (q : MvPolynomial ι ℝ) :
    coeffHom z q = MvPolynomial.eval z (q.map (algebraMap ℝ ℂ)) := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A stable coefficient does not vanish at interior coordinates. -/
theorem coeffHom_ne_zero {q : MvPolynomial ι ℝ} (hq : IsRealStable q)
    {z : ι → ℂ} (hz : ∀ i, 0 < (z i).im) : coeffHom z q ≠ 0 := hq z hz

/-- **Marker stability**: no zero with the coordinates and the marker all in
the open upper half-plane. -/
def MarkerStable (P : Polynomial (MvPolynomial ι ℝ)) : Prop :=
  ∀ (z : ι → ℂ) (y : ℂ), (∀ i, 0 < (z i).im) → 0 < y.im →
    Polynomial.eval₂ (coeffHom z) y P ≠ 0

def MarkerStableOrZero (P : Polynomial (MvPolynomial ι ℝ)) : Prop :=
  P = 0 ∨ MarkerStable P

/-! ### The signed reflection -/

/-- `markerReflect d P` is `y^d · P(−1/y)` as a polynomial: compose with
`−X`, then reverse the coefficients up to degree `d`. -/
noncomputable def markerReflect (d : ℕ) (P : Polynomial (MvPolynomial ι ℝ)) :
    Polynomial (MvPolynomial ι ℝ) :=
  Polynomial.reflect d (P.comp (-Polynomial.X))

/-- The map `y ↦ −1/y` sends the open upper half-plane into itself. -/
theorem im_neg_inv_pos {y : ℂ} (hy : 0 < y.im) : 0 < (-y⁻¹).im := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  have hns : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy0
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- The zero-transfer of the signed reflection. -/
theorem eval₂_markerReflect_eq_zero_iff {P : Polynomial (MvPolynomial ι ℝ)}
    {d : ℕ} (hd : P.natDegree ≤ d) (z : ι → ℂ) {y : ℂ} (hy : y ≠ 0) :
    Polynomial.eval₂ (coeffHom z) y (markerReflect d P) = 0
      ↔ Polynomial.eval₂ (coeffHom z) (-y⁻¹) P = 0 := by
  have hdeg : (P.comp (-Polynomial.X)).natDegree ≤ d := by
    refine le_trans (Polynomial.natDegree_comp_le) ?_
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one]
    exact hd
  letI : Invertible (y⁻¹ : ℂ) := invertibleOfNonzero (inv_ne_zero hy)
  have hinv : (⅟(y⁻¹ : ℂ) : ℂ) = y := by
    rw [invOf_eq_inv, inv_inv]
  have h := Polynomial.eval₂_reflect_eq_zero_iff (coeffHom z) (y⁻¹) d
    (P.comp (-Polynomial.X)) hdeg
  rw [hinv] at h
  rw [markerReflect, h, Polynomial.eval₂_comp]
  have hX : Polynomial.eval₂ (coeffHom z) (y⁻¹ : ℂ) (-Polynomial.X : Polynomial (MvPolynomial ι ℝ))
      = -y⁻¹ := by
    rw [Polynomial.eval₂_neg, Polynomial.eval₂_X]
  rw [hX]

omit [Fintype ι] [DecidableEq ι] in
/-- **Reflection preserves marker stability.** -/
theorem MarkerStable.markerReflect {P : Polynomial (MvPolynomial ι ℝ)}
    (hP : MarkerStable P) {d : ℕ} (hd : P.natDegree ≤ d) :
    MarkerStable (markerReflect d P) := by
  intro z y hz hy
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  rw [Ne, eval₂_markerReflect_eq_zero_iff hd z hy0]
  exact hP z _ hz (im_neg_inv_pos hy)

omit [Fintype ι] [DecidableEq ι] in
theorem MarkerStableOrZero.markerReflect {P : Polynomial (MvPolynomial ι ℝ)}
    (hP : MarkerStableOrZero P) {d : ℕ} (hd : P.natDegree ≤ d) :
    MarkerStableOrZero (TSPGap.markerReflect d P) := by
  rcases hP with rfl | h
  · left
    rw [TSPGap.markerReflect, Polynomial.zero_comp]
    simp
  · exact Or.inr (h.markerReflect hd)

/-! ### Certified differentiation -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Certified marker differentiation.**  A marker-stable polynomial with a
stable-or-zero leading coefficient has a marker-stable-or-zero derivative.

For fixed interior `z`, the specialization has full degree — the certificate
forbids the leading coefficient from vanishing — so its roots lie in the
closed lower half-plane and Gauss–Lucas confines the derivative's roots to
their convex hull, inside the same half-plane. -/
theorem markerStableOrZero_derivative {P : Polynomial (MvPolynomial ι ℝ)}
    (hP : MarkerStable P) (hlead : IsRealStableOrZero P.leadingCoeff) :
    MarkerStableOrZero (Polynomial.derivative P) := by
  rcases eq_or_ne P 0 with rfl | hP0
  · left
    simp
  rcases Nat.eq_zero_or_pos P.natDegree with hd0 | hdpos
  · left
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hd0
    exact Polynomial.derivative_C
  right
  intro z y hz hy hzero
  have hlc : IsRealStable P.leadingCoeff := by
    rcases hlead with h0 | h
    · exact absurd (Polynomial.leadingCoeff_eq_zero.mp h0) hP0
    · exact h
  set pz : Polynomial ℂ := P.map (coeffHom z) with hpz
  have hlcz : pz.coeff P.natDegree ≠ 0 := by
    rw [hpz, Polynomial.coeff_map]
    exact coeffHom_ne_zero hlc hz
  have hpzne : pz ≠ 0 := fun h => hlcz (by rw [h, Polynomial.coeff_zero])
  have hpzdeg : 0 < pz.degree := by
    rw [Polynomial.degree_eq_natDegree hpzne]
    exact_mod_cast lt_of_lt_of_le hdpos
      (Polynomial.le_natDegree_of_ne_zero hlcz)
  -- the specialized roots avoid the open upper half-plane
  have hroots : pz.rootSet ℂ ⊆ {c : ℂ | c.im ≤ 0} := by
    intro ρ hρ
    rw [Polynomial.mem_rootSet] at hρ
    by_contra him
    refine hP z ρ hz (lt_of_not_ge him) ?_
    rw [Polynomial.eval₂_eq_eval_map, ← hpz]
    simpa using hρ.2
  -- the marker is a root of the specialized derivative
  have hyroot : (Polynomial.derivative pz).eval y = 0 := by
    rw [hpz, Polynomial.derivative_map, ← Polynomial.eval₂_eq_eval_map]
    exact hzero
  have hder0 : Polynomial.derivative pz ≠ 0 := by
    intro hc
    have hcd := Polynomial.coeff_derivative pz (P.natDegree - 1)
    rw [Nat.sub_add_cancel hdpos, hc, Polynomial.coeff_zero] at hcd
    have hne : ((P.natDegree - 1 : ℕ) : ℂ) + 1 ≠ 0 :=
      Nat.cast_add_one_ne_zero _
    exact hne (by
      rcases mul_eq_zero.mp hcd.symm with h | h
      · exact absurd h hlcz
      · exact h)
  have hmem : y ∈ (Polynomial.derivative pz).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hder0, by simpa using hyroot⟩
  have hsub := Polynomial.rootSet_derivative_subset_convexHull_rootSet hpzdeg
  have hhull : convexHull ℝ (pz.rootSet ℂ) ⊆ {c : ℂ | c.im ≤ 0} :=
    convexHull_min hroots (convex_halfSpace_im_le 0)
  exact absurd (hhull (hsub hmem)) (not_le.mpr hy)

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HalfPlanePoles
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp

/-!
# Cancellation and residues of real rational functions

Apply the local half-plane pole theorem to a quotient of real polynomials.
All multiplicities are kept: the denominator can have repeated roots, but
the numerator cancels all except at most one copy at every real root.
At a surviving pole the quotient of the remaining factors is positive.

No properness or real-rootedness is needed for these local conclusions.
Those additional hypotheses belong to the subsequent global partial-fraction
and productization argument, not to the pole-order lemma.
-/

namespace TSPGap

open Polynomial

/-- A real polynomial quotient maps the open upper half-plane into the
closed lower half-plane. This is a sign condition, not a nonvanishing claim. -/
def HasNonposImaginaryQuotient (p q : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im → (aeval z p / aeval z q).im ≤ 0

/-- Cancel known powers at a real point. A genuine remaining pole has order
one and a positive residue, including when both original polynomials vanish. -/
theorem simple_pole_of_real_factorizations {p q r s : Polynomial ℝ}
    {a : ℝ} {j k : ℕ}
    (hp : p = (X - C a) ^ j * r) (hq : q = (X - C a) ^ k * s)
    (hr : r.eval a ≠ 0) (hs : s.eval a ≠ 0) (hjk : j < k)
    (him : HasNonposImaginaryQuotient p q) :
    k = j + 1 ∧ 0 < r.eval a / s.eval a := by
  have heval (f : Polynomial ℝ) : aeval (a : ℂ) f = (↑(f.eval a) : ℂ) :=
    aeval_algebraMap_apply_eq_algebraMap_eval a f
  let g : ℂ → ℂ := fun z => aeval (z + (a : ℂ)) r / aeval (z + (a : ℂ)) s
  have hg : ContinuousAt g 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa only [zero_add, heval, ne_eq, Complex.ofReal_eq_zero] using hs
  have hg0 : g 0 = ((r.eval a / s.eval a : ℝ) : ℂ) := by
    dsimp [g]
    rw [zero_add, heval, heval, Complex.ofReal_div]
  have hsign : ∀ z : ℂ, 0 < z.im → (g z / z ^ (k - j)).im ≤ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    have h := him (z + (a : ℂ)) (by simpa using hz)
    have heq : aeval (z + (a : ℂ)) p / aeval (z + (a : ℂ)) q =
        g z / z ^ (k - j) := by
      rw [hp, hq]
      simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C,
        show (algebraMap ℝ ℂ) a = (a : ℂ) from rfl, add_sub_cancel_right]
      have hk : k = j + (k - j) := by omega
      rw [show z ^ k = z ^ j * z ^ (k - j) by rw [← pow_add, ← hk]]
      dsimp [g]
      rw [mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ hz0), div_mul_eq_div_div]
      ring
    rwa [heq] at h
  obtain ⟨horder, hres⟩ := pole_order_eq_one_and_residue_pos hg hg0
    (div_ne_zero hr hs) (Nat.sub_pos_of_lt hjk) hsign
  exact ⟨by omega, hres⟩

/-- A denominator's real-root multiplicity exceeds the numerator's by at
most one. The numerator is explicitly nonzero; the zero rational function
has no genuine pole, regardless of its chosen denominator. -/
theorem rootMultiplicity_le_succ_of_nonposImaginaryQuotient
    {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (him : HasNonposImaginaryQuotient p q) (a : ℝ) :
    q.rootMultiplicity a ≤ p.rootMultiplicity a + 1 := by
  by_cases hle : q.rootMultiplicity a ≤ p.rootMultiplicity a
  · omega
  have hlt : p.rootMultiplicity a < q.rootMultiplicity a := by omega
  obtain ⟨r, hpr, hr⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  obtain ⟨s, hqs, hs⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq a
  have hr0 : r.eval a ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot] using hr
  have hs0 : s.eval a ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot] using hs
  have h := simple_pole_of_real_factorizations hpr hqs hr0 hs0 hlt him
  omega

/-- The canonical residue, using the quotients by the full vanishing
powers. This formulation needs no chosen factorization. -/
theorem residue_pos_of_nonposImaginaryQuotient
    {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (him : HasNonposImaginaryQuotient p q) {a : ℝ}
    (hord : p.rootMultiplicity a < q.rootMultiplicity a) :
    0 < (p /ₘ (X - C a) ^ p.rootMultiplicity a).eval a /
      (q /ₘ (X - C a) ^ q.rootMultiplicity a).eval a := by
  exact (simple_pole_of_real_factorizations
    (p.pow_mul_divByMonic_rootMultiplicity_eq a).symm
    (q.pow_mul_divByMonic_rootMultiplicity_eq a).symm
    (eval_divByMonic_pow_rootMultiplicity_ne_zero a hp)
    (eval_divByMonic_pow_rootMultiplicity_ne_zero a hq) hord him).2

end TSPGap

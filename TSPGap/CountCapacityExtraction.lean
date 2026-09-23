/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountProjectionStable
import TSPGap.UnivariateCapacity

/-!
# Capacity extraction on an actual block of coordinates

Tilt the coordinates outside F, then take the rank polynomial on F. Its
linear coefficient is exactly the generating polynomial of `projectCount`
at the frozen values. Real-rootedness comes from the existing rank law's
homogeneous tilt, and the extracted weight remains stable-or-zero by the
projected-layer closure. This supplies a repeatable extraction step without
general derivative or real-boundary stability assumptions.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Give all coordinates in F the same value, retaining x elsewhere. -/
def blockScale (F : Finset ι) (x : ι → ℝ) (t : ℝ) : ι → ℝ :=
  F.piecewise (fun _ => t) x

omit [Fintype ι] in
theorem prod_blockScale (S F : Finset ι) (x : ι → ℝ) (t : ℝ) :
    (∏ i ∈ S, blockScale F x t i) = t ^ (S ∩ F).card * ∏ i ∈ S \ F, x i := by
  rw [blockScale, Finset.prod_piecewise, Finset.prod_const]

/-- Apply the external field only outside the block being extracted. -/
noncomputable def outsideTilt (w : Finset ι → ℝ) (F : Finset ι) (x : ι → ℝ) :
    Finset ι → ℝ := fun S => w S * ∏ i ∈ S \ F, x i

omit [Fintype ι] in
theorem weightNonneg_outsideTilt {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) (x : ι → ℝ) (hx : ∀ i, i ∉ F → 0 ≤ x i) :
    WeightNonneg (outsideTilt w F x) := by
  intro S
  exact mul_nonneg (hnn S) (Finset.prod_nonneg fun i hi => hx i (Finset.mem_sdiff.mp hi).2)

omit [Fintype ι] in
theorem fixedRankWeight_outsideTilt {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (F : Finset ι) (x : ι → ℝ) :
    FixedRankWeight r (outsideTilt w F x) := by
  intro S hS
  exact hr S (fun h => hS (by simp [outsideTilt, h]))

/-- Positive external fields preserve stability without normalizing. -/
theorem isRealStable_outsideTilt {w : Finset ι → ℝ}
    (hst : IsRealStable (genPoly w)) (F : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, i ∉ F → 0 < x i) : IsRealStable (genPoly (outsideTilt w F x)) := by
  have hs := hst.scale (c := blockScale F x 1) (by
    intro i
    by_cases hi : i ∈ F <;> simp [blockScale, Finset.piecewise, hi, hx])
  rw [bind₁_scale_genPoly] at hs
  have hw : (fun S => w S * ∏ i ∈ S, blockScale F x 1 i) = outsideTilt w F x := by
    funext S
    simp [prod_blockScale, outsideTilt]
  rwa [hw] at hs

/-- The polynomial in a single block value, with all other values frozen. -/
noncomputable def countSlice (w : Finset ι → ℝ) (F : Finset ι) (x : ι → ℝ) : Polynomial ℝ :=
  rankPoly (outsideTilt w F x) F

theorem eval_countSlice (w : Finset ι → ℝ) (F : Finset ι) (x : ι → ℝ) (t : ℝ) :
    (countSlice w F x).eval t = MvPolynomial.eval (blockScale F x t) (genPoly w) := by
  change (rankPoly (outsideTilt w F x) F).eval₂ (RingHom.id ℝ) t = _
  rw [eval₂_rankPoly, eval_genPoly]
  apply Finset.sum_congr rfl
  intro S _
  simp only [RingHom.id_apply, outsideTilt, prod_blockScale]
  ring

/-- All coefficients, not just the linear one, are projected count masses
weighted by the remaining evaluation coordinates. -/
theorem coeff_countSlice (w : Finset ι → ℝ) (F : Finset ι) (x : ι → ℝ) (k : ℕ) :
    (countSlice w F x).coeff k = MvPolynomial.eval x (genPoly (projectCount w F k)) := by
  classical
  rw [countSlice, coeff_rankPoly, weightMass, eval_genPoly_projectCount]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hk : (S ∩ F).card = k <;> simp [hk, outsideTilt]

theorem coeff_nonneg_countSlice {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) (x : ι → ℝ) (hx : ∀ i, i ∉ F → 0 ≤ x i) (k : ℕ) :
    0 ≤ (countSlice w F x).coeff k :=
  coeff_rankPoly_nonneg (weightNonneg_outsideTilt hnn F x hx) F k

/-- Real-rootedness includes a zero input law and needs positive frozen
values only outside F. -/
theorem splits_countSlice {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (F : Finset ι) (x : ι → ℝ) (hx : ∀ i, i ∉ F → 0 < x i) :
    (countSlice w F x).Splits := by
  classical
  rcases hst with hzero | hst
  · have hw : w = fun _ => 0 := genPoly_injective (by rw [hzero, genPoly_zero])
    have hp : countSlice w F x = 0 := by simp [countSlice, rankPoly, outsideTilt, hw]
    rw [hp]
    exact Splits.zero
  have hs := isRealStable_outsideTilt hst F x hx
  have hrank := fixedRankWeight_outsideTilt hr F x
  apply Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
    Complex.ofReal_injective (IsAlgClosed.splits _)
  intro a ha
  have hz : aeval a (rankPoly (outsideTilt w F x) F) = 0 := by
    simpa only [IsRoot, eval_map, aeval_def, countSlice] using (mem_roots'.mp ha).2
  have hi := im_eq_zero_of_aeval_rankPoly hs hrank F hz
  refine ⟨a.re, ?_⟩
  apply Complex.ext <;> simp [hi]

/-- **The repeatable block step.** A uniform linear capacity bound survives
extracting count one and forgetting the block, with loss at most `exp(-1)`.
Stability of the output is separately certified by `isRealStableOrZero_projectCount`.
No positive mass or positive rank is assumed. -/
theorem projectCount_eval_lower_bound {w : Finset ι → ℝ} {r : ℕ} {c : ℝ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (F : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, i ∉ F → 0 < x i)
    (hcap : ∀ t : ℝ, 0 < t → c * t ≤ MvPolynomial.eval (blockScale F x t) (genPoly w)) :
    Real.exp (-1) * c ≤ MvPolynomial.eval x (genPoly (projectCount w F 1)) := by
  rw [← coeff_countSlice]
  exact coeff_one_ge_exp_neg_one_mul_capacity (splits_countSlice hst hr F x hx)
    (coeff_nonneg_countSlice hnn F x (fun i hi => (hx i hi).le))
    (fun t ht => by rw [eval_countSlice]; exact hcap t ht)

omit [Fintype ι] [DecidableEq ι] in
/-- A sure baseline of one costs no extraction factor: cancel X before
extracting the residual linear coefficient. -/
theorem coeff_two_ge_exp_neg_one_mul_capacity {p : Polynomial ℝ} {c : ℝ}
    (hsplit : p.Splits) (hnn : ∀ k, 0 ≤ p.coeff k) (h0 : p.coeff 0 = 0)
    (hcap : ∀ t : ℝ, 0 < t → c * t ^ 2 ≤ p.eval t) :
    Real.exp (-1) * c ≤ p.coeff 2 := by
  have heq : p.divX * X = p := by simpa [h0] using p.divX_mul_X_add
  have hs : p.divX.Splits := Splits.of_mul_X (heq.symm ▸ hsplit)
  have h := coeff_one_ge_exp_neg_one_mul_capacity hs
    (fun k => by rw [coeff_divX]; exact hnn _) (c := c) (by
      intro t ht
      have hb := hcap t ht
      rw [← heq, eval_mul, eval_X, pow_two, ← mul_assoc] at hb
      exact (mul_le_mul_iff_left₀ ht).mp hb)
  simpa only [coeff_divX, Nat.reduceAdd] using h

/-- A support baseline gives a zero constant coefficient before or after
any positive external field. -/
theorem countSlice_coeff_zero_of_lower_count {w : Finset ι → ℝ} {F : Finset ι}
    (hb : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ F).card) (x : ι → ℝ) :
    (countSlice w F x).coeff 0 = 0 := by
  classical
  rw [countSlice, coeff_rankPoly, weightMass]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : w S = 0
  · simp [outsideTilt, hS]
  · rw [if_neg (by have := hb S hS; omega)]

/-- Extracting count two with a sure baseline one still costs only
`exp(-1)`. The baseline is a property of the support, not a chosen edge. -/
theorem projectCount_eval_lower_bound_two {w : Finset ι → ℝ} {r : ℕ} {c : ℝ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (F : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, i ∉ F → 0 < x i)
    (hb : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ F).card)
    (hcap : ∀ t : ℝ, 0 < t → c * t ^ 2 ≤ MvPolynomial.eval (blockScale F x t) (genPoly w)) :
    Real.exp (-1) * c ≤ MvPolynomial.eval x (genPoly (projectCount w F 2)) := by
  rw [← coeff_countSlice]
  exact coeff_two_ge_exp_neg_one_mul_capacity (splits_countSlice hst hr F x hx)
    (coeff_nonneg_countSlice hnn F x (fun i hi => (hx i hi).le))
    (countSlice_coeff_zero_of_lower_count hb x)
    (fun t ht => by rw [eval_countSlice]; exact hcap t ht)

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeStability

/-!
# Stability implies the Rayleigh condition

The **forward** half of Borcea–Brändén–Liggett, which is the half the payment
argument needs.  The reverse implication is deferred: it was mainly a candidate
limit adapter, and `StableLimit.lean` made it unnecessary.

## The argument avoids Hurwitz

Fix `i ≠ j` and a real point `x`.  Multi-affinity writes the polynomial as
`a·XᵢXⱼ + b·Xᵢ + c·Xⱼ + d` with `a, b, c, d` free of `Xᵢ, Xⱼ`, and then the
Rayleigh difference collapses to `bc − ad`, *with the two variables gone*.

Suppose `BC − AD < 0` at the real point.  Put `s = i`; solving `Ast+Bs+Ct+D = 0`
for `t` gives `t = −(Bs+D)/(As+C)`, and a direct computation of the imaginary
part yields

`Im t = −(Im s)·(BC − AD) / |As+C|² > 0`.

That is a zero of the *bivariate* restriction with both variables strictly
inside — but the other coordinates are still real, so it is not yet a
contradiction.  Rather than appeal to Hurwitz to descend to the boundary, the
zero is rebuilt at a perturbed point: shift every other coordinate up by `iε` and
solve for `t` again.  The solution depends continuously on `ε` and tends to the
one above, so for small `ε` it still lies in the open upper half-plane — and now
*every* coordinate does.  That contradicts stability outright.

The `i = j` case is separate and easier: multi-affinity makes `∂ᵢ∂ᵢp = 0`, so the
Rayleigh difference is `(∂ᵢp)²`.

## Route through `genPoly`

Everything is done for generating polynomials, and `genPoly_coeff_self` — the
converse of `isMultiAffine_genPoly` — transports it to an arbitrary multi-affine
polynomial.  That keeps all the bookkeeping inside `Finset` combinatorics, where
`sqExp` and `coeff_genPoly` already do the work.
-/

namespace TSPGap

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Multi-affine polynomials are generating polynomials -/

omit [Fintype ι] in
theorem sqExp_support_eq (S : Finset ι) : (sqExp S).support = S := by
  ext i
  rw [Finsupp.mem_support_iff, sqExp_apply]
  by_cases h : i ∈ S <;> simp [h]

omit [Fintype ι] in
/-- Every monomial of a multi-affine polynomial is `sqExp` of its support. -/
theorem sqExp_support_of_mem {p : MvPolynomial ι ℝ} (hp : IsMultiAffine p)
    {m : ι →₀ ℕ} (hm : m ∈ p.support) : sqExp m.support = m := by
  ext i
  rw [sqExp_apply]
  have h1 : m i ≤ 1 := hp.le_one hm i
  by_cases h : m i = 0
  · rw [if_neg (by simp [Finsupp.mem_support_iff, h]), h]
  · rw [if_pos (Finsupp.mem_support_iff.mpr h)]
    omega

/-- **The converse of `isMultiAffine_genPoly`**: a multi-affine polynomial is the
generating polynomial of its squarefree coefficients. -/
theorem genPoly_coeff_self {p : MvPolynomial ι ℝ} (hp : IsMultiAffine p) :
    genPoly (fun S => p.coeff (sqExp S)) = p := by
  classical
  rw [genPoly_eq_sum_monomial]
  have hrestrict : ∑ S : Finset ι, (monomial (sqExp S) (p.coeff (sqExp S)) : MvPolynomial ι ℝ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => p.coeff (sqExp S) ≠ 0),
          monomial (sqExp S) (p.coeff (sqExp S)) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro S _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hS
    rw [hS, monomial_zero]
  rw [hrestrict]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  refine Finset.sum_nbij' (fun S => sqExp S) (fun m => m.support) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact MvPolynomial.mem_support_iff.mpr hS
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [sqExp_support_of_mem hp hm]
    exact MvPolynomial.mem_support_iff.mp hm
  · intro S _
    exact sqExp_support_eq S
  · intro m hm
    exact sqExp_support_of_mem hp hm
  · intro S _
    rfl

/-! ### Differentiating a generating polynomial -/

omit [Fintype ι] in
theorem sqExp_sub_single {S : Finset ι} {i : ι} (hi : i ∈ S) :
    sqExp S - Finsupp.single i 1 = sqExp (S.erase i) := by
  ext k
  simp only [Finsupp.tsub_apply, sqExp_apply, Finsupp.single_apply]
  by_cases hk : k = i
  · subst hk
    simp [hi]
  · simp [Finset.mem_erase, hk, Ne.symm hk]

/-- **The partial derivative of a generating polynomial.**  Differentiating in
`Xᵢ` keeps the subsets containing `i` and deletes `i` from them. -/
theorem pderiv_genPoly (w : Finset ι → ℝ) (i : ι) :
    pderiv i (genPoly w) = genPoly (fun U => if i ∈ U then 0 else w (insert i U)) := by
  classical
  rw [genPoly_eq_sum_monomial, map_sum, genPoly_eq_sum_monomial]
  have hL : ∀ S : Finset ι,
      (pderiv i) (monomial (sqExp S) (w S) : MvPolynomial ι ℝ)
        = if i ∈ S then monomial (sqExp (S.erase i)) (w S) else 0 := by
    intro S
    rw [MvPolynomial.pderiv_monomial, sqExp_apply]
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos hi, sqExp_sub_single hi]
      norm_num
    · rw [if_neg hi, if_neg hi]
      norm_num
  have hR : ∀ U : Finset ι,
      (monomial (sqExp U) (if i ∈ U then (0 : ℝ) else w (insert i U)) : MvPolynomial ι ℝ)
        = if i ∉ U then monomial (sqExp U) (w (insert i U)) else 0 := by
    intro U
    by_cases hi : i ∈ U
    · rw [if_pos hi, if_neg (by simpa using hi), monomial_zero]
    · rw [if_neg hi, if_pos hi]
  rw [Finset.sum_congr rfl fun S _ => hL S, Finset.sum_congr rfl fun U _ => hR U,
    ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun S => S.erase i) (fun U => insert i U) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact Finset.notMem_erase i S
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    exact Finset.mem_insert_self i U
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.insert_erase hS
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact Finset.erase_insert hU
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [Finset.insert_erase hS]

/-! ### The affine split -/

/-- **A generating polynomial is affine in each variable**:
`p = Xᵢ · ∂ᵢp + p|_{Xᵢ = 0}`. -/
theorem genPoly_split (w : Finset ι → ℝ) (i : ι) :
    genPoly w = X i * genPoly (fun U => if i ∈ U then 0 else w (insert i U))
      + genPoly (fun U => if i ∈ U then 0 else w U) := by
  classical
  have hin : (X i * genPoly (fun U => if i ∈ U then 0 else w (insert i U))
      : MvPolynomial ι ℝ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S), C (w S) * ∏ k ∈ S, X k := by
    rw [genPoly, Finset.mul_sum]
    have hterm : ∀ U : Finset ι,
        (X i * (C (if i ∈ U then (0 : ℝ) else w (insert i U)) * ∏ k ∈ U, X k)
          : MvPolynomial ι ℝ)
          = if i ∉ U then C (w (insert i U)) * ∏ k ∈ insert i U, X k else 0 := by
      intro U
      by_cases hU : i ∈ U
      · rw [if_pos hU, if_neg (by simpa using hU)]
        simp
      · rw [if_neg hU, if_pos hU, Finset.prod_insert hU]
        ring
    rw [Finset.sum_congr rfl fun U _ => hterm U, ← Finset.sum_filter]
    refine (Finset.sum_nbij' (fun S => S.erase i) (fun U => insert i U) ?_ ?_ ?_ ?_ ?_).symm
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact Finset.notMem_erase i S
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
      exact Finset.mem_insert_self i U
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.insert_erase hS
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      exact Finset.erase_insert hU
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.insert_erase hS]
  have hout : (genPoly (fun U => if i ∈ U then 0 else w U) : MvPolynomial ι ℝ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∉ S), C (w S) * ∏ k ∈ S, X k := by
    rw [genPoly]
    have hterm : ∀ U : Finset ι,
        (C (if i ∈ U then (0 : ℝ) else w U) * ∏ k ∈ U, X k : MvPolynomial ι ℝ)
          = if i ∉ U then C (w U) * ∏ k ∈ U, X k else 0 := by
      intro U
      by_cases hU : i ∈ U
      · rw [if_pos hU, if_neg (by simpa using hU)]
        simp
      · rw [if_neg hU, if_pos hU]
    rw [Finset.sum_congr rfl fun U _ => hterm U, ← Finset.sum_filter]
  rw [hin, hout, genPoly, Finset.sum_filter_add_sum_filter_not]

/-! ### The four sectors -/

/-- Weight of the `Xᵢ Xⱼ` sector. -/
noncomputable def sectorA (w : Finset ι → ℝ) (i j : ι) : Finset ι → ℝ :=
  fun V => if i ∈ V ∨ j ∈ V then 0 else w (insert i (insert j V))

/-- Weight of the `Xᵢ` sector. -/
noncomputable def sectorB (w : Finset ι → ℝ) (i j : ι) : Finset ι → ℝ :=
  fun V => if i ∈ V ∨ j ∈ V then 0 else w (insert i V)

/-- Weight of the `Xⱼ` sector. -/
noncomputable def sectorC (w : Finset ι → ℝ) (i j : ι) : Finset ι → ℝ :=
  fun V => if i ∈ V ∨ j ∈ V then 0 else w (insert j V)

/-- Weight of the constant sector. -/
noncomputable def sectorD (w : Finset ι → ℝ) (i j : ι) : Finset ι → ℝ :=
  fun V => if i ∈ V ∨ j ∈ V then 0 else w V

omit [Fintype ι] in
/-- Every sector weight vanishes on sets meeting `{i, j}` — which is what makes
the sectors independent of `Xᵢ` and `Xⱼ`. -/
theorem sector_vanishes (w : Finset ι → ℝ) (i j : ι) (V : Finset ι) (h : i ∈ V ∨ j ∈ V) :
    sectorA w i j V = 0 ∧ sectorB w i j V = 0 ∧ sectorC w i j V = 0 ∧ sectorD w i j V = 0 := by
  simp [sectorA, sectorB, sectorC, sectorD, if_pos h]

theorem pderiv_pderiv_genPoly (w : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) :
    pderiv j (pderiv i (genPoly w)) = genPoly (sectorA w i j) := by
  classical
  rw [pderiv_genPoly, pderiv_genPoly]
  refine congrArg genPoly (funext fun V => ?_)
  by_cases hj : j ∈ V
  · simp [sectorA, hj]
  · by_cases hi : i ∈ V
    · simp [sectorA, hi, hj, Finset.mem_insert, hij]
    · simp [sectorA, hi, hj, Finset.mem_insert, hij]

theorem pderiv_genPoly_eq (w : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) :
    pderiv i (genPoly w) = X j * genPoly (sectorA w i j) + genPoly (sectorB w i j) := by
  classical
  rw [pderiv_genPoly, genPoly_split _ j]
  congr 1
  · refine congrArg (fun q => X j * q) (congrArg genPoly (funext fun V => ?_))
    by_cases hj : j ∈ V
    · simp [sectorA, hj]
    · by_cases hi : i ∈ V
      · simp [sectorA, hi, hj, Finset.mem_insert, hij]
      · simp [sectorA, hi, hj, Finset.mem_insert, hij]
  · refine congrArg genPoly (funext fun V => ?_)
    by_cases hj : j ∈ V
    · simp [sectorB, hj]
    · by_cases hi : i ∈ V
      · simp [sectorB, hi, hj]
      · simp [sectorB, hi, hj]

theorem pderiv_genPoly_eq' (w : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) :
    pderiv j (genPoly w) = X i * genPoly (sectorA w i j) + genPoly (sectorC w i j) := by
  classical
  rw [pderiv_genPoly, genPoly_split _ i]
  congr 1
  · refine congrArg (fun q => X i * q) (congrArg genPoly (funext fun V => ?_))
    by_cases hi : i ∈ V
    · simp [sectorA, hi]
    · by_cases hj : j ∈ V
      · simp [sectorA, hi, hj, Finset.mem_insert, Ne.symm hij]
      · simp only [sectorA, hi, hj, Finset.mem_insert, Ne.symm hij, or_self,
          if_false]
        rw [Finset.insert_comm]
  · refine congrArg genPoly (funext fun V => ?_)
    by_cases hi : i ∈ V
    · simp [sectorC, hi]
    · by_cases hj : j ∈ V
      · simp [sectorC, hi, hj]
      · simp [sectorC, hi, hj]

theorem genPoly_split_two (w : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) :
    genPoly w = X i * X j * genPoly (sectorA w i j) + X i * genPoly (sectorB w i j)
      + (X j * genPoly (sectorC w i j) + genPoly (sectorD w i j)) := by
  classical
  rw [genPoly_split w i]
  congr 1
  · rw [show genPoly (fun U => if i ∈ U then (0:ℝ) else w (insert i U))
        = X j * genPoly (sectorA w i j) + genPoly (sectorB w i j) from ?_]
    · ring
    · rw [← pderiv_genPoly, pderiv_genPoly_eq w hij]
  · rw [genPoly_split _ j]
    congr 1
    · refine congrArg (fun q => X j * q) (congrArg genPoly (funext fun V => ?_))
      by_cases hj : j ∈ V
      · simp [sectorC, hj]
      · by_cases hi : i ∈ V
        · simp [sectorC, hi, hj, Finset.mem_insert, hij]
        · simp [sectorC, hi, hj, Finset.mem_insert, hij]
    · refine congrArg genPoly (funext fun V => ?_)
      by_cases hj : j ∈ V
      · simp [sectorD, hj]
      · by_cases hi : i ∈ V
        · simp [sectorD, hi, hj]
        · simp [sectorD, hi, hj]

/-- **The Rayleigh difference of a generating polynomial is `bc − ad`** — and
the two differentiated variables have disappeared entirely. -/
theorem rayleighDiff_genPoly (w : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) :
    rayleighDiff (genPoly w) i j
      = genPoly (sectorB w i j) * genPoly (sectorC w i j)
        - genPoly (sectorA w i j) * genPoly (sectorD w i j) := by
  rw [rayleighDiff, pderiv_pderiv_genPoly w hij, pderiv_genPoly_eq w hij,
    pderiv_genPoly_eq' w hij, genPoly_split_two w hij]
  ring

/-! ### The analytic step

The sector sums with every coordinate lifted by `iε`.  Keeping this as a
function of `ε` is what lets the forbidden zero be rebuilt at a perturbed point
instead of descending to the boundary by Hurwitz. -/

noncomputable def sectorEval (v : Finset ι → ℝ) (x : ι → ℝ) (ε : ℝ) : ℂ :=
  ∑ S : Finset ι, ((v S : ℝ) : ℂ) * ∏ k ∈ S, ((x k : ℂ) + Complex.I * ε)

omit [DecidableEq ι] in
theorem continuous_sectorEval (v : Finset ι → ℝ) (x : ι → ℝ) :
    Continuous (sectorEval v x) := by
  refine continuous_finsetSum _ fun S _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun k _ =>
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)

theorem sectorEval_zero (v : Finset ι → ℝ) (x : ι → ℝ) :
    sectorEval v x 0 = ((eval x (genPoly v) : ℝ) : ℂ) := by
  rw [sectorEval, eval_genPoly]
  push_cast
  simp

theorem sectorEval_eq_eval (v : Finset ι → ℝ) (x : ι → ℝ) (ε : ℝ) :
    sectorEval v x ε
      = eval (fun k => (x k : ℂ) + Complex.I * ε)
          ((genPoly v).map (algebraMap ℝ ℂ)) := by
  rw [eval_map_genPoly]
  rfl

/-- A sector sum ignores the two distinguished coordinates: its weight vanishes
on every set meeting `{i, j}`. -/
theorem eval_update_of_vanishes {v : Finset ι → ℝ} {i j : ι}
    (hv : ∀ V, i ∈ V ∨ j ∈ V → v V = 0) (z : ι → ℂ) (s t : ℂ) :
    eval (Function.update (Function.update z i s) j t)
        ((genPoly v).map (algebraMap ℝ ℂ))
      = eval z ((genPoly v).map (algebraMap ℝ ℂ)) := by
  classical
  rw [eval_map_genPoly, eval_map_genPoly]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : i ∈ S ∨ j ∈ S
  · rw [hv S hS]
    simp
  · push Not at hS
    refine congrArg _ (Finset.prod_congr rfl fun k hk => ?_)
    have hki : k ≠ i := fun h => hS.1 (h ▸ hk)
    have hkj : k ≠ j := fun h => hS.2 (h ▸ hk)
    rw [Function.update_of_ne hkj, Function.update_of_ne hki]

open Classical in
/-- **The forward implication, off the diagonal.**

If the Rayleigh difference were negative at a real point, solving the bivariate
restriction for `t` would produce a zero with both distinguished coordinates in
the open upper half-plane.  The other coordinates are still real there, so the
same solve is repeated at the point shifted up by `iε`; the solution moves
continuously, so for small `ε` it is still interior — and now every coordinate
is.  That contradicts stability directly, with no Hurwitz argument. -/
theorem rayleighNonneg_genPoly_ne {w : Finset ι → ℝ} (hstab : IsRealStable (genPoly w))
    {i j : ι} (hij : i ≠ j) (x : ι → ℝ) :
    0 ≤ eval x (genPoly (sectorB w i j)) * eval x (genPoly (sectorC w i j))
        - eval x (genPoly (sectorA w i j)) * eval x (genPoly (sectorD w i j)) := by
  by_contra hcon
  push Not at hcon
  -- the four sector values at the real point
  have hA0 := sectorEval_zero (sectorA w i j) x
  have hB0 := sectorEval_zero (sectorB w i j) x
  have hC0 := sectorEval_zero (sectorC w i j) x
  have hD0 := sectorEval_zero (sectorD w i j) x
  -- the denominator does not vanish at the real point
  have hden0 : sectorEval (sectorA w i j) x 0 * Complex.I
      + sectorEval (sectorC w i j) x 0 ≠ 0 := by
    rw [hA0, hC0]
    intro hzero
    rw [Complex.ext_iff] at hzero
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] at hzero
    obtain ⟨hC, hA⟩ := hzero
    rw [hC, hA] at hcon
    simp at hcon
  -- the solution of the linear equation, as a function of the shift
  set T : ℝ → ℂ := fun ε =>
    -(sectorEval (sectorB w i j) x ε * Complex.I + sectorEval (sectorD w i j) x ε)
      / (sectorEval (sectorA w i j) x ε * Complex.I + sectorEval (sectorC w i j) x ε) with hTdef
  have hcontden : ContinuousAt (fun ε => sectorEval (sectorA w i j) x ε * Complex.I
      + sectorEval (sectorC w i j) x ε) 0 :=
    (((continuous_sectorEval _ _).continuousAt).mul continuousAt_const).add
      ((continuous_sectorEval _ _).continuousAt)
  have hcontT : ContinuousAt T 0 := by
    rw [hTdef]
    exact ContinuousAt.div
      ((((continuous_sectorEval _ _).continuousAt).mul continuousAt_const).add
        ((continuous_sectorEval _ _).continuousAt)).neg hcontden hden0
  -- at the real point the solution is strictly inside
  have hT0 : 0 < (T 0).im := by
    rw [hTdef]
    simp only
    rw [hA0, hB0, hC0, hD0, Complex.div_im]
    have hnorm : 0 < Complex.normSq (((eval x (genPoly (sectorA w i j)) : ℝ) : ℂ) * Complex.I
        + ((eval x (genPoly (sectorC w i j)) : ℝ) : ℂ)) := by
      rw [Complex.normSq_pos]
      rw [hA0, hC0] at hden0
      exact hden0
    simp only [Complex.neg_im, Complex.neg_re, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, mul_one, sub_zero, zero_add, add_zero]
    rw [div_sub_div_same]
    apply div_pos _ hnorm
    nlinarith [hcon]
  -- so it is still strictly inside after a small shift
  obtain ⟨ε, hε0, hεim⟩ : ∃ ε : ℝ, 0 < ε ∧ 0 < (T ε).im := by
    have hmem : (fun ε => (T ε).im) ⁻¹' (Set.Ioi 0) ∈ nhds (0 : ℝ) :=
      (Complex.continuous_im.continuousAt.comp hcontT).preimage_mem_nhds (Ioi_mem_nhds hT0)
    rw [Metric.mem_nhds_iff] at hmem
    obtain ⟨δ, hδ, hball⟩ := hmem
    refine ⟨δ / 2, by linarith, hball ?_⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < δ/2)]
    linarith
  have hdenε : sectorEval (sectorA w i j) x ε * Complex.I
      + sectorEval (sectorC w i j) x ε ≠ 0 := by
    intro hz0
    rw [hTdef] at hεim
    simp only [hz0, div_zero, Complex.zero_im] at hεim
    exact lt_irrefl 0 hεim
  have hTmul : T ε * (sectorEval (sectorA w i j) x ε * Complex.I
      + sectorEval (sectorC w i j) x ε)
      = -(sectorEval (sectorB w i j) x ε * Complex.I
          + sectorEval (sectorD w i j) x ε) := by
    rw [hTdef]
    exact div_mul_cancel₀ _ hdenε
  -- the forbidden zero
  set z : ι → ℂ := Function.update
    (Function.update (fun k => (x k : ℂ) + Complex.I * ε) i Complex.I) j (T ε) with hzdef
  have hzi : z i = Complex.I := by
    rw [hzdef, Function.update_of_ne hij, Function.update_self]
  have hzj : z j = T ε := by rw [hzdef, Function.update_self]
  have hzk : ∀ k, k ≠ i → k ≠ j → z k = (x k : ℂ) + Complex.I * ε := by
    intro k hki hkj
    rw [hzdef, Function.update_of_ne hkj, Function.update_of_ne hki]
  have hzim : ∀ k, 0 < (z k).im := by
    intro k
    by_cases hkj : k = j
    · subst hkj; rw [hzj]; exact hεim
    · by_cases hki : k = i
      · subst hki; rw [hzi]; simp
      · rw [hzk k hki hkj]
        simp [hε0]
  -- the sector sums do not see the two distinguished coordinates
  have hsec : ∀ v : Finset ι → ℝ, (∀ V, i ∈ V ∨ j ∈ V → v V = 0) →
      eval z ((genPoly v).map (algebraMap ℝ ℂ)) = sectorEval v x ε := by
    intro v hv
    rw [hzdef, eval_update_of_vanishes hv, sectorEval_eq_eval]
  have hvA : ∀ V, i ∈ V ∨ j ∈ V → sectorA w i j V = 0 := fun V h => (sector_vanishes w i j V h).1
  have hvB : ∀ V, i ∈ V ∨ j ∈ V → sectorB w i j V = 0 :=
    fun V h => (sector_vanishes w i j V h).2.1
  have hvC : ∀ V, i ∈ V ∨ j ∈ V → sectorC w i j V = 0 :=
    fun V h => (sector_vanishes w i j V h).2.2.1
  have hvD : ∀ V, i ∈ V ∨ j ∈ V → sectorD w i j V = 0 :=
    fun V h => (sector_vanishes w i j V h).2.2.2
  have hzero : eval z ((genPoly w).map (algebraMap ℝ ℂ)) = 0 := by
    rw [genPoly_split_two w hij]
    simp only [map_add, map_mul, MvPolynomial.map_X, eval_X]
    rw [hsec _ hvA, hsec _ hvB, hsec _ hvC, hsec _ hvD, hzi, hzj]
    linear_combination hTmul
  exact hstab z hzim hzero

/-! ### The diagonal case -/

theorem pderiv_pderiv_self_genPoly (w : Finset ι → ℝ) (i : ι) :
    pderiv i (pderiv i (genPoly w)) = 0 := by
  classical
  rw [pderiv_genPoly, pderiv_genPoly]
  have : (fun U : Finset ι => if i ∈ U then (0:ℝ)
      else (if i ∈ insert i U then (0:ℝ) else w (insert i (insert i U)))) = fun _ => 0 := by
    funext U
    by_cases hU : i ∈ U <;> simp [hU]
  rw [this, genPoly]
  simp

/-! ### The forward implication -/

theorem rayleighNonneg_genPoly {w : Finset ι → ℝ} (hstab : IsRealStable (genPoly w)) :
    RayleighNonneg (genPoly w) := by
  intro i j x
  by_cases hij : i = j
  · subst hij
    rw [rayleighDiff, pderiv_pderiv_self_genPoly, mul_zero, sub_zero, map_mul]
    exact mul_self_nonneg _
  · rw [rayleighDiff_genPoly w hij, map_sub, map_mul, map_mul]
    exact rayleighNonneg_genPoly_ne hstab hij x

/-- **Stability implies the Rayleigh condition** for multi-affine polynomials.
The forward half of Borcea–Brändén–Liggett. -/
theorem IsRealStable.rayleighNonneg {p : MvPolynomial ι ℝ} (hp : IsRealStable p)
    (hma : IsMultiAffine p) : RayleighNonneg p := by
  rw [← genPoly_coeff_self hma] at hp ⊢
  exact rayleighNonneg_genPoly hp

/-! ### Pairwise negative correlation -/

theorem eval_one_genPoly (w : Finset ι → ℝ) :
    eval (fun _ => (1 : ℝ)) (genPoly w) = ∑ S : Finset ι, w S := by
  rw [eval_genPoly]
  simp

theorem sum_pderiv_weight (w : Finset ι → ℝ) (i : ι) :
    ∑ U : Finset ι, (if i ∈ U then (0 : ℝ) else w (insert i U))
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S), w S := by
  classical
  have h : ∀ U : Finset ι, (if i ∈ U then (0 : ℝ) else w (insert i U))
      = if i ∉ U then w (insert i U) else 0 := by
    intro U
    by_cases hU : i ∈ U <;> simp [hU]
  rw [Finset.sum_congr rfl fun U _ => h U, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun U => insert i U) (fun S => S.erase i) ?_ ?_ ?_ ?_ ?_
  · intro U _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_insert_self i U
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact Finset.notMem_erase i S
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact Finset.erase_insert hU
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.insert_erase hS
  · intro U _
    rfl

theorem sum_sectorA (w : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) :
    ∑ V : Finset ι, sectorA w i j V
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ j ∈ S), w S := by
  classical
  have h : ∀ V : Finset ι, sectorA w i j V
      = if ¬ (i ∈ V ∨ j ∈ V) then w (insert i (insert j V)) else 0 := by
    intro V
    by_cases hV : i ∈ V ∨ j ∈ V <;> simp [sectorA, hV]
  rw [Finset.sum_congr rfl fun V _ => h V, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun V => insert i (insert j V))
    (fun S => (S.erase i).erase j) ?_ ?_ ?_ ?_ ?_
  · intro V _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.mem_insert_self i _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self j V)⟩
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    push Not
    exact ⟨fun hc => Finset.notMem_erase i S (Finset.mem_of_mem_erase hc),
      Finset.notMem_erase j _⟩
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
    push Not at hV
    rw [Finset.erase_insert (by simp [Finset.mem_insert, hij, hV.1]),
      Finset.erase_insert hV.2]
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hij, hS.2⟩),
      Finset.insert_erase hS.1]
  · intro V _
    rfl

/-- `probEvent` as a filtered sum, with the ambient decidability instance. -/
theorem probEvent_filter {n : ℕ} {y : Sym2 (Fin n) → ℝ} (μ : TreeDist n y)
    (Q : Finset (Sym2 (Fin n)) → Prop) [DecidablePred Q] :
    μ.probEvent Q = ∑ T ∈ Finset.univ.filter Q, μ.prob T := by
  classical
  simp only [TreeDist.probEvent]
  congr

/-- **Pairwise negative correlation at the max-entropy limit.**

Evaluating the Rayleigh condition at the all-ones point turns
`∂ₑp · ∂_fp − p · ∂ₑ∂_fp ≥ 0` into `P(e) · P(f) ≥ P(e ∧ f)`, since a generating
polynomial has value `1` there and its derivatives are exactly the marginals. -/
theorem IsMaxEntropyLimit.negCorrelation {n : ℕ} {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) {e f : Sym2 (Fin n)} (hef : e ≠ f) :
    μ.probEvent (fun T => e ∈ T ∧ f ∈ T)
      ≤ μ.probEvent (fun T => e ∈ T) * μ.probEvent (fun T => f ∈ T) := by
  have hray : RayleighNonneg (genPoly μ.prob) := rayleighNonneg_genPoly h.treeRealStable
  have h1 := hray e f (fun _ => (1 : ℝ))
  rw [rayleighDiff, pderiv_pderiv_genPoly _ hef, pderiv_genPoly, pderiv_genPoly,
    map_sub, map_mul, map_mul, eval_one_genPoly, eval_one_genPoly, eval_one_genPoly,
    eval_one_genPoly, sum_pderiv_weight, sum_pderiv_weight, sum_sectorA _ hef,
    μ.total, one_mul] at h1
  rw [probEvent_filter, probEvent_filter, probEvent_filter]
  exact sub_nonneg.mp h1

end TSPGap

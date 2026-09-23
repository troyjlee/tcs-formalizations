/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Stable
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Weighted determinant stability

For a real matrix `A` of full row rank, `det(A diag(z) Aᵀ) ≠ 0` whenever every
`z e` lies in the open upper half-plane; equivalently, the multivariate
polynomial `det(A diag(X) Aᵀ)` is real stable.

## Why this, and why before BBL

This is the first link of the chain that ends in stability of the λ-uniform
spanning-tree measure:

    determinant stability  (this file)
      → reduced oriented incidence matrix, and its full row rank
      → specialized Cauchy–Binet expansion
      → incidence minor = ±1 exactly for spanning trees
      → the λ-uniform generating polynomial is stable
      → `IsMaxEntropyLimit.realStable`

BBL is deliberately deferred: it is much larger, it does not itself prove
λ-uniform tree stability, and `StableLimit.lean`'s fixed-rank adapter has
already removed the reason for it to block this path.

**This file needs no graph theory and no Cauchy–Binet.**  It is pure linear
algebra over `ℂ`.

## The kernel-vector argument

If `det(A_ℂ diag(z) A_ℂᵀ) = 0` there is a nonzero `v` in the kernel.  Because
`A` is *real*, `A_ℂᵀ` is its conjugate transpose, so with `w = v ᵥ* A_ℂ` the
quadratic form collapses:

`v* (A_ℂ diag(z) A_ℂᵀ) v = ∑ e, z e ‖w e‖²`.

That vanishes, so its imaginary part `∑ e, Im(z e) ‖w e‖²` does too — a sum of
nonnegative terms with strictly positive coefficients.  Hence `w = 0`, and full
row rank gives `v = 0`.

Full row rank is taken in the form "no nonzero row combination vanishes"
(`FullRowRank`), which is what the argument consumes; no rank theory is needed.
Nor is any base-change lemma: `FullRowRank.vecMul_eq_zero` complexifies the
hypothesis by separating real and imaginary parts, which works precisely because
`A` is real.
-/

namespace TSPGap

open Matrix MvPolynomial

variable {r m : Type*} [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

/-! ### Full row rank, and its complexification -/

/-- **Full row rank**, in the form the argument uses: no nonzero combination of
the rows vanishes.  Equivalent to `A.rank = card r`, which is never needed. -/
def FullRowRank (A : Matrix r m ℝ) : Prop :=
  ∀ u : r → ℝ, Matrix.vecMul u A = 0 → u = 0

/-- The complexification of a real matrix. -/
noncomputable def cplx (A : Matrix r m ℝ) : Matrix r m ℂ := A.map (algebraMap ℝ ℂ)

omit [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m] in
@[simp] theorem cplx_apply (A : Matrix r m ℝ) (i : r) (e : m) :
    cplx A i e = ((A i e : ℝ) : ℂ) := rfl

omit [Fintype m] [DecidableEq r] [DecidableEq m] in
/-- **Full row rank survives complexification.**  No base-change or rank lemma:
the matrix is real, so it acts on real and imaginary parts independently. -/
theorem FullRowRank.vecMul_eq_zero {A : Matrix r m ℝ} (hA : FullRowRank A)
    (v : r → ℂ) (hv : Matrix.vecMul v (cplx A) = 0) : v = 0 := by
  have key : ∀ e, ∑ i, v i * ((A i e : ℝ) : ℂ) = 0 := by
    intro e
    have h := congrFun hv e
    simpa [Matrix.vecMul, dotProduct] using h
  have hre : Matrix.vecMul (fun i => (v i).re) A = 0 := by
    funext e
    have h' := congrArg Complex.re (key e)
    simpa [Matrix.vecMul, dotProduct, Complex.mul_re] using h'
  have him : Matrix.vecMul (fun i => (v i).im) A = 0 := by
    funext e
    have h := congrArg Complex.im (key e)
    simpa [Matrix.vecMul, dotProduct, Complex.mul_im] using h
  funext i
  have hr : (v i).re = 0 := congrFun (hA _ hre) i
  have hi : (v i).im = 0 := congrFun (hA _ him) i
  simp [Complex.ext_iff, hr, hi]

/-! ### The weighted Gram matrix -/

/-- `A diag(z) Aᵀ`, complexified. -/
noncomputable def weightedGram (A : Matrix r m ℝ) (z : m → ℂ) : Matrix r r ℂ :=
  cplx A * Matrix.diagonal z * (cplx A)ᵀ

/-- **Weighted determinant stability.**

The imaginary part of the quadratic form at a kernel vector is
`∑ e, Im(z e) ‖(A_ℂᵀ v) e‖²`; every coefficient is strictly positive and every
factor nonnegative, so the whole vector `A_ℂᵀ v` must vanish, and full row rank
finishes it. -/
theorem det_weightedGram_ne_zero {A : Matrix r m ℝ} (hA : FullRowRank A)
    {z : m → ℂ} (hz : ∀ e, 0 < (z e).im) : (weightedGram A z).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set w : m → ℂ := Matrix.vecMul v (cplx A) with hwdef
  -- `A` is real, so `v* A_ℂ` is the conjugate of `v ᵥ* A_ℂ`.
  have hstar : Matrix.vecMul (star v) (cplx A) = star w := by
    funext e
    simp only [hwdef, Matrix.vecMul, dotProduct, Pi.star_apply, cplx_apply,
      Complex.star_def, map_sum, map_mul, Complex.conj_ofReal]
  -- the quadratic form collapses to a weighted sum of squared norms
  have hquad : star v ⬝ᵥ ((weightedGram A z) *ᵥ v)
      = ∑ e, z e * ((Complex.normSq (w e) : ℝ) : ℂ) := by
    rw [dotProduct_mulVec, weightedGram, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, hstar, ← dotProduct_mulVec,
      Matrix.mulVec_transpose, ← hwdef, dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.vecMul_diagonal, Pi.star_apply, Complex.star_def,
      show (starRingEnd ℂ) (w e) * z e * w e
        = z e * ((starRingEnd ℂ) (w e) * w e) by ring,
      mul_comm ((starRingEnd ℂ) (w e)) (w e), Complex.mul_conj]
  have hzero : ∑ e, z e * ((Complex.normSq (w e) : ℝ) : ℂ) = 0 := by
    rw [← hquad, hv, dotProduct_zero]
  have him : ∑ e, (z e).im * Complex.normSq (w e) = 0 := by
    have h := congrArg Complex.im hzero
    simpa [Complex.mul_im] using h
  have hw0 : w = 0 := by
    funext e
    have hnn : ∀ e' ∈ (Finset.univ : Finset m), 0 ≤ (z e').im * Complex.normSq (w e') :=
      fun e' _ => mul_nonneg (hz e').le (Complex.normSq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp him e (Finset.mem_univ e)
    have hns : Complex.normSq (w e) = 0 := by
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h (ne_of_gt (hz e))
      · exact h
    simpa using Complex.normSq_eq_zero.mp hns
  refine hv0 (hA.vecMul_eq_zero v ?_)
  rw [← hwdef]
  exact hw0

/-! ### The determinant polynomial -/

/-- The **weighted determinant polynomial** `det(A diag(X) Aᵀ)`.

For the reduced oriented incidence matrix of a graph this is, by Cauchy–Binet,
the weighted spanning-tree polynomial — but nothing here knows that.

No multi-affinity is claimed.  It is true — Cauchy–Binet expands the determinant
as `∑_{|S| = r} det(A_S)² ∏_{e ∈ S} X e` — but that expansion is exactly the
*next* link in the chain, not this one. -/
noncomputable def detPoly (A : Matrix r m ℝ) : MvPolynomial m ℝ :=
  (A.map (C : ℝ → MvPolynomial m ℝ)
    * Matrix.diagonal (fun e => (X e : MvPolynomial m ℝ))
    * (A.map (C : ℝ → MvPolynomial m ℝ))ᵀ).det

/-- Evaluating the determinant polynomial is taking the determinant of the
evaluated matrix: `aeval` is a ring hom, and determinants commute with those. -/
theorem eval_map_detPoly (A : Matrix r m ℝ) (z : m → ℂ) :
    eval z ((detPoly A).map (algebraMap ℝ ℂ)) = (weightedGram A z).det := by
  set φ : MvPolynomial m ℝ →+* ℂ := (aeval z : MvPolynomial m ℝ →ₐ[ℝ] ℂ).toRingHom with hφ
  have haeval : eval z ((detPoly A).map (algebraMap ℝ ℂ)) = φ (detPoly A) :=
    (MvPolynomial.eval_map _ _ _).trans (MvPolynomial.aeval_def z (detPoly A)).symm
  have hmat : φ.mapMatrix (A.map (C : ℝ → MvPolynomial m ℝ)
      * Matrix.diagonal (fun e => (X e : MvPolynomial m ℝ))
      * (A.map (C : ℝ → MvPolynomial m ℝ))ᵀ) = weightedGram A z := by
    ext i j
    simp [hφ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.transpose_apply, weightedGram, cplx,
      apply_ite]
  rw [haeval, detPoly, RingHom.map_det φ, hmat]

/-- **The determinant polynomial of a full-row-rank real matrix is real
stable.** -/
theorem isRealStable_detPoly {A : Matrix r m ℝ} (hA : FullRowRank A) :
    IsRealStable (detPoly A) := by
  intro z hz
  rw [eval_map_detPoly]
  exact det_weightedGram_ne_zero hA hz

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Determinant

/-!
# Cauchy–Binet, and the Gram expansion of the determinant polynomial

The second link of the chain to λ-uniform tree stability.  This file fixes the
exact interface the graph layer will have to satisfy.

## No permutation expansion

Cauchy–Binet comes out of two Mathlib lemmas and a coefficient comparison:
`Matrix.det_one_add_mul_comm` gives `det(1 + XAB) = det(1 + XBA)`, and
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors` reads off the coefficient of
`X^k` as a sum of principal `k × k` minors.  Taking `k = |r|` makes the left side
collapse to a single term — the only `|r|`-subset of `r` is everything — and the
right side is the Cauchy–Binet sum.  No permutation combinatorics is needed.

## Everything stays sign-free

`det_mul_eq_sum_principalMinors` is stated with *principal minors of `BA`*, not
as `∑ det(A_S) det(B_S)`.  The factored form needs an ordering of `S` to make
`det(A_S)` meaningful, and different orderings flip its sign; the principal minor
is canonical.  `gramMinor A S := det(A_S A_Sᵀ)` inherits that: the `±1` is
squared away before anything downstream sees it.

That is deliberate, and it is what makes the *next* increment clean.  All
enumeration and determinant-sign choices are settled here, so the graph layer
sees only an invariant Gram determinant, and its single substantive target is

    gramMinor (reducedIncidence k) T = if IsSpanningTree (k+1) T then 1 else 0

for `T.card = k`, with the reduced incidence matrix indexed by successors — last
vertex deleted, edges oriented from `inf` to `sup`.

## Main results

* `det_mul_eq_sum_principalMinors` — Cauchy–Binet for rectangular `A`, `B`.
* `gramMinor`, `gramMinor_map` — the sign-free minor, and its behaviour under a
  ring hom.
* `det_gram_comm` — `det(M Mᵀ) = det(Mᵀ M)` when the two index types have equal
  cardinality; a second application of Cauchy–Binet, not a new argument.
* `det_weighted_eq_sum_gramMinor` — `det(A diag(d) Aᵀ) = ∑ gramMinor(A,S) ∏ d`.
* `detPoly_eq_sum_gramMinor`, `detPoly_eq_genPoly`, `coeff_detPoly`,
  `isMultiAffine_detPoly`.

`detPoly_eq_genPoly` is the pleasant landing: the determinant polynomial *is* a
`genPoly` — the one from `Stable.lean` — for the weight
`S ↦ if S.card = |r| then gramMinor A S else 0`.  The coefficient formula and
multi-affinity then come for free, and `StableLimit.lean`'s fixed-rank machinery
already speaks this language.
-/

namespace TSPGap

open Matrix MvPolynomial

variable {r m : Type*} [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

/-! ### Cauchy–Binet -/

/-- **Cauchy–Binet**, in principal-minor form: the determinant of a product of
rectangular matrices is the sum of the `|r| × |r|` principal minors of the
product taken the other way.

Proof: compare the coefficient of `X^{|r|}` on the two sides of
`det(1 + XAB) = det(1 + XBA)`.  On the left only `S = univ` contributes. -/
theorem det_mul_eq_sum_principalMinors {R : Type*} [CommRing R]
    (A : Matrix r m R) (B : Matrix m r R) :
    (A * B).det = ∑ S ∈ Finset.powersetCard (Fintype.card r) (Finset.univ : Finset m),
      ((B * A).submatrix (Subtype.val : {x // x ∈ S} → m) Subtype.val).det := by
  classical
  have key := Matrix.det_one_add_mul_comm
    ((Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R))
    (B.map (Polynomial.C : R →+* Polynomial R))
  have h1 : ((Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R))
        * (B.map (Polynomial.C : R →+* Polynomial R))
      = (Polynomial.X : Polynomial R) • ((A * B).map (Polynomial.C : R →+* Polynomial R)) := by
    rw [Matrix.smul_mul]
    exact congrArg _ (Matrix.map_mul (f := (Polynomial.C : R →+* Polynomial R))).symm
  have h2 : (B.map (Polynomial.C : R →+* Polynomial R))
        * ((Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R))
      = (Polynomial.X : Polynomial R) • ((B * A).map (Polynomial.C : R →+* Polynomial R)) := by
    rw [Matrix.mul_smul]
    exact congrArg _ (Matrix.map_mul (f := (Polynomial.C : R →+* Polynomial R))).symm
  rw [h1, h2] at key
  have hcoeff : (1 + (Polynomial.X : Polynomial R) • ((A * B).map (Polynomial.C : R →+* Polynomial R))).det.coeff
        (Fintype.card r)
      = (1 + (Polynomial.X : Polynomial R) • ((B * A).map (Polynomial.C : R →+* Polynomial R))).det.coeff
        (Fintype.card r) := by
    rw [key]
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors] at hcoeff
  rw [← hcoeff]
  have huniv : Finset.powersetCard (Fintype.card r) (Finset.univ : Finset r) = {Finset.univ} := by
    rw [← Finset.card_univ]
    exact Finset.powersetCard_self _
  rw [huniv, Finset.sum_singleton]
  exact (Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) _).symm

/-! ### The sign-free Gram minor -/

/-- `A` with its columns restricted to `S`. -/
def colsOn {R : Type*} (A : Matrix r m R) (S : Finset m) : Matrix r {x // x ∈ S} R :=
  A.submatrix id Subtype.val

/-- The **Gram minor** of `A` on a set `S` of columns: `det(A_S A_Sᵀ)`.

Sign-free by construction.  No ordering of `S` is chosen — none is available
without one — and the `±1` ambiguity that an ordering would introduce is squared
away.  This is the quantity the graph layer has to compute. -/
def gramMinor {R : Type*} [CommRing R] (A : Matrix r m R) (S : Finset m) : R :=
  (colsOn A S * (colsOn A S)ᵀ).det

omit [Fintype m] [DecidableEq m] in
theorem gramMinor_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (A : Matrix r m R) (S : Finset m) : gramMinor (A.map f) S = f (gramMinor A S) := by
  have h : colsOn (A.map f) S * (colsOn (A.map f) S)ᵀ
      = (colsOn A S * (colsOn A S)ᵀ).map f := by
    rw [Matrix.map_mul]
    rfl
  rw [gramMinor, gramMinor, h, RingHom.map_det, RingHom.mapMatrix_apply]

/-- **`det(M Mᵀ) = det(Mᵀ M)` when the index types have equal cardinality.**

Not a new argument: it is Cauchy–Binet again, with the sum over `|r|`-subsets of
a type of exactly `|r|` elements, hence a single term. -/
theorem det_gram_comm {R : Type*} [CommRing R] {s : Type*} [Fintype s] [DecidableEq s]
    (M : Matrix r s R) (h : Fintype.card s = Fintype.card r) :
    (M * Mᵀ).det = (Mᵀ * M).det := by
  rw [det_mul_eq_sum_principalMinors M Mᵀ]
  have huniv : Finset.powersetCard (Fintype.card r) (Finset.univ : Finset s) = {Finset.univ} := by
    rw [← h, ← Finset.card_univ]
    exact Finset.powersetCard_self _
  rw [huniv, Finset.sum_singleton]
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) _

/-! ### The weighted expansion -/

/-- **The weighted Cauchy–Binet expansion.**

`det(A diag(d) Aᵀ) = ∑_{|S| = |r|} gramMinor(A, S) ∏_{e ∈ S} d e`.

The diagonal weight factors out of each principal minor, and `det_gram_comm`
turns the minor of `AᵀA` into the sign-free Gram minor. -/
theorem det_weighted_eq_sum_gramMinor {R : Type*} [CommRing R] (A : Matrix r m R) (d : m → R) :
    (A * Matrix.diagonal d * Aᵀ).det
      = ∑ S ∈ Finset.powersetCard (Fintype.card r) (Finset.univ : Finset m),
          gramMinor A S * ∏ e ∈ S, d e := by
  classical
  rw [det_mul_eq_sum_principalMinors (A * Matrix.diagonal d) Aᵀ]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hcard : S.card = Fintype.card r := Finset.mem_powersetCard_univ.mp hS
  have hfac : (Aᵀ * (A * Matrix.diagonal d)).submatrix
        (Subtype.val : {x // x ∈ S} → m) Subtype.val
      = ((colsOn A S)ᵀ * colsOn A S)
        * Matrix.diagonal (fun e : {x // x ∈ S} => d (e : m)) := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.mul_apply,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.transpose_apply, colsOn,
      Matrix.submatrix_apply, Matrix.submatrix_apply]
    simp only [id_eq]
    ring
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_coe_sort]
  congr 1
  exact (det_gram_comm (colsOn A S) (by rw [Fintype.card_coe]; exact hcard)).symm

/-! ### The determinant polynomial, expanded -/

theorem detPoly_eq_sum_gramMinor (A : Matrix r m ℝ) :
    detPoly A = ∑ S ∈ Finset.powersetCard (Fintype.card r) (Finset.univ : Finset m),
      C (gramMinor A S) * ∏ e ∈ S, X e := by
  rw [detPoly, det_weighted_eq_sum_gramMinor]
  exact Finset.sum_congr rfl fun S _ => by rw [gramMinor_map]

/-- **The determinant polynomial is a generating polynomial.**

For the weight `S ↦ if S.card = |r| then gramMinor A S else 0` — which is
supported on rank `|r|` by construction, exactly the shape
`StableLimit.lean`'s `FixedRankNormalized` wants (bar normalization). -/
theorem detPoly_eq_genPoly (A : Matrix r m ℝ) :
    detPoly A = genPoly (fun S => if S.card = Fintype.card r then gramMinor A S else 0) := by
  classical
  have hfilter : (Finset.univ : Finset (Finset m)).filter (fun S => S.card = Fintype.card r)
      = Finset.powersetCard (Fintype.card r) (Finset.univ : Finset m) := by
    ext S
    simp
  rw [detPoly_eq_sum_gramMinor, genPoly, ← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : S.card = Fintype.card r <;> simp [hS]

/-- The coefficient of a squarefree monomial is the corresponding Gram minor. -/
theorem coeff_detPoly (A : Matrix r m ℝ) (S : Finset m) :
    (detPoly A).coeff (sqExp S)
      = if S.card = Fintype.card r then gramMinor A S else 0 := by
  rw [detPoly_eq_genPoly, coeff_genPoly]

/-- **The determinant polynomial is multi-affine.**  Deferred in
`Determinant.lean` precisely because it is Cauchy–Binet; here it is free. -/
theorem isMultiAffine_detPoly (A : Matrix r m ℝ) : IsMultiAffine (detPoly A) := by
  rw [detPoly_eq_genPoly]
  exact isMultiAffine_genPoly _

end TSPGap

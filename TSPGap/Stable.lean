/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Real stability and generating polynomials

We use Mathlib's multivariate polynomials, evaluation, renaming, substitution
and partial derivatives to define real stability and generating polynomials
for finite measures.

## The representation

A measure on subsets of `ι` is a weight `w : Finset ι → ℝ` — the same shape as
the probability vectors of `MaxEntropyLimit.lean`, deliberately, so that the
limit machinery applies to it without translation.  Its **generating
polynomial** is

`g_w(z) = ∑_S w S · ∏_{i ∈ S} z i`,

a multi-affine element of `MvPolynomial ι ℝ`.  Stability is nonvanishing on the
open upper half-plane, tested at assignments `ι → ℂ`.

## Two predicates, not one

`IsRealStable` and `IsRealStableOrZero` are kept apart.  A stable polynomial
has derivatives and specializations that may vanish identically, and the zero
polynomial is not stable (it vanishes everywhere), so the closure statements
that *produce* new polynomials are naturally about the second.  `IsRealStable`
is the zero-free condition alone: `IsRealStable.ne_zero` shows the nonvanishing
requirement is implied rather than assumed.

## What is deliberately not here

`rayleighDiff` is defined here and nothing is claimed about it.  The **forward**
half of Borcea–Brändén–Liggett — stability plus multi-affinity implies the
Rayleigh difference is nonnegative on `ℝ^ι` — is proved in `Rayleigh.lean`.

⚠️ The **reverse** half is deferred/optional and off the critical path.  It was
wanted mainly as a limit adapter, and `StableLimit.lean` supplies that by a
smaller fixed-rank argument, so nothing downstream needs the equivalence.

Truncation and negative association are separately scoped.  Stability of the
spanning-tree polynomial is proved in `TreeStability.lean`, on a *polynomial*
matrix-tree identity built here rather than imported from Mathlib.

⚠️ **Two guardrails.**  The closures below preserve *stability* and say nothing
about multi-affinity, which they can destroy: arbitrary `rename` identifies
variables (`X i · X j ↦ X k ^ 2`), and multiplication preserves multi-affinity
only when the factors' coordinate supports are disjoint.  `StableLimit.lean`
relies on neither.
-/

namespace TSPGap

open MvPolynomial Finset

variable {ι : Type*}

/-! ### Squarefree exponent vectors

The monomials of a generating polynomial are the squarefree ones, indexed by
the subsets themselves. -/

/-- The `0/1` exponent vector of a finite set: the monomial `∏_{i ∈ S} X i`. -/
noncomputable def sqExp [DecidableEq ι] (S : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator S fun _ _ => 1

@[simp] theorem sqExp_apply [DecidableEq ι] (S : Finset ι) (i : ι) :
    sqExp S i = if i ∈ S then 1 else 0 := by
  simp [sqExp, Finsupp.indicator_apply]

theorem sqExp_le_one [DecidableEq ι] (S : Finset ι) (i : ι) : sqExp S i ≤ 1 := by
  rw [sqExp_apply]
  split <;> simp

/-- Distinct sets give distinct monomials: the set is read back off the
exponent vector. -/
theorem sqExp_injective [DecidableEq ι] : Function.Injective (sqExp (ι := ι)) := by
  intro S T h
  ext i
  have hi := congrArg (fun m => m i) h
  simp only [sqExp_apply] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

theorem sqExp_insert [DecidableEq ι] {a : ι} {S : Finset ι} (ha : a ∉ S) :
    sqExp (insert a S) = Finsupp.single a 1 + sqExp S := by
  ext i
  rw [Finsupp.add_apply, sqExp_apply, sqExp_apply, Finsupp.single_apply]
  by_cases hi : i = a
  · subst hi
    simp [ha]
  · simp [hi, Ne.symm hi, Finset.mem_insert]

theorem prod_X_eq_monomial [DecidableEq ι] {R : Type*} [CommSemiring R]
    (S : Finset ι) :
    (∏ i ∈ S, (X i : MvPolynomial ι R)) = monomial (sqExp S) 1 := by
  classical
  induction S using Finset.induction with
  | empty =>
      have h0 : sqExp (∅ : Finset ι) = 0 := by ext i; simp
      simp [h0]
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, ih, sqExp_insert ha, monomial_single_add, pow_one]

/-! ### Generating polynomials -/

/-- The **generating polynomial** of a weight on subsets:
`g_w(z) = ∑_S w S · ∏_{i ∈ S} z i`. -/
noncomputable def genPoly [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ) :
    MvPolynomial ι ℝ :=
  ∑ S : Finset ι, C (w S) * ∏ i ∈ S, X i

theorem genPoly_eq_sum_monomial [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ) :
    genPoly w = ∑ S : Finset ι, monomial (sqExp S) (w S) := by
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_X_eq_monomial, C_mul_monomial, mul_one]

/-- **The coefficient formula.**  The weight of `S` is the coefficient of the
squarefree monomial of `S` — the correspondence is a bijection, not merely a
map. -/
theorem coeff_genPoly [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ)
    (S : Finset ι) : (genPoly w).coeff (sqExp S) = w S := by
  classical
  rw [genPoly_eq_sum_monomial, coeff_sum]
  rw [Finset.sum_eq_single S]
  · rw [coeff_monomial, if_pos rfl]
  · intro T _ hT
    rw [coeff_monomial, if_neg fun hc => hT (sqExp_injective hc)]
  · intro h
    exact absurd (Finset.mem_univ S) h

/-- **Weights are determined by their generating polynomial.** -/
theorem genPoly_injective [Fintype ι] [DecidableEq ι] :
    Function.Injective (genPoly (ι := ι)) := by
  intro w w' h
  funext S
  rw [← coeff_genPoly w S, ← coeff_genPoly w' S, h]

/-- **The evaluation formula**, over any commutative ring the reals map into —
here stated for a ring homomorphism, so that the complex case used by stability
and the real case are one lemma. -/
theorem eval_map_genPoly [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (φ : ℝ →+* R) (w : Finset ι → ℝ) (z : ι → R) :
    eval z ((genPoly w).map φ) = ∑ S : Finset ι, φ (w S) * ∏ i ∈ S, z i := by
  rw [genPoly]
  rw [show MvPolynomial.map φ (∑ S : Finset ι, C (w S) * ∏ i ∈ S, X i)
      = ∑ S : Finset ι, MvPolynomial.map φ (C (w S) * ∏ i ∈ S, X i) from map_sum _ _ _]
  rw [show eval z (∑ S : Finset ι, MvPolynomial.map φ (C (w S) * ∏ i ∈ S, X i))
      = ∑ S : Finset ι, eval z (MvPolynomial.map φ (C (w S) * ∏ i ∈ S, X i))
        from map_sum _ _ _]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp

theorem eval_genPoly [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ) (z : ι → ℝ) :
    eval z (genPoly w) = ∑ S : Finset ι, w S * ∏ i ∈ S, z i := by
  have h := eval_map_genPoly (RingHom.id ℝ) w z
  simpa using h

/-! ### Multi-affinity -/

/-- `p` is **multi-affine** when no variable occurs to degree two or more. -/
def IsMultiAffine {R : Type*} [CommSemiring R] (p : MvPolynomial ι R) : Prop :=
  ∀ (m : ι →₀ ℕ) (i : ι), 2 ≤ m i → p.coeff m = 0

/-- The support form: every monomial of a multi-affine polynomial is
squarefree. -/
theorem IsMultiAffine.le_one {R : Type*} [CommSemiring R] {p : MvPolynomial ι R}
    (h : IsMultiAffine p) {m : ι →₀ ℕ} (hm : m ∈ p.support) (i : ι) : m i ≤ 1 := by
  by_contra hc
  exact (mem_support_iff.mp hm) (h m i (by omega))

theorem isMultiAffine_genPoly [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ) :
    IsMultiAffine (genPoly w) := by
  classical
  intro m i hi
  rw [genPoly_eq_sum_monomial, coeff_sum]
  refine Finset.sum_eq_zero fun S _ => ?_
  refine (coeff_monomial _ _ _).trans (if_neg fun hc => ?_)
  have := sqExp_le_one S i
  rw [hc] at this
  omega

/-! ### Real stability

The definition is nonvanishing on the open upper half-plane.  This is *not* a
condition on the coefficients, which is why the Borcea–Brändén–Liggett
criterion is a theorem and not an unfolding. -/

/-- `p` has **no zero with every coordinate in the open upper half-plane**. -/
def ZeroFreeUpper (p : MvPolynomial ι ℂ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) → eval z p ≠ 0

/-- **Real stable**: real coefficients, and no zero in the open upper
half-plane. -/
def IsRealStable (p : MvPolynomial ι ℝ) : Prop :=
  ZeroFreeUpper (p.map (algebraMap ℝ ℂ))

/-- **Stable or identically zero.**  Derivatives and specializations of a stable
polynomial can vanish identically, so the closure statements that build new
polynomials land here rather than in `IsRealStable`. -/
def IsRealStableOrZero (p : MvPolynomial ι ℝ) : Prop := p = 0 ∨ IsRealStable p

theorem ZeroFreeUpper.ne_zero {p : MvPolynomial ι ℂ} (h : ZeroFreeUpper p) :
    p ≠ 0 := by
  intro hp
  exact h (fun _ => Complex.I) (fun _ => by simp) (by simp [hp])

/-- Nonvanishing is not an extra hypothesis: a zero-free polynomial is nonzero,
because the upper half-plane is not empty. -/
theorem IsRealStable.ne_zero {p : MvPolynomial ι ℝ} (h : IsRealStable p) :
    p ≠ 0 := by
  intro hp
  exact ZeroFreeUpper.ne_zero h (by rw [hp]; exact map_zero _)

theorem IsRealStable.isRealStableOrZero {p : MvPolynomial ι ℝ}
    (h : IsRealStable p) : IsRealStableOrZero p := Or.inr h

/-! ### The easy closures

Each of these is a change of variables that keeps the upper half-plane inside
itself, so the zero-free condition transfers unchanged.  Nothing here needs
Hurwitz or BBL. -/

/-- **Products.**

⚠️ **Stability only.**  Multiplication does *not* preserve `IsMultiAffine` in
general — `X i · X i` is the immediate counterexample — and does so exactly when
the two factors use disjoint sets of coordinates. -/
theorem IsRealStable.mul {p q : MvPolynomial ι ℝ} (hp : IsRealStable p)
    (hq : IsRealStable q) : IsRealStable (p * q) := by
  intro z hz
  simp only [map_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

theorem IsRealStableOrZero.mul {p q : MvPolynomial ι ℝ}
    (hp : IsRealStableOrZero p) (hq : IsRealStableOrZero q) :
    IsRealStableOrZero (p * q) := by
  rcases hp with rfl | hp
  · exact Or.inl (zero_mul q)
  rcases hq with rfl | hq
  · exact Or.inl (mul_zero p)
  · exact Or.inr (hp.mul hq)

/-- **Nonzero scalars.** -/
theorem IsRealStable.const_mul {c : ℝ} (hc : c ≠ 0) {p : MvPolynomial ι ℝ}
    (hp : IsRealStable p) : IsRealStable (C c * p) := by
  intro z hz
  simp only [map_mul, MvPolynomial.map_C, eval_C]
  refine mul_ne_zero ?_ (hp z hz)
  simpa using hc

/-- **Renaming, including diagonalization.**  A substitution `X i ↦ X (f i)`
for an arbitrary `f` — not necessarily injective, so this covers identifying
variables — carries the upper half-plane into itself coordinatewise, and that is
all the zero-free condition sees.

⚠️ **Stability only.**  Renaming does *not* preserve `IsMultiAffine`: a
non-injective `f` identifies variables, and `X i · X j ↦ X k ^ 2`.  Anything
downstream that needs multi-affinity has to re-establish it. -/
theorem IsRealStable.rename {τ : Type*} (f : ι → τ) {p : MvPolynomial ι ℝ}
    (hp : IsRealStable p) : IsRealStable (rename f p) := by
  intro z hz
  rw [MvPolynomial.map_rename, eval_rename]
  exact hp (z ∘ f) fun i => hz (f i)

theorem IsRealStableOrZero.rename {τ : Type*} (f : ι → τ) {p : MvPolynomial ι ℝ}
    (hp : IsRealStableOrZero p) : IsRealStableOrZero (rename f p) := by
  rcases hp with rfl | hp
  · exact Or.inl (map_zero _)
  · exact Or.inr (hp.rename f)

/-- **Strictly positive coordinate scaling**, `X i ↦ c i · X i` with `c i > 0`.
Multiplying by a positive real keeps the imaginary part positive, so again the
upper half-plane maps into itself. -/
theorem IsRealStable.scale {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {p : MvPolynomial ι ℝ} (hp : IsRealStable p) :
    IsRealStable (bind₁ (fun i => C (c i) * X i) p) := by
  intro z hz
  rw [MvPolynomial.map_bind₁]
  have hbind : eval z (bind₁ (fun i => (C ((algebraMap ℝ ℂ) (c i)) * X i :
      MvPolynomial ι ℂ)) (p.map (algebraMap ℝ ℂ)))
      = eval (fun i => (algebraMap ℝ ℂ) (c i) * z i) (p.map (algebraMap ℝ ℂ)) := by
    have h := eval₂Hom_bind₁ (RingHom.id ℂ) z
      (fun i => (C ((algebraMap ℝ ℂ) (c i)) * X i : MvPolynomial ι ℂ))
      (p.map (algebraMap ℝ ℂ))
    simpa using h
  have hmapC : ∀ i, MvPolynomial.map (algebraMap ℝ ℂ) (C (c i) * X i)
      = C ((algebraMap ℝ ℂ) (c i)) * X i := by
    intro i
    simp
  simp only [hmapC]
  rw [hbind]
  refine hp _ fun i => ?_
  have : ((algebraMap ℝ ℂ) (c i) * z i).im = c i * (z i).im := by
    simp [Complex.mul_im]
  rw [this]
  exact mul_pos (hc i) (hz i)

/-! ### The Rayleigh difference

Defined here, with nothing claimed.  Borcea–Brändén–Liggett: for a *multi-affine*
`p` with real coefficients, `IsRealStableOrZero p` is equivalent to
`0 ≤ eval x (rayleighDiff p i j)` for every `x : ι → ℝ` and every `i, j`.

The **forward** direction is `Rayleigh.lean`'s `IsRealStable.rayleighNonneg`, and
it is the half the payment argument uses.  ⚠️ The **reverse** direction is
deferred/optional: it was wanted as a limit adapter, and `StableLimit.lean`
already discharges that by a smaller fixed-rank argument. -/

/-- The **Rayleigh difference** `∂ᵢp · ∂ⱼp − p · ∂ᵢ∂ⱼp`. -/
noncomputable def rayleighDiff (p : MvPolynomial ι ℝ) (i j : ι) :
    MvPolynomial ι ℝ :=
  pderiv i p * pderiv j p - p * pderiv j (pderiv i p)

/-- The pairwise Rayleigh condition, in the form BBL's criterion would
deliver: a family of non-strict inequalities in the coefficient vector. -/
def RayleighNonneg (p : MvPolynomial ι ℝ) : Prop :=
  ∀ (i j : ι) (x : ι → ℝ), 0 ≤ eval x (rayleighDiff p i j)

end TSPGap

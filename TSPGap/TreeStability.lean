/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Incidence
import TSPGap.StableLimit

/-!
# λ-uniform spanning-tree distributions are real stable

The last link.  `IsMaxEntropyLimit.treeRealStable` closes the chain begun in
`Determinant.lean`, with no callback and no hypotheses:

    determinant stability
      → Cauchy–Binet
      → reduced oriented incidence matrix, full row rank
      → incidence Gram minor = spanning-tree indicator
      → λ-uniform generating polynomial stable      (here)
      → `IsMaxEntropyLimit.realStable`               (here)

## Only scaling and normalization remain

`detPoly_eq_genPoly` already put the determinant polynomial in `genPoly` form,
and `gramMinor_reducedIncidence` identifies its weight with the spanning-tree
indicator.  So the work here is genuinely just introducing the λ-weights and
dividing by `Z`:

* `bind₁_scale_genPoly` — the substitution `X e ↦ C (lam e) · X e` multiplies the
  weight of each subset `T` by `∏_{e ∈ T} lam e`;
* `const_mul_genPoly` — a scalar multiple scales every weight.

Both closures are already in `Stable.lean` (`IsRealStable.scale` for strictly
positive coordinate scaling, `IsRealStable.const_mul` for a nonzero scalar), so
strict positivity is used exactly twice and exactly where expected: `lam e > 0`
for the coordinate scaling, and `Z > 0` only to know `Z⁻¹ ≠ 0`.

⚠️ **What is *not* needed here is the *scalar* identity for `Z`.**  The
*polynomial* matrix-tree identity very much was needed — it is
`detPoly_reducedIncidence_eq_treeGenPoly`, delivered by Cauchy–Binet together
with the incidence Gram minor, and it is what identifies the determinant
polynomial with the weighted tree polynomial in the first place.  What never
appears is `Z = ∑_T ∏_{e ∈ T} lam e`, or any derivative formula for the
marginals: stability is invariant under a nonzero scalar, so `Z` only has to be
nonzero.

## Two bookkeeping seams

**Off-tree weights.**  `IsLambdaUniform` gives the formula `prob T = (∏ lam)/Z`
only on spanning trees.  It extends to all edge sets through
`TreeDist.support_spanningTree`: off the support the probability is zero, which
is what the indicator form records.

**Arbitrary `n`.**  `reducedIncidence k` is indexed by `Fin (k+1)`, so `n` has to
be split.  The zero case is *impossible*, not merely awkward: a `TreeDist` has
total mass one, hence some tree of positive probability, hence a spanning tree,
hence `Nonempty (Fin n)`.  The successor case then matches definitionally.
-/

namespace TSPGap

open MvPolynomial

/-! ### Scaling generating polynomials -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Coordinate scaling multiplies each subset weight by `∏_{i ∈ S} lam i`.** -/
theorem bind₁_scale_genPoly (lam : ι → ℝ) (w : Finset ι → ℝ) :
    bind₁ (fun i => C (lam i) * X i) (genPoly w)
      = genPoly (fun S => w S * ∏ i ∈ S, lam i) := by
  rw [genPoly, genPoly, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hprod : bind₁ (fun i => (C (lam i) : MvPolynomial ι ℝ) * X i) (∏ i ∈ S, X i)
      = ∏ i ∈ S, ((C (lam i) : MvPolynomial ι ℝ) * X i) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => MvPolynomial.bind₁_X_right _ i
  rw [map_mul, MvPolynomial.bind₁_C_right, hprod, Finset.prod_mul_distrib, map_mul, map_prod]
  ring

/-- **A scalar multiple scales every weight.** -/
theorem const_mul_genPoly (c : ℝ) (w : Finset ι → ℝ) :
    C c * genPoly w = genPoly (fun S => c * w S) := by
  rw [genPoly, genPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_mul]
  ring

/-! ### The unweighted spanning-tree polynomial -/

open Classical in
/-- **The determinant polynomial of the reduced incidence matrix is the
spanning-tree generating polynomial.**

Off rank `k` both weights vanish — a spanning tree of `Fin (k+1)` has exactly `k`
edges — so the two agree pointwise. -/
theorem detPoly_reducedIncidence_eq_treeGenPoly (k : ℕ) :
    detPoly (reducedIncidence k)
      = genPoly (fun T => if IsSpanningTree (k+1) T then (1 : ℝ) else 0) := by
  rw [detPoly_eq_genPoly]
  refine congrArg genPoly (funext fun T => ?_)
  rw [Fintype.card_fin]
  by_cases hc : T.card = k
  · rw [if_pos hc, gramMinor_reducedIncidence k hc]
  · rw [if_neg hc, if_neg fun hst => hc (by simpa using hst.2.1)]

/-! ### The weighted spanning-tree polynomial -/

open Classical in
/-- **The weighted spanning-tree polynomial is real stable.**

Strict positivity of `lam` is used here and only here, for the coordinate
scaling. -/
theorem isRealStable_weightedSpanningTree (k : ℕ) {lam : Sym2 (Fin (k+1)) → ℝ}
    (hlam : ∀ e, 0 < lam e) :
    IsRealStable
      (genPoly (fun T => if IsSpanningTree (k+1) T then ∏ e ∈ T, lam e else 0)) := by
  have hstable : IsRealStable (detPoly (reducedIncidence k)) :=
    isRealStable_detPoly (fullRowRank_reducedIncidence k)
  rw [detPoly_reducedIncidence_eq_treeGenPoly] at hstable
  have hscaled := hstable.scale hlam
  rw [bind₁_scale_genPoly] at hscaled
  have heq : (fun T : Finset (Sym2 (Fin (k+1))) =>
      (if IsSpanningTree (k+1) T then (1 : ℝ) else 0) * ∏ e ∈ T, lam e)
      = fun T => if IsSpanningTree (k+1) T then ∏ e ∈ T, lam e else 0 := by
    funext T
    split_ifs <;> ring
  rwa [heq] at hscaled

/-! ### λ-uniform distributions -/

/-- **A λ-uniform spanning-tree distribution has a real stable generating
polynomial.**

`Z > 0` enters only through `Z⁻¹ ≠ 0`; no identity for the partition function is
needed. -/
theorem isRealStable_genPoly_of_lambdaUniform {n : ℕ} {y : Sym2 (Fin n) → ℝ}
    (ν : TreeDist n y) (hν : IsLambdaUniform ν) : IsRealStable (genPoly ν.prob) := by
  classical
  obtain ⟨lam, hlam, Z, hZ, hprob⟩ := hν
  -- the distribution has a tree in its support, so the vertex set is nonempty
  obtain ⟨T₀, hT₀⟩ : ∃ T, ν.prob T ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 : (1 : ℝ) = 0 := by
      rw [← ν.total]
      exact Finset.sum_eq_zero fun T _ => hc T
    norm_num at h1
  have hnonempty : Nonempty (Fin n) := (ν.support_spanningTree T₀ hT₀).2.2.nonempty
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    exact (Classical.choice hnonempty).elim0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  -- the λ-formula extends off the support, where the probability is zero
  have hfull : ∀ T, ν.prob T
      = Z⁻¹ * (if IsSpanningTree (k+1) T then ∏ e ∈ T, lam e else 0) := by
    intro T
    by_cases hst : IsSpanningTree (k+1) T
    · rw [if_pos hst, hprob T hst, div_eq_inv_mul]
    · rw [if_neg hst, mul_zero]
      by_contra hc
      exact hst (ν.support_spanningTree T hc)
  rw [show ν.prob
      = fun T => Z⁻¹ * (if IsSpanningTree (k+1) T then ∏ e ∈ T, lam e else 0) from funext hfull,
    ← const_mul_genPoly]
  exact IsRealStable.const_mul (inv_ne_zero (ne_of_gt hZ))
    (isRealStable_weightedSpanningTree k hlam)

/-- **The export.**  The max-entropy limit has a real stable generating
polynomial — no callback, no hypotheses.

This closes the chain from `Determinant.lean`: `StableLimit.lean` carries
stability through the limit at fixed rank, `TreeDist.fixedRankNormalized`
supplies the rank, and the λ-uniform case is now proved outright. -/
theorem IsMaxEntropyLimit.treeRealStable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) : IsRealStable (genPoly μ.prob) :=
  h.realStable fun ν hν => isRealStable_genPoly_of_lambdaUniform ν hν

end TSPGap

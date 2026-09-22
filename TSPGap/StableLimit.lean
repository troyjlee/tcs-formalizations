/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MaxEntropyLimit
import TSPGap.Stable

/-!
# Real stability survives the max-entropy limit, at fixed rank

The adapter that `MaxEntropyLimit.lean` left outstanding on the stability side.

**This is not the Borcea–Brändén–Liggett criterion.**  BBL is a two-way
equivalence between stability and nonnegativity of the Rayleigh difference, and
its reverse implication is a substantial theorem in its own right.  What is
proved here is the smaller, tree-specific fact that stability passes to the
limit *for weights of a fixed rank with total mass one*, by restricting to a
line and using Mathlib's continuity of roots for monic polynomials of equal
degree.  BBL remains a separate subproject.

## The argument

Fix `z : ι → ℂ` with every coordinate in the open upper half-plane and set
`q_{w,z}(t) = g_w(z + t·1)`.  Rank `r` makes every surviving term
`∏_{i ∈ S}(z i + t)` of degree exactly `r` in `t`, and total mass one makes the
leading coefficients add to one, so `q_{w,z}` is **monic of degree `r`** —
which is what root continuity needs, and what neither condition gives alone.

If `g_w` is stable then `q_{w,z}` has no root with `Im t ≥ 0`.  A coefficientwise
limit of such polynomials can have roots on the real axis — `t + i/k → t` — so
the evaluation point has to be moved strictly inside: shifting `z` down by
`i·ε₀/2`, where `ε₀` is the least imaginary part, puts the point of interest at
`t = i·ε₀/2` with `Im t > 0`, where the limit is still zero-free.

## The invariant travels with the property

`limitClosed_fixedRankStable` is stated for the **conjunction**

`FixedRankNormalized r w ∧ IsRealStable (genPoly w)`,

and that is not decoration.  Stability alone is *not* a sound thing to close
under limits: nonzero stable polynomials can converge to zero, and
`LimitClosed`'s interface would forget that the approximants share a rank, which
is exactly the hypothesis the line restriction needs.  Carrying the invariant in
the property is what keeps the approximants usable.

## Guardrails carried over from `Stable.lean`

Two closure facts there preserve stability but **not** multi-affinity, and
nothing in this file assumes otherwise: arbitrary `rename` (a non-injective `f`
identifies variables and squares them), and multiplication (except when the
coordinate supports are disjoint).
-/

namespace TSPGap

open MvPolynomial Finset

variable {ι : Type*}

/-! ### Fixed-rank normalized weights -/

/-- A weight is **fixed-rank normalized** of rank `r` when it is a probability
distribution supported on the sets of size `r`.

Stated as "vanishes off rank `r`" rather than "supported on rank `r`" so that
each clause is manifestly a closed condition on the weight vector — which is
what `limitClosed_fixedRankStable` needs. -/
structure FixedRankNormalized [Fintype ι] (r : ℕ) (w : Finset ι → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ w S
  supported : ∀ S, S.card ≠ r → w S = 0
  total : ∑ S : Finset ι, w S = 1

/-! ### The line restriction `t ↦ g_w(z + t·1)` -/

/-- The univariate restriction of a generating polynomial to the line
`z + t·1`. -/
noncomputable def lineRestrict [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ)
    (z : ι → ℂ) : Polynomial ℂ :=
  ∑ S : Finset ι, Polynomial.C ((w S : ℂ)) * ∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))

theorem prodLin_monic (S : Finset ι) (z : ι → ℂ) :
    (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C (z i)

theorem prodLin_natDegree (S : Finset ι) (z : ι → ℂ) :
    (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).natDegree = S.card := by
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C (z i)]
  simp

theorem eval_lineRestrict [Fintype ι] [DecidableEq ι] (w : Finset ι → ℝ)
    (z : ι → ℂ) (t : ℂ) :
    (lineRestrict w z).eval t
      = eval (fun i => z i + t) ((genPoly w).map (algebraMap ℝ ℂ)) := by
  rw [eval_map_genPoly, lineRestrict, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp [add_comm]

/-- **Rank and mass make the restriction monic of degree `r`.**  Every set
carrying weight has size `r`, so every surviving factor contributes `t^r`; and
the weights sum to one, so the leading coefficients do. -/
theorem lineRestrict_coeff_rank [Fintype ι] [DecidableEq ι] {r : ℕ}
    {w : Finset ι → ℝ} (hw : FixedRankNormalized r w) (z : ι → ℂ) :
    (lineRestrict w z).coeff r = 1 := by
  rw [lineRestrict, Polynomial.finsetSum_coeff]
  have hterm : ∀ S : Finset ι,
      (Polynomial.C ((w S : ℂ)) * ∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff r
        = ((w S : ℂ)) := by
    intro S
    rw [Polynomial.coeff_C_mul]
    by_cases hS : S.card = r
    · have hm := prodLin_monic S z
      have : (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff r = 1 := by
        have := hm.coeff_natDegree
        rwa [prodLin_natDegree, hS] at this
      rw [this, mul_one]
    · rw [hw.supported S hS]
      simp
  rw [Finset.sum_congr rfl fun S _ => hterm S]
  rw [← Complex.ofReal_sum, hw.total]
  simp

theorem lineRestrict_natDegree_le [Fintype ι] [DecidableEq ι] {r : ℕ}
    {w : Finset ι → ℝ} (hw : FixedRankNormalized r w) (z : ι → ℂ) :
    (lineRestrict w z).natDegree ≤ r := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun S _ => ?_
  by_cases hS : S.card = r
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [prodLin_natDegree, hS]
  · rw [hw.supported S hS]
    simp

theorem lineRestrict_monic [Fintype ι] [DecidableEq ι] {r : ℕ}
    {w : Finset ι → ℝ} (hw : FixedRankNormalized r w) (z : ι → ℂ) :
    (lineRestrict w z).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one r (lineRestrict_natDegree_le hw z)
    (lineRestrict_coeff_rank hw z)

theorem lineRestrict_natDegree [Fintype ι] [DecidableEq ι] {r : ℕ}
    {w : Finset ι → ℝ} (hw : FixedRankNormalized r w) (z : ι → ℂ) :
    (lineRestrict w z).natDegree = r :=
  le_antisymm (lineRestrict_natDegree_le hw z)
    (Polynomial.le_natDegree_of_ne_zero (by rw [lineRestrict_coeff_rank hw z]; exact one_ne_zero))

/-- A stable generating polynomial has a line restriction with no root in the
**closed** upper half-plane: adding a `t` with `Im t ≥ 0` keeps every coordinate
strictly inside. -/
theorem lineRestrict_ne_zero [Fintype ι] [DecidableEq ι] {w : Finset ι → ℝ}
    (hs : IsRealStable (genPoly w)) {z : ι → ℂ} (hz : ∀ i, 0 < (z i).im)
    {t : ℂ} (ht : 0 ≤ t.im) : (lineRestrict w z).eval t ≠ 0 := by
  rw [eval_lineRestrict]
  refine hs (fun i => z i + t) fun i => ?_
  have := hz i
  simp only [Complex.add_im]
  linarith

/-! ### Continuity of roots, wrapped

The only place Mathlib's `exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` is
used.  Everything else in this file is bookkeeping around it. -/

/-- **Monic polynomials of a fixed degree with no root in the open upper
half-plane form a closed set.**  If the limit had a root there, continuity of
roots would put a root of every sufficiently close approximant nearby, hence
still in the upper half-plane. -/
theorem zeroFree_of_approx_monic {r : ℕ} {q : Polynomial ℂ}
    (hq : q.Monic) (hdeg : q.natDegree = r)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ q' : Polynomial ℂ, q'.Monic ∧ q'.natDegree = r ∧
      (∀ j, ‖q'.coeff j - q.coeff j‖ < ε) ∧ ∀ t : ℂ, 0 < t.im → q'.eval t ≠ 0)
    {a : ℂ} (ha : 0 < a.im) : q.eval a ≠ 0 := by
  intro hroot
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [hq.natDegree_eq_zero.mp hdeg] at hroot
    simp at hroot
  set M : ℝ := max ‖a‖ 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set c : ℝ := a.im / M with hc
  have hcpos : 0 < c := div_pos ha hMpos
  set ε : ℝ := c ^ r / (r + 1) with hε
  have hεpos : 0 < ε := div_pos (pow_pos hcpos r) (by positivity)
  obtain ⟨q', hq'm, hq'deg, hq'close, hq'zf⟩ := happrox ε hεpos
  obtain ⟨b, hb, hlt⟩ := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
    hεpos hroot hq hq'm (by rw [hq'deg, hdeg]) hq'close (IsAlgClosed.splits _)
  have hrne : ((r : ℝ)) ≠ 0 := by positivity
  have hkey : ((q.natDegree + 1 : ℝ) * ε) ^ ((q.natDegree : ℝ))⁻¹ * M = a.im := by
    rw [hdeg]
    have h1 : ((r : ℝ) + 1) * ε = c ^ r := by
      rw [hε]; field_simp
    rw [h1, ← Real.rpow_natCast c r, ← Real.rpow_mul hcpos.le,
      mul_inv_cancel₀ hrne, Real.rpow_one, hc, div_mul_cancel₀ _ (ne_of_gt hMpos)]
  rw [hkey] at hlt
  have him : |a.im - b.im| ≤ ‖a - b‖ := by
    have := Complex.abs_im_le_norm (a - b)
    simpa using this
  have hbim : 0 < b.im := by
    have hab : |a.im - b.im| < a.im := lt_of_le_of_lt him hlt
    have h2 := abs_lt.mp hab
    linarith [h2.1, h2.2]
  exact hq'zf b hbim (Polynomial.isRoot_of_mem_roots hb)

/-! ### The coefficient bound

Coefficients of the line restriction are linear in the weight, so a uniform
bound on the weights gives one on the coefficients — uniformly in the
coefficient index, since only finitely many indices are not identically zero. -/

/-- A bound on the coefficient sums that works for every index at once. -/
noncomputable def lineBound [Fintype ι] [DecidableEq ι] (z : ι → ℂ) : ℝ :=
  ∑ S : Finset ι, ∑ j ∈ Finset.range (Fintype.card ι + 1),
    ‖(∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j‖

theorem lineBound_nonneg [Fintype ι] [DecidableEq ι] (z : ι → ℂ) :
    0 ≤ lineBound z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sum_norm_coeff_le [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (j : ℕ) :
    ∑ S : Finset ι, ‖(∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j‖
      ≤ lineBound z := by
  by_cases hj : j ∈ Finset.range (Fintype.card ι + 1)
  · refine Finset.sum_le_sum fun S _ => ?_
    exact Finset.single_le_sum (f := fun j' =>
      ‖(∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j'‖)
      (fun _ _ => norm_nonneg _) hj
  · have hzero : ∀ S : Finset ι,
        (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j = 0 := by
      intro S
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [prodLin_natDegree]
      have hcard : S.card ≤ Fintype.card ι := Finset.card_le_univ S
      simp only [Finset.mem_range, not_lt] at hj
      omega
    simp only [hzero, norm_zero, Finset.sum_const_zero]
    exact lineBound_nonneg z

theorem lineRestrict_coeff_sub_le [Fintype ι] [DecidableEq ι]
    {w w' : Finset ι → ℝ} {z : ι → ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ S, |w' S - w S| ≤ δ) (j : ℕ) :
    ‖(lineRestrict w' z).coeff j - (lineRestrict w z).coeff j‖ ≤ δ * lineBound z := by
  have hsub : (lineRestrict w' z).coeff j - (lineRestrict w z).coeff j
      = ∑ S : Finset ι, ((w' S - w S : ℝ) : ℂ) *
          (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j := by
    rw [lineRestrict, lineRestrict, Polynomial.finsetSum_coeff,
      Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    push_cast
    ring
  rw [hsub]
  have hstep1 : ‖∑ S : Finset ι, ((w' S - w S : ℝ) : ℂ) *
      (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j‖
      ≤ ∑ S : Finset ι, |w' S - w S| *
        ‖(∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))).coeff j‖ := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans hstep1 ?_
  refine le_trans (Finset.sum_le_sum fun S _ =>
    mul_le_mul_of_nonneg_right (hδ S) (norm_nonneg _)) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_norm_coeff_le z j) hδ0

/-! ### Stability at fixed rank passes to the limit -/

/-- **The adapter.**  A fixed-rank normalized weight approximated by fixed-rank
normalized *stable* weights is itself stable.

Both invariants of the approximants are used: the rank makes the line
restrictions monic of a common degree, and normalization makes them monic at
all. -/
theorem isRealStable_of_approx [Fintype ι] [DecidableEq ι] {r : ℕ}
    {w : Finset ι → ℝ} (hw : FixedRankNormalized r w)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ w', FixedRankNormalized r w' ∧
      IsRealStable (genPoly w') ∧ ∀ S, |w' S - w S| ≤ δ) :
    IsRealStable (genPoly w) := by
  intro z hz
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- no variables: the generating polynomial is the constant `∑ w = 1`
    haveI := hι
    have h1 : eval z ((genPoly w).map (algebraMap ℝ ℂ)) = ((1 : ℝ) : ℂ) := by
      rw [eval_map_genPoly, ← hw.total, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun S _ => by simp [Finset.eq_empty_of_isEmpty S]
    rw [h1]
    simp
  -- move the evaluation point strictly inside the half-plane
  haveI : Nonempty ι := hι
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) (fun i => (z i).im) Finset.univ_nonempty
  set ε₀ : ℝ := (z i₀).im with hε₀
  have hε₀pos : 0 < ε₀ := hz i₀
  have hε₀le : ∀ i, ε₀ ≤ (z i).im := fun i => hmin i (Finset.mem_univ i)
  set s : ℝ := ε₀ / 2 with hs
  have hspos : 0 < s := by rw [hs]; linarith
  set z' : ι → ℂ := fun i => z i - Complex.I * (s : ℂ) with hz'
  have hz'im : ∀ i, 0 < (z' i).im := by
    intro i
    have := hε₀le i
    simp only [hz', Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [hs]
    linarith
  -- the point of interest sits at `t = i·s`
  have hpoint : ∀ i, z' i + Complex.I * (s : ℂ) = z i := by
    intro i
    rw [hz']
    ring
  have harg : (fun i => z' i + Complex.I * (s : ℂ)) = z := funext hpoint
  have heval : (lineRestrict w z').eval (Complex.I * (s : ℂ))
      = eval z ((genPoly w).map (algebraMap ℝ ℂ)) := by
    rw [eval_lineRestrict, harg]
  rw [← heval]
  refine zeroFree_of_approx_monic (lineRestrict_monic hw z')
    (lineRestrict_natDegree hw z') (fun ε hε => ?_) ?_
  · -- transfer the closeness from the weights to the coefficients
    have hBnn := lineBound_nonneg z'
    set δ : ℝ := ε / (lineBound z' + 1) with hδdef
    have hδpos : 0 < δ := div_pos hε (by linarith)
    obtain ⟨w', hw'rank, hw'stable, hw'close⟩ := happrox δ hδpos
    refine ⟨lineRestrict w' z', lineRestrict_monic hw'rank z',
      lineRestrict_natDegree hw'rank z', fun j => ?_, fun t ht => ?_⟩
    · refine lt_of_le_of_lt (lineRestrict_coeff_sub_le (le_of_lt hδpos) hw'close j) ?_
      rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    · exact lineRestrict_ne_zero hw'stable hz'im (le_of_lt ht)
  · simp [Complex.mul_im, hspos]

/-! ### The property that travels to the limit -/

variable {n : ℕ}

open Classical in
/-- **Fixed rank, normalization and stability together are limit-closed.**

The conjunction is essential.  `IsRealStable (genPoly ·)` on its own is not a
sound property to close under limits: a sequence of nonzero stable polynomials
can converge to zero, and `LimitClosed`'s interface would hand
`isRealStable_of_approx` approximants with no common rank — precisely the
hypothesis the line restriction consumes.  Carried in the property, the
invariant arrives with them. -/
theorem limitClosed_fixedRankStable (r : ℕ) :
    LimitClosed (fun f : Finset (Sym2 (Fin n)) → ℝ =>
      FixedRankNormalized r f ∧ IsRealStable (genPoly f)) := by
  intro f hf
  -- the invariants first, each a closed condition
  have hnonneg : ∀ S, 0 ≤ f S := by
    intro S
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨g, hg, hclose⟩ := hf δ hδ
    have h1 := hg.1.nonneg S
    have h2 := abs_le.mp (hclose S)
    linarith [h2.1]
  have hsupp : ∀ S, S.card ≠ r → f S = 0 := by
    intro S hS
    by_contra hne
    have habs : 0 < |f S| := abs_pos.mpr hne
    obtain ⟨g, hg, hclose⟩ := hf (|f S| / 2) (by linarith)
    have hgz : g S = 0 := hg.1.supported S hS
    have hc := hclose S
    rw [hgz, zero_sub, abs_neg] at hc
    linarith
  have htotal : ∑ S : Finset (Sym2 (Fin n)), f S = 1 := by
    have hcl : LimitClosed (fun v : Finset (Sym2 (Fin n)) → ℝ =>
        (∑ S, v S * 1) ≤ 1 ∧ (1 : ℝ) ≤ ∑ S, v S * 1) :=
      (limitClosed_le (continuous_probSum _) continuous_const).and
        (limitClosed_le continuous_const (continuous_probSum _))
    have := hcl f fun δ hδ => by
      obtain ⟨g, hg, hclose⟩ := hf δ hδ
      refine ⟨g, ?_, hclose⟩
      have := hg.1.total
      simp only [mul_one]
      exact ⟨le_of_eq this, le_of_eq this.symm⟩
    simp only [mul_one] at this
    exact le_antisymm this.1 this.2
  have hrank : FixedRankNormalized r f := ⟨hnonneg, hsupp, htotal⟩
  refine ⟨hrank, isRealStable_of_approx hrank fun δ hδ => ?_⟩
  obtain ⟨g, hg, hclose⟩ := hf δ hδ
  exact ⟨g, hg.1, hg.2, hclose⟩

/-- **A tree distribution is fixed-rank normalized of rank `n − 1`.**  Its
support consists of spanning trees, which have `n − 1` edges, and it is a
probability vector — so the invariant the limit argument needs is free, and
callers never have to supply it. -/
theorem TreeDist.fixedRankNormalized {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) :
    FixedRankNormalized (n - 1) μ.prob where
  nonneg := μ.prob_nonneg
  supported := fun S hS => by
    by_contra hne
    exact hS (μ.support_spanningTree S hne).2.1
  total := μ.total

/-- The export at an arbitrary rank: if every λ-uniform approximant is a
fixed-rank normalized weight with a stable generating polynomial, so is the
limit. -/
theorem IsMaxEntropyLimit.realStable_of_fixedRank {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (r : ℕ) (h : IsMaxEntropyLimit μ)
    (hlam : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν →
      FixedRankNormalized r ν.prob ∧ IsRealStable (genPoly ν.prob)) :
    FixedRankNormalized r μ.prob ∧ IsRealStable (genPoly μ.prob) :=
  h.holds (limitClosed_fixedRankStable r) hlam

/-- **The export.**  λ-uniform approximants only have to be *stable*: rank and
normalization come from `TreeDist` itself, at rank `n − 1`.

That the λ-uniform distributions are stable is the weighted matrix-tree /
Cauchy–Binet input, separately scoped. -/
theorem IsMaxEntropyLimit.realStable {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ)
    (hlam : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν →
      IsRealStable (genPoly ν.prob)) :
    IsRealStable (genPoly μ.prob) :=
  (h.realStable_of_fixedRank (n - 1) fun ν hν => ⟨ν.fixedRankNormalized, hlam ν hν⟩).2

end TSPGap

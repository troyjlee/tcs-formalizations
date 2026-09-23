/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FederMihail
import TSPGap.Poisson

/-!
# Rank sequences I: the rank polynomial is real-rooted

For a fixed-rank weight `w` with stable generating polynomial, the **rank
polynomial** along any coordinate set `F` — whose `k`-th coefficient is the
mass of `|S ∩ F| = k` — has only real roots.

⚠️ **No boundary specialization.**  Setting the off-`F` variables to `1`
lands on the boundary of the half-plane, where stability says nothing
directly, and repairing that in general is multivariate Hurwitz.  The route
here never takes that step.  A root `t` with `Im t > 0` makes the generating
polynomial vanish at the *boundary* point (`t` on `F`, `1` off `F`); scaling
every coordinate by `λ = 1 + iδ` multiplies that value by `λ^r` — fixed rank
makes the generating polynomial homogeneous — and moves the point so that
**every** coordinate lies in the open upper half-plane: `λ` itself is
interior, and `Im(λt) = Im t + δ·Re t > 0` for small `δ`.  The zero
survives, contradicting stability.

Even the homogeneity is not Mathlib API: `eval_smul_map_genPoly` is one
rearrangement of the evaluation sum, using `FixedRankWeight` termwise.

* `rankPoly w F` — `∑_S w(S) · X^{|S∩F|}`; `coeff_rankPoly` identifies its
  coefficients with the rank masses `weightMass w (fun S => (S ∩ F).card = k)`.
* `eval_indicator_map_genPoly` — the boundary evaluation identity.
* `eval_smul_map_genPoly` — the scaling identity `p(λ·x) = λ^r · p(x)`.
* `aeval_rankPoly_ne_zero_of_im_pos` — no root in the open upper half-plane.
* `im_eq_zero_of_aeval_rankPoly` — by conjugation, every complex root is
  real.

Next (increment 2): nonnegative coefficients force the roots `≤ 0`, giving
the Bernoulli factorization and the bridge to `Bernoulli.probCount`.
-/

namespace TSPGap

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **rank polynomial** of `w` along `F`: the coefficient of `X^k` is
the mass `w` puts on `|S ∩ F| = k`. -/
noncomputable def rankPoly (w : Finset ι → ℝ) (F : Finset ι) : Polynomial ℝ :=
  ∑ S : Finset ι, Polynomial.C (w S) * Polynomial.X ^ (S ∩ F).card

/-- The coefficients of the rank polynomial are the rank masses. -/
theorem coeff_rankPoly (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ) :
    (rankPoly w F).coeff k = weightMass w fun S => (S ∩ F).card = k := by
  classical
  rw [rankPoly, Polynomial.finsetSum_coeff, weightMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : (S ∩ F).card = k
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg fun hc => h hc.symm, if_neg h, mul_zero]

theorem coeff_rankPoly_nonneg {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) (k : ℕ) : 0 ≤ (rankPoly w F).coeff k := by
  rw [coeff_rankPoly]
  exact weightMass_nonneg hnn _

theorem eval₂_rankPoly {R : Type*} [CommRing R] (φ : ℝ →+* R)
    (w : Finset ι → ℝ) (F : Finset ι) (t : R) :
    (rankPoly w F).eval₂ φ t = ∑ S : Finset ι, φ (w S) * t ^ (S ∩ F).card := by
  rw [rankPoly, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]

/-- At `1` the rank polynomial returns the total mass — the normalization
increment 2 will feed to the Bernoulli factorization. -/
theorem eval_one_rankPoly (w : Finset ι → ℝ) (F : Finset ι) :
    (rankPoly w F).eval 1 = totalMass w := by
  rw [show (rankPoly w F).eval 1 = (rankPoly w F).eval₂ (RingHom.id ℝ) 1 from rfl,
    eval₂_rankPoly, totalMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp

/-- **The boundary evaluation identity**: the generating polynomial at
(`t` on `F`, `1` off `F`) is the rank polynomial at `t`. -/
theorem eval_indicator_map_genPoly (w : Finset ι → ℝ) (F : Finset ι) (t : ℂ) :
    MvPolynomial.eval (fun i => if i ∈ F then t else 1)
        ((genPoly w).map (algebraMap ℝ ℂ))
      = Polynomial.aeval t (rankPoly w F) := by
  rw [Polynomial.aeval_def, eval_map_genPoly, eval₂_rankPoly]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [Finset.prod_ite_mem S F fun _ => t, Finset.prod_const]

/-- **The scaling identity.**  A fixed-rank weight has a homogeneous
generating polynomial, termwise: every surviving `S` has `|S| = r`. -/
theorem eval_smul_map_genPoly {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (lam : ℂ) (x : ι → ℂ) :
    MvPolynomial.eval (fun i => lam * x i) ((genPoly w).map (algebraMap ℝ ℂ))
      = lam ^ r * MvPolynomial.eval x ((genPoly w).map (algebraMap ℝ ℂ)) := by
  rw [eval_map_genPoly, eval_map_genPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · rw [Finset.prod_mul_distrib, Finset.prod_const, hr S h0]
    ring

/-- **The rank polynomial has no root in the open upper half-plane.**  The
root gives a zero of the generating polynomial at the boundary point (`t` on
`F`, `1` off `F`); the tilt `λ = 1 + iδ`, `δ = Im t / (2(|Re t| + 1))`,
moves it to a fully interior zero, contradicting stability. -/
theorem aeval_rankPoly_ne_zero_of_im_pos {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (F : Finset ι) {t : ℂ} (ht : 0 < t.im) :
    Polynomial.aeval t (rankPoly w F) ≠ 0 := by
  intro hzero
  have hx : MvPolynomial.eval (fun i => if i ∈ F then t else 1)
      ((genPoly w).map (algebraMap ℝ ℂ)) = 0 := by
    rw [eval_indicator_map_genPoly, hzero]
  set a : ℝ := |t.re| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set δ : ℝ := t.im / (2 * (a + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set lam : ℂ := 1 + (δ : ℂ) * Complex.I with hlam
  have hlam_re : lam.re = 1 := by simp [hlam]
  have hlam_im : lam.im = δ := by simp [hlam]
  -- the tilted first coordinate stays interior
  have hkey : 0 < t.im + δ * t.re := by
    have hml : δ * (-a) ≤ δ * t.re :=
      mul_le_mul_of_nonneg_left (neg_abs_le t.re) hδ0.le
    have hda : 0 ≤ δ * a := mul_nonneg hδ0.le ha0
    have h1 : δ * (2 * (a + 1)) = t.im := by
      rw [hδ]
      field_simp
    nlinarith [hml, hda, h1, hδ0]
  -- every coordinate of the tilted point is interior
  have him : ∀ i : ι, 0 < (lam * (if i ∈ F then t else 1)).im := by
    intro i
    by_cases hi : i ∈ F
    · rw [if_pos hi, Complex.mul_im, hlam_re, hlam_im, one_mul]
      linarith [hkey]
    · rw [if_neg hi, mul_one, hlam_im]
      exact hδ0
  refine hst (fun i => lam * (if i ∈ F then t else 1)) him ?_
  have hsc := eval_smul_map_genPoly (w := w) hr lam
    (fun j => if j ∈ F then t else 1)
  rw [hx, mul_zero] at hsc
  exact hsc

/-- **Every complex root of the rank polynomial is real**: the lower
half-plane is excluded by conjugation, since the coefficients are real. -/
theorem im_eq_zero_of_aeval_rankPoly {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (F : Finset ι) {t : ℂ} (hroot : Polynomial.aeval t (rankPoly w F) = 0) :
    t.im = 0 := by
  by_contra him
  rcases lt_or_gt_of_ne him with hlt | hgt
  · have hconj : Polynomial.aeval ((starRingEnd ℂ) t) (rankPoly w F) = 0 := by
      rw [Polynomial.aeval_conj, hroot, map_zero]
    exact aeval_rankPoly_ne_zero_of_im_pos hst hr F
      (t := (starRingEnd ℂ) t) (by simpa using neg_pos.mpr hlt) hconj
  · exact aeval_rankPoly_ne_zero_of_im_pos hst hr F hgt hroot

/-! ### Increment 2: the Bernoulli factorization

Real-rootedness plus nonnegative coefficients force every root nonpositive,
so the rank polynomial factors into Bernoulli generating factors
`C q · X + C (1 − q)` with `q = 1/(1 − root) ∈ (0, 1]`, and the coefficient
bridge `Bernoulli.probCount_eq_coeff` reads the rank law off the product.

The factorization comes back from `ℂ` with no splits-transfer lemma: factor
the complexification with `Splits.eq_prod_roots`, rewrite each root as real,
and pull the identity through the injective coefficient map. -/

/-- The Bernoulli law reads off the coefficients of the generating product
`∏ (C qᵢ · X + C (1 − qᵢ))`.  `Finset.prod_add` expands the product over
subsets, and the subsets of size `k` are exactly `probCount`'s sum. -/
theorem Bernoulli.probCount_eq_coeff {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : κ → ℝ) (k : ℕ) :
    Bernoulli.probCount q k
      = (∏ i : κ,
          (Polynomial.C (q i) * Polynomial.X + Polynomial.C (1 - q i))).coeff k := by
  classical
  rw [Finset.prod_add, Polynomial.finsetSum_coeff, Bernoulli.probCount_def,
    Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ∏ i ∈ t, Polynomial.C (q i) * Polynomial.X
      = Polynomial.C (∏ i ∈ t, q i) * Polynomial.X ^ t.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
  have h2 : ∏ i ∈ Finset.univ \ t, Polynomial.C (1 - q i)
      = Polynomial.C (∏ i ∈ Finset.univ \ t, (1 - q i)) :=
    (map_prod _ _ _).symm
  rw [h1, h2, Bernoulli.atomProb,
    show Polynomial.C (∏ i ∈ t, q i) * Polynomial.X ^ t.card
        * Polynomial.C (∏ i ∈ Finset.univ \ t, (1 - q i))
      = Polynomial.C ((∏ i ∈ t, q i) * ∏ i ∈ Finset.univ \ t, (1 - q i))
        * Polynomial.X ^ t.card by rw [map_mul]; ring,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : t.card = k
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg fun hc => h hc.symm, mul_zero]

/-- A nonnegative weight of positive total mass has a rank polynomial that
is strictly positive on the positive axis — so no positive root. -/
theorem rankPoly_pos_of_pos {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : 0 < totalMass w) (F : Finset ι) {x : ℝ} (hx : 0 < x) :
    0 < (rankPoly w F).eval x := by
  classical
  obtain ⟨S₀, -, hS₀⟩ := Finset.exists_lt_of_sum_lt
    (f := fun _ : Finset ι => (0 : ℝ)) (g := w)
    (by simpa [totalMass] using htot)
  rw [show (rankPoly w F).eval x = (rankPoly w F).eval₂ (RingHom.id ℝ) x from rfl,
    eval₂_rankPoly]
  refine Finset.sum_pos' (fun S _ => ?_) ⟨S₀, Finset.mem_univ S₀, ?_⟩
  · exact mul_nonneg (hnn S) (pow_nonneg hx.le _)
  · exact mul_pos hS₀ (pow_pos hx _)

/-- **The real factorization, from `ℂ` and back.**  A real polynomial whose
complex roots are all real is a constant times a product of real linear
factors: factor the complexification, rewrite each root as real, and cancel
the injective coefficient map. -/
theorem exists_factorization_of_roots_real {p : Polynomial ℝ}
    (hroots : ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) :
    ∃ s : Multiset ℝ,
      p = Polynomial.C p.leadingCoeff
        * (s.map fun x => Polynomial.X - Polynomial.C x).prod := by
  classical
  have hsp : (p.map (algebraMap ℝ ℂ)).Splits := IsAlgClosed.splits _
  refine ⟨(p.map (algebraMap ℝ ℂ)).roots.map Complex.re, ?_⟩
  have hz : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ((z.re : ℝ) : ℂ) = z := by
    intro z hzr
    have hzero : Polynomial.aeval z p = 0 := by
      have h0 := (Polynomial.mem_roots'.mp hzr).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at h0
    exact Complex.ext (Complex.ofReal_re _) (by simp [hroots z hzero])
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  have hRHS : (Polynomial.C p.leadingCoeff
      * (((p.map (algebraMap ℝ ℂ)).roots.map Complex.re).map
          fun x => Polynomial.X - Polynomial.C x).prod).map (algebraMap ℝ ℂ)
      = Polynomial.C ((algebraMap ℝ ℂ) p.leadingCoeff)
        * ((p.map (algebraMap ℝ ℂ)).roots.map
            fun z => Polynomial.X - Polynomial.C z).prod := by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod,
      Multiset.map_map, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun z hzr => ?_)
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    rw [show (algebraMap ℝ ℂ) z.re = ((z.re : ℝ) : ℂ) from rfl, hz z hzr]
  rw [hRHS, ← Polynomial.leadingCoeff_map]
  exact hsp.eq_prod_roots

/-- A member of the factorization multiset is a root, so positivity on the
positive axis forces it nonpositive. -/
theorem nonpos_of_mem_factorization {p : Polynomial ℝ} {s : Multiset ℝ}
    (hfact : p = Polynomial.C p.leadingCoeff
      * (s.map fun x => Polynomial.X - Polynomial.C x).prod)
    (hpos : ∀ x : ℝ, 0 < x → 0 < p.eval x) {x : ℝ} (hx : x ∈ s) : x ≤ 0 := by
  by_contra hc
  have hxpos : 0 < x := lt_of_not_ge hc
  have hdvd : Polynomial.X - Polynomial.C x ∣ p := by
    rw [hfact]
    exact (Multiset.dvd_prod (Multiset.mem_map_of_mem _ hx)).mul_left _
  exact (hpos x hxpos).ne' (Polynomial.dvd_iff_isRoot.mp hdvd)

/-- Products over the positions of a list are products over the list. -/
theorem prod_fin_get_eq {α M : Type*} [CommMonoid M] (l : List α) (f : α → M) :
    ∏ j : Fin l.length, f (l.get j) = (l.map f).prod := by
  rw [← List.prod_ofFn, ← Function.comp_def f l.get, ← List.map_ofFn,
    List.ofFn_get]

/-- ... and products over a multiset are products over the positions of its
list. -/
theorem multiset_prod_map_eq_prod_fin {α M : Type*} [CommMonoid M]
    (s : Multiset α) (f : α → M) :
    (s.map f).prod = ∏ j : Fin s.toList.length, f (s.toList.get j) := by
  conv_lhs => rw [← Multiset.coe_toList s]
  rw [Multiset.map_coe, Multiset.prod_coe, ← prod_fin_get_eq]

/-- **The Bernoulli rank law.**  For a normalized, nonnegative, fixed-rank
weight with stable generating polynomial, the rank sequence along any `F`
is the law of a sum of independent Bernoullis: with roots `−λⱼ ≤ 0` of the
rank polynomial, the success probabilities are `qⱼ = 1/(1 + λⱼ) ∈ (0, 1]`,
and the normalization `∑ w = 1` identifies the leading coefficient with
`∏ qⱼ`. -/
theorem exists_bernoulli_rank_law {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι) :
    ∃ (m : ℕ) (q : Fin m → ℝ), (∀ j, 0 < q j ∧ q j ≤ 1) ∧
      ∀ k : ℕ, weightMass w (fun S => (S ∩ F).card = k)
        = Bernoulli.probCount q k := by
  classical
  obtain ⟨s, hfact⟩ := exists_factorization_of_roots_real
    (p := rankPoly w F) fun z hz => im_eq_zero_of_aeval_rankPoly hst hr F hz
  have hpos : ∀ x : ℝ, 0 < x → 0 < (rankPoly w F).eval x := fun x hx =>
    rankPoly_pos_of_pos hnn (by rw [htot]; exact one_pos) F hx
  have hs_nonpos : ∀ x ∈ s, x ≤ 0 := fun x hx =>
    nonpos_of_mem_factorization hfact hpos hx
  have hfac_pos : ∀ x ∈ s, (0 : ℝ) < 1 - x := fun x hx => by
    have := hs_nonpos x hx
    linarith
  -- the normalization at `1`
  have hone : (rankPoly w F).eval 1 = 1 := by rw [eval_one_rankPoly, htot]
  have heval1 : (rankPoly w F).eval 1
      = (rankPoly w F).leadingCoeff * ((s.map fun x => (1 : ℝ) - x)).prod := by
    conv_lhs => rw [hfact]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  have hprod_pos : 0 < ((s.map fun x => (1 : ℝ) - x)).prod := by
    refine Multiset.prod_pos fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    exact hfac_pos x hx
  have hc : (rankPoly w F).leadingCoeff
      * ((s.map fun x => (1 : ℝ) - x)).prod = 1 := by
    rw [← heval1, hone]
  -- the product of the success probabilities is the leading coefficient
  have hq : (∏ j : Fin s.toList.length, 1 / (1 - s.toList.get j))
      = (rankPoly w F).leadingCoeff := by
    have hQP : (∏ j : Fin s.toList.length, 1 / (1 - s.toList.get j))
        * ((s.map fun x => (1 : ℝ) - x)).prod = 1 := by
      rw [← multiset_prod_map_eq_prod_fin s fun x => 1 / (1 - x),
        ← Multiset.prod_map_mul,
        Multiset.map_congr rfl fun x hx =>
          div_mul_cancel₀ (1 : ℝ) (hfac_pos x hx).ne']
      simp
    exact mul_right_cancel₀ hprod_pos.ne' (hQP.trans hc.symm)
  -- the success probabilities, listed
  refine ⟨s.toList.length, fun j => 1 / (1 - s.toList.get j), fun j => ?_,
    fun k => ?_⟩
  · have hmem : s.toList.get j ∈ s :=
      Multiset.mem_toList.mp (s.toList.get_mem j)
    refine ⟨div_pos one_pos (hfac_pos _ hmem), ?_⟩
    have h2 : (1 : ℝ) ≤ 1 - s.toList.get j := by
      linarith [hs_nonpos _ hmem]
    exact (div_le_one (hfac_pos _ hmem)).mpr h2
  · rw [← coeff_rankPoly, Bernoulli.probCount_eq_coeff]
    congr 1
    symm
    -- each Bernoulli factor is `q · (X − root)`
    have hfac : ∀ j : Fin s.toList.length,
        Polynomial.C (1 / (1 - s.toList.get j)) * Polynomial.X
            + Polynomial.C (1 - 1 / (1 - s.toList.get j))
          = Polynomial.C (1 / (1 - s.toList.get j))
            * (Polynomial.X - Polynomial.C (s.toList.get j)) := by
      intro j
      have hne : (1 : ℝ) - s.toList.get j ≠ 0 :=
        (hfac_pos _ (Multiset.mem_toList.mp (s.toList.get_mem j))).ne'
      have hval : 1 - 1 / (1 - s.toList.get j)
          = -(1 / (1 - s.toList.get j) * s.toList.get j) := by
        field_simp
        ring
      rw [hval, map_neg, ← sub_eq_add_neg, mul_sub, ← Polynomial.C_mul]
    calc ∏ j : Fin s.toList.length,
          (Polynomial.C (1 / (1 - s.toList.get j)) * Polynomial.X
            + Polynomial.C (1 - 1 / (1 - s.toList.get j)))
        = ∏ j : Fin s.toList.length,
            Polynomial.C (1 / (1 - s.toList.get j))
              * (Polynomial.X - Polynomial.C (s.toList.get j)) :=
          Finset.prod_congr rfl fun j _ => hfac j
      _ = (∏ j : Fin s.toList.length,
              Polynomial.C (1 / (1 - s.toList.get j)))
            * ∏ j : Fin s.toList.length,
                (Polynomial.X - Polynomial.C (s.toList.get j)) :=
          Finset.prod_mul_distrib
      _ = Polynomial.C (rankPoly w F).leadingCoeff
            * (s.map fun x => Polynomial.X - Polynomial.C x).prod := by
          rw [← map_prod, hq,
            ← multiset_prod_map_eq_prod_fin s
              fun x => Polynomial.X - Polynomial.C x]
      _ = rankPoly w F := hfact.symm

/-- **The Bernoulli rank law at the max-entropy limit**: for any edge set
`F`, the number of tree edges in `F` is distributed as a sum of independent
Bernoullis.  Hypothesis-free beyond the limit itself: stability is
`treeRealStable`, rank and normalization come with the distribution. -/
theorem IsMaxEntropyLimit.exists_bernoulli_rank_law {n : ℕ}
    {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x} (h : IsMaxEntropyLimit μ)
    (F : Finset (Sym2 (Fin n))) :
    ∃ (m : ℕ) (q : Fin m → ℝ), (∀ j, 0 < q j ∧ q j ≤ 1) ∧
      ∀ k : ℕ, μ.probEvent (fun T => (T ∩ F).card = k)
        = Bernoulli.probCount q k := by
  obtain ⟨m, q, hq, hlaw⟩ := _root_.TSPGap.exists_bernoulli_rank_law
    h.treeRealStable μ.fixedRankWeight μ.weightNonneg (totalMass_treeDist μ) F
  refine ⟨m, q, hq, fun k => ?_⟩
  rw [← weightMass_treeDist]
  exact hlaw k

end TSPGap


/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BernoulliCount
import TSPGap.BinomialPoisson

/-!
# Poisson lower bounds for Bernoulli sums (KKO21 Lemmas 2.21 and 2.22)

**KKO21 Lemma 2.21**: if `X` is a sum of independent Bernoullis with mean
`p` and `k` is an integer with `k - 1 < p < k + 1`, then

  `P[X = k] ≥ min_ℓ Poi(p - ℓ, k - ℓ) · (1 - (p-ℓ)/(k-ℓ+1))^{(p-k)⁺}`,

the minimum over integers `0 ≤ ℓ ≤ min(p, k)`.  We state it in the
equivalent existential form (`poi_le_probCount`): some `ℓ` realizes the
bound.

The proof pipeline:

* `exists_min_three_valued` (Hoeffding, KKO21 Thm 2.15) reduces to a
  three-valued vector: `ℓ` sure successes, some sure failures, and `r`
  i.i.d. `x`-Bernoullis;
* `probCount_threeValued` evaluates `P[X = k]` there as the shifted
  binomial mass `C(r, k-ℓ) x^{k-ℓ} (1-x)^{r-(k-ℓ)}`;
* `poi_mul_le_choose_mul` lower-bounds the binomial mass by the Poisson
  expression, via Fact 2.20 (`exp_neg_le_prod_mul_pow`).

## A repair to the paper's proof

For `k < p < k + 1` KKO invoke Fact 2.20 with the integer exponent `n - k`,
but its hypothesis `k - 1 ≤ p ≤ k` fails there — and indeed the cited
inequality `∏(1-i/n)(1-p/n)^{n-k} ≥ e^{-p}` is **false** for `n` close to
`p` (e.g. `k = 1`, `p = 1.9`, `n = 2`).  We instead prove
(`one_sub_div_rpow_mul_exp_le`) that `p ↦ (1 - p/t)^{t-p} e^p` is monotone
— reducing to `log x ≥ 1 - 1/x` — which upgrades Fact 2.20 at the endpoint
`p = k` to the real-exponent form
`∏(1-i/n)(1-p/n)^{n-p} ≥ e^{-p}` valid for all `k ≤ p < n`
(`exp_neg_le_prod_mul_rpow`).  Splitting
`(1-p/n)^{n-k} = (1-p/n)^{n-p}(1-p/n)^{p-k}` and shrinking the base
`1 - p/n ≥ 1 - p/(k+1)` then yields the corrected bound, with the same
statement as the paper's.

## Lemma 2.22 (the tail bound)

**KKO21 Lemma 2.22**: with `k = ⌈p⌉`,
`P[X ≥ k] ≥ min_ℓ Poi(p - ℓ, ≥ k - ℓ)` over integers `0 ≤ ℓ ≤ p`.  We prove
it (`poi_tail_le_probGE`, existential form) from the same Hoeffding
reduction together with `TSPGap.binomial_lowerTail_le_shifted_poisson`: a
binomial lower tail with threshold below the mean is dominated by a shifted
Poisson lower tail.  That statement is [Hoe56, Theorem 4] pushed
to the binomial→Poisson limit — the analytic heart of the paper's proof,
which cites Hoe56 for it.  It was a declared black box until 2026-09-11 and is
proved in `BinomialPoisson.lean`.  Note the shift is essential: the unshifted
comparison `P[Bin ≤ j] ≤ P[Poi ≤ j]` at equal means is false
(`Bin(2, 0.51)` at `j = 1`: `0.7399 > 0.7284`), so no per-configuration
argument à la Lemma 2.21 can work.
-/

namespace TSPGap
namespace Bernoulli

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Elementary analytic inequalities -/

/-- `k^k ≤ k! · e^{k-1}` (a weak Stirling bound), by induction from
`(m+1)^m ≤ e·m^m`. -/
theorem pow_self_le_factorial_mul_exp (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ k ≤ (k.factorial : ℝ) * Real.exp ((k : ℝ) - 1) := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have ihm := ih hm
    have hstep := succ_pow_le_exp_mul_pow m hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    have h1 : ((m : ℝ) + 1) ^ (m + 1) = ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ m := by
      rw [pow_succ]; ring
    have h2 : ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ m
        ≤ ((m : ℝ) + 1) * (Real.exp 1 * (m : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hstep hm0
    have h3 : ((m : ℝ) + 1) * (Real.exp 1 * (m : ℝ) ^ m)
        ≤ ((m : ℝ) + 1) * (Real.exp 1 * ((m.factorial : ℝ)
            * Real.exp ((m : ℝ) - 1))) := by
      refine mul_le_mul_of_nonneg_left ?_ hm0
      exact mul_le_mul_of_nonneg_left ihm (Real.exp_pos 1).le
    have h4 : Real.exp 1 * Real.exp ((m : ℝ) - 1) = Real.exp ((m : ℝ) + 1 - 1) := by
      rw [← Real.exp_add]
      ring_nf
    calc ((m : ℝ) + 1) ^ (m + 1)
        = ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ m := h1
      _ ≤ ((m : ℝ) + 1) * (Real.exp 1 * ((m.factorial : ℝ)
            * Real.exp ((m : ℝ) - 1))) := le_trans h2 h3
      _ = ((m : ℝ) + 1) * (m.factorial : ℝ)
            * (Real.exp 1 * Real.exp ((m : ℝ) - 1)) := by ring
      _ = ((m : ℝ) + 1) * (m.factorial : ℝ) * Real.exp ((m : ℝ) + 1 - 1) := by
          rw [h4]

/-- Monotonicity of `p ↦ (1 - p/t)^{t-p} e^p` on `[0, t)` (real exponents);
reduces to `log x ≥ 1 - 1/x`.  This repairs the out-of-range Fact 2.20
application in KKO21's proof of Lemma 2.21. -/
theorem one_sub_div_rpow_mul_exp_le {t a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbt : b < t) :
    (1 - a / t) ^ (t - a) * Real.exp a ≤ (1 - b / t) ^ (t - b) * Real.exp b := by
  have ht : 0 < t := lt_of_le_of_lt (h0.trans hab) hbt
  have hu : 0 < t - a := by linarith [hab.trans_lt hbt]
  have hv : 0 < t - b := by linarith
  have haa : 0 < 1 - a / t := by
    rw [sub_pos, div_lt_one ht]
    linarith
  have hba : 0 < 1 - b / t := by
    rw [sub_pos, div_lt_one ht]
    exact hbt
  rw [Real.rpow_def_of_pos haa, Real.rpow_def_of_pos hba, ← Real.exp_add,
    ← Real.exp_add, Real.exp_le_exp]
  have hlog_a : Real.log (1 - a / t) = Real.log (t - a) - Real.log t := by
    rw [show 1 - a / t = (t - a) / t by field_simp, Real.log_div hu.ne' ht.ne']
  have hlog_b : Real.log (1 - b / t) = Real.log (t - b) - Real.log t := by
    rw [show 1 - b / t = (t - b) / t by field_simp, Real.log_div hv.ne' ht.ne']
  rw [hlog_a, hlog_b]
  have hut : t - a ≤ t := by linarith
  have hk1 : ((t - a) - (t - b)) * Real.log (t - a)
      ≤ ((t - a) - (t - b)) * Real.log t :=
    mul_le_mul_of_nonneg_left ((Real.log_le_log_iff hu ht).mpr hut)
      (by linarith)
  have hk2 : (t - b) - (t - a) ≤ (t - b) * (Real.log (t - b) - Real.log (t - a)) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (t - a) / (t - b) by positivity)
    rw [Real.log_div hu.ne' hv.ne'] at h
    have h3 := mul_le_mul_of_nonneg_left h hv.le
    have h4 : (t - b) * ((t - a) / (t - b) - 1) = (t - a) - (t - b) := by
      field_simp
    nlinarith [h3, h4]
  nlinarith [hk1, hk2]

/-- Nonnegativity of the falling-factorial product `∏_{i=1}^{k-1}(1 - i/n)`. -/
theorem prod_one_sub_div_nonneg (n k : ℕ) (h : k - 1 ≤ n) :
    0 ≤ ∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n) := by
  refine Finset.prod_nonneg fun i hi => ?_
  have hi' := Finset.mem_Icc.mp hi
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  · have h1 : (i : ℝ) ≤ n := by exact_mod_cast (by omega : i ≤ n)
    have := (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr h1
    linarith

/-- Real-exponent form of KKO21 Fact 2.20, valid on the *other* side of the
integer `k`: for `k ≤ p < n`,
`e^{-p} ≤ ∏_{i=1}^{k-1}(1 - i/n) · (1 - p/n)^{n-p}`. -/
theorem exp_neg_le_prod_mul_rpow {n k : ℕ} (hkn : k < n) {p : ℝ}
    (hpk : (k : ℝ) ≤ p) (hpn : p < n) :
    Real.exp (-p) ≤
      (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
        (1 - p / n) ^ ((n : ℝ) - p) := by
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hA0 : 0 ≤ ∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n) :=
    prod_one_sub_div_nonneg n k (by omega)
  have hbn : 0 < 1 - p / n := by
    rw [sub_pos, div_lt_one hnR]
    exact hpn
  -- Fact 2.20 at `p = k` (trivial for `k = 0`)
  have hbase : Real.exp (-(k : ℝ)) ≤
      (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
        (1 - (k : ℝ) / n) ^ (n - k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num [show Finset.Icc 1 (0 - 1) = (∅ : Finset ℕ) from rfl]
    · exact exp_neg_le_prod_mul_pow hk hkn (by linarith) le_rfl
  -- monotone step from `k` to `p`
  have hmono := one_sub_div_rpow_mul_exp_le (t := (n : ℝ)) (a := (k : ℝ))
    (b := p) (by positivity) hpk hpn
  have hnat : ((1 : ℝ) - (k : ℝ) / n) ^ ((n : ℝ) - (k : ℝ))
      = (1 - (k : ℝ) / n) ^ (n - k) := by
    rw [show (n : ℝ) - (k : ℝ) = ((n - k : ℕ) : ℝ) by
        rw [Nat.cast_sub hkn.le], Real.rpow_natCast]
  rw [hnat] at hmono
  have h1 : 1 ≤ (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
      (1 - (k : ℝ) / n) ^ (n - k) * Real.exp (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (k : ℝ)).le
    rw [← Real.exp_add] at h
    simpa using h
  have h2 : (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
        ((1 - (k : ℝ) / n) ^ (n - k) * Real.exp (k : ℝ))
      ≤ (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
        ((1 - p / n) ^ ((n : ℝ) - p) * Real.exp p) :=
    mul_le_mul_of_nonneg_left hmono hA0
  have h3 : 1 ≤ (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
      (1 - p / n) ^ ((n : ℝ) - p) * Real.exp p := by
    nlinarith [h1, h2]
  have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-p)).le
  rw [one_mul] at h4
  calc Real.exp (-p)
      ≤ (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
          (1 - p / n) ^ ((n : ℝ) - p) * Real.exp p * Real.exp (-p) := h4
    _ = (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
          (1 - p / n) ^ ((n : ℝ) - p) := by
        rw [mul_assoc, ← Real.exp_add]
        simp

/-! ### The i.i.d. case -/

/-- The i.i.d. case of KKO21 Lemma 2.21: for `k - 1 < p < k + 1` and
`0 < p ≤ n`, the binomial point mass `P[Bin(n, p/n) = k]` is at least
`Poi(p, k) · (1 - p/(k+1))^{(p-k)⁺}`. -/
theorem poi_mul_le_choose_mul {n k : ℕ} (hkn : k ≤ n) {p : ℝ} (hp0 : 0 < p)
    (hp1 : (k : ℝ) - 1 < p) (hp2 : p < (k : ℝ) + 1) (hpn : p ≤ n) :
    poi p k * (1 - p / ((k : ℝ) + 1)) ^ (max (p - k) 0)
      ≤ (n.choose k : ℝ) * (p / n) ^ k * (1 - p / n) ^ (n - k) := by
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le hp0 hpn
  have hn : 0 < n := by exact_mod_cast hnR
  rw [cast_choose_mul_pow n k hkn hn p]
  have hA0 : 0 ≤ ∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n) :=
    prod_one_sub_div_nonneg n k (by omega)
  rcases le_or_gt p (k : ℝ) with hpk | hpk
  · -- case `p ≤ k`: the correction factor is `1`
    have hmax : max (p - (k : ℝ)) 0 = 0 := max_eq_right (by linarith)
    rw [hmax, Real.rpow_zero, mul_one]
    have hk1 : 1 ≤ k := by
      by_contra hcon
      have hk0 : k = 0 := by omega
      subst hk0
      norm_num at hpk
      linarith
    have hkey : Real.exp (-p) ≤
        (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
          (1 - p / n) ^ (n - k) := by
      rcases eq_or_lt_of_le hkn with rfl | hkn'
      · -- `n = k`: weak Stirling
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        rw [Nat.sub_self, pow_zero, mul_one]
        have hAval : (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / k))
            = (k.factorial : ℝ) / (k : ℝ) ^ k := by
          have h1 := cast_choose_mul_pow k k le_rfl hn 1
          rw [Nat.choose_self, Nat.cast_one, one_mul, div_pow, one_pow] at h1
          have hkk : ((k : ℝ)) ^ k ≠ 0 := by positivity
          have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
          field_simp at h1 ⊢
          linarith [h1]
        rw [hAval]
        have hst := pow_self_le_factorial_mul_exp k hk1
        have h2 : Real.exp (1 - (k : ℝ)) * (k : ℝ) ^ k ≤ (k.factorial : ℝ) := by
          calc Real.exp (1 - (k : ℝ)) * (k : ℝ) ^ k
              ≤ Real.exp (1 - (k : ℝ)) * ((k.factorial : ℝ)
                  * Real.exp ((k : ℝ) - 1)) :=
                mul_le_mul_of_nonneg_left hst (Real.exp_pos _).le
            _ = (k.factorial : ℝ) * (Real.exp (1 - (k : ℝ))
                  * Real.exp ((k : ℝ) - 1)) := by ring
            _ = (k.factorial : ℝ) := by
                rw [← Real.exp_add]
                norm_num
        have h3 : Real.exp (-p) ≤ Real.exp (1 - (k : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
        have hkkpos : (0 : ℝ) < (k : ℝ) ^ k := by positivity
        rw [le_div_iff₀ hkkpos]
        calc Real.exp (-p) * (k : ℝ) ^ k
            ≤ Real.exp (1 - (k : ℝ)) * (k : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right h3 hkkpos.le
          _ ≤ (k.factorial : ℝ) := h2
      · -- `k < n`: Fact 2.20 directly
        exact exp_neg_le_prod_mul_pow hk1 hkn' (by linarith) hpk
    unfold poi
    have hc0 : (0 : ℝ) ≤ p ^ k / (k.factorial : ℝ) := by positivity
    calc Real.exp (-p) * p ^ k / (k.factorial : ℝ)
        = (p ^ k / (k.factorial : ℝ)) * Real.exp (-p) := by ring
      _ ≤ (p ^ k / (k.factorial : ℝ)) *
            ((∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
              (1 - p / n) ^ (n - k)) := mul_le_mul_of_nonneg_left hkey hc0
      _ = p ^ k / (k.factorial : ℝ) *
            (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
            (1 - p / n) ^ (n - k) := by ring
  · -- case `k < p`
    have hmax : max (p - (k : ℝ)) 0 = p - k := max_eq_left (by linarith)
    rw [hmax]
    have hkn' : k < n := by
      by_contra hcon
      have hnk : n = k := by omega
      subst hnk
      linarith
    have hk1n : ((k : ℝ) + 1) ≤ n := by
      have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : k + 1 ≤ n)
      push_cast at this
      linarith
    have hpn' : p < n := by linarith
    have hbn : 0 < 1 - p / n := by
      rw [sub_pos, div_lt_one hnR]
      exact hpn'
    have hbk : 0 < 1 - p / ((k : ℝ) + 1) := by
      rw [sub_pos, div_lt_one (by positivity)]
      exact hp2
    have hsplit : ((1 - p / n) ^ (n - k) : ℝ)
        = (1 - p / n) ^ ((n : ℝ) - p) * (1 - p / n) ^ (p - (k : ℝ)) := by
      rw [← Real.rpow_natCast (1 - p / n) (n - k), Nat.cast_sub hkn'.le,
        ← Real.rpow_add hbn]
      congr 1
      ring
    have hkey := exp_neg_le_prod_mul_rpow hkn' hpk.le hpn'
    have hfac : (1 - p / ((k : ℝ) + 1)) ^ (p - (k : ℝ))
        ≤ (1 - p / n) ^ (p - (k : ℝ)) := by
      refine Real.rpow_le_rpow hbk.le ?_ (by linarith)
      have hd : p / (n : ℝ) ≤ p / ((k : ℝ) + 1) := by
        gcongr
      linarith
    have hcombine : Real.exp (-p) * (1 - p / ((k : ℝ) + 1)) ^ (p - (k : ℝ))
        ≤ (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
            (1 - p / n) ^ ((n : ℝ) - p) * (1 - p / n) ^ (p - (k : ℝ)) :=
      mul_le_mul hkey hfac (Real.rpow_nonneg hbk.le _)
        (mul_nonneg hA0 (Real.rpow_nonneg hbn.le _))
    have hc0 : (0 : ℝ) ≤ p ^ k / (k.factorial : ℝ) := by positivity
    unfold poi
    rw [hsplit]
    calc Real.exp (-p) * p ^ k / (k.factorial : ℝ)
          * (1 - p / ((k : ℝ) + 1)) ^ (p - (k : ℝ))
        = (p ^ k / (k.factorial : ℝ))
            * (Real.exp (-p) * (1 - p / ((k : ℝ) + 1)) ^ (p - (k : ℝ))) := by
          ring
      _ ≤ (p ^ k / (k.factorial : ℝ))
            * ((∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
                (1 - p / n) ^ ((n : ℝ) - p) * (1 - p / n) ^ (p - (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hcombine hc0
      _ = p ^ k / (k.factorial : ℝ) *
            (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n)) *
            ((1 - p / n) ^ ((n : ℝ) - p) * (1 - p / n) ^ (p - (k : ℝ))) := by
          ring

/-! ### KKO21 Lemma 2.21 -/

/-- **KKO21 Lemma 2.21**: if `X` is a sum of independent Bernoullis with
mean `p` and `k` is an integer with `k - 1 < p < k + 1`, then for some
integer `0 ≤ l ≤ min(p, k)`,

`P[X = k] ≥ Poi(p - l, k - l) · (1 - (p-l)/(k-l+1))^{(p-k)⁺}`.

Taking the minimum over `l` recovers the paper's statement. -/
theorem poi_le_probCount (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk1 : (k : ℝ) - 1 < ∑ i, q i) (hk2 : ∑ i, q i < (k : ℝ) + 1) :
    ∃ l : ℕ, l ≤ k ∧ (l : ℝ) ≤ ∑ i, q i ∧
      poi ((∑ i, q i) - l) (k - l)
          * (1 - ((∑ i, q i) - l) / (((k - l : ℕ) : ℝ) + 1))
            ^ (max ((∑ i, q i) - k) 0)
        ≤ probCount q k := by
  classical
  set p : ℝ := ∑ i, q i with hpdef
  have hp0 : (0 : ℝ) ≤ p := Finset.sum_nonneg fun i _ => (hq i).1
  rcases eq_or_lt_of_le hp0 with hp0' | hp0'
  · -- degenerate case `p = 0`: forced `k = 0` and `P[X = 0] = 1`
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) < 1 := by linarith
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h1)
    subst hk0
    have hpc : probCount q 0 = 1 := by
      rw [probCount_def, Finset.powersetCard_zero, Finset.sum_singleton]
      unfold atomProb
      rw [Finset.prod_empty, one_mul, Finset.sdiff_empty]
      have hsum0 : ∑ i, q i = 0 := by
        rw [← hpdef]
        exact hp0'.symm
      have hall : ∀ i ∈ Finset.univ, (1 : ℝ) - q i = 1 := by
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hq i).1)] at hsum0
        intro i hi
        rw [hsum0 i hi]
        ring
      rw [Finset.prod_congr rfl hall, Finset.prod_const_one]
    refine ⟨0, le_rfl, by simpa using hp0, ?_⟩
    rw [hpc, ← hp0']
    norm_num [poi, Real.rpow_zero]
  · -- main case `0 < p`: reduce via Hoeffding to a three-valued vector
    have hsn : p ≤ (Fintype.card ι : ℝ) := by
      rw [hpdef]
      calc ∑ i, q i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hq i).2
        _ = Fintype.card ι := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    obtain ⟨w, hwIcc, hwsum, ⟨x, hx0, hx1, h3v⟩, hwmin⟩ :=
      exists_min_three_valued (fun m => if m = k then (1 : ℝ) else 0) p hp0 hsn
    have hwq : probCount w k ≤ probCount q k := by
      have h := hwmin q hq hpdef.symm
      rwa [expect_indicator, expect_indicator] at h
    obtain ⟨O, hOdef⟩ : ∃ s : Finset ι, s = Finset.univ.filter (fun i => w i = 1) :=
      ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ s : Finset ι, s = Finset.univ.filter (fun i => w i = 0) :=
      ⟨_, rfl⟩
    have hOw : ∀ i ∈ O, w i = 1 := by
      intro i hi
      rw [hOdef] at hi
      exact (Finset.mem_filter.mp hi).2
    have hZw : ∀ i ∈ Z, w i = 0 := by
      intro i hi
      rw [hZdef] at hi
      exact (Finset.mem_filter.mp hi).2
    have hxw : ∀ i, i ∉ O → i ∉ Z → w i = x := by
      intro i hiO hiZ
      rw [hOdef] at hiO
      rw [hZdef] at hiZ
      rcases h3v i with h | h | h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hiZ
      · exact h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hiO
    have hOZ : Disjoint O Z := by
      rw [Finset.disjoint_left]
      intro i hiO hiZ
      have h1 := hOw i hiO
      have h2 := hZw i hiZ
      rw [h1] at h2
      norm_num at h2
    have hpl : p = (O.card : ℝ)
        + ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
      rw [← hwsum]
      exact sum_threeValued w O Z x hOw hZw hxw hOZ
    have hlp : (O.card : ℝ) ≤ p := by
      rw [hpl]
      have : (0 : ℝ) ≤ ((Finset.univ \ (O ∪ Z)).card : ℝ) * x :=
        mul_nonneg (Nat.cast_nonneg _) hx0.le
      linarith
    have hlk : O.card ≤ k := by
      by_contra hcon
      have h1 : ((k + 1 : ℕ) : ℝ) ≤ (O.card : ℝ) := by
        exact_mod_cast (by omega : k + 1 ≤ O.card)
      push_cast at h1
      linarith
    refine ⟨O.card, hlk, hlp, ?_⟩
    rcases Nat.eq_zero_or_pos (Finset.univ \ (O ∪ Z)).card with hr | hr
    · -- no interior coordinates: `p = l` is an integer, so `l = k`
      have hpl' : p = (O.card : ℝ) := by
        rw [hpl, hr]
        norm_num
      have hlkeq : O.card = k := by
        have h1 : (k : ℝ) - 1 < (O.card : ℝ) := by rw [← hpl']; exact hk1
        have h2 : k ≤ O.card := by
          by_contra hcon
          have : ((O.card + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (by omega : O.card + 1 ≤ k)
          push_cast at this
          linarith
        omega
      have hpc1 : probCount w k = 1 := by
        rw [probCount_threeValued w O Z x hOw hZw hxw hOZ k hlk, hlkeq, hr]
        norm_num
      have hbound : poi (p - (O.card : ℝ)) (k - O.card)
          * (1 - (p - (O.card : ℝ)) / (((k - O.card : ℕ) : ℝ) + 1))
            ^ (max (p - (k : ℝ)) 0) = 1 := by
        rw [hlkeq, hpl', hlkeq]
        norm_num [poi, Nat.sub_self]
      rw [hbound]
      calc (1 : ℝ) = probCount w k := hpc1.symm
        _ ≤ probCount q k := hwq
    · -- interior coordinates present: the shifted-binomial main branch
      have hrR : (0 : ℝ) < ((Finset.univ \ (O ∪ Z)).card : ℝ) := by
        exact_mod_cast hr
      have hrx : ((Finset.univ \ (O ∪ Z)).card : ℝ) * x = p - O.card := by
        rw [hpl]
        ring
      have hxval : x = (p - (O.card : ℝ)) / ((Finset.univ \ (O ∪ Z)).card : ℝ) := by
        rw [← hrx, mul_comm, mul_div_assoc, div_self hrR.ne', mul_one]
      have hp'0 : 0 < p - (O.card : ℝ) := by
        rw [← hrx]
        exact mul_pos hrR hx0
      have hp'r : p - (O.card : ℝ) < ((Finset.univ \ (O ∪ Z)).card : ℝ) := by
        rw [← hrx]
        nlinarith [hrR, hx1]
      have hk'r : k - O.card ≤ (Finset.univ \ (O ∪ Z)).card := by
        by_contra hcon
        have h1 : ((O.card + (Finset.univ \ (O ∪ Z)).card + 1 : ℕ) : ℝ)
            ≤ (k : ℝ) := by
          exact_mod_cast (by omega : O.card + (Finset.univ \ (O ∪ Z)).card + 1 ≤ k)
        push_cast at h1
        linarith [hp'r, hk1]
      have hp'1 : ((k - O.card : ℕ) : ℝ) - 1 < p - O.card := by
        rw [Nat.cast_sub hlk]
        linarith
      have hp'2 : p - (O.card : ℝ) < ((k - O.card : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub hlk]
        linarith
      have hiid := poi_mul_le_choose_mul (n := (Finset.univ \ (O ∪ Z)).card)
        (k := k - O.card) hk'r hp'0 hp'1 hp'2 hp'r.le
      have hexp : (p - (O.card : ℝ)) - ((k - O.card : ℕ) : ℝ) = p - k := by
        rw [Nat.cast_sub hlk]
        ring
      rw [hexp] at hiid
      have hpc := probCount_threeValued w O Z x hOw hZw hxw hOZ k hlk
      rw [hxval] at hpc
      calc poi (p - (O.card : ℝ)) (k - O.card)
            * (1 - (p - (O.card : ℝ)) / (((k - O.card : ℕ) : ℝ) + 1))
              ^ (max (p - (k : ℝ)) 0)
          ≤ ((Finset.univ \ (O ∪ Z)).card.choose (k - O.card) : ℝ)
              * ((p - (O.card : ℝ)) / ((Finset.univ \ (O ∪ Z)).card : ℝ))
                  ^ (k - O.card)
              * (1 - (p - (O.card : ℝ))
                  / ((Finset.univ \ (O ∪ Z)).card : ℝ))
                  ^ ((Finset.univ \ (O ∪ Z)).card - (k - O.card)) := hiid
        _ = probCount w k := by rw [hpc]; ring
        _ ≤ probCount q k := hwq

/-- **KKO21 Lemma 2.22** (from `TSPGap.binomial_lowerTail_le_shifted_poisson`,
`BinomialPoisson.lean`): if `X` is a sum of
independent Bernoullis with mean `p` and `k = ⌈p⌉` (equivalently
`k - 1 < p ≤ k`), then for some integer `0 ≤ l ≤ min(p, k)`

`P[X ≥ k] ≥ Poi(p - l, ≥ k - l) = 1 - ∑_{i < k-l} poi (p-l) i`.

Taking the minimum over `l` recovers the paper's statement. -/
theorem poi_tail_le_probGE (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk1 : (k : ℝ) - 1 < ∑ i, q i) (hk2 : ∑ i, q i ≤ (k : ℝ)) :
    ∃ l : ℕ, l ≤ k ∧ (l : ℝ) ≤ ∑ i, q i ∧
      1 - ∑ i ∈ Finset.range (k - l), poi ((∑ i, q i) - l) i ≤ probGE q k := by
  classical
  set p : ℝ := ∑ i, q i with hpdef
  have hp0 : (0 : ℝ) ≤ p := Finset.sum_nonneg fun i _ => (hq i).1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: the tail is everything and the bound is `1`
    refine ⟨0, le_rfl, by simpa using hp0, ?_⟩
    have h := sum_probCount_add_probGE q 0
    rw [Finset.range_zero, Finset.sum_empty, zero_add] at h
    rw [Nat.sub_self, Finset.range_zero, Finset.sum_empty, sub_zero, h]
  · -- `k ≥ 1`, hence `p > 0`
    have hsn : p ≤ (Fintype.card ι : ℝ) := by
      rw [hpdef]
      calc ∑ i, q i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hq i).2
        _ = Fintype.card ι := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    obtain ⟨w, hwIcc, hwsum, ⟨x, hx0, hx1, h3v⟩, hwmin⟩ :=
      exists_min_three_valued (fun m => if k ≤ m then (1 : ℝ) else 0) p hp0 hsn
    have hwq : probGE w k ≤ probGE q k := by
      have h := hwmin q hq hpdef.symm
      rwa [expect_indicator_ge, expect_indicator_ge] at h
    obtain ⟨O, hOdef⟩ : ∃ s : Finset ι,
        s = Finset.univ.filter (fun i => w i = 1) := ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ s : Finset ι,
        s = Finset.univ.filter (fun i => w i = 0) := ⟨_, rfl⟩
    have hOw : ∀ i ∈ O, w i = 1 := by
      intro i hi
      rw [hOdef] at hi
      exact (Finset.mem_filter.mp hi).2
    have hZw : ∀ i ∈ Z, w i = 0 := by
      intro i hi
      rw [hZdef] at hi
      exact (Finset.mem_filter.mp hi).2
    have hxw : ∀ i, i ∉ O → i ∉ Z → w i = x := by
      intro i hiO hiZ
      rw [hOdef] at hiO
      rw [hZdef] at hiZ
      rcases h3v i with h | h | h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hiZ
      · exact h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hiO
    have hOZ : Disjoint O Z := by
      rw [Finset.disjoint_left]
      intro i hiO hiZ
      have h1 := hOw i hiO
      have h2 := hZw i hiZ
      rw [h1] at h2
      norm_num at h2
    have hpl : p = (O.card : ℝ)
        + ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
      rw [← hwsum]
      exact sum_threeValued w O Z x hOw hZw hxw hOZ
    have hlp : (O.card : ℝ) ≤ p := by
      rw [hpl]
      have h1 : (0 : ℝ) ≤ ((Finset.univ \ (O ∪ Z)).card : ℝ) * x :=
        mul_nonneg (Nat.cast_nonneg _) hx0.le
      linarith
    have hlk : O.card ≤ k := by
      by_contra hcon
      have h1 : ((k + 1 : ℕ) : ℝ) ≤ (O.card : ℝ) := by
        exact_mod_cast (by omega : k + 1 ≤ O.card)
      push_cast at h1
      linarith
    have hcompl := sum_probCount_add_probGE w k
    rcases Nat.eq_zero_or_pos (Finset.univ \ (O ∪ Z)).card with hr | hr
    · -- no interior coordinates: `p = l = k` and the tail is everything
      have hpl' : p = (O.card : ℝ) := by
        rw [hpl, hr]
        norm_num
      have hlkeq : O.card = k := by
        have h2 : k ≤ O.card := by
          by_contra hcon
          have h3 : ((O.card + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (by omega : O.card + 1 ≤ k)
          push_cast at h3
          rw [hpl'] at hk1
          linarith
        omega
      have hvan : ∀ j ∈ Finset.range k, probCount w j = 0 := fun j hj =>
        probCount_eq_zero_of_lt w O hOw
          (by rw [hlkeq]; exact Finset.mem_range.mp hj)
      rw [Finset.sum_congr rfl hvan, Finset.sum_const_zero, zero_add] at hcompl
      refine ⟨k, le_rfl, by rw [hpl', hlkeq], ?_⟩
      rw [Nat.sub_self, Finset.range_zero, Finset.sum_empty, sub_zero, ← hcompl]
      exact hwq
    · -- interior coordinates present: shifted binomial + black box
      have hrR : (0 : ℝ) < ((Finset.univ \ (O ∪ Z)).card : ℝ) := by
        exact_mod_cast hr
      have hrx : ((Finset.univ \ (O ∪ Z)).card : ℝ) * x = p - O.card := by
        rw [hpl]
        ring
      have hlklt : O.card < k := by
        by_contra hcon
        have hOk : O.card = k := by omega
        have h1 : (0 : ℝ) < ((Finset.univ \ (O ∪ Z)).card : ℝ) * x :=
          mul_pos hrR hx0
        rw [hpl, hOk] at hk2
        linarith
      have h2 : ∀ i : ℕ, probCount w (O.card + i)
          = ((Finset.univ \ (O ∪ Z)).card.choose i : ℝ) * x ^ i
            * (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - i) := by
        intro i
        rw [probCount_threeValued w O Z x hOw hZw hxw hOZ (O.card + i)
          (Nat.le_add_right _ _),
          show O.card + i - O.card = i from by omega]
        ring
      have htail : ∑ j ∈ Finset.range k, probCount w j
          = ∑ i ∈ Finset.range (k - O.card),
              ((Finset.univ \ (O ∪ Z)).card.choose i : ℝ) * x ^ i
                * (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - i) := by
        have hvan : ∑ j ∈ Finset.range O.card, probCount w j = 0 :=
          Finset.sum_eq_zero fun j hj =>
            probCount_eq_zero_of_lt w O hOw (Finset.mem_range.mp hj)
        calc ∑ j ∈ Finset.range k, probCount w j
            = (∑ j ∈ Finset.range O.card, probCount w j)
              + ∑ j ∈ Finset.Ico O.card k, probCount w j := by
              rw [Finset.range_eq_Ico,
                ← Finset.sum_Ico_consecutive (fun j => probCount w j)
                  (Nat.zero_le O.card) hlklt.le,
                ← Finset.range_eq_Ico]
          _ = ∑ j ∈ Finset.Ico O.card k, probCount w j := by
              rw [hvan, zero_add]
          _ = ∑ i ∈ Finset.range (k - O.card), probCount w (O.card + i) :=
              Finset.sum_Ico_eq_sum_range _ _ _
          _ = _ := Finset.sum_congr rfl fun i _ => h2 i
      have hjR : ((k - O.card - 1 : ℕ) : ℝ)
          < ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
        rw [hrx]
        have hcast : ((k - O.card - 1 : ℕ) : ℝ) = (k : ℝ) - O.card - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k - O.card), Nat.cast_sub hlklt.le]
          norm_num
        rw [hcast]
        linarith
      have hjU : ((Finset.univ \ (O ∪ Z)).card : ℝ) * x
          ≤ ((k - O.card - 1 : ℕ) : ℝ) + 1 := by
        rw [hrx]
        have hcast : ((k - O.card - 1 : ℕ) : ℝ) = (k : ℝ) - O.card - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k - O.card), Nat.cast_sub hlklt.le]
          norm_num
        rw [hcast]
        linarith [hk2]
      obtain ⟨a, ha, hble⟩ :=
        binomial_lowerTail_le_shifted_poisson hx0 hx1 hjR hjU
      rw [hrx, show k - O.card - 1 + 1 = k - O.card from by omega,
        show k - O.card - a = k - (O.card + a) from by omega,
        show p - (O.card : ℝ) - (a : ℝ) = p - ((O.card + a : ℕ) : ℝ) from by
          push_cast; ring] at hble
      have hpoi : ∑ i ∈ Finset.range (k - (O.card + a)),
          Real.exp (-(p - ((O.card + a : ℕ) : ℝ)))
              * (p - ((O.card + a : ℕ) : ℝ)) ^ i / (i.factorial : ℝ)
          = ∑ i ∈ Finset.range (k - (O.card + a)),
              poi (p - ((O.card + a : ℕ) : ℝ)) i :=
        Finset.sum_congr rfl fun i _ => rfl
      rw [hpoi] at hble
      refine ⟨O.card + a, by omega, ?_, ?_⟩
      · have h4 : ((O.card + a + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast (by omega : O.card + a + 1 ≤ k)
        push_cast at h4 ⊢
        linarith
      · have h6 : ∑ j ∈ Finset.range k, probCount w j
            ≤ ∑ i ∈ Finset.range (k - (O.card + a)),
                poi (p - ((O.card + a : ℕ) : ℝ)) i := by
          rw [htail]
          exact hble
        linarith [hcompl, hwq, h6]

end Bernoulli
end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Bernoulli-sum parity toolkit (KKO21 §2.5)

Phase 1 of the roadmap.  Sums of independent Bernoullis drive all the
odd-parity estimates in the payment argument; the pivotal algorithm constants
(`0.5678`, `0.56797`, `τ = 0.571β`) come from the bounds in this file.

* `evenMass_eq` — **KKO21 Fact 2.16**: the probability that a sum of
  independent Bernoullis with success probabilities `q i` is even equals
  `(1 + ∏ (1 - 2 q i)) / 2`.
* `evenMass_le` — **KKO21 Corollary 2.17** in the regime `q i ≤ 1/2`:
  the even-parity mass is at most `(1 + exp (-2 ∑ q i)) / 2`.
* `evenMass_le_of_sum_le` — **KKO21 Corollary 2.17, general form**: the same
  bound assuming only `0 ≤ q i` and `∑ q i ≤ 1.2`.  Up to two factors
  `1 - 2 q i` can be negative (three would force `∑ q i > 3/2`); zero
  negative factors is the regime above, one makes the product nonpositive,
  and for two the AM–GM bound `(1-2a)(1-2b) ≤ (a+b-1)²` reduces everything
  to `(t-1)² ≤ e^{-2t}` on `(1, 1.2]`, certified by `e^{2.4} ≤ 25`.

* `exp_neg_le_prod_mul_pow` — **KKO21 Fact 2.20**: the sharp product bound
  `∏_{i=1}^{k-1} (1 - i/t) · (1 - p/t)^{t-k} ≥ e^{-p}` for `k - 1 ≤ p ≤ k`,
  by an elementary calculus-free argument (see the section header below).

We work with the finite product measure directly: the atom at the success
set `t ⊆ ι` has probability `∏_{i ∈ t} q i · ∏_{i ∉ t} (1 - q i)`, so no
measure-theoretic apparatus is needed.
-/

namespace TSPGap
namespace Bernoulli

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability that independent Bernoullis with success probabilities
`q` succeed exactly on the set `t`. -/
def atomProb (q : ι → ℝ) (t : Finset ι) : ℝ :=
  (∏ i ∈ t, q i) * ∏ i ∈ Finset.univ \ t, (1 - q i)

/-- The atoms have total mass one. -/
theorem sum_atomProb (q : ι → ℝ) :
    ∑ t ∈ Finset.univ.powerset, atomProb q t = 1 := by
  unfold atomProb
  rw [← Finset.prod_add]
  have h1 : ∀ i ∈ Finset.univ, q i + (1 - q i) = (1 : ℝ) := fun i _ => by ring
  rw [Finset.prod_congr rfl h1, Finset.prod_const_one]

/-- Signed atom masses sum to the product `∏ (1 - 2 q i)`. -/
theorem sum_signed_atomProb (q : ι → ℝ) :
    ∑ t ∈ Finset.univ.powerset, (-1 : ℝ) ^ t.card * atomProb q t
      = ∏ i, (1 - 2 * q i) := by
  have key : ∀ t : Finset ι,
      (-1 : ℝ) ^ t.card * atomProb q t
        = (∏ i ∈ t, (-q i)) * ∏ i ∈ Finset.univ \ t, (1 - q i) := by
    intro t
    have hneg : ∏ i ∈ t, (-q i) = (-1 : ℝ) ^ t.card * ∏ i ∈ t, q i := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    unfold atomProb
    rw [hneg]; ring
  rw [Finset.sum_congr rfl fun t _ => key t, ← Finset.prod_add]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- **KKO21 Fact 2.16** (parity generating identity): the even-parity mass of
a sum of independent Bernoullis is `(1 + ∏ (1 - 2 q i)) / 2`. -/
theorem evenMass_eq (q : ι → ℝ) :
    ∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card), atomProb q t
      = (1 + ∏ i, (1 - 2 * q i)) / 2 := by
  have hsplit :
      (∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card), atomProb q t)
        + ∑ t ∈ Finset.univ.powerset.filter (fun t => ¬ Even t.card), atomProb q t
      = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact sum_atomProb q
  have hsigned :
      (∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card), atomProb q t)
        - ∑ t ∈ Finset.univ.powerset.filter (fun t => ¬ Even t.card), atomProb q t
      = ∏ i, (1 - 2 * q i) := by
    rw [← sum_signed_atomProb q,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ.powerset
        (fun t => Even t.card) (fun t => (-1 : ℝ) ^ t.card * atomProb q t)]
    have he :
        ∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card),
            (-1 : ℝ) ^ t.card * atomProb q t
          = ∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card),
              atomProb q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [(Finset.mem_filter.mp ht).2.neg_one_pow, one_mul]
    have ho :
        ∑ t ∈ Finset.univ.powerset.filter (fun t => ¬ Even t.card),
            (-1 : ℝ) ^ t.card * atomProb q t
          = - ∑ t ∈ Finset.univ.powerset.filter (fun t => ¬ Even t.card),
              atomProb q t := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [(Nat.not_even_iff_odd.mp (Finset.mem_filter.mp ht).2).neg_one_pow]
      ring
    rw [he, ho]; ring
  linarith

/-- `1 - 2x ≤ exp (-2x)`. -/
theorem one_sub_two_mul_le_exp (x : ℝ) : 1 - 2 * x ≤ Real.exp (-2 * x) := by
  have h := Real.add_one_le_exp (-2 * x)
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- If `q i ≤ 1/2` on `s` then `∏_{i ∈ s} (1 - 2 q i) ≤ exp (-2 ∑_{i ∈ s} q i)`. -/
theorem prod_one_sub_two_mul_le_on (s : Finset ι) (q : ι → ℝ)
    (hh : ∀ i ∈ s, q i ≤ 1 / 2) :
    ∏ i ∈ s, (1 - 2 * q i) ≤ Real.exp (-2 * ∑ i ∈ s, q i) := by
  calc ∏ i ∈ s, (1 - 2 * q i)
      ≤ ∏ i ∈ s, Real.exp (-2 * q i) :=
        Finset.prod_le_prod (fun i hi => by have := hh i hi; linarith)
          (fun i _ => one_sub_two_mul_le_exp (q i))
    _ = Real.exp (∑ i ∈ s, -2 * q i) := (Real.exp_sum _ _).symm
    _ = Real.exp (-2 * ∑ i ∈ s, q i) := by rw [← Finset.mul_sum]

omit [DecidableEq ι] in
/-- If every `q i ≤ 1/2` then `∏ (1 - 2 q i) ≤ exp (-2 ∑ q i)`. -/
theorem prod_one_sub_two_mul_le (q : ι → ℝ) (hh : ∀ i, q i ≤ 1 / 2) :
    ∏ i, (1 - 2 * q i) ≤ Real.exp (-2 * ∑ i, q i) :=
  prod_one_sub_two_mul_le_on Finset.univ q fun i _ => hh i

/-- `e^{2.4} ≤ 25`, from `e ≤ 2.7182818286` by cubing. -/
theorem exp_two_point_four_le : Real.exp 2.4 ≤ 25 := by
  have e1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h24 : Real.exp 2.4 ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hsq : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul e1 e1 h0 (by norm_num)
  have hcube : Real.exp 1 * Real.exp 1 * Real.exp 1
      ≤ 2.7182818286 * 2.7182818286 * 2.7182818286 :=
    mul_le_mul hsq e1 h0 (by norm_num)
  nlinarith [h24, h3, hcube]

/-- `0.04 ≤ e^{-2.4}`. -/
theorem le_exp_neg_two_point_four : (0.04 : ℝ) ≤ Real.exp (-2.4) := by
  have h1 : Real.exp (-2.4) * Real.exp 2.4 = 1 := by
    rw [← Real.exp_add]; norm_num [Real.exp_zero]
  have h3 : (0 : ℝ) < Real.exp (-2.4) := Real.exp_pos _
  nlinarith [mul_nonneg h3.le (sub_nonneg.mpr exp_two_point_four_le)]

/-- On `1 ≤ t ≤ 1.2` we have `(t - 1)² ≤ e^{-2t}`: the square is at most
`0.04` while the exponential is at least `e^{-2.4}`. -/
theorem sq_sub_one_le_exp {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 1.2) :
    (t - 1) ^ 2 ≤ Real.exp (-2 * t) := by
  have ha : (t - 1) ^ 2 ≤ 0.04 := by nlinarith
  have hb : Real.exp (-2.4) ≤ Real.exp (-2 * t) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith [le_exp_neg_two_point_four]

omit [DecidableEq ι] in
/-- **KKO21 Corollary 2.17, product form** (general regime): if `0 ≤ q i`
and `∑ q i ≤ 1.2` then `∏ (1 - 2 q i) ≤ exp (-2 ∑ q i)`.

At most two factors are negative (three would force `∑ q i > 3/2 > 1.2`).
With none the factorwise bound applies; with one the product is nonpositive;
with two, AM–GM gives `(1-2 q j)(1-2 q k) ≤ (q j + q k - 1)²` and
`sq_sub_one_le_exp` finishes. -/
theorem prod_one_sub_two_mul_le_of_sum_le (q : ι → ℝ) (h0 : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1.2) :
    ∏ i, (1 - 2 * q i) ≤ Real.exp (-2 * ∑ i, q i) := by
  classical
  set N := Finset.univ.filter (fun i => 1 / 2 < q i) with hN
  have hmem : ∀ i ∈ N, 1 / 2 < q i := fun i hi => (Finset.mem_filter.mp hi).2
  have hout : ∀ i, i ∉ N → q i ≤ 1 / 2 := fun i hi =>
    not_lt.mp fun hlt => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
  have hcard : N.card ≤ 2 := by
    by_contra hc
    have hc3 : 3 ≤ N.card := by omega
    have h1 : (N.card : ℝ) * (1 / 2) ≤ ∑ i ∈ N, q i := by
      have h := Finset.sum_le_sum (s := N) (f := fun _ : ι => (1 / 2 : ℝ))
        (g := q) (fun i hi => (hmem i hi).le)
      rwa [Finset.sum_const, nsmul_eq_mul] at h
    have h2 : ∑ i ∈ N, q i ≤ ∑ i, q i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
        fun i _ _ => h0 i
    have h3 : (3 : ℝ) ≤ (N.card : ℝ) := by exact_mod_cast hc3
    nlinarith
  obtain hc0 | hc1 | hc2 : N.card = 0 ∨ N.card = 1 ∨ N.card = 2 := by omega
  · -- no negative factors
    have hall : ∀ i, q i ≤ 1 / 2 := fun i =>
      hout i (by simp [Finset.card_eq_zero.mp hc0])
    exact prod_one_sub_two_mul_le q hall
  · -- one negative factor: the whole product is nonpositive
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc1
    have hjN : j ∈ N := by rw [hj]; simp
    have hqj := hmem j hjN
    have hle : ∏ i, (1 - 2 * q i) ≤ 0 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      have hrest : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 - 2 * q i) :=
        Finset.prod_nonneg fun i hi => by
          have hij : i ≠ j := (Finset.mem_erase.mp hi).1
          have hi' : q i ≤ 1 / 2 := hout i (by rw [hj]; simp [hij])
          linarith
      have hneg : 1 - 2 * q j ≤ 0 := by linarith
      nlinarith [mul_nonneg (neg_nonneg.mpr hneg) hrest]
    exact hle.trans (Real.exp_pos _).le
  · -- two negative factors
    obtain ⟨j, k, hjk, hN2⟩ := Finset.card_eq_two.mp hc2
    have hjN : j ∈ N := by rw [hN2]; simp
    have hkN : k ∈ N := by rw [hN2]; simp
    have hqj := hmem j hjN
    have hqk := hmem k hkN
    have hNprod : ∏ i ∈ N, (1 - 2 * q i) = (1 - 2 * q j) * (1 - 2 * q k) := by
      rw [hN2]; exact Finset.prod_pair hjk
    have hNsum : ∑ i ∈ N, q i = q j + q k := by
      rw [hN2]; exact Finset.sum_pair hjk
    have hts : (q j + q k) + ∑ i ∈ Nᶜ, q i = ∑ i, q i := by
      rw [← hNsum]; exact Finset.sum_add_sum_compl N q
    have hsc : 0 ≤ ∑ i ∈ Nᶜ, q i := Finset.sum_nonneg fun i _ => h0 i
    have hcomp : ∀ i ∈ Nᶜ, q i ≤ 1 / 2 := fun i hi =>
      hout i (Finset.mem_compl.mp hi)
    have hB : ∏ i ∈ Nᶜ, (1 - 2 * q i) ≤ Real.exp (-2 * ∑ i ∈ Nᶜ, q i) :=
      prod_one_sub_two_mul_le_on Nᶜ q hcomp
    have hBnn : 0 ≤ ∏ i ∈ Nᶜ, (1 - 2 * q i) :=
      Finset.prod_nonneg fun i hi => by have := hcomp i hi; linarith
    calc ∏ i, (1 - 2 * q i)
        = (∏ i ∈ N, (1 - 2 * q i)) * ∏ i ∈ Nᶜ, (1 - 2 * q i) :=
          (Finset.prod_mul_prod_compl N _).symm
      _ ≤ ((q j + q k) - 1) ^ 2 * Real.exp (-2 * ∑ i ∈ Nᶜ, q i) := by
          refine mul_le_mul ?_ hB hBnn (by positivity)
          rw [hNprod]
          nlinarith [sq_nonneg (q j - q k)]
      _ ≤ Real.exp (-2 * (q j + q k)) * Real.exp (-2 * ∑ i ∈ Nᶜ, q i) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact sq_sub_one_le_exp (by linarith) (by linarith [hts, hsc, hsum])
      _ = Real.exp (-2 * ∑ i, q i) := by
          rw [← Real.exp_add]
          congr 1
          linarith [hts]

/-- **KKO21 Corollary 2.17** (regime `q i ≤ 1/2`): the even-parity mass of a
Bernoulli sum is at most `(1 + exp (-2 ∑ q i)) / 2`.  For the general regime
see `evenMass_le_of_sum_le`. -/
theorem evenMass_le (q : ι → ℝ) (hh : ∀ i, q i ≤ 1 / 2) :
    ∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card), atomProb q t
      ≤ (1 + Real.exp (-2 * ∑ i, q i)) / 2 := by
  rw [evenMass_eq]
  have h := prod_one_sub_two_mul_le q hh
  linarith

/-- **KKO21 Corollary 2.17** (general form): for success probabilities
`0 ≤ q i` with `∑ q i ≤ 1.2`, the even-parity mass of a Bernoulli sum is at
most `(1 + exp (-2 ∑ q i)) / 2`. -/
theorem evenMass_le_of_sum_le (q : ι → ℝ) (h0 : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i ≤ 1.2) :
    ∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card), atomProb q t
      ≤ (1 + Real.exp (-2 * ∑ i, q i)) / 2 := by
  rw [evenMass_eq]
  have h := prod_one_sub_two_mul_le_of_sum_le q h0 hsum
  linarith

/-! ### KKO21 Fact 2.20: a sharp Poisson-type product bound

`∏_{i=1}^{k-1} (1 - i/t) · (1 - p/t)^{t-k} ≥ e^{-p}` for integers `k < t`
and `k - 1 ≤ p ≤ k` (`exp_neg_le_prod_mul_pow` below).  This feeds the
Poisson lower bounds for Bernoulli sums (KKO21 Lemmas 2.21/2.22).

KKO21 prove it by showing the left side decreases in `t` (differentiating
the logarithm, an integral comparison, and a Taylor estimate).  We give an
elementary proof with no calculus — everything reduces to `1 + x ≤ eˣ`:

* *induction on `k` at `p = k - 1`*: the ratio of consecutive cases is
  `((t-j)/(t-j+1))^{t-j}`, so the step is exactly the classical
  `(1 + 1/m)^m ≤ e`;
* *reduction from general `p`*: with `u = p - k + 1 ∈ [0, 1]`, the bound
  `(1 - (k-1)/t) ≤ (1 + u/(t-k))(1 - p/t)` is the polynomial identity
  `(c+u)(c+1-u) - c(c+1) = u(1-u) ≥ 0`, and raising to the `(t-k)`-th power
  costs exactly a factor `e^u`.
-/

/-- The classical `(m+1)^m ≤ e · m^m`, i.e. `(1 + 1/m)^m ≤ e`. -/
theorem succ_pow_le_exp_mul_pow (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ m ≤ Real.exp 1 * (m : ℝ) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (m : ℝ) + 1 ≤ m * Real.exp (1 / m) := by
    have h := Real.add_one_le_exp (1 / (m : ℝ))
    have h2 : (m : ℝ) * (1 / m + 1) ≤ m * Real.exp (1 / m) :=
      mul_le_mul_of_nonneg_left h hm0.le
    have h3 : (m : ℝ) * (1 / m + 1) = m + 1 := by
      field_simp
      ring
    linarith
  calc ((m : ℝ) + 1) ^ m
      ≤ ((m : ℝ) * Real.exp (1 / m)) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
    _ = (m : ℝ) ^ m * Real.exp (1 / m) ^ m := mul_pow _ _ _
    _ = (m : ℝ) ^ m * Real.exp 1 := by
        rw [← Real.exp_nat_mul, mul_one_div, div_self hm0.ne']
    _ = Real.exp 1 * (m : ℝ) ^ m := mul_comm _ _

/-- The `p = k - 1` case of KKO21 Fact 2.20: for `j < t`,
`e^{-j} ≤ ∏_{i=1}^{j} (1 - i/t) · (1 - j/t)^{t-j-1}`. -/
theorem exp_neg_natCast_le_prod_mul_pow (t : ℕ) (j : ℕ) :
    j < t →
      Real.exp (-(j : ℝ)) ≤
        (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℝ) / t)) *
          (1 - (j : ℝ) / t) ^ (t - j - 1) := by
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hjt
    have hjt' : j < t := by omega
    have htpos : 0 < t := by omega
    have ht0 : (0 : ℝ) < t := by exact_mod_cast htpos
    push_cast
    set M : ℕ := t - j - 1 with hMdef
    have hM1 : 1 ≤ M := by omega
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hMr : (M : ℝ) = (t : ℝ) - (j : ℝ) - 1 := by
      have h : M = t - (j + 1) := by omega
      rw [h, Nat.cast_sub (by omega : j + 1 ≤ t)]
      push_cast
      ring
    have hx0 : (0 : ℝ) ≤ 1 - ((j : ℝ) + 1) / t := by
      have hle : (j : ℝ) + 1 ≤ t := by exact_mod_cast hjt.le
      have := (div_le_one ht0).mpr hle
      linarith
    have hb0 : 1 - (j : ℝ) / t = ((M : ℝ) + 1) / t := by
      rw [hMr, one_sub_div ht0.ne']
      ring_nf
    have hb1 : 1 - ((j : ℝ) + 1) / t = (M : ℝ) / t := by
      rw [hMr, one_sub_div ht0.ne']
      ring_nf
    have hfact : 1 - (j : ℝ) / t = (1 + 1 / (M : ℝ)) * (1 - ((j : ℝ) + 1) / t) := by
      rw [hb0, hb1]
      field_simp
    have hone : (1 + 1 / (M : ℝ)) ^ M ≤ Real.exp 1 := by
      have h := succ_pow_le_exp_mul_pow M hM1
      have heq : 1 + 1 / (M : ℝ) = ((M : ℝ) + 1) / M := by field_simp
      rw [heq, div_pow, div_le_iff₀ (pow_pos hM0 M)]
      linarith
    have hstep : (1 - (j : ℝ) / t) ^ M ≤ Real.exp 1 * (1 - ((j : ℝ) + 1) / t) ^ M := by
      rw [hfact, mul_pow]
      exact mul_le_mul_of_nonneg_right hone (pow_nonneg hx0 M)
    have hsplit :
        (∏ i ∈ Finset.Icc 1 (j + 1), (1 - (i : ℝ) / t))
          = (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℝ) / t)) * (1 - ((j : ℝ) + 1) / t) := by
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ j + 1)]
      push_cast
      ring
    have hexp : t - (j + 1) - 1 = M - 1 := by omega
    have hprod0 : 0 ≤ ∏ i ∈ Finset.Icc 1 j, (1 - (i : ℝ) / t) :=
      Finset.prod_nonneg fun i hi => by
        have hi2 : i ≤ j := (Finset.mem_Icc.mp hi).2
        have hle : (i : ℝ) ≤ t := by exact_mod_cast (by omega : i ≤ t)
        have := (div_le_one ht0).mpr hle
        linarith
    have hIH := ih hjt'
    rw [hsplit, hexp, mul_assoc,
      show (1 - ((j : ℝ) + 1) / t) * (1 - ((j : ℝ) + 1) / t) ^ (M - 1)
          = (1 - ((j : ℝ) + 1) / t) ^ M from by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega]
    calc Real.exp (-((j : ℝ) + 1))
        = Real.exp (-(j : ℝ)) * Real.exp (-1) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ ((∏ i ∈ Finset.Icc 1 j, (1 - (i : ℝ) / t)) * (1 - (j : ℝ) / t) ^ M) *
            Real.exp (-1) :=
          mul_le_mul_of_nonneg_right hIH (Real.exp_pos _).le
      _ = (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℝ) / t)) *
            ((1 - (j : ℝ) / t) ^ M * Real.exp (-1)) := by ring
      _ ≤ (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℝ) / t)) * (1 - ((j : ℝ) + 1) / t) ^ M := by
          refine mul_le_mul_of_nonneg_left ?_ hprod0
          have h2 := mul_le_mul_of_nonneg_left hstep (Real.exp_pos (-1)).le
          have h3 : Real.exp (-1) * Real.exp 1 = 1 := by
            rw [← Real.exp_add]
            norm_num
          calc (1 - (j : ℝ) / t) ^ M * Real.exp (-1)
              = Real.exp (-1) * (1 - (j : ℝ) / t) ^ M := mul_comm _ _
            _ ≤ Real.exp (-1) * (Real.exp 1 * (1 - ((j : ℝ) + 1) / t) ^ M) := h2
            _ = (1 - ((j : ℝ) + 1) / t) ^ M := by
                rw [← mul_assoc, h3, one_mul]

/-- **KKO21 Fact 2.20**: for integers `k < t` with `1 ≤ k` and any real
`k - 1 ≤ p ≤ k`,
`e^{-p} ≤ ∏_{i=1}^{k-1} (1 - i/t) · (1 - p/t)^{t-k}`. -/
theorem exp_neg_le_prod_mul_pow {t k : ℕ} (hk : 1 ≤ k) (hkt : k < t) {p : ℝ}
    (hp1 : (k : ℝ) - 1 ≤ p) (hp2 : p ≤ (k : ℝ)) :
    Real.exp (-p) ≤
      (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / t)) *
        (1 - p / t) ^ (t - k) := by
  have htpos : 0 < t := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast htpos
  have hn1 : 1 ≤ t - k := by omega
  have hnr : ((t - k : ℕ) : ℝ) = (t : ℝ) - k := by
    rw [Nat.cast_sub hkt.le]
  have hN0 : (0 : ℝ) < ((t - k : ℕ) : ℝ) := by exact_mod_cast hn1
  have hC0 : (0 : ℝ) < (t : ℝ) - k := by rw [← hnr]; exact hN0
  have hkt' : (k : ℝ) ≤ t := by exact_mod_cast hkt.le
  have hpt0 : (0 : ℝ) ≤ 1 - p / t := by
    have hple : p ≤ (t : ℝ) := hp2.trans hkt'
    have := (div_le_one ht0).mpr hple
    linarith
  have hqt0 : (0 : ℝ) ≤ 1 - ((k : ℝ) - 1) / t := by
    have h : (k : ℝ) - 1 ≤ t := by linarith
    have := (div_le_one ht0).mpr h
    linarith
  set v : ℝ := p - ((k : ℝ) - 1) with hv
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hv1 : v ≤ 1 := by rw [hv]; linarith
  have hbase : 1 - ((k : ℝ) - 1) / t ≤ (1 + v / ((t : ℝ) - k)) * (1 - p / t) := by
    have key : (1 + v / ((t : ℝ) - k)) * (1 - p / t) - (1 - ((k : ℝ) - 1) / t)
        = v * (1 - v) / (((t : ℝ) - k) * t) := by
      rw [hv]
      field_simp
      ring
    have hnn : 0 ≤ v * (1 - v) / (((t : ℝ) - k) * t) :=
      div_nonneg (mul_nonneg hv0 (by linarith)) (mul_pos hC0 ht0).le
    linarith [key, hnn]
  have hexp_base : 1 - ((k : ℝ) - 1) / t ≤ Real.exp (v / ((t : ℝ) - k)) * (1 - p / t) := by
    refine hbase.trans (mul_le_mul_of_nonneg_right ?_ hpt0)
    linarith [Real.add_one_le_exp (v / ((t : ℝ) - k))]
  have hpow : (1 - ((k : ℝ) - 1) / t) ^ (t - k) ≤ Real.exp v * (1 - p / t) ^ (t - k) := by
    calc (1 - ((k : ℝ) - 1) / t) ^ (t - k)
        ≤ (Real.exp (v / ((t : ℝ) - k)) * (1 - p / t)) ^ (t - k) :=
          pow_le_pow_left₀ hqt0 hexp_base _
      _ = Real.exp (v / ((t : ℝ) - k)) ^ (t - k) * (1 - p / t) ^ (t - k) := mul_pow _ _ _
      _ = Real.exp v * (1 - p / t) ^ (t - k) := by
          rw [← Real.exp_nat_mul]
          congr 1
          rw [hnr]
          field_simp
  have hA := exp_neg_natCast_le_prod_mul_pow t (k - 1) (by omega : k - 1 < t)
  have hkr : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hidx : t - (k - 1) - 1 = t - k := by omega
  rw [hkr, hidx] at hA
  have hprod0 : 0 ≤ ∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / t) :=
    Finset.prod_nonneg fun i hi => by
      have hi2 : i ≤ k - 1 := (Finset.mem_Icc.mp hi).2
      have hle : (i : ℝ) ≤ t := by exact_mod_cast (by omega : i ≤ t)
      have := (div_le_one ht0).mpr hle
      linarith
  calc Real.exp (-p)
      = Real.exp (-((k : ℝ) - 1)) * Real.exp (-v) := by
        rw [← Real.exp_add, hv]
        congr 1
        ring
    _ ≤ ((∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / t)) *
            (1 - ((k : ℝ) - 1) / t) ^ (t - k)) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ = (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / t)) *
          ((1 - ((k : ℝ) - 1) / t) ^ (t - k) * Real.exp (-v)) := by ring
    _ ≤ (∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / t)) * (1 - p / t) ^ (t - k) := by
        refine mul_le_mul_of_nonneg_left ?_ hprod0
        have h2 := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-v)).le
        have h3 : Real.exp (-v) * Real.exp v = 1 := by
          rw [← Real.exp_add]
          norm_num
        calc (1 - ((k : ℝ) - 1) / t) ^ (t - k) * Real.exp (-v)
            = Real.exp (-v) * (1 - ((k : ℝ) - 1) / t) ^ (t - k) := mul_comm _ _
          _ ≤ Real.exp (-v) * (Real.exp v * (1 - p / t) ^ (t - k)) := h2
          _ = (1 - p / t) ^ (t - k) := by
              rw [← mul_assoc, h3, one_mul]

/-! ### KKO21 Lemma 2.18: log-concave tail bounds

For a positive log-concave sequence `p 0, …, p n` with a single ratio drop
`p (i+1) ≤ γ · p i` for some `γ < 1`, log-concavity propagates the drop down
the whole tail (`logConcave_succ_le`), so the tail is dominated termwise by
a geometric sequence (`logConcave_le_geometric`) and the tail sums by
geometric series: `∑_{j=k}^{n} p j ≤ p k / (1-γ)` for `i ≤ k ≤ n`, and
`∑_{j=i+1}^{n} p j · j ≤ (p (i+1)/(1-γ)) · (i+1+γ/(1-γ))`.  These feed
KKO21 Corollary 2.19. -/

section LogConcave

variable {p : ℕ → ℝ} {n i : ℕ} {γ : ℝ}

/-- Log-concavity propagates a single ratio drop down the tail. -/
theorem logConcave_succ_le (hpos : ∀ j, j ≤ n → 0 < p j)
    (hlc : ∀ j, j + 2 ≤ n → p j * p (j + 2) ≤ p (j + 1) ^ 2)
    (hstep : p (i + 1) ≤ γ * p i) :
    ∀ j, i ≤ j → j + 1 ≤ n → p (j + 1) ≤ γ * p j := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact hstep
  | succ j hij ihj =>
    intro hjn
    have h1 : p (j + 1) ≤ γ * p j := ihj (by omega)
    have h2 : p j * p (j + 2) ≤ p (j + 1) ^ 2 := hlc j (by omega)
    have hpj : 0 < p j := hpos j (by omega)
    have hpj1 : 0 < p (j + 1) := hpos (j + 1) (by omega)
    have key : p (j + 2) ≤ γ * p (j + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hpj1.le]
    exact key

/-- Past the ratio drop, the sequence is dominated by a geometric one. -/
theorem logConcave_le_geometric (hγ0 : 0 ≤ γ) (hpos : ∀ j, j ≤ n → 0 < p j)
    (hlc : ∀ j, j + 2 ≤ n → p j * p (j + 2) ≤ p (j + 1) ^ 2)
    (hstep : p (i + 1) ≤ γ * p i) {k : ℕ} (hik : i ≤ k) :
    ∀ l, k + l ≤ n → p (k + l) ≤ γ ^ l * p k := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ihl =>
    intro hln
    have h1 : p (k + l) ≤ γ ^ l * p k := ihl (by omega)
    have h2 : p (k + l + 1) ≤ γ * p (k + l) :=
      logConcave_succ_le hpos hlc hstep (k + l) (by omega) (by omega)
    calc p (k + (l + 1)) = p (k + l + 1) := rfl
      _ ≤ γ * p (k + l) := h2
      _ ≤ γ * (γ ^ l * p k) := mul_le_mul_of_nonneg_left h1 hγ0
      _ = γ ^ (l + 1) * p k := by ring

/-- Partial geometric sums are at most `(1-γ)⁻¹`. -/
theorem geom_sum_le_inv_one_sub (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (m : ℕ) :
    ∑ l ∈ Finset.range m, γ ^ l ≤ (1 - γ)⁻¹ := by
  have hs : Summable fun l : ℕ => γ ^ l := summable_geometric_of_lt_one hγ0 hγ1
  have h := hs.sum_le_tsum (Finset.range m) (fun l _ => by positivity)
  rwa [tsum_geometric_of_lt_one hγ0 hγ1] at h

/-- Partial sums of `l · γ^l` are at most `γ / (1-γ)²`. -/
theorem geom_weighted_sum_le (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (m : ℕ) :
    ∑ l ∈ Finset.range m, (l : ℝ) * γ ^ l ≤ γ / (1 - γ) ^ 2 := by
  have hnorm : ‖γ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hγ0]; exact hγ1
  have hs : Summable fun l : ℕ => (l : ℝ) * γ ^ l := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    simpa using h
  have h := hs.sum_le_tsum (Finset.range m) (fun l _ => by positivity)
  rwa [tsum_coe_mul_geometric_of_norm_lt_one hnorm] at h

/-- **KKO21 Lemma 2.18, first bound**: for a positive log-concave sequence
with `p (i+1) ≤ γ · p i`, `γ < 1`, every tail sum from `k ≥ i` satisfies
`∑_{j=k}^{n} p j ≤ p k / (1-γ)`. -/
theorem logConcave_tail_sum_le (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hpos : ∀ j, j ≤ n → 0 < p j)
    (hlc : ∀ j, j + 2 ≤ n → p j * p (j + 2) ≤ p (j + 1) ^ 2)
    (hstep : p (i + 1) ≤ γ * p i)
    {k : ℕ} (hik : i ≤ k) (hkn : k ≤ n) :
    ∑ j ∈ Finset.Icc k n, p j ≤ p k / (1 - γ) := by
  have hIcc : Finset.Icc k n = Finset.Ico k (n + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  calc ∑ l ∈ Finset.range (n + 1 - k), p (k + l)
      ≤ ∑ l ∈ Finset.range (n + 1 - k), γ ^ l * p k := by
        refine Finset.sum_le_sum fun l hl => ?_
        exact logConcave_le_geometric hγ0 hpos hlc hstep hik l
          (by have := Finset.mem_range.mp hl; omega)
    _ = (∑ l ∈ Finset.range (n + 1 - k), γ ^ l) * p k := by
        rw [← Finset.sum_mul]
    _ ≤ (1 - γ)⁻¹ * p k :=
        mul_le_mul_of_nonneg_right (geom_sum_le_inv_one_sub hγ0 hγ1 _)
          (hpos k hkn).le
    _ = p k / (1 - γ) := by rw [div_eq_inv_mul]

/-- **KKO21 Lemma 2.18, second bound**: for a positive log-concave sequence
with `p (i+1) ≤ γ · p i`, `γ < 1`,
`∑_{j=i+1}^{n} p j · j ≤ (p (i+1)/(1-γ)) · (i+1+γ/(1-γ))`. -/
theorem logConcave_tail_weighted_sum_le (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hpos : ∀ j, j ≤ n → 0 < p j)
    (hlc : ∀ j, j + 2 ≤ n → p j * p (j + 2) ≤ p (j + 1) ^ 2)
    (hstep : p (i + 1) ≤ γ * p i) (hin : i + 1 ≤ n) :
    ∑ j ∈ Finset.Icc (i + 1) n, p j * j
      ≤ p (i + 1) / (1 - γ) * (i + 1 + γ / (1 - γ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hp1 : 0 < p (i + 1) := hpos (i + 1) hin
  have hA : (0 : ℝ) ≤ p (i + 1) * ((i : ℝ) + 1) :=
    mul_nonneg hp1.le (by positivity)
  have hIcc : Finset.Icc (i + 1) n = Finset.Ico (i + 1) (n + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  calc ∑ l ∈ Finset.range (n + 1 - (i + 1)), p (i + 1 + l) * ↑(i + 1 + l)
      ≤ ∑ l ∈ Finset.range (n + 1 - (i + 1)),
          γ ^ l * p (i + 1) * ((i : ℝ) + 1 + l) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hd := logConcave_le_geometric hγ0 hpos hlc hstep (Nat.le_succ i) l
          (by have := Finset.mem_range.mp hl; omega)
        have hcast : ((i + 1 + l : ℕ) : ℝ) = (i : ℝ) + 1 + l := by
          push_cast; ring
        rw [hcast]
        exact mul_le_mul_of_nonneg_right hd (by positivity)
    _ = (p (i + 1) * ((i : ℝ) + 1)) * (∑ l ∈ Finset.range (n + 1 - (i + 1)), γ ^ l)
          + p (i + 1) * ∑ l ∈ Finset.range (n + 1 - (i + 1)), (l : ℝ) * γ ^ l := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ (p (i + 1) * ((i : ℝ) + 1)) * (1 - γ)⁻¹
          + p (i + 1) * (γ / (1 - γ) ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hγ0 hγ1 _) hA)
          (mul_le_mul_of_nonneg_left (geom_weighted_sum_le hγ0 hγ1 _) hp1.le)
    _ = p (i + 1) / (1 - γ) * (i + 1 + γ / (1 - γ)) := by
        field_simp

/-- **KKO21 Corollary 2.19** (sequence form): if a positive log-concave
probability sequence on `{0, …, n}` has mass at least `1 - ε` at `k`, with
`ε ≤ 1/10`, then its mean `q = ∑ j, p j · j` satisfies
`k (1-ε) ≤ q ≤ k (1+ε) + 3ε`.

KKO state this for `k ≥ 1`, but the hypothesis is not needed.  The upper
bound goes through the sharper intermediate `q ≤ k + 2ε`: the tail excess
`∑_{j>k} (j-k) p j` is at most `p (k+1) (γ/(1-γ)² + (1-γ)⁻¹) ≤ 2 p (k+1)`
for `γ = ε/(1-ε) ≤ 1/9`, and `p (k+1) ≤ ε`. -/
theorem logConcave_mean_est {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10)
    (hpos : ∀ j, j ≤ n → 0 < p j)
    (hlc : ∀ j, j + 2 ≤ n → p j * p (j + 2) ≤ p (j + 1) ^ 2)
    (hsum : ∑ j ∈ Finset.range (n + 1), p j = 1)
    {k : ℕ} (hkn : k ≤ n) (hpk : 1 - ε ≤ p k) :
    (k : ℝ) * (1 - ε) ≤ (∑ j ∈ Finset.range (n + 1), p j * j) ∧
      (∑ j ∈ Finset.range (n + 1), p j * j) ≤ k * (1 + ε) + 3 * ε := by
  have hnonneg : ∀ j ∈ Finset.range (n + 1), 0 ≤ p j * (j : ℝ) := fun j hj =>
    mul_nonneg (hpos j (by have := Finset.mem_range.mp hj; omega)).le
      (by positivity)
  constructor
  · -- lower bound: the single term at `k`
    have h1 : p k * (k : ℝ) ≤ ∑ j ∈ Finset.range (n + 1), p j * j :=
      Finset.single_le_sum hnonneg (Finset.mem_range.mpr (by omega))
    nlinarith [mul_le_mul_of_nonneg_right hpk (Nat.cast_nonneg k)]
  · -- upper bound
    -- split the sum at `k`
    have hsplit : ∑ j ∈ Finset.range (n + 1), p j * j
        = (∑ j ∈ Finset.Ico 0 (k + 1), p j * j)
          + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * j := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun j => p j * (j : ℝ))
          (by omega : 0 ≤ k + 1) (by omega : k + 1 ≤ n + 1)]
    have hone : (∑ j ∈ Finset.Ico 0 (k + 1), p j)
        + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j = 1 := by
      rw [Finset.sum_Ico_consecutive p (by omega : 0 ≤ k + 1)
        (by omega : k + 1 ≤ n + 1), ← Finset.range_eq_Ico]
      exact hsum
    have hp1 : ∑ j ∈ Finset.Ico 0 (k + 1), p j * j
        ≤ (k : ℝ) * ∑ j ∈ Finset.Ico 0 (k + 1), p j := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j ≤ k := by have := (Finset.mem_Ico.mp hj).2; omega
      have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj'
      have hpj : (0 : ℝ) ≤ p j := (hpos j (by omega)).le
      nlinarith [mul_nonneg hpj (sub_nonneg.mpr hjk)]
    have hp2 : ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * j
        = (k : ℝ) * (∑ j ∈ Finset.Ico (k + 1) (n + 1), p j)
          + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * ((j : ℝ) - k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- the tail excess is at most 2ε
    have hD : ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * ((j : ℝ) - k) ≤ 2 * ε := by
      rcases Nat.lt_or_ge k n with hkn' | hkn'
      · -- k + 1 ≤ n: geometric tail
        have hk1n : k + 1 ≤ n := hkn'
        have hpk1 : p (k + 1) ≤ ε := by
          have hsub : p k + p (k + 1) ≤ ∑ j ∈ Finset.range (n + 1), p j := by
            have hss : ({k, k + 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with h | h <;> exact Finset.mem_range.mpr (by omega)
            calc p k + p (k + 1)
                = ∑ j ∈ ({k, k + 1} : Finset ℕ), p j :=
                  (Finset.sum_pair (by omega : k ≠ k + 1)).symm
              _ ≤ ∑ j ∈ Finset.range (n + 1), p j :=
                  Finset.sum_le_sum_of_subset_of_nonneg hss fun j hj _ =>
                    (hpos j (by have := Finset.mem_range.mp hj; omega)).le
          rw [hsum] at hsub
          linarith
        set γ : ℝ := ε / (1 - ε) with hγdef
        have hε1 : (0 : ℝ) < 1 - ε := by linarith
        have hγ0 : 0 ≤ γ := div_nonneg hε0 hε1.le
        have hγ9 : γ ≤ 1 / 9 := by
          rw [hγdef, div_le_iff₀ hε1]
          linarith
        have hγ1 : γ < 1 := by linarith
        have hstep : p (k + 1) ≤ γ * p k := by
          have h1 : γ * (1 - ε) = ε := by
            rw [hγdef]
            field_simp
          have h2 : γ * (1 - ε) ≤ γ * p k := mul_le_mul_of_nonneg_left hpk hγ0
          linarith
        have hpk1' : (0 : ℝ) ≤ p (k + 1) := (hpos (k + 1) hk1n).le
        rw [Finset.sum_Ico_eq_sum_range]
        calc ∑ l ∈ Finset.range (n + 1 - (k + 1)),
              p (k + 1 + l) * ((↑(k + 1 + l) : ℝ) - k)
            ≤ ∑ l ∈ Finset.range (n + 1 - (k + 1)),
                γ ^ l * p (k + 1) * ((l : ℝ) + 1) := by
              refine Finset.sum_le_sum fun l hl => ?_
              have hln : k + 1 + l ≤ n := by
                have := Finset.mem_range.mp hl; omega
              have hd := logConcave_le_geometric hγ0 hpos hlc hstep
                (Nat.le_succ k) l hln
              have hcast : ((k + 1 + l : ℕ) : ℝ) - k = (l : ℝ) + 1 := by
                push_cast; ring
              rw [hcast]
              exact mul_le_mul_of_nonneg_right hd (by positivity)
          _ = p (k + 1) * (∑ l ∈ Finset.range (n + 1 - (k + 1)), (l : ℝ) * γ ^ l)
                + p (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), γ ^ l := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun l _ => by ring
          _ ≤ p (k + 1) * (γ / (1 - γ) ^ 2) + p (k + 1) * (1 - γ)⁻¹ :=
              add_le_add
                (mul_le_mul_of_nonneg_left (geom_weighted_sum_le hγ0 hγ1 _) hpk1')
                (mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hγ0 hγ1 _)
                  hpk1')
          _ ≤ 2 * ε := by
              have h89 : (8 : ℝ) / 9 ≤ 1 - γ := by linarith
              have hsq : (0 : ℝ) < (1 - γ) ^ 2 := by positivity
              have ha : γ / (1 - γ) ^ 2 ≤ 9 / 64 := by
                rw [div_le_iff₀ hsq]
                nlinarith
              have hb : (1 - γ)⁻¹ ≤ 9 / 8 := by
                rw [← one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - γ)]
                linarith
              linarith [mul_le_mul_of_nonneg_left ha hpk1',
                mul_le_mul_of_nonneg_left hb hpk1', hpk1]
      · -- k = n: empty tail
        have hempty : Finset.Ico (k + 1) (n + 1) = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [hempty, Finset.sum_empty]
        linarith
    -- combine the pieces
    have hq : ∑ j ∈ Finset.range (n + 1), p j * j ≤ (k : ℝ) + 2 * ε := by
      calc ∑ j ∈ Finset.range (n + 1), p j * j
          = (∑ j ∈ Finset.Ico 0 (k + 1), p j * j)
            + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * j := hsplit
        _ ≤ (k : ℝ) * (∑ j ∈ Finset.Ico 0 (k + 1), p j)
            + ((k : ℝ) * (∑ j ∈ Finset.Ico (k + 1) (n + 1), p j)
              + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * ((j : ℝ) - k)) :=
            add_le_add hp1 (le_of_eq hp2)
        _ = (k : ℝ) * ((∑ j ∈ Finset.Ico 0 (k + 1), p j)
              + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j)
            + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * ((j : ℝ) - k) := by
            ring
        _ = (k : ℝ) + ∑ j ∈ Finset.Ico (k + 1) (n + 1), p j * ((j : ℝ) - k) := by
            rw [hone, mul_one]
        _ ≤ (k : ℝ) + 2 * ε := by linarith
    have hkε : (0 : ℝ) ≤ (k : ℝ) * ε := mul_nonneg (Nat.cast_nonneg k) hε0
    linarith

end LogConcave

end Bernoulli
end TSPGap

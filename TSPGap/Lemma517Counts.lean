/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleSetup
import TSPGap.Lemma57

/-!
# The count estimates of KKO22 Lemma 5.17

Standalone wrappers, each stated over its own mean range so that the kernel
never re-derives one.

| result | mean range |
| --- | --- |
| `P[N = 4] ≥ 0.028` | `[3.0289, 3.502]` |
| baseline-one `P[≤2] ≥ 0.499`, `P[≥2] ≥ 0.39` | `[1.499, 2.002]` |
| baseline-one sharp `P[= 2] ≥ 0.058` | `[1.49, 2.94]` |
| ordinary `P[≤1] ≥ 0.249`, `P[≥1] ≥ 0.63` | `[0.9989, 1.502]` |

⚠️ **KKO's `0.029` is not available at these ranges.**  Applying
`poi_le_probCount` at `k = 4` — directly, unshifted — the mean stays below
`4`, so the tail factor is `x ^ (0 : ℝ) = 1` and the bound is just
`poi (p − l) (4 − l)`.  The four admissible `l` give roughly
`0.170, 0.183, 0.189, 0.0281`; the tight branch is `l = 3`, and it yields
`0.028`, not `0.029`.  That is still enough:
`0.49 · 0.028 · 0.13 = 0.0017836 > 0.0015 = 3ε₁ᐟ₂`.

KKO's `0.0582` at the two-count, by contrast, **is** available here (minus
rounding): it needs Hoeffding's extremal theorem rather than the Poisson
surrogate, as the sharp `k = 1` specialization `probCount_one_ge`, fed
through the residual shift.

## The two `ThreeCell` closures

The tails feed `three_cell_bound_shifted` as the products
`0.499 · 0.39 ≥ 0.194` (giving `0.13`) and `0.249 · 0.63 ≥ 0.15` (giving
`0.11`); the closures `weightMass_two_two_ge` and `weightMass_one_one_ge`
package both, division-free.

## Main results

* `probCount_four_ge` — the `0.028` point mass.
* `weightMass_le_one_ge`, `weightMass_one_le_ge` — the ordinary tails.
* `probCount_succ_update_zero`, `sum_update_zero` — the residual shift.
* `weightMass_le_two_ge_of_baseline`, `weightMass_two_le_ge_of_baseline` —
  the shifted tails, on an a.s. baseline of one.
* `probCount_one_ge` — the sharp `0.058` point mass, from Hoeffding's
  extremal theorem.
* `weightMass_eq_two_ge_of_baseline` — its weight-level, baseline-one form.
* `weightMass_two_two_ge`, `weightMass_one_one_ge` — the division-free
  three-cell closures at `0.13` and `0.11`.
-/

namespace TSPGap
open Finset

/-! ### Exponential bounds -/

theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hlow : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h : 1 / Real.exp (-x) ≤ 1 / (1 - x) := one_div_le_one_div_of_le hpos hlow
  rwa [Real.exp_neg, one_div, inv_inv] at h

theorem exp_1502_le : Real.exp 1.502 ≤ 5 := by
  have h1 : Real.exp 1.5 ≤ 4.5 := exp_three_halves_le
  have h2' : Real.exp 0.002 ≤ 1.01 := by
    refine le_trans (exp_le_inv_one_sub (by norm_num)) ?_
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 0.002)]
    norm_num
  have hsplit : Real.exp 1.502 = Real.exp 1.5 * Real.exp 0.002 := by
    rw [← Real.exp_add]; norm_num
  have hmul := mul_le_mul h1 h2' (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 4.5)
  rw [hsplit]
  linarith

theorem exp_2502_le : Real.exp 2.502 ≤ 15 := by
  have h1 : Real.exp 2 ≤ 7.39 := exp_two_le
  have h2' : Real.exp 0.502 ≤ 2.01 := by
    refine le_trans (exp_le_inv_one_sub (by norm_num)) ?_
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 0.502)]
    norm_num
  have hsplit : Real.exp 2.502 = Real.exp 2 * Real.exp 0.502 := by
    rw [← Real.exp_add]; norm_num
  have hmul := mul_le_mul h1 h2' (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 7.39)
  rw [hsplit]
  linarith

theorem exp_3502_le : Real.exp 3.502 ≤ 37 := by
  have h1 : Real.exp 2 ≤ 7.39 := exp_two_le
  have h2 : Real.exp 1.502 ≤ 5 := exp_1502_le
  have hsplit : Real.exp 3.502 = Real.exp 2 * Real.exp 1.502 := by
    rw [← Real.exp_add]; norm_num
  have hmul := mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 7.39)
  rw [hsplit]
  linarith

/-- `exp (-y) ≥ 1/C` whenever `y ≤ Y` and `exp Y ≤ C`. -/
theorem inv_le_exp_neg {y Y C : ℝ} (hyY : y ≤ Y)
    (hC : Real.exp Y ≤ C) : 1 / C ≤ Real.exp (-y) := by
  have h1 : Real.exp y ≤ C := le_trans (Real.exp_le_exp.mpr hyY) hC
  have h : 1 / C ≤ 1 / Real.exp y := one_div_le_one_div_of_le (Real.exp_pos _) h1
  rwa [Real.exp_neg, ← one_div]

/-- The shape every branch of the `k = 4` estimate takes. -/
theorem poi_ge_of_bounds {y c : ℝ} {m : ℕ} (hy0 : 0 ≤ y)
    (hc : c ≤ Real.exp (-y))
    (hb : (0.028 : ℝ) * (m.factorial : ℝ) ≤ c * y ^ m) :
    (0.028 : ℝ) ≤ Bernoulli.poi y m := by
  rw [Bernoulli.poi, le_div_iff₀ (by positivity)]
  have hstep : c * y ^ m ≤ Real.exp (-y) * y ^ m :=
    mul_le_mul_of_nonneg_right hc (pow_nonneg hy0 m)
  linarith

/-! ### The `0.028` point mass at count four -/

theorem probCount_four_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 3.0289 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 3.502) :
    (0.028 : ℝ) ≤ Bernoulli.probCount q 4 := by
  classical
  obtain ⟨l, hl4, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 4
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  set p : ℝ := ∑ i, q i with hp
  have hmax : max (p - ((4 : ℕ) : ℝ)) 0 = 0 := by
    refine max_eq_right ?_
    push_cast
    linarith
  rw [hmax, Real.rpow_zero, mul_one]
  interval_cases l
  · -- `l = 0`
    have key : (0.028 : ℝ) ≤ Bernoulli.poi p 4 := by
      refine poi_ge_of_bounds (by linarith)
        (inv_le_exp_neg (show p ≤ 3.502 by linarith) exp_3502_le) ?_
      have hpow : (3.0289 : ℝ) ^ 4 ≤ p ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
      norm_num
      nlinarith [hpow]
    simpa using key
  · -- `l = 1`
    have key : (0.028 : ℝ) ≤ Bernoulli.poi (p - 1) 3 := by
      refine poi_ge_of_bounds (by linarith)
        (inv_le_exp_neg (show p - 1 ≤ 2.502 by linarith) exp_2502_le) ?_
      have hpow : (2.0289 : ℝ) ^ 3 ≤ (p - 1) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 3
      norm_num
      nlinarith [hpow]
    simpa using key
  · -- `l = 2`
    have key : (0.028 : ℝ) ≤ Bernoulli.poi (p - 2) 2 := by
      refine poi_ge_of_bounds (by linarith)
        (inv_le_exp_neg (show p - 2 ≤ 1.502 by linarith) exp_1502_le) ?_
      have hpow : (1.0289 : ℝ) ^ 2 ≤ (p - 2) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 2
      norm_num
      nlinarith [hpow]
    simpa using key
  · -- `l = 3`, the tight branch: `y (1 − y) ≥ 0.028` on `[0.0289, 0.502]`
    have key : (0.028 : ℝ) ≤ Bernoulli.poi (p - 3) 1 := by
      refine poi_ge_of_bounds (by linarith) (c := 1 - (p - 3)) ?_ ?_
      · have := Real.add_one_le_exp (-(p - 3))
        linarith
      · norm_num
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p - 3 - 0.0289)
          (by linarith : (0:ℝ) ≤ 0.502 - (p - 3))]
    simpa using key
  · -- `l = 4` is impossible: the mean stays below `4`
    exfalso
    push_cast at hlp
    linarith

/-! ### The ordinary tails -/

section Tails

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P[N ≤ 1] ≥ 0.249` for mean at most `1.502` — Markov. -/
theorem weightMass_le_one_ge {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) {F : Finset ι} (hmean : expCard w F ≤ 1.502) :
    (0.249 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card ≤ 1) := by
  have h := two_mul_weightMass_le_one_ge hnn F
  rw [htot] at h
  linarith

/-- `P[N ≥ 1] ≥ 0.63` for mean at least `0.9989`. -/
theorem weightMass_one_le_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hmean : 0.9989 ≤ expCard w F) :
    (0.63 : ℝ) ≤ weightMass w (fun T => 1 ≤ (T ∩ F).card) := by
  have h := one_sub_exp_le_weightMass_one_le hst hr hnn htot F
  have hlow : (2.7152 : ℝ) ≤ Real.exp 0.9989 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : (1 : ℝ) - 0.0011 ≤ Real.exp (-0.0011) := by
      have := Real.add_one_le_exp (-(0.0011 : ℝ))
      linarith
    have hsplit : Real.exp 0.9989 = Real.exp 1 * Real.exp (-0.0011) := by
      rw [← Real.exp_add]; norm_num
    have hmul := mul_le_mul h1.le h2 (by norm_num : (0:ℝ) ≤ 1 - 0.0011)
      (Real.exp_pos (1:ℝ)).le
    rw [hsplit]
    nlinarith [hmul]
  have hmono : Real.exp (-(expCard w F)) ≤ Real.exp (-(0.9989 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hval : Real.exp (-(0.9989 : ℝ)) ≤ 0.37 := by
    have h : 1 / Real.exp 0.9989 ≤ 1 / 2.7152 :=
      one_div_le_one_div_of_le (by norm_num) hlow
    have hnum : (1 : ℝ) / 2.7152 ≤ 0.37 := by norm_num
    rw [Real.exp_neg, ← one_div]
    linarith
  linarith

/-- `P[N ≤ 2] ≥ 0.499` for mean at most `2.002`, when `N ≥ 1` always —
Markov on the residual. -/
theorem two_mul_weightMass_three_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {F : Finset ι} (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) :
    2 * weightMass w (fun T => 3 ≤ (T ∩ F).card) ≤ expCard w F - totalMass w := by
  classical
  rw [weightMass, expCard, totalMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · have hb := hbase S h0
    have hnn' := hnn S
    by_cases h : 3 ≤ (S ∩ F).card
    · rw [if_pos h]
      have : (3 : ℝ) ≤ ((S ∩ F).card : ℝ) := by exact_mod_cast h
      nlinarith [hnn', this]
    · rw [if_neg h, mul_zero]
      have : (1 : ℝ) ≤ ((S ∩ F).card : ℝ) := by exact_mod_cast hb
      nlinarith [hnn', this]

theorem weightMass_le_two_ge_of_baseline {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) (hmean : expCard w F ≤ 2.002) :
    (0.499 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card ≤ 2) := by
  have h := two_mul_weightMass_three_le hnn hbase
  rw [htot] at h
  have hnot := weightMass_not w (fun T => 3 ≤ (T ∩ F).card)
  have hcongr : weightMass w (fun T => ¬ 3 ≤ (T ∩ F).card)
      = weightMass w (fun T => (T ∩ F).card ≤ 2) :=
    weightMass_congr fun T => by omega
  rw [hcongr, htot] at hnot
  linarith

end Tails

/-! ### The residual shift

Under an a.s. baseline of one the rank law has a **deterministic coordinate**:
`P[N = 0] = ∏ (1 − qᵢ) = 0` forces some `q_j = 1`.  Setting that coordinate
to zero gives the residual law `q⁰ := Function.update q j 0`, and the whole
count sequence shifts: `P_q[N = k + 1] = P_{q⁰}[N = k]`, with
`∑ q⁰ = ∑ q − 1`.  The `0.39` tail consumes the shift at `k = 0`; the `0.058`
estimate will consume it at `k = 1`.  ⚠️ The shift is what preserves the
baseline constraint — applying Hoeffding to the original law would lose it. -/

section Shift

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P[N = 0] = 0` forces a deterministic coordinate. -/
theorem exists_eq_one_of_probCount_zero {q : ι → ℝ}
    (h0 : Bernoulli.probCount q 0 = 0) : ∃ j, q j = 1 := by
  classical
  rw [probCount_zero_eq_prod] at h0
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨j, by linarith⟩

/-- The residual mean: `∑ q⁰ = ∑ q − q j`. -/
theorem sum_update_zero (q : ι → ℝ) (j : ι) :
    ∑ i, Function.update q j 0 i = (∑ i, q i) - q j := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), zero_add,
    Finset.sdiff_singleton_eq_erase, eq_sub_iff_add_eq,
    Finset.sum_erase_add _ _ (Finset.mem_univ j)]

omit [Fintype ι] in
/-- The residual coordinates stay in `[0, 1]`. -/
theorem update_zero_mem_Icc {q : ι → ℝ} (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (j : ι) : ∀ i, Function.update q j 0 i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  rcases eq_or_ne i j with rfl | hij
  · rw [Function.update_self]
    exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
  · rw [Function.update_of_ne hij]
    exact hq i

/-- **The residual shift**: a deterministic coordinate shifts the whole count
sequence down by one.  Atoms of size `k + 1` missing `j` vanish on the left,
atoms of size `k` containing `j` vanish on the right, and `t ↦ t.erase j`
matches what survives. -/
theorem probCount_succ_update_zero {q : ι → ℝ} {j : ι} (hj : q j = 1) (k : ℕ) :
    Bernoulli.probCount q (k + 1)
      = Bernoulli.probCount (Function.update q j 0) k := by
  classical
  rw [Bernoulli.probCount_def, Bernoulli.probCount_def]
  have hvanL : ∀ t ∈ Finset.univ.powersetCard (k + 1),
      Bernoulli.atomProb q t ≠ 0 → j ∈ t := by
    intro t _ hne
    by_contra hjt
    refine hne ?_
    unfold Bernoulli.atomProb
    rw [Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjt⟩)
      (by rw [hj]; ring), mul_zero]
  have hvanR : ∀ s ∈ Finset.univ.powersetCard k,
      Bernoulli.atomProb (Function.update q j 0) s ≠ 0 → j ∉ s := by
    intro s _ hne hjs
    refine hne ?_
    unfold Bernoulli.atomProb
    rw [Finset.prod_eq_zero hjs (by rw [Function.update_self]), zero_mul]
  rw [← Finset.sum_filter_of_ne hvanL, ← Finset.sum_filter_of_ne hvanR]
  refine Finset.sum_bij' (fun t _ => t.erase j) (fun s _ => insert j s)
    ?_ ?_ ?_ ?_ ?_
  · -- maps into the target family
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
    obtain ⟨⟨-, htk⟩, hjt⟩ := ht
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.notMem_erase j t⟩
    rw [Finset.card_erase_of_mem hjt, htk]
    omega
  · -- maps back
    intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨-, hsk⟩, hjs⟩ := hs
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self j s⟩
    rw [Finset.card_insert_of_notMem hjs, hsk]
  · -- left inverse
    intro t ht
    rw [Finset.mem_filter] at ht
    exact Finset.insert_erase ht.2
  · -- right inverse
    intro s hs
    rw [Finset.mem_filter] at hs
    exact Finset.erase_insert hs.2
  · -- values
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
    obtain ⟨⟨-, -⟩, hjt⟩ := ht
    unfold Bernoulli.atomProb
    have h1 : ∏ i ∈ t.erase j, Function.update q j 0 i = ∏ i ∈ t, q i := by
      rw [← Finset.mul_prod_erase t q hjt, hj, one_mul]
      exact Finset.prod_congr rfl fun i hi =>
        Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
    have hmem : j ∈ Finset.univ \ t.erase j :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, Finset.notMem_erase j t⟩
    have hset : (Finset.univ \ t.erase j).erase j = Finset.univ \ t := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyj, hy'⟩ := Finset.mem_erase.mp hy
        obtain ⟨-, hyt⟩ := Finset.mem_sdiff.mp hy'
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y,
          fun hc => hyt (Finset.mem_erase.mpr ⟨hyj, hc⟩)⟩
      · intro hy
        obtain ⟨-, hyt⟩ := Finset.mem_sdiff.mp hy
        refine Finset.mem_erase.mpr ⟨fun hc => hyt ?_, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ y, fun hc => hyt (Finset.mem_of_mem_erase hc)⟩⟩
        rw [hc]
        exact hjt
    have h2 : ∏ i ∈ Finset.univ \ t.erase j, (1 - Function.update q j 0 i)
        = ∏ i ∈ Finset.univ \ t, (1 - q i) := by
      rw [← Finset.mul_prod_erase _ _ hmem, hset, Function.update_self,
        sub_zero, one_mul]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := fun hc => (Finset.mem_sdiff.mp hi).2 (hc ▸ hjt)
      rw [Function.update_of_ne hij]
    rw [h1, h2]

/-- `P[N = 1]` collapses to the residual `P[N = 0]` — the shift at `k = 0`,
written out as the product over the other coordinates. -/
theorem probCount_one_eq_of_zero {q : ι → ℝ} {j : ι} (hj : q j = 1) :
    Bernoulli.probCount q 1 = ∏ k ∈ Finset.univ.erase j, (1 - q k) := by
  classical
  have h := probCount_succ_update_zero hj 0
  rw [zero_add] at h
  rw [h, probCount_zero_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    Function.update_self, sub_zero, one_mul]
  exact Finset.prod_congr rfl fun i hi => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- With a deterministic success removed, `P[N = 1]` is at most `e^{-(p-1)}`. -/
theorem probCount_one_le_exp_of_zero {q : ι → ℝ}
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h0 : Bernoulli.probCount q 0 = 0) :
    Bernoulli.probCount q 1 ≤ Real.exp (-((∑ i, q i) - 1)) := by
  classical
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero h0
  have h := probCount_succ_update_zero hj 0
  rw [zero_add] at h
  rw [h]
  have hle := probCount_zero_le_exp (Function.update q j 0)
    fun i => (update_zero_mem_Icc hq j i).2
  rwa [sum_update_zero, hj] at hle

end Shift

/-! ### The shifted lower tail -/

/-- `P[N ≥ 2] ≥ 0.39` for mean at least `1.499`, when `N ≥ 1` always. -/
theorem weightMass_two_le_ge_of_baseline {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : Finset ι → ℝ} {r : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {F : Finset ι} (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hmean : 1.499 ≤ expCard w F) :
    (0.39 : ℝ) ≤ weightMass w (fun T => 2 ≤ (T ∩ F).card) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmeanq : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  -- the baseline kills the empty layer
  have h0 : Bernoulli.probCount q 0 = 0 := by
    rw [← hlaw 0]
    refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans
      (weightMass_false w)
    intro S hS
    have := hbase S hS
    exact ⟨fun hc => by omega, False.elim⟩
  have h1 := probCount_one_le_exp_of_zero (fun i => ⟨(hq i).1.le, (hq i).2⟩) h0
  -- the two low layers are the complement of `2 ≤ N`
  have hsplit : weightMass w (fun T => 2 ≤ (T ∩ F).card)
      = 1 - Bernoulli.probCount q 0 - Bernoulli.probCount q 1 := by
    have hnot := weightMass_not w (fun T => 2 ≤ (T ∩ F).card)
    have hlow : weightMass w (fun T => ¬ 2 ≤ (T ∩ F).card)
        = weightMass w (fun T => (T ∩ F).card = 0)
          + weightMass w (fun T => (T ∩ F).card = 1) := by
      have hor := weightMass_or w (fun T => (T ∩ F).card = 0)
        (fun T => (T ∩ F).card = 1)
      have hand : weightMass w (fun T => (T ∩ F).card = 0 ∧ (T ∩ F).card = 1) = 0 := by
        refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans
          (weightMass_false w)
        exact ⟨fun h => by omega, False.elim⟩
      have hcongr : weightMass w (fun T => ¬ 2 ≤ (T ∩ F).card)
          = weightMass w (fun T => (T ∩ F).card = 0 ∨ (T ∩ F).card = 1) :=
        weightMass_congr fun T => by omega
      rw [hcongr]
      linarith
    rw [hlow, hlaw 0, hlaw 1] at hnot
    rw [htot] at hnot
    linarith
  -- `exp(-(p-1)) ≤ 0.61`
  have hexp : Real.exp (-((∑ i, q i) - 1)) ≤ 0.61 := by
    have hmono : Real.exp (-((∑ i, q i) - 1)) ≤ Real.exp (-(0.499 : ℝ)) :=
      Real.exp_le_exp.mpr (by rw [← hmeanq]; linarith)
    have hlow : (1.646 : ℝ) ≤ Real.exp 0.499 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hsq : Real.exp 0.499 * Real.exp 0.499 = Real.exp 0.998 := by
        rw [← Real.exp_add]; norm_num
      have h2 : Real.exp 0.998 = Real.exp 1 * Real.exp (-0.002) := by
        rw [← Real.exp_add]; norm_num
      have h3 : (1 : ℝ) - 0.002 ≤ Real.exp (-0.002) := by
        have := Real.add_one_le_exp (-(0.002 : ℝ))
        linarith
      have hpos : (0 : ℝ) < Real.exp 0.499 := Real.exp_pos _
      nlinarith [hsq, h2, h3, h1, hpos, Real.exp_pos (-(0.002:ℝ)),
        sq_nonneg (Real.exp 0.499 - 1.646)]
    have hval : Real.exp (-(0.499 : ℝ)) ≤ 0.61 := by
      have h : 1 / Real.exp 0.499 ≤ 1 / 1.646 :=
        one_div_le_one_div_of_le (by norm_num) hlow
      rw [Real.exp_neg, ← one_div]
      have hnum : (1 : ℝ) / 1.646 ≤ 0.61 := by norm_num
      linarith
    linarith
  rw [hsplit, h0]
  linarith

/-! ### The sharp count-one estimate

`poi_le_probCount` at `k = 1` cannot reach `0.058`: the target value is
*attained* (two Bernoullis at `0.97`), so no analytic surrogate beats it.
Hoeffding's extremal theorem itself does.  Reduce to a three-valued minimizer
with `ℓ` sure successes and `R` coordinates equal to `x`; the mean range
forces `ℓ ≤ 1`, and every configuration clears `0.058`:

* `ℓ = 1`: `(1 − x)^R ≥ 1 − Rx = 2 − p ≥ 0.06` (Bernoulli's inequality);
* `ℓ = 0, R = 1`: the value is `x = p ≥ 0.49`;
* `ℓ = 0, R = 2`: `2x(1 − x) = p(1 − p/2) ≥ 0.0582`, the sharp extremizer,
  tight at `p = 1.94`;
* `ℓ = 0, R ≥ 3, p ≤ 1`: Fact 2.20 at `k = 1` gives `p·e^{−p} ≥ 0.18`;
* `ℓ = 0, R ≥ 3, p > 1`: Fact 2.20 at `k = 2` gives
  `p(1 − p/3)e^{−p} ≥ 0.094`. -/

theorem exp_194_le : Real.exp 1.94 ≤ 6.972 := by
  have h1 : Real.exp 2 ≤ 7.39 := exp_two_le
  have h2 : (1.06 : ℝ) ≤ Real.exp 0.06 := by
    have := Real.add_one_le_exp (0.06 : ℝ)
    linarith
  have hsplit : Real.exp 1.94 * Real.exp 0.06 = Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  have h3 : Real.exp 1.94 * 1.06 ≤ Real.exp 1.94 * Real.exp 0.06 :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  rw [hsplit] at h3
  linarith

/-- The two-Bernoulli extremizer: at mean `p = 2x ∈ [0.49, 1.94]`,
`2x(1 − x) ≥ 0.058`, tight at the right endpoint (`0.0582`). -/
theorem two_bernoulli_sharp {p x : ℝ} (hpx : p = 2 * x) (h1 : 0.49 ≤ p)
    (h2 : p ≤ 1.94) : (0.058 : ℝ) ≤ 2 * (x * (1 - x)) := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 0.245)
    (by linarith : (0:ℝ) ≤ 0.97 - x)]

/-- The `R ≥ 3, p ≤ 1` branch: `p·B ≥ 0.058` once `B ≥ e^{−p}`. -/
theorem pexp_low_bound {p B : ℝ} (hp1 : 0.49 ≤ p) (hp2 : p ≤ 1)
    (hB : Real.exp (-p) ≤ B) : (0.058 : ℝ) ≤ p * B := by
  have hexp1 : Real.exp 1 ≤ 2.72 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : (1 : ℝ) / 2.72 ≤ B := le_trans (inv_le_exp_neg hp2 hexp1) hB
  have h2 := mul_le_mul hp1 h1 (by norm_num) (by linarith)
  linarith

/-- The `R ≥ 3, p > 1` branch: `p·B·c ≥ 0.058` once `B ≥ e^{−p}` and
`c ≥ 1 − p/3`. -/
theorem pexp_high_bound {p B c : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 1.94)
    (hB : Real.exp (-p) ≤ B) (hc : 1 - p / 3 ≤ c) :
    (0.058 : ℝ) ≤ p * (B * c) := by
  have hexp : (1 : ℝ) / 6.972 ≤ B := le_trans (inv_le_exp_neg hp2 exp_194_le) hB
  have hq : (0.66 : ℝ) ≤ p * (1 - p / 3) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p - 1)
      (by linarith : (0:ℝ) ≤ 1.94 - p)]
  have hc0 : (0 : ℝ) ≤ 1 - p / 3 := by linarith
  have hmul : (1 : ℝ) / 6.972 * (1 - p / 3) ≤ B * c :=
    mul_le_mul hexp hc hc0 (by linarith)
  have hstep : p * ((1 : ℝ) / 6.972 * (1 - p / 3)) ≤ p * (B * c) :=
    mul_le_mul_of_nonneg_left hmul (by linarith)
  nlinarith [hq, hstep]

/-- **The sharp `k = 1` point mass** (KKO21 Theorem 2.15, specialized):
`P[N = 1] ≥ 0.058` for mean in `[0.49, 1.94]`. -/
theorem probCount_one_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 0.49 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 1.94) :
    (0.058 : ℝ) ≤ Bernoulli.probCount q 1 := by
  classical
  set p : ℝ := ∑ i, q i with hpdef
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hsn : p ≤ (Fintype.card ι : ℝ) := by
    rw [hpdef]
    calc ∑ i, q i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hq i).2
      _ = Fintype.card ι := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  obtain ⟨w, hwIcc, hwsum, ⟨x, hx0, hx1, h3v⟩, hwmin⟩ :=
    Bernoulli.exists_min_three_valued (fun m => if m = 1 then (1 : ℝ) else 0)
      p hp0 hsn
  have hwq : Bernoulli.probCount w 1 ≤ Bernoulli.probCount q 1 := by
    have h := hwmin q hq hpdef.symm
    rwa [Bernoulli.expect_indicator, Bernoulli.expect_indicator] at h
  refine le_trans ?_ hwq
  -- the three-valued configuration
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
    have ha := hOw i hiO
    have hb := hZw i hiZ
    rw [ha] at hb
    norm_num at hb
  set R : ℕ := (Finset.univ \ (O ∪ Z)).card with hRdef
  have hpl : p = (O.card : ℝ) + (R : ℝ) * x := by
    rw [← hwsum]
    exact Bernoulli.sum_threeValued w O Z x hOw hZw hxw hOZ
  have hlp : (O.card : ℝ) ≤ p := by
    have : (0 : ℝ) ≤ (R : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0.le
    linarith [hpl]
  have hlk : O.card ≤ 1 := by
    by_contra hcon
    have hc : ((2 : ℕ) : ℝ) ≤ (O.card : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ O.card)
    push_cast at hc
    linarith
  have hpc := Bernoulli.probCount_threeValued w O Z x hOw hZw hxw hOZ 1 hlk
  rw [← hRdef] at hpc
  rcases (by omega : O.card = 0 ∨ O.card = 1) with hl | hl
  · -- no sure successes: the value is `R x (1 − x)^{R−1}`
    rw [hl] at hpc hpl
    simp only [Nat.sub_zero] at hpc
    rw [Nat.choose_one_right, pow_one] at hpc
    norm_num at hpl
    have hR0 : R ≠ 0 := by
      intro hc
      rw [hc] at hpl
      norm_num at hpl
      linarith
    rcases (by omega : R = 1 ∨ R = 2 ∨ 3 ≤ R) with hR | hR | hR
    · -- a single Bernoulli: the value is `p` itself
      rw [hR] at hpc hpl
      norm_num at hpc hpl
      rw [hpc]
      linarith
    · -- the sharp extremizer
      rw [hR] at hpc hpl
      have hpc2 : Bernoulli.probCount w 1 = 2 * (x * (1 - x)) := by
        rw [hpc]
        norm_num
      push_cast at hpl
      rw [hpc2]
      exact two_bernoulli_sharp hpl h1 h2
    · -- `R ≥ 3`: Fact 2.20
      have hRne : ((R : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
        exact this.ne'
      have h3R : (3 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hxval : x = p / (R : ℝ) := by
        field_simp
        linarith [hpl]
      rw [hpc, hxval]
      have hcan : (R : ℝ) * (p / (R : ℝ)) = p := by field_simp
      rcases le_or_gt p 1 with hple | hpgt
      · -- Fact 2.20 at `k = 1`
        have hfact := Bernoulli.exp_neg_le_prod_mul_pow (t := R) (k := 1)
          le_rfl (by omega) (p := p) (by push_cast; linarith)
          (by push_cast; linarith)
        rw [show Finset.Icc 1 (1 - 1) = (∅ : Finset ℕ) from rfl,
          Finset.prod_empty, one_mul] at hfact
        have hgoal : (R : ℝ) * (p / (R : ℝ) * (1 - p / (R : ℝ)) ^ (R - 1))
            = p * (1 - p / (R : ℝ)) ^ (R - 1) := by
          rw [← mul_assoc, hcan]
        rw [hgoal]
        exact pexp_low_bound h1 hple hfact
      · -- Fact 2.20 at `k = 2`
        have hfact := Bernoulli.exp_neg_le_prod_mul_pow (t := R) (k := 2)
          (by omega) (by omega) (p := p) (by push_cast; linarith)
          (by push_cast; linarith)
        rw [show (2 : ℕ) - 1 = 1 from rfl, Finset.Icc_self,
          Finset.prod_singleton] at hfact
        push_cast at hfact
        have hbase0 : (0 : ℝ) ≤ 1 - p / (R : ℝ) := by
          have hd : p / (R : ℝ) ≤ p / 3 := by gcongr
          linarith
        have hpow0 : (0 : ℝ) ≤ (1 - p / (R : ℝ)) ^ (R - 2) := pow_nonneg hbase0 _
        have hone : (1 : ℝ) - 1 / (R : ℝ) ≤ 1 := by
          have : (0 : ℝ) ≤ 1 / (R : ℝ) := by positivity
          linarith
        have hfact2 : Real.exp (-p) ≤ (1 - p / (R : ℝ)) ^ (R - 2) :=
          le_trans hfact (by
            calc (1 - 1 / (R : ℝ)) * (1 - p / (R : ℝ)) ^ (R - 2)
                ≤ 1 * (1 - p / (R : ℝ)) ^ (R - 2) :=
                  mul_le_mul_of_nonneg_right hone hpow0
              _ = (1 - p / (R : ℝ)) ^ (R - 2) := one_mul _)
        have hc : 1 - p / 3 ≤ 1 - p / (R : ℝ) := by
          have hd : p / (R : ℝ) ≤ p / 3 := by gcongr
          linarith
        have hsplit : (1 - p / (R : ℝ)) ^ (R - 1)
            = (1 - p / (R : ℝ)) ^ (R - 2) * (1 - p / (R : ℝ)) := by
          rw [← pow_succ]
          congr 1
          omega
        have hgoal : (R : ℝ) * (p / (R : ℝ) * (1 - p / (R : ℝ)) ^ (R - 1))
            = p * ((1 - p / (R : ℝ)) ^ (R - 2) * (1 - p / (R : ℝ))) := by
          rw [hsplit, ← mul_assoc, hcan]
        rw [hgoal]
        exact pexp_high_bound hpgt.le h2 hfact2 hc
  · -- one sure success: the value is `(1 − x)^R ≥ 1 − Rx = 2 − p`
    rw [hl] at hpc hpl
    simp only [Nat.sub_self, Nat.choose_zero_right, pow_zero, Nat.sub_zero,
      Nat.cast_one, one_mul] at hpc
    push_cast at hpl
    have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) R
    have he1 : (1 : ℝ) + (R : ℝ) * (-x) = 1 - (R : ℝ) * x := by ring
    have he2 : (1 : ℝ) + (-x) = 1 - x := by ring
    rw [he1, he2] at hbern
    rw [hpc]
    linarith

/-! ### The sharp two-count mass -/

/-- **`P[N = 2] ≥ 0.058`** for mean in `[1.49, 2.94]`, when `N ≥ 1` always —
the residual shift at `k = 1` feeding the sharp count-one estimate. -/
theorem weightMass_eq_two_ge_of_baseline {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : Finset ι → ℝ} {r : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {F : Finset ι} (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (hm1 : 1.49 ≤ expCard w F) (hm2 : expCard w F ≤ 2.94) :
    (0.058 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card = 2) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmeanq : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have h0 : Bernoulli.probCount q 0 = 0 := by
    rw [← hlaw 0]
    refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans
      (weightMass_false w)
    intro S hS
    have := hbase S hS
    exact ⟨fun hc => by omega, False.elim⟩
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero h0
  have hshift := probCount_succ_update_zero hj 1
  rw [hlaw 2, show (2 : ℕ) = 1 + 1 from rfl, hshift]
  refine probCount_one_ge _
    (update_zero_mem_Icc (fun i => ⟨(hq i).1.le, (hq i).2⟩) j) ?_ ?_
  · rw [sum_update_zero, hj]
    linarith
  · rw [sum_update_zero, hj]
    linarith

/-! ### The two three-cell closures

The tails feed `three_cell_bound_shifted` as products, and the conditional
`0.13` and `0.11` come out **division-free**: from
`m·ε·(1 − 3ε) ≤ mid·(1 − 2ε)`, any `c` with `c·(1 − 2ε) ≤ ε·(1 − 3ε)` gives
`c·m ≤ mid` by cancelling the positive factor `1 − 2ε`. -/

section Closures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The four-count closure** (KKO's `P[U = 2 ∣ U + V = 4] ≥ 0.13`,
division-free): shifted baselines, means in `[1.499, 2.002]`. -/
theorem weightMass_two_two_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B)
    (hbaseA : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ A).card)
    (hbaseB : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card)
    (hmA1 : 1.499 ≤ expCard w A) (hmA2 : expCard w A ≤ 2.002)
    (hmB1 : 1.499 ≤ expCard w B) (hmB2 : expCard w B ≤ 2.002) :
    0.13 * weightMass w (fun T => (T ∩ (A ∪ B)).card = 4)
      ≤ weightMass w (fun T => (T ∩ A).card = 2 ∧ (T ∩ B).card = 2) := by
  have hA_low := weightMass_le_two_ge_of_baseline hnn htot hbaseA hmA2
  have hA_high := weightMass_two_le_ge_of_baseline hst hr hnn htot hbaseA hmA1
  have hB_low := weightMass_le_two_ge_of_baseline hnn htot hbaseB hmB2
  have hB_high := weightMass_two_le_ge_of_baseline hst hr hnn htot hbaseB hmB1
  have h3c := three_cell_bound_shifted hst hr hnn htot hAB 1 1 hbaseA hbaseB
    (ε := 0.194) (by norm_num) (by norm_num)
    (le_trans (by norm_num)
      (mul_le_mul hA_low hB_high (by norm_num) (weightMass_nonneg hnn _)))
    (le_trans (by norm_num)
      (mul_le_mul hA_high hB_low (by norm_num) (weightMass_nonneg hnn _)))
  have hcongr : weightMass w (fun T => (T ∩ (A ∪ B)).card = 1 + 1 + 2)
      = weightMass w (fun T => (T ∩ (A ∪ B)).card = 4) :=
    weightMass_congr fun T => by omega
  rw [hcongr] at h3c
  have hm4 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 4)
  linarith

/-- **The two-count closure** (KKO's `P[W = 1 ∣ V + W = 2] ≥ 0.11`,
division-free): means in `[0.9989, 1.502]`, no baseline needed. -/
theorem weightMass_one_one_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B)
    (hmA1 : 0.9989 ≤ expCard w A) (hmA2 : expCard w A ≤ 1.502)
    (hmB1 : 0.9989 ≤ expCard w B) (hmB2 : expCard w B ≤ 1.502) :
    0.11 * weightMass w (fun T => (T ∩ (A ∪ B)).card = 2)
      ≤ weightMass w (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) := by
  have hA_low := weightMass_le_one_ge hnn htot hmA2
  have hA_high := weightMass_one_le_ge hst hr hnn htot hmA1
  have hB_low := weightMass_le_one_ge hnn htot hmB2
  have hB_high := weightMass_one_le_ge hst hr hnn htot hmB1
  have h3c := three_cell_bound hst hr hnn htot hAB (ε := 0.15)
    (by norm_num) (by norm_num)
    (le_trans (by norm_num)
      (mul_le_mul hA_low hB_high (by norm_num) (weightMass_nonneg hnn _)))
    (le_trans (by norm_num)
      (mul_le_mul hA_high hB_low (by norm_num) (weightMass_nonneg hnn _)))
  have hm2 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 2)
  linarith

end Closures

/-! ### The two orientation kernels

The numeric core of Lemma 5.17, one kernel per case of the `0.03` split,
each stated over the abstract conditioned measure with Eq. (24)-style mean
intervals as hypotheses.  The other orientation of the Lemma 2.27
disjunction is these same kernels applied with `(u, E)` and `(z, F)`
swapped — nothing below is oriented beyond its inputs.

* `two_two_kernel` — KKO's `P_{ν−e}[U_T = (V_{+f})_T = 2] ≥ 0.028 · 0.13`:
  the four-count point mass through the rank law on the disjoint union,
  closed by `weightMass_two_two_ge`.
* `one_one_kernel` — KKO's
  `P_{ν+f}[(V_{+e})_T = W_T = 1] ≥ 0.49 · 0.058 · 0.11`: condition the
  second bundle out, apply the sharp two-count mass to the conditioned law,
  return through the cross-multiplied avoid bridge, and close with
  `weightMass_one_one_ge`. -/

section Kernels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The 2-2 kernel**: shifted baselines and Eq. (24)-style mean intervals
give the joint two-two count, `P[|T∩A| = 2 ∧ |T∩B| = 2] ≥ 0.028 · 0.13`. -/
theorem two_two_kernel {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B)
    (hbaseA : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ A).card)
    (hbaseB : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card)
    (hmA1 : 1.499 ≤ expCard w A) (hmA2 : expCard w A ≤ 2.002)
    (hmB1 : 1.499 ≤ expCard w B) (hmB2 : expCard w B ≤ 2.002)
    (hsum1 : 3.0289 ≤ expCard w A + expCard w B)
    (hsum2 : expCard w A + expCard w B ≤ 3.502) :
    (0.00364 : ℝ)
      ≤ weightMass w (fun T => (T ∩ A).card = 2 ∧ (T ∩ B).card = 2) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot (A ∪ B)
  have hmean : expCard w (A ∪ B) = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hunion : expCard w (A ∪ B) = expCard w A + expCard w B :=
    expCard_union_of_disjoint w hAB
  have h4 : (0.028 : ℝ) ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = 4) := by
    rw [hlaw 4]
    exact probCount_four_ge q (fun i => ⟨(hq i).1.le, (hq i).2⟩)
      (by rw [← hmean, hunion]; linarith) (by rw [← hmean, hunion]; linarith)
  have hclosure := weightMass_two_two_ge hst hr hnn htot hAB hbaseA hbaseB
    hmA1 hmA2 hmB1 hmB2
  linarith

/-- **The 1-1 kernel**: means in the one-count range, a second bundle `E`
avoided with probability at least `0.49`, the connectivity baseline under
that avoidance, and the conditioned mean in `[1.49, 2.94]` give the joint
one-one count, `P[|T∩A| = 1 ∧ |T∩B| = 1] ≥ 0.49 · 0.058 · 0.11`. -/
theorem one_one_kernel {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B E : Finset ι} (hAB : Disjoint A B)
    (hmA1 : 0.9989 ≤ expCard w A) (hmA2 : expCard w A ≤ 1.502)
    (hmB1 : 0.9989 ≤ expCard w B) (hmB2 : expCard w B ≤ 1.502)
    (hmass : 0.49 ≤ weightMass w (fun T => (T ∩ E).card = 0))
    (hbase : ∀ T, w T ≠ 0 → (T ∩ E).card = 0 → 1 ≤ (T ∩ (A ∪ B)).card)
    (hcond1 : 1.49 ≤ expCard (avoidDist w E) (A ∪ B))
    (hcond2 : expCard (avoidDist w E) (A ∪ B) ≤ 2.94) :
    (0.00312 : ℝ)
      ≤ weightMass w (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) := by
  classical
  have hmasspos : 0 < totalMass (avoidWeight w E) := by
    rw [totalMass_avoidWeight]
    linarith
  -- the conditioned law inherits everything
  have hnorm := fixedRankNormalized_avoidDist (r := r) hr hnn hmasspos
  have hst' := isRealStable_genPoly_avoidDist hst hr hnn hmasspos
  have hr' : FixedRankWeight r (avoidDist w E) := by
    intro S hS
    by_contra hc
    exact hS (hnorm.supported S hc)
  -- the connectivity baseline transfers to the conditioned support
  have hbase' : ∀ T, avoidDist w E T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card := by
    intro T hT
    have haw : avoidWeight w E T ≠ 0 := by
      intro hc
      exact hT (by simp only [avoidDist, hc, zero_div])
    have hcard : (T ∩ E).card = 0 := by
      by_contra hc
      exact haw (by rw [avoidWeight_apply, if_neg hc])
    have hwT : w T ≠ 0 := fun hc =>
      haw (by rw [avoidWeight_apply, if_pos hcard]; exact hc)
    exact hbase T hwT hcard
  -- the sharp two-count mass under the conditioned law
  have h058 := weightMass_eq_two_ge_of_baseline hst' hr' hnorm.nonneg
    hnorm.total hbase' hcond1 hcond2
  -- return through the cross-multiplied avoid bridge
  have h2 : (0.02842 : ℝ) ≤ weightMass w
      (fun T => (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ E).card = 0) := by
    have hm049 : (0.49 : ℝ) ≤ totalMass (avoidWeight w E) := by
      rw [totalMass_avoidWeight]
      exact hmass
    have hmul := mul_le_mul h058 hm049 (by norm_num)
      (weightMass_nonneg hnorm.nonneg _)
    rw [weightMass_avoidDist_mul hmasspos] at hmul
    linarith
  -- drop the avoidance conjunct
  have hdrop : weightMass w
        (fun T => (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ E).card = 0)
      ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = 2) := by
    have hand := weightMass_and_not w (fun T => (T ∩ (A ∪ B)).card = 2)
      (fun T => (T ∩ E).card = 0)
    have hnn2 := weightMass_nonneg hnn
      (fun T => (T ∩ (A ∪ B)).card = 2 ∧ ¬ (T ∩ E).card = 0)
    linarith
  have hclosure := weightMass_one_one_ge hst hr hnn htot hAB hmA1 hmA2 hmB1 hmB2
  linarith

end Kernels

end TSPGap

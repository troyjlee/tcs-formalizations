/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LogConcave
import TSPGap.CountEstimates
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric tails of a PF₂ rank law (KKO21 Corollary 2.19)

A PF₂ sequence whose ratio at one step is at most `γ` keeps ratio at most `γ`
from then on (`PF2.decay`).  For a rank law concentrated at level `k` —
`a k > 0` and `a (k+1) ≤ γ · a k` — this bounds the mean by

`∑ j · a j ≤ k + a (k+1) · ((k+1)/(1−γ) + γ/(1−γ)²)`

(`mean_le_of_pf2`): the mass at or below `k` contributes at most `k`, and
the tail is dominated by the geometric series.  KKO's Corollary 2.19
(`P[X = k] ≥ 1 − ε ⟹ E X ≤ k(1 + ε) + 3ε`) is the instance
`γ = ε/(1 − ε)`, `a (k+1) ≤ ε`.

`probGE_eq_zero_of_card_lt` supplies the total mass of a Bernoulli count law
over `range (N+1)` for `N ≥ |ι|`, which is how the abstract statement is
instantiated on `Bernoulli.probCount`.
-/

namespace TSPGap
open Finset

/-- Geometric decay past a step of ratio at most `γ`. -/
theorem PF2.decay {a : ℕ → ℝ} (h : PF2 a) (hnn : ∀ i, 0 ≤ a i) {k : ℕ} (hk : 0 < a k)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : a (k + 1) ≤ γ * a k) :
    ∀ m, a (k + 1 + m) ≤ γ ^ m * a (k + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hpf := h k (k + 1 + m) (by omega)
    -- `a k · a (k+2+m) ≤ a (k+1) · a (k+1+m) ≤ γ a k · a (k+1+m)`
    have h1 : a k * a (k + 1 + m + 1) ≤ γ * a k * a (k + 1 + m) := by
      calc a k * a (k + 1 + m + 1) ≤ a (k + 1) * a (k + 1 + m) := hpf
        _ ≤ γ * a k * a (k + 1 + m) := mul_le_mul_of_nonneg_right hγ (hnn _)
    have h2 : a (k + 1 + m + 1) ≤ γ * a (k + 1 + m) := by
      have := le_of_mul_le_mul_left (a := a k) (by linarith [h1] : a k * a (k + 1 + m + 1) ≤ a k * (γ * a (k + 1 + m))) hk
      exact this
    calc a (k + 1 + (m + 1)) = a (k + 1 + m + 1) := by ring_nf
      _ ≤ γ * a (k + 1 + m) := h2
      _ ≤ γ * (γ ^ m * a (k + 1)) := mul_le_mul_of_nonneg_left ih hγ0
      _ = γ ^ (m + 1) * a (k + 1) := by ring

/-- **The mean of a PF₂ law concentrated at level `k`.** -/
theorem mean_le_of_pf2 {a : ℕ → ℝ} (h : PF2 a) (hnn : ∀ i, 0 ≤ a i) {N k : ℕ}
    (htot : ∑ j ∈ Finset.range (N + 1), a j = 1) (hk : 0 < a k)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : a (k + 1) ≤ γ * a k) :
    ∑ j ∈ Finset.range (N + 1), (j : ℝ) * a j
      ≤ k + a (k + 1) * (((k : ℝ) + 1) * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2) := by
  have hγpos : 0 < 1 - γ := by linarith
  have htail_nn : 0 ≤ a (k + 1) * (((k : ℝ) + 1) * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2) := by
    apply mul_nonneg (hnn _)
    have : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr hγpos.le
    positivity
  -- the mass at or below `k` contributes at most `k`
  have hlow : ∀ M, M ≤ N + 1 → ∀ c : ℕ, (∀ j < M, j ≤ c) →
      ∑ j ∈ Finset.range M, (j : ℝ) * a j ≤ c := by
    intro M hM c hc
    calc ∑ j ∈ Finset.range M, (j : ℝ) * a j ≤ ∑ j ∈ Finset.range M, (c : ℝ) * a j := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc j (Finset.mem_range.mp hj))
            (hnn j)
      _ = c * ∑ j ∈ Finset.range M, a j := by rw [Finset.mul_sum]
      _ ≤ c * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
          rw [← htot]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
            fun j _ _ => hnn j
      _ = c := mul_one _
  rcases le_or_gt (k + 1) (N + 1) with hkN | hkN
  · -- split at `k + 1`
    rw [← Finset.sum_range_add_sum_Ico _ hkN]
    have h1 := hlow (k + 1) hkN k fun j hj => by omega
    -- the tail, reindexed from `k + 1`
    have h2 : ∑ j ∈ Finset.Ico (k + 1) (N + 1), (j : ℝ) * a j
        ≤ a (k + 1) * (((k : ℝ) + 1) * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hdec := h.decay hnn hk hγ0 hγ
      have hsum : ∀ L : ℕ, ∑ m ∈ Finset.range L, (((k + 1 + m : ℕ) : ℝ) * a (k + 1 + m))
          ≤ a (k + 1) * ∑ m ∈ Finset.range L, (((k : ℝ) + 1) * γ ^ m + (m : ℝ) * γ ^ m) := by
        intro L
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun m _ => ?_
        have hm : ((k + 1 + m : ℕ) : ℝ) = (k : ℝ) + 1 + m := by push_cast; ring
        rw [hm]
        calc ((k : ℝ) + 1 + m) * a (k + 1 + m) ≤ ((k : ℝ) + 1 + m) * (γ ^ m * a (k + 1)) :=
              mul_le_mul_of_nonneg_left (hdec m) (by positivity)
          _ = a (k + 1) * (((k : ℝ) + 1) * γ ^ m + (m : ℝ) * γ ^ m) := by ring
      refine (hsum _).trans (mul_le_mul_of_nonneg_left ?_ (hnn _))
      -- the partial sums are below the two geometric series
      have hgeo : Summable fun m : ℕ => γ ^ m := summable_geometric_of_lt_one hγ0 hγ1
      have hmgeo : Summable fun m : ℕ => (m : ℝ) * γ ^ m := by
        have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := γ)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hγ0]; exact hγ1)
        simpa using this
      have hg1 : ∑ m ∈ Finset.range (N + 1 - (k + 1)), γ ^ m ≤ (1 - γ)⁻¹ := by
        rw [← tsum_geometric_of_lt_one hγ0 hγ1]
        exact Summable.sum_le_tsum _ (fun m _ => pow_nonneg hγ0 m) hgeo
      have hg2 : ∑ m ∈ Finset.range (N + 1 - (k + 1)), (m : ℝ) * γ ^ m ≤ γ / (1 - γ) ^ 2 := by
        rw [← tsum_coe_mul_geometric_of_norm_lt_one
          (by rw [Real.norm_eq_abs, abs_of_nonneg hγ0]; exact hγ1)]
        exact Summable.sum_le_tsum _ (fun m _ => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hγ0 m)) hmgeo
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hg1 hk1, hg2]
    linarith
  · -- everything is at or below `N < k`
    have := hlow (N + 1) le_rfl k fun j hj => by omega
    linarith

/-- `P[X ≥ k] = 0` beyond the support. -/
theorem probGE_eq_zero_of_card_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) {k : ℕ}
    (hk : Fintype.card ι < k) : Bernoulli.probGE q k = 0 := by
  rw [Bernoulli.probGE_def]
  refine Finset.sum_eq_zero fun t ht => ?_
  have h := (Finset.mem_filter.mp ht).2
  have := Finset.card_le_univ t
  omega

/-- The total mass of a Bernoulli count law over `range (N + 1)`, `N ≥ |ι|`. -/
theorem sum_range_probCount_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) {N : ℕ}
    (hN : Fintype.card ι ≤ N) :
    ∑ j ∈ Finset.range (N + 1), Bernoulli.probCount q j = 1 := by
  have h := Bernoulli.sum_probCount_add_probGE q (N + 1)
  rw [probGE_eq_zero_of_card_lt q (by omega), add_zero] at h
  exact h

end TSPGap

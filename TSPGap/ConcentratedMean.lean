/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankTail
import TSPGap.RankSequence

/-!
# Corollary 2.19 at the weight level

If a stable fixed-rank normalized law has `P[F_T = k] ≥ 1 − δ` and
`P[F_T = k+1] ≤ δ`, then its Bernoulli rank law is PF₂ with ratio at most
`γ = δ/(1 − δ)` at step `k`, and `mean_le_of_pf2` bounds the mean:

`E[F_T] ≤ k + δ · ((k+1)/(1−γ) + γ/(1−γ)²)`.

For `k = 2` and `δ ≤ 1/10` the bracket is at most `3.6`, which is the form
Lemma 5.27 uses (`expCard_le_two_add_of_concentrated`): KKO's
`E X ≤ k(1+ε) + 3ε` is `2 + 5ε` there; ours is `2 + 3.6δ`.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Corollary 2.19**, general form. -/
theorem expCard_le_of_concentrated {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι) {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10)
    (hk : 1 - δ ≤ weightMass w (fun T => (T ∩ F).card = k))
    (hk1 : weightMass w (fun T => (T ∩ F).card = k + 1) ≤ δ) :
    expCard w F ≤ k + δ * (((k : ℝ) + 1) * (1 - δ / (1 - δ))⁻¹
      + (δ / (1 - δ)) / (1 - δ / (1 - δ)) ^ 2) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard w F = ∑ j ∈ Finset.range (m + 1), (j : ℝ) * Bernoulli.probCount q j := by
    rw [expCard_eq_sum_of_rankLaw hlaw, sum_range_mul_probCount q (by simp)]
  have hpf : PF2 (Bernoulli.probCount q) :=
    Bernoulli.pf2_probCount q fun i => ⟨(hq i).1.le, (hq i).2⟩
  have hnn' : ∀ i, 0 ≤ Bernoulli.probCount q i := fun i => by
    rw [← hlaw]; exact weightMass_nonneg hnn _
  have htot' := sum_range_probCount_eq_one q (N := m) (by simp)
  have hδ1 : 0 < 1 - δ := by linarith
  set γ : ℝ := δ / (1 - δ) with hγ
  have hγ0 : 0 ≤ γ := div_nonneg hδ0 hδ1.le
  have hγ1 : γ < 1 := by
    rw [hγ, div_lt_one hδ1]; linarith
  have hak : 0 < Bernoulli.probCount q k := by rw [← hlaw]; linarith
  have hak1 : Bernoulli.probCount q (k + 1) ≤ γ * Bernoulli.probCount q k := by
    rw [← hlaw, ← hlaw]
    have h1 : δ ≤ γ * (1 - δ) := by
      rw [hγ, div_mul_cancel₀ _ hδ1.ne']
    calc weightMass w (fun T => (T ∩ F).card = k + 1) ≤ δ := hk1
      _ ≤ γ * (1 - δ) := h1
      _ ≤ γ * weightMass w (fun T => (T ∩ F).card = k) :=
          mul_le_mul_of_nonneg_left hk hγ0
  have h := mean_le_of_pf2 hpf hnn' htot' hak hγ0 hγ1 hak1
  rw [hmean]
  refine h.trans ?_
  have hbr : 0 ≤ ((k : ℝ) + 1) * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2 := by
    have : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
    positivity
  have hak1' : Bernoulli.probCount q (k + 1) ≤ δ := by rw [← hlaw]; exact hk1
  linarith [mul_le_mul_of_nonneg_right hak1' hbr]

/-- **Corollary 2.19 at level two**: `E[F_T] ≤ 2 + 3.6δ`. -/
theorem expCard_le_two_add_of_concentrated {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10)
    (hk : 1 - δ ≤ weightMass w (fun T => (T ∩ F).card = 2))
    (hk1 : weightMass w (fun T => (T ∩ F).card = 3) ≤ δ) :
    expCard w F ≤ 2 + 3.6 * δ := by
  have h := expCard_le_of_concentrated hst hr hnn htot F hδ0 hδ hk hk1
  have hδ1 : 0 < 1 - δ := by linarith
  set γ : ℝ := δ / (1 - δ) with hγ
  have hγ0 : 0 ≤ γ := div_nonneg hδ0 hδ1.le
  have hγ9 : γ ≤ 1 / 9 := by
    rw [hγ, div_le_iff₀ hδ1]; linarith
  have hγ1 : 0 < 1 - γ := by linarith
  -- the bracket is at most 3.6 for γ ≤ 1/9
  have hinv : (1 - γ)⁻¹ ≤ 9 / 8 := by
    rw [inv_le_comm₀ hγ1 (by norm_num)]; linarith
  have hsq : γ / (1 - γ) ^ 2 ≤ 0.1407 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hbr : (((2 : ℕ) : ℝ) + 1) * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2 ≤ 3.6 := by
    push_cast
    linarith
  have := mul_le_mul_of_nonneg_left hbr hδ0
  push_cast at h
  linarith

end TSPGap

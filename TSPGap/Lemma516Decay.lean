/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankTail
import TSPGap.Lemma2122Tails
import TSPGap.LayerTails
import TSPGap.BernoulliRecursion

/-!
# Geometric tails for KKO21 Lemma 5.16 (Lemma 2.18)

In Case 2 of Lemma 5.16 the sum count `Z = δ↑(u)_T + δ(v)_T` (baseline `1`)
has `P[Z = 3] ≤ γ P[Z = 2]` with `γ` small, and KKO use Lemma 2.18 — the
log-concave tail decays geometrically — twice:

* `P[Z ≥ 4] ≤ P[Z = 3] · γ/(1 − γ)` (`weightMass_four_le_tail`);
* `E[(Z − 1) · 𝟙{Z ≥ 3}] ≤ P[Z = 3] · (2/(1 − γ) + γ/(1 − γ)²)`
  (`restricted_mean_le_tail`), which bounds `E[X · 𝟙{X ≥ 2}]` for either
  summand `X` of `Z` (`X ≤ Z − 1` and `X ≥ 2 ⟹ Z ≥ 3`).

Both come from `PF2.decay` on the baseline-shifted Bernoulli law of `Z`
(`exists_shift_of_baseline`), with the partial sums dominated by the two
geometric series exactly as in `mean_le_of_pf2`.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Regrouping a function of the count -/

theorem weightMass_eq_sum_mul_ite (w : Finset ι → ℝ) (P : Finset ι → Prop) [DecidablePred P] :
    weightMass w P = ∑ T, w T * (if P T then (1 : ℝ) else 0) := by
  unfold weightMass
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : P T <;> simp [h]

/-- `∑_T w(T) g(|T ∩ F|) = ∑_j g(j) P[|T ∩ F| = j]`. -/
theorem sum_weight_count_eq (w : Finset ι → ℝ) (F : Finset ι) (g : ℕ → ℝ) :
    ∑ T, w T * g (T ∩ F).card
      = ∑ j ∈ Finset.range (F.card + 1), g j * weightMass w (fun T => (T ∩ F).card = j) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (F.card + 1))
    (g := fun T => (T ∩ F).card) (fun T _ => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightMass_eq_filter_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [(Finset.mem_filter.mp hT).2]
  ring

/-! ### Tail sums of a geometrically decaying sequence -/

/-- Partial sums below the geometric series. -/
theorem sum_geom_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (L : ℕ) :
    ∑ m ∈ Finset.range L, γ ^ m ≤ (1 - γ)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hγ0 hγ1]
  exact Summable.sum_le_tsum _ (fun m _ => pow_nonneg hγ0 m)
    (summable_geometric_of_lt_one hγ0 hγ1)

theorem sum_mul_geom_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (L : ℕ) :
    ∑ m ∈ Finset.range L, (m : ℝ) * γ ^ m ≤ γ / (1 - γ) ^ 2 := by
  have hnorm : ‖γ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hγ0]; exact hγ1
  rw [← tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  have hmgeo : Summable fun m : ℕ => (m : ℝ) * γ ^ m := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    simpa using this
  exact Summable.sum_le_tsum _ (fun m _ => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hγ0 m)) hmgeo

/-- From `a (2 + m) ≤ γ^m a 2`: the tail from index `3` and the weighted tail
from index `2`. -/
theorem decay_tail_sums {a : ℕ → ℝ} (hnn : ∀ i, 0 ≤ a i) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hdec : ∀ m, a (2 + m) ≤ γ ^ m * a 2) (L : ℕ) :
    (∑ m ∈ Finset.range L, a (3 + m) ≤ a 2 * (γ / (1 - γ)))
    ∧ (∑ m ∈ Finset.range L, ((2 : ℝ) + m) * a (2 + m)
        ≤ a 2 * (2 * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2)) := by
  have hγpos : 0 < 1 - γ := by linarith
  constructor
  · -- `a (3 + m) = a (2 + (m + 1)) ≤ γ^{m+1} a 2`
    have h1 : ∑ m ∈ Finset.range L, a (3 + m) ≤ ∑ m ∈ Finset.range L, γ ^ (m + 1) * a 2 := by
      refine Finset.sum_le_sum fun m _ => ?_
      have := hdec (m + 1)
      rw [show 2 + (m + 1) = 3 + m by ring] at this
      exact this
    have h2 : ∑ m ∈ Finset.range L, γ ^ (m + 1) * a 2
        = a 2 * γ * ∑ m ∈ Finset.range L, γ ^ m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [h2] at h1
    have h3 := sum_geom_le hγ0 hγ1 L
    have h4 : a 2 * γ * ∑ m ∈ Finset.range L, γ ^ m ≤ a 2 * γ * (1 - γ)⁻¹ :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (hnn 2) hγ0)
    calc ∑ m ∈ Finset.range L, a (3 + m) ≤ a 2 * γ * (1 - γ)⁻¹ := h1.trans h4
      _ = a 2 * (γ / (1 - γ)) := by rw [div_eq_mul_inv]; ring
  · have h1 : ∑ m ∈ Finset.range L, ((2 : ℝ) + m) * a (2 + m)
        ≤ ∑ m ∈ Finset.range L, ((2 : ℝ) + m) * (γ ^ m * a 2) := by
      refine Finset.sum_le_sum fun m _ => ?_
      exact mul_le_mul_of_nonneg_left (hdec m) (by positivity)
    have h2 : ∑ m ∈ Finset.range L, ((2 : ℝ) + m) * (γ ^ m * a 2)
        = a 2 * (2 * ∑ m ∈ Finset.range L, γ ^ m + ∑ m ∈ Finset.range L, (m : ℝ) * γ ^ m) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [h2] at h1
    have h3 := sum_geom_le hγ0 hγ1 L
    have h4 := sum_mul_geom_le hγ0 hγ1 L
    calc ∑ m ∈ Finset.range L, ((2 : ℝ) + m) * a (2 + m)
        ≤ a 2 * (2 * ∑ m ∈ Finset.range L, γ ^ m + ∑ m ∈ Finset.range L, (m : ℝ) * γ ^ m) := h1
      _ ≤ a 2 * (2 * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (hnn 2)
          linarith

/-! ### The two tails at a baseline-`1` count -/

/-- **Lemma 2.18 for the sum count**: with `P[Z = 3] ≤ γ P[Z = 2]`, the tail
`P[Z ≥ 4]` and the restricted mean `E[(Z − 1)𝟙{Z ≥ 3}]` are geometric in
`P[Z = 3]`. -/
theorem tails_of_baseline {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    (h2pos : 0 < weightMass w (fun T => (T ∩ F).card = 2)) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hγ : weightMass w (fun T => (T ∩ F).card = 3) ≤ γ * weightMass w (fun T => (T ∩ F).card = 2)) :
    (weightMass w (fun T => 4 ≤ (T ∩ F).card)
        ≤ weightMass w (fun T => (T ∩ F).card = 3) * (γ / (1 - γ)))
    ∧ (∑ T, w T * ((((T ∩ F).card : ℝ) - 1) * (if 3 ≤ (T ∩ F).card then (1 : ℝ) else 0))
        ≤ weightMass w (fun T => (T ∩ F).card = 3) * (2 * (1 - γ)⁻¹ + γ / (1 - γ) ^ 2)) := by
  classical
  obtain ⟨m, q, hq, -, hlaw⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  set a : ℕ → ℝ := Bernoulli.probCount q with ha
  have hpf : PF2 a := Bernoulli.pf2_probCount q fun i => ⟨(hq i).1, (hq i).2⟩
  have hann : ∀ i, 0 ≤ a i := fun i => probCount_nonneg hq i
  have hlaw' : ∀ k, weightMass w (fun T => (T ∩ F).card = k + 1) = a k := hlaw
  have h1 : 0 < a 1 := by rw [← hlaw' 1]; exact h2pos
  have h2 : a 2 ≤ γ * a 1 := by rw [← hlaw' 1, ← hlaw' 2]; exact hγ
  have hdec := hpf.decay hann h1 hγ0 h2
  have hdec' : ∀ n, a (2 + n) ≤ γ ^ n * a 2 := fun n => by
    have := hdec n
    rw [show 1 + 1 + n = 2 + n by ring, show (1 : ℕ) + 1 = 2 by norm_num] at this
    exact this
  have hP3 : weightMass w (fun T => (T ∩ F).card = 3) = a 2 := hlaw' 2
  set N := F.card with hN
  constructor
  · -- `P[Z ≥ 4] = ∑_{j ≥ 4} P[Z = j] = ∑_{m} a (3 + m)`
    rw [weightMass_eq_sum_mul_ite, sum_weight_count_eq w F (fun j => if 4 ≤ j then (1 : ℝ) else 0)]
    rcases le_or_gt 4 (N + 1) with hle | hlt
    · rw [← Finset.sum_range_add_sum_Ico _ hle]
      have hlow : ∑ j ∈ Finset.range 4, (if 4 ≤ j then (1 : ℝ) else 0)
          * weightMass w (fun T => (T ∩ F).card = j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [if_neg (by have := Finset.mem_range.mp hj; omega), zero_mul]
      rw [hlow, zero_add, Finset.sum_Ico_eq_sum_range]
      have hterm : ∀ k ∈ Finset.range (N + 1 - 4),
          (if 4 ≤ 4 + k then (1 : ℝ) else 0) * weightMass w (fun T => (T ∩ F).card = 4 + k)
            = a (3 + k) := by
        intro k _
        rw [if_pos (by omega), one_mul, show 4 + k = (3 + k) + 1 by ring, hlaw']
      rw [Finset.sum_congr rfl hterm, hP3]
      exact (decay_tail_sums hann hγ0 hγ1 hdec' _).1
    · -- no layer at or above `4`
      have : ∑ j ∈ Finset.range (N + 1), (if 4 ≤ j then (1 : ℝ) else 0)
          * weightMass w (fun T => (T ∩ F).card = j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [if_neg (by have := Finset.mem_range.mp hj; omega), zero_mul]
      rw [this, hP3]
      exact mul_nonneg (hann 2) (div_nonneg hγ0 (by linarith))
  · rw [sum_weight_count_eq w F (fun j => ((j : ℝ) - 1) * (if 3 ≤ j then (1 : ℝ) else 0))]
    rcases le_or_gt 3 (N + 1) with hle | hlt
    · rw [← Finset.sum_range_add_sum_Ico _ hle]
      have hlow : ∑ j ∈ Finset.range 3, ((j : ℝ) - 1) * (if 3 ≤ j then (1 : ℝ) else 0)
          * weightMass w (fun T => (T ∩ F).card = j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [if_neg (by have := Finset.mem_range.mp hj; omega), mul_zero, zero_mul]
      rw [hlow, zero_add, Finset.sum_Ico_eq_sum_range]
      have hterm : ∀ k ∈ Finset.range (N + 1 - 3),
          (((3 + k : ℕ) : ℝ) - 1) * (if 3 ≤ 3 + k then (1 : ℝ) else 0)
            * weightMass w (fun T => (T ∩ F).card = 3 + k)
            = ((2 : ℝ) + k) * a (2 + k) := by
        intro k _
        rw [if_pos (by omega), mul_one, show 3 + k = (2 + k) + 1 by ring, hlaw']
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, hP3]
      exact (decay_tail_sums hann hγ0 hγ1 hdec' _).2
    · have : ∑ j ∈ Finset.range (N + 1), ((j : ℝ) - 1) * (if 3 ≤ j then (1 : ℝ) else 0)
          * weightMass w (fun T => (T ∩ F).card = j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [if_neg (by have := Finset.mem_range.mp hj; omega), mul_zero, zero_mul]
      rw [this, hP3]
      have hγpos : 0 < 1 - γ := by linarith
      apply mul_nonneg (hann 2)
      have : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr hγpos.le
      positivity

end TSPGap

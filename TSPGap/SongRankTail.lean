/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankTail

/-!
# Song's central-rank error: the finite PF₂ estimate

The upper half of Song, Lemma 12, charges the tail mass only once.  The
geometric series bounds the distance *beyond the first tail level*, not the
whole upper tail.  Thus the error is independent of the central rank.

This leaf proves only sequence estimates.  Stability and the lower bound by
complementation belong to `SongRankConcentration`.
-/

noncomputable section
namespace TSPGap.Song
open Finset

/-- Ratio bound past a rank carrying at least `1 - δ` of the mass. -/
def rankRatio (δ : ℝ) : ℝ := δ / (1 - δ)

/-- The sharper central-rank error in Song's Lemma 12. -/
def rankPsi (δ : ℝ) : ℝ :=
  δ + δ * rankRatio δ / (1 - rankRatio δ) ^ 2

/-- The simpler upper envelope used by Song's marginal-shift estimates. -/
def rankPhi (δ : ℝ) : ℝ := δ / (1 - rankRatio δ) ^ 2

theorem rankRatio_bounds {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) :
    0 ≤ rankRatio δ ∧ rankRatio δ < 1 := by
  have hd : 0 < 1 - δ := by linarith
  exact ⟨div_nonneg hδ0 hd.le, (div_lt_one hd).2 (by linarith)⟩

theorem rankPsi_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) :
    0 ≤ rankPsi δ := by
  have hg := (rankRatio_bounds hδ0 hδ).1
  unfold rankPsi
  positivity

theorem rankPsi_le_rankPhi {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) :
    rankPsi δ ≤ rankPhi δ := by
  obtain ⟨hg0, hg1⟩ := rankRatio_bounds hδ0 hδ
  have hd : 0 < (1 - rankRatio δ) ^ 2 := sq_pos_of_pos (by linarith)
  unfold rankPsi rankPhi
  rw [add_div', div_le_div_iff_of_pos_right hd]
  · nlinarith [mul_nonneg hδ0 (mul_nonneg hg0 (sub_nonneg.mpr hg1.le))]
  · exact hd.ne'

private theorem weighted_geometric_sum_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (L : ℕ) : ∑ m ∈ range L, (m : ℝ) * γ ^ m ≤ γ / (1 - γ) ^ 2 := by
  have hn : ‖γ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hγ0]
    exact hγ1
  rw [← tsum_coe_mul_geometric_of_norm_lt_one hn]
  have hs : Summable fun m : ℕ => (m : ℝ) * γ ^ m := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  exact Summable.sum_le_tsum _
    (fun m _ => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hγ0 m)) hs

/-- Sharp upper mean estimate for a finite normalized PF₂ sequence.
The next-mass premise is discharged from normalization at the probability
interface; it is kept explicit here so no infinite-support convention is needed.
The central rank may be zero or beyond the finite summation range. -/
theorem mean_le_rankPsi {a : ℕ → ℝ} (hpf : PF2 a) (hnn : ∀ i, 0 ≤ a i)
    {N k : ℕ} (htot : ∑ j ∈ range (N + 1), a j = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hk : 1 - δ ≤ a k) (hnext : a (k + 1) ≤ δ) :
    ∑ j ∈ range (N + 1), (j : ℝ) * a j ≤ k + rankPsi δ := by
  obtain ⟨hg0, hg1⟩ := rankRatio_bounds hδ0 hδ
  have hak : 0 < a k := by linarith
  have hstep : a (k + 1) ≤ rankRatio δ * a k := by
    have hd : 1 - δ ≠ 0 := by linarith
    calc a (k + 1) ≤ δ := hnext
      _ = rankRatio δ * (1 - δ) := by unfold rankRatio; field_simp
      _ ≤ rankRatio δ * a k := mul_le_mul_of_nonneg_left hk hg0
  have hdec := hpf.decay hnn hak hg0 hstep
  have hgeom0 : 0 ≤ rankRatio δ / (1 - rankRatio δ) ^ 2 := by positivity
  rcases le_or_gt (k + 1) (N + 1) with hkN | hkN
  · let L := ∑ j ∈ range (k + 1), a j
    let H := ∑ j ∈ Ico (k + 1) (N + 1), a j
    have hmass : L + H = 1 := by
      dsimp [L, H]
      rw [sum_range_add_sum_Ico _ hkN, htot]
    have hcenter : a k ≤ L :=
      single_le_sum (fun j _ => hnn j) (mem_range.mpr (by omega))
    have htail : H ≤ δ := by linarith
    have hlow : ∑ j ∈ range (k + 1), (j : ℝ) * a j ≤ k * L := by
      dsimp [L]
      rw [mul_sum]
      refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (hnn j)
      exact_mod_cast (show j ≤ k by have := mem_range.mp hj; omega)
    have hhigh : ∑ j ∈ Ico (k + 1) (N + 1), (j : ℝ) * a j ≤
        (k + 1) * H + a (k + 1) * (rankRatio δ / (1 - rankRatio δ) ^ 2) := by
      dsimp [H]
      rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
      have hterm : ∀ m : ℕ, ((k + 1 + m : ℕ) : ℝ) * a (k + 1 + m) ≤
          ((k : ℝ) + 1) * a (k + 1 + m) +
            a (k + 1) * ((m : ℝ) * rankRatio δ ^ m) := by
        intro m
        have := mul_le_mul_of_nonneg_left (hdec m) (Nat.cast_nonneg m)
        push_cast
        nlinarith only [this]
      calc
        _ ≤ ∑ m ∈ range (N + 1 - (k + 1)),
            (((k : ℝ) + 1) * a (k + 1 + m) +
              a (k + 1) * ((m : ℝ) * rankRatio δ ^ m)) :=
          sum_le_sum fun m _ => hterm m
        _ = ((k : ℝ) + 1) * ∑ m ∈ range (N + 1 - (k + 1)), a (k + 1 + m) +
            a (k + 1) * ∑ m ∈ range (N + 1 - (k + 1)), (m : ℝ) * rankRatio δ ^ m := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (weighted_geometric_sum_le hg0 hg1 _) (hnn _))
    have hsmall := mul_le_mul_of_nonneg_right hnext hgeom0
    rw [← sum_range_add_sum_Ico _ hkN]
    calc
      _ ≤ (k : ℝ) * L + ((k + 1) * H +
          a (k + 1) * (rankRatio δ / (1 - rankRatio δ) ^ 2)) := add_le_add hlow hhigh
      _ = (k : ℝ) * (L + H) + H +
          a (k + 1) * (rankRatio δ / (1 - rankRatio δ) ^ 2) := by ring
      _ = k + H + a (k + 1) * (rankRatio δ / (1 - rankRatio δ) ^ 2) := by
        rw [hmass, mul_one]
      _ ≤ k + δ + δ * (rankRatio δ / (1 - rankRatio δ) ^ 2) :=
        add_le_add (add_le_add le_rfl htail) hsmall
      _ = k + rankPsi δ := by unfold rankPsi; ring
  · have hmean : ∑ j ∈ range (N + 1), (j : ℝ) * a j ≤ k := by
      calc
        _ ≤ ∑ j ∈ range (N + 1), (k : ℝ) * a j := by
          refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (hnn j)
          exact_mod_cast (show j ≤ k by have := mem_range.mp hj; omega)
        _ = k := by rw [← mul_sum, htot, mul_one]
    linarith [rankPsi_nonneg hδ0 hδ]

end TSPGap.Song

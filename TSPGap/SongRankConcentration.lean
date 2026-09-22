/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRankTail
import TSPGap.LawPackage

/-!
# Song's central-rank concentration lemma

Song, Lemma 12: a rank with mass at least `1 - δ`, for `0 ≤ δ < 1/2`,
pins its mean within `rankPsi δ` of that rank, hence within `rankPhi δ`.
The upper bound uses the Bernoulli rank law and PF₂.  The lower bound applies
the same upper bound to the complementary coordinates of the fixed-rank law.
No condition is imposed on the next rank: its small mass is derived.

The statements also cover central rank zero.  `central_mass_mean_le` is the
elementary one-sided estimate used separately in Song's Lemma 20.
-/

namespace TSPGap.Song
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The elementary lower mean bound needs neither stability nor normalization. -/
theorem central_mass_mean_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) {k : ℕ} {δ : ℝ}
    (hk : 1 - δ ≤ weightMass w (fun T => (T ∩ F).card = k)) :
    (k : ℝ) * (1 - δ) ≤ expCard w F :=
  (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg k)).trans
    (mul_weightMass_eq_le_expCard hnn F k)

/-- Upper half of Song's Lemma 12, with the sharper error `Ψ`. -/
theorem expCard_le_rankPsi {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r)
    (F : Finset ι) {k : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hk : 1 - δ ≤ weightMass w (fun T => (T ∩ F).card = k)) :
    expCard w F ≤ k + rankPsi δ := by
  classical
  have hnext : weightMass w (fun T => (T ∩ F).card = k + 1) ≤ δ := by
    have hm := weightMass_mono hw.nn
      (A := fun T => (T ∩ F).card = k + 1)
      (B := fun T => ¬ (T ∩ F).card = k) (fun T hT => by omega)
    rw [weightMass_not, hw.tot] at hm
    linarith
  obtain ⟨m, q, hq, hlaw⟩ :=
    exists_bernoulli_rank_law hw.st hw.rank hw.nn hw.tot F
  have hmean : expCard w F =
      ∑ j ∈ range (m + 1), (j : ℝ) * Bernoulli.probCount q j := by
    rw [expCard_eq_sum_of_rankLaw hlaw, sum_range_mul_probCount q (by simp)]
  have hpf : PF2 (Bernoulli.probCount q) :=
    Bernoulli.pf2_probCount q fun i => ⟨(hq i).1.le, (hq i).2⟩
  have hnn : ∀ j, 0 ≤ Bernoulli.probCount q j := fun j => by
    rw [← hlaw]
    exact weightMass_nonneg hw.nn _
  rw [hmean]
  apply mean_le_rankPsi hpf hnn (sum_range_probCount_eq_one q (by simp)) hδ0 hδ
  · rw [← hlaw]; exact hk
  · rw [← hlaw]; exact hnext

/-- Lower half of Song's Lemma 12, by complementing the counted coordinates. -/
theorem rankPsi_le_expCard {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r)
    (F : Finset ι) {k : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hk : 1 - δ ≤ weightMass w (fun T => (T ∩ F).card = k)) :
    k - rankPsi δ ≤ expCard w F := by
  have hkr : k ≤ r := by
    by_contra hkr
    have hz : weightMass w (fun T => (T ∩ F).card = k) = 0 := by
      refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans
        (weightMass_false w)
      intro T hT
      have hr := hw.rank T hT
      have hc := card_le_card (inter_subset_left (s₁ := T) (s₂ := F))
      exact ⟨fun hcount => by omega, False.elim⟩
    rw [hz] at hk
    linarith
  have hmass : weightMass w (fun T => (T ∩ Fᶜ).card = r - k) =
      weightMass w (fun T => (T ∩ F).card = k) := by
    refine weightMass_congr_of_support fun T hT => ?_
    have hc := card_inter_add_card_sdiff T F
    rw [hw.rank T hT] at hc
    rw [← sdiff_eq_inter_compl]
    omega
  have hu := expCard_le_rankPsi hw Fᶜ hδ0 hδ (by rw [hmass]; exact hk)
  have hmean : expCard w Fᶜ = (r : ℝ) - expCard w F := by
    rw [compl_eq_univ_sdiff, expCard_sdiff_of_subset w (subset_univ F),
      expCard_univ hw.rank, hw.tot, mul_one]
  rw [hmean, Nat.cast_sub hkr] at hu
  linarith

/-- Song's Lemma 12, retaining both the sharp error and its simpler envelope. -/
theorem rank_concentration {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r)
    (F : Finset ι) {k : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hk : 1 - δ ≤ weightMass w (fun T => (T ∩ F).card = k)) :
    k - rankPsi δ ≤ expCard w F ∧ expCard w F ≤ k + rankPsi δ ∧
      (k : ℝ) + rankPsi δ ≤ k + rankPhi δ :=
  ⟨rankPsi_le_expCard hw F hδ0 hδ hk, expCard_le_rankPsi hw F hδ0 hδ hk,
    by linarith [rankPsi_le_rankPhi hδ0 hδ]⟩

end TSPGap.Song

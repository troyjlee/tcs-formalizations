/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedInputs

/-!
# Joint avoidance and overlap accounting for Song's paired prefixes

Consecutive zero restrictions are one joint event, even when their sets
overlap. Their normalization masses multiply to the joint mass, not to a
product of independent probabilities. A bound on the union mean proves
positivity of both stages. One-hot support for the last set then derives
the strict mean bound needed by `paired_input_profile`.

The final two lemmas bound the expected overlap under any earlier event
restriction, charging the original mean once and dividing by the actual
restriction mass floor. No tree geometry or Song numerical parameter is
used here.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A count agrees with its punctured version after avoidance, including
when the avoiding mass is zero. No sign hypothesis on the input is needed. -/
theorem expCard_avoid_sdiff (ν : Finset ι → ℝ) (A D : Finset ι) :
    expCard (avoidDist ν D) A = expCard (avoidDist ν D) (A \ D) := by
  unfold expCard
  refine sum_congr rfl fun T _ => ?_
  by_cases hT : avoidDist ν D T = 0
  · simp only [hT, zero_mul]
  · have hz := (avoidDist_ne_zero_imp hT).2
    have heq : T ∩ (A \ D) = T ∩ A := by
      simpa using inter_sdiff_union_eq_of_card_inter_zero (A := A) (X := ∅) hz
    rw [heq]

/-- The additive upper bound also permits overlap with the avoided set.
Only the lower sign needs disjointness. -/
theorem avoid_overlap_le {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    (A D : Finset ι) (hmass : 0 < totalMass (avoidWeight ν D)) :
    expCard (avoidDist ν D) A ≤ expCard ν A + expCard ν D := by
  have hdis : Disjoint (A \ D) D :=
    disjoint_left.mpr fun _ hA hD => (mem_sdiff.mp hA).2 hD
  have hupper : expCard (avoidDist ν D) (A \ D) ≤ expCard ν (A \ D) + expCard ν D :=
    hw.avoid_le hdis hmass
  have hmono : expCard ν (A \ D) ≤ expCard ν A :=
    expCard_mono hw.nn (sdiff_subset (s := A) (t := D))
  rw [expCard_avoid_sdiff ν A D]
  exact hupper.trans (add_le_add hmono le_rfl)

/-- The two avoidance masses multiply to the union-avoidance mass.
The sets need not be disjoint; only the first normalization needs positivity. -/
theorem avoid_chain_mass {ν : Finset ι → ℝ} {D F : Finset ι}
    (hD : 0 < totalMass (avoidWeight ν D)) :
    totalMass (avoidWeight ν D) * totalMass (avoidWeight (avoidDist ν D) F) =
      totalMass (avoidWeight ν (D ∪ F)) := by
  rw [totalMass_avoidWeight (avoidDist ν D) F, mul_comm,
    weightMass_avoidDist_mul hD, totalMass_avoidWeight]
  refine weightMass_congr fun T => ?_
  simp only [card_eq_zero, inter_union_distrib_left, union_eq_empty]
  exact and_comm

/-- A one-hot count and its avoidance mass sum to the total mass.
This identity is valid for signed weights too. -/
theorem onehot_mean_add_avoid {ν : Finset ι → ℝ} {F : Finset ι}
    (hone : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1) :
    expCard ν F + totalMass (avoidWeight ν F) = totalMass ν := by
  have heq : weightMass ν (fun T => (T ∩ F).card = 1) =
      weightMass ν (fun T => ¬ (T ∩ F).card = 0) := by
    refine weightMass_congr_of_support fun T hT => ?_
    have := hone T hT
    omega
  rw [expCard_eq_weightMass_one hone, totalMass_avoidWeight, heq, weightMass_not]
  ring

/-- Construct the prefix `D = 0`, keeping `F = 0` as the next step. A
single mean bound on `D ∪ F` gives every positivity assertion required
by that next step. One-hot is needed only for its strict mean bound. -/
theorem avoid_prefix_setup {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {D F : Finset ι} (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (hR : expCard ν (D ∪ F) < 1) :
    0 < totalMass (avoidWeight ν D) ∧
      LawData (avoidDist ν D) rank ∧
      expCard (avoidDist ν D) F < 1 ∧
      1 - expCard ν (D ∪ F) ≤
        totalMass (avoidWeight ν D) * totalMass (avoidWeight (avoidDist ν D) F) := by
  have hDmean := expCard_mono hw.nn (subset_union_left (s₁ := D) (s₂ := F))
  have hD : 0 < totalMass (avoidWeight ν D) :=
    (sub_pos.mpr (hDmean.trans_lt hR)).trans_le (hw.avoid_mass_ge D)
  have hwa := hw.avoid D hD
  have hprod := hw.avoid_mass_ge (D ∪ F)
  rw [← avoid_chain_mass hD] at hprod
  have hFpos : 0 < totalMass (avoidWeight (avoidDist ν D) F) := by
    by_contra! hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hD.le hn
    linarith only [hp, hprod, hR]
  have honeF' : ∀ T, avoidDist ν D T ≠ 0 → (T ∩ F).card ≤ 1 :=
    fun T hT => honeF T (avoidDist_ne_zero_imp hT).1
  have hs := onehot_mean_add_avoid honeF'
  rw [hwa.tot] at hs
  exact ⟨hD, hwa, by linarith only [hs, hFpos], hprod⟩

/-- Expected counts under a restriction, before division. No normalization
or positivity of the scalar mass is needed for this inequality. -/
theorem restriction_expCard_le {μ ν : Finset ι → ℝ} (hμ : WeightNonneg μ)
    {M : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (D : Finset ι) : expCard ν D * M ≤ expCard μ D := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [hunwind]
  exact weightMass_mono hμ fun _ hT => hT.1

/-- A positive lower mass floor turns an original mean bound into a
conditional bound. This is the overlap charge `h / P_pre` in both branches. -/
theorem restriction_expCard_bound {μ ν : Finset ι → ℝ}
    (hμ : WeightNonneg μ) (hν : WeightNonneg ν)
    {M m b : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hm : 0 < m) (hM : m ≤ M) {D : Finset ι} (hb : expCard μ D ≤ b) :
    expCard ν D ≤ b / m := by
  apply (le_div_iff₀ hm).mpr
  exact (mul_le_mul_of_nonneg_left hM (expCard_nonneg hν D)).trans
    ((restriction_expCard_le hμ hunwind D).trans hb)

end TSPGap.Song

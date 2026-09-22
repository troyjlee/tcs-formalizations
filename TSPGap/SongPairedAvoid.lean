/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRankConcentration

/-!
# The last avoidance in Song's paired-bundle tables

This is the common argument on printed pages 33 and 35 of Song's Lemma 21.
The input law is already conditioned (the paper's `E₀` or `E₁`).  Two
disjoint pairs of count sets have a near-certain common rank.  Avoiding
the second set gives seven bounds on the three remaining sets.

The sharp upper bounds for unions use fixed-rank conservation under
avoidance, not a sum of separately transferred marginal bounds.  The
initial conditioned laws and their input mean bounds remain obligations
of the paired-bundle assembly; this file does not construct them.
-/

namespace TSPGap.Song
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Transfer a near-certain event using a positive lower bound for the
avoiding mass.  No independence or disjointness of the event is needed. -/
theorem avoid_near_certain {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
    {B : Finset ι} {m δ : ℝ} (hm : 0 < m)
    (hmass : m ≤ totalMass (avoidWeight w B))
    {Q : Finset ι → Prop} (hQ : 1 - δ ≤ weightMass w Q) :
    1 - δ / m ≤ weightMass (avoidDist w B) Q := by
  have hpos := hm.trans_le hmass
  have hv := hw.avoid B hpos
  have ht := cond_near_certain hw.nn hv.tot (hw.avoid_unwind hpos) Q
  rw [weightMass_not, hw.tot] at ht
  have hq := weightMass_le_one hv.nn hv.tot Q
  have hcross : (1 - weightMass (avoidDist w B) Q) * m ≤ δ := by
    have := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hq)
    nlinarith only [this, ht, hQ]
  have := (le_div_iff₀ hm).mpr hcross
  linarith only [this]

/-- Symbolic seven-row table.  `d` is the original rank-mean error and
`t` the error after avoidance, rather than probabilities of failure. -/
structure PairedAvoidBounds (ν : Finset ι → ℝ) (A U W : Finset ι)
    (j lower upper d t : ℝ) : Prop where
  a : lower ≤ expCard ν A ∧ expCard ν A ≤ 2 * upper
  u : max 0 (j - t - 2 * upper) ≤ expCard ν U ∧
    expCard ν U ≤ j + t - lower
  w : j - t ≤ expCard ν W ∧ expCard ν W ≤ j + d
  au : j - t ≤ expCard ν (A ∪ U) ∧ expCard ν (A ∪ U) ≤ j + t
  aw : lower + j - t ≤ expCard ν (A ∪ W) ∧
    expCard ν (A ∪ W) ≤ upper + j + d
  uw : max 0 (j - t - 2 * upper) + j - t ≤ expCard ν (U ∪ W) ∧
    expCard ν (U ∪ W) ≤ 2 * (j + d) - lower
  auw : 2 * (j - t) ≤ expCard ν ((A ∪ U) ∪ W) ∧
    expCard ν ((A ∪ U) ∪ W) ≤ 2 * (j + d)

/-- Both of Song's final-avoidance tables, uniformly in the central rank.
In the two applications `j = 2` and `j = 1`, respectively. -/
theorem paired_avoid_bounds {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
    {A B U W : Finset ι}
    (hAB : Disjoint A B) (hAU : Disjoint A U) (hAW : Disjoint A W)
    (hBU : Disjoint B U) (hBW : Disjoint B W) (hUW : Disjoint U W)
    {j : ℕ} {lower upper δ : ℝ} (hupper : upper < 1)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) (hθ : δ / (1 - upper) < 1 / 2)
    (hAl : lower ≤ expCard w A) (hAu : expCard w A ≤ upper)
    (hBu : expCard w B ≤ upper)
    (hX : 1 - δ ≤ weightMass w (fun T => (T ∩ (A ∪ U)).card = j))
    (hY : 1 - δ ≤ weightMass w (fun T => (T ∩ (B ∪ W)).card = j)) :
    1 - upper ≤ totalMass (avoidWeight w B) ∧
      PairedAvoidBounds (avoidDist w B) A U W j lower upper
        (rankPsi δ) (rankPsi (δ / (1 - upper))) := by
  have hm : 0 < 1 - upper := sub_pos.mpr hupper
  have hmass : 1 - upper ≤ totalMass (avoidWeight w B) := by
    linarith only [hw.avoid_mass_ge B, hBu]
  have hpos := hm.trans_le hmass
  have hv := hw.avoid B hpos
  have hθ0 := div_nonneg hδ0 hm.le
  have hXv := avoid_near_certain hw hm hmass hX
  have hYv := avoid_near_certain hw hm hmass hY
  have hWv : 1 - δ / (1 - upper) ≤
      weightMass (avoidDist w B) (fun T => (T ∩ W).card = j) := by
    have heq : weightMass (avoidDist w B) (fun T => (T ∩ (B ∪ W)).card = j) =
        weightMass (avoidDist w B) (fun T => (T ∩ W).card = j) := by
      refine weightMass_congr_of_support fun T hT => ?_
      have hz := (avoidDist_ne_zero_imp hT).2
      rw [card_eq_zero] at hz
      rw [inter_union_distrib_left, hz, empty_union]
    rwa [heq] at hYv
  have hXup := expCard_le_rankPsi hw (A ∪ U) hδ0 hδ hX
  have hYup := expCard_le_rankPsi hw (B ∪ W) hδ0 hδ hY
  have hXvlo := rankPsi_le_expCard hv (A ∪ U) hθ0 hθ hXv
  have hXvup := expCard_le_rankPsi hv (A ∪ U) hθ0 hθ hXv
  have hWvlo := rankPsi_le_expCard hv W hθ0 hθ hWv
  have ha_lo := hAl.trans (hw.avoid_ge hAB hpos)
  have ha_up := hw.avoid_le hAB hpos
  have hw_up := hw.avoid_le hBW.symm hpos
  have haw_up := hw.avoid_le (disjoint_union_left.mpr ⟨hAB, hBW.symm⟩) hpos
  have huw_up := hw.avoid_le (disjoint_union_left.mpr ⟨hBU.symm, hBW.symm⟩) hpos
  have hauw_up := hw.avoid_le
    (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hAB, hBU.symm⟩, hBW.symm⟩) hpos
  have hu_nn := expCard_nonneg hv.nn U
  have hAUW := disjoint_union_left.mpr ⟨hAW, hUW⟩
  rw [expCard_union_of_disjoint _ hAU] at hXup hXvlo hXvup
  rw [expCard_union_of_disjoint _ hBW] at hYup
  rw [expCard_union_of_disjoint (avoidDist w B) hAW,
    expCard_union_of_disjoint w hAW] at haw_up
  rw [expCard_union_of_disjoint (avoidDist w B) hUW,
    expCard_union_of_disjoint w hUW] at huw_up
  rw [expCard_union_of_disjoint (avoidDist w B) hAUW,
    expCard_union_of_disjoint (avoidDist w B) hAU,
    expCard_union_of_disjoint w hAUW, expCard_union_of_disjoint w hAU] at hauw_up
  have hu_lo : max 0 ((j : ℝ) - rankPsi (δ / (1 - upper)) - 2 * upper) ≤
      expCard (avoidDist w B) U := by
    rw [max_le_iff]
    constructor
    · exact hu_nn
    · linarith only [hXvlo, ha_up, hAu, hBu]
  refine ⟨hmass, ?_⟩
  constructor
  · exact ⟨ha_lo, by linarith only [ha_up, hAu, hBu]⟩
  · exact ⟨hu_lo, by linarith only [hXvup, ha_lo]⟩
  · exact ⟨hWvlo, by linarith only [hw_up, hYup]⟩
  · rw [expCard_union_of_disjoint _ hAU]
    exact ⟨hXvlo, hXvup⟩
  · rw [expCard_union_of_disjoint _ hAW]
    constructor <;> linarith only [ha_lo, hWvlo, haw_up, hAu, hYup]
  · rw [expCard_union_of_disjoint _ hUW]
    constructor <;> linarith only [hu_lo, hWvlo, huw_up, hXup, hYup, hAl]
  · rw [expCard_union_of_disjoint _ hAUW, expCard_union_of_disjoint _ hAU]
    constructor <;> linarith only [hXvlo, hWvlo, hauw_up, hXup, hYup]

end TSPGap.Song

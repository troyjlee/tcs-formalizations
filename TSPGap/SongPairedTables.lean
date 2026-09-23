/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedAvoid
import TSPGap.SongPairedBudgets

/-!
# Song's paired-bundle mean tables

The seven rows on printed pages 33 and 35 of Lemma 21, with weak decimal
bounds sufficient for capacity extraction.  The two public producers take
the paper's already-conditioned input means and central-rank probabilities
as explicit hypotheses.  They do not yet construct the initial `E₀`/`E₁`
laws, identify the happy event, or improve the end-to-end gap.
-/

namespace TSPGap.Song

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `Z = 0` table, with target counts `(1,1,2)`. -/
structure PairedAbsentMeans (ν : Finset ι → ℝ) (A U W : Finset ι) : Prop where
  a : 0.3407 ≤ expCard ν A ∧ expCard ν A ≤ 1.2786
  u : 0.4905 ≤ expCard ν U ∧ expCard ν U ≤ 1.8902
  w : 1.7691 ≤ expCard ν W ∧ expCard ν W ≤ 2.0672
  au : 1.7691 ≤ expCard ν (A ∪ U) ∧ expCard ν (A ∪ U) ≤ 2.2309
  aw : 2.1098 ≤ expCard ν (A ∪ W) ∧ expCard ν (A ∪ W) ≤ 2.7065
  uw : 2.2597 ≤ expCard ν (U ∪ W) ∧ expCard ν (U ∪ W) ≤ 3.7937
  auw : 3.5382 ≤ expCard ν ((A ∪ U) ∪ W) ∧ expCard ν ((A ∪ U) ∪ W) ≤ 4.1344

/-- The `Z = 1` table, with target counts `(1,0,1)`. -/
structure PairedPresentMeans (ν : Finset ι → ℝ) (A U W : Finset ι) : Prop where
  a : 0.3226 ≤ expCard ν A ∧ expCard ν A ≤ 1.1250
  u : 0 ≤ expCard ν U ∧ expCard ν U ≤ 0.8646
  w : 0.8127 ≤ expCard ν W ∧ expCard ν W ≤ 1.0705
  au : 0.8127 ≤ expCard ν (A ∪ U) ∧ expCard ν (A ∪ U) ≤ 1.1873
  aw : 1.1354 ≤ expCard ν (A ∪ W) ∧ expCard ν (A ∪ W) ≤ 1.6330
  uw : 0.8127 ≤ expCard ν (U ∪ W) ∧ expCard ν (U ∪ W) ≤ 1.8182
  auw : 1.6255 ≤ expCard ν ((A ∪ U) ∪ W) ∧ expCard ν ((A ∪ U) ∪ W) ≤ 2.1409

theorem paired_absent_table {w : Finset ι → ℝ} {A U W : Finset ι}
    (hm : PairedAvoidBounds w A U W 2 pairedAbsentLower pairedAbsentUpper
      (rankPsi pairedAbsentDefect)
      (rankPsi (pairedAbsentDefect / (1 - pairedAbsentUpper)))) :
    PairedAbsentMeans w A U W := by
  obtain ⟨_, hl, hu, _, _, _, hd, ht⟩ := paired_absent_budget
  have huLo := (le_max_right 0
    (2 - rankPsi (pairedAbsentDefect / (1 - pairedAbsentUpper)) -
      2 * pairedAbsentUpper)).trans hm.u.1
  have huwLo := hm.uw.1
  have hmax := le_max_right 0
    (2 - rankPsi (pairedAbsentDefect / (1 - pairedAbsentUpper)) - 2 * pairedAbsentUpper)
  constructor
  · constructor <;> linarith only [hm.a.1, hm.a.2, hl, hu]
  · constructor <;> linarith only [huLo, hm.u.2, hl, hu, ht]
  · constructor <;> linarith only [hm.w.1, hm.w.2, hd, ht]
  · constructor <;> linarith only [hm.au.1, hm.au.2, ht]
  · constructor <;> linarith only [hm.aw.1, hm.aw.2, hl, hu, hd, ht]
  · constructor <;> linarith only [huwLo, hmax, hm.uw.2, hl, hu, hd, ht]
  · constructor <;> linarith only [hm.auw.1, hm.auw.2, hd, ht]

theorem paired_present_table {w : Finset ι → ℝ} {A U W : Finset ι}
    (hm : PairedAvoidBounds w A U W 1 pairedPresentLower pairedPresentUpper
      (rankPsi pairedPresentDefect)
      (rankPsi (pairedPresentDefect / (1 - pairedPresentUpper)))) :
    PairedPresentMeans w A U W := by
  obtain ⟨_, hl, hu, _, _, _, hd, ht⟩ := paired_present_budget
  have hmax := le_max_left 0
    (1 - rankPsi (pairedPresentDefect / (1 - pairedPresentUpper)) - 2 * pairedPresentUpper)
  constructor
  · constructor <;> linarith only [hm.a.1, hm.a.2, hl, hu]
  · constructor <;> linarith only [hmax, hm.u.1, hm.u.2, hl, ht]
  · constructor <;> linarith only [hm.w.1, hm.w.2, hd, ht]
  · constructor <;> linarith only [hm.au.1, hm.au.2, ht]
  · constructor <;> linarith only [hm.aw.1, hm.aw.2, hl, hu, hd, ht]
  · constructor <;> linarith only [hmax, hm.uw.1, hm.uw.2, hl, hd, ht]
  · constructor <;> linarith only [hm.auw.1, hm.auw.2, hd, ht]

/-- Last-avoidance producer for the absent branch.  All input law bounds
are explicit; positivity of the normalizing mass is derived. -/
theorem paired_absent_means {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
    {A B U W : Finset ι}
    (hAB : Disjoint A B) (hAU : Disjoint A U) (hAW : Disjoint A W)
    (hBU : Disjoint B U) (hBW : Disjoint B W) (hUW : Disjoint U W)
    (hAl : pairedAbsentLower ≤ expCard w A) (hAu : expCard w A ≤ pairedAbsentUpper)
    (hBu : expCard w B ≤ pairedAbsentUpper)
    (hX : 1 - pairedAbsentDefect ≤ weightMass w (fun T => (T ∩ (A ∪ U)).card = 2))
    (hY : 1 - pairedAbsentDefect ≤ weightMass w (fun T => (T ∩ (B ∪ W)).card = 2)) :
    0.3607 ≤ totalMass (avoidWeight w B) ∧
      LawData (avoidDist w B) rank ∧ PairedAbsentMeans (avoidDist w B) A U W := by
  obtain ⟨_, _, hu, hd0, hd, ht, _, _⟩ := paired_absent_budget
  have hu1 : pairedAbsentUpper < 1 := by linarith only [hu]
  obtain ⟨hmass, hm⟩ := paired_avoid_bounds hw hAB hAU hAW hBU hBW hUW
    hu1 hd0 hd ht hAl hAu hBu hX hY
  have hpos : 0 < totalMass (avoidWeight w B) := by linarith only [hmass, hu]
  exact ⟨by linarith only [hmass, hu], hw.avoid B hpos, paired_absent_table hm⟩

/-- Last-avoidance producer for the present branch. -/
theorem paired_present_means {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
    {A B U W : Finset ι}
    (hAB : Disjoint A B) (hAU : Disjoint A U) (hAW : Disjoint A W)
    (hBU : Disjoint B U) (hBW : Disjoint B W) (hUW : Disjoint U W)
    (hAl : pairedPresentLower ≤ expCard w A) (hAu : expCard w A ≤ pairedPresentUpper)
    (hBu : expCard w B ≤ pairedPresentUpper)
    (hX : 1 - pairedPresentDefect ≤ weightMass w (fun T => (T ∩ (A ∪ U)).card = 1))
    (hY : 1 - pairedPresentDefect ≤ weightMass w (fun T => (T ∩ (B ∪ W)).card = 1)) :
    0.4375 ≤ totalMass (avoidWeight w B) ∧
      LawData (avoidDist w B) rank ∧ PairedPresentMeans (avoidDist w B) A U W := by
  obtain ⟨_, _, hu, hd0, hd, ht, _, _⟩ := paired_present_budget
  have hu1 : pairedPresentUpper < 1 := by linarith only [hu]
  obtain ⟨hmass, hm⟩ := paired_avoid_bounds hw hAB hAU hAW hBU hBW hUW
    hu1 hd0 hd ht hAl hAu hBu hX hY
  have hpos : 0 < totalMass (avoidWeight w B) := by linarith only [hmass, hu]
  exact ⟨by linarith only [hmass, hu], hw.avoid B hpos,
    paired_present_table (by simpa only [Nat.cast_one] using hm)⟩

end TSPGap.Song

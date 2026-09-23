/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRankConcentration

/-!
# Song's containing-set marginal shift (Lemma 20)

Concentration of a containing set `L` bounds the change of any `D ⊆ L`.
The residual `L \ D` has the favorable marginal-shift sign, so the change on
`D` cannot exceed the change on `L`.  An upper mean bound from Lemma 12 and
the elementary lower bound `E[L] ≥ j P[L=j]` close the estimate.

Avoidance and one-hot presence are the existing stable conditioning laws;
their masses must be positive.  The overlap extension allows `F ∩ L ⊆ D`
when avoiding `F`, and concludes only the upper bound, not a shift sign.

Unlike the paper's `j ∈ {1,2}`, these statements permit every natural `j`.
Only the defect used in the upper mean bound needs to be below `1/2`.
The other defect enters the elementary lower bound and needs no separate
range hypothesis.  No payment parameter or end-to-end gap changes here.
-/

namespace TSPGap.Song
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The containing-set argument is pure expectation algebra. -/
theorem shift_le_of_residual {w v : Finset ι → ℝ} {D L : Finset ι}
    (hDL : D ⊆ L) (hres : expCard w (L \ D) ≤ expCard v (L \ D)) :
    expCard v D - expCard w D ≤ expCard v L - expCard w L := by
  rw [expCard_sdiff_of_subset w hDL, expCard_sdiff_of_subset v hDL] at hres
  linarith

/-- Concentration only at the upper-mean law needs the SR package. -/
theorem shift_le_rankPhi {w v : Finset ι → ℝ} {r : ℕ}
    (hnn : WeightNonneg w) (hv : LawData v r) {D L : Finset ι} (hDL : D ⊆ L)
    (hres : expCard w (L \ D) ≤ expCard v (L \ D))
    {j : ℕ} {δw δv : ℝ} (hδv0 : 0 ≤ δv) (hδv : δv < 1 / 2)
    (hwj : 1 - δw ≤ weightMass w (fun T => (T ∩ L).card = j))
    (hvj : 1 - δv ≤ weightMass v (fun T => (T ∩ L).card = j)) :
    expCard v D - expCard w D ≤ rankPhi δv + (j : ℝ) * δw := by
  have hshift := shift_le_of_residual hDL hres
  have hlow := central_mass_mean_le hnn L hwj
  have hupp := expCard_le_rankPsi hv L hδv0 hδv hvj
  have hphi := rankPsi_le_rankPhi hδv0 hδv
  nlinarith only [hshift, hlow, hupp, hphi]

/-- Song's overlap extension under avoidance.  No lower sign is asserted
when the set being counted can contain coordinates forced absent. -/
theorem avoid_shift_le {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r)
    {D L F : Finset ι} (hDL : D ⊆ L) (hoverlap : F ∩ L ⊆ D)
    (hmass : 0 < totalMass (avoidWeight w F))
    {j : ℕ} {δminus δplus : ℝ} (hδ0 : 0 ≤ δplus) (hδ : δplus < 1 / 2)
    (hminus : 1 - δminus ≤ weightMass w (fun T => (T ∩ L).card = j))
    (hplus : 1 - δplus ≤
      weightMass (avoidDist w F) (fun T => (T ∩ L).card = j)) :
    expCard (avoidDist w F) D - expCard w D ≤ rankPhi δplus + (j : ℝ) * δminus := by
  have hres : Disjoint (L \ D) F := by
    refine disjoint_left.mpr fun e he hf => ?_
    exact (mem_sdiff.mp he).2 (hoverlap (mem_inter.mpr ⟨hf, (mem_sdiff.mp he).1⟩))
  exact shift_le_rankPhi hw.nn (hw.avoid F hmass) hDL (hw.avoid_ge hres hmass)
    hδ0 hδ hminus hplus

/-- Song, Lemma 20, avoiding a disjoint set: sign and magnitude together. -/
theorem avoid_shift {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r)
    {D L F : Finset ι} (hDL : D ⊆ L) (hLF : Disjoint L F)
    (hmass : 0 < totalMass (avoidWeight w F))
    {j : ℕ} {δminus δplus : ℝ} (hδ0 : 0 ≤ δplus) (hδ : δplus < 1 / 2)
    (hminus : 1 - δminus ≤ weightMass w (fun T => (T ∩ L).card = j))
    (hplus : 1 - δplus ≤
      weightMass (avoidDist w F) (fun T => (T ∩ L).card = j)) :
    0 ≤ expCard (avoidDist w F) D - expCard w D ∧
      expCard (avoidDist w F) D - expCard w D ≤ rankPhi δplus + (j : ℝ) * δminus := by
  have hoverlap : F ∩ L ⊆ D := by
    intro e he
    exact False.elim (disjoint_left.mp hLF (mem_inter.mp he).2 (mem_inter.mp he).1)
  exact ⟨sub_nonneg.mpr (hw.avoid_ge (hLF.mono_left hDL) hmass),
    avoid_shift_le hw hDL hoverlap hmass hδ0 hδ hminus hplus⟩

/-- Song, Lemma 20, conditioning a one-hot bundle present.
One-hot support is essential for the existing maximum-face conditioning API. -/
theorem present_shift {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r)
    {D L F : Finset ι} (hDL : D ⊆ L) (hLF : Disjoint L F)
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ 1)
    (hmass : 0 < totalMass (presentWeight w F))
    {j : ℕ} {δminus δplus : ℝ} (hδ0 : 0 ≤ δminus) (hδ : δminus < 1 / 2)
    (hminus : 1 - δminus ≤ weightMass w (fun T => (T ∩ L).card = j))
    (hplus : 1 - δplus ≤ weightMass (faceDist w (indicatorCost F) 1)
      (fun T => (T ∩ L).card = j)) :
    0 ≤ expCard w D - expCard (faceDist w (indicatorCost F) 1) D ∧
      expCard w D - expCard (faceDist w (indicatorCost F) 1) D ≤
        rankPhi δminus + (j : ℝ) * δplus := by
  have hv := hw.present hone hmass
  have hres := hw.present_le hone (hLF.mono_left (sdiff_subset (s := L) (t := D))) hmass
  exact ⟨sub_nonneg.mpr (hw.present_le hone (hLF.mono_left hDL) hmass),
    shift_le_rankPhi hv.nn hw hDL hres hδ0 hδ hplus hminus⟩

end TSPGap.Song

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongMarginalShift
import TSPGap.SongBundleConditioning

/-!
# The shared conditioning inputs to Song's paired-bundle tables

The last two steps constructing the laws `E₀` and `E₁` in Song's Lemma 21
(printed pages 33–35) are avoidance of `f`, followed by presence of `e(A)`.
They are constructed here on arbitrary coordinates.  The earlier atom face,
`Z` selection, `C` avoidance and `e(B)` avoidance are inputs, not hidden
assumptions about the original tree law.

All normalization masses and the combined event identity are explicit.
Rank defects can be transported from an original law through the combined
restriction, with no independence assumption.  Avoidance may overlap the
counted set: the lower bound then pays its overlap mean, whereas the sharp
upper bound uses Song's containing-set argument.  Neither payment constants
nor the proved end-to-end gap are changed by this module.
-/

namespace TSPGap.Song
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A near-certain event through any normalized restriction.  The positive
floor is a lower bound for the *whole* conditioning mass. -/
theorem restriction_near_certain {μ ν : Finset ι → ℝ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1)
    (hν : WeightNonneg ν) (hνtot : totalMass ν = 1)
    {M m δ : ℝ} {K Q : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hm : 0 < m) (hmass : m ≤ M) (hQ : 1 - δ ≤ weightMass μ Q) :
    1 - δ / m ≤ weightMass ν Q := by
  classical
  have ht := cond_near_certain hμ hνtot hunwind Q
  rw [weightMass_not, hμtot] at ht
  have hq := weightMass_le_one hν hνtot Q
  have hcross : (1 - weightMass ν Q) * m ≤ δ := by
    have := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hq)
    nlinarith only [this, ht, hQ]
  have := (le_div_iff₀ hm).mpr hcross
  linarith only [this]

omit [DecidableEq ι] in
/-- Composition of event restrictions; this is an equality for arbitrary
weights and masses and does not require either normalization to be positive. -/
theorem restriction_compose {μ ν ξ : Finset ι → ℝ} {M N : ℝ}
    {K L : Finset ι → Prop}
    (hν : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hξ : ∀ P, weightMass ξ P * N = weightMass ν (fun T => P T ∧ L T))
    (P : Finset ι → Prop) :
    weightMass ξ P * (M * N) = weightMass μ (fun T => P T ∧ (L T ∧ K T)) := by
  calc
    _ = (weightMass ξ P * N) * M := by ring
    _ = weightMass μ (fun T => (P T ∧ L T) ∧ K T) := by rw [hξ, hν]
    _ = _ := weightMass_congr fun _ => and_assoc

/-- The honest lower bound for a count overlapping the avoided set. -/
theorem avoid_overlap_ge {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    (D F : Finset ι) (hmass : 0 < totalMass (avoidWeight ν F)) :
    expCard ν D - expCard ν (D ∩ F) ≤ expCard (avoidDist ν F) D := by
  have hdis : Disjoint (D \ F) F := disjoint_left.mpr fun _ hD hF => (mem_sdiff.mp hD).2 hF
  have hlow := hw.avoid_ge hdis hmass
  have hsplit := expCard_split ν D F
  exact (by linarith only [hlow, hsplit] :
    expCard ν D - expCard ν (D ∩ F) ≤ expCard (avoidDist ν F) (D \ F)).trans
      (expCard_mono (hw.avoid F hmass).nn sdiff_subset)

/-- The shared law: first avoid `F`, then present `E`. -/
noncomputable def pairedInputLaw (ν : Finset ι → ℝ) (F E : Finset ι) :
    Finset ι → ℝ := faceDist (avoidDist ν F) (indicatorCost E) 1

/-- Its joint conditioning mass, relative to the input law. -/
noncomputable def pairedInputMass (ν : Finset ι → ℝ) (F E : Finset ι) : ℝ :=
  totalMass (avoidWeight ν F) * totalMass (presentWeight (avoidDist ν F) E)

/-- Both stage masses are positive, presence preserves the fixed-rank stable
package, and avoidance can only increase the marginal of the disjoint `E`. -/
theorem paired_input_setup {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {F E : Finset ι} (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) (hE : 0 < expCard ν E) :
    0 < totalMass (avoidWeight ν F) ∧
      0 < totalMass (presentWeight (avoidDist ν F) E) ∧
      LawData (pairedInputLaw ν F E) rank ∧
      totalMass (avoidWeight ν F) * expCard ν E ≤ pairedInputMass ν F E := by
  have ha : 0 < totalMass (avoidWeight ν F) :=
    (sub_pos.mpr hF).trans_le (hw.avoid_mass_ge F)
  have hv := hw.avoid F ha
  have hone' : ∀ T, avoidDist ν F T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => hone T (avoidDist_ne_zero_imp hT).1
  have he := hw.avoid_ge hEF ha
  have hpm := totalMass_presentWeight_eq_expCard hone'
  have hp : 0 < totalMass (presentWeight (avoidDist ν F) E) := by
    rw [hpm]; exact hE.trans_le he
  refine ⟨ha, hp, hv.present hone' hp, ?_⟩
  unfold pairedInputMass
  rw [hpm]
  exact mul_le_mul_of_nonneg_left he ha.le

/-- The final law only uses configurations satisfying both restrictions. -/
theorem paired_input_support {ν : Finset ι → ℝ} {F E T : Finset ι}
    (hT : pairedInputLaw ν F E T ≠ 0) :
    ν T ≠ 0 ∧ (T ∩ F).card = 0 ∧ (T ∩ E).card = 1 := by
  have hp := presentDist_ne_zero_imp hT
  have ha := avoidDist_ne_zero_imp hp.1
  exact ⟨ha.1, ha.2, hp.2⟩

/-- Exact joint-event identity, with the two normalization factors retained. -/
theorem paired_input_unwind {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {F E : Finset ι} (ha : 0 < totalMass (avoidWeight ν F))
    (hp : 0 < totalMass (presentWeight (avoidDist ν F) E)) (P : Finset ι → Prop) :
    weightMass (pairedInputLaw ν F E) P * pairedInputMass ν F E =
      weightMass ν (fun T => P T ∧ ((T ∩ E).card = 1 ∧ (T ∩ F).card = 0)) :=
  restriction_compose (hw.avoid_unwind ha) ((hw.avoid F ha).present_unwind hp) P

/-- A pre-presence floor in the original space and an `E` marginal floor
give the original-space mass floor for both restrictions together. -/
theorem paired_input_mass_ge {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {F E : Finset ι} (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) {M pre e : ℝ}
    (hM : 0 ≤ M) (he : 0 < e) (hE : e ≤ expCard ν E)
    (hmass : pre ≤ M * totalMass (avoidWeight ν F)) :
    pre * e ≤ M * pairedInputMass ν F E := by
  obtain ⟨ha, _, _, hm⟩ := paired_input_setup hw hEF hone hF (he.trans_le hE)
  have h1 := mul_le_mul_of_nonneg_right hmass he.le
  have h2 := mul_le_mul_of_nonneg_left hE ha.le
  have h3 := mul_le_mul_of_nonneg_left (h2.trans hm) hM
  nlinarith only [h1, h3]

/-- Transport an original near-certain event to all three laws.  `pre` is
the original-space mass floor *after* avoidance.  The final floor is
`pre * e`, where `e` is a positive lower bound for the input `E` marginal.
Thus the pre-presence defect can safely be used at both sides of avoidance. -/
theorem paired_input_near_certain {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {M pre e δ : ℝ} {K Q : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hM : 0 < M) (hpre : 0 < pre)
    {F E : Finset ι} (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) (he : 0 < e) (hE : e ≤ expCard ν E)
    (hmass : pre ≤ M * totalMass (avoidWeight ν F))
    (hQ : 1 - δ ≤ weightMass μ Q) :
    1 - δ / pre ≤ weightMass ν Q ∧
      1 - δ / pre ≤ weightMass (avoidDist ν F) Q ∧
      1 - δ / (pre * e) ≤ weightMass (pairedInputLaw ν F E) Q := by
  obtain ⟨ha, hp, hv, _⟩ := paired_input_setup hw hEF hone hF (he.trans_le hE)
  have hwa := hw.avoid F ha
  have hamax : totalMass (avoidWeight ν F) ≤ 1 := by
    rw [totalMass_avoidWeight]; exact weightMass_le_one hw.nn hw.tot _
  have hpreM : pre ≤ M := hmass.trans (by nlinarith only [hamax, hM])
  have hfinal := paired_input_mass_ge hw hEF hone hF hM.le he hE hmass
  exact ⟨restriction_near_certain hμ hμtot hw.nn hw.tot hunwind hpre hpreM hQ,
    restriction_near_certain hμ hμtot hwa.nn hwa.tot
      (restriction_compose hunwind (hw.avoid_unwind ha)) hpre hmass hQ,
    restriction_near_certain hμ hμtot hv.nn hv.tot
      (restriction_compose hunwind (paired_input_unwind hw ha hp))
      (mul_pos hpre he) hfinal hQ⟩

/-- The three mean inputs to the paired tables, before their final `B = 0`
restriction.  The overlap loss is explicit; both upper bounds use the
same sharp pre-presence concentration error. -/
theorem paired_input_mean_bounds {ν : Finset ι → ℝ} {rank : ℕ}
    (hw : LawData ν rank) {A B X Y F E : Finset ι}
    (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hFX : F ∩ X ⊆ A) (hFY : Disjoint Y F)
    (hXE : Disjoint X E) (hBE : Disjoint B E) (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) (hE : 0 < expCard ν E)
    {j : ℕ} {δpre δpost lower upper loss : ℝ}
    (hδ0 : 0 ≤ δpre) (hδ : δpre < 1 / 2)
    (hAl : lower ≤ expCard ν A) (hAu : expCard ν A ≤ upper)
    (hBu : expCard ν B ≤ upper) (hloss : expCard ν (A ∩ F) ≤ loss)
    (hX : 1 - δpre ≤ weightMass ν (fun T => (T ∩ X).card = j))
    (hY : 1 - δpre ≤ weightMass ν (fun T => (T ∩ Y).card = j))
    (hXa : 1 - δpre ≤ weightMass (avoidDist ν F) (fun T => (T ∩ X).card = j))
    (hYa : 1 - δpre ≤ weightMass (avoidDist ν F) (fun T => (T ∩ Y).card = j))
    (hXp : 1 - δpost ≤ weightMass (pairedInputLaw ν F E)
      (fun T => (T ∩ X).card = j)) :
    lower - loss - rankPhi δpre - (j : ℝ) * δpost ≤ expCard (pairedInputLaw ν F E) A ∧
      expCard (pairedInputLaw ν F E) A ≤ upper + rankPhi δpre + (j : ℝ) * δpre ∧
      expCard (pairedInputLaw ν F E) B ≤ upper + rankPhi δpre + (j : ℝ) * δpre := by
  obtain ⟨ha, hp, _, _⟩ := paired_input_setup hw hEF hone hF hE
  have hwa := hw.avoid F ha
  have hone' : ∀ T, avoidDist ν F T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => hone T (avoidDist_ne_zero_imp hT).1
  have hAa := avoid_shift_le hw hAX hFX ha hδ0 hδ hX hXa
  have hBa := (avoid_shift hw hBY hFY ha hδ0 hδ hY hYa).2
  have hAlow := avoid_overlap_ge hw A F ha
  have hAp := present_shift hwa hAX hXE hone' hp hδ0 hδ hXa hXp
  have hBp := hwa.present_le hone' hBE hp
  dsimp only [pairedInputLaw]
  exact ⟨by linarith only [hAl, hloss, hAlow, hAp.2],
    by linarith only [hAu, hAa, hAp.1],
    by linarith only [hBu, hBa, hBp]⟩

/-- The complete input profile for the final-avoidance table.  `X` and `Y`
are the containing count sets, later instantiated as `A ∪ U` and `B ∪ W`. -/
structure PairedInputBounds (ν : Finset ι → ℝ) (rank : ℕ) (A B X Y : Finset ι)
    (j : ℕ) (lower upper δ : ℝ) : Prop where
  law : LawData ν rank
  a_lower : lower ≤ expCard ν A
  a_upper : expCard ν A ≤ upper
  b_upper : expCard ν B ≤ upper
  x_rank : 1 - δ ≤ weightMass ν (fun T => (T ∩ X).card = j)
  y_rank : 1 - δ ≤ weightMass ν (fun T => (T ∩ Y).card = j)

/-- Build the mean and rank inputs from an earlier restricted law and the
original rank probabilities.  No intermediate or final rank-concentration
hypothesis remains: all are derived from the original event and mass floor.
The original events need only agree with the residual count events on the
support of the earlier law, as happens after selecting `Z = 1`.
The construction permits any central rank, including zero. -/
theorem paired_input_profile {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {M pre e δ lower upper loss : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hM : 0 < M) (hpre : 0 < pre)
    {A B X Y F E : Finset ι}
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hFX : F ∩ X ⊆ A) (hFY : Disjoint Y F)
    (hXE : Disjoint X E) (hBE : Disjoint B E) (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) (he : 0 < e) (hE : e ≤ expCard ν E)
    (hmass : pre ≤ M * totalMass (avoidWeight ν F))
    (hδ0 : 0 ≤ δ) (hδ : δ / pre < 1 / 2)
    (hAl : lower ≤ expCard ν A) (hAu : expCard ν A ≤ upper)
    (hBu : expCard ν B ≤ upper) (hloss : expCard ν (A ∩ F) ≤ loss)
    {j : ℕ} {QX QY : Finset ι → Prop}
    (hX : 1 - δ ≤ weightMass μ QX) (hY : 1 - δ ≤ weightMass μ QY)
    (hXeq : ∀ T, ν T ≠ 0 → (QX T ↔ (T ∩ X).card = j))
    (hYeq : ∀ T, ν T ≠ 0 → (QY T ↔ (T ∩ Y).card = j)) :
    pre * e ≤ M * pairedInputMass ν F E ∧
      PairedInputBounds (pairedInputLaw ν F E) rank A B X Y j
        (lower - loss - rankPhi (δ / pre) - (j : ℝ) * (δ / (pre * e)))
        (upper + rankPhi (δ / pre) + (j : ℝ) * (δ / pre)) (δ / (pre * e)) := by
  have hx := paired_input_near_certain hμ hμtot hw hunwind hM hpre hEF hone hF he hE hmass hX
  have hy := paired_input_near_certain hμ hμtot hw hunwind hM hpre hEF hone hF he hE hmass hY
  have hx0 := weightMass_congr_of_support hXeq
  have hy0 := weightMass_congr_of_support hYeq
  have hxa := weightMass_congr_of_support (w := avoidDist ν F)
    (fun T hT => hXeq T (avoidDist_ne_zero_imp hT).1)
  have hya := weightMass_congr_of_support (w := avoidDist ν F)
    (fun T hT => hYeq T (avoidDist_ne_zero_imp hT).1)
  have hxp := weightMass_congr_of_support (w := pairedInputLaw ν F E)
    (fun T hT => hXeq T (paired_input_support hT).1)
  have hyp := weightMass_congr_of_support (w := pairedInputLaw ν F E)
    (fun T hT => hYeq T (paired_input_support hT).1)
  rw [hx0, hxa, hxp] at hx
  rw [hy0, hya, hyp] at hy
  obtain ⟨hlo, hhiA, hhiB⟩ := paired_input_mean_bounds hw hAX hBY hFX hFY hXE hBE
    hEF hone hF (he.trans_le hE) (div_nonneg hδ0 hpre.le) hδ hAl hAu hBu hloss
    hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2
  exact ⟨paired_input_mass_ge hw hEF hone hF hM.le he hE hmass,
    ⟨(paired_input_setup hw hEF hone hF (he.trans_le hE)).2.2.1,
      hlo, hhiA, hhiB, hx.2.2, hy.2.2⟩⟩

end TSPGap.Song

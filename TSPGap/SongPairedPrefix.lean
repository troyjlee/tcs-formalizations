/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongAvoidChain
import TSPGap.SongPairedBudgets

/-!
# Earlier conditioning prefixes in Song's paired-bundle argument

Starting from the atom-tree law, the low-Z branch avoids
`D = Z ∪ C ∪ e(B)`. The high-Z branch first presents Z and then avoids
`D = C ∪ e(B)`. Both leave `F = f` avoidance and `E = e(A)` presence to
the already constructed `pairedInputLaw`.

The branch theorems construct these prefixes and prove the exact Song
pre-presence and final mass floors. The scalar `M` is the mass of the
earlier atom-tree restriction; its lower bound is explicit, not an
independence assertion. The generic unwinding lemmas compose with its
existing face identity. Initial atom-face mean bounds and set geometry
remain inputs to be discharged by the fiber-tree instance.

In the high-Z branch fixed-rank conservation bounds every disjoint count
loss by `1 - E[Z] ≤ 3 epsilon`, sharper than the paper's rank-error bound.
No new Z-specific concentration argument or analytic closure is required.
The numerical table and end-to-end constants are unchanged.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The prefix in the high-Z branch, before avoiding `f`. -/
noncomputable def presentPrefixLaw (ν : Finset ι → ℝ) (Z D : Finset ι) :
    Finset ι → ℝ := avoidDist (faceDist ν (indicatorCost Z) 1) D

/-- Joint mass of the two prefix restrictions in their input law. -/
noncomputable def presentPrefixMass (ν : Finset ι → ℝ) (Z D : Finset ι) : ℝ :=
  totalMass (presentWeight ν Z) * totalMass (avoidWeight (faceDist ν (indicatorCost Z) 1) D)

/-- Presenting Z lowers the mean of the whole union being avoided. The
mass bound charges this union once, not separately for each zero set. -/
theorem present_prefix_setup {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {Z D F : Finset ι} (hRZ : Disjoint (D ∪ F) Z)
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (hZ : 0 < expCard ν Z) (hR : expCard ν (D ∪ F) < 1) :
    0 < totalMass (presentWeight ν Z) ∧
      0 < totalMass (avoidWeight (faceDist ν (indicatorCost Z) 1) D) ∧
      LawData (presentPrefixLaw ν Z D) rank ∧
      expCard (presentPrefixLaw ν Z D) F < 1 ∧
      expCard ν Z * (1 - expCard ν (D ∪ F)) ≤
        presentPrefixMass ν Z D * totalMass (avoidWeight (presentPrefixLaw ν Z D) F) := by
  have hmassZ : 0 < totalMass (presentWeight ν Z) := by
    rwa [totalMass_presentWeight_eq_expCard honeZ]
  have hwp := hw.present honeZ hmassZ
  have hRle := hw.present_le honeZ hRZ hmassZ
  have honeF' : ∀ T, faceDist ν (indicatorCost Z) 1 T ≠ 0 → (T ∩ F).card ≤ 1 :=
    fun T hT => honeF T (presentDist_ne_zero_imp hT).1
  obtain ⟨hD, hwa, hF, hprod⟩ := avoid_prefix_setup hwp honeF' (hRle.trans_lt hR)
  refine ⟨hmassZ, hD, hwa, hF, ?_⟩
  have h0 := mul_le_mul_of_nonneg_left (sub_le_sub_left hRle 1) hZ.le
  have h1 := mul_le_mul_of_nonneg_left hprod hZ.le
  dsimp only [presentPrefixMass, presentPrefixLaw]
  rw [totalMass_presentWeight_eq_expCard honeZ]
  nlinarith only [h0, h1]

/-- The high-Z prefix retains both conditions on its support. -/
theorem present_prefix_support {ν : Finset ι → ℝ} {Z D T : Finset ι}
    (hT : presentPrefixLaw ν Z D T ≠ 0) :
    ν T ≠ 0 ∧ (T ∩ Z).card = 1 ∧ (T ∩ D).card = 0 := by
  have ha := avoidDist_ne_zero_imp hT
  have hp := presentDist_ne_zero_imp ha.1
  exact ⟨hp.1, hp.2, ha.2⟩

/-- Exact event identity for composing the prefix with the atom-tree face. -/
theorem present_prefix_unwind {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {Z D : Finset ι} (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (hZ : 0 < totalMass (presentWeight ν Z))
    (hD : 0 < totalMass (avoidWeight (faceDist ν (indicatorCost Z) 1) D))
    (P : Finset ι → Prop) :
    weightMass (presentPrefixLaw ν Z D) P * presentPrefixMass ν Z D =
      weightMass ν (fun T => P T ∧ ((T ∩ D).card = 0 ∧ (T ∩ Z).card = 1)) :=
  restriction_compose (hw.present_unwind hZ) ((hw.present honeZ hZ).avoid_unwind hD) P

/-- High-Z prefix means. The lower bounds spend the Z deficiency; the
upper bounds spend only the mean of D. B may overlap D. -/
theorem present_prefix_mean_bounds {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {Z D A B E : Finset ι}
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (hZ : 0 < totalMass (presentWeight ν Z))
    (hD : 0 < totalMass (avoidWeight (faceDist ν (indicatorCost Z) 1) D))
    (hAZ : Disjoint A Z) (hBZ : Disjoint B Z) (hEZ : Disjoint E Z)
    (hDZ : Disjoint D Z) (hAD : Disjoint A D) (hED : Disjoint E D) :
    expCard ν A + expCard ν Z - 1 ≤ expCard (presentPrefixLaw ν Z D) A ∧
      expCard (presentPrefixLaw ν Z D) A ≤ expCard ν A + expCard ν D ∧
      expCard (presentPrefixLaw ν Z D) B ≤ expCard ν B + expCard ν D ∧
      expCard ν E + expCard ν Z - 1 ≤ expCard (presentPrefixLaw ν Z D) E := by
  have hwp := hw.present honeZ hZ
  have haL := (hw.present_ge honeZ hAZ hZ).trans (hwp.avoid_ge hAD hD)
  have heL := (hw.present_ge honeZ hEZ hZ).trans (hwp.avoid_ge hED hD)
  have haU := avoid_overlap_le hwp A D hD
  have hbU := avoid_overlap_le hwp B D hD
  have haP := hw.present_le honeZ hAZ hZ
  have hbP := hw.present_le honeZ hBZ hZ
  have hdP := hw.present_le honeZ hDZ hZ
  exact ⟨haL, haU.trans (add_le_add haP hdP), hbU.trans (add_le_add hbP hdP), heL⟩

/-- Song's low-Z pre-presence and full conditioning mass floors, for the
actual prefix `D = 0`. Initial union and E means are measured at the atom
face; `M` carries its original-space mass. -/
theorem paired_absent_prefix_mass {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {M : ℝ} (hM : 1 - 3 * d₀ ≤ M) {D F E : Finset ι}
    (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (honeE : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hED : Disjoint E D) (hEF : Disjoint E F)
    (hR : expCard ν (D ∪ F) ≤ 1 / 2 + 3 * epsilon + 2 * r + d₀ + 2 * h)
    (hE : 1 / 2 - 2 * h - 2 * r - 4 * d₀ ≤ expCard ν E) :
    0 < M * totalMass (avoidWeight ν D) ∧
      LawData (avoidDist ν D) rank ∧ expCard (avoidDist ν D) F < 1 ∧
      1 / 2 - 3 * h ≤ expCard (avoidDist ν D) E ∧
      pairedAbsentPreMass ≤ M * totalMass (avoidWeight ν D) *
        totalMass (avoidWeight (avoidDist ν D) F) ∧
      pairedAbsentMass ≤ M * totalMass (avoidWeight ν D) *
        pairedInputMass (avoidDist ν D) F E := by
  have hnum : 1 / 2 + 3 * epsilon + 2 * r + d₀ + 2 * h < (1 : ℝ) := by
    norm_num [epsilon, K, h, r, d₀]
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num [d₀]) hM
  obtain ⟨hD, hwa, hF, hprod⟩ := avoid_prefix_setup hw honeF (hR.trans_lt hnum)
  have he : 1 / 2 - 3 * h ≤ expCard (avoidDist ν D) E := by
    have hbase : 1 / 2 - 3 * h ≤ 1 / 2 - 2 * h - 2 * r - 4 * d₀ := by
      norm_num [h, r, d₀]
    exact (hbase.trans hE).trans (hw.avoid_ge hED hD)
  have hpre : pairedAbsentPreMass ≤ M * totalMass (avoidWeight ν D) *
      totalMass (avoidWeight (avoidDist ν D) F) := by
    have hl : 1 / 2 - 3 * epsilon - 2 * r - d₀ - 2 * h ≤
        totalMass (avoidWeight ν D) * totalMass (avoidWeight (avoidDist ν D) F) := by
      linarith only [hprod, hR]
    have hp := mul_le_mul hM hl (by norm_num [epsilon, K, h, r, d₀]) hMpos.le
    unfold pairedAbsentPreMass
    nlinarith only [hp]
  have hfinal := paired_input_mass_ge hwa hEF
    (fun T hT => honeE T (avoidDist_ne_zero_imp hT).1) hF (mul_pos hMpos hD).le
    (by norm_num [h] : (0 : ℝ) < 1 / 2 - 3 * h) he hpre
  exact ⟨mul_pos hMpos hD, hwa, hF, he, hpre, hfinal⟩

/-- Song's high-Z mass floors, with the prefix constructed in the source
order. The zero union is disjoint from Z, so it costs no more after its
presence. All normalizations are derived positive before they are used. -/
theorem paired_present_prefix_mass {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {M : ℝ} (hM : 1 - 3 * d₀ ≤ M) {Z D F E : Finset ι}
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (honeE : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hRZ : Disjoint (D ∪ F) Z) (hEZ : Disjoint E Z)
    (hED : Disjoint E D) (hEF : Disjoint E F)
    (hZ : 1 - 3 * epsilon ≤ expCard ν Z)
    (hR : expCard ν (D ∪ F) ≤ 1 / 2 + 2 * r + 2 * h + 4 * d₀)
    (hE : 1 / 2 - 2 * h - 2 * r - 4 * d₀ ≤ expCard ν E) :
    0 < M * presentPrefixMass ν Z D ∧
      LawData (presentPrefixLaw ν Z D) rank ∧ expCard (presentPrefixLaw ν Z D) F < 1 ∧
      1 / 2 - 2 * h - 2 * r - 4 * d₀ - 3 * epsilon ≤
        expCard (presentPrefixLaw ν Z D) E ∧
      pairedPresentPreMass ≤ M * presentPrefixMass ν Z D *
        totalMass (avoidWeight (presentPrefixLaw ν Z D) F) ∧
      pairedPresentMass ≤ M * presentPrefixMass ν Z D *
        pairedInputMass (presentPrefixLaw ν Z D) F E := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num [d₀]) hM
  have hZpos : 0 < expCard ν Z :=
    lt_of_lt_of_le (by norm_num [epsilon, K, h]) hZ
  have hnum : 1 / 2 + 2 * r + 2 * h + 4 * d₀ < (1 : ℝ) := by norm_num [r, h, d₀]
  obtain ⟨hz, hd, hwa, hF, hprod⟩ :=
    present_prefix_setup hw hRZ honeZ honeF hZpos (hR.trans_lt hnum)
  have hmPre : 0 < M * presentPrefixMass ν Z D := mul_pos hMpos (mul_pos hz hd)
  have he : 1 / 2 - 2 * h - 2 * r - 4 * d₀ - 3 * epsilon ≤
      expCard (presentPrefixLaw ν Z D) E := by
    have hlow := (hw.present_ge honeZ hEZ hz).trans ((hw.present honeZ hz).avoid_ge hED hd)
    change _ ≤ expCard (avoidDist (faceDist ν (indicatorCost Z) 1) D) E
    linarith only [hlow, hZ, hE]
  have hpre : pairedPresentPreMass ≤ M * presentPrefixMass ν Z D *
      totalMass (avoidWeight (presentPrefixLaw ν Z D) F) := by
    have hr : 1 / 2 - 2 * r - 2 * h - 4 * d₀ ≤ 1 - expCard ν (D ∪ F) := by
      linarith only [hR]
    have hp := mul_le_mul hZ hr (by norm_num [r, h, d₀]) hZpos.le
    have hp' := mul_le_mul hM (hp.trans hprod)
      (by norm_num [epsilon, K, h, r, d₀]) hMpos.le
    unfold pairedPresentPreMass
    nlinarith only [hp']
  have hfinal := paired_input_mass_ge hwa hEF
    (fun T hT => honeE T (present_prefix_support hT).1) hF hmPre.le
    (by norm_num [h, r, d₀, epsilon, K] :
      (0 : ℝ) < 1 / 2 - 2 * h - 2 * r - 4 * d₀ - 3 * epsilon) he hpre
  exact ⟨hmPre, hwa, hF, he, hpre, hfinal⟩

/-- The conservation loss in the high-Z prefix is strictly smaller than
the paper's rank-error budget. Existing table bounds can be kept unchanged. -/
theorem paired_present_conservation_budget :
    3 * epsilon < rankPhi pairedZMinus + pairedZPlus := by
  norm_num [epsilon, K, h, d₀, pairedZMinus, pairedZPlus, rankPhi, rankRatio]

end TSPGap.Song

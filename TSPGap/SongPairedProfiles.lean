/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedRanks
import TSPGap.SongPairedTables

/-!
# From the original rank events to both paired mean tables

The prefix packets are composed with their actual restriction identities.
The overlap charge is taken in the original law; every central-rank
probability is also transported from that law. No conditional rank
hypothesis is added. The source of the two original near-certain events,
coefficient extraction and happy-event identification remain separate.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The prefix packet supplies all numerical inputs to the shared profile.
Only original-law rank events and their supported count identities remain. -/
theorem PairedStartData.profile {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1)
    {A B E F Z U W : Finset ι} (G : PairedCountGeometry A B E F Z U W)
    {M pre e lower upper : ℝ}
    (H : PairedStartData ν rank (A \ E) (B \ F) (E ∩ A) F M pre e lower upper)
    {Kcond : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ Kcond T))
    (hpre : 0 < pre) (he : 0 < e) (hδ : epsilon / pre < 1 / 2)
    (hxFA : expCard μ (F ∩ A) ≤ h)
    {j : ℕ} {QX QY : Finset ι → Prop}
    (hX : 1 - epsilon ≤ weightMass μ QX) (hY : 1 - epsilon ≤ weightMass μ QY)
    (hXeq : ∀ T, ν T ≠ 0 →
      (QX T ↔ (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = j))
    (hYeq : ∀ T, ν T ≠ 0 →
      (QY T ↔ (T ∩ ((B \ F) ∪ (W \ (F ∪ Z)))).card = j)) :
    pre * e ≤ M * pairedInputMass ν F (E ∩ A) ∧
      PairedInputBounds (pairedInputLaw ν F (E ∩ A)) rank (A \ E) (B \ F)
        ((A \ E) ∪ (U \ (E ∪ Z))) ((B \ F) ∪ (W \ (F ∪ Z))) j
        (lower - h / pre - rankPhi (epsilon / pre) - (j : ℝ) * (epsilon / (pre * e)))
        (upper + rankPhi (epsilon / pre) + (j : ℝ) * (epsilon / pre))
        (epsilon / (pre * e)) := by
  have hamax : totalMass (avoidWeight ν F) ≤ 1 := by
    rw [totalMass_avoidWeight]
    exact weightMass_le_one H.law.nn H.law.tot _
  have hpreM : pre ≤ M := H.pre_mass.trans (by nlinarith only [hamax, H.mass_pos])
  have hloss := restriction_expCard_bound hμ H.law.nn hunwind hpre hpreM
    (paired_overlap_mean hμ hxFA (E := E))
  exact paired_input_profile hμ hμtot H.law hunwind H.mass_pos hpre
    subset_union_left subset_union_left G.fx G.yf G.xe G.be G.ef H.e_one
    H.f_mean he H.e_mean H.pre_mass (by norm_num [epsilon, K, h]) hδ
    H.a_lower H.a_upper H.b_upper hloss hX hY hXeq hYeq

/-- Low-Z profile with all rank inputs in the original law. The scalar M
is the original-space restriction mass, given by the exact identity. -/
theorem paired_absent_profile {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {A B C E F Z U W : Finset ι} {M : ℝ} {Kface : Finset ι → Prop}
    (hM : 0 < M)
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ Kface T))
    (G : PairedCountGeometry A B E F Z U W)
    (HP : PairedPrefixPair ν rank A B C E F Z M)
    (hxFA : expCard μ (F ∩ A) ≤ h)
    (hX : 1 - epsilon ≤ weightMass μ (fun T =>
      (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2))
    (hY : 1 - epsilon ≤ weightMass μ (fun T =>
      (T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2))
    (hZ : expCard ν Z ≤ 3 * epsilon) :
    pairedAbsentMass ≤ M * totalMass (avoidWeight ν (Z ∪ (C ∪ (E ∩ B)))) *
        pairedInputMass (avoidDist ν (Z ∪ (C ∪ (E ∩ B)))) F (E ∩ A) ∧
      PairedInputBounds (pairedInputLaw (avoidDist ν (Z ∪ (C ∪ (E ∩ B)))) F (E ∩ A))
        rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
        ((B \ F) ∪ (W \ (F ∪ Z))) 2
        pairedAbsentLower pairedAbsentUpper pairedAbsentDefect := by
  have H := HP.absent hZ
  have hm := pos_of_mul_pos_right H.mass_pos hM.le
  have hun := restriction_compose hunwind (hw.avoid_unwind hm)
  obtain ⟨hmass, HB⟩ := H.profile hμ hμtot G hun
    (by norm_num [pairedAbsentPreMass, epsilon, K, h, r, d₀])
    (by norm_num [h])
    (by norm_num [epsilon, pairedAbsentPreMass, K, h, r, d₀]) hxFA hX hY
    (fun T hT => (G.absent_rank_events hT).1)
    (fun T hT => (G.absent_rank_events hT).2)
  refine ⟨hmass, HB.law, ?_, ?_, ?_, HB.x_rank, HB.y_rank⟩
  · exact HB.a_lower
  · convert HB.a_upper using 1
    simp only [pairedAbsentUpper, pairedAbsentPreDefect, Nat.cast_ofNat]
    ring
  · convert HB.b_upper using 1
    simp only [pairedAbsentUpper, pairedAbsentPreDefect, Nat.cast_ofNat]
    ring

/-- High-Z profile. The pointwise rank split uses Z = 1, while the
stronger conservation lower mean implies the existing paper table budget. -/
theorem paired_present_profile {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {A B C E F Z U W : Finset ι} {M : ℝ} {Kface : Finset ι → Prop}
    (hM : 0 < M)
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ Kface T))
    (G : PairedCountGeometry A B E F Z U W)
    (HP : PairedPrefixPair ν rank A B C E F Z M)
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (hxFA : expCard μ (F ∩ A) ≤ h)
    (hX : 1 - epsilon ≤ weightMass μ (fun T =>
      (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2))
    (hY : 1 - epsilon ≤ weightMass μ (fun T =>
      (T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2))
    (hZ : 1 - 3 * epsilon ≤ expCard ν Z) :
    pairedPresentMass ≤ M * presentPrefixMass ν Z (C ∪ (E ∩ B)) *
        pairedInputMass (presentPrefixLaw ν Z (C ∪ (E ∩ B))) F (E ∩ A) ∧
      PairedInputBounds (pairedInputLaw (presentPrefixLaw ν Z (C ∪ (E ∩ B))) F (E ∩ A))
        rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
        ((B \ F) ∪ (W \ (F ∪ Z))) 1
        pairedPresentLower pairedPresentUpper pairedPresentDefect := by
  have H := HP.present hZ
  have hzp : 0 < totalMass (presentWeight ν Z) := by
    rw [totalMass_presentWeight_eq_expCard honeZ]
    exact lt_of_lt_of_le (by norm_num [epsilon, K, h]) hZ
  have hm := pos_of_mul_pos_right H.mass_pos hM.le
  have hdp := pos_of_mul_pos_right hm hzp.le
  have hun := restriction_compose hunwind (present_prefix_unwind hw honeZ hzp hdp)
  obtain ⟨hmass, HB⟩ := H.profile hμ hμtot G hun
    (by norm_num [pairedPresentPreMass, epsilon, K, h, r, d₀])
    (by norm_num [epsilon, K, h, r, d₀])
    (by norm_num [epsilon, pairedPresentPreMass, K, h, r, d₀]) hxFA hX hY
    (fun T hT => (G.present_rank_events hT).1)
    (fun T hT => (G.present_rank_events hT).2)
  refine ⟨hmass, HB.law, ?_, ?_, ?_, HB.x_rank, HB.y_rank⟩
  · have hl := HB.a_lower
    have hc := paired_present_conservation_budget
    simp only [Nat.cast_one, one_mul] at hl
    dsimp only [pairedPresentLower, pairedPresentDefect, pairedPresentMass,
      pairedPresentPreDefect]
    linarith only [hl, hc]
  · convert HB.a_upper using 1
    simp only [pairedPresentUpper, pairedPresentPreDefect, Nat.cast_one]
    ring
  · convert HB.b_upper using 1
    simp only [pairedPresentUpper, pairedPresentPreDefect, Nat.cast_one]
    ring

/-- Close the absent table once its profile is assembled. No new numerical
or probability premise is introduced at the final avoidance. -/
theorem PairedInputBounds.absent_table {ν : Finset ι → ℝ} {rank : ℕ}
    {A B E F Z U W : Finset ι} (G : PairedCountGeometry A B E F Z U W)
    (H : PairedInputBounds ν rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
      ((B \ F) ∪ (W \ (F ∪ Z))) 2 pairedAbsentLower pairedAbsentUpper pairedAbsentDefect) :
    0.3607 ≤ totalMass (avoidWeight ν (B \ F)) ∧
      LawData (avoidDist ν (B \ F)) rank ∧
      PairedAbsentMeans (avoidDist ν (B \ F)) (A \ E) (U \ (E ∪ Z)) (W \ (F ∪ Z)) :=
  paired_absent_means H.law G.ab G.au G.aw G.bu G.bw G.uw
    H.a_lower H.a_upper H.b_upper H.x_rank H.y_rank

/-- The present table keeps the central rank one and target `(1,0,1)`. -/
theorem PairedInputBounds.present_table {ν : Finset ι → ℝ} {rank : ℕ}
    {A B E F Z U W : Finset ι} (G : PairedCountGeometry A B E F Z U W)
    (H : PairedInputBounds ν rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
      ((B \ F) ∪ (W \ (F ∪ Z))) 1 pairedPresentLower pairedPresentUpper pairedPresentDefect) :
    0.4375 ≤ totalMass (avoidWeight ν (B \ F)) ∧
      LawData (avoidDist ν (B \ F)) rank ∧
      PairedPresentMeans (avoidDist ν (B \ F)) (A \ E) (U \ (E ∪ Z)) (W \ (F ∪ Z)) :=
  paired_present_means H.law G.ab G.au G.aw G.bu G.bw G.uw
    H.a_lower H.a_upper H.b_upper H.x_rank H.y_rank

end TSPGap.Song

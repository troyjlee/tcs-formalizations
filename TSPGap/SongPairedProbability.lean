/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedCapacity
import TSPGap.SongPairedHappy

/-!
# Original-law probabilities in both paired branches

Compose the prefix, avoid-F/present-E, and final avoidance identities with
their actual normalization masses. The coefficient events are transported
to any original event containing the raw restrictions and target counts.
The atom-face and graph interpretation is supplied by `SongPairedBundle`.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Append the last three restrictions to an already constructed prefix.
Every normalization is proved positive before its identity is used. -/
theorem PairedStartData.final_unwind {μ ν : Finset ι → ℝ} {rank : ℕ}
    {A B E F : Finset ι} {M pre e lower upper : ℝ}
    (H : PairedStartData ν rank A B E F M pre e lower upper)
    {Kcond : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ Kcond T))
    (hEF : Disjoint E F) (he : 0 < e)
    (hb : 0 < totalMass (avoidWeight (pairedInputLaw ν F E) B))
    (P : Finset ι → Prop) :
    weightMass (avoidDist (pairedInputLaw ν F E) B) P *
        (M * pairedInputMass ν F E * totalMass (avoidWeight (pairedInputLaw ν F E) B)) =
      weightMass μ (fun T => P T ∧ ((T ∩ B).card = 0 ∧
        (((T ∩ E).card = 1 ∧ (T ∩ F).card = 0) ∧ Kcond T))) := by
  obtain ⟨ha, hp, hl, _⟩ :=
    paired_input_setup H.law hEF H.e_one H.f_mean (he.trans_le H.e_mean)
  exact restriction_compose
    (restriction_compose hunwind (paired_input_unwind H.law ha hp))
    (hl.avoid_unwind hb) P

/-- The absent-Z branch, including all conditioning masses. Crossing is
needed only for the sure W baseline in the final coefficient extraction. -/
theorem paired_absent_probability {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {A B C E F Z U W : Finset ι} {M : ℝ} {Kface Happy : Finset ι → Prop}
    (hM : 0 < M)
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ Kface T))
    (G : PairedCountGeometry A B E F Z U W)
    (HP : PairedPrefixPair ν rank A B C E F Z M)
    (hxFA : expCard μ (F ∩ A) ≤ h)
    (hX : 1 - epsilon ≤ weightMass μ (fun T =>
      (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2))
    (hY : 1 - epsilon ≤ weightMass μ (fun T =>
      (T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2))
    (hZ : expCard ν Z ≤ 3 * epsilon)
    (hcross : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ W).card)
    (hhappy : ∀ T, μ T ≠ 0 → Kface T →
      (T ∩ (E ∩ A)).card = 1 → (T ∩ F).card = 0 →
      (T ∩ C).card = 0 → (T ∩ (B \ F)).card = 0 → (T ∩ Z).card = 0 →
      ((T ∩ (A \ E)).card = 1 ∧ (T ∩ (U \ (E ∪ Z))).card = 1 ∧
        (T ∩ (W \ (F ∪ Z))).card = 2) → Happy T) :
    p < weightMass μ Happy := by
  let ν₀ := avoidDist ν (Z ∪ (C ∪ (E ∩ B)))
  let ν₁ := pairedInputLaw ν₀ F (E ∩ A)
  let ξ := avoidDist ν₁ (B \ F)
  have H := HP.absent hZ
  have hd := pos_of_mul_pos_right H.mass_pos hM.le
  have hun := restriction_compose hunwind (hw.avoid_unwind hd)
  obtain ⟨hmass, HB⟩ := paired_absent_profile hμ hμtot hw hM hunwind G HP hxFA hX hY hZ
  obtain ⟨hb, hξ, hmeans⟩ := HB.absent_table G
  have hbp : 0 < totalMass (avoidWeight ν₁ (B \ F)) := lt_of_lt_of_le (by norm_num) hb
  have hfin := H.final_unwind hun G.ef (by norm_num [h]) hbp
  have hs (T : Finset ι) (hT : ξ T ≠ 0) :
      ν T ≠ 0 ∧ (T ∩ F).card = 0 ∧ (T ∩ Z).card = 0 := by
    have hi := paired_input_support (avoidDist_ne_zero_imp hT).1
    have ha := avoidDist_ne_zero_imp hi.1
    have hz := card_le_card (inter_subset_inter_left
      (subset_union_left (s₁ := Z) (s₂ := C ∪ (E ∩ B))) (s := T))
    exact ⟨ha.1, hi.2.1, by omega⟩
  have hbase := paired_absent_baseline
    (fun T hT => hcross T (hs T hT).1)
    (fun T hT => (hs T hT).2.1) (fun T hT => (hs T hT).2.2)
  have hk := paired_absent_counts hξ G.au G.aw G.uw hmeans hbase
  have hm0 : (0.2279 : ℝ) ≤
      M * totalMass (avoidWeight ν (Z ∪ (C ∪ (E ∩ B)))) * pairedInputMass ν₀ F (E ∩ A) :=
    paired_absent_budget.1.le.trans hmass
  have hm := mul_le_mul hm0 hb (by norm_num) (by linarith only [hm0])
  have hprod := mul_le_mul hk hm (by norm_num) (weightMass_nonneg hξ.nn _)
  have hraw := hfin (fun T => (T ∩ (A \ E)).card = 1 ∧
    (T ∩ (U \ (E ∪ Z))).card = 1 ∧ (T ∩ (W \ (F ∪ Z))).card = 2)
  rw [hraw] at hprod
  have hprob : p < _ := paired_product_margins.1
  have hbound := (show p < ((2 / 55 : ℝ) * 0.1098 ^ 3) * (0.2279 * 0.3607) by
    nlinarith only [hprob]).trans_le hprod
  have hsup : weightMass μ Happy = weightMass μ (fun T => μ T ≠ 0 → Happy T) :=
    weightMass_congr_of_support fun _ hT => ⟨fun h _ => h, fun h => h hT⟩
  rw [hsup]
  refine hbound.trans_le (weightMass_mono hμ fun T ht hT => ?_)
  obtain ⟨hcell, hB, ⟨hEA, hF⟩, hD, hface⟩ := ht
  have hC := card_le_card (inter_subset_inter_left
    (subset_union_left.trans subset_union_right : C ⊆ Z ∪ (C ∪ (E ∩ B))) (s := T))
  have hZ0 := card_le_card (inter_subset_inter_left
    (subset_union_left : Z ⊆ Z ∪ (C ∪ (E ∩ B))) (s := T))
  exact hhappy T hT hface hEA hF (by omega) hB (by omega) hcell

/-- The present-Z branch. The zero middle target remains an actual count
constraint after all restrictions are unwound to the original law. -/
theorem paired_present_probability {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {A B C E F Z U W : Finset ι} {M : ℝ} {Kface Happy : Finset ι → Prop}
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
    (hZ : 1 - 3 * epsilon ≤ expCard ν Z)
    (hhappy : ∀ T, μ T ≠ 0 → Kface T →
      (T ∩ (E ∩ A)).card = 1 → (T ∩ F).card = 0 →
      (T ∩ C).card = 0 → (T ∩ (B \ F)).card = 0 → (T ∩ Z).card = 1 →
      ((T ∩ (A \ E)).card = 1 ∧ (T ∩ (U \ (E ∪ Z))).card = 0 ∧
        (T ∩ (W \ (F ∪ Z))).card = 1) → Happy T) :
    p < weightMass μ Happy := by
  let ν₀ := presentPrefixLaw ν Z (C ∪ (E ∩ B))
  let ν₁ := pairedInputLaw ν₀ F (E ∩ A)
  have H := HP.present hZ
  have hz : 0 < totalMass (presentWeight ν Z) := by
    rw [totalMass_presentWeight_eq_expCard honeZ]
    exact lt_of_lt_of_le (by norm_num [epsilon, K, h]) hZ
  have hm := pos_of_mul_pos_right H.mass_pos hM.le
  have hd := pos_of_mul_pos_right hm hz.le
  have hun := restriction_compose hunwind (present_prefix_unwind hw honeZ hz hd)
  obtain ⟨hmass, HB⟩ :=
    paired_present_profile hμ hμtot hw hM hunwind G HP honeZ hxFA hX hY hZ
  obtain ⟨hb, hξ, hmeans⟩ := HB.present_table G
  have hbp : 0 < totalMass (avoidWeight ν₁ (B \ F)) := lt_of_lt_of_le (by norm_num) hb
  have hfin := H.final_unwind hun G.ef (by norm_num [h, r, d₀, epsilon, K]) hbp
  have hk := paired_present_counts hξ G.au G.aw G.uw hmeans
  have hm0 : (0.2182 : ℝ) ≤
      M * presentPrefixMass ν Z (C ∪ (E ∩ B)) * pairedInputMass ν₀ F (E ∩ A) :=
    paired_present_budget.1.le.trans hmass
  have hlast := mul_le_mul hm0 hb (by norm_num) (by linarith only [hm0])
  have hprod := mul_le_mul hk hlast (by norm_num) (weightMass_nonneg hξ.nn _)
  have hraw := hfin (fun T => (T ∩ (A \ E)).card = 1 ∧
    (T ∩ (U \ (E ∪ Z))).card = 0 ∧ (T ∩ (W \ (F ∪ Z))).card = 1)
  rw [hraw] at hprod
  have hprob : p < _ := paired_product_margins.2
  have hbound := (show p < ((1 / 8 : ℝ) * 0.1354 ^ 3) * (0.2182 * 0.4375) by
    nlinarith only [hprob]).trans_le hprod
  have hsup : weightMass μ Happy = weightMass μ (fun T => μ T ≠ 0 → Happy T) :=
    weightMass_congr_of_support fun _ hT => ⟨fun h _ => h, fun h => h hT⟩
  rw [hsup]
  refine hbound.trans_le (weightMass_mono hμ fun T ht hT => ?_)
  obtain ⟨hcell, hB, ⟨hEA, hF⟩, ⟨hD, hZ1⟩, hface⟩ := ht
  have hC := card_le_card (inter_subset_inter_left
    (subset_union_left : C ⊆ C ∪ (E ∩ B)) (s := T))
  exact hhappy T hT hface hEA hF (by omega) hB hZ1 hcell

end TSPGap.Song

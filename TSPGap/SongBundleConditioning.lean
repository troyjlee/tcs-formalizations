/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeFaces

/-!
# A clean present/avoid order for Song's large-bundle calculation

Present `E \ C` first, then avoid `C \ E`. On a one-hot bundle this is
exactly the support condition `E = 1, C = 0`. The part `C ∩ E` disappears
at the first step, so it is not charged again in the avoidance estimate.
Everything is generic in the coordinates; no graph or marginal rounding
is used. The original distribution in this module is already the atom face.
-/

namespace TSPGap.Song

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expCard_split (w : Finset ι → ℝ) (S E : Finset ι) :
    expCard w S = expCard w (S \ E) + expCard w (S ∩ E) := by
  conv_lhs => rw [← sdiff_union_inter S E]
  exact expCard_union_of_disjoint w (disjoint_sdiff_inter S E)

/-- Presenting a one-hot set changes any count by at most its deficiency,
including a count that overlaps the presented set. -/
theorem present_mean_bounds {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {E : Finset ι} (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hm : 0 < totalMass (presentWeight w E)) (S : Finset ι) :
    expCard w S + expCard w E - 1 ≤ expCard (faceDist w (indicatorCost E) 1) S ∧
    expCard (faceDist w (indicatorCost E) 1) S ≤ expCard w S + 1 - expCard w E := by
  have hlo := hw.face_inside_ge hone hm (inter_subset_right (s₁ := S))
  have hhi := hw.face_inside_le hone hm (inter_subset_right (s₁ := S))
  have hso : S \ E ⊆ Eᶜ := fun _ he => mem_compl.mpr (mem_sdiff.mp he).2
  have hLo := hw.face_outside_ge hone hm hso
  have hHi := hw.face_outside_le hone hm hso
  rw [faceDeficiency] at hhi hLo
  norm_num only [Nat.cast_one] at hhi hLo
  have hs := expCard_split w S E
  have hs' := expCard_split (faceDist w (indicatorCost E) 1) S E
  constructor <;> linarith

omit [Fintype ι] in
/-- The support equivalence needed after the two restrictions. -/
theorem clean_present_avoid_support {T E C : Finset ι}
    (hone : (T ∩ E).card ≤ 1) (hp : (T ∩ (E \ C)).card = 1)
    (ha : (T ∩ (C \ E)).card = 0) : (T ∩ E).card = 1 ∧ (T ∩ C).card = 0 := by
  have heq : T ∩ (E \ C) = T ∩ E :=
    eq_of_subset_of_card_le (inter_subset_inter_left sdiff_subset) (by omega)
  refine ⟨by rwa [heq] at hp, ?_⟩
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hT, hC⟩ := mem_inter.mp he
  by_cases hE : e ∈ E
  · have hh : e ∈ T ∩ (E \ C) := by rw [heq]; exact mem_inter.mpr ⟨hT, hE⟩
    exact (mem_sdiff.mp (mem_inter.mp hh).2).2 hC
  · have hh : e ∈ T ∩ (C \ E) := mem_inter.mpr ⟨hT, mem_sdiff.mpr ⟨hC, hE⟩⟩
    rw [card_eq_zero.mp ha] at hh
    exact notMem_empty e hh

noncomputable def cleanPresent (w : Finset ι → ℝ) (E C : Finset ι) : Finset ι → ℝ :=
  faceDist w (indicatorCost (E \ C)) 1

noncomputable def cleanBundleLaw (w : Finset ι → ℝ) (E C : Finset ι) : Finset ι → ℝ :=
  avoidDist (cleanPresent w E C) (C \ E)

noncomputable def cleanBundleMass (w : Finset ι → ℝ) (E C : Finset ι) : ℝ :=
  totalMass (presentWeight w (E \ C)) *
    totalMass (avoidWeight (cleanPresent w E C) (C \ E))

/-- The normalized law and its sharp transfers, constructed below. -/
structure CleanBundleData (w : Finset ι → ℝ) (E C : Finset ι) (k : ℕ) : Prop where
  mass_pos : 0 < cleanBundleMass w E C
  mass_ge : expCard w E - expCard w C ≤ cleanBundleMass w E C
  law : LawData (cleanBundleLaw w E C) k
  supp : ∀ T, cleanBundleLaw w E C T ≠ 0 →
    w T ≠ 0 ∧ (T ∩ E).card = 1 ∧ (T ∩ C).card = 0
  unwind : ∀ Q : Finset ι → Prop,
    weightMass (cleanBundleLaw w E C) Q * cleanBundleMass w E C =
      weightMass w (fun T => (Q T ∧ (T ∩ (C \ E)).card = 0) ∧ (T ∩ (E \ C)).card = 1)
  mean_lower : ∀ S, Disjoint S C →
    expCard w S + expCard w E - expCard w C - 1 ≤ expCard (cleanBundleLaw w E C) S
  mean_upper : ∀ S, Disjoint S C →
    expCard (cleanBundleLaw w E C) S ≤ expCard w S + 1 - expCard w E + expCard w C
  disjoint_upper : ∀ S, Disjoint S C → Disjoint S E →
    expCard (cleanBundleLaw w E C) S ≤ expCard w S + expCard w C
  contains_lower : ∀ S, Disjoint S C → E \ C ⊆ S →
    expCard w S ≤ expCard (cleanBundleLaw w E C) S
  contains_upper : ∀ S, Disjoint S C → E \ C ⊆ S →
    expCard (cleanBundleLaw w E C) S ≤ 1 + expCard w ((S ∪ C) \ E)

theorem cleanBundleData {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {E C : Finset ι} (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hc : expCard w C < 1) (hec : expCard w C < expCard w E) :
    CleanBundleData w E C k := by
  classical
  have hsplitE := expCard_split w E C
  have hsplitC := expCard_split w C E
  rw [inter_comm C E] at hsplitC
  have hEC := expCard_mono hw.nn (inter_subset_right (s₁ := E) (s₂ := C))
  have hone' : ∀ T, w T ≠ 0 → (T ∩ (E \ C)).card ≤ 1 := fun T hT =>
    (card_le_card (inter_subset_inter_left sdiff_subset)).trans (hone T hT)
  have hpmEq := totalMass_presentWeight_eq_expCard hone'
  have hp : 0 < totalMass (presentWeight w (E \ C)) := by rw [hpmEq]; linarith
  have hwp : LawData (cleanPresent w E C) k := hw.present hone' hp
  have hDE : Disjoint (C \ E) (E \ C) :=
    disjoint_of_subset_right sdiff_subset sdiff_disjoint
  have hpc : expCard (cleanPresent w E C) (C \ E) ≤ expCard w (C \ E) :=
    hw.present_le hone' hDE hp
  have hCc := expCard_mono hw.nn (sdiff_subset (s := C) (t := E))
  have ha : 0 < totalMass (avoidWeight (cleanPresent w E C) (C \ E)) := by
    have hh := hwp.avoid_mass_ge (C \ E)
    linarith
  have hwl : LawData (cleanBundleLaw w E C) k := hwp.avoid (C \ E) ha
  have hp1 : expCard w (E \ C) ≤ 1 := by
    rw [expCard_eq_weightMass_one hone']
    exact weightMass_le_one hw.nn hw.tot _
  have hpm : 0 < cleanBundleMass w E C := mul_pos hp ha
  have hmass : expCard w E - expCard w C ≤ cleanBundleMass w E C := by
    have hma := hwp.avoid_mass_ge (C \ E)
    have hh := mul_le_mul_of_nonneg_left hma hp.le
    rw [hpmEq] at hh
    have hn := expCard_nonneg hw.nn (C \ E)
    have hmul := mul_le_mul_of_nonneg_right hp1 hn
    unfold cleanBundleMass
    rw [hpmEq]
    nlinarith
  have hge : ∀ S, Disjoint S C →
      expCard (cleanPresent w E C) S ≤ expCard (cleanBundleLaw w E C) S :=
    fun _ hSC => hwp.avoid_ge (disjoint_of_subset_right sdiff_subset hSC) ha
  have hle : ∀ S, Disjoint S C → expCard (cleanBundleLaw w E C) S ≤
      expCard (cleanPresent w E C) S + expCard (cleanPresent w E C) (C \ E) :=
    fun _ hSC => hwp.avoid_le (disjoint_of_subset_right sdiff_subset hSC) ha
  have hself : expCard (cleanPresent w E C) (E \ C) = 1 := by
    rw [cleanPresent, expCard_faceDist, ← presentWeight, expCard_presentWeight_self,
      div_self hp.ne']
  refine ⟨hpm, hmass, hwl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    have ht := avoidDist_ne_zero_imp hT
    have hs := presentDist_ne_zero_imp ht.1
    exact ⟨hs.1, clean_present_avoid_support (hone T hs.1) hs.2 ht.2⟩
  · intro Q
    have hh := hwp.avoid_unwind ha Q
    have hh' := hw.present_unwind hp (fun T => Q T ∧ (T ∩ (C \ E)).card = 0)
    change weightMass (cleanBundleLaw w E C) Q *
      totalMass (avoidWeight (cleanPresent w E C) (C \ E)) = _ at hh
    unfold cleanBundleMass
    calc _ = (weightMass (cleanBundleLaw w E C) Q *
        totalMass (avoidWeight (cleanPresent w E C) (C \ E))) *
          totalMass (presentWeight w (E \ C)) := by ring
      _ = _ := by rw [hh]; exact hh'
  · intro S hSC
    have hh := (present_mean_bounds hw hone' hp S).1
    have hl := hge S hSC
    change _ ≤ expCard (cleanPresent w E C) S at hh
    linarith
  · intro S hSC
    have hh := (present_mean_bounds hw hone' hp S).2
    have hl := hle S hSC
    change expCard (cleanPresent w E C) S ≤ _ at hh
    linarith
  · intro S hSC hSE
    have hh := hw.present_le hone' (disjoint_of_subset_right sdiff_subset hSE) hp
    have hl := hle S hSC
    change expCard (cleanPresent w E C) S ≤ _ at hh
    linarith
  · intro S hSC hES
    have hh := hw.present_ge hone'
      (show Disjoint (S \ (E \ C)) (E \ C) from sdiff_disjoint) hp
    have hs := expCard_sdiff_of_subset w hES
    have hs' := expCard_sdiff_of_subset (cleanPresent w E C) hES
    rw [hself] at hs'
    change _ ≤ expCard (cleanPresent w E C) (S \ (E \ C)) at hh
    have hl := hge S hSC
    linarith
  · intro S hSC hES
    have hh := hw.present_le hone'
      (show Disjoint (S \ (E \ C)) (E \ C) from sdiff_disjoint) hp
    have hs' := expCard_sdiff_of_subset (cleanPresent w E C) hES
    rw [hself] at hs'
    change expCard (cleanPresent w E C) (S \ (E \ C)) ≤ _ at hh
    have heq : S \ (E \ C) = S \ E := by
      ext e
      simp only [mem_sdiff]
      have hn : e ∈ S → e ∉ C := fun he => disjoint_left.mp hSC he
      tauto
    rw [heq] at hh hs'
    have heq' : (S ∪ C) \ E = (S \ E) ∪ (C \ E) := by ext e; simp; tauto
    rw [heq', expCard_union_of_disjoint w
      (disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset hSC))]
    have hl := hle S hSC
    linarith

end TSPGap.Song

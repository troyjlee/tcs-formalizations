/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527Core
import TSPGap.ConcentratedMean

/-!
# Generic helpers for the assembly of Lemma 5.27

Union bounds for `expCard`, `k·P[X = k] ≤ E[X]`, `P[Q] ≤ 1`, the support of
an avoided law, the cross-multiplied "near-certain events stay near-certain"
transfer through an unwinding identity, and two support congruences for
intersections with differences.
-/

namespace TSPGap
open Finset

/-! ### Generic helpers -/

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expCard_union_le {w : Finset ι → ℝ} (hnn : WeightNonneg w) (X Y : Finset ι) :
    expCard w (X ∪ Y) ≤ expCard w X + expCard w Y := by
  have h1 : X ∪ Y = X ∪ (Y \ X) := Finset.union_sdiff_self_eq_union.symm
  have h2 : expCard w (Y \ X) ≤ expCard w Y :=
    expCard_mono hnn (Finset.sdiff_subset (s := Y) (t := X))
  have h3 : Disjoint X (Y \ X) := Finset.disjoint_sdiff
  rw [h1, expCard_union_of_disjoint _ h3]
  linarith

/-- `k · P[X = k] ≤ E[X]`. -/
theorem mul_weightMass_eq_le_expCard {w : Finset ι → ℝ} (hnn : WeightNonneg w) (F : Finset ι)
    (k : ℕ) : (k : ℝ) * weightMass w (fun T => (T ∩ F).card = k) ≤ expCard w F := by
  have h : ∀ T : Finset ι,
      (if (T ∩ F).card = k then (k : ℝ) * w T else 0) ≤ w T * ((T ∩ F).card : ℝ) := by
    intro T
    split_ifs with hk
    · rw [hk, mul_comm]
    · exact mul_nonneg (hnn T) (Nat.cast_nonneg _)
  calc (k : ℝ) * weightMass w (fun T => (T ∩ F).card = k)
      = ∑ T : Finset ι, (if (T ∩ F).card = k then (k : ℝ) * w T else 0) := by
        unfold weightMass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ T : Finset ι, w T * ((T ∩ F).card : ℝ) := Finset.sum_le_sum fun T _ => h T
    _ = expCard w F := rfl

theorem weightMass_le_one {w : Finset ι → ℝ} (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (Q : Finset ι → Prop) : weightMass w Q ≤ 1 := by
  have := weightMass_not_le hnn htot Q
  have := weightMass_nonneg hnn (fun T => ¬ Q T)
  linarith

theorem avoidDist_ne_zero_imp {w : Finset ι → ℝ} {D T : Finset ι} (h : avoidDist w D T ≠ 0) :
    w T ≠ 0 ∧ (T ∩ D).card = 0 := by
  have h1 : avoidWeight w D T ≠ 0 := by
    intro hc; exact h (by rw [avoidDist, hc, zero_div])
  rw [avoidWeight_apply] at h1
  split_ifs at h1 with hc
  · exact ⟨h1, hc⟩
  · exact absurd rfl h1

/-- A near-certain event stays near-certain under a conditioning with
unwinding identity `W_L(P) · M = W_w(P ∧ K)`, cross-multiplied. -/
theorem cond_near_certain {w L : Finset ι → ℝ} (hnn : WeightNonneg w) (hLtot : totalMass L = 1)
    {M : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P : Finset ι → Prop, weightMass L P * M = weightMass w (fun T => P T ∧ K T))
    (Q : Finset ι → Prop) :
    (1 - weightMass L Q) * M ≤ weightMass w (fun T => ¬ Q T) := by
  have h1 := hunwind Q
  have h0 := hunwind (fun _ => True)
  rw [weightMass_true, hLtot, one_mul] at h0
  have hK : weightMass w (fun T => True ∧ K T) = weightMass w K :=
    weightMass_congr fun T => by simp
  rw [hK] at h0
  have h2 := weightMass_and_ge_sub hnn K Q
  have h3 : weightMass w (fun T => K T ∧ Q T) = weightMass w (fun T => Q T ∧ K T) :=
    weightMass_congr fun T => and_comm
  nlinarith

theorem inter_sdiff_union_eq_of_card_inter_zero {T A X Y : Finset ι}
    (h : (T ∩ Y).card = 0) : T ∩ (A \ (X ∪ Y)) = T ∩ (A \ X) := by
  rw [Finset.card_eq_zero] at h
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, not_or]
  constructor
  · rintro ⟨hT, hA, hX, -⟩; exact ⟨hT, hA, hX⟩
  · rintro ⟨hT, hA, hX⟩
    refine ⟨hT, hA, hX, fun hY => ?_⟩
    have : e ∈ T ∩ Y := Finset.mem_inter.mpr ⟨hT, hY⟩
    simp [h] at this

theorem inter_sdiff_eq_of_card_inter_inter_zero {T A E : Finset ι}
    (h : (T ∩ (E ∩ A)).card = 0) : T ∩ (A \ E) = T ∩ A := by
  rw [Finset.card_eq_zero] at h
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hT, hA, -⟩; exact ⟨hT, hA⟩
  · rintro ⟨hT, hA⟩
    refine ⟨hT, hA, fun hE => ?_⟩
    have : e ∈ T ∩ (E ∩ A) := Finset.mem_inter.mpr ⟨hT, Finset.mem_inter.mpr ⟨hE, hA⟩⟩
    simp [h] at this

theorem inter_sdiff_union_eq_of_card_inter_inter_zero {T A X Y : Finset ι}
    (h : (T ∩ (Y ∩ A)).card = 0) : T ∩ (A \ (X ∪ Y)) = T ∩ (A \ X) := by
  rw [Finset.card_eq_zero] at h
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, not_or]
  constructor
  · rintro ⟨hT, hA, hX, -⟩; exact ⟨hT, hA, hX⟩
  · rintro ⟨hT, hA, hX⟩
    refine ⟨hT, hA, hX, fun hY => ?_⟩
    have : e ∈ T ∩ (Y ∩ A) := Finset.mem_inter.mpr ⟨hT, Finset.mem_inter.mpr ⟨hY, hA⟩⟩
    simp [h] at this

end Generic

end TSPGap

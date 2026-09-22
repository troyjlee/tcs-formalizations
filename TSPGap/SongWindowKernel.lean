/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeCell
import TSPGap.SongArithmetic

/-!
# The two-stage splitting kernel of Song's Lemma 18

The existing refined three-cell inequality already gives both factors
`0.1206` and `0.998`; the paper's extra mode argument is not needed.
The rank-three law is a normalized projected layer, not an assumed stable
restriction. The tail inputs below still have to be supplied by the
endpoint-tree / C-avoidance / bundle-present conditioning construction at
`r = h/4`. This file does not assert that the old Lemma A.1 supplies them.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The smaller of the two second-stage tail products. -/
noncomputable def windowSplit : ℝ := 0.1469 * 0.63 * (K - 0.51) * h

/-- Both three-cell estimates clear the factors used in the final product. -/
theorem window_split_bounds :
    0 < windowSplit ∧ 3 * windowSplit ≤ 1 ∧ 0 < 1 - 2 * windowSplit ∧
    windowSplit ≤ 0.0585 * 0.1469 ∧
    0.998 * windowSplit * (1 - 2 * windowSplit) ≤
      windowSplit * (1 - 3 * windowSplit) ∧
    (0.1206 : ℝ) * (1 - 2 * 0.15687) ≤ 0.15687 * (1 - 3 * 0.15687) := by
  norm_num [windowSplit, K, h]

/-- The exact probability inputs on the conditioned window law. Every
layer inequality is cross-multiplied by the rank-three mass. -/
structure WindowTails (ν : Finset ι → ℝ) (A B V : Finset ι) : Prop where
  rank_three : 0.398 * h ≤ weightMass ν
    (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
  x_ge : 0.63 ≤ weightMass ν (fun T => 2 ≤ (T ∩ (A ∪ B)).card)
  x_le : 0.249 ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card ≤ 2)
  v_ge : 0.63 ≤ weightMass ν (fun T => 1 ≤ (T ∩ V).card)
  v_le : 0.249 ≤ weightMass ν (fun T => (T ∩ V).card ≤ 1)
  a_ge : 0.0585 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) ≤
    weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ A).card)
  a_le : 0.1469 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) ≤
    weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ A).card ≤ 1)
  b_ge : 0.63 * (K - 0.51) * h *
      weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) ≤
    weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ B).card)
  b_le : 0.1469 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3) ≤
    weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ B).card ≤ 1)

/-- The conditioned three-count event, before the restriction mass is paid. -/
theorem window_kernel {ν : Finset ι → ℝ} {rank : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight rank ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card)
    (H : WindowTails ν A B V) :
    (0.398 * h) * (0.1206 * (0.998 * windowSplit)) ≤ weightMass ν
      (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
  classical
  have hXV : Disjoint (A ∪ B) V := disjoint_union_left.mpr ⟨hAV, hBV⟩
  let F := (A ∪ B) ∪ V
  let m := weightMass ν (fun T => (T ∩ F).card = 3)
  have hm : 0.398 * h ≤ m := H.rank_three
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num [h]) hm
  have hmnn := hmpos.le
  have hlow1 : (0.15687 : ℝ) ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card ≤ 2) *
      weightMass ν (fun T => 1 ≤ (T ∩ V).card) :=
    (by norm_num : (0.15687 : ℝ) ≤ 0.249 * 0.63).trans
      (mul_le_mul H.x_le H.v_ge (by norm_num) (weightMass_nonneg hnn _))
  have hhigh1 : (0.15687 : ℝ) ≤ weightMass ν (fun T => 2 ≤ (T ∩ (A ∪ B)).card) *
      weightMass ν (fun T => (T ∩ V).card ≤ 1) :=
    (by norm_num : (0.15687 : ℝ) ≤ 0.63 * 0.249).trans
      (mul_le_mul H.x_ge H.v_le (by norm_num) (weightMass_nonneg hnn _))
  have hstage1 := three_cell_bound_shifted hst hr hnn htot hXV 1 0 hbase
    (fun _ _ => Nat.zero_le _) (ε := 0.15687) (by norm_num) (by norm_num) hlow1 hhigh1
  change m * 0.15687 * (1 - 3 * 0.15687) ≤ weightMass ν
    (fun T => (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) * (1 - 2 * 0.15687)
    at hstage1
  have hmid1 : 0.1206 * m ≤ weightMass ν
      (fun T => (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) := by
    nlinarith only [hstage1, hmnn]
  have hmid_as_layer : weightMass ν
      (fun T => (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) =
      weightMass ν (fun T => (T ∩ F).card = 3 ∧ (T ∩ (A ∪ B)).card = 2) := by
    apply weightMass_congr
    intro T
    dsimp [F]
    rw [card_inter_union_of_disjoint hXV]
    omega
  rw [hmid_as_layer] at hmid1
  -- Stability of the positive projected layer supplies the second law.
  have hLmass : totalMass (projLayer ν F 3) = m := totalMass_projLayer ν F 3
  have hLpos : 0 < totalMass (projLayer ν F 3) := by rw [hLmass]; exact hmpos
  obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ := exists_layer_interval hst hr hnn htot F
  have hthree := (hiff 3).mp hLpos
  have hLst := isRealStable_projLayer_interval hst hr hnn hab hbr hiff hsupp 3
    hthree.1 hthree.2
  let ρ : Finset ι → ℝ := fun U => m⁻¹ * projLayer ν F 3 U
  have hρnn : WeightNonneg ρ := fun U =>
    mul_nonneg (inv_nonneg.mpr hmnn) (weightNonneg_projLayer hnn F 3 U)
  have hρrank : FixedRankWeight 3 ρ := by
    intro U hU
    exact fixedRankWeight_projLayer ν F 3 U fun hz => hU (by
      change m⁻¹ * projLayer ν F 3 U = 0
      rw [hz, mul_zero])
  have hρtot : totalMass ρ = 1 := by
    change totalMass (fun U => m⁻¹ * projLayer ν F 3 U) = 1
    rw [totalMass, ← mul_sum]
    change m⁻¹ * totalMass (projLayer ν F 3) = 1
    rw [hLmass, inv_mul_cancel₀ hmpos.ne']
  have hρst : IsRealStable (genPoly ρ) := by
    change IsRealStable (genPoly (fun U => m⁻¹ * projLayer ν F 3 U))
    rw [← const_mul_genPoly]
    exact IsRealStable.const_mul (inv_ne_zero hmpos.ne') hLst
  have hAF : A ⊆ F := fun i hi => mem_union_left V (mem_union_left B hi)
  have hBF : B ⊆ F := fun i hi => mem_union_left V (mem_union_right A hi)
  have hρmass (Q : Finset ι → Prop) (hQ : EventDependsOn Q F) :
      weightMass ρ Q = m⁻¹ * weightMass ν (fun T => (T ∩ F).card = 3 ∧ Q T) := by
    have hscale : weightMass ρ Q = m⁻¹ * weightMass (projLayer ν F 3) Q := by
      simp only [ρ, weightMass, mul_sum, mul_ite, mul_zero]
    rw [hscale, weightMass_projLayer_of_dependsOn ν 3 hQ]
  have hnorm (c raw : ℝ) (hc : c * m ≤ raw) : c ≤ m⁻¹ * raw := by
    calc c = m⁻¹ * (c * m) := by
           rw [mul_comm c m, ← mul_assoc, inv_mul_cancel₀ hmpos.ne', one_mul]
         _ ≤ m⁻¹ * raw := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hmnn)
  have hAge : 0.0585 ≤ weightMass ρ (fun T => 1 ≤ (T ∩ A).card) := by
    rw [hρmass _ ((eventDependsOn_le_card A 1).mono hAF)]
    exact hnorm _ _ H.a_ge
  have hAle : 0.1469 ≤ weightMass ρ (fun T => (T ∩ A).card ≤ 1) := by
    rw [hρmass _ ((eventDependsOn_card_le A 1).mono hAF)]
    exact hnorm _ _ H.a_le
  have hBge : 0.63 * (K - 0.51) * h ≤ weightMass ρ (fun T => 1 ≤ (T ∩ B).card) := by
    rw [hρmass _ ((eventDependsOn_le_card B 1).mono hBF)]
    exact hnorm _ _ H.b_ge
  have hBle : 0.1469 ≤ weightMass ρ (fun T => (T ∩ B).card ≤ 1) := by
    rw [hρmass _ ((eventDependsOn_card_le B 1).mono hBF)]
    exact hnorm _ _ H.b_le
  have hXeq : 0.1206 ≤ weightMass ρ (fun T => (T ∩ (A ∪ B)).card = 2) := by
    rw [hρmass _ ((eventDependsOn_card_eq (A ∪ B) 2).mono subset_union_left)]
    exact hnorm _ _ hmid1
  have hlow2 : windowSplit ≤ weightMass ρ (fun T => (T ∩ A).card ≤ 1) *
      weightMass ρ (fun T => 1 ≤ (T ∩ B).card) := by
    calc windowSplit = 0.1469 * (0.63 * (K - 0.51) * h) := by unfold windowSplit; ring
         _ ≤ _ := mul_le_mul hAle hBge (by norm_num [K, h]) (weightMass_nonneg hρnn _)
  have hhigh2 : windowSplit ≤ weightMass ρ (fun T => 1 ≤ (T ∩ A).card) *
      weightMass ρ (fun T => (T ∩ B).card ≤ 1) :=
    window_split_bounds.2.2.2.1.trans
      (mul_le_mul hAge hBle (by norm_num) (weightMass_nonneg hρnn _))
  have hs := three_cell_bound hρst hρrank hρnn hρtot hAB window_split_bounds.1.le
    window_split_bounds.2.1 hlow2 hhigh2
  let mid := weightMass ρ (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1)
  have hxnn := weightMass_nonneg hρnn (fun T => (T ∩ (A ∪ B)).card = 2)
  have hc0 : 0 ≤ 0.998 * windowSplit := mul_nonneg (by norm_num) window_split_bounds.1.le
  have hdpos := window_split_bounds.2.2.1
  have hscaled : (0.1206 * (0.998 * windowSplit)) * (1 - 2 * windowSplit) ≤
      mid * (1 - 2 * windowSplit) := by
    calc
      _ = 0.1206 * (0.998 * windowSplit * (1 - 2 * windowSplit)) := by ring
      _ ≤ weightMass ρ (fun T => (T ∩ (A ∪ B)).card = 2) *
          (0.998 * windowSplit * (1 - 2 * windowSplit)) :=
        mul_le_mul_of_nonneg_right hXeq (mul_nonneg hc0 hdpos.le)
      _ ≤ weightMass ρ (fun T => (T ∩ (A ∪ B)).card = 2) *
          (windowSplit * (1 - 3 * windowSplit)) :=
        mul_le_mul_of_nonneg_left window_split_bounds.2.2.2.2.1 hxnn
      _ ≤ _ := by simpa only [mul_assoc] using hs
  have hmid := le_of_mul_le_mul_right hscaled hdpos
  have hdep : EventDependsOn (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) F := by
    intro S T hST
    exact and_congr ((eventDependsOn_card_eq A 1).mono hAF S T hST)
      ((eventDependsOn_card_eq B 1).mono hBF S T hST)
  have hraw : m * (0.1206 * (0.998 * windowSplit)) ≤ weightMass ν
      (fun T => (T ∩ F).card = 3 ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) := by
    calc _ ≤ m * mid := mul_le_mul_of_nonneg_left hmid hmnn
         _ = _ := by
           dsimp [mid]
           rw [hρmass _ hdep, ← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul]
  have hfinal : weightMass ν
      (fun T => (T ∩ F).card = 3 ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) =
      weightMass ν
        (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
    apply weightMass_congr
    intro T
    dsimp [F]
    rw [card_inter_union_of_disjoint hXV, card_inter_union_of_disjoint hAB]
    omega
  rw [hfinal] at hraw
  exact (mul_le_mul_of_nonneg_right hm (mul_nonneg (by norm_num) hc0)).trans hraw

/-- Pay the actual restriction mass, then identify the three-count event
inside the original happy event. No stability is asserted for an event restriction. -/
theorem window_mass_gt {μ ν : Finset ι → ℝ} (hμ : WeightNonneg μ) {rank : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight rank ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card)
    (H : WindowTails ν A B V) {M : ℝ} (hM : 0.49 ≤ M)
    {C Q : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ C T))
    (hhappy : ∀ T, μ T ≠ 0 →
      ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) ∧ C T → Q T) :
    p < weightMass μ Q := by
  have hk := window_kernel hst hr hnn htot hAB hAV hBV hbase H
  have hm := mul_le_mul hk hM (by norm_num) (weightMass_nonneg hnn _)
  rw [hunwind] at hm
  have hi : weightMass μ (fun T =>
      ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) ∧ C T) ≤
      weightMass μ Q := by
    classical
    unfold weightMass
    apply sum_le_sum
    intro T _
    by_cases hz : μ T = 0
    · simp [hz]
    by_cases he : ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) ∧ C T
    · simp [he, hhappy T hz he]
    · simp only [if_neg he]
      split_ifs <;> first | exact hμ T | exact le_rfl
  have hp : p < ((0.398 * h) * (0.1206 * (0.998 * windowSplit))) * 0.49 := by
    norm_num [windowSplit, K, h, p]
  exact hp.trans_le (hm.trans hi)

end TSPGap.Song

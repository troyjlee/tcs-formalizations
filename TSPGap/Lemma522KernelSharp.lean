/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Kernel

/-! # Lemma 5.22 with the recovered probability inputs

The two-stage argument uses layer mass ε, layer tails 0.577ε and 0.147,
and the existing first-stage factor 0.12. The old kernel remains available
on its larger parameter range; this export uses ε ≤ 0.0002.
-/
namespace TSPGap
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem eventDependsOn_and_recovered {P Q : Finset ι → Prop} {F : Finset ι}
    (hP : EventDependsOn P F) (hQ : EventDependsOn Q F) :
    EventDependsOn (fun T => P T ∧ Q T) F := by
  intro S T hST
  exact and_congr (hP S T hST) (hQ S T hST)

set_option maxHeartbeats 1600000 in
-- Two projected-layer normalizations and the two three-cell estimates elaborate together.
/-- **The kernel of Lemma 5.22.** -/
theorem lemma_5_22_kernel_sharp {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) {ε : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.0002)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card)
    (hm : ε ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3))
    (hXge : 0.63 ≤ weightMass ν (fun T => 2 ≤ (T ∩ (A ∪ B)).card))
    (hXle : 0.249 ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card ≤ 2))
    (hVge : 0.63 ≤ weightMass ν (fun T => 1 ≤ (T ∩ V).card))
    (hVle : 0.249 ≤ weightMass ν (fun T => (T ∩ V).card ≤ 1))
    (hAge : 0.577 * ε * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ A).card))
    (hAle : 0.147 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ A).card ≤ 1))
    (hBge : 0.577 * ε * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ B).card))
    (hBle : 0.147 * weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ B).card ≤ 1)) :
    0.0101 * ε ^ 2 ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
  classical
  have hXV : Disjoint (A ∪ B) V := Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩
  by_cases hε : ε = 0
  · subst ε
    norm_num
    exact weightMass_nonneg hnn _
  have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε)
  let F : Finset ι := (A ∪ B) ∪ V
  let m : ℝ := weightMass ν (fun T => (T ∩ F).card = 3)
  change ε ≤ m at hm
  change 0.577 * ε * m ≤ weightMass ν (fun T => (T ∩ F).card = 3 ∧ 1 ≤ (T ∩ A).card) at hAge
  change 0.147 * m ≤ weightMass ν (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card ≤ 1) at hAle
  change 0.577 * ε * m ≤ weightMass ν (fun T => (T ∩ F).card = 3 ∧ 1 ≤ (T ∩ B).card) at hBge
  change 0.147 * m ≤ weightMass ν (fun T => (T ∩ F).card = 3 ∧ (T ∩ B).card ≤ 1) at hBle
  have hmpos : 0 < m := lt_of_lt_of_le hεpos hm
  have hmne : m ≠ 0 := ne_of_gt hmpos
  /- The first Corollary 5.5 call, on `(A ∪ B, V)`. -/
  have hlow1 : (0.156 : ℝ) ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card ≤ 2)
      * weightMass ν (fun T => 1 ≤ (T ∩ V).card) :=
    le_trans (by norm_num) (mul_le_mul hXle hVge (by norm_num) (weightMass_nonneg hnn _))
  have hhigh1 : (0.156 : ℝ) ≤ weightMass ν (fun T => 2 ≤ (T ∩ (A ∪ B)).card)
      * weightMass ν (fun T => (T ∩ V).card ≤ 1) :=
    le_trans (by norm_num) (mul_le_mul hXge hVle (by norm_num) (weightMass_nonneg hnn _))
  have hstage1 := three_cell_bound_shifted hst hr hnn htot hXV 1 0 hbase
    (fun _ _ => Nat.zero_le _) (ε := 0.156) (by norm_num) (by norm_num) hlow1 hhigh1
  change m * 0.156 * (1 - 3 * 0.156) ≤
    weightMass ν (fun T => (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) * (1 - 2 * 0.156)
    at hstage1
  have hmid1 : 0.12 * m ≤ weightMass ν (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) := by
    have hmidnn := weightMass_nonneg hnn (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1)
    nlinarith [hstage1]
  have hmid_as_layer : weightMass ν (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) =
      weightMass ν (fun T => (T ∩ F).card = 3 ∧ (T ∩ (A ∪ B)).card = 2) := by
    apply weightMass_congr
    intro T
    change ((T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) ↔
      ((T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ (A ∪ B)).card = 2)
    rw [card_inter_union_of_disjoint hXV T]
    omega
  rw [hmid_as_layer] at hmid1
  /- Normalize the positive projected layer. -/
  have hLnn : WeightNonneg (projLayer ν F 3) := weightNonneg_projLayer hnn F 3
  have hLmass : totalMass (projLayer ν F 3) = m := by rw [totalMass_projLayer]
  have hLpos : 0 < totalMass (projLayer ν F 3) := by rw [hLmass]; exact hmpos
  obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ := exists_layer_interval hst hr hnn htot F
  have hlayer := (hiff 3).mp hLpos
  have hLst : IsRealStable (genPoly (projLayer ν F 3)) :=
    isRealStable_projLayer_interval hst hr hnn hab hbr hiff hsupp 3 hlayer.1 hlayer.2
  let ρ : Finset ι → ℝ := fun U => m⁻¹ * projLayer ν F 3 U
  have hρnn : WeightNonneg ρ := fun U => mul_nonneg (inv_nonneg.mpr hmpos.le) (hLnn U)
  have hρrank : FixedRankWeight 3 ρ := by
    intro U hU
    exact fixedRankWeight_projLayer ν F 3 U fun hzero => hU (by
      change m⁻¹ * projLayer ν F 3 U = 0
      rw [hzero, mul_zero])
  have hρtot : totalMass ρ = 1 := by
    change totalMass (fun U => m⁻¹ * projLayer ν F 3 U) = 1
    rw [totalMass_smul, hLmass, inv_mul_cancel₀ hmne]
  have hρst : IsRealStable (genPoly ρ) := by
    change IsRealStable (genPoly (fun U => m⁻¹ * projLayer ν F 3 U))
    rw [← const_mul_genPoly]
    exact IsRealStable.const_mul (inv_ne_zero hmne) hLst
  have hAF : A ⊆ F := fun i hi => Finset.mem_union_left V (Finset.mem_union_left B hi)
  have hBF : B ⊆ F := fun i hi => Finset.mem_union_left V (Finset.mem_union_right A hi)
  have hXF : A ∪ B ⊆ F := Finset.subset_union_left
  have hρmass (Q : Finset ι → Prop) (hQ : EventDependsOn Q F) :
      weightMass ρ Q = m⁻¹ * weightMass ν (fun T => (T ∩ F).card = 3 ∧ Q T) := by
    change weightMass (fun U => m⁻¹ * projLayer ν F 3 U) Q = _
    rw [weightMass_smul, weightMass_projLayer_of_dependsOn ν 3 hQ]
  have hnormalize_lower (c raw : ℝ) (h : c * m ≤ raw) : c ≤ m⁻¹ * raw := by
    calc c = m⁻¹ * (c * m) := by rw [mul_comm c m, ← mul_assoc, inv_mul_cancel₀ hmne, one_mul]
      _ ≤ m⁻¹ * raw := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hmpos.le)
  have hAgeρ : 0.577 * ε ≤ weightMass ρ (fun T => 1 ≤ (T ∩ A).card) := by
    rw [hρmass _ ((eventDependsOn_le_card A 1).mono hAF)]
    exact hnormalize_lower _ _ hAge
  have hAleρ : 0.147 ≤ weightMass ρ (fun T => (T ∩ A).card ≤ 1) := by
    rw [hρmass _ ((eventDependsOn_card_le A 1).mono hAF)]
    exact hnormalize_lower _ _ hAle
  have hBgeρ : 0.577 * ε ≤ weightMass ρ (fun T => 1 ≤ (T ∩ B).card) := by
    rw [hρmass _ ((eventDependsOn_le_card B 1).mono hBF)]
    exact hnormalize_lower _ _ hBge
  have hBleρ : 0.147 ≤ weightMass ρ (fun T => (T ∩ B).card ≤ 1) := by
    rw [hρmass _ ((eventDependsOn_card_le B 1).mono hBF)]
    exact hnormalize_lower _ _ hBle
  have hXeqρ : 0.12 ≤ weightMass ρ (fun T => (T ∩ (A ∪ B)).card = 2) := by
    rw [hρmass _ ((eventDependsOn_card_eq (A ∪ B) 2).mono hXF)]
    exact hnormalize_lower _ _ hmid1
  /- The second Corollary 5.5 call, on the normalized layer. -/
  have hlow2 : 0.084819 * ε ≤ weightMass ρ (fun T => (T ∩ A).card ≤ 1)
      * weightMass ρ (fun T => 1 ≤ (T ∩ B).card) := by
    calc 0.084819 * ε ≤ 0.147 * (0.577 * ε) := by nlinarith
      _ ≤ _ := mul_le_mul hAleρ hBgeρ (by positivity) (weightMass_nonneg hρnn _)
  have hhigh2 : 0.084819 * ε ≤ weightMass ρ (fun T => 1 ≤ (T ∩ A).card)
      * weightMass ρ (fun T => (T ∩ B).card ≤ 1) := by
    calc 0.084819 * ε ≤ 0.577 * ε * (0.147) := by nlinarith
      _ ≤ _ := mul_le_mul hAgeρ hBleρ (by positivity) (weightMass_nonneg hρnn _)
  have hstage2 := three_cell_bound hρst hρrank hρnn hρtot hAB
    (ε := 0.084819 * ε) (by positivity) (by nlinarith) hlow2 hhigh2
  let xmass : ℝ := weightMass ρ (fun T => (T ∩ (A ∪ B)).card = 2)
  let mid : ℝ := weightMass ρ (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1)
  change xmass * (0.084819 * ε) * (1 - 3 * (0.084819 * ε)) ≤
    mid * (1 - 2 * (0.084819 * ε)) at hstage2
  change 0.12 ≤ xmass at hXeqρ
  have hxnn : 0 ≤ xmass := weightMass_nonneg hρnn _
  have hmidnn : 0 ≤ mid := weightMass_nonneg hρnn _
  let c : ℝ := 0.0842 * ε
  let d : ℝ := 1 - 2 * (0.084819 * ε)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hdpos : 0 < d := by dsimp [d]; nlinarith
  have hcoef : c * d ≤ (0.084819 * ε) * (1 - 3 * (0.084819 * ε)) := by
    dsimp [c, d]
    nlinarith
  have hscaled : (0.12 * c) * d ≤ mid * d := by
    calc (0.12 * c) * d = 0.12 * (c * d) := by ring
      _ ≤ xmass * (c * d) := mul_le_mul_of_nonneg_right hXeqρ (mul_nonneg hc0 hdpos.le)
      _ ≤ xmass * ((0.084819 * ε) * (1 - 3 * (0.084819 * ε))) :=
        mul_le_mul_of_nonneg_left hcoef hxnn
      _ = xmass * (0.084819 * ε) * (1 - 3 * (0.084819 * ε)) := by ring
      _ ≤ mid * d := by simpa [d] using hstage2
  have hmidρ : 0.0101 * ε ≤ mid := by
    have hcancel : 0.12 * c ≤ mid := le_of_mul_le_mul_right hscaled hdpos
    calc 0.0101 * ε ≤ 0.12 * c := by dsimp [c]; linarith
      _ ≤ mid := hcancel
  have hABdep : EventDependsOn (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) F :=
    eventDependsOn_and_recovered ((eventDependsOn_card_eq A 1).mono hAF)
      ((eventDependsOn_card_eq B 1).mono hBF)
  have hmid_bridge : mid = m⁻¹ * weightMass ν (fun T =>
      (T ∩ F).card = 3 ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) := by
    dsimp [mid]
    exact hρmass _ hABdep
  have hraw_mid : m * (0.0101 * ε) ≤ weightMass ν (fun T =>
      (T ∩ F).card = 3 ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) := by
    calc m * (0.0101 * ε) ≤ m * mid := mul_le_mul_of_nonneg_left hmidρ hmpos.le
      _ = _ := by rw [hmid_bridge, ← mul_assoc, mul_inv_cancel₀ hmne, one_mul]
  have hfinal_bridge : weightMass ν (fun T =>
      (T ∩ F).card = 3 ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) =
      weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
    apply weightMass_congr
    intro T
    change ((T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) ↔
      ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1)
    rw [card_inter_union_of_disjoint hXV T, card_inter_union_of_disjoint hAB T]
    omega
  rw [hfinal_bridge] at hraw_mid
  calc 0.0101 * ε ^ 2 ≤ (ε) * (0.0101 * ε) := by nlinarith
    _ ≤ m * (0.0101 * ε) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ ≤ _ := hraw_mid

end TSPGap

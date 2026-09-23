/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1

/-!
# KKO21 Lemma A.1: the conditioned analytic kernel

This file isolates the two applications of KKO21 Corollary 5.5 used in
Lemma A.1.  The first application is made to the two cells `A ∪ B` and
`V`.  The second is made to `A` and `B` after projecting to, and
normalizing, the three-element layer of `(A ∪ B) ∪ V`.

All hypotheses on the normalized layer are stated without division: a
conditional lower bound `c` is supplied as `c * m3 ≤ ...`, where `m3` is
the mass of the three-element layer.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem eventDependsOn_and {P Q : Finset ι → Prop} {F : Finset ι}
    (hP : EventDependsOn P F) (hQ : EventDependsOn Q F) :
    EventDependsOn (fun T => P T ∧ Q T) F := by
  intro S T hST
  exact and_congr (hP S T hST) (hQ S T hST)

/-- **The conditioned analytic kernel in KKO21 Lemma A.1.**

The baseline on `A ∪ B` is the support fact needed by the shifted first
three-cell call.  In the graph-theoretic application it says that the
present bundle contributes at least one edge.  No baseline is needed for
the second call.

The `0.058` layer-three tail is enough in the second orientation:
`0.058 * 0.147 = 0.008526 ≥ 0.44 ε` for `ε ≤ 0.001`.
-/
theorem lemma_A1_conditioned_kernel {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) {ε : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card)
    (hm3 : 0.2 * ε ≤ weightMass ν
      (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3))
    (hXge : 0.63 ≤ weightMass ν
      (fun T => 2 ≤ (T ∩ (A ∪ B)).card))
    (hXle : 0.249 ≤ weightMass ν
      (fun T => (T ∩ (A ∪ B)).card ≤ 2))
    (hVge : 0.63 ≤ weightMass ν
      (fun T => 1 ≤ (T ∩ V).card))
    (hVle : 0.249 ≤ weightMass ν
      (fun T => (T ∩ V).card ≤ 1))
    (hAge : 0.058 * weightMass ν
        (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ A).card))
    (hAle : 0.147 * weightMass ν
        (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ A).card ≤ 1))
    (hBge : 3.02 * ε * weightMass ν
        (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ 1 ≤ (T ∩ B).card))
    (hBle : 0.147 * weightMass ν
        (fun T => (T ∩ ((A ∪ B) ∪ V)).card = 3)
      ≤ weightMass ν (fun T =>
        (T ∩ ((A ∪ B) ∪ V)).card = 3 ∧ (T ∩ B).card ≤ 1)) :
    0.01008 * ε ^ 2 ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
  classical
  have hXV : Disjoint (A ∪ B) V :=
    Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩
  by_cases hε : ε = 0
  · subst ε
    norm_num
    exact weightMass_nonneg hnn _
  have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε)
  let F : Finset ι := (A ∪ B) ∪ V
  let m3 : ℝ := weightMass ν (fun T => (T ∩ F).card = 3)
  change 0.2 * ε ≤ m3 at hm3
  change 0.058 * m3 ≤ weightMass ν
    (fun T => (T ∩ F).card = 3 ∧ 1 ≤ (T ∩ A).card) at hAge
  change 0.147 * m3 ≤ weightMass ν
    (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card ≤ 1) at hAle
  change 3.02 * ε * m3 ≤ weightMass ν
    (fun T => (T ∩ F).card = 3 ∧ 1 ≤ (T ∩ B).card) at hBge
  change 0.147 * m3 ≤ weightMass ν
    (fun T => (T ∩ F).card = 3 ∧ (T ∩ B).card ≤ 1) at hBle
  have hm3pos : 0 < m3 := lt_of_lt_of_le (mul_pos (by norm_num) hεpos) hm3
  have hm3ne : m3 ≠ 0 := ne_of_gt hm3pos
  /- The first Corollary 5.5 call, on `(A ∪ B, V)`. -/
  have hlow1 : (0.156 : ℝ) ≤
      weightMass ν (fun T => (T ∩ (A ∪ B)).card ≤ 2)
        * weightMass ν (fun T => 1 ≤ (T ∩ V).card) :=
    le_trans (by norm_num)
      (mul_le_mul hXle hVge (by norm_num) (weightMass_nonneg hnn _))
  have hhigh1 : (0.156 : ℝ) ≤
      weightMass ν (fun T => 2 ≤ (T ∩ (A ∪ B)).card)
        * weightMass ν (fun T => (T ∩ V).card ≤ 1) :=
    le_trans (by norm_num)
      (mul_le_mul hXge hVle (by norm_num) (weightMass_nonneg hnn _))
  have hstage1 := three_cell_bound_shifted hst hr hnn htot hXV 1 0 hbase
    (fun _ _ => Nat.zero_le _) (ε := 0.156) (by norm_num) (by norm_num)
    hlow1 hhigh1
  change m3 * 0.156 * (1 - 3 * 0.156) ≤
    weightMass ν (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) *
        (1 - 2 * 0.156) at hstage1
  have hmid1 : 0.12 * m3 ≤ weightMass ν (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) := by
    have hmidnn := weightMass_nonneg hnn (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1)
    nlinarith [hstage1]
  have hmid_as_layer : weightMass ν (fun T =>
      (T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) =
      weightMass ν (fun T =>
        (T ∩ F).card = 3 ∧ (T ∩ (A ∪ B)).card = 2) := by
    apply weightMass_congr
    intro T
    change ((T ∩ (A ∪ B)).card = 2 ∧ (T ∩ V).card = 1) ↔
      ((T ∩ ((A ∪ B) ∪ V)).card = 3 ∧
        (T ∩ (A ∪ B)).card = 2)
    rw [card_inter_union_of_disjoint hXV T]
    omega
  rw [hmid_as_layer] at hmid1
  /- Normalize the positive projected three-element layer. -/
  have hLnn : WeightNonneg (projLayer ν F 3) :=
    weightNonneg_projLayer hnn F 3
  have hLmass : totalMass (projLayer ν F 3) = m3 := by
    rw [totalMass_projLayer]
  have hLpos : 0 < totalMass (projLayer ν F 3) := by rw [hLmass]; exact hm3pos
  obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ :=
    exists_layer_interval hst hr hnn htot F
  have hthree := (hiff 3).mp hLpos
  have hLst : IsRealStable (genPoly (projLayer ν F 3)) :=
    isRealStable_projLayer_interval hst hr hnn hab hbr hiff hsupp 3
      hthree.1 hthree.2
  let ρ : Finset ι → ℝ := fun U => m3⁻¹ * projLayer ν F 3 U
  have hρnn : WeightNonneg ρ := by
    intro U
    exact mul_nonneg (inv_nonneg.mpr hm3pos.le) (hLnn U)
  have hρrank : FixedRankWeight 3 ρ := by
    intro U hU
    exact fixedRankWeight_projLayer ν F 3 U fun hzero => hU (by
      change m3⁻¹ * projLayer ν F 3 U = 0
      rw [hzero, mul_zero])
  have hρtot : totalMass ρ = 1 := by
    change totalMass (fun U => m3⁻¹ * projLayer ν F 3 U) = 1
    rw [totalMass_smul, hLmass, inv_mul_cancel₀ hm3ne]
  have hρst : IsRealStable (genPoly ρ) := by
    change IsRealStable
      (genPoly (fun U => m3⁻¹ * projLayer ν F 3 U))
    rw [← const_mul_genPoly]
    exact IsRealStable.const_mul (inv_ne_zero hm3ne) hLst
  have hAF : A ⊆ F := by
    intro i hi
    exact Finset.mem_union_left V (Finset.mem_union_left B hi)
  have hBF : B ⊆ F := by
    intro i hi
    exact Finset.mem_union_left V (Finset.mem_union_right A hi)
  have hXF : A ∪ B ⊆ F := Finset.subset_union_left
  have hρmass (Q : Finset ι → Prop) (hQ : EventDependsOn Q F) :
      weightMass ρ Q = m3⁻¹ * weightMass ν
        (fun T => (T ∩ F).card = 3 ∧ Q T) := by
    change weightMass (fun U => m3⁻¹ * projLayer ν F 3 U) Q = _
    rw [weightMass_smul, weightMass_projLayer_of_dependsOn ν 3 hQ]
  have hnormalize_lower (c raw : ℝ) (h : c * m3 ≤ raw) :
      c ≤ m3⁻¹ * raw := by
    calc
      c = m3⁻¹ * (c * m3) := by
        rw [mul_comm c m3, ← mul_assoc, inv_mul_cancel₀ hm3ne, one_mul]
      _ ≤ m3⁻¹ * raw :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hm3pos.le)
  have hAgeρ : 0.058 ≤ weightMass ρ (fun T => 1 ≤ (T ∩ A).card) := by
    rw [hρmass _ ((eventDependsOn_le_card A 1).mono hAF)]
    exact hnormalize_lower _ _ hAge
  have hAleρ : 0.147 ≤ weightMass ρ (fun T => (T ∩ A).card ≤ 1) := by
    rw [hρmass _ ((eventDependsOn_card_le A 1).mono hAF)]
    exact hnormalize_lower _ _ hAle
  have hBgeρ : 3.02 * ε ≤ weightMass ρ (fun T => 1 ≤ (T ∩ B).card) := by
    rw [hρmass _ ((eventDependsOn_le_card B 1).mono hBF)]
    exact hnormalize_lower _ _ hBge
  have hBleρ : 0.147 ≤ weightMass ρ (fun T => (T ∩ B).card ≤ 1) := by
    rw [hρmass _ ((eventDependsOn_card_le B 1).mono hBF)]
    exact hnormalize_lower _ _ hBle
  have hXeqρ : 0.12 ≤ weightMass ρ
      (fun T => (T ∩ (A ∪ B)).card = 2) := by
    rw [hρmass _ ((eventDependsOn_card_eq (A ∪ B) 2).mono hXF)]
    exact hnormalize_lower _ _ hmid1
  /- The second Corollary 5.5 call, on the normalized layer. -/
  have hlow2 : 0.44 * ε ≤
      weightMass ρ (fun T => (T ∩ A).card ≤ 1)
        * weightMass ρ (fun T => 1 ≤ (T ∩ B).card) := by
    calc
      0.44 * ε ≤ 0.147 * (3.02 * ε) := by nlinarith
      _ ≤ _ := mul_le_mul hAleρ hBgeρ (by positivity)
        (weightMass_nonneg hρnn _)
  have hhigh2 : 0.44 * ε ≤
      weightMass ρ (fun T => 1 ≤ (T ∩ A).card)
        * weightMass ρ (fun T => (T ∩ B).card ≤ 1) := by
    calc
      0.44 * ε ≤ 0.058 * 0.147 := by nlinarith
      _ ≤ _ := mul_le_mul hAgeρ hBleρ (by norm_num)
        (weightMass_nonneg hρnn _)
  have hstage2 := three_cell_bound hρst hρrank hρnn hρtot hAB
    (ε := 0.44 * ε) (by positivity) (by nlinarith) hlow2 hhigh2
  let xmass : ℝ := weightMass ρ (fun T => (T ∩ (A ∪ B)).card = 2)
  let mid : ℝ := weightMass ρ
    (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1)
  change xmass * (0.44 * ε) * (1 - 3 * (0.44 * ε)) ≤
    mid * (1 - 2 * (0.44 * ε)) at hstage2
  change 0.12 ≤ xmass at hXeqρ
  have hxnn : 0 ≤ xmass := weightMass_nonneg hρnn _
  have hmidnn : 0 ≤ mid := weightMass_nonneg hρnn _
  let c : ℝ := 0.42 * ε
  let d : ℝ := 1 - 2 * (0.44 * ε)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hdpos : 0 < d := by dsimp [d]; nlinarith
  have hcoef : c * d ≤ (0.44 * ε) * (1 - 3 * (0.44 * ε)) := by
    dsimp [c, d]
    nlinarith
  have hscaled : (0.12 * c) * d ≤ mid * d := by
    calc
      (0.12 * c) * d = 0.12 * (c * d) := by ring
      _ ≤ xmass * (c * d) :=
        mul_le_mul_of_nonneg_right hXeqρ (mul_nonneg hc0 hdpos.le)
      _ ≤ xmass * ((0.44 * ε) * (1 - 3 * (0.44 * ε))) :=
        mul_le_mul_of_nonneg_left hcoef hxnn
      _ = xmass * (0.44 * ε) * (1 - 3 * (0.44 * ε)) := by ring
      _ ≤ mid * d := by simpa [d] using hstage2
  have hmidρ : 0.0504 * ε ≤ mid := by
    have hcancel : 0.12 * c ≤ mid := le_of_mul_le_mul_right hscaled hdpos
    calc
      0.0504 * ε = 0.12 * c := by dsimp [c]; ring
      _ ≤ mid := hcancel
  have hABdep : EventDependsOn
      (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) F :=
    eventDependsOn_and ((eventDependsOn_card_eq A 1).mono hAF)
      ((eventDependsOn_card_eq B 1).mono hBF)
  have hmid_bridge : mid = m3⁻¹ * weightMass ν (fun T =>
      (T ∩ F).card = 3 ∧
        ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) := by
    dsimp [mid]
    exact hρmass _ hABdep
  have hraw_mid : m3 * (0.0504 * ε) ≤ weightMass ν (fun T =>
      (T ∩ F).card = 3 ∧
        ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) := by
    calc
      m3 * (0.0504 * ε) ≤ m3 * mid :=
        mul_le_mul_of_nonneg_left hmidρ hm3pos.le
      _ = _ := by
        rw [hmid_bridge, ← mul_assoc, mul_inv_cancel₀ hm3ne, one_mul]
  have hfinal_bridge : weightMass ν (fun T =>
      (T ∩ F).card = 3 ∧
        ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) =
      weightMass ν (fun T =>
        (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
    apply weightMass_congr
    intro T
    change ((T ∩ ((A ∪ B) ∪ V)).card = 3 ∧
        ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1)) ↔
      ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1)
    rw [card_inter_union_of_disjoint hXV T,
      card_inter_union_of_disjoint hAB T]
    omega
  rw [hfinal_bridge] at hraw_mid
  calc
    0.01008 * ε ^ 2 = (0.2 * ε) * (0.0504 * ε) := by ring
    _ ≤ m3 * (0.0504 * ε) :=
      mul_le_mul_of_nonneg_right hm3 (by positivity)
    _ ≤ _ := hraw_mid

end TSPGap

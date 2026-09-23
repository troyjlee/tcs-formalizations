/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongHalfBundleMeans
import TSPGap.SongHalfBundleIndependence

/-!
# Song's balanced half-bundle event bound

The half bundle has at least h mean in each of the two principal partition
sides. The four-h goodness tail feeds the rescaled 5.24 kernel, and Fact
2.8 puts the present bundle edge in the complementary side. Unwinding
the actual restriction gives a strict surplus over Song's common p.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Attach the complementary bundle edge to the two outside split events. -/
theorem half_bundle_attach (M : FiberTreeModel ι n) {ν : Finset ι → ℝ}
    (hnn : WeightNonneg ν) {u v : Finset (Fin n)} (huv : Disjoint u v)
    {A B C : Finset ι} (hAB : Disjoint A B)
    (hsupp : ∀ T, ν T ≠ 0 →
      (T ∩ M.fiberOver (betweenEdges u v)).card = 1 ∧ (T ∩ C).card = 0 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T))
    {b q : ℝ} (hb : 0 ≤ b)
    (hA : b ≤ weightMass ν
      (fun T => (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card = 1))
    (hB : b ≤ weightMass ν
      (fun T => (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card = 1))
    (hker : q ≤ weightMass ν (fun T =>
      (T ∩ ((A ∪ B) \ M.fiberOver (betweenEdges u v))).card = 1 ∧
        (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
    (hind1 : weightMass ν (fun T =>
      (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card = 1 ∧ M.splitEvent u v A B 0 1 T) =
        weightMass ν (fun T => (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card = 1) *
          weightMass ν (M.splitEvent u v A B 0 1))
    (hind2 : weightMass ν (fun T =>
      (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card = 1 ∧ M.splitEvent u v A B 1 0 T) =
        weightMass ν (fun T => (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card = 1) *
          weightMass ν (M.splitEvent u v A B 1 0)) :
    b * q ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
          InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  let E := M.fiberOver (betweenEdges u v)
  let P := fun T => (T ∩ (A ∩ E)).card = 1 ∧ M.splitEvent u v A B 0 1 T
  let Q := fun T => (T ∩ (B ∩ E)).card = 1 ∧ M.splitEvent u v A B 1 0 T
  have hsplit : weightMass ν (fun T =>
      (T ∩ ((A ∪ B) \ E)).card = 1 ∧
        (T ∩ (M.fiberOver (cutEdges v) \ E)).card = 1) =
      weightMass ν (M.splitEvent u v A B 0 1) +
        weightMass ν (M.splitEvent u v A B 1 0) := by
    have hor := weightMass_or ν (M.splitEvent u v A B 0 1) (M.splitEvent u v A B 1 0)
    have hand : weightMass ν (fun T =>
        M.splitEvent u v A B 0 1 T ∧ M.splitEvent u v A B 1 0 T) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      simp only [FiberTreeModel.splitEvent]
      constructor
      · rintro ⟨⟨h0, -⟩, ⟨h1, -⟩⟩
        omega
      · intro hf
        exact hf.elim
    have hset : (A ∪ B) \ E = (A \ E) ∪ (B \ E) := by
      ext e
      simp only [mem_sdiff, mem_union]
      tauto
    have heq : weightMass ν (fun T =>
        (T ∩ ((A ∪ B) \ E)).card = 1 ∧
          (T ∩ (M.fiberOver (cutEdges v) \ E)).card = 1) =
        weightMass ν (fun T =>
          M.splitEvent u v A B 0 1 T ∨ M.splitEvent u v A B 1 0 T) := by
      apply weightMass_congr
      intro T
      rw [hset, card_inter_union_of_disjoint (hAB.mono sdiff_subset sdiff_subset) T]
      dsimp only [FiberTreeModel.splitEvent, E]
      omega
    linarith only [hor, hand, heq]
  have hand : weightMass ν (fun T => P T ∧ Q T) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    dsimp only [P, Q, FiberTreeModel.splitEvent, E]
    constructor
    · rintro ⟨⟨-, h0, -⟩, ⟨-, h1, -⟩⟩
      omega
    · intro hf
      exact hf.elim
  have himp : weightMass ν (fun T => P T ∨ Q T) ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
          InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
    apply weightMass_mono_of_support hnn
    intro T hT hj
    obtain ⟨he, hz, hu, hv⟩ := hsupp T hT
    change (T ∩ E).card = 1 at he
    have hs : ∀ S : Finset ι,
        (T ∩ S).card = (T ∩ (S \ E)).card + (T ∩ (S ∩ E)).card := by
      intro S
      rw [← card_inter_union_of_disjoint (disjoint_sdiff_inter S E) T, sdiff_union_inter]
    have ha := hs A
    have hb := hs B
    have hparts : (T ∩ (A ∩ E)).card + (T ∩ (B ∩ E)).card ≤ 1 := by
      rw [← card_inter_union_of_disjoint
        (hAB.mono inter_subset_left inter_subset_left) T, ← he]
      exact card_le_card (inter_subset_inter_left
        (union_subset inter_subset_right inter_subset_right))
    have hvcard := hs (M.fiberOver (cutEdges v))
    have hEV : E ⊆ M.fiberOver (cutEdges v) :=
      M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
    rw [inter_eq_right.mpr hEV, he] at hvcard
    change ((T ∩ (A ∩ E)).card = 1 ∧
      (T ∩ (A \ E)).card = 0 ∧ (T ∩ (B \ E)).card = 1 ∧
        (T ∩ (M.fiberOver (cutEdges v) \ E)).card = 1) ∨
      ((T ∩ (B ∩ E)).card = 1 ∧
      (T ∩ (A \ E)).card = 1 ∧ (T ∩ (B \ E)).card = 0 ∧
        (T ∩ (M.fiberOver (cutEdges v) \ E)).card = 1) at hj
    exact ⟨by omega, by omega, hz, by omega, hu, hv⟩
  have hsum : weightMass ν P + weightMass ν Q ≤ weightMass ν (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
          InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
    linarith only [weightMass_or ν P Q, hand, himp]
  have hprod1 := mul_le_mul_of_nonneg_right hA
    (weightMass_nonneg hnn (M.splitEvent u v A B 0 1))
  have hprod2 := mul_le_mul_of_nonneg_right hB
    (weightMass_nonneg hnn (M.splitEvent u v A B 1 0))
  have htail := mul_le_mul_of_nonneg_left hker hb
  rw [hsplit, mul_add] at htail
  change weightMass ν P = _ at hind1
  change weightMass ν Q = _ at hind2
  linarith only [htail, hprod1, hprod2, hind1, hind2, hsum]

/-- Song 5.24 for a full fiber bundle, retaining the original-law mass. -/
theorem lemma_5_24_indexed (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v : Finset (Fin n)}
    (huv : Disjoint u v) (hc : M.TwoAtomUnionData w u v) {A B C : Finset ι}
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxAE : h ≤ expCard w (A ∩ M.fiberOver (betweenEdges u v)))
    (hxBE : h ≤ expCard w (B ∩ M.fiberOver (betweenEdges u v)))
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hgood : 4 * h ≤ weightMass (M.tau w u v) (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (hind1 : M.CondIndepAt w u v C
      (fun T => (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card = 1)
      (M.splitEvent u v A B 0 1))
    (hind2 : M.CondIndepAt w u v C
      (fun T => (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card = 1)
      (M.splitEvent u v A B 1 0)) :
    p + 1.03e-9 < weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
          InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  let E := M.fiberOver (betweenEdges u v)
  let F := M.fiberOver (twoAtomInternal u v)
  let V := M.fiberOver (cutEdges v) \ E
  let X := (A ∪ B) \ E
  let ν := largeBundleLaw w F (twoAtomBudget u v) E C
  have hC : C ⊆ M.fiberOver (cutEdges u) := by rw [hpart]; exact subset_union_right
  have hEU : E ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEV : E ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hSC : M.SupportComplete w E u v := ⟨Subset.refl _, fun _ _ => inter_subset_right⟩
  have D : WindowConditioningData w F (twoAtomBudget u v) E C k :=
    window_conditioning_indexed M hw huv hc.toTwoAtomOneHotData
      (Subset.refl _) hC hdef (by linarith only [(abs_le.mp hxE).1]) hxC
  have hout := window_cut_outside M huv
  have hUV : Disjoint (M.fiberOver (cutEdges u)) V := by
    apply disjoint_left.mpr
    intro e heu hev
    obtain ⟨hev, heE⟩ := mem_sdiff.mp hev
    have hh : e ∈ M.fiberOver (cutEdges u ∩ cutEdges v) := by
      rw [M.fiberOver_inter]
      exact mem_inter.mpr ⟨heu, hev⟩
    exact heE (by rwa [cutEdges_inter_cutEdges huv] at hh)
  have hEVeq : E ∪ V = M.fiberOver (cutEdges v) := union_sdiff_of_subset hEV
  have hm : HalfBundleMeanBounds ν X V :=
    half_bundle_mean_bounds hw D hAB hAC hBC (by rwa [← hpart]) (by rwa [← hpart])
      (by rw [← hpart]; exact union_subset hout.1 (sdiff_subset.trans hout.2))
      hxE hxA hxB hxC (by rw [hEVeq]; exact hxv)
  have haway : ∀ T, ν T ≠ 0 → T ∩ (X ∪ V) = T ∩ windowPuncture M u v := by
    intro T hT
    have hz := card_eq_zero.mp (D.clean.supp T hT).2.2
    ext e
    have hn : e ∈ T → e ∉ C := fun he heC => by
      have hh := mem_inter.mpr ⟨he, heC⟩
      rw [hz] at hh
      exact notMem_empty e hh
    simp only [X, V, E, windowPuncture, hpart, mem_inter, mem_union, mem_sdiff]
    tauto
  have htail := window_low_tail_indexed M huv hc.toTwoAtomCrossData D hSC
    hC hxE hxC hxu hxv hgood
  have hker : 0.0238 * windowError ≤ weightMass ν (fun T =>
      (T ∩ X).card = 1 ∧ (T ∩ V).card = 1) := by
    have hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (X ∪ V)).card := by
      intro T hT
      rw [haway T hT]
      exact window_puncture_baseline M hc.toTwoAtomCrossData
        (D.face.supp T (D.clean.supp T hT).1).1
    apply half_bundle_kernel (ν := ν) D.clean.law
      (hUV.mono_left (sdiff_subset.trans (by rw [hpart]; exact subset_union_left))) hbase hm
    convert htail using 1
    exact weightMass_congr_of_support fun T hT => by rw [haway T hT]
  have hone : ∀ T, w T ≠ 0 → (T ∩ F).card = twoAtomBudget u v → (T ∩ E).card ≤ 1 := by
    intro T hT hf
    obtain ⟨hu, hv⟩ := (hc.eq_iff T hT).mp hf
    exact hc.one_hot T hT hu hv
  have hpartmass : ∀ Z, Z ⊆ E → Disjoint Z C → h ≤ expCard w Z →
      1.99 * h ≤ weightMass ν (fun T => (T ∩ Z).card = 1) := by
    intro Z hZE hZC hxZ
    have hz := window_bundle_part_lower D hone (hEU.trans hout.1) hZE hZC
      (by linarith only [(abs_le.mp hxE).2]) hxZ
    have hνone : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1 := fun T hT =>
      (card_le_card (inter_subset_inter_left hZE)).trans (D.clean.supp T hT).2.1.le
    rw [← expCard_eq_weightMass_one hνone]
    exact hz
  have hhappy := half_bundle_attach M (ν := ν) D.clean.law.nn huv hAB
    (fun T hT => ⟨(D.clean.supp T hT).2.1, (D.clean.supp T hT).2.2,
      (hc.eq_iff T (D.face.supp T (D.clean.supp T hT).1).1).mp
        (D.face.supp T (D.clean.supp T hT).1).2⟩)
    (by norm_num [h] : 0 ≤ 1.99 * h)
    (hpartmass (A ∩ E) inter_subset_right (hAC.mono_left inter_subset_left) hxAE)
    (hpartmass (B ∩ E) inter_subset_right (hBC.mono_left inter_subset_left) hxBE)
    hker (D.independent M hc hind1) (D.independent M hc hind2)
  let Happy := fun T =>
    (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)
  change (1.99 * h) * (0.0238 * windowError) ≤ weightMass ν Happy at hhappy
  have hmass := mul_le_mul_of_nonneg_right hhappy
    (le_trans (by norm_num) D.mass_ge)
  change _ ≤ weightMass (largeBundleLaw w F (twoAtomBudget u v) E C) Happy *
    largeBundleMass w F (twoAtomBudget u v) E C at hmass
  rw [D.unwind] at hmass
  have hdrop : weightMass w (fun T =>
      ((Happy T ∧ (T ∩ (C \ E)).card = 0) ∧ (T ∩ (E \ C)).card = 1) ∧
        (T ∩ F).card = twoAtomBudget u v) ≤ weightMass w Happy :=
    weightMass_mono hw.nn (fun _ hT => hT.1.1.1)
  have hbudget := mul_le_mul_of_nonneg_left D.mass_ge
    (by norm_num [h, windowError] : 0 ≤ (1.99 * h) * (0.0238 * windowError))
  have hprob : halfBundleProbability ≤ weightMass w Happy := by
    unfold halfBundleProbability
    nlinarith only [hbudget, hmass, hdrop]
  exact half_bundle_probability_gt.trans_le hprob

end TSPGap.Song

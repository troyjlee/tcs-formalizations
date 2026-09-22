/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedGeometry
import TSPGap.SongPairedPrefix

/-!
# Initial atom-face means for Song's paired bundles

The face is constructed from the existing three-atom count certificate.
Its outside upper comparison has no deficiency loss. In particular, the
whole avoided union costs at most its original mean, rather than the sum
of separately perturbed means. All numerical inputs below are in the
original normalized law; no conditional means are assumed.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The three-atom face with its one-hot bundles, original-space identity,
and signed-direction expectation transfers. -/
structure PairedAtomLaw {n : ℕ} (M : FiberTreeModel ι n) (w : Finset ι → ℝ)
    (u v z : Finset (Fin n)) (rank : ℕ) : Prop where
  law : LawData (M.tau3 w u v z) rank
  mass_pos : 0 < totalMass (faceWeight w
    (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
  mass_ge : 1 - 3 * d₀ ≤ totalMass (faceWeight w
    (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
  support : ∀ T, M.tau3 w u v z T ≠ 0 → w T ≠ 0 ∧
    InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)
  one_e : ∀ T, M.tau3 w u v z T ≠ 0 → (T ∩ M.fiberOver (betweenEdges u v)).card ≤ 1
  one_f : ∀ T, M.tau3 w u v z T ≠ 0 → (T ∩ M.fiberOver (betweenEdges v z)).card ≤ 1
  one_z : ∀ T, M.tau3 w u v z T ≠ 0 → (T ∩ M.fiberOver (betweenEdges u z)).card ≤ 1
  lower : ∀ S, S ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ →
    expCard w S - 3 * d₀ ≤ expCard (M.tau3 w u v z) S
  upper : ∀ S, S ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ →
    expCard (M.tau3 w u v z) S ≤ expCard w S
  unwind : ∀ P, weightMass (M.tau3 w u v z) P * totalMass (faceWeight w
    (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) =
      weightMass w (fun T => P T ∧
        (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z)

/-- No new graph theorem: tight face count supplies all three induced
trees, and the existing one-hot clauses apply on that support. -/
theorem paired_atom_law {n : ℕ} (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {rank : ℕ} (hw : LawData w rank) {u v z : Finset (Fin n)}
    (hc : M.ThreeAtomUzData w u v z)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) ≤ 3 * d₀) : PairedAtomLaw M w u v z rank := by
  have hge := (sub_le_sub_left hdef 1).trans (hw.face_mass_ge hc.le)
  have hm : 0 < totalMass (faceWeight w
      (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) :=
    lt_of_lt_of_le (by norm_num [d₀]) hge
  have hs : ∀ T, M.tau3 w u v z T ≠ 0 → w T ≠ 0 ∧
      InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧
      InducesTree z (M.project T) := by
    intro T hT
    have ht := faceDist_ne_zero_imp hT
    rw [setCost_indicatorCost] at ht
    exact ⟨ht.1, (hc.eq_iff T ht.1).mp ht.2⟩
  refine ⟨hw.face hc.le hm, hm, hge, hs, ?_, ?_, ?_, ?_, ?_, hw.face_unwind hm⟩
  · intro T hT
    exact hc.one_hot_uv T (hs T hT).1 (hs T hT).2.1 (hs T hT).2.2.1
  · intro T hT
    exact hc.one_hot_vz T (hs T hT).1 (hs T hT).2.2.1 (hs T hT).2.2.2
  · intro T hT
    exact hc.one_hot_uz T (hs T hT).1 (hs T hT).2.1 (hs T hT).2.2.2
  · intro S hS
    have hh := hw.face_outside_ge hc.le hm hS
    change expCard w S - faceDeficiency w _ _ ≤ expCard (M.tau3 w u v z) S at hh
    linarith only [hh, hdef]
  · exact fun S hS => hw.face_outside_le hc.le hm hS

/-- Original-law side accounting. No topology, fixed rank or normalization
is used: the bundle sits in the three sides and its wrong-side mass is small. -/
theorem partition_side_means {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {A B C E : Finset ι} (hE : E ⊆ (A ∪ B) ∪ C)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxEB : expCard w (E ∩ B) ≤ h) :
    1 / 2 - 2 * h - 2 * r - d₀ ≤ expCard w (E ∩ A) ∧
      1 / 2 - h - r ≤ expCard w (A \ E) ∧
      expCard w (A \ E) ≤ 1 / 2 + 2 * h + 2 * r + 2 * d₀ := by
  have hsplit : E ⊆ ((E ∩ A) ∪ (E ∩ B)) ∪ C := by
    intro e he
    have hh := hE he
    simp only [mem_union, mem_inter] at hh ⊢
    tauto
  have hm := expCard_mono hnn hsplit
  have hu := expCard_union_le hnn ((E ∩ A) ∪ (E ∩ B)) C
  have hu' := expCard_union_le hnn (E ∩ A) (E ∩ B)
  obtain ⟨heL, heU⟩ := abs_le.mp hxE
  have hea : 1 / 2 - 2 * h - 2 * r - d₀ ≤ expCard w (E ∩ A) := by
    linarith only [hm, hu, hu', heL, hxEB, hxC]
  have hs := expCard_split w A E
  rw [inter_comm A E] at hs
  have hem := expCard_mono hnn (inter_subset_left (s₁ := E) (s₂ := A))
  exact ⟨hea, by linarith only [hxA.1, hs, hem, heU],
    by linarith only [hxA.2, hs, hea]⟩

/-- The pre-prefix means consumed in both branches. Upper bounds use the
outside-face sign, so they are slightly sharper than the source budgets. -/
structure PairedFaceBounds (ν : Finset ι → ℝ) (A B C E F : Finset ι) : Prop where
  ea_lower : 1 / 2 - 2 * h - 2 * r - 4 * d₀ ≤ expCard ν (E ∩ A)
  a_lower : 1 / 2 - 2 * h - 2 * r - 4 * d₀ ≤ expCard ν (A \ E)
  a_upper : expCard ν (A \ E) ≤ 1 / 2 + 2 * h + 2 * r + 2 * d₀
  b_upper : expCard ν (B \ F) ≤ 1 / 2 + 2 * h + 2 * r + 2 * d₀
  zero_upper : expCard ν (C ∪ (E ∩ B)) ≤ h + 2 * r + d₀
  union_upper : expCard ν ((C ∪ (E ∩ B)) ∪ F) ≤ 1 / 2 + 2 * h + 2 * r + d₀

/-- Supply the initial means using only original-law marginal hypotheses
and the one-sided transfers of the actual atom face. -/
theorem paired_face_bounds {w ν : Finset ι → ℝ} (hnn : WeightNonneg w)
    {A B C E F Z I : Finset ι} (G : PairedBoundaryGeometry A B C E F Z I)
    (hlo : ∀ S, S ⊆ Iᶜ → expCard w S - 3 * d₀ ≤ expCard ν S)
    (hhi : ∀ S, S ⊆ Iᶜ → expCard ν S ≤ expCard w S)
    (hxE : |expCard w E - 1 / 2| ≤ h) (hxF : |expCard w F - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxEB : expCard w (E ∩ B) ≤ h) (hxFA : expCard w (F ∩ A) ≤ h) :
    PairedFaceBounds ν A B C E F := by
  have hA : A ⊆ Iᶜ :=
    (subset_union_left.trans (subset_union_left.trans subset_union_left)).trans G.outside
  have hB : B ⊆ Iᶜ :=
    (subset_union_right.trans (subset_union_left.trans subset_union_left)).trans G.outside
  have hC : C ⊆ Iᶜ := (subset_union_right.trans subset_union_left).trans G.outside
  have hF : F ⊆ Iᶜ := (G.f_subset.trans subset_union_left).trans G.outside
  have hD : C ∪ (E ∩ B) ⊆ Iᶜ := union_subset hC (inter_subset_right.trans hB)
  have ha := partition_side_means hnn G.e_subset hxE hxA hxC hxEB
  have hfsub : F ⊆ (B ∪ A) ∪ C := by rw [union_comm B A]; exact G.f_subset
  have hb := partition_side_means hnn hfsub hxF hxB hxC hxFA
  have hzero : expCard w (C ∪ (E ∩ B)) ≤ h + 2 * r + d₀ := by
    have hh := expCard_union_le hnn C (E ∩ B)
    linarith only [hh, hxC, hxEB]
  refine ⟨?_, ?_, (hhi _ (sdiff_subset.trans hA)).trans ha.2.2,
    (hhi _ (sdiff_subset.trans hB)).trans hb.2.2, (hhi _ hD).trans hzero, ?_⟩
  · have hh := hlo (E ∩ A) (inter_subset_right.trans hA)
    linarith only [hh, ha.1]
  · have hh := hlo (A \ E) (sdiff_subset.trans hA)
    have hmargin : 0 ≤ h + r + d₀ := by norm_num [h, r, d₀]
    linarith only [hh, ha.2.1, hmargin]
  · have hh := expCard_union_le hnn (C ∪ (E ∩ B)) F
    have ht := hhi _ (union_subset hD hF)
    have hfu := (abs_le.mp hxF).2
    linarith only [hh, ht, hzero, hfu]

/-- The original overlap charged by the later F-avoidance is bounded by
the wrong-side marginal. This applies to arbitrary piece sides. -/
theorem paired_overlap_mean {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {A E F : Finset ι} (hxFA : expCard w (F ∩ A) ≤ h) :
    expCard w ((A \ E) ∩ F) ≤ h := by
  have hs : (A \ E) ∩ F ⊆ F ∩ A := by
    intro i hi
    exact mem_inter.mpr ⟨(mem_inter.mp hi).2, (mem_sdiff.mp (mem_inter.mp hi).1).1⟩
  exact (expCard_mono hnn hs).trans hxFA

end TSPGap.Song

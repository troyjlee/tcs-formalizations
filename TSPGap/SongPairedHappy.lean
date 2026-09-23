/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedProfiles

/-!
# The paired coefficient events imply three-atom happiness

One count identity handles both Z branches. The extraction targets are
`(1,1,2)` when Z is absent and `(1,0,1)` when it is present. The atom-face
and bundle restrictions are retained explicitly in the raw-event bridge.
The absent branch's sure W baseline is proved separately from crossing;
an expectation lower bound would not suffice for coefficient extraction.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Split a count into its removed and retained coordinates. -/
theorem paired_count_split (T D E : Finset ι) :
    (T ∩ D).card = (T ∩ (D \ E)).card + (T ∩ (D ∩ E)).card := by
  calc
    _ = (T ∩ ((D \ E) ∪ (D ∩ E))).card := by rw [sdiff_union_inter]
    _ = _ := card_inter_union_of_disjoint
      (sdiff_disjoint.mono_right inter_subset_right) T

omit [Fintype ι] in
/-- The common count calculation, parameterized by the far-bundle count.
No tree or probability hypothesis is used in this identity. -/
theorem paired_cut_counts {A B C E F Z U V W T : Finset ι}
    (G : PairedCountGeometry A B E F Z U W)
    (hpart : V = (A ∪ B) ∪ C) (hAB : Disjoint A B)
    (hAC : Disjoint A C) (hBC : Disjoint B C) (hEU : E ⊆ U) (hFW : F ⊆ W)
    (hE : (T ∩ E).card = 1) (hEA : (T ∩ (E ∩ A)).card = 1)
    (hF : (T ∩ F).card = 0) (hC : (T ∩ C).card = 0)
    (hB : (T ∩ (B \ F)).card = 0) {j l z : ℕ}
    (hZ : (T ∩ Z).card = z) (hj : j + z = 1) (hl : l + z = 2)
    (hcell : (T ∩ (A \ E)).card = 1 ∧
      (T ∩ (U \ (E ∪ Z))).card = j ∧ (T ∩ (W \ (F ∪ Z))).card = l) :
    (T ∩ U).card = 2 ∧ (T ∩ V).card = 2 ∧ (T ∩ W).card = 2 := by
  have hu := G.u_shift T
  rw [card_inter_union_of_disjoint G.au T] at hu
  have hw := G.w_shift T
  rw [card_inter_union_of_disjoint G.bw T] at hw
  have hsU := paired_count_split T U E
  rw [inter_eq_right.mpr hEU] at hsU
  have hsW := paired_count_split T W F
  rw [inter_eq_right.mpr hFW] at hsW
  have hsA := paired_count_split T A E
  rw [inter_comm A E] at hsA
  have hsB := paired_count_split T B F
  have hBF : (T ∩ (B ∩ F)).card ≤ (T ∩ F).card :=
    card_le_card (inter_subset_inter_left inter_subset_right)
  have hsV : (T ∩ V).card = (T ∩ A).card + (T ∩ B).card + (T ∩ C).card := by
    rw [hpart, card_inter_union_of_disjoint (disjoint_union_left.mpr ⟨hAC, hBC⟩) T,
      card_inter_union_of_disjoint hAB T]
  omega

/-- Restore the three endpoint counts and trees from the raw restriction
and coefficient event. This applies before normalizing any restriction. -/
theorem paired_happy_of_raw_cells {n : ℕ} (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {u v z : Finset (Fin n)}
    (hc : M.ThreeAtomUzData w u v z)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    {A B C T : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hT : w T ≠ 0)
    (hface : (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z)
    (hEA : (T ∩ (M.fiberOver (betweenEdges u v) ∩ A)).card = 1)
    (hF : (T ∩ M.fiberOver (betweenEdges v z)).card = 0)
    (hC : (T ∩ C).card = 0)
    (hB : (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 0)
    {j l s : ℕ} (hZ : (T ∩ M.fiberOver (betweenEdges u z)).card = s)
    (hj : j + s = 1) (hl : l + s = 2)
    (hcell : (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ (M.fiberOver (cutEdges u) \
        (M.fiberOver (betweenEdges u v) ∪ M.fiberOver (betweenEdges u z)))).card = j ∧
      (T ∩ (M.fiberOver (cutEdges z) \
        (M.fiberOver (betweenEdges v z) ∪ M.fiberOver (betweenEdges u z)))).card = l) :
    (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
      (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧
      InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧
      InducesTree z (M.project T) := by
  obtain ⟨htu, htv, htz⟩ := (hc.eq_iff T hT).mp hface
  have hone := hc.one_hot_uv T hT htu htv
  have hsub : (T ∩ (M.fiberOver (betweenEdges u v) ∩ A)).card ≤
      (T ∩ M.fiberOver (betweenEdges u v)).card :=
    card_le_card (inter_subset_inter_left inter_subset_left)
  have hE : (T ∩ M.fiberOver (betweenEdges u v)).card = 1 := by omega
  have hA : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact subset_union_left.trans subset_union_left
  have hBs : B ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact subset_union_right.trans subset_union_left
  have G := paired_count_geometry_indexed M huv hvz huz hA hBs hAB
  obtain ⟨hU, hV, hW⟩ := paired_cut_counts G hpart hAB hAC hBC
    (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv))
    (M.fiberOver_mono (betweenEdges_subset_cutEdges hvz)) hE hEA hF hC hB hZ hj hl hcell
  exact ⟨hU, hV, hW, htu, htv, htz⟩

omit [Fintype ι] in
/-- With F and Z absent, the pruned W-cut equals its full cut on support.
Crossing, not its mean, supplies the baseline for the `(1,1,2)` extraction. -/
theorem paired_absent_baseline {ν : Finset ι → ℝ} {W F Z : Finset ι}
    (hcross : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ W).card)
    (hF : ∀ T, ν T ≠ 0 → (T ∩ F).card = 0)
    (hZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card = 0) :
    ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (W \ (F ∪ Z))).card := by
  intro T hT
  have hf := card_eq_zero.mp (hF T hT)
  have hz := card_eq_zero.mp (hZ T hT)
  have heq : T ∩ (W \ (F ∪ Z)) = T ∩ W := by
    ext e
    have hnf : e ∈ T → e ∉ F := fun het hef => by
      have hh := mem_inter.mpr ⟨het, hef⟩
      rw [hf] at hh
      exact notMem_empty _ hh
    have hnz : e ∈ T → e ∉ Z := fun het hez => by
      have hh := mem_inter.mpr ⟨het, hez⟩
      rw [hz] at hh
      exact notMem_empty _ hh
    simp only [mem_inter, mem_sdiff, mem_union]
    tauto
  rw [heq]
  exact hcross T hT

end TSPGap.Song

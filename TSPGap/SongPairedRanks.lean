/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedStart

/-!
# The pruned rank events in Song's paired branches

Removing the far bundle Z subtracts its count from both original rank
events. The identity is pointwise. Only its specialization to Z = 0 or
Z = 1 uses the support of a conditioned law. Partition sides remain
arbitrary coordinate sets, including sides splitting parallel pieces.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Pruning a contained set separates its count without natural subtraction. -/
theorem count_prune_shift {A U E Z : Finset ι}
    (hAU : Disjoint (A \ E) (U \ E)) (hZ : Z ⊆ U \ E) (T : Finset ι) :
    (T ∩ (U \ E)).card + (T ∩ (A \ E)).card =
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card + (T ∩ Z).card := by
  have hs : (U \ (E ∪ Z)) ∪ Z = U \ E := by
    ext i
    have hz' : i ∈ Z → i ∈ U ∧ i ∉ E := fun hi => mem_sdiff.mp (hZ hi)
    simp only [mem_union, mem_sdiff]
    tauto
  have hd : Disjoint (U \ (E ∪ Z)) Z := by
    exact disjoint_left.mpr fun i hi hz =>
      (mem_sdiff.mp hi).2 (mem_union_right _ hz)
  have ha : Disjoint (A \ E) (U \ (E ∪ Z)) :=
    disjoint_of_subset_right (by intro i hi; simp only [mem_sdiff, mem_union] at *; tauto) hAU
  rw [card_inter_union_of_disjoint ha, ← hs, card_inter_union_of_disjoint hd]
  omega

/-- The count geometry needed by the shared mean profile and final table. -/
structure PairedCountGeometry (A B E F Z U W : Finset ι) : Prop where
  ab : Disjoint (A \ E) (B \ F)
  au : Disjoint (A \ E) (U \ (E ∪ Z))
  aw : Disjoint (A \ E) (W \ (F ∪ Z))
  bu : Disjoint (B \ F) (U \ (E ∪ Z))
  bw : Disjoint (B \ F) (W \ (F ∪ Z))
  uw : Disjoint (U \ (E ∪ Z)) (W \ (F ∪ Z))
  fx : F ∩ ((A \ E) ∪ (U \ (E ∪ Z))) ⊆ A \ E
  yf : Disjoint ((B \ F) ∪ (W \ (F ∪ Z))) F
  xe : Disjoint ((A \ E) ∪ (U \ (E ∪ Z))) (E ∩ A)
  be : Disjoint (B \ F) (E ∩ A)
  ef : Disjoint (E ∩ A) F
  u_shift : ∀ T, (T ∩ (U \ E)).card + (T ∩ (A \ E)).card =
    (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card + (T ∩ Z).card
  w_shift : ∀ T, (T ∩ (W \ F)).card + (T ∩ (B \ F)).card =
    (T ∩ ((B \ F) ∪ (W \ (F ∪ Z)))).card + (T ∩ Z).card

omit [Fintype ι] in
/-- All graph input is contained in three cut intersections and the fact
that the far endpoint misses the opposite adjacent bundle. -/
theorem paired_count_geometry_of_cuts {A B E F Z U V W : Finset ι}
    (hUV : U ∩ V = E) (hVW : V ∩ W = F) (hUW : U ∩ W = Z)
    (hFU : Disjoint F U) (hA : A ⊆ V) (hB : B ⊆ V) (hAB : Disjoint A B) :
    PairedCountGeometry A B E F Z U W := by
  have he (i : ι) : i ∈ E ↔ i ∈ U ∧ i ∈ V := by rw [← hUV, mem_inter]
  have hf (i : ι) : i ∈ F ↔ i ∈ V ∧ i ∈ W := by rw [← hVW, mem_inter]
  have hz (i : ι) : i ∈ Z ↔ i ∈ U ∧ i ∈ W := by rw [← hUW, mem_inter]
  have hAU : Disjoint (A \ E) (U \ E) := by
    apply disjoint_left.mpr
    intro i hi hu
    exact (mem_sdiff.mp hi).2 ((he i).mpr ⟨(mem_sdiff.mp hu).1, hA (mem_sdiff.mp hi).1⟩)
  have hBW : Disjoint (B \ F) (W \ F) := by
    apply disjoint_left.mpr
    intro i hi hw
    exact (mem_sdiff.mp hi).2 ((hf i).mpr ⟨hB (mem_sdiff.mp hi).1, (mem_sdiff.mp hw).1⟩)
  have hZU : Z ⊆ U \ E := by
    intro i hi
    obtain ⟨hu, hw⟩ := (hz i).mp hi
    refine mem_sdiff.mpr ⟨hu, fun hiE => ?_⟩
    exact disjoint_left.mp hFU ((hf i).mpr ⟨((he i).mp hiE).2, hw⟩) hu
  have hZW : Z ⊆ W \ F := by
    intro i hi
    obtain ⟨hu, hw⟩ := (hz i).mp hi
    exact mem_sdiff.mpr ⟨hw, fun hiF => disjoint_left.mp hFU hiF hu⟩
  refine ⟨disjoint_of_subset_left sdiff_subset
      (disjoint_of_subset_right sdiff_subset hAB), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      count_prune_shift hAU hZU, count_prune_shift hBW hZW⟩
  · apply disjoint_of_subset_right _ hAU
    intro i hi; simp only [mem_sdiff, mem_union] at *; tauto
  · apply disjoint_left.mpr
    intro i hi hw
    exact (mem_sdiff.mp hw).2 (mem_union_left _
      ((hf i).mpr ⟨hA (mem_sdiff.mp hi).1, (mem_sdiff.mp hw).1⟩))
  · apply disjoint_left.mpr
    intro i hi hu
    exact (mem_sdiff.mp hu).2 (mem_union_left _
      ((he i).mpr ⟨(mem_sdiff.mp hu).1, hB (mem_sdiff.mp hi).1⟩))
  · apply disjoint_of_subset_right _ hBW
    intro i hi; simp only [mem_sdiff, mem_union] at *; tauto
  · apply disjoint_left.mpr
    intro i hu hw
    exact (mem_sdiff.mp hu).2 (mem_union_right _
      ((hz i).mpr ⟨(mem_sdiff.mp hu).1, (mem_sdiff.mp hw).1⟩))
  · intro i hi
    rcases mem_union.mp (mem_inter.mp hi).2 with ha | hu
    · exact ha
    · exact (disjoint_left.mp hFU (mem_inter.mp hi).1 (mem_sdiff.mp hu).1).elim
  · apply disjoint_left.mpr
    intro i hi hiF
    rcases mem_union.mp hi with hb | hw
    · exact (mem_sdiff.mp hb).2 hiF
    · exact (mem_sdiff.mp hw).2 (mem_union_left _ hiF)
  · apply disjoint_left.mpr
    intro i hi hiE
    rcases mem_union.mp hi with ha | hu
    · exact (mem_sdiff.mp ha).2 (mem_inter.mp hiE).1
    · exact (mem_sdiff.mp hu).2 (mem_union_left _ (mem_inter.mp hiE).1)
  · exact disjoint_of_subset_left sdiff_subset
      (disjoint_of_subset_right inter_subset_right hAB.symm)
  · apply disjoint_left.mpr
    intro i hi hiF
    exact disjoint_left.mp hFU hiF ((he i).mp (mem_inter.mp hi).1).1

/-- Fiber-tree instance, with no fiber-saturation condition on A or B. -/
theorem paired_count_geometry_indexed {n : ℕ} (M : FiberTreeModel ι n)
    {u v z : Finset (Fin n)} (huv : Disjoint u v) (hvz : Disjoint v z)
    (huz : Disjoint u z) {A B : Finset ι}
    (hA : A ⊆ M.fiberOver (cutEdges v)) (hB : B ⊆ M.fiberOver (cutEdges v))
    (hAB : Disjoint A B) :
    PairedCountGeometry A B (M.fiberOver (betweenEdges u v))
      (M.fiberOver (betweenEdges v z)) (M.fiberOver (betweenEdges u z))
      (M.fiberOver (cutEdges u)) (M.fiberOver (cutEdges z)) := by
  apply paired_count_geometry_of_cuts
  · rw [← M.fiberOver_inter, cutEdges_inter_cutEdges huv]
  · rw [← M.fiberOver_inter, cutEdges_inter_cutEdges hvz]
  · rw [← M.fiberOver_inter, cutEdges_inter_cutEdges huz]
  · exact M.disjoint_fiberOver (betweenEdges_disjoint_cutEdges huv.symm huz.symm)
  · exact hA
  · exact hB
  · exact hAB

omit [Fintype ι] in
/-- A single identity specializes to rank two when Z is absent and rank
one when Z is present. No subtraction is truncated. -/
theorem PairedCountGeometry.rank_events {A B E F Z U W T : Finset ι}
    (G : PairedCountGeometry A B E F Z U W) {j z : ℕ}
    (hZ : (T ∩ Z).card = z) (hj : j + z = 2) :
    ((T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2 ↔
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = j) ∧
    ((T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2 ↔
      (T ∩ ((B \ F) ∪ (W \ (F ∪ Z)))).card = j) := by
  rw [G.u_shift T, G.w_shift T, hZ]
  omega

/-- Low-Z specialization is guarded by nonzero prefix weight. -/
theorem PairedCountGeometry.absent_rank_events {A B C E F Z U W T : Finset ι}
    (G : PairedCountGeometry A B E F Z U W) {ν : Finset ι → ℝ}
    (hT : avoidDist ν (Z ∪ (C ∪ (E ∩ B))) T ≠ 0) :
    ((T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2 ↔
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = 2) ∧
    ((T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2 ↔
      (T ∩ ((B \ F) ∪ (W \ (F ∪ Z)))).card = 2) := by
  have ht := (avoidDist_ne_zero_imp hT).2
  have hh := card_le_card (inter_subset_inter (Subset.refl T)
    (subset_union_left (s₁ := Z) (s₂ := C ∪ (E ∩ B))))
  exact G.rank_events (z := 0) (by omega) (by decide)

/-- High-Z specialization subtracts the present far edge from both ranks. -/
theorem PairedCountGeometry.present_rank_events {A B C E F Z U W T : Finset ι}
    (G : PairedCountGeometry A B E F Z U W) {ν : Finset ι → ℝ}
    (hT : presentPrefixLaw ν Z (C ∪ (E ∩ B)) T ≠ 0) :
    ((T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2 ↔
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = 1) ∧
    ((T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2 ↔
      (T ∩ ((B \ F) ∪ (W \ (F ∪ Z)))).card = 1) :=
  G.rank_events (present_prefix_support hT).2.1 (by decide)

end TSPGap.Song

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527SetupIndexed

/-!
# Boundary geometry for Song's paired conditioning prefixes

The sides A/B/C are arbitrary coordinate subsets, not projections of base
edge sides. Only the full bundles and atom-internal sets are fiber-saturated.
The certificate below records the small part of the geometry needed before
the rank-event identifications and coefficient extraction.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two adjacent bundles lie in the partitioned middle boundary; the
far bundle misses it. All these coordinates are outside the atom face. -/
structure PairedBoundaryGeometry (A B C E F Z I : Finset ι) : Prop where
  e_subset : E ⊆ (A ∪ B) ∪ C
  f_subset : F ⊆ (A ∪ B) ∪ C
  ab : Disjoint A B
  ac : Disjoint A C
  bc : Disjoint B C
  ef : Disjoint E F
  z_boundary : Disjoint Z ((A ∪ B) ∪ C)
  outside : ((A ∪ B) ∪ C) ∪ Z ⊆ Iᶜ

namespace PairedBoundaryGeometry
variable {A B C E F Z I : Finset ι}

/-- Disjointness needed by presence of Z, then avoidance of C/e(B). -/
theorem present_disjoint (G : PairedBoundaryGeometry A B C E F Z I) :
    Disjoint ((C ∪ (E ∩ B)) ∪ F) Z ∧ Disjoint (E ∩ A) Z ∧
      Disjoint (E ∩ A) (C ∪ (E ∩ B)) ∧ Disjoint (E ∩ A) F ∧
      Disjoint (A \ E) Z ∧ Disjoint (B \ F) Z ∧
      Disjoint (A \ E) (C ∪ (E ∩ B)) := by
  have hA : A ⊆ (A ∪ B) ∪ C := subset_union_left.trans subset_union_left
  have hB : B ⊆ (A ∪ B) ∪ C := subset_union_right.trans subset_union_left
  have hD : C ∪ (E ∩ B) ⊆ (A ∪ B) ∪ C :=
    union_subset subset_union_right (inter_subset_right.trans hB)
  have hDZ := disjoint_of_subset_left hD G.z_boundary.symm
  have hAZ := disjoint_of_subset_left hA G.z_boundary.symm
  have hBZ := disjoint_of_subset_left hB G.z_boundary.symm
  have hAD : Disjoint A (C ∪ (E ∩ B)) := disjoint_union_right.mpr
    ⟨G.ac, disjoint_of_subset_right inter_subset_right G.ab⟩
  exact ⟨disjoint_union_left.mpr
      ⟨hDZ, disjoint_of_subset_left G.f_subset G.z_boundary.symm⟩,
    disjoint_of_subset_left inter_subset_right hAZ,
    disjoint_of_subset_left inter_subset_right hAD,
    disjoint_of_subset_left inter_subset_left G.ef,
    disjoint_of_subset_left sdiff_subset hAZ,
    disjoint_of_subset_left sdiff_subset hBZ,
    disjoint_of_subset_left sdiff_subset hAD⟩

/-- Adding the far bundle to the avoided union still misses e(A) and A-e. -/
theorem absent_disjoint (G : PairedBoundaryGeometry A B C E F Z I) :
    Disjoint (E ∩ A) (Z ∪ (C ∪ (E ∩ B))) ∧
      Disjoint (A \ E) (Z ∪ (C ∪ (E ∩ B))) := by
  obtain ⟨_, heZ, heD, _, haZ, _, haD⟩ := G.present_disjoint
  exact ⟨disjoint_union_right.mpr ⟨heZ, heD⟩, disjoint_union_right.mpr ⟨haZ, haD⟩⟩

end PairedBoundaryGeometry

/-- Construct the boundary certificate without restricting the piece sides
to be fiber-saturated. Pairwise disjoint atoms supply every graph fact. -/
theorem paired_boundary_geometry {n : ℕ} (M : FiberTreeModel ι n)
    {u v z : Finset (Fin n)} (huv : Disjoint u v) (hvz : Disjoint v z)
    (huz : Disjoint u z) {A B C : Finset ι}
    (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    PairedBoundaryGeometry A B C (M.fiberOver (betweenEdges u v))
      (M.fiberOver (betweenEdges v z)) (M.fiberOver (betweenEdges u z))
      (M.fiberOver (threeAtomInternal u v z)) := by
  have hcv : M.fiberOver (cutEdges v) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom
      (cutEdges_disjoint_internalEdges huv.symm) (cutEdges_disjoint_internalEdges_self v)
      (cutEdges_disjoint_internalEdges hvz))
  have hcu : M.fiberOver (cutEdges u) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom
      (cutEdges_disjoint_internalEdges_self u) (cutEdges_disjoint_internalEdges huv)
      (cutEdges_disjoint_internalEdges huz))
  refine ⟨?_, ?_, hAB, hAC, hBC, M.disjoint_fiberOver (bundle_disjoint huv huz), ?_, ?_⟩
  · rw [← hpart]
    exact M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  · rw [← hpart]
    exact M.fiberOver_mono (betweenEdges_subset_cutEdges_left hvz)
  · rw [← hpart]
    exact M.disjoint_fiberOver (betweenEdges_disjoint_cutEdges huv hvz.symm)
  · rw [← hpart]
    exact union_subset hcv
      ((M.fiberOver_mono (betweenEdges_subset_cutEdges_left huz)).trans hcu)

end TSPGap.Song

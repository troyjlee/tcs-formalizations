/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowFace
import TSPGap.Lemma524Indexed

/-!
# Conditional independence in Song's clean half-bundle law

The face / clean-presence / avoidance restriction is exactly the inside,
outside and union-tree conditioning used by Fact 2.8. Its positive total
mass is retained when the cross identity is normalized. No independence
of arbitrary projected piece partitions is assumed.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Unwind the clean law into the conditioning event used by Fact 2.8. -/
theorem WindowConditioningData.unwind_trees (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {u v : Finset (Fin n)} {C : Finset ι} {k : ℕ}
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C k)
    (hc : M.TwoAtomUnionData w u v) (P : Finset ι → Prop) :
    weightMass (largeBundleLaw w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C) P *
        largeBundleMass w (M.fiberOver (twoAtomInternal u v))
          (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C =
      weightMass w (fun T => P T ∧ M.nuInside u v C T ∧ M.nuOutside u v C T ∧
        InducesTreeOn (u ∪ v) (M.project T)) := by
  rw [D.unwind]
  apply weightMass_congr_of_support
  intro T hT
  let E := M.fiberOver (betweenEdges u v)
  have hsplit : ∀ S J : Finset ι,
      (T ∩ S).card = (T ∩ (S \ J)).card + (T ∩ (S ∩ J)).card := by
    intro S J
    rw [← card_inter_union_of_disjoint (disjoint_sdiff_inter S J) T, sdiff_union_inter]
  have hEC := hsplit E C
  have hC := hsplit C E
  have hCE : (T ∩ (C ∩ E)).card ≤ (T ∩ C).card :=
    card_le_card (inter_subset_inter_left inter_subset_left)
  have hECeq : (T ∩ (E ∩ C)).card = (T ∩ (C ∩ E)).card := by rw [inter_comm E C]
  change (((P T ∧ (T ∩ (C \ E)).card = 0) ∧ (T ∩ (E \ C)).card = 1) ∧
    (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) ↔
      P T ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧
        (T ∩ (C ∩ E)).card = 0) ∧ (T ∩ (C \ E)).card = 0 ∧
          InducesTreeOn (u ∪ v) (M.project T)
  constructor
  · rintro ⟨⟨⟨hP, ha⟩, hp⟩, hf⟩
    obtain ⟨hu, hv⟩ := (hc.eq_iff T hT).mp hf
    obtain ⟨he, hz⟩ := clean_present_avoid_support (hc.one_hot T hT hu hv) hp ha
    exact ⟨hP, ⟨⟨hu, hv⟩, by omega⟩, ha, (hc.union_iff T hT hu hv).mpr he⟩
  · rintro ⟨hP, ⟨⟨hu, hv⟩, hi⟩, ha, ht⟩
    have he := (hc.union_iff T hT hu hv).mp ht
    change (T ∩ E).card = 1 at he
    exact ⟨⟨⟨hP, ha⟩, by omega⟩, (hc.eq_iff T hT).mpr ⟨hu, hv⟩⟩

/-- Normalize the raw cross identity using the actual restriction mass. -/
theorem WindowConditioningData.independent (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {u v : Finset (Fin n)} {C : Finset ι} {k : ℕ}
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C k)
    (hc : M.TwoAtomUnionData w u v) {P Q : Finset ι → Prop}
    (hind : M.CondIndepAt w u v C P Q) :
    weightMass (largeBundleLaw w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C) (fun T => P T ∧ Q T) =
      weightMass (largeBundleLaw w (M.fiberOver (twoAtomInternal u v))
        (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C) P *
      weightMass (largeBundleLaw w (M.fiberOver (twoAtomInternal u v))
        (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C) Q := by
  let ν := largeBundleLaw w (M.fiberOver (twoAtomInternal u v))
    (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C
  let Z := largeBundleMass w (M.fiberOver (twoAtomInternal u v))
    (twoAtomBudget u v) (M.fiberOver (betweenEdges u v)) C
  have hZ : 0 < Z := lt_of_lt_of_le (by norm_num) D.mass_ge
  have hZeq : Z = weightMass w (fun T =>
      M.nuInside u v C T ∧ M.nuOutside u v C T ∧
        InducesTreeOn (u ∪ v) (M.project T)) := by
    have hh := D.unwind_trees M hc (fun _ => True)
    have htot : totalMass ν = 1 := D.clean.law.tot
    change weightMass ν (fun _ => True) * Z = _ at hh
    simpa only [true_and, weightMass_true, htot, one_mul] using hh
  have hid : (weightMass ν (fun T => P T ∧ Q T) * Z) * Z =
      (weightMass ν P * Z) * (weightMass ν Q * Z) := by
    rw [D.unwind_trees M hc, D.unwind_trees M hc, D.unwind_trees M hc, hZeq]
    simpa only [FiberTreeModel.CondIndepAt, and_assoc, and_left_comm, and_comm] using hind
  apply mul_right_cancel₀ (mul_ne_zero hZ.ne' hZ.ne')
  calc
    weightMass ν (fun T => P T ∧ Q T) * (Z * Z) =
        (weightMass ν (fun T => P T ∧ Q T) * Z) * Z := by ring
    _ = (weightMass ν P * Z) * (weightMass ν Q * Z) := hid
    _ = (weightMass ν P * weightMass ν Q) * (Z * Z) := by ring

end TSPGap.Song

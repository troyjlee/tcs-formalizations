/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowAssembly
import TSPGap.SongPairedProfiles

/-!
# Both original rank events from the paired non-goodness hypotheses

Apply the window at `(v,u)` with sides `(A,B,C)`, and at `(v,z)` with
sides `(B,A,C)`. The full bundles are support-complete by construction;
only their endpoint orientation needs rewriting. Four-h goodness and
the two face deficiencies remain explicit, distinct inputs.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The original rank inputs consumed by both paired profiles. No new
conditional probability premise is introduced in either orientation. -/
theorem paired_original_ranks_of_not_happy (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v z : Finset (Fin n)}
    (huv : Disjoint u v) (hvz : Disjoint v z)
    (hcu : M.TwoAtomCrossData w v u) (hcz : M.TwoAtomCrossData w v z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdefU : faceDeficiency w (M.fiberOver (twoAtomInternal v u))
      (twoAtomBudget v u) ≤ 2 * d₀)
    (hdefZ : faceDeficiency w (M.fiberOver (twoAtomInternal v z))
      (twoAtomBudget v z) ≤ 2 * d₀)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ h)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ h)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hxz : 2 ≤ expCard w (M.fiberOver (cutEdges z)) ∧
      expCard w (M.fiberOver (cutEdges z)) ≤ 2 + d₀)
    (hgoodE : 4 * h ≤ weightMass (M.tau w v u) (fun T =>
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges u)).card = 2))
    (hgoodF : 4 * h ≤ weightMass (M.tau w v z) (fun T =>
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2))
    (hnotE : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        InducesTree v (M.project T) ∧ InducesTree u (M.project T)) ≤ p)
    (hnotF : weightMass w (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧
        InducesTree v (M.project T) ∧ InducesTree z (M.project T)) ≤ p) :
    (1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card +
        (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)) ∧
    (1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card +
        (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)) := by
  have hSCU : M.SupportComplete w (M.fiberOver (betweenEdges u v)) v u := by
    rw [FiberTreeModel.SupportComplete, betweenEdges_comm v u]
    exact ⟨Subset.refl _, fun _ _ => inter_subset_right⟩
  have hSCZ : M.SupportComplete w (M.fiberOver (betweenEdges v z)) v z :=
    ⟨Subset.refl _, fun _ _ => inter_subset_right⟩
  constructor
  · exact (window_rank_of_not_happy M hw huv.symm hcu hSCU hpart hAB hAC hBC
      hdefU hxE hxA hxB hxC (by simpa only [inter_comm] using hxEB)
      hxv hxu hgoodE hnotE).2
  · exact (window_rank_of_not_happy M hw hvz hcz hSCZ
      (by simpa only [union_comm A B] using hpart) hAB.symm hBC hAC
      hdefZ hxF hxB hxA hxC (by simpa only [inter_comm] using hxFA)
      hxv hxz hgoodF hnotF).2

end TSPGap.Song

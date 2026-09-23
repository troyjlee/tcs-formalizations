/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedProbability
import TSPGap.SongPairedWindow

/-!
# Song's paired-bundle probability on the original tree law

The original rank events select one of the two verified branches. Both
branches restore the three degree-two counts and induced trees while
paying the entire conditioning mass. The final export obtains the ranks
from the two window non-goodness hypotheses. Four-h goodness remains an
explicit input; no old three-h goodness predicate is strengthened here.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The paired dichotomy and both coefficient extractions, with their
actual atom-face and prefix masses. The rank events are in the original law. -/
theorem paired_happy_of_ranks_indexed (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w (k + 1))
    {u v z : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty) (hz : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hc : M.ThreeAtomUzData w u v z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) ≤ 3 * d₀)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ h)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ h)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ h)
    (hX : 1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card +
        (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2))
    (hY : 1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card +
        (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)) :
    p < weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧
        InducesTree z (M.project T)) := by
  have H := paired_atom_law M hw hc hdef
  have HP := paired_prefixes_indexed M hw hc huv hvz huz hpart hAB hAC hBC hdef
    hxE hxF hxA hxB hxC hxEB hxFA
  have hA : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact subset_union_left.trans subset_union_left
  have hB : B ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact subset_union_right.trans subset_union_left
  have G := paired_count_geometry_indexed M huv hvz huz hA hB hAB
  rcases paired_dichotomy_indexed M hw hu hv hz huv hvz huz hc hA hB hAB hdef hX hY
    with hZ | hZ
  · apply paired_absent_probability hw.nn hw.tot H.law H.mass_pos H.unwind G HP
      hxFA hX hY hZ (fun T hT => hc.cut_z T (H.support T hT).1)
    intro T hT hface hEA hF hC hB0 hZ0 hcell
    exact paired_happy_of_raw_cells M hc huv hvz huz hpart hAB hAC hBC hT hface
      hEA hF hC hB0 hZ0 (by decide) (by decide) hcell
  · apply paired_present_probability hw.nn hw.tot H.law H.mass_pos H.unwind G HP
      H.one_z hxFA hX hY hZ
    intro T hT hface hEA hF hC hB0 hZ1 hcell
    exact paired_happy_of_raw_cells M hc huv hvz huz hpart hAB hAC hBC hT hface
      hEA hF hC hB0 hZ1 (by decide) (by decide) hcell

/-- Song's paired-bundle Lemma 21 (the 5.27 role), for arbitrary piece
sides. All graph count certificates follow from the original tree support;
all intermediate laws, means, ranks and probabilities are constructed.
The original face deficiencies and four-h goodness are explicit. -/
theorem lemma_5_27_indexed (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w (k + 1)) (htree : M.TreeSupport w)
    {u v z : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty) (hz : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) ≤ 3 * d₀)
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
    p < weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧
        InducesTree z (M.project T)) := by
  have hc := FiberTreeModel.ThreeAtomUzData.ofSupport htree hu hv hz huv hvz huz
  have hcu := FiberTreeModel.TwoAtomCrossData.ofSupport htree hv hu huv.symm
    (FiberTreeModel.ne_univ_of_disjoint_nonempty hz (disjoint_union_left.mpr ⟨hvz, huz⟩))
  have hcz := FiberTreeModel.TwoAtomCrossData.ofSupport htree hv hz hvz
    (FiberTreeModel.ne_univ_of_disjoint_nonempty hu
      (disjoint_union_left.mpr ⟨huv.symm, huz.symm⟩))
  obtain ⟨hX, hY⟩ := paired_original_ranks_of_not_happy M hw huv hvz hcu hcz hpart
    hAB hAC hBC hdefU hdefZ hxE hxF hxA hxB hxC hxEB hxFA hxu hxv hxz
    hgoodE hgoodF hnotE hnotF
  exact paired_happy_of_ranks_indexed M hw hu hv hz huv hvz huz hc hpart hAB hAC hBC
    hdef hxE hxF hxA hxB hxC hxEB hxFA hX hY

end TSPGap.Song

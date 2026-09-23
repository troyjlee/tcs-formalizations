/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527PresentIndexed

/-!
# KKO21 Lemma 5.27 over a fiber tree model

The fourth checkpoint of Lemma 5.27's port, the assembly: Eq. (56) for `e`
and for `f` (`lemma_5_27_eq56_indexed`, the second with the roles of `A` and
`B` swapped), the `Z` dichotomy (`lemma_5_27_dichotomy_indexed`), and the
two cases (`lemma_5_27_absent_indexed`, `lemma_5_27_present_indexed`).  The
pieces read the graph through three certificates, all supplied by a
transversal spanning support: `ThreeAtomUzData` at `(u, v, z)` and
`TwoAtomCrossData` at `(v, u)` and `(v, z)`.

The existing `lemma_5_27` is this theorem at the identity model
(`Lemma527.lean`, statement unchanged); the lifted-piece instance lives in
`RefinedLemma527.lean`.

`lemma_5_27_gurvits_indexed` uses the enlarged not-good threshold
`0.02ε₂²`, the PF₂ concentration defect `38ε₂`, and the unrounded
branch budgets to give fallback mass `0.0005`. It takes the same count
certificates and does not change the old public statement.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- **KKO21 Lemma 5.27 over a fiber tree model**: the assembly of the four
pieces, with the three certificates the pieces read — the three-atom
certificate with the far bundle one-hot, and the two-atom crossing
certificates at `(v, u)` and `(v, z)`. -/
theorem lemma_5_27_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hvup : v ∪ u ≠ Finset.univ) (hvzp : v ∪ z ≠ Finset.univ)
    (hcert3 : M.ThreeAtomUzData w u v z)
    (hcertE : M.TwoAtomCrossData w v u) (hcertF : M.TwoAtomCrossData w v z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef3 : faceDeficiency w (M.fiberOver (threeAtomInternal u v z)) (atomBudget u v z) ≤ 3 * εη)
    (hdefvu : faceDeficiency w (M.fiberOver (twoAtomInternal v u)) (twoAtomBudget v u) ≤ 2 * εη)
    (hdefvz : faceDeficiency w (M.fiberOver (twoAtomInternal v z)) (twoAtomBudget v z) ≤ 2 * εη)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ ε₂)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (M.fiberOver (cutEdges u))) (hdu2 : expCard w (M.fiberOver (cutEdges u)) ≤ 2 + εη)
    (hdz1 : 2 ≤ expCard w (M.fiberOver (cutEdges z))) (hdz2 : expCard w (M.fiberOver (cutEdges z)) ≤ 2 + εη)
    (hgoodE : 3 * ε₂ ≤ weightMass (M.tau w v u)
      (fun T => (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (M.tau w v z)
      (fun T => (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2))
    (hnotgoodE : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ InducesTree v (M.project T) ∧ InducesTree u (M.project T)) < 0.005 * ε₂ ^ 2)
    (hnotgoodF : weightMass w (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) < 0.005 * ε₂ ^ 2) :
    0.005 ≤ weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) := by
  -- Eq. (56) for `e`
  have h56U := lemma_5_27_eq56_indexed M hst hr hnn htot hune hvne huv hvup hcertE hpart hAB hAC hBC
    hεη hε₂ (by linarith) hεηsq hdefvu hxE hxA1 hxA2 hxB1 hxB2 hxC hxEB hdu1 hdu2 hgoodE hnotgoodE
  -- Eq. (56) for `f`, with the roles of `A` and `B` swapped
  have hpart' : M.fiberOver (cutEdges v) = (B ∪ A) ∪ C := by rw [hpart, Finset.union_comm A B]
  have hcomm : M.fiberOver (betweenEdges z v) = M.fiberOver (betweenEdges v z) := by
    rw [betweenEdges_comm z v]
  have h56W' := lemma_5_27_eq56_indexed M hst hr hnn htot hzne hvne hvz.symm hvzp hcertF hpart' hAB.symm
    hBC hAC hεη hε₂ (by linarith) hεηsq hdefvz (by rw [hcomm]; exact hxF) hxB1 hxB2 hxA1 hxA2 hxC
    (by rw [hcomm]; exact hxFA) hdz1 hdz2 hgoodF hnotgoodF
  rw [hcomm] at h56W'
  have hε' : (0 : ℝ) ≤ 27.2 * ε₂ := by positivity
  -- the dichotomy
  have hAcv : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcv : B ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  rcases lemma_5_27_dichotomy_indexed M hst hr hnn htot hune hvne hzne huv hvz huz hcert3 hAcv hBcv hAB
    hεη (by nlinarith) hε' (by linarith) hdef3 h56U h56W' with hZ | hZ
  · exact lemma_5_27_absent_indexed M hst hr hnn htot hune hvne hzne huv hvz huz hcert3 hpart hAB hAC hBC
      hεη hε₂ hε₂cap hεηsq hε' le_rfl hdef3 hxE hxF hxA1 hxA2 hxB1 hxB2 hxC hxEB hxFA h56U h56W' hZ
  · exact lemma_5_27_present_indexed M hst hr hnn htot hune hvne hzne huv hvz huz hcert3 hpart hAB hAC hBC
      hεη hε₂ hε₂cap hεηsq hε' le_rfl hdef3 hxE hxF hxA1 hxA2 hxB1 hxB2 hxC hxEB hxFA h56U h56W' hZ

/-- Lemma 5.27 at the first Gurvits probability budget: not-good means
mass below `0.02 ε₂²`, while the coherent three-atom fallback has mass
at least `0.0005`. The endpoint constant is not changed here. -/
theorem lemma_5_27_gurvits_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hvup : v ∪ u ≠ Finset.univ) (hvzp : v ∪ z ≠ Finset.univ)
    (hcert3 : M.ThreeAtomUzData w u v z)
    (hcertE : M.TwoAtomCrossData w v u) (hcertF : M.TwoAtomCrossData w v z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef3 : faceDeficiency w (M.fiberOver (threeAtomInternal u v z)) (atomBudget u v z) ≤ 3 * εη)
    (hdefvu : faceDeficiency w (M.fiberOver (twoAtomInternal v u)) (twoAtomBudget v u) ≤ 2 * εη)
    (hdefvz : faceDeficiency w (M.fiberOver (twoAtomInternal v z)) (twoAtomBudget v z) ≤ 2 * εη)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ ε₂)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (M.fiberOver (cutEdges u))) (hdu2 : expCard w (M.fiberOver (cutEdges u)) ≤ 2 + εη)
    (hdz1 : 2 ≤ expCard w (M.fiberOver (cutEdges z))) (hdz2 : expCard w (M.fiberOver (cutEdges z)) ≤ 2 + εη)
    (hgoodE : 3 * ε₂ ≤ weightMass (M.tau w v u)
      (fun T => (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (M.tau w v z)
      (fun T => (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2))
    (hnotgoodE : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ InducesTree v (M.project T) ∧ InducesTree u (M.project T)) < 0.02 * ε₂ ^ 2)
    (hnotgoodF : weightMass w (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) < 0.02 * ε₂ ^ 2) :
    0.0005 ≤ weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges z)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T)) := by
  -- Eq. (56) for `e`
  have h56U := lemma_5_27_eq56_gurvits M hst hr hnn htot hune hvne huv hvup hcertE hpart hAB hAC hBC
    hεη hε₂ (by linarith) hεηsq hdefvu hxE hxA1 hxA2 hxB1 hxB2 hxC hxEB hdu1 hdu2 hgoodE hnotgoodE
  -- Eq. (56) for `f`, with the roles of `A` and `B` swapped
  have hpart' : M.fiberOver (cutEdges v) = (B ∪ A) ∪ C := by rw [hpart, Finset.union_comm A B]
  have hcomm : M.fiberOver (betweenEdges z v) = M.fiberOver (betweenEdges v z) := by
    rw [betweenEdges_comm z v]
  have h56W' := lemma_5_27_eq56_gurvits M hst hr hnn htot hzne hvne hvz.symm hvzp hcertF hpart' hAB.symm
    hBC hAC hεη hε₂ (by linarith) hεηsq hdefvz (by rw [hcomm]; exact hxF) hxB1 hxB2 hxA1 hxA2 hxC
    (by rw [hcomm]; exact hxFA) hdz1 hdz2 hgoodF hnotgoodF
  rw [hcomm] at h56W'
  have hε' : (0 : ℝ) ≤ 38 * ε₂ := by positivity
  -- the dichotomy
  have hAcv : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcv : B ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  rcases lemma_5_27_dichotomy_indexed M hst hr hnn htot hune hvne hzne huv hvz huz hcert3 hAcv hBcv hAB
    hεη (by nlinarith) hε' (by linarith) hdef3 h56U h56W' with hZ | hZ
  · apply (lemma527_absent_budget_gurvits hε' (by linarith : 38 * ε₂ ≤ 0.0076)).trans
    exact lemma_5_27_absent_indexed_of_defect M hst hr hnn htot hune hvne hzne huv hvz huz hcert3 hpart hAB hAC hBC
      hεη hε₂ hε₂cap hεηsq hε' le_rfl hdef3 hxE hxF hxA1 hxA2 hxB1 hxB2 hxC hxEB hxFA h56U h56W' hZ
  · apply (lemma527_present_budget_gurvits hε' (by linarith : 38 * ε₂ ≤ 0.0076)).trans
    exact lemma_5_27_present_indexed_of_defect M hst hr hnn htot hune hvne hzne huv hvz huz hcert3 hpart hAB hAC hBC
      hεη hε₂ hε₂cap hεηsq hε' le_rfl hdef3 hxE hxF hxA1 hxA2 hxB1 hxB2 hxC hxEB hxFA h56U h56W' hZ

end TSPGap

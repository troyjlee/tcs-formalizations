/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527Indexed
import TSPGap.Lemma527Setup
import TSPGap.Lemma527Present

/-!
# KKO21 Lemma 5.27

Let `e = E(u,v)`, `f = E(v,z)` be two good top half edge bundles at `v`, and
`δ(v) = A ⊔ B ⊔ C` the degree partition with `x(e ∩ B), x(f ∩ A) ≤ ε₂`.  If
neither `e` nor `f` is 2-1-1 good with respect to `v` and `ε₂ ≤ 0.0002`, then
`e, f` are 2-2-2 happy with probability at least `0.005`.

The proof is the assembly of the four pieces: Eq. (56) for `e` and for `f`
(`lemma_5_27_eq56`, the second with the roles of `A` and `B` swapped), the
`Z` dichotomy (`lemma_5_27_dichotomy`), and the two cases
(`lemma_5_27_absent`, `lemma_5_27_present`).

⚠️ KKO state `0.01`; with Lemma A.1's repaired threshold (`8ε₂` instead of
`5ε₂`), Eq. (56) holds at `1 − 27.2ε₂` rather than `1 − 20ε₂`, and the
constant becomes `0.005` — still far above the `p = 0.005ε₂²` that 2-2-2
goodness (Definition 5.26) requires.

The proof lives in `Lemma527Indexed.lean`, over a fiber tree model; this file
is its instance at the **identity model**, with the statement unchanged.

The separate `lemma_5_27_gurvits` permits the larger not-good threshold
`0.02ε₂²` and gives fallback mass `0.0005`. This resolves the 5.27 gate
for the first Gurvits probability budget, not the paper's full `0.0375ε₂²`
threshold. The global thinning mass is not changed here.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- **KKO21 Lemma 5.27.** -/
theorem lemma_5_27 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hvup : v ∪ u ≠ Finset.univ) (hvzp : v ∪ z ≠ Finset.univ)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef3 : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * εη)
    (hdefvu : faceDeficiency w (twoAtomInternal v u) (twoAtomBudget v u) ≤ 2 * εη)
    (hdefvz : faceDeficiency w (twoAtomInternal v z) (twoAtomBudget v z) ≤ 2 * εη)
    (hxE : |expCard w (betweenEdges u v) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (betweenEdges v z) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (betweenEdges u v ∩ B) ≤ ε₂)
    (hxFA : expCard w (betweenEdges v z ∩ A) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (cutEdges u)) (hdu2 : expCard w (cutEdges u) ≤ 2 + εη)
    (hdz1 : 2 ≤ expCard w (cutEdges z)) (hdz2 : expCard w (cutEdges z) ≤ 2 + εη)
    (hgoodE : 3 * ε₂ ≤ weightMass (lemmaA1Tau w v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (lemmaA1Tau w v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2))
    (hnotgoodE : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges u).card = 2 ∧ InducesTree v T ∧ InducesTree u T) < 0.005 * ε₂ ^ 2)
    (hnotgoodF : weightMass w (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges z).card = 2 ∧ InducesTree v T ∧ InducesTree z T) < 0.005 * ε₂ ^ 2) :
    0.005 ≤ weightMass w (fun T =>
      (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
        ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcert3 : (FiberTreeModel.id n).ThreeAtomUzData w u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp hune hvne hzne huv hvz huz
  have hcertE : (FiberTreeModel.id n).TwoAtomCrossData w v u :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hvne hune huv.symm hvup
  have hcertF : (FiberTreeModel.id n).TwoAtomCrossData w v z :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hvne hzne hvz hvzp
  have h := lemma_5_27_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne hzne huv hvz huz
    hvup hvzp hcert3 hcertE hcertF (A := A) (B := B) (C := C)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef3)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdefvu) (by rw [FiberTreeModel.id_fiberOver]; exact hdefvz)
    (by rw [FiberTreeModel.id_fiberOver]; exact hxE) (by rw [FiberTreeModel.id_fiberOver]; exact hxF)
    hxA1 hxA2 hxB1 hxB2 hxC
    (by rw [FiberTreeModel.id_fiberOver]; exact hxEB) (by rw [FiberTreeModel.id_fiberOver]; exact hxFA)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdu1) (by rw [FiberTreeModel.id_fiberOver]; exact hdu2)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdz1) (by rw [FiberTreeModel.id_fiberOver]; exact hdz2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgoodE)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgoodF)
    (by simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using hnotgoodE)
    (by simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using hnotgoodF)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

/-- Lemma 5.27 with the increased `0.02 ε₂²` not-good threshold and
an absolute `0.0005` coherent fallback mass. -/
theorem lemma_5_27_gurvits {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hvup : v ∪ u ≠ Finset.univ) (hvzp : v ∪ z ≠ Finset.univ)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef3 : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * εη)
    (hdefvu : faceDeficiency w (twoAtomInternal v u) (twoAtomBudget v u) ≤ 2 * εη)
    (hdefvz : faceDeficiency w (twoAtomInternal v z) (twoAtomBudget v z) ≤ 2 * εη)
    (hxE : |expCard w (betweenEdges u v) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (betweenEdges v z) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (betweenEdges u v ∩ B) ≤ ε₂)
    (hxFA : expCard w (betweenEdges v z ∩ A) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (cutEdges u)) (hdu2 : expCard w (cutEdges u) ≤ 2 + εη)
    (hdz1 : 2 ≤ expCard w (cutEdges z)) (hdz2 : expCard w (cutEdges z) ≤ 2 + εη)
    (hgoodE : 3 * ε₂ ≤ weightMass (lemmaA1Tau w v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2))
    (hgoodF : 3 * ε₂ ≤ weightMass (lemmaA1Tau w v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2))
    (hnotgoodE : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges u).card = 2 ∧ InducesTree v T ∧ InducesTree u T) < 0.02 * ε₂ ^ 2)
    (hnotgoodF : weightMass w (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges z).card = 2 ∧ InducesTree v T ∧ InducesTree z T) < 0.02 * ε₂ ^ 2) :
    0.0005 ≤ weightMass w (fun T =>
      (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
        ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcert3 : (FiberTreeModel.id n).ThreeAtomUzData w u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp hune hvne hzne huv hvz huz
  have hcertE : (FiberTreeModel.id n).TwoAtomCrossData w v u :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hvne hune huv.symm hvup
  have hcertF : (FiberTreeModel.id n).TwoAtomCrossData w v z :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hvne hzne hvz hvzp
  have h := lemma_5_27_gurvits_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne hzne huv hvz huz
    hvup hvzp hcert3 hcertE hcertF (A := A) (B := B) (C := C)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef3)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdefvu) (by rw [FiberTreeModel.id_fiberOver]; exact hdefvz)
    (by rw [FiberTreeModel.id_fiberOver]; exact hxE) (by rw [FiberTreeModel.id_fiberOver]; exact hxF)
    hxA1 hxA2 hxB1 hxB2 hxC
    (by rw [FiberTreeModel.id_fiberOver]; exact hxEB) (by rw [FiberTreeModel.id_fiberOver]; exact hxFA)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdu1) (by rw [FiberTreeModel.id_fiberOver]; exact hdu2)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdz1) (by rw [FiberTreeModel.id_fiberOver]; exact hdz2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgoodE)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgoodF)
    (by simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using hnotgoodE)
    (by simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using hnotgoodF)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

end TSPGap

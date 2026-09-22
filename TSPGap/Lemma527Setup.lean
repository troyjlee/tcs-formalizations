/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527SetupIndexed
import TSPGap.LemmaA1Assembly
import TSPGap.ClaimA2
import TSPGap.Lemma527Generic
import TSPGap.Lemma517

/-!
# Lemma 5.27's two inputs: Eq. (56) and the `Z` dichotomy

**Eq. (56).**  If the half bundle `e = E(u,v)` is *not* 2-1-1 good with
respect to `v`, Lemma A.1's tail hypothesis must fail, so
`P[(δ(u)∖e)_T + (A∖e)_T ≥ 2] > 1 − 8ε₂` (our repaired threshold; KKO's is
`5ε₂`).  With the mean of that count at most `2 + 3.17ε₂ + 3ε_η` and
`E[X] ≥ 2·P[X ≥ 2] + P[X ≥ 3]`, the count is exactly `2` with probability
at least `1 − 27.2ε₂` (`lemma_5_27_eq56`; KKO: `1 − ε` with `ε = 20ε₂`).

**Claim A.2.**  Under the three-atom face `ν`, the two (56) events hold
simultaneously with probability `≥ 1 − 2.002ε'`, and on that event
`D_T + 2 Z_T = 4` for `D = (U ∖ Z) ⊔ (A ∖ e) ⊔ (W ∖ Z) ⊔ (B ∖ f)`,
`Z = E(u,z)`; `claim_A2` then gives `E_ν[Z] ≤ 3ε'` or `≥ 1 − 3ε'`
(`lemma_5_27_dichotomy`).

Both proofs live in `Lemma527SetupIndexed.lean`, over a fiber tree model; this
file is their instance at the **identity model**, with the statements unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- **Eq. (56)**: a half bundle that is not 2-1-1 good has its two-count
near-certain. -/
theorem lemma_5_27_eq56 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (hvup : v ∪ u ≠ Finset.univ)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal v u) (twoAtomBudget v u) ≤ 2 * εη)
    (hxE : |expCard w (betweenEdges u v) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (betweenEdges u v ∩ B) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (cutEdges u)) (hdu2 : expCard w (cutEdges u) ≤ 2 + εη)
    (hgood : 3 * ε₂ ≤ weightMass (lemmaA1Tau w v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2))
    (hnotgood : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges u).card = 2 ∧ InducesTree v T ∧ InducesTree u T) < 0.005 * ε₂ ^ 2) :
    1 - 27.2 * ε₂ ≤ weightMass w (fun T =>
      (T ∩ (cutEdges u \ betweenEdges u v)).card + (T ∩ (A \ betweenEdges u v)).card = 2) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcert : (FiberTreeModel.id n).TwoAtomCrossData w v u :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hvne hune huv.symm hvup
  have h := lemma_5_27_eq56_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne huv hvup hcert
    (A := A) (B := B) (C := C) (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq (by rw [FiberTreeModel.id_fiberOver]; exact hdef)
    (by rw [FiberTreeModel.id_fiberOver]; exact hxE) hxA1 hxA2 hxB1 hxB2 hxC
    (by rw [FiberTreeModel.id_fiberOver]; exact hxEB)
    (by rw [FiberTreeModel.id_fiberOver]; exact hdu1) (by rw [FiberTreeModel.id_fiberOver]; exact hdu2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgood)
    (by simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using hnotgood)
  simpa only [FiberTreeModel.id_fiberOver] using h

/-- **The `Z` dichotomy** (Claim A.2 applied): under the three-atom face,
the bundle `E(u,z)` is nearly absent or nearly present. -/
theorem lemma_5_27_dichotomy {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    {A B : Finset (Sym2 (Fin n))} (hAcv : A ⊆ cutEdges v) (hBcv : B ⊆ cutEdges v)
    (hAB : Disjoint A B)
    {εη ε' : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00001) (hε' : 0 ≤ ε') (hε'cap : ε' ≤ 1 / 15)
    (hdef : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * εη)
    (h56U : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (cutEdges u \ betweenEdges u v)).card + (T ∩ (A \ betweenEdges u v)).card = 2))
    (h56W : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (cutEdges z \ betweenEdges v z)).card + (T ∩ (B \ betweenEdges v z)).card = 2)) :
    expCard (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z))
        (betweenEdges u z) ≤ 3 * ε'
      ∨ 1 - 3 * ε' ≤ expCard (faceDist w (indicatorCost (threeAtomInternal u v z))
        (atomBudget u v z)) (betweenEdges u z) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcert : (FiberTreeModel.id n).ThreeAtomUzData w u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp hune hvne hzne huv hvz huz
  have h := lemma_5_27_dichotomy_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne hzne
    huv hvz huz hcert (A := A) (B := B) (by rw [FiberTreeModel.id_fiberOver]; exact hAcv)
    (by rw [FiberTreeModel.id_fiberOver]; exact hBcv) hAB hεη hεηcap hε' hε'cap
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef)
    (by simpa only [FiberTreeModel.id_fiberOver] using h56U)
    (by simpa only [FiberTreeModel.id_fiberOver] using h56W)
  simpa only [FiberTreeModel.id_fiberOver] using h

end TSPGap

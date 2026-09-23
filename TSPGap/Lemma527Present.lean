/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527PresentIndexed
import TSPGap.Lemma527Absent

/-!
# KKO21 Lemma 5.27, the case `E[Z_T | u, v, z trees] ≥ 1 − 3ε`

The mirror of `Lemma527Absent.lean` ("a similar proof shows…" in KKO): with
the bundle `Z = E(u,z)` nearly present, the law is

`L := ((ν | C ∪ e(B) ∪ f absent) | Z present) | e present`,

of mass `≥ 0.237`, and on its support the (56) events read `U'' + A'' = 1`,
`W'' + B'' = 1` (the present `Z` edge accounts for one unit of `δ(u)` and
of `δ(z)`).  The sandwich is the same — Corollary 2.19 at `σ` on
`(δ(u)∖e) ∪ (A∖e)` (whose count is `U'' + Z + A''`), presence lowering
`E[U'']` and `E[A'']` — with `E_σ[Z] ≥ 1 − 3ε'` replacing the `3ε'` loss;
the core runs with targets `(1, 1)` and 2-2-2 happiness reads
`δ(u)_T = U'' + Z + e = 0 + 1 + 1`, `δ(z)_T = W'' + Z + f = 1 + 1 + 0`.

The proof lives in `Lemma527PresentIndexed.lean`, over a fiber tree model; this
file keeps the base laws and is the instance at the **identity model**, with the
statement unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- The avoided set without `Z`: `C ∪ e(B) ∪ f`. -/
def l527R' (B C : Finset (Sym2 (Fin n))) (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  C ∪ (betweenEdges u v ∩ B) ∪ betweenEdges v z

/-- The face law with `C ∪ e(B) ∪ f` avoided. -/
noncomputable def l527SigmaP (w : Finset (Sym2 (Fin n)) → ℝ) (B C : Finset (Sym2 (Fin n)))
    (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  avoidDist (l527Face w u v z) (l527R' B C u v z)

/-- … with `Z` present. -/
noncomputable def l527Rho (w : Finset (Sym2 (Fin n)) → ℝ) (B C : Finset (Sym2 (Fin n)))
    (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  faceDist (l527SigmaP w B C u v z) (indicatorCost (betweenEdges u z)) 1

/-- … and `e` present: the law of the `Z`-present case. -/
noncomputable def l527LawP (w : Finset (Sym2 (Fin n)) → ℝ) (B C : Finset (Sym2 (Fin n)))
    (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  faceDist (l527Rho w B C u v z) (indicatorCost (betweenEdges u v)) 1

/-- **Lemma 5.27, the `Z`-present case.** -/
theorem lemma_5_27_present {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ ε' : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2) (hε' : 0 ≤ ε') (hε'cap : ε' ≤ 27.2 * ε₂)
    (hdef : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * εη)
    (hxE : |expCard w (betweenEdges u v) - 1 / 2| ≤ ε₂)
    (hxF : |expCard w (betweenEdges v z) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (betweenEdges u v ∩ B) ≤ ε₂)
    (hxFA : expCard w (betweenEdges v z ∩ A) ≤ ε₂)
    (h56U : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (cutEdges u \ betweenEdges u v)).card + (T ∩ (A \ betweenEdges u v)).card = 2))
    (h56W : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (cutEdges z \ betweenEdges v z)).card + (T ∩ (B \ betweenEdges v z)).card = 2))
    (hZ : 1 - 3 * ε' ≤ expCard (l527Face w u v z) (betweenEdges u z)) :
    0.005 ≤ weightMass w (fun T =>
      (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
        ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcert : (FiberTreeModel.id n).ThreeAtomUzData w u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp hune hvne hzne huv hvz huz
  have h := lemma_5_27_present_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne hzne
    huv hvz huz hcert (A := A) (B := B) (C := C)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε₂ hε₂cap hεηsq hε' hε'cap
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef)
    (by rw [FiberTreeModel.id_fiberOver]; exact hxE) (by rw [FiberTreeModel.id_fiberOver]; exact hxF)
    hxA1 hxA2 hxB1 hxB2 hxC
    (by rw [FiberTreeModel.id_fiberOver]; exact hxEB) (by rw [FiberTreeModel.id_fiberOver]; exact hxFA)
    (by simpa only [FiberTreeModel.id_fiberOver] using h56U)
    (by simpa only [FiberTreeModel.id_fiberOver] using h56W)
    (by simpa only [FiberTreeModel.tau3_id, FiberTreeModel.id_fiberOver] using hZ)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

end TSPGap

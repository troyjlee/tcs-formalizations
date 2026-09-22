/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527AbsentIndexed
import TSPGap.Lemma527Generic
import TSPGap.Lemma517
import TSPGap.Lemma524Assembly

/-!
# KKO21 Lemma 5.27, the case `E[Z_T | u, v, z trees] ≤ 3ε`

Atoms `u, v, z`, bundles `e = E(u,v)`, `f = E(v,z)` (taken as the full
between sets), the degree partition `δ(v) = A ⊔ B ⊔ C`, and
`Z := E(u,z)` the bundle between the outer atoms.  Given KKO's (56) at the
ambient law — `P[(δ(u)∖e)_T + (A∖e)_T = 2] ≥ 1 − ε'` and the symmetric
statement for `(δ(z)∖f, B∖f)` — and `E_ν[Z] ≤ 3ε'` under the three-atom
face `ν`, the law

`L := (ν | Z ∪ C ∪ e(B) ∪ f absent) | e present`

has mass `≥ 0.241`, and under it the four inputs of `lemma_5_27_core` hold
with `U'' = δ(u) ∖ (e ∪ Z)`, `A'' = A ∖ (e ∪ f)`, `W'' = δ(z) ∖ (f ∪ Z)`,
`B'' = B ∖ (f ∪ e)` and targets `(2, 2)`:

* the two count events transfer with `δ_L = 4.15ε'` (cross-multiplied);
* `E_L[A''] ∈ [0.41, 0.57]` and `E_L[B''] ≤ 0.57` by the **sandwich**: at
  `σ` (after the avoid step) Corollary 2.19 caps `E_σ[U'' ∪ A'']` at
  `2 + 3.6δ_σ`, avoiding raises `E[U'']`, so `E_σ[A'']` rises by at most
  `3.6δ_σ + 2δ_ν + 3ε'` (KKO's "35ε"); presence of `e` lowers both
  `E[U'']` and `E[A'']`, and the same sandwich at `L` bounds the drop of
  `E[A'']` by `2δ_L + 3.6δ_σ`.

The core gives `P_L[A'' = 1, B'' = 0, U'' = 1, W'' = 2] ≥ 0.068 − 2δ_L`,
and on `L`'s support that event is 2-2-2 happiness:
`δ(u)_T = U'' + Z + e = 1 + 0 + 1`, `δ(v)_T = (A'' + e(A) + f(A)) + (B'' + …)
+ C = (1 + 1 + 0) + 0 + 0`, `δ(z)_T = W'' + Z + f = 2 + 0 + 0`.  Unwinding
the three conditionings gives `≥ (0.068 − 8.3ε')·0.241 ≥ 0.005` for
`ε' ≤ 27.2 ε₂`, `ε₂ ≤ 0.0002`.

The proof lives in `Lemma527AbsentIndexed.lean`, over a fiber tree model; this
file keeps the base laws and is the instance at the **identity model**, with the
statement unchanged.
-/

namespace TSPGap
open Finset


variable {n : ℕ}

/-- The avoided set of Lemma 5.27: `Z ∪ C ∪ e(B) ∪ f`. -/
def l527R (B C : Finset (Sym2 (Fin n))) (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  betweenEdges u z ∪ C ∪ (betweenEdges u v ∩ B) ∪ betweenEdges v z

/-- The three-atom face law. -/
noncomputable def l527Face (w : Finset (Sym2 (Fin n)) → ℝ) (u v z : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) → ℝ :=
  faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)

/-- The face law with `Z ∪ C ∪ e(B) ∪ f` avoided. -/
noncomputable def l527Sigma (w : Finset (Sym2 (Fin n)) → ℝ) (B C : Finset (Sym2 (Fin n)))
    (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  avoidDist (l527Face w u v z) (l527R B C u v z)

/-- The law `E` of Lemma 5.27: additionally `e` present. -/
noncomputable def l527Law (w : Finset (Sym2 (Fin n)) → ℝ) (B C : Finset (Sym2 (Fin n)))
    (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  faceDist (l527Sigma w B C u v z) (indicatorCost (betweenEdges u v)) 1

/-- The three-atom face law of the identity model is `l527Face`. -/
theorem FiberTreeModel.tau3_id {w : Finset (Sym2 (Fin n)) → ℝ} (u v z : Finset (Fin n)) :
    (FiberTreeModel.id n).tau3 w u v z = l527Face w u v z := by
  simp [FiberTreeModel.tau3, l527Face]

/-- **Lemma 5.27, the `Z`-absent case.** -/
theorem lemma_5_27_absent {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
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
    (hZ : expCard (l527Face w u v z) (betweenEdges u z) ≤ 3 * ε') :
    0.005 ≤ weightMass w (fun T =>
      (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
        ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcert : (FiberTreeModel.id n).ThreeAtomUzData w u v z :=
    FiberTreeModel.ThreeAtomUzData.ofSupport hsupp hune hvne hzne huv hvz huz
  have h := lemma_5_27_absent_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne hzne
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

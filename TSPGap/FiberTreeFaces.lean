/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeSupport
import TSPGap.LawPackage
import TSPGap.NestedLaw

/-!
# Faces on a fiber tree model: the setup certificates

The §5 chains start from a stable fixed-rank normalized weight and one
maximal face — the two-atom face of Lemma A.1 (`u`, `v` trees) or the
three-atom face — and then condition by avoiding and presenting.  All of the
probability in that setup is generic in the coordinate type; the only graph
input is a handful of **counts read on the support**: the face count is at
most the budget, it equals the budget exactly when the atoms induce trees, a
spanning tree crosses a nonempty proper atom, and a tree in which both atoms
are trees holds at most one bundle edge.  This file separates the two:

* `FaceLawData` — the generic face package (mass, law, support, outside
  transfer, unwinding), built from the count bound alone;
* `TwoAtomFaceData` — the two-atom face package on a model, the exact shape
  of `TwoAtomTauData` that Lemma 5.21's chain consumes.

The support certificates themselves (`TreeSupport`, `TwoAtomCountData`,
`ThreeAtomCountData`, the one-hot extensions) live below the §5 chain in
`FiberTreeSupport.lean`; this file needs `LawData` and so sits above it.

A §5 lemma over a model takes the certificate for its ambient weight; every
count it needs on a conditioned law's support comes back through the
support inclusion.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The generic face package -/

/-- **The face package of a weight**: the maximal face of `F` at budget `m`,
with its mass, its law, its support, the outside marginal transfer and the
unwinding identity.  `twoAtomTauData`'s shape, with the count bound abstract. -/
structure FaceLawData (w : Finset ι → ℝ) (F : Finset ι) (m r : ℕ) (εη : ℝ) : Prop where
  mass : 0 < totalMass (faceWeight w (indicatorCost F) m)
  massGe : 1 - 2 * εη ≤ totalMass (faceWeight w (indicatorCost F) m)
  law : LawData (faceDist w (indicatorCost F) m) r
  supp : ∀ T, faceDist w (indicatorCost F) m T ≠ 0 → w T ≠ 0 ∧ (T ∩ F).card = m
  transfer : ∀ S : Finset ι, S ⊆ Fᶜ →
    |expCard (faceDist w (indicatorCost F) m) S - expCard w S| ≤ 2 * εη
  unwind : ∀ P : Finset ι → Prop,
    weightMass (faceDist w (indicatorCost F) m) P * totalMass (faceWeight w (indicatorCost F) m)
      = weightMass w (fun T => P T ∧ (T ∩ F).card = m)

/-- **Constructing the face package** from the ambient package and the count
bound on the support. -/
theorem faceLawData {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {F : Finset ι} {m : ℕ} (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m)
    {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.001)
    (hdef : faceDeficiency w F m ≤ 2 * εη) : FaceLawData w F m r εη := by
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w (indicatorCost F) m) := by linarith
  have hnorm := fixedRankNormalized_faceDist (r := r) hr hnn hmass
  refine ⟨hmass, by linarith, ?_, fun T hT => ?_,
    fun S hS => le_trans (abs_expCard_faceDist_sub_le hst hr hnn htot hsup hmass hS) hdef,
    fun P => ?_⟩
  · exact
      { st := isRealStable_genPoly_maxFaceDist hst hr hnn hsup hmass
        rank := fun S hS => by by_contra hc; exact hS (hnorm.supported S hc)
        nn := hnorm.nonneg
        tot := hnorm.total }
  · have h := faceDist_ne_zero_imp hT
    rw [setCost_indicatorCost] at h
    exact h
  · rw [weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_face]

namespace FiberTreeModel

variable (M : FiberTreeModel ι n)

/-! ### The two-atom face law on a model -/

/-- **The two-atom face law** on the model: `u`, `v` induce trees in the
projection. -/
noncomputable def tau (w : Finset ι → ℝ) (u v : Finset (Fin n)) : Finset ι → ℝ :=
  faceDist w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)

/-- **The two-atom face package on a model**: `TwoAtomTauData`'s exact shape,
with the support read as "both atoms induce trees in the projection". -/
structure TwoAtomFaceData (w : Finset ι → ℝ) (k : ℕ) (u v : Finset (Fin n)) (εη : ℝ) :
    Prop where
  mass : 0 < totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v)))
    (twoAtomBudget u v))
  massGe : 1 - 2 * εη ≤ totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v)))
    (twoAtomBudget u v))
  law : LawData (M.tau w u v) (k + 1)
  supp : ∀ T, M.tau w u v T ≠ 0 →
    w T ≠ 0 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)
  transfer : ∀ S : Finset ι, S ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ →
    |expCard (M.tau w u v) S - expCard w S| ≤ 2 * εη
  unwind : ∀ P : Finset ι → Prop,
    weightMass (M.tau w u v) P
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v)))
            (twoAtomBudget u v))
      = weightMass w (fun T => P T ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)

/-- **Constructing the two-atom face package** from the ambient package and
the two-atom count certificate. -/
theorem twoAtomFaceData {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hcount : M.TwoAtomCountData w u v)
    {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.001)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη) :
    M.TwoAtomFaceData w k u v εη := by
  have F := faceLawData hst hr hnn htot hcount.le hεη hεηcap hdef
  exact ⟨F.mass, F.massGe, F.law, fun T hT => ⟨(F.supp T hT).1,
    (hcount.eq_iff T (F.supp T hT).1).mp (F.supp T hT).2⟩, F.transfer, F.unwind⟩

end FiberTreeModel

end TSPGap

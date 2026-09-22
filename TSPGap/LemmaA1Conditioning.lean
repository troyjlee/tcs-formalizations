/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TwoAtomFace

/-!
# The conditioned law for KKO21 Lemma A.1

Lemma A.1 conditions in three stages:

1. `lemmaA1Tau` is the maximum face on the internal edges of two atoms, so
   both atoms induce trees;
2. `lemmaA1Sigma` conditions `lemmaA1Tau` on avoiding the negligible cell
   `C`;
3. `lemmaA1Nu` conditions `lemmaA1Sigma` on the bundle `E` being present.

The first and third stages are maximum faces and the middle stage is a
cylinder face.  Consequently the final law is fixed-rank normalized and real
stable using the existing face, avoidance, and one-hot present APIs.  No
product decomposition or independence theorem is needed.

## Main results

* `lemmaA1Tau_support` identifies the support of the two-atom face.
* `lemmaA1Sigma_support` records what survives the avoidance conditioning.
* `lemmaA1Sigma_oneHot` supplies the maximum-face hypothesis for presenting
  the bundle.
* `lemmaA1Nu_fixedRankNormalized_stable` packages normalization and real
  stability of the fully conditioned law.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### The three conditioned laws -/

/-- The law after conditioning the two atoms to induce trees. -/
noncomputable def lemmaA1Tau (w : Finset (Sym2 (Fin n)) → ℝ)
    (u v : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  faceDist w (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v)

/-- The two-atom law further conditioned on avoiding `C`. -/
noncomputable def lemmaA1Sigma (w : Finset (Sym2 (Fin n)) → ℝ)
    (u v : Finset (Fin n)) (C : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) → ℝ :=
  avoidDist (lemmaA1Tau w u v) C

/-- The Lemma A.1 law: two atom trees, `C` avoided, and one bundle edge present. -/
noncomputable def lemmaA1Nu (w : Finset (Sym2 (Fin n)) → ℝ)
    (u v : Finset (Fin n)) (C E : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) → ℝ :=
  faceDist (lemmaA1Sigma w u v C) (indicatorCost E) 1

/-! ### Support of the intermediate laws -/

/-- A nonzero atom of `lemmaA1Tau` is a nonzero atom of the original weight,
is a spanning tree, and induces trees on both atoms. -/
theorem lemmaA1Tau_support {w : Finset (Sym2 (Fin n)) → ℝ}
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) {T : Finset (Sym2 (Fin n))}
    (hT : lemmaA1Tau w u v T ≠ 0) :
    w T ≠ 0 ∧ IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T := by
  have hface := faceDist_ne_zero hT
  rw [faceWeight_indicatorCost_apply] at hface
  have hcard : (T ∩ twoAtomInternal u v).card = twoAtomBudget u v := by
    by_contra hc
    exact hface (by rw [if_neg hc])
  have hwT : w T ≠ 0 := fun hc => hface (by rw [if_pos hcard, hc])
  have hspan := htree T hwT
  obtain ⟨hu, hv⟩ :=
    (card_inter_twoAtom_eq_iff hspan hune hvne huv).mp hcard
  exact ⟨hwT, hspan, hu.2, hv.2⟩

/-- Avoidance preserves support in `lemmaA1Tau` and forces the avoided count
to zero. -/
theorem lemmaA1Sigma_support {w : Finset (Sym2 (Fin n)) → ℝ}
    {u v : Finset (Fin n)} {C : Finset (Sym2 (Fin n))}
    {T : Finset (Sym2 (Fin n))} (hT : lemmaA1Sigma w u v C T ≠ 0) :
    lemmaA1Tau w u v T ≠ 0 ∧ (T ∩ C).card = 0 := by
  have hav : avoidWeight (lemmaA1Tau w u v) C T ≠ 0 := by
    intro hc
    exact hT (by rw [lemmaA1Sigma, avoidDist, hc, zero_div])
  have hcard : (T ∩ C).card = 0 := by
    by_contra hc
    exact hav (by rw [avoidWeight_apply, if_neg hc])
  have hτ : lemmaA1Tau w u v T ≠ 0 := fun hc =>
    hav (by rw [avoidWeight_apply, if_pos hcard, hc])
  exact ⟨hτ, hcard⟩

/-- On `lemmaA1Sigma` the bundle is one-hot: avoiding `C` only restricts the
two-atom face, and a spanning tree whose endpoint atoms induce trees contains
at most one edge between them. -/
theorem lemmaA1Sigma_oneHot {w : Finset (Sym2 (Fin n)) → ℝ}
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) {C E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ betweenEdges u v) {T : Finset (Sym2 (Fin n))}
    (hT : lemmaA1Sigma w u v C T ≠ 0) :
    (T ∩ E).card ≤ 1 := by
  have hτ := (lemmaA1Sigma_support hT).1
  obtain ⟨_, hspan, hu, hv⟩ := lemmaA1Tau_support htree hune hvne huv hτ
  exact card_inter_bundle_le_one hspan hu hv huv hE

/-! ### Stability and normalization -/

/-- **The conditioned law used by Lemma A.1 is fixed-rank normalized and
strongly Rayleigh.**

The three strict mass hypotheses are stated at the raw weights consumed by
the corresponding normalization APIs.  They are normally supplied together
by the lower bound on the full conditioning event. -/
theorem lemmaA1Nu_fixedRankNormalized_stable
    {w : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) {C E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ betweenEdges u v)
    (hτmass : 0 < totalMass (faceWeight w
      (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v)))
    (hσmass : 0 < totalMass (avoidWeight (lemmaA1Tau w u v) C))
    (hνmass : 0 < totalMass (presentWeight (lemmaA1Sigma w u v C) E)) :
    FixedRankNormalized r (lemmaA1Nu w u v C E)
      ∧ IsRealStable (genPoly (lemmaA1Nu w u v C E)) := by
  have hsup : ∀ T, w T ≠ 0 →
      (T ∩ twoAtomInternal u v).card ≤ twoAtomBudget u v := fun T hT =>
    card_inter_twoAtom_le (htree T hT) hune hvne huv
  have hτnorm : FixedRankNormalized r (lemmaA1Tau w u v) :=
    fixedRankNormalized_faceDist hr hnn hτmass
  have hτst : IsRealStable (genPoly (lemmaA1Tau w u v)) :=
    isRealStable_genPoly_maxFaceDist hst hr hnn hsup hτmass
  have hτrank : FixedRankWeight r (lemmaA1Tau w u v) := by
    intro T hT
    by_contra hc
    exact hT (hτnorm.supported T hc)
  have hσnorm : FixedRankNormalized r (lemmaA1Sigma w u v C) :=
    fixedRankNormalized_avoidDist hτrank hτnorm.nonneg hσmass
  have hσst : IsRealStable (genPoly (lemmaA1Sigma w u v C)) :=
    isRealStable_genPoly_avoidDist hτst hτrank hτnorm.nonneg hσmass
  have hσrank : FixedRankWeight r (lemmaA1Sigma w u v C) := by
    intro T hT
    by_contra hc
    exact hT (hσnorm.supported T hc)
  have hone : ∀ T, lemmaA1Sigma w u v C T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => lemmaA1Sigma_oneHot htree hune hvne huv hE hT
  have hνface : 0 < totalMass
      (faceWeight (lemmaA1Sigma w u v C) (indicatorCost E) 1) := by
    simpa only [presentWeight] using hνmass
  have hνnorm : FixedRankNormalized r (lemmaA1Nu w u v C E) :=
    fixedRankNormalized_faceDist hσrank hσnorm.nonneg hνface
  have hνst : IsRealStable (genPoly (lemmaA1Nu w u v C E)) :=
    isRealStable_genPoly_presentDist hσst hσrank hσnorm.nonneg hone hνmass
  exact ⟨hνnorm, hνst⟩

end TSPGap

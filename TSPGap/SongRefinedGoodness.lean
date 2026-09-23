/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongGoodness
import TSPGap.SongRefinedPaired
import TSPGap.RefinedTheorem528

/-!
# Goodness on fiber models and Song's paired producer

The goodness policy transfers exactly to the actual lifted law. The adjacent
bundle result and the paired producer can therefore consume Song-good bundles
without separate four-h probability hypotheses. Partition sides in the paired
producer remain arbitrary piece sets; its common mass and fallback constants
are unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

namespace BundleGoodnessPolicy

/-- The same goodness policy on a fiber model, with the original LP window. -/
def IsGoodIndexed (P : BundleGoodnessPolicy) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) (x : Sym2 (Fin n) → ℝ) (w : Finset ι → ℝ)
    (u v : Finset (Fin n)) : Prop :=
  ¬ IsHalfBundle x P.halfWidth u v ∨ P.twoTwoThreshold ≤ weightMass (M.tau w u v)
    (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
      (T ∩ M.fiberOver (cutEdges v)).card = 2)

theorem mass_of_goodIndexed_of_half {P : BundleGoodnessPolicy}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : FiberTreeModel ι n}
    {w : Finset ι → ℝ} {u v : Finset (Fin n)}
    (hg : P.IsGoodIndexed M x w u v) (hh : IsHalfBundle x P.halfWidth u v) :
    P.twoTwoThreshold ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2) :=
  hg.resolve_left fun hn => hn hh

end BundleGoodnessPolicy

variable {D : Finset (Sym2 (Fin n))} {eps : ℝ}

/-- Refinement preserves the whole policy, including its half window. -/
theorem EdgeRefinement.isGoodIndexed_liftProb_iff (R : EdgeRefinement x D eps)
    (P : BundleGoodnessPolicy) (μ : TreeDist n x) (u v : Finset (Fin n)) :
    P.IsGoodIndexed R.model x (R.liftProb μ) u v ↔ P.IsGood μ u v := by
  unfold BundleGoodnessPolicy.IsGoodIndexed
  simp only [R.model_fiberOver]
  rw [R.weightMass_tau_liftProb_twoTwo]
  rfl

namespace Song

/-- The conditional probability consumed by piece-native §5 producers. -/
theorem mass_liftProb_of_good (R : EdgeRefinement x D eps) {μ : TreeDist n x}
    {u v : Finset (Fin n)} (hg : goodness.IsGood μ u v) (hh : IsHalfBundle x h u v) :
    4 * h ≤ weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2) := by
  rw [R.weightMass_tau_liftProb_twoTwo]
  exact BundleGoodnessPolicy.mass_of_good_of_half hg hh

/-- The adjacent-half-bundle probability bound is unchanged on pieces. -/
theorem lemma_5_17_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (R : EdgeRefinement x D eps) {S u v z : Finset (Fin n)} (hu : IsChildOf H.cuts u S)
    (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h) :
    (4 * h < weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2)) ∨
    (4 * h < weightMass (R.model.tau (R.liftProb μ) v z)
      (fun T => (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2)) := by
  rw [R.weightMass_tau_liftProb_twoTwo, R.weightMass_tau_liftProb_twoTwo]
  exact lemma_5_17 hx μ hμ H hu hv hz huv hvz huz heta hcap hxE hxF

/-- At least one of two adjacent bundles is good in the lifted law. -/
theorem adjacent_good_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (R : EdgeRefinement x D eps) {S u v z : Finset (Fin n)} (hu : IsChildOf H.cuts u S)
    (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    goodness.IsGoodIndexed R.model x (R.liftProb μ) u v ∨
      goodness.IsGoodIndexed R.model x (R.liftProb μ) v z := by
  rw [R.isGoodIndexed_liftProb_iff, R.isGoodIndexed_liftProb_iff]
  exact adjacent_good hx μ hμ H hu hv hz huv hvz huz heta hcap

/-- The paired producer consumes Song-good bundles at the unchanged half window. -/
theorem lemma_5_27_liftProb_of_good {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D eps) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    (hxEB : ∑ q ∈ R.piecesOver (betweenEdges u v) ∩ B, R.weight q ≤ h)
    (hxFA : ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h)
    (hgoodE : goodness.IsGood μ v u)
    (hgoodF : goodness.IsGood μ v z)
    (hnotE : weightMass (R.liftProb μ) (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree u (R.project T)) ≤ p)
    (hnotF : weightMass (R.liftProb μ) (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree z (R.project T)) ≤ p) :
    p < weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  have hhalfE : IsHalfBundle x h v u := by
    change |pairSum x v u - 1 / 2| ≤ h
    rw [pairSum_comm]
    exact hxE
  exact lemma_5_27_liftProb hx μ hμ H heta hcap R hu hv hz huv hvz huz
    hpart hAB hAC hBC hxE hxF hxA hxB hxC hxEB hxFA
    (mass_liftProb_of_good R hgoodE hhalfE) (mass_liftProb_of_good R hgoodF hxF) hnotE hnotF

end Song
end TSPGap

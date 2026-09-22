/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedBundle
import TSPGap.RefinedSection5Setup
import TSPGap.RefinedHappyEvents

/-!
# The paired probability for hierarchy children on pieces

The existing triple data supplies the face deficiencies, cut means and
tree support. Partition sides remain arbitrary piece sets. Four-h
goodness is measured in the specified two-atom faces and is not inferred
from the old goodness policy. The conclusion supplies Song's common mass;
it does not change either of the older absolute fallback constants.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- Song's paired-bundle probability for the actual lifted max-entropy law.
Only original partition weights and goodness/non-goodness hypotheses remain;
the conditioning and count-certificate inputs are all derived. -/
theorem lemma_5_27_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
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
    (hgoodE : 4 * h ≤ weightMass (R.model.tau (R.liftProb μ) v u) (fun T =>
      (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2))
    (hgoodF : 4 * h ≤ weightMass (R.model.tau (R.liftProb μ) v z) (fun T =>
      (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2))
    (hnotE : weightMass (R.liftProb μ) (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree u (R.project T)) ≤ p)
    (hnotF : weightMass (R.liftProb μ) (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree z (R.project T)) ≤ p) :
    p < weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  classical
  have T0 := H.tripleData hx μ hμ hu hv hz huv hvz huz
  have T := R.refinedTripleData hμ T0
  have hw : LawData (R.liftProb μ) (n - 2 + 1) :=
    ⟨T.uv.stable, T.uv.rank, R.liftProb_weightNonneg μ, R.liftProb_totalMass μ⟩
  have hh := lemma_5_27_indexed R.model hw (R.treeSupport_liftProb μ)
    T0.uv.une T0.uv.vne T0.vz.vne T0.uv.disj T0.vz.disj T0.uz.disj
    (A := A) (B := B) (C := C) (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC
    (by rw [R.model_fiberOver]; linarith only [T.deficiency3, hcap, heta])
    (by rw [R.model_fiberOver, twoAtomInternal_comm v u, twoAtomBudget_comm v u]
        linarith only [T.uv.deficiency, hcap, heta])
    (by rw [R.model_fiberOver]; linarith only [T.vz.deficiency, hcap, heta])
    (by rw [R.model_fiberOver, T.uv.bundle]; exact hxE)
    (by rw [R.model_fiberOver, T.vz.bundle]; exact hxF)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact ⟨hxA.1, by linarith only [hxA.2, hcap]⟩)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact ⟨hxB.1, by linarith only [hxB.2, hcap]⟩)
    (by rw [R.expCard_liftProb_eq_sum_weight]; linarith only [hxC, hcap])
    (by rw [R.model_fiberOver, R.expCard_liftProb_eq_sum_weight]; exact hxEB)
    (by rw [R.model_fiberOver, R.expCard_liftProb_eq_sum_weight]; exact hxFA)
    (by rw [R.model_fiberOver]; exact ⟨T.uv.du1, by linarith only [T.uv.du2, hcap]⟩)
    (by rw [R.model_fiberOver]; exact ⟨T.uv.dv1, by linarith only [T.uv.dv2, hcap]⟩)
    (by rw [R.model_fiberOver]; exact ⟨T.vz.dv1, by linarith only [T.vz.dv2, hcap]⟩)
    (by simpa only [R.model_fiberOver] using hgoodE)
    (by simpa only [R.model_fiberOver] using hgoodF)
    (by simpa only [R.model_fiberOver, R.model_project] using hnotE)
    (by simpa only [R.model_fiberOver, R.model_project] using hnotF)
  unfold EdgeRefinement.TwoTwoTwoHappyOn
  simpa only [R.model_fiberOver, R.model_project] using hh

end TSPGap.Song

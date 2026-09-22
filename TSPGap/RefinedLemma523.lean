/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedSection5Setup
import TSPGap.RefinedHappyEvents

/-!
# KKO21 Lemma 5.23's tail layer on pieces

The lifted-piece instance of `lemma_5_23_indexed`: for three children `u, v, z`
of a hierarchy cut with the two bundles off the middle atom near `½`, and a
piece set `A` over `δ(v)` whose part outside both bundles is tiny, one of the
two bundles satisfies Lemma A.1's tail hypothesis under the lifted law.  The
side `A` is an arbitrary piece set; the bundles are the full piece bundles.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- **Lemma 5.23's tail layer for the lifted law, with a piece side.** -/
theorem lemma_5_23_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges v))
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0005)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε₂) (hxF : |pairSum x v z - 1 / 2| ≤ ε₂)
    (hD : ∑ p ∈ (A \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z),
      R.weight p ≤ 0.00201) :
    (0.02 : ℝ) ≤ weightMass (R.liftProb μ) (fun Ť =>
        (Ť ∩ (A \ R.piecesOver (betweenEdges u v))).card
          + (Ť ∩ (R.piecesOver (cutEdges u) \ R.piecesOver (betweenEdges u v))).card ≤ 1)
    ∨ (0.02 : ℝ) ≤ weightMass (R.liftProb μ) (fun Ť =>
        (Ť ∩ (A \ R.piecesOver (betweenEdges v z))).card
          + (Ť ∩ (R.piecesOver (cutEdges z) \ R.piecesOver (betweenEdges v z))).card ≤ 1) := by
  have T := R.refinedTripleData hμ (H.tripleData hx μ hμ hu hv hz huv hvz huz)
  have hsmall : ε₂ + 3 * εη ≤ 1 / 1000 := by linarith
  have h24 := R.eqTwentyFourAlt_liftProb hx μ hμ H hu hv hz huv hvz huz hεη hε₂ hxE hxF hsmall
  have h := lemma_5_23_indexed R.model T.uv.stable T.uv.rank (R.liftProb_weightNonneg μ)
    (R.liftProb_totalMass μ) T.uv.une T.uv.vne T.vz.vne T.uv.disj T.vz.disj T.uz.disj T.count
    (E := R.piecesOver (betweenEdges u v)) (F := R.piecesOver (betweenEdges v z)) (A := A)
    (by simp only [R.model_fiberOver, Finset.Subset.refl])
    (by simp only [R.model_fiberOver, Finset.Subset.refl])
    (by rw [R.model_fiberOver]; exact hA) hεη hε₂ hεηcap hε₂cap
    (by rw [R.model_fiberOver]; linarith [T.deficiency3])
    (by rw [T.uv.bundle]; exact hxE) (by rw [T.vz.bundle]; exact hxF)
    (by rw [R.model_fiberOver]; exact T.uv.du2) (by rw [R.model_fiberOver]; exact T.vz.dv2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hD) h24
  simpa only [R.model_fiberOver] using h

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedTreeFace
import TSPGap.RefinedCondIndepTransport

/-!
# Fact 2.8 at the piece tree face

The two exports step 2 promised its consumers, at the max-entropy limit:

* `EdgeRefinement.refinedTreeFace_indep` — under the lifted law conditioned on
  `S` inducing a tree (`refinedTreeFace`), an inside-determined piece event and
  an outside-determined piece event are independent.  The piece analogue of
  `treeFace_indep`, with the *same* positivity hypothesis on the base face.
* `IsMaxEntropyLimit.refinedCondIndep_conditioned` — the conditioned cross
  identity of `Lemma524Independence.lean`, on pieces.

Both are `IsMaxEntropyLimit.refinedTreeCondIndep` unwound through
`refinedTreeFace_unwind`; nothing about the limit is used beyond base
Fact 2.8.
-/

namespace TSPGap.EdgeRefinement

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- **Fact 2.8 at the piece tree face**: inside and outside piece events are
independent under the lifted law conditioned on `S` inducing a tree. -/
theorem refinedTreeFace_indep (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)}
    (hSne : S.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    {A B : Finset R.Piece → Prop} (hA : R.RefinedInsideDetermined S A)
    (hB : R.RefinedOutsideDetermined S B) :
    weightMass (R.refinedTreeFace (R.liftProb μ) S) (fun Ť => A Ť ∧ B Ť)
      = weightMass (R.refinedTreeFace (R.liftProb μ) S) A
        * weightMass (R.refinedTreeFace (R.liftProb μ) S) B := by
  have hfact := hμ.refinedTreeCondIndep R S A B hA hB
  unfold RefinedCondIndepCross at hfact
  -- the four unwindings
  have hAB := R.refinedTreeFace_unwind μ hSne hmass (fun Ť => A Ť ∧ B Ť)
  have hA' := R.refinedTreeFace_unwind μ hSne hmass A
  have hB' := R.refinedTreeFace_unwind μ hSne hmass B
  have hC : totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
      = weightMass (R.liftProb μ) (R.RefinedInducesTreeOn S) := by
    have := R.refinedTreeFace_unwind μ hSne hmass (fun _ => True)
    rw [weightMass_true, R.totalMass_refinedTreeFace μ hmass, one_mul] at this
    rw [this]
    exact weightMass_congr fun Ť => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have hassoc : weightMass (R.liftProb μ) (fun Ť => A Ť ∧ B Ť ∧ R.RefinedInducesTreeOn S Ť)
      = weightMass (R.liftProb μ)
          (fun Ť => (fun Ť' => A Ť' ∧ B Ť') Ť ∧ R.RefinedInducesTreeOn S Ť) :=
    weightMass_congr fun Ť => ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  rw [hassoc, ← hAB, ← hA', ← hB', ← hC] at hfact
  refine mul_right_cancel₀ (mul_pos hmass hmass).ne' ?_
  linear_combination hfact

end TSPGap.EdgeRefinement

namespace TSPGap

/-- **The conditioned cross identity on pieces, at the max-entropy limit.** -/
theorem IsMaxEntropyLimit.refinedCondIndep_conditioned {n : ℕ} {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ} (R : EdgeRefinement x D ε₁) (S : Finset (Fin n))
    {Kin A Kout B : Finset R.Piece → Prop}
    (hKin : R.RefinedInsideDetermined S Kin) (hA : R.RefinedInsideDetermined S A)
    (hKout : R.RefinedOutsideDetermined S Kout) (hB : R.RefinedOutsideDetermined S B) :
    weightMass (R.liftProb μ)
          (fun Ť => (Kin Ť ∧ A Ť) ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť)
        * weightMass (R.liftProb μ) (fun Ť => Kin Ť ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť)
      = weightMass (R.liftProb μ)
          (fun Ť => (Kin Ť ∧ A Ť) ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť)
        * weightMass (R.liftProb μ)
          (fun Ť => Kin Ť ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť) :=
  R.refinedCondIndep_conditioned (R.liftProb_weightNonneg μ) (hμ.refinedTreeCondIndep R) S
    hKin hA hKout hB

end TSPGap

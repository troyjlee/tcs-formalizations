/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RectangularTransfer
import TSPGap.RefinedTreeFaceIndep
import TSPGap.RefinedHappyEvents
import TSPGap.RefinedSection5Setup

/-!
# What rectangularity buys, on pieces

The piece analogue of `RectangularTransfer.lean`, and the first file of the §7
piece zone.  `IsRectangularAtOn u E` says `E Ť ↔ InducesTree u (project Ť) ∧ Q Ť`
with `Q` reading only the pieces outside `u`; conditioning the lifted law on
such an `E` leaves it inside `u` exactly where conditioning on the tree event
of `u` leaves it — the piece Fact 2.8 (`refinedTreeFace_indep`).

Exports, in the shape the piece claims consume:

* the factorization `W(E ∧ A ∧ B) = W_face(A) · W(E ∧ B)` for `A` inside- and
  `B` outside-determined at `u` in the piece sense
  (`IsRectangularAtOn.weightMass_factor`), its `B = True` case, and the
  transfer of an inside bound through a uniform thinning of the lifted law
  (`thin_weightMass_le`, `thin_expCard_le`);
* **the face-mass transport**: the piece tree face of the lifted law is the
  lift of the base tree face, so a count event over a fiber-saturated set —
  `Q (Ť ∩ piecesOver F).card` — and an expected count over `piecesOver F`
  have the same value at the piece face as at the base face
  (`weightMass_refinedTreeFace_count`, `expCard_refinedTreeFace_piecesOver`).
  This is what lets the claims keep their parity and mean bounds on the base
  face while factoring against a piece event.

⚠️ On the lifted law's support the tree event of `u` in the projection is the
refined tree event (`inducesTree_project_iff_of_support`); off the support
the two differ, so the conversion is done once, inside the factorization.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### The support conversion -/

/-- On the lifted law's support, inducing a tree on `u` in the projection **is**
the refined tree event of `u`. -/
theorem inducesTree_project_iff_of_support (μ : TreeDist n x) {u : Finset (Fin n)}
    {Ť : Finset R.Piece} (h : R.liftProb μ Ť ≠ 0) :
    InducesTree u (R.project Ť) ↔ R.RefinedInducesTreeOn u Ť :=
  ⟨fun h' => ⟨(R.liftProb_ne_zero μ h).1, (R.liftProb_ne_zero μ h).2.1, h'⟩, fun h' => h'.2.2⟩

/-! ### The face-mass transport -/

/-- **A count event over a fiber-saturated set has the same mass at the piece
face as at the base face.** -/
theorem weightMass_refinedTreeFace_count (μ : TreeDist n x) (u : Finset (Fin n))
    (F : Finset (Sym2 (Fin n))) (Q : ℕ → Prop) :
    weightMass (R.refinedTreeFace (R.liftProb μ) u) (fun Ť => Q (Ť ∩ R.piecesOver F).card)
      = weightMass (treeFace μ.prob u) (fun T => Q (T ∩ F).card) := by
  rw [R.refinedTreeFace_liftProb, ← R.weightMass_liftWeight_project (w := treeFace μ.prob u)
    (weightSupportedOn_faceDist μ.weightSupportedOn_edgeFinset _ _) (fun T => Q (T ∩ F).card)]
  exact weightMass_congr_of_support fun Ť h => by
    rw [R.card_inter_piecesOver_of_transversal (R.liftWeight_ne_zero h).1]

/-- **A projected event has the same mass at the piece face as at the base face.** -/
theorem weightMass_refinedTreeFace_project (μ : TreeDist n x) (u : Finset (Fin n))
    (A : Finset (Sym2 (Fin n)) → Prop) :
    weightMass (R.refinedTreeFace (R.liftProb μ) u) (fun Ť => A (R.project Ť))
      = weightMass (treeFace μ.prob u) A := by
  rw [R.refinedTreeFace_liftProb]
  exact R.weightMass_liftWeight_project (w := treeFace μ.prob u)
    (weightSupportedOn_faceDist μ.weightSupportedOn_edgeFinset _ _) A

/-- **An expected count over a fiber-saturated set has the same value at the
piece face as at the base face.** -/
theorem expCard_refinedTreeFace_piecesOver (μ : TreeDist n x) (u : Finset (Fin n))
    (F : Finset (Sym2 (Fin n))) :
    expCard (R.refinedTreeFace (R.liftProb μ) u) (R.piecesOver F)
      = expCard (treeFace μ.prob u) F := by
  rw [R.refinedTreeFace_liftProb]
  exact R.expCard_liftWeight (w := treeFace μ.prob u)
    (weightSupportedOn_faceDist μ.weightSupportedOn_edgeFinset _ _) F

variable {R}

/-! ### The factorization -/

set_option maxHeartbeats 400000 in
-- four `weightMass` unwindings plus the piece Fact 2.8 in one chain
/-- **Inside-event mass factorization through a piece-rectangular event.**  For
`A` inside-determined and `B` outside-determined at `u` in the piece sense,
conditioning the lifted law on a rectangular `E` factors the inside part off at
the piece tree face. -/
theorem IsRectangularAtOn.weightMass_factor (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn u E)
    {A : Finset R.Piece → Prop} (hA : R.RefinedInsideDetermined u A)
    {B : Finset R.Piece → Prop} (hB : R.RefinedOutsideDetermined u B) :
    weightMass (R.liftProb μ) (fun Ť => E Ť ∧ A Ť ∧ B Ť)
      = weightMass (R.refinedTreeFace (R.liftProb μ) u) A
        * weightMass (R.liftProb μ) (fun Ť => E Ť ∧ B Ť) := by
  classical
  obtain ⟨Q, hQ, hEQ⟩ := hE
  have hsupp : ∀ Ť, R.liftProb μ Ť ≠ 0 → (E Ť ↔ (Q Ť ∧ R.RefinedInducesTreeOn u Ť)) := by
    intro Ť hŤ
    rw [hEQ Ť, R.inducesTree_project_iff_of_support μ hŤ]
    tauto
  have h1 : weightMass (R.liftProb μ) (fun Ť => E Ť ∧ A Ť ∧ B Ť)
      = weightMass (R.liftProb μ) (fun Ť => (A Ť ∧ (Q Ť ∧ B Ť)) ∧ R.RefinedInducesTreeOn u Ť) := by
    refine weightMass_congr_of_support fun Ť hŤ => ?_
    rw [hsupp Ť hŤ]
    tauto
  have h2 : weightMass (R.liftProb μ) (fun Ť => E Ť ∧ B Ť)
      = weightMass (R.liftProb μ) (fun Ť => (Q Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn u Ť) := by
    refine weightMass_congr_of_support fun Ť hŤ => ?_
    rw [hsupp Ť hŤ]
    tauto
  have hu1 := R.refinedTreeFace_unwind μ hune hmass (fun Ť => A Ť ∧ (Q Ť ∧ B Ť))
  have hu2 := R.refinedTreeFace_unwind μ hune hmass (fun Ť => Q Ť ∧ B Ť)
  rw [h1, h2, ← hu1, ← hu2, R.refinedTreeFace_indep μ hμ hune hmass hA (hQ.and hB)]
  ring

/-- The `B = True` case: the inside event's face mass factors off outright. -/
theorem IsRectangularAtOn.weightMass_factor' (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn u E)
    {A : Finset R.Piece → Prop} (hA : R.RefinedInsideDetermined u A) :
    weightMass (R.liftProb μ) (fun Ť => E Ť ∧ A Ť)
      = weightMass (R.refinedTreeFace (R.liftProb μ) u) A * weightMass (R.liftProb μ) E := by
  have h := hE.weightMass_factor μ hμ hune hmass hA
    (B := fun _ => True) (fun _ _ _ => Iff.rfl)
  rw [weightMass_congr (A := fun Ť => E Ť ∧ A Ť ∧ True) (B := fun Ť => E Ť ∧ A Ť)
      (fun Ť => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, trivial⟩⟩)] at h
  rw [weightMass_congr (A := fun Ť => E Ť ∧ True) (B := E)
      (fun Ť => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)] at h
  exact h

/-! ### Transfer through a uniform thinning of the lifted law -/

/-- **An inside bound at the piece tree face transfers to any uniform thinning
of the lifted law over a piece-rectangular event.**  Zero-safe. -/
theorem IsRectangularAtOn.thin_weightMass_le (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn u E)
    {v : Finset R.Piece → ℝ} {p : ℝ} (hv : IsUniformThinning (R.liftProb μ) v E p)
    {A : Finset R.Piece → Prop} (hA : R.RefinedInsideDetermined u A)
    {c : ℝ} (h : weightMass (R.refinedTreeFace (R.liftProb μ) u) A ≤ c) :
    weightMass v A ≤ p * c := by
  refine hv.weightMass_le (R.liftProb_weightNonneg μ) ?_
  rw [hE.weightMass_factor' μ hμ hune hmass hA]
  exact mul_le_mul_of_nonneg_right h (weightMass_nonneg (R.liftProb_weightNonneg μ) E)

/-- **Inside `expCard` transfer**: a mean bound at the piece tree face, over
pieces whose base edges lie inside `u`, becomes a mean bound at the thinning. -/
theorem IsRectangularAtOn.thin_expCard_le (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn u E)
    {v : Finset R.Piece → ℝ} {p : ℝ} (hv : IsUniformThinning (R.liftProb μ) v E p)
    {Dp : Finset R.Piece} (hD : ∀ q ∈ Dp, ∀ w ∈ R.base q, w ∈ u)
    {c : ℝ} (h : expCard (R.refinedTreeFace (R.liftProb μ) u) Dp ≤ c) :
    expCard v Dp ≤ p * c := by
  classical
  have hp0 : 0 ≤ p := by rw [← hv.total]; exact totalMass_nonneg hv.nonneg
  rw [expCard_eq_sum_marginal]
  calc ∑ q ∈ Dp, weightMass v (fun Ť => q ∈ Ť)
      ≤ ∑ q ∈ Dp, p * weightMass (R.refinedTreeFace (R.liftProb μ) u) (fun Ť => q ∈ Ť) :=
        Finset.sum_le_sum fun q hq => hE.thin_weightMass_le μ hμ hune hmass hv
          (R.refinedInsideDetermined_mem (hD q hq)) le_rfl
    _ = p * expCard (R.refinedTreeFace (R.liftProb μ) u) Dp := by
        rw [expCard_eq_sum_marginal, Finset.mul_sum]
    _ ≤ p * c := mul_le_mul_of_nonneg_left h hp0

end EdgeRefinement

end TSPGap

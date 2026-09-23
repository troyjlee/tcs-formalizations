/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonEvent
import TSPGap.Lemma524Independence

/-!
# KKO21 Corollary 5.9: the max-flow event leaves the inside law alone

KKO split the conditioned law as `ν = ν_S × ν_{G/S}` (Lemma 2.23) and define
`E_S` on the contracted factor alone, so that conditioning on `E_S` does not
touch `ν_S`.  **No product measure is built here.**  The same content comes
out of two facts already in the development:

* **Fact 2.8** (`IsMaxEntropyLimit.treeCondIndep`): conditioned on `S`
  inducing a tree, an inside-determined event and an outside-determined event
  are independent.  `treeFace_indep` states that at the tree-face law and
  `polygonLaw_indep` carries it through the further conditioning on `C_T = 0`
  (which is itself outside-determined, `partC ⊆ δ(S)`).
* **The master identity** (`weightMass_selectedWeight`): the mass a selected
  subweight gives an event splits over the pair cells, and a pair cell of two
  subsets of `δ(S)` is outside-determined (`outsideDetermined_pairCell`).

Together: for every inside-determined `P`,

`W_base(P) = W_ν(P) · totalMass base`   (`weightMass_selected_inside`)

— the inside law under the max-flow event is the inside law under `ν` — and
more generally inside and outside stay independent under `base`
(`weightMass_selected_cross`).  That is Corollary 5.9 in the form Corollaries
5.10 and 5.11 consume, and it is what lets the Bernoulli-sum machinery
(`exists_bernoulli_rank_law`, which needs a *stable* law) be applied to `ν`
rather than to the flow-derived subweight, which has no stability.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Determinacy combinators -/

/-- Avoiding a set of cut edges is outside-determined.  (`OutsideDetermined.and`
and `eventMass_eq_weightMass` are already in `Lemma524Independence`.) -/
theorem outsideDetermined_avoid {S : Finset (Fin n)} {D : Finset (Sym2 (Fin n))}
    (hD : D ⊆ cutEdges S) : OutsideDetermined S (fun T => (T ∩ D).card = 0) :=
  outsideDetermined_inter (fun e he => not_forall_mem_of_mem_cutEdges (hD he))
    (fun X => X.card = 0)

/-- A pair cell of two sets of cut edges is outside-determined. -/
theorem outsideDetermined_pairCell {S : Finset (Fin n)} {A B : Finset (Sym2 (Fin n))}
    (hA : A ⊆ cutEdges S) (hB : B ⊆ cutEdges S) (e f : Sym2 (Fin n)) :
    OutsideDetermined S (PairCell A B e f) :=
  OutsideDetermined.and
    (outsideDetermined_inter (fun g hg => not_forall_mem_of_mem_cutEdges (hA hg))
      (fun X => X = {e}))
    (outsideDetermined_inter (fun g hg => not_forall_mem_of_mem_cutEdges (hB hg))
      (fun X => X = {f}))

/-! ### Independence at the tree face -/

/-- The tree-face event, read as `InducesTreeOn`. -/
theorem treeFace_unwind (μ : TreeDist n x) {S : Finset (Fin n)} (hSne : S.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    (P : Finset (Sym2 (Fin n)) → Prop) :
    weightMass (treeFace μ.prob S) P
        * totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
      = weightMass μ.prob (fun T => P T ∧ InducesTreeOn S T) := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hSne
  rw [show treeFace μ.prob S
      = faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1) from rfl,
    weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_face]
  refine weightMass_congr_of_support fun T hT => ?_
  have hT' := μ.support_spanningTree T hT
  constructor
  · rintro ⟨hP, hc⟩
    refine ⟨hP, (inducesTreeOn_iff_card hT' S).mpr ?_⟩
    rw [Finset.inter_comm] at hc
    omega
  · rintro ⟨hP, hc⟩
    refine ⟨hP, ?_⟩
    have := (inducesTreeOn_iff_card hT' S).mp hc
    rw [Finset.inter_comm]
    omega

/-- **Fact 2.8 at the tree face**: inside and outside events are independent
under the law conditioned on `S` inducing a tree. -/
theorem treeFace_indep (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)}
    (hSne : S.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    {A B : Finset (Sym2 (Fin n)) → Prop} (hA : InsideDetermined S A)
    (hB : OutsideDetermined S B) :
    weightMass (treeFace μ.prob S) (fun T => A T ∧ B T)
      = weightMass (treeFace μ.prob S) A * weightMass (treeFace μ.prob S) B := by
  have hfact := hμ.treeCondIndep S A B hA hB
  unfold CondIndepCross at hfact
  simp only [eventMass_eq_weightMass] at hfact
  -- the four unwindings
  have hAB := treeFace_unwind μ hSne hmass (fun T => A T ∧ B T)
  have hA' := treeFace_unwind μ hSne hmass A
  have hB' := treeFace_unwind μ hSne hmass B
  have hC : totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
      = weightMass μ.prob (InducesTreeOn S) := by
    have := treeFace_unwind μ hSne hmass (fun _ => True)
    rw [show weightMass (treeFace μ.prob S) (fun _ => True)
        = totalMass (treeFace μ.prob S) from weightMass_true _] at this
    rw [show totalMass (treeFace μ.prob S) = 1 from
      (fixedRankNormalized_faceDist (r := n - 1) μ.fixedRankWeight μ.weightNonneg hmass).total,
      one_mul] at this
    rw [this]
    exact weightMass_congr fun T => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have hassoc : weightMass μ.prob (fun T => A T ∧ B T ∧ InducesTreeOn S T)
      = weightMass μ.prob (fun T => (fun T' => A T' ∧ B T') T ∧ InducesTreeOn S T) :=
    weightMass_congr fun T => ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  rw [hassoc, ← hAB, ← hA', ← hB', ← hC] at hfact
  refine mul_right_cancel₀ (mul_pos hmass hmass).ne' ?_
  linear_combination hfact

/-! ### Independence at the polygon law -/

/-- Under the polygon law, inside-determined masses agree with the tree-face
law's. -/
theorem polygonLaw_inside (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {S : Finset (Fin n)} {C : Finset (Sym2 (Fin n))} (hSne : S.Nonempty)
    (hC : C ⊆ cutEdges S)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    (hmass₂ : 0 < totalMass (avoidWeight (treeFace μ.prob S) C))
    {A : Finset (Sym2 (Fin n)) → Prop} (hA : InsideDetermined S A) :
    weightMass (polygonLaw μ S C) A = weightMass (treeFace μ.prob S) A := by
  have hkey := treeFace_indep μ hμ hSne hmass hA (outsideDetermined_avoid hC)
  have hunw : weightMass (polygonLaw μ S C) A * totalMass (avoidWeight (treeFace μ.prob S) C)
      = weightMass (treeFace μ.prob S) (fun T => A T ∧ (T ∩ C).card = 0) :=
    weightMass_avoidDist_mul hmass₂ A
  have hmC : totalMass (avoidWeight (treeFace μ.prob S) C)
      = weightMass (treeFace μ.prob S) (fun T => (T ∩ C).card = 0) :=
    totalMass_avoidWeight _ _
  rw [hkey, ← hmC] at hunw
  exact mul_right_cancel₀ hmass₂.ne' hunw

/-- **Independence under the polygon law.** -/
theorem polygonLaw_indep (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {S : Finset (Fin n)} {C : Finset (Sym2 (Fin n))} (hSne : S.Nonempty)
    (hC : C ⊆ cutEdges S)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    (hmass₂ : 0 < totalMass (avoidWeight (treeFace μ.prob S) C))
    {A B : Finset (Sym2 (Fin n)) → Prop} (hA : InsideDetermined S A)
    (hB : OutsideDetermined S B) :
    weightMass (polygonLaw μ S C) (fun T => A T ∧ B T)
      = weightMass (polygonLaw μ S C) A * weightMass (polygonLaw μ S C) B := by
  have hBC : OutsideDetermined S (fun T => B T ∧ (T ∩ C).card = 0) :=
    hB.and (outsideDetermined_avoid hC)
  have hkey := treeFace_indep μ hμ hSne hmass hA hBC
  have h1 : weightMass (polygonLaw μ S C) (fun T => A T ∧ B T)
      * totalMass (avoidWeight (treeFace μ.prob S) C)
      = weightMass (treeFace μ.prob S) (fun T => (A T ∧ B T) ∧ (T ∩ C).card = 0) :=
    weightMass_avoidDist_mul hmass₂ _
  have h2 : weightMass (polygonLaw μ S C) B * totalMass (avoidWeight (treeFace μ.prob S) C)
      = weightMass (treeFace μ.prob S) (fun T => B T ∧ (T ∩ C).card = 0) :=
    weightMass_avoidDist_mul hmass₂ B
  have hre : weightMass (treeFace μ.prob S) (fun T => (A T ∧ B T) ∧ (T ∩ C).card = 0)
      = weightMass (treeFace μ.prob S) (fun T => A T ∧ (B T ∧ (T ∩ C).card = 0)) :=
    weightMass_congr fun T => ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  rw [hre, hkey, ← h2, ← polygonLaw_inside μ hμ hSne hC hmass hmass₂ hA] at h1
  exact mul_right_cancel₀ hmass₂.ne' (by linear_combination h1)

/-! ### The selected subweight -/

/-- **Corollary 5.9 for the inside**: the max-flow selection does not change
the inside law. -/
theorem weightMass_selected_inside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Finset ι → ℝ) (A B : Finset ι) (z : ↥A → ↥B → ℝ) (P : Finset ι → Prop)
    (hindep : ∀ e f, weightMass w (fun T => P T ∧ PairCell A B e f T)
      = weightMass w P * weightMass w (PairCell A B e f)) :
    weightMass (selectedWeight w A B z) P
      = weightMass w P * totalMass (selectedWeight w A B z) := by
  classical
  rw [weightMass_selectedWeight, ← weightMass_true (selectedWeight w A B z),
    weightMass_selectedWeight]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hindep ↑e ↑f]
  have hcell : weightMass w (fun T => True ∧ PairCell A B ↑e ↑f T)
      = weightMass w (PairCell A B ↑e ↑f) :=
    weightMass_congr fun T => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [hcell]
  ring

/-- **Corollary 5.9, cross form**: the inside factor of a mixed event is the
inside factor under `ν`, the outside factor stays under the selection.  This is
what Corollary 5.10's two-term split consumes. -/
theorem weightMass_selected_cross {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Finset ι → ℝ) (A B : Finset ι) (z : ↥A → ↥B → ℝ) (P Q : Finset ι → Prop)
    (hindep : ∀ e f, weightMass w (fun T => P T ∧ (Q T ∧ PairCell A B e f T))
      = weightMass w P * weightMass w (fun T => Q T ∧ PairCell A B e f T)) :
    weightMass (selectedWeight w A B z) (fun T => P T ∧ Q T)
      = weightMass w P * weightMass (selectedWeight w A B z) Q := by
  classical
  rw [weightMass_selectedWeight, weightMass_selectedWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hre : weightMass w (fun T => (P T ∧ Q T) ∧ PairCell A B ↑e ↑f T)
      = weightMass w (fun T => P T ∧ (Q T ∧ PairCell A B ↑e ↑f T)) :=
    weightMass_congr fun T => ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  rw [hre, hindep ↑e ↑f]
  ring

end TSPGap

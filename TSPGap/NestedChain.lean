/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NestedLaw
import TSPGap.MatchingSetup
import TSPGap.Lemma524Independence
import TSPGap.Lemma517

/-!
# The conditioned law of KKO21 Lemma 5.16

For a child `u` of a cut `S` with `x(δ↑(u)) ≥ 1/2 + 9ε₂`, a second child `v`,
and `W := S ∖ u`, the **nested law** `ν := μ | u, v, W, S trees` is the
maximum face of the multiplicity cost (`NestedFace.lean`).  This file exports
what Lemma 5.16's analytic kernel consumes (`NestedData`):

* the face mass, at least `1/2 + 9ε₂ − 5ε_η/2` (the deficiency is exact:
  `Σ_X (x(δ(X))/2 − 1)`, and `x(δ(W)) = x(δ(S)) + x(δ(u)) − 2x(δ↑(u))`);
* the law package (stability by the negated-cost trick), the support (four
  tree events on spanning trees), and unwinding;
* `E_ν[δ↑(u)] ∈ [x(δ↑(u)) − ε_η/2, x(δ↑(u))]`: 🔑 `δ↑(u)` lies outside every
  face set, so the stagewise transfer would lose the `≈ 1/2` deficiency of
  `W`; instead **Fact 2.8** makes the nested law and the `S`-tree law agree on
  outside-determined events (`nestedLaw_outside`), and the `S` face moves an
  outside mean by at most `ε_η/2`;
* `E_ν[δ(v)] ∈ [3/2 + 9ε₂ − 9ε_η/2, 5/2 − 9ε₂ + 4ε_η]`: the nested law is the
  four-stage chain `S`, `u`, `v`, `W` of tree-face conditionings
  (`faceDist_faceDist`), `δ(v)` is split inside/outside at the `S` and `W`
  stages and lies outside `E(u)`, `E(v)`, and each stage moves it by at most
  that stage's deficiency; the deficiencies are tracked along the chain with
  `MaxFace`'s bounds (inside means only go up, outside means drop by at most
  the deficiency).
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- Conditioning an atom to induce a tree. -/
noncomputable def treeFace (ν : Finset (Sym2 (Fin n)) → ℝ) (X : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) → ℝ :=
  faceDist ν (indicatorCost (internalEdges X)) (X.card - 1)

/-- **The nested law** `μ | u, v, W, S trees`. -/
noncomputable def nestedLaw (μ : TreeDist n x) (u v W S : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) → ℝ :=
  faceDist μ.prob (nestedCost u v W S) (nestedBudget u v W S)

/-! ### Deficiencies at a tree law -/

/-- The deficiency of an atom's tree face at a tree law: `x(δ(X))/2 − 1`. -/
theorem faceDeficiency_internal_eq {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) {X : Finset (Fin n)} (hX : X.Nonempty) (hX0 : AvoidsRootEdge e₀ X) :
    faceDeficiency μ.prob (internalEdges X) (X.card - 1) = cutSum x X / 2 - 1 := by
  have h1 : 1 ≤ X.card := Finset.card_pos.mpr hX
  rw [faceDeficiency, expCard_prob_internalEdges, sum_internalEdges_eq_of_avoids hx hX0]
  push_cast [Nat.cast_sub h1]
  ring

/-- `x(δ(S ∖ u)) = x(δ(S)) + x(δ(u)) − 2 x(δ↑(u))`. -/
theorem cutSum_sdiff_eq_upSum (x : Sym2 (Fin n) → ℝ) {S u : Finset (Fin n)} (huS : u ⊆ S) :
    cutSum x (S \ u) = cutSum x S + cutSum x u - 2 * upSum x S u :=
  cutSum_sdiff_of_subset x huS

/-! ### Fact 2.8 for the nested law -/

/-- An edge with an endpoint outside `S` is an outside-determined event. -/
theorem outsideDetermined_mem {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (he : ¬ ∀ v ∈ e, v ∈ S) : OutsideDetermined S (fun T => e ∈ T) := by
  classical
  have h := outsideDetermined_inter (S := S) (D := {e}) (fun e' he' => by
    rw [Finset.mem_singleton] at he'; rw [he']; exact he) (fun X => e ∈ X)
  intro T T' hTT'
  have := h T T' hTT'
  simpa [Finset.mem_inter] using this

theorem not_forall_mem_of_mem_cutEdges {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (he : e ∈ cutEdges S) : ¬ ∀ v ∈ e, v ∈ S := by
  obtain ⟨a, -, b, hb, rfl⟩ := mem_cutEdges_iff''.mp he
  intro h
  exact (Finset.mem_compl.mp hb) (h b (Sym2.mem_mk_right a b))

/-- **Fact 2.8**: the nested law and the `S`-tree law agree on
outside-determined events — the extra conditioning on `u`, `v`, `W` is
inside `S`. -/
theorem nestedLaw_outside (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u v W S : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hWne : W.Nonempty)
    (hSne : S.Nonempty) (huS : u ⊆ S) (hvS : v ⊆ S) (hWS : W ⊆ S)
    (hmass : 0 < totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S)))
    (hM₁ : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    {B : Finset (Sym2 (Fin n)) → Prop} (hB : OutsideDetermined S B) :
    weightMass (nestedLaw μ u v W S) B = weightMass (treeFace μ.prob S) B := by
  classical
  set A : Finset (Sym2 (Fin n)) → Prop :=
    fun T => InducesTree u T ∧ InducesTree v T ∧ InducesTree W T with hA
  have hAin : InsideDetermined S A :=
    (insideDetermined_inducesTree huS).and
      ((insideDetermined_inducesTree hvS).and (insideDetermined_inducesTree hWS))
  have hci := hμ.treeCondIndep S A B hAin hB
  unfold CondIndepCross at hci
  simp only [eventMass_eq_weightMass] at hci
  -- the nested face is `A ∧ C` on the support
  have hface : ∀ T, μ.prob T ≠ 0 →
      (setCost (nestedCost u v W S) T = nestedBudget u v W S ↔ A T ∧ InducesTreeOn S T) := by
    intro T hT
    have hsp := μ.support_spanningTree T hT
    rw [setCost_nestedCost_eq_iff hsp hune hvne hWne hSne]
    unfold InducesTreeOn
    constructor
    · rintro ⟨⟨-, hu⟩, ⟨-, hv⟩, ⟨-, hW⟩, hS⟩; exact ⟨⟨hu, hv, hW⟩, hS⟩
    · rintro ⟨⟨hu, hv, hW⟩, hS⟩; exact ⟨⟨hsp, hu⟩, ⟨hsp, hv⟩, ⟨hsp, hW⟩, hS⟩
  have hfaceS : ∀ T, μ.prob T ≠ 0 →
      ((T ∩ internalEdges S).card = S.card - 1 ↔ InducesTreeOn S T) := by
    intro T hT
    rw [inducesTreeOn_iff_card (μ.support_spanningTree T hT), Finset.inter_comm]
    have := card_internal_inter_add_one_le (μ.support_spanningTree T hT) hSne
    omega
  -- the four masses
  have e1 : weightMass (nestedLaw μ u v W S) B
      = weightMass μ.prob (fun T => A T ∧ B T ∧ InducesTreeOn S T)
        / weightMass μ.prob (fun T => A T ∧ InducesTreeOn S T) := by
    unfold nestedLaw
    rw [weightMass_faceDist, weightMass_faceWeight, totalMass_faceWeight]
    congr 1
    · exact weightMass_congr_of_support fun T hT => by rw [hface T hT]; tauto
    · exact weightMass_congr_of_support fun T hT => hface T hT
  have e2 : weightMass (treeFace μ.prob S) B
      = weightMass μ.prob (fun T => B T ∧ InducesTreeOn S T)
        / weightMass μ.prob (InducesTreeOn S) := by
    unfold treeFace
    rw [weightMass_faceDist, weightMass_face, totalMass_face]
    congr 1
    · exact weightMass_congr_of_support fun T hT => by rw [hfaceS T hT]
    · exact weightMass_congr_of_support fun T hT => hfaceS T hT
  have hden1 : weightMass μ.prob (fun T => A T ∧ InducesTreeOn S T) ≠ 0 := by
    have : totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S))
        = weightMass μ.prob (fun T => A T ∧ InducesTreeOn S T) := by
      rw [totalMass_faceWeight]
      exact weightMass_congr_of_support fun T hT => hface T hT
    rw [← this]; exact hmass.ne'
  have hden2 : weightMass μ.prob (InducesTreeOn S) ≠ 0 := by
    have : totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
        = weightMass μ.prob (InducesTreeOn S) := by
      rw [totalMass_face]
      exact weightMass_congr_of_support fun T hT => hfaceS T hT
    rw [← this]; exact hM₁.ne'
  rw [e1, e2, div_eq_div_iff hden1 hden2]
  linarith [hci]

/-! ### The package -/

/-- **The data of the nested law** that Lemma 5.16's kernel consumes. -/
structure NestedData (μ : TreeDist n x) (r : ℕ) (u v W S : Finset (Fin n)) (ε₂ εη : ℝ) :
    Prop where
  mass : 0 < totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S))
  massGe : 1 / 2 + 9 * ε₂ - 5 / 2 * εη
    ≤ totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S))
  law : LawData (nestedLaw μ u v W S) r
  supp : ∀ T, nestedLaw μ u v W S T ≠ 0 → μ.prob T ≠ 0 ∧ IsSpanningTree n T
    ∧ InducesTreeOn u T ∧ InducesTreeOn v T ∧ InducesTreeOn W T ∧ InducesTreeOn S T
  up_ge : upSum x S u - εη / 2 ≤ expCard (nestedLaw μ u v W S) (upEdges S u)
  up_le : expCard (nestedLaw μ u v W S) (upEdges S u) ≤ upSum x S u
  cutv_ge : 3 / 2 + 9 * ε₂ - 9 / 2 * εη ≤ expCard (nestedLaw μ u v W S) (cutEdges v)
  cutv_le : expCard (nestedLaw μ u v W S) (cutEdges v) ≤ 5 / 2 - 9 * ε₂ + 4 * εη
  unwind : ∀ P : Finset (Sym2 (Fin n)) → Prop,
    weightMass (nestedLaw μ u v W S) P
        * totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S))
      = weightMass μ.prob (fun T => P T ∧ setCost (nestedCost u v W S) T = nestedBudget u v W S)

/-- **The nested data with an absolute hierarchy-error bound.** The construction
needs no upper bound on `ε₂`; the older square-error interface is a corollary. -/
theorem Hierarchy.nestedData_of_small_error {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : IsChildOf H.cuts u S)
    (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {ε₂ : ℝ} (_hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hεηcap : εη ≤ 0.00000004)
    (hup : 1 / 2 + 9 * ε₂ ≤ upSum x S u) :
    NestedData μ (n - 2 + 1) u v (S \ u) S ε₂ εη := by
  classical
  set W := S \ u with hW
  -- the geometry
  have hune := H.child_nonempty hu
  have hvne := H.child_nonempty hv
  have hSne := (H.nearMin S hS).nonempty
  have huS := H.child_subset hu
  have hvS := H.child_subset hv
  have hduv := H.children_disjoint hu hv huv
  have hvW : v ⊆ W := fun a ha =>
    Finset.mem_sdiff.mpr ⟨hvS ha, fun hau => Finset.disjoint_left.mp hduv hau ha⟩
  have hWne : W.Nonempty := hvne.mono hvW
  have hWS : W ⊆ S := Finset.sdiff_subset
  have hduW : Disjoint u W := Finset.disjoint_sdiff
  -- the LP facts
  have hcS := (H.nearMin S hS).cut_le
  have hcS2 := H.two_le_cutSum hx hS
  have hcu := (H.child_nearMin hu).cut_le
  have hcv := (H.child_nearMin hv).cut_le
  have hcv2 := H.child_two_le_cutSum hx hv
  have hS0 := H.avoids S hS
  have hu0 := H.child_avoids hu
  have hv0 := H.child_avoids hv
  have hW0 : AvoidsRootEdge e₀ W := hS0.mono hWS
  have hcW : cutSum x W ≤ 3 - 18 * ε₂ + 2 * εη := by
    rw [hW, cutSum_sdiff_eq_upSum x huS]; linarith
  -- the base law
  have hnn := μ.weightNonneg
  have htot := totalMass_treeDist μ
  have hst := hμ.treeRealStable
  have hrank := fixedRankWeight_prob_succ μ hune hvne hduv
  have htree := μ.support_spanningTree
  have L₀ : TreeLawData μ.prob (n - 2 + 1) := ⟨⟨hst, hrank, hnn, htot⟩, htree⟩
  -- the deficiencies at `μ`
  have qS := faceDeficiency_internal_eq hx μ hSne hS0
  have qu := faceDeficiency_internal_eq hx μ hune hu0
  have qv := faceDeficiency_internal_eq hx μ hvne hv0
  have qW := faceDeficiency_internal_eq hx μ hWne hW0
  /- ### The nested face directly: mass, law, support, unwinding -/
  have hsup : ∀ T, μ.prob T ≠ 0 → setCost (nestedCost u v W S) T ≤ nestedBudget u v W S :=
    fun T hT => setCost_nestedCost_le (htree T hT) hune hvne hWne hSne
  have hmassGe : 1 / 2 + 9 * ε₂ - 5 / 2 * εη
      ≤ totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S)) := by
    have h := one_sub_costDeficiency_le_faceMass hnn htot hsup
    rw [costDeficiency_nested_eq hx μ hune hvne hWne hSne hu0 hv0 hW0 hS0] at h
    linarith
  have hmass : 0 < totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S)) := by
    linarith
  have hlaw : LawData (nestedLaw μ u v W S) (n - 2 + 1) :=
    { st := isRealStable_genPoly_faceDist_max hst hrank hnn (nestedCost_le_four u v W S) hsup hmass
      rank := fun T hT => by
        by_contra hc
        exact hT ((fixedRankNormalized_faceDist (r := n - 2 + 1) hrank hnn hmass).supported T hc)
      nn := (fixedRankNormalized_faceDist (r := n - 2 + 1) hrank hnn hmass).nonneg
      tot := (fixedRankNormalized_faceDist (r := n - 2 + 1) hrank hnn hmass).total }
  have hsupp : ∀ T, nestedLaw μ u v W S T ≠ 0 → μ.prob T ≠ 0 ∧ IsSpanningTree n T
      ∧ InducesTreeOn u T ∧ InducesTreeOn v T ∧ InducesTreeOn W T ∧ InducesTreeOn S T := by
    intro T hT
    obtain ⟨hμT, hc⟩ := faceDist_ne_zero_imp hT
    have hsp := htree T hμT
    obtain ⟨h1, h2, h3, h4⟩ := (setCost_nestedCost_eq_iff hsp hune hvne hWne hSne).mp hc
    exact ⟨hμT, hsp, h1, h2, h3, h4⟩
  have hunwind : ∀ P : Finset (Sym2 (Fin n)) → Prop,
      weightMass (nestedLaw μ u v W S) P
          * totalMass (faceWeight μ.prob (nestedCost u v W S) (nestedBudget u v W S))
        = weightMass μ.prob (fun T => P T ∧ setCost (nestedCost u v W S) T
          = nestedBudget u v W S) := by
    intro P
    unfold nestedLaw
    rw [weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_faceWeight]
  /- ### Stage 1: `S` a tree -/
  have hsup1 := L₀.face_sup hSne
  have hM₁ : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) := by
    have := L₀.law.face_mass_ge hsup1; linarith
  set L₁ := faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1) with hL₁
  have D₁ : TreeLawData L₁ (n - 2 + 1) := L₀.face hSne hM₁
  /- ### `E_ν[δ↑(u)]` through Fact 2.8 -/
  have hupE : expCard μ.prob (upEdges S u) = upSum x S u := by
    unfold upSum
    exact expCard_prob_eq_sum μ (Finset.inter_subset_left.trans (cutEdges_subset_edgeFinset S))
  have hupC : upEdges S u ⊆ (internalEdges S)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_left
      (cutEdges_disjoint_internalEdges_self S))
  have hupν : expCard (nestedLaw μ u v W S) (upEdges S u) = expCard L₁ (upEdges S u) := by
    change expCard (nestedLaw μ u v W S) (upEdges S u) = expCard (treeFace μ.prob S) (upEdges S u)
    rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal]
    refine Finset.sum_congr rfl fun e he => ?_
    exact nestedLaw_outside μ hμ hune hvne hWne hSne huS hvS hWS hmass hM₁
      (outsideDetermined_mem (not_forall_mem_of_mem_cutEdges (Finset.mem_inter.mp he).1))
  have hup_le : expCard (nestedLaw μ u v W S) (upEdges S u) ≤ upSum x S u := by
    rw [hupν, ← hupE]
    have := L₀.law.face_outside_le hsup1 hM₁ hupC
    rw [← hL₁] at this
    exact this
  have hup_ge : upSum x S u - εη / 2 ≤ expCard (nestedLaw μ u v W S) (upEdges S u) := by
    rw [hupν]
    have := L₀.law.face_outside_ge hsup1 hM₁ hupC
    rw [← hL₁, hupE] at this
    have hq1 : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
      rw [qS]; linarith
    linarith
  /- ### Stages 2–4 and the chain identity -/
  have hEuS : internalEdges u ⊆ internalEdges S := internalEdges_mono huS
  have hEvS : internalEdges v ⊆ internalEdges S := internalEdges_mono hvS
  have hEWS : internalEdges W ⊆ internalEdges S := internalEdges_mono hWS
  have hEvW : internalEdges v ⊆ internalEdges W := internalEdges_mono hvW
  have hEvu : internalEdges v ⊆ (internalEdges u)ᶜ :=
    subset_compl_of_disjoint (disjoint_internalEdges hduv.symm)
  have hEWu : internalEdges W ⊆ (internalEdges u)ᶜ :=
    subset_compl_of_disjoint (disjoint_internalEdges hduW.symm)
  -- stage 2: `u` a tree
  have hsup2 := D₁.face_sup hune
  have qu' : ((u.card - 1 : ℕ) : ℝ) - expCard μ.prob (internalEdges u) = cutSum x u / 2 - 1 := qu
  have hq2 : faceDeficiency L₁ (internalEdges u) (u.card - 1) ≤ εη / 2 := by
    change ((u.card - 1 : ℕ) : ℝ) - expCard L₁ (internalEdges u) ≤ εη / 2
    have := L₀.law.face_inside_ge hsup1 hM₁ hEuS
    rw [← hL₁] at this
    linarith
  have hM₂ : 0 < totalMass (faceWeight L₁ (indicatorCost (internalEdges u)) (u.card - 1)) := by
    have := D₁.law.face_mass_ge hsup2; linarith
  set L₂ := faceDist L₁ (indicatorCost (internalEdges u)) (u.card - 1) with hL₂
  have D₂ : TreeLawData L₂ (n - 2 + 1) := D₁.face hune hM₂
  -- stage 3: `v` a tree
  have hsup3 := D₂.face_sup hvne
  have qv' : ((v.card - 1 : ℕ) : ℝ) - expCard μ.prob (internalEdges v) = cutSum x v / 2 - 1 := qv
  have hq3 : faceDeficiency L₂ (internalEdges v) (v.card - 1) ≤ εη := by
    change ((v.card - 1 : ℕ) : ℝ) - expCard L₂ (internalEdges v) ≤ εη
    have h1 := L₀.law.face_inside_ge hsup1 hM₁ hEvS
    rw [← hL₁] at h1
    have h2 := D₁.law.face_outside_ge hsup2 hM₂ hEvu
    rw [← hL₂] at h2
    linarith
  have hM₃ : 0 < totalMass (faceWeight L₂ (indicatorCost (internalEdges v)) (v.card - 1)) := by
    have := D₂.law.face_mass_ge hsup3; linarith
  set L₃ := faceDist L₂ (indicatorCost (internalEdges v)) (v.card - 1) with hL₃
  have D₃ : TreeLawData L₃ (n - 2 + 1) := D₂.face hvne hM₃
  -- stage 4: `W` a tree
  have hsup4 := D₃.face_sup hWne
  have qW' : ((W.card - 1 : ℕ) : ℝ) - expCard μ.prob (internalEdges W) = cutSum x W / 2 - 1 := qW
  have hq4 : faceDeficiency L₃ (internalEdges W) (W.card - 1) ≤ 1 / 2 - 9 * ε₂ + 5 / 2 * εη := by
    change ((W.card - 1 : ℕ) : ℝ) - expCard L₃ (internalEdges W) ≤ 1 / 2 - 9 * ε₂ + 5 / 2 * εη
    have h1 := L₀.law.face_inside_ge hsup1 hM₁ hEWS
    rw [← hL₁] at h1
    have h2 := D₁.law.face_outside_ge hsup2 hM₂ hEWu
    rw [← hL₂] at h2
    have h3 := D₂.law.face_inside_ge hsup3 hM₃ (Finset.Subset.refl (internalEdges v))
    rw [← hL₃] at h3
    have h4 := D₂.law.face_outside_ge hsup3 hM₃
      (subset_compl_of_disjoint (Finset.sdiff_disjoint (s := internalEdges v)
        (t := internalEdges W)))
    rw [← hL₃] at h4
    have s2 := expCard_inter_add_sdiff L₂ (internalEdges W) (internalEdges v)
    have s3 := expCard_inter_add_sdiff L₃ (internalEdges W) (internalEdges v)
    rw [Finset.inter_eq_right.mpr hEvW] at s2 s3
    have hq3' : ((v.card - 1 : ℕ) : ℝ) - expCard L₂ (internalEdges v) ≤ εη := hq3
    linarith
  have hM₄ : 0 < totalMass (faceWeight L₃ (indicatorCost (internalEdges W)) (W.card - 1)) := by
    have := D₃.law.face_mass_ge hsup4; linarith
  -- the chain identity
  have hchain : nestedLaw μ u v W S =
      faceDist L₃ (indicatorCost (internalEdges W)) (W.card - 1) := by
    have hsupμ : ∀ T, μ.prob T ≠ 0 → ∀ X : Finset (Fin n), X.Nonempty →
        setCost (indicatorCost (internalEdges X)) T ≤ X.card - 1 := by
      intro T hT X hX
      rw [setCost_indicatorCost]
      exact L₀.face_sup hX T hT
    have e12 : L₂ = faceDist μ.prob
        (fun e => indicatorCost (internalEdges S) e + indicatorCost (internalEdges u) e)
        ((S.card - 1) + (u.card - 1)) := by
      rw [hL₂, hL₁]
      exact faceDist_faceDist μ.prob (fun T hT => ⟨hsupμ T hT S hSne, hsupμ T hT u hune⟩) hM₁.ne'
    have hM12 : totalMass (faceWeight μ.prob
        (fun e => indicatorCost (internalEdges S) e + indicatorCost (internalEdges u) e)
        ((S.card - 1) + (u.card - 1))) ≠ 0 := by
      rw [← totalMass_faceWeight_faceDist μ.prob
        (fun T hT => ⟨hsupμ T hT S hSne, hsupμ T hT u hune⟩) hM₁.ne']
      rw [← hL₁]
      exact mul_ne_zero hM₂.ne' hM₁.ne'
    have e123 : L₃ = faceDist μ.prob
        (fun e => (indicatorCost (internalEdges S) e + indicatorCost (internalEdges u) e)
          + indicatorCost (internalEdges v) e)
        (((S.card - 1) + (u.card - 1)) + (v.card - 1)) := by
      rw [hL₃, e12]
      exact faceDist_faceDist μ.prob (fun T hT => ⟨by
        rw [setCost_add]; exact add_le_add (hsupμ T hT S hSne) (hsupμ T hT u hune),
        hsupμ T hT v hvne⟩) hM12
    have hM123 : totalMass (faceWeight μ.prob
        (fun e => (indicatorCost (internalEdges S) e + indicatorCost (internalEdges u) e)
          + indicatorCost (internalEdges v) e)
        (((S.card - 1) + (u.card - 1)) + (v.card - 1))) ≠ 0 := by
      rw [← totalMass_faceWeight_faceDist μ.prob (fun T hT => ⟨by
        rw [setCost_add]; exact add_le_add (hsupμ T hT S hSne) (hsupμ T hT u hune),
        hsupμ T hT v hvne⟩) hM12]
      rw [← e12]
      exact mul_ne_zero hM₃.ne' hM12
    have e1234 : faceDist L₃ (indicatorCost (internalEdges W)) (W.card - 1) = faceDist μ.prob
        (fun e => ((indicatorCost (internalEdges S) e + indicatorCost (internalEdges u) e)
          + indicatorCost (internalEdges v) e) + indicatorCost (internalEdges W) e)
        ((((S.card - 1) + (u.card - 1)) + (v.card - 1)) + (W.card - 1)) := by
      rw [e123]
      exact faceDist_faceDist μ.prob (fun T hT => ⟨by
        rw [setCost_add, setCost_add]
        exact add_le_add (add_le_add (hsupμ T hT S hSne) (hsupμ T hT u hune))
          (hsupμ T hT v hvne), hsupμ T hT W hWne⟩) hM123
    rw [e1234]
    unfold nestedLaw
    have hc : (fun e => ((indicatorCost (internalEdges S) e + indicatorCost (internalEdges u) e)
          + indicatorCost (internalEdges v) e) + indicatorCost (internalEdges W) e)
        = nestedCost u v W S := by
      funext e; unfold nestedCost; omega
    have hb : (((S.card - 1) + (u.card - 1)) + (v.card - 1)) + (W.card - 1)
        = nestedBudget u v W S := by
      unfold nestedBudget; omega
    rw [hc, hb]
  /- ### `E_ν[δ(v)]` along the chain -/
  have hcvS : cutEdges v ⊆ (internalEdges v)ᶜ :=
    subset_compl_of_disjoint (cutEdges_disjoint_internalEdges_self v)
  have hcvu : cutEdges v ⊆ (internalEdges u)ᶜ :=
    subset_compl_of_disjoint (cutEdges_disjoint_internalEdges hduv.symm)
  have hxv : expCard μ.prob (cutEdges v) = cutSum x v := expCard_prob_cutEdges μ v
  have hq1 : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
    rw [qS]; linarith
  -- stage 1: split by `E(S)`
  have s0 := expCard_inter_add_sdiff μ.prob (cutEdges v) (internalEdges S)
  have s1 := expCard_inter_add_sdiff L₁ (cutEdges v) (internalEdges S)
  have a1 := L₀.law.face_inside_ge hsup1 hM₁ (Finset.inter_subset_right (s₁ := cutEdges v)
    (s₂ := internalEdges S))
  have a2 := L₀.law.face_inside_le hsup1 hM₁ (Finset.inter_subset_right (s₁ := cutEdges v)
    (s₂ := internalEdges S))
  have a3 := L₀.law.face_outside_le hsup1 hM₁ (subset_compl_of_disjoint
    (Finset.sdiff_disjoint (s := internalEdges S) (t := cutEdges v)))
  have a4 := L₀.law.face_outside_ge hsup1 hM₁ (subset_compl_of_disjoint
    (Finset.sdiff_disjoint (s := internalEdges S) (t := cutEdges v)))
  rw [← hL₁] at a1 a2 a3 a4
  -- stages 2, 3: outside
  have b1 := D₁.law.face_outside_le hsup2 hM₂ hcvu
  have b2 := D₁.law.face_outside_ge hsup2 hM₂ hcvu
  rw [← hL₂] at b1 b2
  have c1 := D₂.law.face_outside_le hsup3 hM₃ hcvS
  have c2 := D₂.law.face_outside_ge hsup3 hM₃ hcvS
  rw [← hL₃] at c1 c2
  -- stage 4: split by `E(W)`
  have s3 := expCard_inter_add_sdiff L₃ (cutEdges v) (internalEdges W)
  have s4 := expCard_inter_add_sdiff (faceDist L₃ (indicatorCost (internalEdges W)) (W.card - 1))
    (cutEdges v) (internalEdges W)
  have d1 := D₃.law.face_inside_ge hsup4 hM₄ (Finset.inter_subset_right (s₁ := cutEdges v)
    (s₂ := internalEdges W))
  have d2 := D₃.law.face_inside_le hsup4 hM₄ (Finset.inter_subset_right (s₁ := cutEdges v)
    (s₂ := internalEdges W))
  have d3 := D₃.law.face_outside_le hsup4 hM₄ (subset_compl_of_disjoint
    (Finset.sdiff_disjoint (s := internalEdges W) (t := cutEdges v)))
  have d4 := D₃.law.face_outside_ge hsup4 hM₄ (subset_compl_of_disjoint
    (Finset.sdiff_disjoint (s := internalEdges W) (t := cutEdges v)))
  have hcutv_ge : 3 / 2 + 9 * ε₂ - 9 / 2 * εη ≤ expCard (nestedLaw μ u v W S) (cutEdges v) := by
    rw [hchain]
    linarith
  have hcutv_le : expCard (nestedLaw μ u v W S) (cutEdges v) ≤ 5 / 2 - 9 * ε₂ + 4 * εη := by
    rw [hchain]
    linarith
  exact ⟨hmass, hmassGe, hlaw, hsupp, hup_ge, hup_le, hcutv_ge, hcutv_le, hunwind⟩

/-- **The nested data of two children of a hierarchy cut**, when
`x(δ↑(u)) ≥ 1/2 + 9ε₂`. This preserves the original KKO interface. -/
theorem Hierarchy.nestedData {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : IsChildOf H.cuts u S)
    (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hup : 1 / 2 + 9 * ε₂ ≤ upSum x S u) :
    NestedData μ (n - 2 + 1) u v (S \ u) S ε₂ εη :=
  H.nestedData_of_small_error hx μ hμ hS hu hv huv hεη hε₂ (by nlinarith) hup

end TSPGap

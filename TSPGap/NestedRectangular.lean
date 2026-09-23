/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Claim75

/-!
# Rectangularity descends to a nested cut

`claim_7_5_nested` took the rectangularity of `E ∧ InducesTree S` at `S` as a
hypothesis.  This file discharges it, so nothing escapes into Lemma 7.3.

The chain is short and needs **no contracted graph**:

* `outsidePart_nested` — for `S ⊆ U`, `outsidePart U T` is already determined by
  `outsidePart S T`.
* `OutsideDetermined.descend` — hence outside-determinacy descends from `U` to
  `S`.
* `InducesTree.glue_nested` — 🔑 the graph content: inside an induced tree on
  `U`, one induced tree on `S` may be replaced by another with the same outside
  part.  Counting is free (`insidePart U W = insidePart S W ⊔ bridge W`, and the
  two inside parts have the same size `|S| − 1`); connectivity is the walk
  induction of `InducesTreeOn.glue`, rerouting each `S`-internal edge through
  the new tree.
* `IsRectangularAt.nested` — the witness is
  `R T := (∀ T', InducesTree S T' → outsidePart S T' = outsidePart S T →
   InducesTree U T') ∧ Q T`, which reads only `outsidePart S T` by
  construction, and which `glue_nested` shows is implied by `InducesTree U T`.

`treeFace_not_inducesTree_le` supplies the other premise: under the tree face of
`U`, the mass on which `S` fails to induce a tree is at most `ε_η/2` — the
max-face bound at `S`, with the face deficiency only *decreasing* when passed to
the face at `U` (inside counts go up).  `claim_7_5_nested'` is then the
paper-facing form with neither premise exposed.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Outside-determinacy descends -/

/-- For `S ⊆ U` the outside of `U` is already visible from the outside of `S`. -/
theorem outsidePart_nested {S U : Finset (Fin n)} (hSU : S ⊆ U)
    (T : Finset (Sym2 (Fin n))) :
    outsidePart U T = outsidePart U (outsidePart S T) := by
  classical
  ext e
  simp only [mem_outsidePart]
  constructor
  · rintro ⟨hT, hU⟩
    exact ⟨⟨hT, fun hS => hU fun w hw => hSU (hS w hw)⟩, hU⟩
  · rintro ⟨⟨hT, -⟩, hU⟩
    exact ⟨hT, hU⟩

/-- Outside-determinacy at `U` implies outside-determinacy at any `S ⊆ U`. -/
theorem OutsideDetermined.descend {S U : Finset (Fin n)} (hSU : S ⊆ U)
    {P : Finset (Sym2 (Fin n)) → Prop} (h : OutsideDetermined U P) :
    OutsideDetermined S P := by
  intro T T' hTT'
  refine h T T' ?_
  rw [outsidePart_nested hSU T, outsidePart_nested hSU T', hTT']

/-! ### The inside part splits at a nested cut -/

/-- `insidePart U W` is the `S`-inside part together with the edges of `W`
inside `U` but not inside `S`. -/
theorem insidePart_nested_union {S U : Finset (Fin n)} (hSU : S ⊆ U)
    (W : Finset (Sym2 (Fin n))) :
    insidePart U W = insidePart S W ∪ insidePart U (outsidePart S W) := by
  classical
  ext e
  simp only [mem_insidePart, mem_outsidePart, Finset.mem_union]
  constructor
  · rintro ⟨hW, hU⟩
    by_cases hS : ∀ w ∈ e, w ∈ S
    · exact Or.inl ⟨hW, hS⟩
    · exact Or.inr ⟨⟨hW, hS⟩, hU⟩
  · rintro (⟨hW, hS⟩ | ⟨⟨hW, -⟩, hU⟩)
    · exact ⟨hW, fun w hw => hSU (hS w hw)⟩
    · exact ⟨hW, hU⟩

/-- ⚠️ Stated at **two** sets: after the outside parts are identified the two
halves of the split come from different trees, so a single-set version does not
match. -/
theorem insidePart_disjoint_outside {S U : Finset (Fin n)} (W W' : Finset (Sym2 (Fin n))) :
    Disjoint (insidePart S W) (insidePart U (outsidePart S W')) := by
  classical
  refine Finset.disjoint_left.mpr fun e h1 h2 => ?_
  exact (mem_outsidePart.mp (mem_insidePart.mp h2).1).2 (mem_insidePart.mp h1).2

/-! ### The glue -/

set_option maxHeartbeats 400000 in
-- the cardinality split and the walk induction in one proof
/-- 🔑 **Inside an induced tree on `U`, one induced tree on `S` may be replaced
by another with the same outside part.**  This is what makes
`E ∧ InducesTree S` rectangular at `S` when `E` is rectangular at `U ⊇ S`. -/
theorem InducesTree.glue_nested {S U : Finset (Fin n)} (hSU : S ⊆ U)
    {T T' : Finset (Sym2 (Fin n))} (hUT : InducesTree U T) (hST : InducesTree S T)
    (hST' : InducesTree S T') (hout : outsidePart S T' = outsidePart S T) :
    InducesTree U T' := by
  classical
  have hsplitT := insidePart_nested_union hSU T
  have hsplitT' := insidePart_nested_union hSU T'
  rw [hout] at hsplitT'
  refine ⟨?_, ?_⟩
  · -- counting: the two `S`-parts have the same size, the bridges are equal
    have hc := hUT.1
    rw [hsplitT, Finset.card_union_of_disjoint (insidePart_disjoint_outside _ _)] at hc
    have h1 := hST.1
    have h2 := hST'.1
    rw [hsplitT', Finset.card_union_of_disjoint (insidePart_disjoint_outside _ _)]
    omega
  · -- connectivity: reroute each `S`-internal edge through the new tree
    have hmono : SimpleGraph.fromEdgeSet (↑(insidePart S T') : Set (Sym2 (Fin n)))
        ≤ SimpleGraph.fromEdgeSet (↑(insidePart U T') : Set (Sym2 (Fin n))) := by
      refine SimpleGraph.fromEdgeSet_mono ?_
      rw [hsplitT']
      exact_mod_cast (Finset.subset_union_left :
        insidePart S T' ⊆ insidePart S T' ∪ insidePart U (outsidePart S T))
    have hstep : ∀ a b, (SimpleGraph.fromEdgeSet (↑(insidePart U T) : Set (Sym2 (Fin n)))).Adj a b →
        (SimpleGraph.fromEdgeSet (↑(insidePart U T') : Set (Sym2 (Fin n)))).Reachable a b := by
      intro a b hadj
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      obtain ⟨hmem, hne⟩ := hadj
      rw [Finset.mem_coe, hsplitT, Finset.mem_union] at hmem
      rcases hmem with hin | hbr
      · -- an `S`-internal edge: route through the new tree on `S`
        obtain ⟨-, hS⟩ := mem_insidePart.mp hin
        exact (hST'.2 a (hS a (by simp)) b (hS b (by simp))).mono hmono
      · -- a bridge edge: present in `T'` outright
        refine SimpleGraph.Adj.reachable ?_
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, hne⟩
        rw [Finset.mem_coe, hsplitT']
        exact Finset.mem_union_right _ hbr
    have hwalk : ∀ a b,
        ∀ _ : (SimpleGraph.fromEdgeSet (↑(insidePart U T) : Set (Sym2 (Fin n)))).Walk a b,
        (SimpleGraph.fromEdgeSet (↑(insidePart U T') : Set (Sym2 (Fin n)))).Reachable a b := by
      intro a b w
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih => exact (hstep _ _ hadj).trans ih
    intro a ha b hb
    exact (hUT.2 a ha b hb).elim (hwalk a b)

/-! ### The nested rectangularity -/

/-- **Rectangularity descends to a nested cut**, once the inner tree event is
conjoined.  The witness reads only `outsidePart S T` by construction; that it is
*implied* by `InducesTree U T` is exactly `glue_nested`. -/
theorem IsRectangularAt.nested {S U : Finset (Fin n)} (hSU : S ⊆ U)
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt U E) :
    IsRectangularAt S (fun T => E T ∧ InducesTree S T) := by
  obtain ⟨Q, hQ, hEQ⟩ := hE
  refine ⟨fun T => (∀ T', InducesTree S T' → outsidePart S T' = outsidePart S T →
      InducesTree U T') ∧ Q T, ?_, ?_⟩
  · refine OutsideDetermined.and ?_ (hQ.descend hSU)
    intro T₁ T₂ h12
    constructor
    · exact fun h T' hT' hout => h T' hT' (by rw [hout, h12])
    · exact fun h T' hT' hout => h T' hT' (by rw [hout, ← h12])
  · intro T
    constructor
    · rintro ⟨hET, hS⟩
      obtain ⟨hU, hQT⟩ := (hEQ T).mp hET
      exact ⟨hS, fun T' hT' hout => InducesTree.glue_nested hSU hU hS hT' hout, hQT⟩
    · rintro ⟨hS, hall, hQT⟩
      exact ⟨(hEQ T).mpr ⟨hall T hS rfl, hQT⟩, hS⟩

/-! ### The failure term -/

set_option maxHeartbeats 400000 in
-- the max-face bound at `S`, transported to the face of `U`
/-- **Under the tree face of `U`, an inner cut `S ⊆ U` fails to induce a tree on
at most `ε_η/2` of the mass.**  This is the max-face bound at `S`, and the face
deficiency only *decreases* when read at the face of `U`, because inside counts
go up there (`face_inside_ge`). -/
theorem treeFace_not_inducesTree_le {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} {S U : Finset (Fin n)} (hSU : S ⊆ U)
    (hSne : S.Nonempty) (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U)
    (hScut : cutSum x S ≤ 2 + εη) (hUcut : cutSum x U ≤ 2 + εη) (hεηcap : εη ≤ 1e-10) :
    weightMass (treeFace μ.prob U) (fun T => ¬ InducesTree S T) ≤ εη / 2 := by
  classical
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsupU := hbase.face_sup hUne
  have hdefU : faceDeficiency μ.prob (internalEdges U) (U.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hUne hU0]; linarith
  have hmassU : 0 <
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges U)) (U.card - 1)) := by
    have := hbase.law.face_mass_ge hsupU; linarith
  have hFtree : TreeLawData (treeFace μ.prob U) (n - 1) := hbase.face hUne hmassU
  -- the deficiency at `S` is no larger under the face of `U`
  have hdefS : faceDeficiency (treeFace μ.prob U) (internalEdges S) (S.card - 1) ≤ εη / 2 := by
    have hge : expCard μ.prob (internalEdges S)
        ≤ expCard (treeFace μ.prob U) (internalEdges S) :=
      hbase.law.face_inside_ge hsupU hmassU (internalEdges_mono hSU)
    have hdS : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
      rw [faceDeficiency_internal_eq hx μ hSne (hU0.mono hSU)]; linarith
    unfold faceDeficiency at hdS ⊢
    linarith
  have hmassS := hFtree.law.face_mass_ge (hFtree.face_sup hSne)
  -- the face mass at `S` *is* the tree event
  have hid : totalMass
      (faceWeight (treeFace μ.prob U) (indicatorCost (internalEdges S)) (S.card - 1))
      = weightMass (treeFace μ.prob U) (fun T => InducesTree S T) := by
    rw [totalMass_faceWeight]
    refine weightMass_congr_of_support fun T hT => ?_
    have hTst : IsSpanningTree n T := hFtree.tree T hT
    have h1S : 1 ≤ S.card := Finset.card_pos.mpr hSne
    rw [setCost_indicatorCost]
    constructor
    · intro hcard
      refine ((inducesTreeOn_iff_card hTst S).mpr ?_).2
      rw [Finset.inter_comm]; omega
    · intro hind
      have hc := (inducesTreeOn_iff_card hTst S).mp ⟨hTst, hind⟩
      rw [Finset.inter_comm] at hc
      omega
  have hnot := weightMass_not (treeFace μ.prob U) (fun T => InducesTree S T)
  rw [hFtree.law.tot] at hnot
  linarith

/-! ### The paper-facing nested claim -/

set_option maxHeartbeats 400000 in
-- both premises of the low-level form are discharged here
/-- **Claim 7.5 at a nested cut**, with neither premise exposed: the
rectangularity of `E ∧ InducesTree S` at `S` comes from `IsRectangularAt.nested`
and the failure mass from `treeFace_not_inducesTree_le` through the rectangular
transfer at `U`.  This is the form Lemma 7.3's Case 3 consumes, so `hnest` never
escapes. -/
theorem claim_7_5_nested' {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {S u U : Finset (Fin n)} (hSne : S.Nonempty) (hune : u.Nonempty) (huS : u ⊂ S)
    (huniv : u ≠ Finset.univ) (hScut : cutSum x S ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hSU : S ⊆ U) (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hUcut : cutSum x U ≤ 2 + εη)
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt U E)
    {v : Finset (Sym2 (Fin n)) → ℝ} {p : ℝ} (hv : IsUniformThinning μ.prob v E p)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges S, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges S, x g) ≤ 1 - ε) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) + p * (εη / 2) := by
  classical
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsupU := hbase.face_sup hUne
  have hdefU : faceDeficiency μ.prob (internalEdges U) (U.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hUne hU0]; linarith
  have hmassU : 0 <
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges U)) (U.card - 1)) := by
    have := hbase.law.face_mass_ge hsupU; linarith
  refine claim_7_5_nested hx hμ hεη hεηcap hSne (hU0.mono hSU) hune huS huniv hScut hucut
    (hE.nested hSU) hv ?_ hε0 hclo hchi
  have hins : InsideDetermined U (fun T => ¬ InducesTree S T) := fun T T' hTT' =>
    not_congr (insideDetermined_inducesTree hSU T T' hTT')
  exact hE.thin_weightMass_le μ hμ hUne hmassU hv hins
    (treeFace_not_inducesTree_le hx μ hμ hSU hSne hUne hU0 hScut hUcut hεηcap)

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Claim75
import TSPGap.RefinedRectangularTransfer

/-!
# KKO21 Claim 7.5 on pieces

The piece form of `Claim75.lean`.  A thinning of the **lifted** law, uniform
over an event rectangular at `U` in the piece sense, puts mass at most
`p · (1 − ε + max(2ε_η, ε²))` on the trees whose piece count over `δ(u)` is
odd, for `u ⊊ U` with `x(δ(u) ∩ δ(U)) ∈ [ε, 1 − ε]`.

Only the factorization is piece-native: the rectangular event may distinguish
copies of one edge, so it is factored against the inside parity through the
piece Fact 2.8 (`IsRectangularAtOn.weightMass_factor`).  The two parity
numbers at the tree face of `U` — the mass of an odd inside crossing count and
its complement — are read on fiber-saturated sets, so they are the **base**
numbers, transported through `weightMass_refinedTreeFace_count`; the base
proof of their bounds is reused verbatim.  The nested form takes the
rectangularity of `E ∧ "S induces a tree in the projection"` at `S` as a
hypothesis, discharged in `RefinedNestedRectangular.lean`.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### The cut of a nested atom splits on pieces -/

/-- The pieces over a nested atom's cut split into the inside and the outside
crossings, as the base cut does. -/
theorem card_split_of_subcut_on {S u : Finset (Fin n)} (huS : u ⊆ S) (Ť : Finset R.Piece) :
    (Ť ∩ R.piecesOver (cutEdges u)).card
      = (Ť ∩ R.piecesOver (cutEdges u ∩ internalEdges S)).card
        + (Ť ∩ R.piecesOver (cutEdges u ∩ cutEdges S)).card := by
  classical
  have hsplit : R.piecesOver (cutEdges u)
      = R.piecesOver (cutEdges u ∩ internalEdges S) ∪ R.piecesOver (cutEdges u ∩ cutEdges S) := by
    rw [← R.model_fiberOver, ← R.model_fiberOver, ← R.model_fiberOver, ← R.model.fiberOver_union,
      ← cutEdges_eq_din_union_dout huS]
  have hd : Disjoint (R.piecesOver (cutEdges u ∩ internalEdges S))
      (R.piecesOver (cutEdges u ∩ cutEdges S)) := by
    rw [← R.model_fiberOver, ← R.model_fiberOver]
    exact R.model.disjoint_fiberOver (din_disjoint_dout S u)
  rw [hsplit, card_inter_union_of_disjoint hd Ť]

/-! ### The claim -/

set_option maxHeartbeats 400000 in
-- the base face-law package and parity bounds, then the piece factorization
/-- **KKO21 Claim 7.5 at the lifted law**, the cross-multiplied form the
thinning transfer consumes. -/
theorem claim_7_5_core_on {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {U u : Finset (Fin n)} (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hune : u.Nonempty)
    (huU : u ⊂ U)
    (huniv : u ≠ Finset.univ) (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn U E)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges U, x g) ≤ 1 - ε) :
    weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
      ≤ (1 - ε + max (2 * εη) (ε ^ 2)) * weightMass (R.liftProb μ) E := by
  classical
  -- the law package at the tree face of `U`
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsup := hbase.face_sup hUne
  have hdefle : faceDeficiency μ.prob (internalEdges U) (U.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hUne hU0]; linarith
  have hmassge := hbase.law.face_mass_ge hsup
  have hmass : 0 <
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges U)) (U.card - 1)) := by
    linarith
  have hFlaw : LawData (treeFace μ.prob U) (n - 1) := (hbase.face hUne hmass).law
  -- the inside crossing count never vanishes
  have hzero := weightMass_din_treeFace_eq_zero (μ := μ) hUne hune huU
  -- the mean of the inside crossing count at the face
  have hxDin : expCard μ.prob (cutEdges u ∩ internalEdges U)
      = ∑ e ∈ cutEdges u ∩ internalEdges U, x e :=
    expCard_prob_eq_sum μ (Finset.inter_subset_right.trans (internalEdges_subset_edgeFinset U))
  have hsplit : cutSum x u = (∑ e ∈ cutEdges u ∩ internalEdges U, x e)
      + ∑ e ∈ cutEdges u ∩ cutEdges U, x e := by
    conv_lhs => rw [cutSum, cutEdges_eq_din_union_dout huU.subset]
    exact Finset.sum_union (din_disjoint_dout U u)
  have hu2 : 2 ≤ cutSum x u := hx.cut_lower u hune huniv (hU0.mono huU.subset)
  have hface_ge : expCard μ.prob (cutEdges u ∩ internalEdges U)
      ≤ expCard (treeFace μ.prob U) (cutEdges u ∩ internalEdges U) :=
    hbase.law.face_inside_ge hsup hmass Finset.inter_subset_right
  have hface_le : expCard (treeFace μ.prob U) (cutEdges u ∩ internalEdges U)
      ≤ expCard μ.prob (cutEdges u ∩ internalEdges U)
        + faceDeficiency μ.prob (internalEdges U) (U.card - 1) :=
    hbase.law.face_inside_le hsup hmass Finset.inter_subset_right
  have hmlo : 1 + ε ≤ expCard (treeFace μ.prob U) (cutEdges u ∩ internalEdges U) := by
    rw [hxDin] at hface_ge; linarith
  have hmhi : expCard (treeFace μ.prob U) (cutEdges u ∩ internalEdges U) ≤ 2 - ε + 2 * εη := by
    rw [hxDin] at hface_le; linarith
  -- name the two pieces of `δ(u)`
  set Din : Finset (Sym2 (Fin n)) := cutEdges u ∩ internalEdges U with hDinDef
  set Dout : Finset (Sym2 (Fin n)) := cutEdges u ∩ cutEdges U with hDoutDef
  -- the two parity bounds at the face
  set a : ℝ := weightMass (treeFace μ.prob U) (fun T => Odd (T ∩ Din).card) with ha
  have haupper : a ≤ 1 - ε + ε ^ 2 := by
    have h := oddCount_le hFlaw.st hFlaw.rank hFlaw.nn hFlaw.tot Din hzero (by linarith)
    have hmono : Real.exp (-2 * (expCard (treeFace μ.prob U) Din - 1)) ≤ Real.exp (-2 * ε) :=
      Real.exp_le_exp.mpr (by linarith)
    have hel := sub_sq_le_one_sub_exp_neg_two_mul hε0
    linarith
  have halower : 1 - a ≤ 1 - ε + 2 * εη := by
    have h := oddCount_ge hFlaw.st hFlaw.rank hFlaw.nn hFlaw.tot Din hzero
    linarith
  -- the base parity numbers, transported to the piece face
  have haEven : weightMass (treeFace μ.prob U) (fun T => Even (T ∩ Din).card) = 1 - a := by
    have hnot := weightMass_not (treeFace μ.prob U) (fun T => Odd (T ∩ Din).card)
    rw [hFlaw.tot] at hnot
    rw [← hnot]
    exact weightMass_congr fun T => by rw [Nat.not_odd_iff_even]
  have haOdd' : weightMass (R.refinedTreeFace (R.liftProb μ) U)
      (fun Ť => Odd (Ť ∩ R.piecesOver Din).card) = a := by
    rw [R.weightMass_refinedTreeFace_count μ U Din (fun k => Odd k)]
  have haEven' : weightMass (R.refinedTreeFace (R.liftProb μ) U)
      (fun Ť => Even (Ť ∩ R.piecesOver Din).card) = 1 - a := by
    rw [R.weightMass_refinedTreeFace_count μ U Din (fun k => Even k)]
    exact haEven
  -- determinacy of the four parity events, on pieces
  have hDinsub : ∀ g ∈ Din, ∀ w ∈ g, w ∈ U := fun g hg w hw =>
    (mem_internalEdges.mp (Finset.mem_inter.mp hg).2).2 w hw
  have hDoutsub : ∀ g ∈ Dout, ¬ ∀ w ∈ g, w ∈ U := fun g hg =>
    not_forall_mem_of_mem_cutEdges (Finset.mem_inter.mp hg).2
  have hinOdd : R.RefinedInsideDetermined U (fun Ť => Odd (Ť ∩ R.piecesOver Din).card) :=
    R.refinedInsideDetermined_inter (fun q hq => hDinsub _ (R.mem_piecesOver.mp hq))
      (fun X => Odd X.card)
  have hinEven : R.RefinedInsideDetermined U (fun Ť => Even (Ť ∩ R.piecesOver Din).card) :=
    R.refinedInsideDetermined_inter (fun q hq => hDinsub _ (R.mem_piecesOver.mp hq))
      (fun X => Even X.card)
  have houtEven : R.RefinedOutsideDetermined U (fun Ť => Even (Ť ∩ R.piecesOver Dout).card) :=
    R.refinedOutsideDetermined_inter (fun q hq => hDoutsub _ (R.mem_piecesOver.mp hq))
      (fun X => Even X.card)
  have houtOdd : R.RefinedOutsideDetermined U (fun Ť => Odd (Ť ∩ R.piecesOver Dout).card) :=
    R.refinedOutsideDetermined_inter (fun q hq => hDoutsub _ (R.mem_piecesOver.mp hq))
      (fun X => Odd X.card)
  -- the piece count over `δ(u)` is odd exactly when the two parities differ
  have hpar : ∀ Ť : Finset R.Piece, Odd (Ť ∩ R.piecesOver (cutEdges u)).card ↔
      ((Odd (Ť ∩ R.piecesOver Din).card ∧ Even (Ť ∩ R.piecesOver Dout).card)
        ∨ (Even (Ť ∩ R.piecesOver Din).card ∧ Odd (Ť ∩ R.piecesOver Dout).card)) := by
    intro Ť
    have hsp := R.card_split_of_subcut_on huU.subset Ť
    rw [← hDinDef, ← hDoutDef] at hsp
    rw [hsp]
    simp only [Nat.odd_iff, Nat.even_iff]
    omega
  have hA0 : weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
      = weightMass (R.liftProb μ)
          (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver Din).card ∧ Even (Ť ∩ R.piecesOver Dout).card)
        + weightMass (R.liftProb μ)
          (fun Ť => E Ť ∧ Even (Ť ∩ R.piecesOver Din).card ∧ Odd (Ť ∩ R.piecesOver Dout).card) := by
    have hor := weightMass_or (R.liftProb μ)
      (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver Din).card ∧ Even (Ť ∩ R.piecesOver Dout).card)
      (fun Ť => E Ť ∧ Even (Ť ∩ R.piecesOver Din).card ∧ Odd (Ť ∩ R.piecesOver Dout).card)
    have hand : weightMass (R.liftProb μ) (fun Ť =>
        (E Ť ∧ Odd (Ť ∩ R.piecesOver Din).card ∧ Even (Ť ∩ R.piecesOver Dout).card)
          ∧ (E Ť ∧ Even (Ť ∩ R.piecesOver Din).card ∧ Odd (Ť ∩ R.piecesOver Dout).card)) = 0 := by
      rw [show (fun Ť : Finset R.Piece =>
          (E Ť ∧ Odd (Ť ∩ R.piecesOver Din).card ∧ Even (Ť ∩ R.piecesOver Dout).card)
            ∧ (E Ť ∧ Even (Ť ∩ R.piecesOver Din).card ∧ Odd (Ť ∩ R.piecesOver Dout).card))
            = fun _ => False from ?_, weightMass_false]
      funext Ť
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      exact (Nat.not_odd_iff_even.mpr h.2.2.1) h.1.2.1
    rw [hand, add_zero] at hor
    rw [← hor]
    exact weightMass_congr fun Ť => by rw [hpar Ť]; tauto
  have hB0 : weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Even (Ť ∩ R.piecesOver Dout).card)
      + weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver Dout).card)
      = weightMass (R.liftProb μ) E := by
    have hor := weightMass_or (R.liftProb μ) (fun Ť => E Ť ∧ Even (Ť ∩ R.piecesOver Dout).card)
      (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver Dout).card)
    have hand : weightMass (R.liftProb μ) (fun Ť => (E Ť ∧ Even (Ť ∩ R.piecesOver Dout).card)
        ∧ (E Ť ∧ Odd (Ť ∩ R.piecesOver Dout).card)) = 0 := by
      rw [show (fun Ť : Finset R.Piece => (E Ť ∧ Even (Ť ∩ R.piecesOver Dout).card)
          ∧ (E Ť ∧ Odd (Ť ∩ R.piecesOver Dout).card)) = fun _ => False from ?_, weightMass_false]
      funext Ť
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      exact (Nat.not_odd_iff_even.mpr h.1.2) h.2.2
    have htrue : weightMass (R.liftProb μ) (fun Ť => (E Ť ∧ Even (Ť ∩ R.piecesOver Dout).card)
        ∨ (E Ť ∧ Odd (Ť ∩ R.piecesOver Dout).card)) = weightMass (R.liftProb μ) E := by
      refine weightMass_congr fun Ť => ?_
      rcases Nat.even_or_odd (Ť ∩ R.piecesOver Dout).card with he | ho
      · exact ⟨fun h => h.elim (fun k => k.1) (fun k => k.1), fun h => Or.inl ⟨h, he⟩⟩
      · exact ⟨fun h => h.elim (fun k => k.1) (fun k => k.1), fun h => Or.inr ⟨h, ho⟩⟩
    rw [hand, add_zero, htrue] at hor
    exact hor.symm
  -- factor the inside parity off each piece, through the piece Fact 2.8
  have hf1 := hE.weightMass_factor μ hμ hUne hmass hinOdd houtEven
  have hf2 := hE.weightMass_factor μ hμ hUne hmass hinEven houtOdd
  rw [haOdd'] at hf1
  rw [haEven'] at hf2
  rw [hA0, hf1, hf2, ← hB0]
  -- a mixture is at most its larger weight
  have hn1 : 0 ≤ weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Even (Ť ∩ R.piecesOver Dout).card) :=
    weightMass_nonneg (R.liftProb_weightNonneg μ) _
  have hn2 : 0 ≤ weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver Dout).card) :=
    weightMass_nonneg (R.liftProb_weightNonneg μ) _
  have hac : a ≤ 1 - ε + max (2 * εη) (ε ^ 2) := by
    have := le_max_right (2 * εη) (ε ^ 2); linarith
  have hac' : 1 - a ≤ 1 - ε + max (2 * εη) (ε ^ 2) := by
    have := le_max_left (2 * εη) (ε ^ 2); linarith
  nlinarith [mul_le_mul_of_nonneg_right hac hn1, mul_le_mul_of_nonneg_right hac' hn2]

/-- **KKO21 Claim 7.5 on pieces**, in the consumer form: at a thinning of the
lifted law uniform over an event rectangular at `U` in the piece sense, the
mass on which the piece count over `δ(u)` is odd is at most
`p · (1 − ε + max(2ε_η, ε²))`. -/
theorem claim_7_5_on {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {U u : Finset (Fin n)} (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hune : u.Nonempty)
    (huU : u ⊂ U)
    (huniv : u ≠ Finset.univ) (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn U E)
    {v : Finset R.Piece → ℝ} {p : ℝ} (hv : IsUniformThinning (R.liftProb μ) v E p)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges U, x g) ≤ 1 - ε) :
    weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) :=
  hv.weightMass_le (R.liftProb_weightNonneg μ)
    (R.claim_7_5_core_on hx hμ hεη hεηcap hUne hU0 hune huU huniv hUcut hucut hE hε0 hclo hchi)

/-! ### The nested adapter -/

set_option maxHeartbeats 400000 in
-- the split, the core at the restricted event, and the failure term
/-- **The nested transfer on pieces.**  The rectangularity of
`E ∧ "S induces a tree in the projection"` at `S` is a hypothesis here,
discharged in `RefinedNestedRectangular.lean`. -/
theorem claim_7_5_nested_on {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {S u : Finset (Fin n)} (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S) (hune : u.Nonempty)
    (huS : u ⊂ S)
    (huniv : u ≠ Finset.univ) (hScut : cutSum x S ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {E : Finset R.Piece → Prop}
    (hnest : R.IsRectangularAtOn S (fun Ť => E Ť ∧ InducesTree S (R.project Ť)))
    {v : Finset R.Piece → ℝ} {p : ℝ} (hv : IsUniformThinning (R.liftProb μ) v E p)
    (hfail : weightMass v (fun Ť => ¬ InducesTree S (R.project Ť)) ≤ p * (εη / 2))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges S, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges S, x g) ≤ 1 - ε) :
    weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) + p * (εη / 2) := by
  classical
  have hcnn : 0 ≤ 1 - ε + max (2 * εη) (ε ^ 2) := by
    have h1 : ε ≤ 1 - ε := le_trans hclo hchi
    have h2 : (0:ℝ) ≤ max (2 * εη) (ε ^ 2) := le_trans (by positivity) (le_max_right _ _)
    linarith
  -- split off the trees on which `S` fails
  have hsplit : weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
      ≤ weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card
          ∧ InducesTree S (R.project Ť))
        + weightMass v (fun Ť => ¬ InducesTree S (R.project Ť)) := by
    have hor := weightMass_or v
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card ∧ InducesTree S (R.project Ť))
      (fun Ť => ¬ InducesTree S (R.project Ť))
    have hmono : weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ weightMass v (fun Ť => (Odd (Ť ∩ R.piecesOver (cutEdges u)).card
            ∧ InducesTree S (R.project Ť)) ∨ ¬ InducesTree S (R.project Ť)) := by
      refine weightMass_mono hv.nonneg fun Ť h => ?_
      by_cases hg : InducesTree S (R.project Ť)
      · exact Or.inl ⟨h, hg⟩
      · exact Or.inr hg
    have hand : 0 ≤ weightMass v (fun Ť => (Odd (Ť ∩ R.piecesOver (cutEdges u)).card
        ∧ InducesTree S (R.project Ť)) ∧ ¬ InducesTree S (R.project Ť)) :=
      weightMass_nonneg hv.nonneg _
    linarith
  -- the `S`-tree part, through the core at the restricted event
  have hmain : weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card
      ∧ InducesTree S (R.project Ť)) ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) := by
    refine hv.weightMass_le (R.liftProb_weightNonneg μ) ?_
    have hcore := R.claim_7_5_core_on hx hμ hεη hεηcap hSne hS0 hune huS huniv hScut hucut
      hnest hε0 hclo hchi
    have hre : weightMass (R.liftProb μ)
        (fun Ť => E Ť ∧ Odd (Ť ∩ R.piecesOver (cutEdges u)).card ∧ InducesTree S (R.project Ť))
        = weightMass (R.liftProb μ)
          (fun Ť => (fun Ť' => E Ť' ∧ InducesTree S (R.project Ť')) Ť
            ∧ Odd (Ť ∩ R.piecesOver (cutEdges u)).card) :=
      weightMass_congr fun Ť => ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2⟩⟩
    have hsub : weightMass (R.liftProb μ) (fun Ť => E Ť ∧ InducesTree S (R.project Ť))
        ≤ weightMass (R.liftProb μ) E :=
      weightMass_mono (R.liftProb_weightNonneg μ) fun Ť h => h.1
    rw [hre]
    exact le_trans hcore (mul_le_mul_of_nonneg_left hsub hcnn)
  linarith

end EdgeRefinement

end TSPGap

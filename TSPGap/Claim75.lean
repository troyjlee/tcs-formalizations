/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BottomGuarantees
import TSPGap.RectangularTransfer

/-!
# KKO21 Claim 7.5

For `u ⊊ U` in the hierarchy and a thinning `v` uniform over an event `E`
rectangular at `U`,

`W_v[δ(u)_T odd] ≤ p · (1 − ε + max(2ε_η, ε²))`

whenever the crossing mass `x(δ(u) ∩ δ(U))` lies in `[ε, 1 − ε]`.

⚠️ Stated **directly in the consumer form**, at the thinning and with no
conditioning on `(δ(u) ∩ δ(U))_T`.  KKO condition on that count and then quote
"for any integer `k ≥ 0`"; the conditioning is unnecessary here because
rectangularity already factors the inside law off, and carrying it would force
a per-layer conditional theorem and a division.

The proof is a parity partition and two existing parity bounds:

* `δ(u)_T = D_in + D_out` for `D_in = δ(u) ∩ E(U)` and `D_out = δ(u) ∩ δ(U)`,
  so `δ(u)_T` is odd exactly when the two parities differ.
* `D_in`'s parity is inside-determined and `D_out`'s outside-determined, so
  `IsRectangularAt.weightMass_factor` turns the mass into
  `a · W(E ∧ D_out even) + (1 − a) · W(E ∧ D_out odd)` with
  `a = W_face[D_in odd]` — a mixture, hence at most `max(a, 1 − a) · W(E)`.
* `D_in ≥ 1` almost surely at the face (`one_le_card_din`), and its mean lies
  in `[1 + ε, 2 − ε + 2ε_η]`.  `oddCount_le` bounds `a` above and `oddCount_ge`
  bounds it below — no new point-mass export is needed.

The only new analytic input is the elementary `(1 − e^{−2ε})/2 ≥ ε − ε²`,
proved from the degree-two Taylor lower bound on `exp` together with
`(1 − t + t²/2)(1 + t + t²/2) = 1 + t⁴/4 ≥ 1`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The elementary exponential bound -/

/-- `1 + t + t²/2 ≤ e^t` for `t ≥ 0`: the degree-two partial sum. -/
theorem one_add_add_sq_div_two_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 3
  have he : ∑ i ∈ Finset.range 3, t ^ i / (Nat.factorial i : ℝ) = 1 + t + t ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [he] at h
  exact h

/-- **`(1 − e^{−2ε})/2 ≥ ε − ε²`**, Claim 7.5's analytic input.  ⚠️ The naive
route through `e^{−t} ≤ 1/(1+t)` is **too weak**: it needs `ε ≥ 1/2`.  The
degree-two partial sum works because `(1 − t + t²/2)(1 + t + t²/2) = 1 + t⁴/4`. -/
theorem sub_sq_le_one_sub_exp_neg_two_mul {ε : ℝ} (hε : 0 ≤ ε) :
    ε - ε ^ 2 ≤ (1 - Real.exp (-2 * ε)) / 2 := by
  have ht : (0:ℝ) ≤ 2 * ε := by linarith
  have hlow : 1 + 2 * ε + (2 * ε) ^ 2 / 2 ≤ Real.exp (2 * ε) :=
    one_add_add_sq_div_two_le_exp ht
  have hpos : (0:ℝ) < 1 + 2 * ε + (2 * ε) ^ 2 / 2 := by nlinarith
  have hexp : Real.exp (-2 * ε) = 1 / Real.exp (2 * ε) := by
    rw [show (-2 : ℝ) * ε = -(2 * ε) by ring, Real.exp_neg]
    ring
  have h1 : Real.exp (-2 * ε) ≤ 1 / (1 + 2 * ε + (2 * ε) ^ 2 / 2) := by
    rw [hexp]
    exact one_div_le_one_div_of_le hpos hlow
  have h2 : 1 / (1 + 2 * ε + (2 * ε) ^ 2 / 2) ≤ 1 - 2 * ε + 2 * ε ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg (ε ^ 2)]
  linarith

/-! ### The inside crossing never vanishes at the tree face -/

/-- At the tree face of `U`, the inside crossing count of `u ⊊ U` is at least
one — `one_le_card_din` without the avoidance layer of
`weightMass_din_eq_zero`. -/
theorem one_le_card_din_treeFace {μ : TreeDist n x} {U u : Finset (Fin n)}
    (hUne : U.Nonempty) (hune : u.Nonempty) (huU : u ⊂ U)
    {T : Finset (Sym2 (Fin n))} (hT : treeFace μ.prob U T ≠ 0) :
    1 ≤ (T ∩ (cutEdges u ∩ internalEdges U)).card := by
  classical
  obtain ⟨hprob, hcost⟩ := faceDist_ne_zero_imp hT
  have hTst := μ.support_spanningTree T hprob
  rw [setCost_indicatorCost] at hcost
  have h1U : 1 ≤ U.card := Finset.card_pos.mpr hUne
  have hcard : (internalEdges U ∩ T).card + 1 = U.card := by
    rw [Finset.inter_comm]
    omega
  exact one_le_card_din ((inducesTreeOn_iff_card hTst U).mpr hcard) hune huU

theorem weightMass_din_treeFace_eq_zero {μ : TreeDist n x} {U u : Finset (Fin n)}
    (hUne : U.Nonempty) (hune : u.Nonempty) (huU : u ⊂ U) :
    weightMass (treeFace μ.prob U)
      (fun T => (T ∩ (cutEdges u ∩ internalEdges U)).card = 0) = 0 := by
  refine weightMass_eq_zero_of_support fun T hT => ?_
  have := one_le_card_din_treeFace hUne hune huU hT
  omega

/-! ### The claim -/

set_option maxHeartbeats 400000 in
-- the face law package, the two parity bounds and the mixture in one chain
/-- **KKO21 Claim 7.5 at `μ.prob`**, the cross-multiplied form the thinning
transfer consumes.  Kept separate from the thinning statement so that the
nested adapter can reuse it at a *different* rectangular event. -/
theorem claim_7_5_core {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {U u : Finset (Fin n)} (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hune : u.Nonempty)
    (huU : u ⊂ U)
    (huniv : u ≠ Finset.univ) (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt U E)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges U, x g) ≤ 1 - ε) :
    weightMass μ.prob (fun T => E T ∧ Odd (T ∩ cutEdges u).card)
      ≤ (1 - ε + max (2 * εη) (ε ^ 2)) * weightMass μ.prob E := by
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
  -- determinacy of the four parity events
  have hDinsub : ∀ g ∈ Din, ∀ w ∈ g, w ∈ U := fun g hg w hw =>
    (mem_internalEdges.mp (Finset.mem_inter.mp hg).2).2 w hw
  have hDoutsub : ∀ g ∈ Dout, ¬ ∀ w ∈ g, w ∈ U := fun g hg =>
    not_forall_mem_of_mem_cutEdges (Finset.mem_inter.mp hg).2
  have hinOdd : InsideDetermined U (fun T => Odd (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Odd X.card)
  have hinEven : InsideDetermined U (fun T => Even (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Even X.card)
  have houtEven : OutsideDetermined U (fun T => Even (T ∩ Dout).card) :=
    outsideDetermined_inter hDoutsub (fun X => Even X.card)
  have houtOdd : OutsideDetermined U (fun T => Odd (T ∩ Dout).card) :=
    outsideDetermined_inter hDoutsub (fun X => Odd X.card)
  -- `δ(u)_T` is odd exactly when the two parities differ
  have hpar : ∀ T : Finset (Sym2 (Fin n)), Odd (T ∩ cutEdges u).card ↔
      ((Odd (T ∩ Din).card ∧ Even (T ∩ Dout).card)
        ∨ (Even (T ∩ Din).card ∧ Odd (T ∩ Dout).card)) := by
    intro T
    have hsp := card_split_of_subcut huU.subset T
    rw [← hDinDef, ← hDoutDef] at hsp
    rw [hsp]
    simp only [Nat.odd_iff, Nat.even_iff]
    omega
  have hA0 : weightMass μ.prob (fun T => E T ∧ Odd (T ∩ cutEdges u).card)
      = weightMass μ.prob (fun T => E T ∧ Odd (T ∩ Din).card ∧ Even (T ∩ Dout).card)
        + weightMass μ.prob (fun T => E T ∧ Even (T ∩ Din).card ∧ Odd (T ∩ Dout).card) := by
    have hor := weightMass_or μ.prob
      (fun T => E T ∧ Odd (T ∩ Din).card ∧ Even (T ∩ Dout).card)
      (fun T => E T ∧ Even (T ∩ Din).card ∧ Odd (T ∩ Dout).card)
    have hand : weightMass μ.prob (fun T =>
        (E T ∧ Odd (T ∩ Din).card ∧ Even (T ∩ Dout).card)
          ∧ (E T ∧ Even (T ∩ Din).card ∧ Odd (T ∩ Dout).card)) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (E T ∧ Odd (T ∩ Din).card ∧ Even (T ∩ Dout).card)
            ∧ (E T ∧ Even (T ∩ Din).card ∧ Odd (T ∩ Dout).card)) = fun _ => False from ?_,
        weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      exact (Nat.not_odd_iff_even.mpr h.2.2.1) h.1.2.1
    rw [hand, add_zero] at hor
    rw [← hor]
    exact weightMass_congr fun T => by rw [hpar T]; tauto
  have hB0 : weightMass μ.prob (fun T => E T ∧ Even (T ∩ Dout).card)
      + weightMass μ.prob (fun T => E T ∧ Odd (T ∩ Dout).card) = weightMass μ.prob E := by
    have hor := weightMass_or μ.prob (fun T => E T ∧ Even (T ∩ Dout).card)
      (fun T => E T ∧ Odd (T ∩ Dout).card)
    have hand : weightMass μ.prob (fun T => (E T ∧ Even (T ∩ Dout).card)
        ∧ (E T ∧ Odd (T ∩ Dout).card)) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) => (E T ∧ Even (T ∩ Dout).card)
          ∧ (E T ∧ Odd (T ∩ Dout).card)) = fun _ => False from ?_, weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      exact (Nat.not_odd_iff_even.mpr h.1.2) h.2.2
    have htrue : weightMass μ.prob (fun T => (E T ∧ Even (T ∩ Dout).card)
        ∨ (E T ∧ Odd (T ∩ Dout).card)) = weightMass μ.prob E := by
      refine weightMass_congr fun T => ?_
      rcases Nat.even_or_odd (T ∩ Dout).card with he | ho
      · exact ⟨fun h => h.elim (fun k => k.1) (fun k => k.1), fun h => Or.inl ⟨h, he⟩⟩
      · exact ⟨fun h => h.elim (fun k => k.1) (fun k => k.1), fun h => Or.inr ⟨h, ho⟩⟩
    rw [hand, add_zero, htrue] at hor
    exact hor.symm
  -- factor the inside parity off each piece
  have haEven : weightMass (treeFace μ.prob U) (fun T => Even (T ∩ Din).card) = 1 - a := by
    have hnot := weightMass_not (treeFace μ.prob U) (fun T => Odd (T ∩ Din).card)
    rw [hFlaw.tot] at hnot
    rw [← hnot]
    exact weightMass_congr fun T => by rw [Nat.not_odd_iff_even]
  have hf1 := hE.weightMass_factor μ hμ hUne hmass hinOdd houtEven
  have hf2 := hE.weightMass_factor μ hμ hUne hmass hinEven houtOdd
  rw [haEven] at hf2
  rw [hA0, hf1, hf2, ← hB0]
  -- a mixture is at most its larger weight
  have hn1 : 0 ≤ weightMass μ.prob (fun T => E T ∧ Even (T ∩ Dout).card) :=
    weightMass_nonneg μ.weightNonneg _
  have hn2 : 0 ≤ weightMass μ.prob (fun T => E T ∧ Odd (T ∩ Dout).card) :=
    weightMass_nonneg μ.weightNonneg _
  have hac : a ≤ 1 - ε + max (2 * εη) (ε ^ 2) := by
    have := le_max_right (2 * εη) (ε ^ 2); linarith
  have hac' : 1 - a ≤ 1 - ε + max (2 * εη) (ε ^ 2) := by
    have := le_max_left (2 * εη) (ε ^ 2); linarith
  nlinarith [mul_le_mul_of_nonneg_right hac hn1, mul_le_mul_of_nonneg_right hac' hn2]

/-- **KKO21 Claim 7.5**, in the consumer form: at a thinning uniform over an
event rectangular at `U`, the odd mass of `δ(u)_T` is at most
`p · (1 − ε + max(2ε_η, ε²))`. -/
theorem claim_7_5 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {U u : Finset (Fin n)} (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hune : u.Nonempty)
    (huU : u ⊂ U)
    (huniv : u ≠ Finset.univ) (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt U E)
    {v : Finset (Sym2 (Fin n)) → ℝ} {p : ℝ} (hv : IsUniformThinning μ.prob v E p)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges U, x g) ≤ 1 - ε) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) :=
  hv.weightMass_le μ.weightNonneg
    (claim_7_5_core hx hμ hεη hεηcap hUne hU0 hune huU huniv hUcut hucut hE hε0 hclo hchi)

/-! ### The nested adapter -/

set_option maxHeartbeats 400000 in
-- the split, the core at the restricted event, and the failure term
/-- **The nested transfer**, for Lemma 7.3's Case 3.  The thinning is
conditioned at a *higher* ancestor `U`, but Claim 7.5 is wanted at `S = p(u)`.
This is the paper's step, packaged directly: `S` failing to be a tree costs at
most `p · ε_η/2`, and on the `S`-tree part the core applies at `S`.

⚠️ `hnest` is a **hypothesis**, not derived.  An outside-determined `Q` does
descend from `U` to `S ⊆ U` — `outsidePart U T = outsidePart U (outsidePart S T)`
— but `E`'s other clause `InducesTree U` reads edges *inside* `S`, so
`E ∧ InducesTree S` is not rectangular at `S` for free.  It is nonetheless
true: given `S` induces a tree, whether `U` does depends only on
`outsidePart S T`, since the count splits as `(|S| − 1) + |T ∩ (E(U) ∖ E(S))|`
and connectivity of `U` reduces to connectivity with `S` contracted.  That is a
contraction argument of the size of `InducesTreeOn.glue`, so it is left to the
caller rather than silently assumed. -/
theorem claim_7_5_nested {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {S u : Finset (Fin n)} (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S) (hune : u.Nonempty)
    (huS : u ⊂ S)
    (huniv : u ≠ Finset.univ) (hScut : cutSum x S ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {E : Finset (Sym2 (Fin n)) → Prop}
    (hnest : IsRectangularAt S (fun T => E T ∧ InducesTree S T))
    {v : Finset (Sym2 (Fin n)) → ℝ} {p : ℝ} (hv : IsUniformThinning μ.prob v E p)
    (hfail : weightMass v (fun T => ¬ InducesTree S T) ≤ p * (εη / 2))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges S, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges S, x g) ≤ 1 - ε) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) + p * (εη / 2) := by
  classical
  have hcnn : 0 ≤ 1 - ε + max (2 * εη) (ε ^ 2) := by
    have h1 : ε ≤ 1 - ε := le_trans hclo hchi
    have h2 : (0:ℝ) ≤ max (2 * εη) (ε ^ 2) := le_trans (by positivity) (le_max_right _ _)
    linarith
  -- split off the trees on which `S` fails
  have hsplit : weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      ≤ weightMass v (fun T => Odd (T ∩ cutEdges u).card ∧ InducesTree S T)
        + weightMass v (fun T => ¬ InducesTree S T) := by
    have hor := weightMass_or v (fun T => Odd (T ∩ cutEdges u).card ∧ InducesTree S T)
      (fun T => ¬ InducesTree S T)
    have hmono : weightMass v (fun T => Odd (T ∩ cutEdges u).card)
        ≤ weightMass v (fun T => (Odd (T ∩ cutEdges u).card ∧ InducesTree S T)
            ∨ ¬ InducesTree S T) := by
      refine weightMass_mono hv.nonneg fun T h => ?_
      by_cases hg : InducesTree S T
      · exact Or.inl ⟨h, hg⟩
      · exact Or.inr hg
    have hand : 0 ≤ weightMass v (fun T => (Odd (T ∩ cutEdges u).card ∧ InducesTree S T)
        ∧ ¬ InducesTree S T) := weightMass_nonneg hv.nonneg _
    linarith
  -- the `S`-tree part, through the core at the restricted event
  have hmain : weightMass v (fun T => Odd (T ∩ cutEdges u).card ∧ InducesTree S T)
      ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) := by
    refine hv.weightMass_le μ.weightNonneg ?_
    have hcore := claim_7_5_core hx hμ hεη hεηcap hSne hS0 hune huS huniv hScut hucut
      hnest hε0 hclo hchi
    have hre : weightMass μ.prob
        (fun T => E T ∧ Odd (T ∩ cutEdges u).card ∧ InducesTree S T)
        = weightMass μ.prob
          (fun T => (fun T' => E T' ∧ InducesTree S T') T ∧ Odd (T ∩ cutEdges u).card) :=
      weightMass_congr fun T => ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2⟩⟩
    have hsub : weightMass μ.prob (fun T => E T ∧ InducesTree S T) ≤ weightMass μ.prob E :=
      weightMass_mono μ.weightNonneg fun T h => h.1
    rw [hre]
    exact le_trans hcore (mul_le_mul_of_nonneg_left hsub hcnn)
  linarith

end TSPGap

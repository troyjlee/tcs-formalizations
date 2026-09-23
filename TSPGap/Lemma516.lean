/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NestedChain
import TSPGap.Lemma516Kernel
import TSPGap.MatchingInputs

/-!
# KKO21 Lemma 5.16, and `bad_up`

**Lemma 5.16.** For children `u ≠ v` of a hierarchy cut `S` with
`x(δ↑(u)) ≥ 1/2 + 9ε₂`, the bundle `E(u,v)` is 2-2 good (Definition 5.13).

The nested law `ν = μ | u, v, W = S ∖ u, S trees` (`NestedChain.lean`) is fed
to the analytic kernel with `A = δ↑(u)`, `B = δ(v)`:

* `A` and `B` are disjoint (`δ(u) ∩ δ(v) = E(u,v)` lies inside `S`, `A` outside);
* `B_T ≥ 1` on the support (a spanning tree crosses `v`);
* the means are `NestedData`'s `up_*`, `cutv_*`;

so `P_ν[A_T = 1 ∧ B_T = 2] ≥ 6ε₂`.  On the support `E(u, W)_T = 1` (`S` is a
tree on `u`, `W` trees), so `δ(u)_T = A_T + 1`, and the event is
`δ(u)_T = δ(v)_T = 2`.  The nested face has unnormalized mass at least
`1/2 + 9ε₂ − 5ε_η/2 ≥ 1/2`, and sits inside the two-atom face of `u, v`; the
bridge `isGoodBundle_of_costFace` (the general-cost form of
`isGoodBundle_of_face`) then gives Definition 5.13's `3ε₂ ≤ 6ε₂ · (1/2)`.

`lemma_5_16_bad_up` is the contrapositive in the exact form consumed by
`MatchingInputs.of_bad_up`, and `Hierarchy.matchingInputs` closes the package.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The bridge for a general-cost face -/

/-- **The bridge, general cost**: `c₀` in a cost face of mass at least `m₀`
lying inside the two-atom face gives Definition 5.13's `3ε₂` when
`3ε₂ ≤ c₀ m₀`. -/
theorem isGoodBundle_of_costFace (μ : TreeDist n x)
    {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {ε₂ : ℝ} {c : Sym2 (Fin n) → ℕ} {b : ℕ}
    (hface : ∀ T, μ.prob T ≠ 0 → setCost c T = b → InducesTreeOn u T ∧ InducesTreeOn v T)
    {m₀ c₀ : ℝ} (hm₀ : m₀ ≤ totalMass (faceWeight μ.prob c b))
    (hmass : 0 < totalMass (faceWeight μ.prob c b))
    (h : c₀ ≤ weightMass (faceDist μ.prob c b)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (hc₀ : 0 ≤ c₀) (hε : 3 * ε₂ ≤ c₀ * m₀) :
    IsGoodBundle μ ε₂ u v := by
  right
  have hune := H.child_nonempty hu
  have hvne := H.child_nonempty hv
  have hduv := H.children_disjoint hu hv huv
  have hnn := μ.weightNonneg
  have htot := totalMass_treeDist μ
  set Q : Finset (Sym2 (Fin n)) → Prop :=
    fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 with hQ
  rw [weightMass_faceDist, le_div_iff₀ hmass] at h
  have hW : weightMass (faceWeight μ.prob c b) Q
      ≤ weightMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
        (twoAtomBudget u v)) Q := by
    rw [weightMass_faceWeight, weightMass_face]
    refine weightMass_mono_of_support hnn fun T hT ⟨hQT, hf⟩ => ⟨hQT, ?_⟩
    have hT' := μ.support_spanningTree T hT
    exact (card_inter_twoAtom_eq_iff hT' hune hvne hduv).mpr (hface T hT hf)
  have hM2le : totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) ≤ 1 := by
    rw [totalMass_face]; exact weightMass_le_one hnn htot _
  have hW2 := weightMass_le_totalMass (weightNonneg_faceWeight hnn
    (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v)) Q
  have hcm : c₀ * m₀ ≤ weightMass (faceWeight μ.prob c b) Q :=
    le_trans (mul_le_mul_of_nonneg_left hm₀ hc₀) h
  have hWnn := weightMass_nonneg (weightNonneg_faceWeight hnn (indicatorCost (twoAtomInternal u v))
    (twoAtomBudget u v)) Q
  unfold lemmaA1Tau
  rw [weightMass_faceDist]
  by_cases hM2 : totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) = 0
  · -- the two-atom face is massless: the normalized mass is `0`, and so is `3ε₂`
    rw [hM2, div_zero]
    linarith
  · have hM2pos : 0 < totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
        (twoAtomBudget u v)) :=
      lt_of_le_of_ne (totalMass_nonneg (weightNonneg_faceWeight hnn _ _)) (Ne.symm hM2)
    rw [le_div_iff₀ hM2pos]
    nlinarith

/-! ### Geometry of `δ↑(u)`, `δ(v)`, `E(u, S ∖ u)` -/

/-- `δ↑(u)` and `δ(v)` are disjoint for children `u ≠ v` of `S`: an edge of
both would lie between `u` and `v`, inside `S`. -/
theorem upEdges_disjoint_cutEdges_child {S u v : Finset (Fin n)} (huS : u ⊆ S) (hvS : v ⊆ S)
    (huv : Disjoint u v) : Disjoint (upEdges S u) (cutEdges v) := by
  refine Finset.disjoint_left.mpr fun e he hv => ?_
  obtain ⟨hS, hu⟩ := Finset.mem_inter.mp he
  have hb : e ∈ betweenEdges u v := by
    rw [← cutEdges_inter_cutEdges huv]; exact Finset.mem_inter.mpr ⟨hu, hv⟩
  obtain ⟨a, ha, b, hb', rfl⟩ := mem_betweenEdges_iff.mp hb
  rcases mk_mem_cutEdges_iff.mp hS with ⟨-, hbS⟩ | ⟨-, haS⟩
  · exact hbS (hvS hb')
  · exact haS (huS ha)

/-- `δ(u) ∖ δ(S) = E(u, S ∖ u)` for `u ⊆ S`. -/
theorem cutEdges_sdiff_cutEdges_eq_between {S u : Finset (Fin n)} (huS : u ⊆ S) :
    cutEdges u \ cutEdges S = betweenEdges u (S \ u) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [Finset.mem_sdiff, mk_mem_cutEdges_iff, mem_betweenEdges_iff]
    constructor
    · rintro ⟨hu, hS⟩
      rcases hu with ⟨hau, hbu⟩ | ⟨hbu, hau⟩
      · refine ⟨a, hau, b, ⟨?_, hbu⟩, rfl⟩
        by_contra hbS
        exact hS (Or.inl ⟨huS hau, hbS⟩)
      · refine ⟨b, hbu, a, ⟨?_, hau⟩, Sym2.eq_swap⟩
        by_contra haS
        exact hS (Or.inr ⟨huS hbu, haS⟩)
    · rintro ⟨a', ha', b', hb', h⟩
      obtain ⟨hb'S, hb'u⟩ := hb'
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Or.inl ⟨ha', hb'u⟩, fun h => by
          rcases h with ⟨-, h⟩ | ⟨-, h⟩
          · exact h hb'S
          · exact h (huS ha')⟩
      · exact ⟨Or.inr ⟨ha', hb'u⟩, fun h => by
          rcases h with ⟨-, h⟩ | ⟨-, h⟩
          · exact h (huS ha')
          · exact h hb'S⟩

/-- On the nested support, `δ(u)_T = δ↑(u)_T + 1`. -/
theorem card_cut_eq_up_add_one {S u : Finset (Fin n)} (huS : u ⊆ S) (hune : u.Nonempty)
    (hWne : (S \ u).Nonempty) {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    (hu : InducesTreeOn u T) (hW : InducesTreeOn (S \ u) T) (hS : InducesTreeOn S T) :
    (T ∩ cutEdges u).card = (T ∩ upEdges S u).card + 1 := by
  have hsplit : (T ∩ cutEdges u).card
      = (T ∩ (cutEdges S ∩ cutEdges u)).card + (T ∩ (cutEdges u \ cutEdges S)).card := by
    have h : cutEdges u = (cutEdges S ∩ cutEdges u) ∪ (cutEdges u \ cutEdges S) := by
      ext e; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    conv_lhs => rw [h]
    exact card_inter_union_of_disjoint (Finset.disjoint_left.mpr fun e h1 h2 =>
      (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1) T
  have hbundle : (T ∩ (cutEdges u \ cutEdges S)).card = 1 := by
    rw [cutEdges_sdiff_cutEdges_eq_between huS]
    have hduW : Disjoint u (S \ u) := Finset.disjoint_sdiff
    have hunion : u ∪ (S \ u) = S := Finset.union_sdiff_of_subset huS
    have hSW : InducesTreeOn (u ∪ (S \ u)) T := by rw [hunion]; exact hS
    have := (inducesTreeOn_union_iff_bundle_present (w := fun _ => (1 : ℝ))
      (supportComplete_betweenEdges _ u (S \ u)) (by norm_num) hT hu.2 hW.2 hduW).mp hSW
    exact this
  unfold upEdges
  omega

/-! ### Lemma 5.16 -/

/-- **KKO21 Lemma 5.16**: if `x(δ↑(u)) ≥ 1/2 + 9ε₂`, every bundle at `u` is
2-2 good. -/
theorem lemma_5_16 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S u v : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 < ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hup : 1 / 2 + 9 * ε₂ ≤ upSum x S u) : IsGoodBundle μ ε₂ u v := by
  classical
  have D := H.nestedData hx μ hμ hS hu hv huv hεη hε₂.le hε₂cap hεηsq hup
  set W := S \ u with hW
  have hune := H.child_nonempty hu
  have hvne := H.child_nonempty hv
  have huS := H.child_subset hu
  have hvS := H.child_subset hv
  have hduv := H.children_disjoint hu hv huv
  have hvW : v ⊆ W := fun a ha =>
    Finset.mem_sdiff.mpr ⟨hvS ha, fun hau => Finset.disjoint_left.mp hduv hau ha⟩
  have hWne : W.Nonempty := hvne.mono hvW
  have hSne := (H.nearMin S hS).nonempty
  have hvproper := (H.child_nearMin hv).ne_univ
  -- Lemma 2.7: `x(δ↑(u)) ≤ 1 + ε_η`
  have hup1 : upSum x S u ≤ 1 + εη :=
    upSum_le_one_add hx (H.avoids S hS) hu.2.2.1 hune (H.nearMin S hS).cut_le
      (H.child_nearMin hu).cut_le
  -- the kernel's inputs
  have hAB : Disjoint (upEdges S u) (cutEdges v) := upEdges_disjoint_cutEdges_child huS hvS hduv
  have hbase : ∀ T, nestedLaw μ u v W S T ≠ 0 → 1 ≤ (T ∩ cutEdges v).card := by
    intro T hT
    obtain ⟨-, hsp, -, -, -, -⟩ := D.supp T hT
    exact one_le_card_cut_inter_atom hsp hvne hvproper
  have hker := lemma_5_16_kernel D.law.st D.law.rank D.law.nn D.law.tot hAB hbase hε₂ hε₂cap
    hεη hεηsq (by linarith [D.up_ge]) (by linarith [D.up_le]) D.cutv_ge D.cutv_le
  -- the event is `δ(u)_T = δ(v)_T = 2` on the support
  have hev : weightMass (nestedLaw μ u v W S)
      (fun T => (T ∩ upEdges S u).card = 1 ∧ (T ∩ cutEdges v).card = 2)
      ≤ weightMass (nestedLaw μ u v W S)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) := by
    refine weightMass_mono_of_support D.law.nn fun T hT ⟨h1, h2⟩ => ⟨?_, h2⟩
    obtain ⟨-, hsp, hu', -, hW', hS'⟩ := D.supp T hT
    rw [card_cut_eq_up_add_one huS hune hWne hsp hu' hW' hS', h1]
  -- the bridge to Definition 5.13
  refine isGoodBundle_of_costFace μ H hu hv huv (c := nestedCost u v W S)
    (b := nestedBudget u v W S) (fun T hT hc => ?_) D.massGe D.mass (hker.trans hev)
    (by linarith) ?_
  · obtain ⟨h1, h2, -, -⟩ :=
      (setCost_nestedCost_eq_iff (μ.support_spanningTree T hT) hune hvne hWne hSne).mp hc
    exact ⟨h1, h2⟩
  · nlinarith

/-- **`bad_up` for `MatchingInputs`**: an atom incident to a bad bundle has
`x(δ↑(u)) ≤ 1/2 + 9ε₂`. -/
theorem lemma_5_16_bad_up {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S : Finset (Fin n)}
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
      ¬ IsGoodBundle μ ε₂ u u' → upSum x S u ≤ 1 / 2 + 9 * ε₂ := by
  intro u hu u' hu' huu' hbad
  rcases eq_or_lt_of_le hε₂ with h0 | hpos
  · -- at `ε₂ = 0` every bundle is good
    exfalso
    apply hbad
    right
    rw [← h0, mul_zero]
    have hnn : WeightNonneg (lemmaA1Tau μ.prob u u') := fun T => by
      unfold lemmaA1Tau faceDist
      exact div_nonneg (weightNonneg_faceWeight μ.weightNonneg _ _ T)
        (totalMass_nonneg (weightNonneg_faceWeight μ.weightNonneg _ _))
    exact weightMass_nonneg hnn _
  · by_contra hc
    push_neg at hc
    have hu_c := H.mem_children.mp hu
    exact hbad (lemma_5_16 hx μ hμ H hu_c.2.1 hu_c (H.mem_children.mp hu') huu' hεη hpos hε₂cap
      hεηsq hc.le)

/-- **The matching lemma's inputs, discharged.** -/
theorem Hierarchy.matchingInputs {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S : Finset (Fin n)} {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2) : MatchingInputs H μ S ε₂ :=
  MatchingInputs.of_bad_up hx μ hμ H hεη hε₂ hε₂cap hεηsq
    (lemma_5_16_bad_up hx μ hμ H hεη hε₂ hε₂cap hεηsq)

end TSPGap

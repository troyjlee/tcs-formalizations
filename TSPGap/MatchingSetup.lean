/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Theorem528Defs
import TSPGap.TreeDistBridge

/-!
# The LP layer of KKO21 §6 (the matching lemma's inputs)

For a cut `S` of the hierarchy with atoms `A(S) = H.children S`, KKO's
matching lemma (Lemma 6.2) is a max-flow/min-cut argument whose min-cut side
reduces to a Hall condition on sets of atoms `Q ⊆ A(S)`: the sink capacity of
`Q` is at most `(1 + α)` times the good mass of the bundles touching `Q`.
This file proves the purely LP-level facts that condition consumes:

* `upSum x S u = x(δ↑(u)) = x(δ(u) ∩ δ(S))`, `arrowSum x S u = x(δ→(u))`;
* **Lemma 2.7**: `x(δ↑(u)) ≤ 1 + ε` (`upSum_le_one_add`);
* the cut of a disjoint union of atoms
  (`cutSum_biUnion_eq`): `x(δ(⋃Q)) = ∑_{u∈Q} x(δ(u)) − I(Q)` with
  `I(Q) = ∑_{u∈Q} ∑_{u'∈Q∖u} x(E(u,u'))` the ordered internal mass;
* `δ↑` is additive over disjoint atoms (`sum_upSum_eq`);
* **Lemma 6.3** in the form the network needs (`touchSum_ge`): the mass of the
  bundles touching a proper subfamily `Q` of atoms — bundles between two atoms
  of `Q` counted once — is at least `½ ∑_{u∈Q} x(δ(u)) − ε/2 ≥ |Q| − ε/2`;
* **Eq. (29)'s base**: `x(E→(S)) = ½(∑_u x(δ(u)) − x(δ(S))) ≥ |A(S)| − 1 − ε/2`
  (`topSum_eq`, `topSum_ge`).

The bundle masses are handled as the ordered double sum
`∑_{u} ∑_{u' ≠ u} pairSum x u u'`, so no `Sym2`-of-atoms bookkeeping is
needed; each unordered bundle appears twice, which is exactly how the network
rows are indexed.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### `δ↑`, `δ→` -/

/-- `δ↑(u) := δ(u) ∩ δ(S)`, the edges of `u` going higher. -/
def upEdges (S u : Finset (Fin n)) : Finset (Sym2 (Fin n)) := cutEdges S ∩ cutEdges u

/-- `x(δ↑(u))`. -/
noncomputable def upSum (x : Sym2 (Fin n) → ℝ) (S u : Finset (Fin n)) : ℝ :=
  ∑ e ∈ upEdges S u, x e

/-- `x(δ→(u)) = x(δ(u)) − x(δ↑(u))`. -/
noncomputable def arrowSum (x : Sym2 (Fin n) → ℝ) (S u : Finset (Fin n)) : ℝ :=
  cutSum x u - upSum x S u

theorem upSum_nonneg (hx : ∀ e, 0 ≤ x e) (S u : Finset (Fin n)) : 0 ≤ upSum x S u :=
  Finset.sum_nonneg fun e _ => hx e

theorem upSum_le_cutSum (hx : ∀ e, 0 ≤ x e) (S u : Finset (Fin n)) :
    upSum x S u ≤ cutSum x u :=
  Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun e _ _ => hx e

/-- **KKO Lemma 2.7**: `x(δ↑(u)) ≤ 1 + ε` for a nonempty proper near-min sub-cut
`u ⊂ S` of a near-min cut `S`. -/
theorem upSum_le_one_add_of_cut_lower {S u : Finset (Fin n)} {ε : ℝ}
    (huS : u ⊂ S) (hlow : 2 ≤ cutSum x (S \ u)) (hS : cutSum x S ≤ 2 + ε)
    (hu : cutSum x u ≤ 2 + ε) : upSum x S u ≤ 1 + ε := by
  have hlp := hlow
  rw [cutSum_sdiff_of_subset x huS.subset] at hlp
  unfold upSum upEdges
  linarith

/-- Lemma 2.7 for the restricted LP: the outer cut avoids the root endpoints. -/
theorem upSum_le_one_add {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {S u : Finset (Fin n)}
    {ε : ℝ} (hS0 : AvoidsRootEdge e₀ S) (huS : u ⊂ S) (hune : u.Nonempty)
    (hS : cutSum x S ≤ 2 + ε) (hu : cutSum x u ≤ 2 + ε) : upSum x S u ≤ 1 + ε := by
  have hne : (S \ u).Nonempty := by
    obtain ⟨a, haS, hau⟩ := Finset.exists_of_ssubset huS
    exact ⟨a, Finset.mem_sdiff.mpr ⟨haS, hau⟩⟩
  have hproper : S \ u ≠ Finset.univ := by
    intro h
    obtain ⟨a, ha⟩ := hune
    have : a ∈ S \ u := by rw [h]; exact Finset.mem_univ a
    exact (Finset.mem_sdiff.mp this).2 ha
  exact upSum_le_one_add_of_cut_lower huS
    (hx.cut_lower (S \ u) hne hproper (hS0.mono Finset.sdiff_subset)) hS hu

/-! ### The cut of a disjoint union of atoms -/

/-- The ordered internal mass of a family of atoms:
`I(Q) = ∑_{u∈Q} ∑_{u'∈Q∖u} x(E(u,u'))`. -/
noncomputable def internalPairSum (x : Sym2 (Fin n) → ℝ) (Q : Finset (Finset (Fin n))) : ℝ :=
  ∑ u ∈ Q, ∑ u' ∈ Q.erase u, pairSum x u u'

/-- `pairSum` is additive over a disjoint family in its first argument. -/
theorem pairSum_biUnion_left (x : Sym2 (Fin n) → ℝ) (Q : Finset (Finset (Fin n)))
    (V : Finset (Fin n)) (hQ : (Q : Set (Finset (Fin n))).PairwiseDisjoint id) :
    pairSum x (Q.biUnion id) V = ∑ u ∈ Q, pairSum x u V := by
  unfold pairSum
  rw [Finset.sum_biUnion hQ]
  rfl

/-- `x(δ(⋃Q)) = ∑_{u∈Q} x(δ(u)) − I(Q)` for pairwise disjoint atoms. -/
theorem cutSum_biUnion_eq (x : Sym2 (Fin n) → ℝ) (Q : Finset (Finset (Fin n)))
    (hQ : (Q : Set (Finset (Fin n))).PairwiseDisjoint id) :
    cutSum x (Q.biUnion id) = ∑ u ∈ Q, cutSum x u - internalPairSum x Q := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    simp [internalPairSum, cutSum, cutEdges]
  | insert a Q ha ih =>
    have hQ' : (Q : Set (Finset (Fin n))).PairwiseDisjoint id :=
      hQ.subset (by simp)
    have hdisj : Disjoint a (Q.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro u hu
      exact hQ (by simp) (by simp [hu]) (fun h => ha (h ▸ hu))
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 := cutSum_add_cutSum_of_disjoint x hdisj
    -- the internal mass of `insert a Q`
    have hI : internalPairSum x (insert a Q)
        = internalPairSum x Q + 2 * pairSum x a (Q.biUnion id) := by
      unfold internalPairSum
      rw [Finset.sum_insert ha, Finset.erase_insert ha]
      have h2 : ∑ u ∈ Q, ∑ u' ∈ (insert a Q).erase u, pairSum x u u'
          = ∑ u ∈ Q, (pairSum x u a + ∑ u' ∈ Q.erase u, pairSum x u u') := by
        refine Finset.sum_congr rfl fun u hu => ?_
        have hau : a ≠ u := fun h => ha (h ▸ hu)
        rw [Finset.erase_insert_of_ne hau, Finset.sum_insert (by
          intro h; exact ha (Finset.mem_of_mem_erase h))]
      rw [h2, Finset.sum_add_distrib]
      have h3 : pairSum x a (Q.biUnion id) = ∑ u ∈ Q, pairSum x a u := by
        rw [pairSum_comm, pairSum_biUnion_left x Q a hQ']
        exact Finset.sum_congr rfl fun u _ => pairSum_comm x u a
      have h4 : ∑ u ∈ Q, pairSum x u a = ∑ u ∈ Q, pairSum x a u :=
        Finset.sum_congr rfl fun u _ => pairSum_comm x u a
      rw [h3, h4]
      ring
    show cutSum x (a ∪ Q.biUnion id) = _
    rw [hI]
    have := ih hQ'
    linarith

/-! ### `δ↑` is additive over disjoint atoms inside `S` -/

/-- `δ(S) ∩ δ(⋃Q) = ⋃_{u∈Q} δ(S) ∩ δ(u)` for atoms `u ⊆ S`. -/
theorem upEdges_biUnion {S : Finset (Fin n)} (Q : Finset (Finset (Fin n)))
    (hQS : ∀ u ∈ Q, u ⊆ S) :
    upEdges S (Q.biUnion id) = Q.biUnion (fun u => upEdges S u) := by
  classical
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [upEdges, Finset.mem_inter, Finset.mem_biUnion, mk_mem_cutEdges_iff, id]
    constructor
    · rintro ⟨hS, hU⟩
      rcases hU with ⟨⟨u, hu, hau⟩, hb⟩ | ⟨⟨u, hu, hbu⟩, ha⟩
      · refine ⟨u, hu, hS, Or.inl ⟨hau, fun hbu => ?_⟩⟩
        rcases hS with ⟨-, hbS⟩ | ⟨-, haS⟩
        · exact hbS (hQS u hu hbu)
        · exact haS (hQS u hu hau)
      · refine ⟨u, hu, hS, Or.inr ⟨hbu, fun hau => ?_⟩⟩
        rcases hS with ⟨-, hbS⟩ | ⟨-, haS⟩
        · exact hbS (hQS u hu hbu)
        · exact haS (hQS u hu hau)
    · rintro ⟨u, hu, hS, hu'⟩
      refine ⟨hS, ?_⟩
      rcases hu' with ⟨hau, hbu⟩ | ⟨hbu, hau⟩
      · refine Or.inl ⟨⟨u, hu, hau⟩, fun ⟨u', hu', hbu'⟩ => ?_⟩
        rcases hS with ⟨-, hbS⟩ | ⟨-, haS⟩
        · exact hbS (hQS u' hu' hbu')
        · exact haS (hQS u hu hau)
      · refine Or.inr ⟨⟨u, hu, hbu⟩, fun ⟨u', hu', hau'⟩ => ?_⟩
        rcases hS with ⟨-, hbS⟩ | ⟨-, haS⟩
        · exact hbS (hQS u hu hbu)
        · exact haS (hQS u' hu' hau')

/-- Disjoint atoms inside `S` have disjoint `δ↑`. -/
theorem upEdges_disjoint {S u u' : Finset (Fin n)} (huS : u ⊆ S) (hu'S : u' ⊆ S)
    (h : Disjoint u u') : Disjoint (upEdges S u) (upEdges S u') := by
  classical
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  induction e using Sym2.ind with
  | h a b =>
    simp only [upEdges, Finset.mem_inter, mk_mem_cutEdges_iff] at he he'
    obtain ⟨hS, hu⟩ := he
    obtain ⟨-, hu'⟩ := he'
    rcases hS with ⟨haS, hbS⟩ | ⟨hbS, haS⟩
    · -- `a ∈ S`, `b ∉ S`: both `u`-memberships and `u'`-memberships are at `a`
      have ha : a ∈ u := by
        rcases hu with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd (huS h) hbS
      have ha' : a ∈ u' := by
        rcases hu' with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd (hu'S h) hbS
      exact Finset.disjoint_left.mp h ha ha'
    · have hb : b ∈ u := by
        rcases hu with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd (huS h) haS
        · exact h
      have hb' : b ∈ u' := by
        rcases hu' with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd (hu'S h) haS
        · exact h
      exact Finset.disjoint_left.mp h hb hb'

/-- `x(δ↑(⋃Q)) = ∑_{u∈Q} x(δ↑(u))` for pairwise disjoint atoms inside `S`. -/
theorem sum_upSum_eq (x : Sym2 (Fin n) → ℝ) {S : Finset (Fin n)} (Q : Finset (Finset (Fin n)))
    (hQS : ∀ u ∈ Q, u ⊆ S) (hQ : (Q : Set (Finset (Fin n))).PairwiseDisjoint id) :
    upSum x S (Q.biUnion id) = ∑ u ∈ Q, upSum x S u := by
  classical
  unfold upSum
  rw [upEdges_biUnion Q hQS, Finset.sum_biUnion]
  intro u hu u' hu' huu'
  exact upEdges_disjoint (hQS u hu) (hQS u' hu') (hQ hu hu' huu')

/-! ### The atoms of a cut -/

namespace Hierarchy

variable {e₀ : RootEdge n} {ε : ℝ} (H : Hierarchy x e₀ ε)

theorem children_pairwiseDisjoint (S : Finset (Fin n)) :
    ((H.children S : Finset (Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint id :=
  fun a ha b hb hab =>
    H.children_disjoint (H.mem_children.mp ha) (H.mem_children.mp hb) hab

theorem children_subset {S u : Finset (Fin n)} (hu : u ∈ H.children S) : u ⊆ S :=
  H.child_subset (H.mem_children.mp hu)

/-- The atoms of a cut with at least one child cover it. -/
theorem biUnion_children_eq {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hne : (H.children S).Nonempty) : (H.children S).biUnion id = S := by
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨u, hu, hv⟩
    exact H.children_subset hu hv
  · intro hv
    rcases H.union_children S hS v hv with ⟨a, ha, hva⟩ | hnone
    · exact ⟨a, H.mem_children.mpr ha, hva⟩
    · obtain ⟨u, hu⟩ := hne
      exact absurd (H.mem_children.mp hu) (hnone u)

/-- `x(δ→(u)) = ∑_{u' sibling} x(E(u,u'))`. -/
theorem arrowSum_eq_sum {S u : Finset (Fin n)} (hu : IsChildOf H.cuts u S) :
    arrowSum x S u = ∑ u' ∈ H.siblings S u, pairSum x u u' := by
  unfold arrowSum upSum upEdges
  exact H.cutSum_arrow_eq_sum hu

/-- The mass of the bundles touching a family `Q` of atoms, each unordered
bundle counted once: `∑_{u∈Q} x(δ→(u)) − I(Q)/2`. -/
noncomputable def touchSum (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n))
    (Q : Finset (Finset (Fin n))) : ℝ :=
  ∑ u ∈ Q, arrowSum x S u - internalPairSum x Q / 2

/-- **KKO Lemma 6.3** (first inequality): for a proper subfamily `Q` of the
atoms of a near-min cut `S`, the bundles touching `Q` carry at least
`½ ∑_{u∈Q} x(δ(u)) − ε/2`. -/
theorem touchSum_ge (hx : IsRestrictedLP e₀ x) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) (hQne : Q ≠ H.children S) :
    (∑ u ∈ Q, cutSum x u) / 2 - ε / 2 ≤ touchSum x S Q := by
  classical
  have hpd : (Q : Set (Finset (Fin n))).PairwiseDisjoint id :=
    (H.children_pairwiseDisjoint S).subset (by exact_mod_cast hQ)
  have hQS : ∀ u ∈ Q, u ⊆ S := fun u hu => H.children_subset (hQ hu)
  set U := Q.biUnion id with hU
  have hUS : U ⊆ S := Finset.biUnion_subset.mpr fun u hu => hQS u hu
  -- an atom outside `Q` sits inside `S ∖ U`
  obtain ⟨a, haC, haQ⟩ : ∃ a ∈ H.children S, a ∉ Q := by
    by_contra hcon
    push_neg at hcon
    exact hQne (Finset.Subset.antisymm hQ hcon)
  have hane := H.child_nonempty (H.mem_children.mp haC)
  have haU : Disjoint a U := by
    rw [hU, Finset.disjoint_biUnion_right]
    intro u hu
    exact H.children_disjoint (H.mem_children.mp haC) (H.mem_children.mp (hQ hu))
      (fun h => haQ (h ▸ hu))
  have hne : (S \ U).Nonempty := by
    obtain ⟨v, hv⟩ := hane
    exact ⟨v, Finset.mem_sdiff.mpr ⟨H.children_subset haC hv,
      fun h => Finset.disjoint_left.mp haU hv h⟩⟩
  have hproper : S \ U ≠ Finset.univ := by
    intro h
    exact (H.nearMin S hS).ne_univ (Finset.eq_univ_of_forall fun v => by
      have : v ∈ S \ U := by rw [h]; exact Finset.mem_univ v
      exact (Finset.mem_sdiff.mp this).1)
  have hlp := hx.cut_lower (S \ U) hne hproper ((H.avoids S hS).mono Finset.sdiff_subset)
  rw [cutSum_sdiff_of_subset x hUS] at hlp
  have hScut := (H.nearMin S hS).cut_le
  have hcutU := cutSum_biUnion_eq x Q hpd
  have hup := sum_upSum_eq x Q hQS hpd
  unfold touchSum arrowSum
  rw [Finset.sum_sub_distrib, ← hup]
  unfold upSum upEdges
  rw [← hU] at hcutU ⊢
  linarith

/-- Lemma 6.3's second inequality: `x(δ(u)) ≥ 2` for every atom, so the
touching mass is at least `|Q| − ε/2`. -/
theorem touchSum_ge_card (hx : IsRestrictedLP e₀ x) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) (hQne : Q ≠ H.children S) :
    (Q.card : ℝ) - ε / 2 ≤ touchSum x S Q := by
  have h1 := H.touchSum_ge hx hS hQ hQne
  have h2 : (Q.card : ℝ) * 2 ≤ ∑ u ∈ Q, cutSum x u := by
    have := Finset.card_nsmul_le_sum Q (fun u => cutSum x u) 2 fun u hu =>
      H.child_two_le_cutSum hx (H.mem_children.mp (hQ hu))
    rw [nsmul_eq_mul] at this
    exact this
  linarith

/-- **`x(E→(S))`**: the mass of all top bundles of `S`, each counted once. -/
noncomputable def topSum (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  touchSum x S (H.children S)

/-- `x(E→(S)) = ½ (∑_{u∈A(S)} x(δ(u)) − x(δ(S)))`. -/
theorem topSum_eq {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hne : (H.children S).Nonempty) :
    H.topSum x S = ((∑ u ∈ H.children S, cutSum x u) - cutSum x S) / 2 := by
  classical
  have hpd := H.children_pairwiseDisjoint S
  have hQS : ∀ u ∈ H.children S, u ⊆ S := fun u hu => H.children_subset hu
  have hcutU := cutSum_biUnion_eq x (H.children S) hpd
  have hup := sum_upSum_eq x (H.children S) hQS hpd
  rw [H.biUnion_children_eq hS hne] at hcutU hup
  have hupS : upSum x S S = cutSum x S := by
    unfold upSum upEdges cutSum
    rw [Finset.inter_self]
  unfold topSum touchSum arrowSum
  rw [Finset.sum_sub_distrib, ← hup, hupS]
  linarith

/-- **Eq. (29)'s base**: `x(E→(S)) ≥ |A(S)| − 1 − ε/2`. -/
theorem topSum_ge (hx : IsRestrictedLP e₀ x) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hne : (H.children S).Nonempty) :
    ((H.children S).card : ℝ) - 1 - ε / 2 ≤ H.topSum x S := by
  rw [H.topSum_eq hS hne]
  have h2 : ((H.children S).card : ℝ) * 2 ≤ ∑ u ∈ H.children S, cutSum x u := by
    have := Finset.card_nsmul_le_sum (H.children S) (fun u => cutSum x u) 2 fun u hu =>
      H.child_two_le_cutSum hx (H.mem_children.mp hu)
    rw [nsmul_eq_mul] at this
    exact this
  have hScut := (H.nearMin S hS).cut_le
  linarith

end Hierarchy

end TSPGap

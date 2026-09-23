/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic
import TSPGap.Polygon
import TSPGap.Components

/-!
# Rooted cuts and rooted crossing components (KKO22 §4.2)

KKO22 §4.2 opens by fixing an orientation:

> All statements in the previous section do not depend on which side of each
> diagonal we consider.  The ambiguity on the sides of the cut considered makes
> it difficult to define a consistent orientation on the polygon […].
> Motivated by this, we identify every cut with the side that does not contain
> `u₀, v₀`.

Their `N_η ⊆ 2^{V ∖ {u₀,v₀}}` is therefore a family of *oriented* cuts.  The
development so far has taken `IsCrossingComponent` over arbitrary near-minimum
vertex subsets, with no orientation — and the first half of this file shows
that is not a harmless simplification but an inconsistency: **a crossing
component in the unrooted sense always contains both sides of each of its
cuts**, and no `PolygonRep` can exist over such a family.

The second half introduces the rooted notions the rest of the development
should be built on, and the one-line fact that repairs the damage: a rooted
component contains at most one side of each cut.

The payoff of the orientation is immediate — KKO22's Fact 4.7, that for cuts
avoiding `u₀, v₀` the fourth crossing condition `A ∪ B ≠ V` is automatic.  In
the unrooted development that condition had to be bought from a `root` field
of `PolygonRep`; here it is a theorem about the cuts themselves.
-/

namespace TSPGap

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ}

/-! ### The unrooted encoding is inconsistent

Three steps: crossing is invariant under complementing an argument, so is
near-minimality, so `maximal` drags in the complement of every cut that
crosses something.  A `PolygonRep`'s root atom then has to avoid both sides of
a cut, and it is nonempty. -/

/-- **Crossing is invariant under complementing an argument.**  The four
conditions permute: `Aᶜ ∩ B` is fed by `B ∖ A`, `Aᶜ ∖ B` by `A ∪ B ≠ V`,
`B ∖ Aᶜ` by `A ∩ B`, and `Aᶜ ∪ B ≠ V` by `A ∖ B`. -/
theorem Crossing.compl_left {A B : Finset (Fin n)} (h : Crossing A B) :
    Crossing Aᶜ B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := h3
    rw [Finset.mem_sdiff] at hv
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hv.2, hv.1⟩⟩
  · obtain ⟨v, hv⟩ : ∃ v : Fin n, v ∉ A ∪ B := by
      by_contra hcon
      push Not at hcon
      exact h4 (Finset.eq_univ_iff_forall.mpr hcon)
    rw [Finset.mem_union] at hv
    push Not at hv
    exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hv.1, hv.2⟩⟩
  · obtain ⟨v, hv⟩ := h1
    rw [Finset.mem_inter] at hv
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hv.2, fun hc => (Finset.mem_compl.mp hc) hv.1⟩⟩
  · intro hc
    obtain ⟨v, hv⟩ := h2
    rw [Finset.mem_sdiff] at hv
    have : v ∈ Aᶜ ∪ B := hc ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp this with h' | h'
    · exact (Finset.mem_compl.mp h') hv.1
    · exact hv.2 h'

/-- Near-minimality is invariant under complementation: `δ(S) = δ(Sᶜ)`. -/
theorem IsNearMinCut.compl {S : Finset (Fin n)} (h : IsNearMinCut x η S) :
    IsNearMinCut x η Sᶜ where
  nonempty := compl_nonempty_of_ne_univ h.ne_univ
  ne_univ := compl_ne_univ_of_nonempty h.nonempty
  cut_le := by rw [cutSum_compl]; exact h.cut_le

/-- **A crossing component contains both sides of any cut that crosses.**
`Sᶜ` is a near-minimum cut crossing `T ∈ 𝒞`, so `maximal` puts it in `𝒞`. -/
theorem IsCrossingComponent.compl_mem {𝒞 : Finset (Finset (Fin n))}
    (hC : IsCrossingComponent x η 𝒞) {S T : Finset (Fin n)} (hS : S ∈ 𝒞)
    (hT : T ∈ 𝒞) (hcr : Crossing S T) : Sᶜ ∈ 𝒞 :=
  hC.maximal Sᶜ (hC.nearMin S hS).compl ⟨T, hT, hcr.compl_left⟩

/-- A component with two members has a crossing pair: the connecting path has
at least one step. -/
theorem IsCrossingComponent.exists_crossing_of_one_lt_card
    {𝒞 : Finset (Finset (Fin n))} (hC : IsCrossingComponent x η 𝒞)
    (hns : 2 ≤ 𝒞.card) : ∃ S ∈ 𝒞, ∃ T ∈ 𝒞, Crossing S T := by
  obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < 𝒞.card)
  have h := hC.conn S hS T hT
  clear hS hT
  revert hne
  induction h with
  | refl => exact fun hne => absurd rfl hne
  | tail _ hstep _ => exact fun _ => ⟨_, hstep.1, _, hstep.2.1, hstep.2.2⟩

/-- **No polygon representation exists over an unrooted crossing component
with a crossing pair.**

The root atom must avoid `S` and `Sᶜ`, both of which lie in `𝒞`, so it is
empty — but atoms are nonempty.

Together with `exists_crossing_of_one_lt_card` this says the black box
`polygonRep_exists`, which asserted `Nonempty (PolygonRep 𝒞)` for every
crossing component with `2 ≤ 𝒞.card`, was **false as stated**.  It is not the
polygon representation that fails — it is the missing orientation, and the
rooted notions below are the repair.

Note the argument needs only that the root is an *atom* meeting no cut, so it
survives the correction that made `PolygonRep.rootAtom` an atom rather than a
polygon point: weakening the root does not rescue the unrooted statement. -/
theorem not_nonempty_polygonRep_of_crossing {𝒞 : Finset (Finset (Fin n))}
    (hC : IsCrossingComponent x η 𝒞) {S T : Finset (Fin n)} (hS : S ∈ 𝒞)
    (hT : T ∈ 𝒞) (hcr : Crossing S T) : ¬ Nonempty (PolygonRep 𝒞) := by
  rintro ⟨P⟩
  obtain ⟨v, hv⟩ := P.rootAtom_nonempty
  by_cases hvS : v ∈ S
  · exact Finset.disjoint_left.mp (P.rootAtom_disjoint S hS) hv hvS
  · exact Finset.disjoint_left.mp
      (P.rootAtom_disjoint Sᶜ (hC.compl_mem hS hT hcr)) hv
      (Finset.mem_compl.mpr hvS)

/-- The refutation in the form `polygonRep_exists` is stated in. -/
theorem not_nonempty_polygonRep {𝒞 : Finset (Finset (Fin n))}
    (hC : IsCrossingComponent x η 𝒞) (hns : 2 ≤ 𝒞.card) :
    ¬ Nonempty (PolygonRep 𝒞) := by
  obtain ⟨S, hS, T, hT, hcr⟩ := hC.exists_crossing_of_one_lt_card hns
  exact not_nonempty_polygonRep_of_crossing hC hS hT hcr

/-! ### Rooted cuts

KKO22 work with `N_η ⊆ 2^{V ∖ {u₀,v₀}}`: near-minimum cuts of `G/e₀`, each
identified with the side avoiding both endpoints of the distinguished edge. -/

/-- **A rooted near-minimum cut** (KKO22 §4.2): an `η`-near minimum cut of `x`
identified with the side containing neither endpoint of `e₀`. -/
structure IsRootedNearMinCut (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (S : Finset (Fin n)) : Prop where
  /-- The underlying near-minimum cut condition. -/
  nearMin : IsNearMinCut x η S
  /-- The orientation: `S` is the side missing `u₀` and `v₀`. -/
  avoids : AvoidsRootEdge e₀ S

/-- **KKO22 Fact 4.7.**  For cuts avoiding `u₀, v₀` the fourth crossing
condition is automatic, since `u₀` witnesses `A ∪ B ≠ V`. -/
theorem crossing_of_avoidsRootEdge {e₀ : RootEdge n} {A B : Finset (Fin n)}
    (hA : AvoidsRootEdge e₀ A) (hB : AvoidsRootEdge e₀ B)
    (h1 : (A ∩ B).Nonempty) (h2 : (A \ B).Nonempty) (h3 : (B \ A).Nonempty) :
    Crossing A B := by
  refine ⟨h1, h2, h3, fun hc => ?_⟩
  have : e₀.u₀ ∈ A ∪ B := hc ▸ Finset.mem_univ _
  exact (Finset.mem_union.mp this).elim hA.1 hB.1

/-- KKO22 Fact 4.7 as an equivalence: for rooted cuts, crossing *is* the three
nonemptiness conditions. -/
theorem crossing_iff_of_avoidsRootEdge {e₀ : RootEdge n} {A B : Finset (Fin n)}
    (hA : AvoidsRootEdge e₀ A) (hB : AvoidsRootEdge e₀ B) :
    Crossing A B ↔ (A ∩ B).Nonempty ∧ (A \ B).Nonempty ∧ (B \ A).Nonempty := by
  refine ⟨fun h => ?_, fun h => crossing_of_avoidsRootEdge hA hB h.1 h.2.1 h.2.2⟩
  obtain ⟨h1, h2, h3, _⟩ := h
  exact ⟨h1, h2, h3⟩

/-- **A rooted crossing component**: KKO22 Definition 4.1 taken over the
oriented cuts of §4.2.  Only `maximal` differs in substance from
`IsCrossingComponent` — it may absorb a crossing cut only if that cut is
itself rooted, which is exactly what stops the complement from being dragged
in.

`nearMin` is deliberately spelled the same way as `IsCrossingComponent`'s, so
that the §4–§5 lemmas — which use the component hypothesis for nothing else —
port by changing the hypothesis type and nothing in the proofs. -/
structure IsRootedCrossingComponent (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ)
    (η : ℝ) (𝒞 : Finset (Finset (Fin n))) : Prop where
  /-- The component is nonempty. -/
  nonempty : 𝒞.Nonempty
  /-- Every member is an `η`-near minimum cut. -/
  nearMin : ∀ S ∈ 𝒞, IsNearMinCut x η S
  /-- The orientation: every member is the side missing `u₀` and `v₀`. -/
  avoids : ∀ S ∈ 𝒞, AvoidsRootEdge e₀ S
  /-- Members are connected through crossings inside `𝒞`. -/
  conn : ∀ S ∈ 𝒞, ∀ S' ∈ 𝒞,
    Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S S'
  /-- Maximality, over the *rooted* cuts only. -/
  maximal : ∀ S, IsNearMinCut x η S → AvoidsRootEdge e₀ S →
    (∃ S' ∈ 𝒞, Crossing S S') → S ∈ 𝒞

/-- The members of a rooted component, packaged. -/
theorem IsRootedCrossingComponent.rootedNearMin {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))} (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {S : Finset (Fin n)} (hS : S ∈ 𝒞) : IsRootedNearMinCut e₀ x η S :=
  ⟨hC.nearMin S hS, hC.avoids S hS⟩

/-- **The rooted near-min-cut bridge.**  A rooted `η`-near minimum cut of
the LP point is an `η`-near minimum cut of the restricted vector: avoidance
makes the two cut values agree (`cutSum_restrict`).

This is the seam between the two vectors of KKO22 Theorem 5.2 — the
geometry of §4–§5 is stated over the subtour-LP point `x`, while the tree
marginals are `e₀.restrict x`, whose total edge mass is `n − 1` and which
is therefore never itself a subtour-LP point. -/
theorem IsRootedNearMinCut.restrict {e₀ : RootEdge n} {S : Finset (Fin n)}
    (h : IsRootedNearMinCut e₀ x η S) :
    IsNearMinCut (e₀.restrict x) η S where
  nonempty := h.nearMin.nonempty
  ne_univ := h.nearMin.ne_univ
  cut_le := by rw [cutSum_restrict h.avoids]; exact h.nearMin.cut_le

/-- **The repair.**  At most one side of a cut is rooted, since `u₀` lies in
`S` or in `Sᶜ`.  So a rooted component never contains both — which is what
makes a root atom, disjoint from every member, possible. -/
theorem IsRootedNearMinCut.not_compl {e₀ : RootEdge n} {S : Finset (Fin n)}
    (hS : IsRootedNearMinCut e₀ x η S) : ¬ IsRootedNearMinCut e₀ x η Sᶜ :=
  fun hSc => hSc.avoids.1 (Finset.mem_compl.mpr hS.avoids.1)

/-- A rooted component contains at most one side of each cut. -/
theorem IsRootedCrossingComponent.compl_notMem {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))} (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {S : Finset (Fin n)} (hS : S ∈ 𝒞) : Sᶜ ∉ 𝒞 :=
  fun hSc => (hC.rootedNearMin hS).not_compl (hC.rootedNearMin hSc)

/-! ### Every rooted cut lies in a rooted component

The decomposition of `Polygon.lean`, restricted to the rooted cuts.  The
crossing relation is symmetric there too, so the reachability class of a
rooted cut is a rooted component containing it. -/

/-- Two rooted `η`-near minimum cuts that cross. -/
def RootedCrossRel (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (A B : Finset (Fin n)) : Prop :=
  IsRootedNearMinCut e₀ x η A ∧ IsRootedNearMinCut e₀ x η B ∧ Crossing A B

theorem RootedCrossRel.symm' {e₀ : RootEdge n} {A B : Finset (Fin n)}
    (h : RootedCrossRel e₀ x η A B) : RootedCrossRel e₀ x η B A :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- The crossing-reachability class of `B` among rooted `η`-near min cuts. -/
noncomputable def rootedCrossComp (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ)
    (η : ℝ) (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  letI : DecidablePred fun S : Finset (Fin n) =>
      Relation.ReflTransGen (RootedCrossRel e₀ x η) B S :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter fun S => Relation.ReflTransGen (RootedCrossRel e₀ x η) B S

theorem mem_rootedCrossComp {e₀ : RootEdge n} {B S : Finset (Fin n)} :
    S ∈ rootedCrossComp e₀ x η B ↔
      Relation.ReflTransGen (RootedCrossRel e₀ x η) B S := by
  letI : DecidablePred fun S : Finset (Fin n) =>
      Relation.ReflTransGen (RootedCrossRel e₀ x η) B S :=
    fun _ => Classical.propDecidable _
  rw [rootedCrossComp, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem isRootedNearMinCut_of_reflTransGen {e₀ : RootEdge n}
    {B S : Finset (Fin n)} (hB : IsRootedNearMinCut e₀ x η B)
    (h : Relation.ReflTransGen (RootedCrossRel e₀ x η) B S) :
    IsRootedNearMinCut e₀ x η S := by
  induction h with
  | refl => exact hB
  | tail _ hbc _ => exact hbc.2.1

theorem reflTransGen_rootedCrossRel_symm {e₀ : RootEdge n}
    {A B : Finset (Fin n)}
    (h : Relation.ReflTransGen (RootedCrossRel e₀ x η) A B) :
    Relation.ReflTransGen (RootedCrossRel e₀ x η) B A := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm' ih

theorem reflTransGen_rootedRestrict {e₀ : RootEdge n} {B S S' : Finset (Fin n)}
    (hBS : Relation.ReflTransGen (RootedCrossRel e₀ x η) B S)
    (h : Relation.ReflTransGen (RootedCrossRel e₀ x η) S S') :
    Relation.ReflTransGen
      (fun A A' => A ∈ rootedCrossComp e₀ x η B ∧
        A' ∈ rootedCrossComp e₀ x η B ∧ Crossing A A') S S' := by
  induction h with
  | refl => exact .refl
  | @tail c d hSc hcd ih =>
      exact ih.tail ⟨mem_rootedCrossComp.mpr (hBS.trans hSc),
        mem_rootedCrossComp.mpr ((hBS.trans hSc).tail hcd), hcd.2.2⟩

/-- The reachability class of a rooted cut is a rooted crossing component. -/
theorem isRootedCrossingComponent_rootedCrossComp {e₀ : RootEdge n}
    {B : Finset (Fin n)} (hB : IsRootedNearMinCut e₀ x η B) :
    IsRootedCrossingComponent e₀ x η (rootedCrossComp e₀ x η B) := by
  refine ⟨⟨B, mem_rootedCrossComp.mpr .refl⟩, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact (isRootedNearMinCut_of_reflTransGen hB (mem_rootedCrossComp.mp hS)).nearMin
  · intro S hS
    exact (isRootedNearMinCut_of_reflTransGen hB (mem_rootedCrossComp.mp hS)).avoids
  · intro S hS S' hS'
    exact reflTransGen_rootedRestrict (mem_rootedCrossComp.mp hS)
      ((reflTransGen_rootedCrossRel_symm (mem_rootedCrossComp.mp hS)).trans
        (mem_rootedCrossComp.mp hS'))
  · rintro S hnm hav ⟨S', hS', hcross⟩
    refine mem_rootedCrossComp.mpr ((mem_rootedCrossComp.mp hS').tail ?_)
    exact ⟨isRootedNearMinCut_of_reflTransGen hB (mem_rootedCrossComp.mp hS'),
      ⟨hnm, hav⟩, hcross.symm⟩

/-- **Every rooted near-minimum cut lies in a rooted crossing component.** -/
theorem exists_isRootedCrossingComponent_mem {e₀ : RootEdge n}
    {B : Finset (Fin n)} (hB : IsRootedNearMinCut e₀ x η B) :
    ∃ 𝒞, IsRootedCrossingComponent e₀ x η 𝒞 ∧ B ∈ 𝒞 :=
  ⟨rootedCrossComp e₀ x η B, isRootedCrossingComponent_rootedCrossComp hB,
    mem_rootedCrossComp.mpr .refl⟩

/-! ### The root atom

With the orientation in place the root atom exists unconditionally: the atom
of `u₀` meets no cut of the component, because every cut avoids `u₀`.  KKO22
§4.2 note it "is not necessarily an outside atom", which is why it is recorded
here as an atom rather than as a polygon point. -/

/-- The **root atom** of a rooted component: the atom containing `u₀`. -/
def rootAtomOf (e₀ : RootEdge n) (𝒞 : Finset (Finset (Fin n))) :
    Finset (Fin n) := atomOf 𝒞 e₀.u₀

/-- The root atom lies in no cut of a rooted component — the property the
`root` field of `PolygonRep` was standing in for, now a theorem. -/
theorem rootAtomOf_disjoint {e₀ : RootEdge n} {𝒞 : Finset (Finset (Fin n))}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {S : Finset (Fin n)}
    (hS : S ∈ 𝒞) : Disjoint (rootAtomOf e₀ 𝒞) S :=
  atomOf_disjoint_of_notMem hS (hC.avoids S hS).1

/-- The root atom is an atom of the component. -/
theorem rootAtomOf_mem_atoms {e₀ : RootEdge n} {𝒞 : Finset (Finset (Fin n))} :
    rootAtomOf e₀ 𝒞 ∈ atoms 𝒞 := mem_atoms.mpr ⟨e₀.u₀, rfl⟩

/-- Hence unions of cuts of a rooted component are proper: `u₀` is in none of
them.  This is what `PolygonRep.union_ne_univ` was buying from its root. -/
theorem union_ne_univ_of_rooted {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))} (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {S S' : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞) :
    S ∪ S' ≠ Finset.univ := by
  intro hc
  have : e₀.u₀ ∈ S ∪ S' := hc ▸ Finset.mem_univ _
  exact (Finset.mem_union.mp this).elim (hC.avoids S hS).1 (hC.avoids S' hS').1

/-! ### Theorem 4.5 over rooted components

Benczúr's lemma is proved in `Components.lean` in root-free form — over two
families that are connected under crossing, do not cross each other, and
consist of proper cuts.  Rooted components satisfy all three, so only the
separation step has to be redone: `maximal` now needs the absorbed cut to be
rooted, which it is, being a member of a rooted component. -/

/-- Rooted components sharing a cut are equal. -/
theorem IsRootedCrossingComponent.eq_of_mem_of_mem {e₀ : RootEdge n}
    {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hC' : IsRootedCrossingComponent e₀ x η 𝒞')
    {S : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S ∈ 𝒞') : 𝒞 = 𝒞' := by
  have key : ∀ (𝒟 𝒟' : Finset (Finset (Fin n))),
      IsRootedCrossingComponent e₀ x η 𝒟 →
      IsRootedCrossingComponent e₀ x η 𝒟' → S ∈ 𝒟 → S ∈ 𝒟' → 𝒟' ⊆ 𝒟 := by
    intro 𝒟 𝒟' hD hD' hSD hSD' T hT
    have h := hD'.conn S hSD' T hT
    clear hT
    induction h with
    | refl => exact hSD
    | tail _ hstep ih =>
        exact hD.maximal _ (hD'.nearMin _ hstep.2.1) (hD'.avoids _ hstep.2.1)
          ⟨_, ih, hstep.2.2.symm⟩
  exact Finset.Subset.antisymm (key 𝒞' 𝒞 hC' hC hS' hS) (key 𝒞 𝒞' hC hC' hS hS')

/-- **Cuts in different rooted components do not cross.** -/
theorem IsRootedCrossingComponent.not_crossing_of_ne {e₀ : RootEdge n}
    {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hC' : IsRootedCrossingComponent e₀ x η 𝒞') (hne : 𝒞 ≠ 𝒞')
    {S S' : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞') :
    ¬ Crossing S S' := by
  intro hcr
  exact hne (hC.eq_of_mem_of_mem hC' hS
    (hC'.maximal S (hC.nearMin S hS) (hC.avoids S hS) ⟨S', hS', hcr⟩))

/-- **KKO22 Theorem 4.5** (= [Ben97, Lemma 4.1.7]) over rooted components:
distinct rooted components have an atom apiece covering `V`. -/
theorem exists_atom_union_eq_univ_rooted {e₀ : RootEdge n}
    {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hC' : IsRootedCrossingComponent e₀ x η 𝒞') (hne : 𝒞 ≠ 𝒞') :
    ∃ a ∈ atoms 𝒞, ∃ a' ∈ atoms 𝒞', a ∪ a' = Finset.univ := by
  obtain ⟨p, q, h⟩ := exists_atomOf_union_atomOf_eq_univ hC.nonempty
    hC'.nonempty hC.conn hC'.conn
    (fun C hCm => ⟨(hC.nearMin C hCm).nonempty, (hC.nearMin C hCm).ne_univ⟩)
    (fun C hCm D hDm => hC.not_crossing_of_ne hC' hne hCm hDm)
  exact ⟨atomOf 𝒞 p, mem_atoms.mpr ⟨p, rfl⟩, atomOf 𝒞' q,
    mem_atoms.mpr ⟨q, rfl⟩, h⟩

end TSPGap

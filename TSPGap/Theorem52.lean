/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BadEventIndex
import TSPGap.MainTheorem

/-!
# KKO22 Theorem 5.2, assembled at the global bad-event index

`MainTheorem.lean` proves Theorem 5.2 from three facts about an abstract
family of bad events — `hsat`, `hcharge`/`hlocal`, `hprob` — and
`BadEventIndex.lean` builds the genuine family, one event per (polygon,
polygon point, direction), discharging all but `hsat` at it.  This file
supplies `hsat` and performs the application, so that Theorem 5.2 holds for
the events KKO actually define rather than for hypothetical ones.

**`hsat` at the index.**  Let `S` be a cut of the family crossed on both
sides and let the tree meet `δ(S)` other than twice.  Both of `S`'s polygon
points are then *active* — `S` itself witnesses the existence of
`L(rightPoint S)` and of `R(leftPoint S)` — so the two events
`(i, rightPoint S, true)` and `(i, leftPoint S, false)` carry genuine
payloads, and Lemma 5.3 at the polygon points
(`occursLeft_or_occursRight_of_cut_card_ne_two`) says that one of them
occurs.  Two further facts turn that occurrence into what Theorem 5.2
consumes:

* the charged edges lie in `δ(S)`, since
  `E(B→(p)) ⊆ E→(L(p)) = E→(S) ⊆ δ(S)`, the middle equality being Lemma 5.1
  (`arrowRight_subset_cutEdges_of_isLp` below, and its left mirror);
* they carry `x`-mass at least `1 − η`, which is Lemma 5.6 at the chosen
  star (`one_sub_le_sum_badEdges{Right,Left}_chosen`).

**The two vectors.**  §4–§5's geometry lives over the LP point `x₀` while the
mass Theorem 5.2 asks for is over the restriction `e₀.restrict x₀`.  The
bridge is `RootEdge.sum_restrict_of_notMem`: the charged edges lie in `δ(S)`
and `S` avoids `e₀`, so `e₀` is not among them and the two sums agree.

**Crossed on both sides.**  KKO's Definition 4.13 is relative to a polygon,
so the theorem's cut quantifier is `PolygonFamily.CrossedBoth F`: `S` lies in
one of the family's components and is crossed on both sides inside it.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {α η : ℝ} {e₀ : RootEdge n}
variable {𝒞 : Finset (Finset (Fin n))} {S : Finset (Fin n)}

/-! ### `E→(L(p)) ⊆ δ(S)`: Lemma 5.1 at the anchor cuts

Theorem 5.2 needs the charged edges of the event at `S`'s polygon point to
lie inside `δ(S)` — not inside `δ(L(p))`, which is a different, larger cut.
That is exactly Lemma 5.1's arrow equality `E→(S) = E→(L(p))`, available
unconditionally since `isSR_of_shared_rightPoint'`; the containment `S ⊆ L(p)`
it needs comes from the shared polygon point and `L(p)`'s maximality. -/

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **The charged edges of a right event lie in `δ(S)`.**  `S` and its
`L(rightPoint S)` share a right polygon point, so `S ⊆ L(p)` and Lemma 5.1
identifies their `S_R`'s and hence their `E→`'s; `E→(S) ⊆ δ(S)` is then the
definition. -/
theorem arrowRight_subset_cutEdges_of_isLp (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞)
    (hboth : P.CrossedOnBothSides S) {L LR : Finset (Fin n)}
    (hLp : P.IsLp (P.rightPoint S) L) (hLR : P.IsSR L LR) :
    arrowRight L LR ⊆ cutEdges S := by
  obtain ⟨SR, hSR⟩ := P.exists_isSR hboth.2
  have hLmem := hLp.1
  have hptL : P.rightPoint S = P.rightPoint L := hLp.2.1.symm
  have hlenL : P.len S ≤ P.len L := hLp.2.2.2 S hS rfl hboth
  have hsubL : S ⊆ L := P.subset_of_shared_rightPoint hS hLmem hptL hlenL
  have hSRL : P.IsSR L SR :=
    P.isSR_of_shared_rightPoint' hS hLmem hsubL hptL hlenL hSR
  have hSReq : SR = LR := IsSR.unique P hLmem hSRL hLR
  have hEright : arrowRight S SR = arrowRight L LR := by
    rw [← hSReq]
    exact P.arrowRight_eq_of_shared_rightPoint hx hη0 (by linarith) hC hS hLmem
      hSR.1 hsubL hptL hlenL hSR.2.1
  rw [← hEright]
  exact arrowRight_subset_cut S SR

/-- **The charged edges of a left event lie in `δ(S)`** — the mirror, through
the shared *left* polygon point (which is the start of the arc). -/
theorem arrowLeft_subset_cutEdges_of_isRp (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞)
    (hboth : P.CrossedOnBothSides S) {R RL : Finset (Fin n)}
    (hRp : P.IsRp (P.leftPoint S) R) (hRL : P.IsSL R RL) :
    arrowLeft R RL ⊆ cutEdges S := by
  obtain ⟨SL, hSL⟩ := P.exists_isSL hboth.1
  have hRmem := hRp.1
  have hstR : P.start S = P.start R := hRp.2.1.symm
  have hlenR : P.len S ≤ P.len R := hRp.2.2.2 S hS rfl hboth
  have hsubR : S ⊆ R := P.subset_of_shared_leftPoint hS hRmem hstR hlenR
  have hSLR : P.IsSL R SL := P.isSL_of_shared_leftPoint' hS hRmem hsubR hstR hSL
  have hSLeq : SL = RL := IsSL.unique P hRmem hSLR hRL
  have hEleft : arrowLeft S SL = arrowLeft R RL := by
    rw [← hSLeq]
    exact P.arrowLeft_eq_of_shared_leftPoint hx hη0 (by linarith) hC hS hRmem
      hSL.1 hsubR hstR hSL.2.1
  rw [← hEleft]
  exact arrowLeft_subset_cut S SL

end PolygonRep

/-! ### Crossed on both sides, over the family -/

namespace PolygonFamily

/-- **KKO22 Definition 4.13 at the level of the family**: `S` belongs to one
of the family's crossing components and is crossed on both sides inside it.
The relativization is forced — "left" and "right" are read off a polygon's
arcs — and it is the cut quantifier of Theorem 5.2. -/
def CrossedBoth (F : PolygonFamily x η e₀) (S : Finset (Fin n)) : Prop :=
  ∃ i : Fin F.N, S ∈ F.comp i ∧ (F.rep i).CrossedOnBothSides S

end PolygonFamily

/-! ### Crossed on both sides, without a polygon

Definition 4.13 reads "left" and "right" off a polygon's arcs, so as stated
it can only be used once a representation is in hand.  It has, however, a
purely set-theoretic characterization: **`S` is crossed on both sides exactly
when two rooted near-minimum cuts cross it with disjoint outside parts.**

One direction is Lemma 4.27 (`sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight`).
The other is proved here, and is the observation that two crossers on the
*same* side always share an outside atom of `S`:

* two left-crossers both contain the atom immediately *preceding* `start S` —
  each of their arcs runs from its own start (outside `S`'s arc, by side
  exclusivity) up to `start S`;
* two right-crossers both contain the atom at `rightPoint S`, which every
  right-crosser reaches (`rightPoint_mem_arc_of_crossesOnRight`) and which
  lies outside `S`'s own arc.

That atom is nonempty and disjoint from `S`, so it inhabits both differences.
The characterization is what lets Theorem 5.2 be stated with no polygon in
sight. -/

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **Definition 4.13 from disjoint outside parts.**  Two cuts crossing `S`
whose parts outside `S` are disjoint must cross it on opposite sides, so `S`
is crossed on both sides. -/
theorem crossedOnBothSides_of_disjoint_sdiff (hS : S ∈ 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hcA : Crossing A S) (hcB : Crossing B S)
    (hd : Disjoint (A \ S) (B \ S)) : P.CrossedOnBothSides S := by
  have hm := P.hm
  have hlenS := P.len_le S hS
  have h2S := P.two_le_len S hS
  -- an outside atom index outside `S`'s arc puts its vertices in `W ∖ S`
  -- for every cut `W` whose arc reaches it
  have key : ∀ j : Fin P.m, j ∉ arcSet (P.start S) (P.len S) →
      ∀ v ∈ P.out j, ∀ W ∈ 𝒞, j ∈ arcSet (P.start W) (P.len W) → v ∈ W \ S := by
    intro j hj v hv W hW hjW
    have hvW : v ∈ W := (P.outside_eq_arc W hW j).mpr hjW hv
    have hvS : v ∉ S := by
      rcases atom_subset_or_disjoint (P.out_atom j) hS with h | h
      · exact absurd ((P.outside_eq_arc S hS j).mp h) hj
      · exact Finset.disjoint_left.mp h hv
    exact Finset.mem_sdiff.mpr ⟨hvW, hvS⟩
  rcases P.crossesOnLeft_or_crossesOnRight hA hS hcA with hlA | hrA
  · rcases P.crossesOnLeft_or_crossesOnRight hB hS hcB with hlB | hrB
    · -- both on the left: the atom just before `start S` lies in both
      exfalso
      obtain ⟨j, hjval⟩ : ∃ j : Fin P.m, (j - P.start S).val = P.m - 1 :=
        ⟨P.start S + ⟨P.m - 1, by omega⟩, by rw [add_sub_cancel_left]⟩
      have hjS : j ∉ arcSet (P.start S) (P.len S) := by
        rw [mem_arcSet_compl, hjval]; omega
      have harc : ∀ W ∈ 𝒞, P.CrossesOnLeft W S →
          j ∈ arcSet (P.start W) (P.len W) := by
        intro W hW hcl
        have hlenW := P.len_le W hW
        have hdW : (P.start S - P.start W).val < P.len W := mem_arcSet.mp hcl.2
        have hpos : (P.start S - P.start W).val ≠ 0 := by
          intro h0
          refine P.not_crossesOnLeft_and_crossesOnRight hW hS ⟨hcl, hcl.1, ?_⟩
          have heq : P.start S = P.start W := sub_eq_zero.mp (Fin.val_eq_zero_iff.mp h0)
          rw [mem_arcSet, heq, sub_self]
          simpa using by omega
        have hrel := val_sub_rel j (P.start W) (P.start S)
        rw [hjval, show P.m - 1 + (P.start S - P.start W).val
            = P.m + (P.m - 1 + (P.start S - P.start W).val - P.m) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
        rw [mem_arcSet, hrel]
        omega
      obtain ⟨v, hv⟩ := P.out_nonempty j
      exact Finset.disjoint_left.mp hd (key j hjS v hv A hA (harc A hA hlA))
        (key j hjS v hv B hB (harc B hB hlB))
    · exact ⟨⟨A, hA, hlA⟩, ⟨B, hB, hrB⟩⟩
  · rcases P.crossesOnLeft_or_crossesOnRight hB hS hcB with hlB | hrB
    · exact ⟨⟨B, hB, hlB⟩, ⟨A, hA, hrA⟩⟩
    · -- both on the right: the atom at `rightPoint S` lies in both
      exfalso
      obtain ⟨v, hv⟩ := P.out_nonempty (P.rightPoint S)
      exact Finset.disjoint_left.mp hd
        (key _ (P.rightPoint_notMem_arc hS) v hv A hA
          (P.rightPoint_mem_arc_of_crossesOnRight hS hA hrA))
        (key _ (P.rightPoint_notMem_arc hS) v hv B hB
          (P.rightPoint_mem_arc_of_crossesOnRight hS hB hrB))

end PolygonRep

/-- **KKO22's "crossed on both sides", polygon-free**: two rooted near-minimum
cuts cross `S` with disjoint outside parts.  Equivalent to Definition 4.13
inside any polygon of the family (`PolygonFamily.crossedBoth_iff`), and the
form in which Theorem 5.2 quantifies over cuts. -/
def CrossedBothSides (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (S : Finset (Fin n)) : Prop :=
  ∃ A B : Finset (Fin n), IsRootedNearMinCut e₀ x η A ∧
    IsRootedNearMinCut e₀ x η B ∧ Crossing A S ∧ Crossing B S ∧
    Disjoint (A \ S) (B \ S)

/-! ### `N_{η,≤1}` and its components (KKO22 Definition 4.14)

Appendix A and the hierarchy of Appendix B are both built over connected
components of the family `N_{η,≤1}` of cuts *not* crossed on both sides, and
that is a different family from `N_η`.  Its components have to be taken in the
induced sense. -/

/-- **Membership in KKO22's `N_{η,≤1}`** (Definition 4.14): a rooted `η`-near
minimum cut that is not crossed on both sides. -/
def IsOneSideNearMinCut (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (S : Finset (Fin n)) : Prop :=
  IsRootedNearMinCut e₀ x η S ∧ ¬ CrossedBothSides e₀ x η S

/-- **A connected component of `N_{η,≤1}`.**  This is the object KKO22
Theorem B.3 runs its hierarchy construction on ("run the following procedure
on `N_{η,≤1}`: for every connected component `C` …"), and the object Appendix A
attaches a polygon to.

It is *not* a rooted crossing component of `N_η` that happens to contain no cut
crossed on both sides.  Deleting `N_{η,2}` changes both clauses of the
definition:

* **connectivity**, because a crossing path joining two surviving cuts may have
  passed through a deleted one, so what was one component can break into
  several;
* **maximality**, which is now relative to `N_{η,≤1}` and therefore does not
  absorb a cut crossed on both sides merely because it crosses a member.

So a component of the induced family may be strictly smaller than the component
of `N_η` containing it, and several of them may sit inside one. -/
structure IsOneSideComponent (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (𝒞 : Finset (Finset (Fin n))) : Prop where
  /-- The component is nonempty. -/
  nonempty : 𝒞.Nonempty
  /-- Every member lies in `N_{η,≤1}`. -/
  mem : ∀ S ∈ 𝒞, IsOneSideNearMinCut e₀ x η S
  /-- Members are connected through crossings inside `𝒞`. -/
  conn : ∀ S ∈ 𝒞, ∀ S' ∈ 𝒞,
    Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S S'
  /-- Maximality **inside `N_{η,≤1}`**. -/
  maximal : ∀ S, IsOneSideNearMinCut e₀ x η S → (∃ S' ∈ 𝒞, Crossing S S') → S ∈ 𝒞

namespace IsOneSideComponent

theorem nearMin (h : IsOneSideComponent e₀ x η 𝒞) :
    ∀ S ∈ 𝒞, IsNearMinCut x η S := fun S hS => (h.mem S hS).1.nearMin

theorem avoids (h : IsOneSideComponent e₀ x η 𝒞) :
    ∀ S ∈ 𝒞, AvoidsRootEdge e₀ S := fun S hS => (h.mem S hS).1.avoids

theorem rootedNearMin (h : IsOneSideComponent e₀ x η 𝒞) {S : Finset (Fin n)}
    (hS : S ∈ 𝒞) : IsRootedNearMinCut e₀ x η S := (h.mem S hS).1

theorem oneSide (h : IsOneSideComponent e₀ x η 𝒞) :
    ∀ S ∈ 𝒞, ¬ CrossedBothSides e₀ x η S := fun S hS => (h.mem S hS).2

end IsOneSideComponent

/-! #### Every cut of `N_{η,≤1}` lies in a component of `N_{η,≤1}`

The decomposition of `Rooted.lean`, taken inside the induced family.  Nothing
in that argument used maximality against the *whole* of `N_η`: crossing is
still symmetric, and "crossed on both sides" is a property of a single cut, so
the relation stays inside `N_{η,≤1}` and the reachability class of a member is
a component of the induced family. -/

/-- Two cuts of `N_{η,≤1}` that cross. -/
def OneSideCrossRel (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (A B : Finset (Fin n)) : Prop :=
  IsOneSideNearMinCut e₀ x η A ∧ IsOneSideNearMinCut e₀ x η B ∧ Crossing A B

theorem OneSideCrossRel.symm' {A B : Finset (Fin n)}
    (h : OneSideCrossRel e₀ x η A B) : OneSideCrossRel e₀ x η B A :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- The crossing-reachability class of `B` inside `N_{η,≤1}`. -/
noncomputable def oneSideComp (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  letI : DecidablePred fun S : Finset (Fin n) =>
      Relation.ReflTransGen (OneSideCrossRel e₀ x η) B S :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter fun S => Relation.ReflTransGen (OneSideCrossRel e₀ x η) B S

theorem mem_oneSideComp {B S : Finset (Fin n)} :
    S ∈ oneSideComp e₀ x η B ↔
      Relation.ReflTransGen (OneSideCrossRel e₀ x η) B S := by
  letI : DecidablePred fun S : Finset (Fin n) =>
      Relation.ReflTransGen (OneSideCrossRel e₀ x η) B S :=
    fun _ => Classical.propDecidable _
  rw [oneSideComp, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem isOneSideNearMinCut_of_reflTransGen {B S : Finset (Fin n)}
    (hB : IsOneSideNearMinCut e₀ x η B)
    (h : Relation.ReflTransGen (OneSideCrossRel e₀ x η) B S) :
    IsOneSideNearMinCut e₀ x η S := by
  induction h with
  | refl => exact hB
  | tail _ hbc _ => exact hbc.2.1

theorem reflTransGen_oneSideCrossRel_symm {A B : Finset (Fin n)}
    (h : Relation.ReflTransGen (OneSideCrossRel e₀ x η) A B) :
    Relation.ReflTransGen (OneSideCrossRel e₀ x η) B A := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm' ih

theorem reflTransGen_oneSideRestrict {B S S' : Finset (Fin n)}
    (hBS : Relation.ReflTransGen (OneSideCrossRel e₀ x η) B S)
    (h : Relation.ReflTransGen (OneSideCrossRel e₀ x η) S S') :
    Relation.ReflTransGen
      (fun A A' => A ∈ oneSideComp e₀ x η B ∧
        A' ∈ oneSideComp e₀ x η B ∧ Crossing A A') S S' := by
  induction h with
  | refl => exact .refl
  | @tail c d hSc hcd ih =>
      exact ih.tail ⟨mem_oneSideComp.mpr (hBS.trans hSc),
        mem_oneSideComp.mpr ((hBS.trans hSc).tail hcd), hcd.2.2⟩

/-- The reachability class of a cut of `N_{η,≤1}` is a component of it. -/
theorem isOneSideComponent_oneSideComp {B : Finset (Fin n)}
    (hB : IsOneSideNearMinCut e₀ x η B) :
    IsOneSideComponent e₀ x η (oneSideComp e₀ x η B) := by
  refine ⟨⟨B, mem_oneSideComp.mpr .refl⟩, ?_, ?_, ?_⟩
  · intro S hS
    exact isOneSideNearMinCut_of_reflTransGen hB (mem_oneSideComp.mp hS)
  · intro S hS S' hS'
    exact reflTransGen_oneSideRestrict (mem_oneSideComp.mp hS)
      ((reflTransGen_oneSideCrossRel_symm (mem_oneSideComp.mp hS)).trans
        (mem_oneSideComp.mp hS'))
  · rintro S hone ⟨S', hS', hcross⟩
    refine mem_oneSideComp.mpr ((mem_oneSideComp.mp hS').tail ?_)
    exact ⟨isOneSideNearMinCut_of_reflTransGen hB (mem_oneSideComp.mp hS'),
      hone, hcross.symm⟩

/-- **Every cut of `N_{η,≤1}` lies in a component of `N_{η,≤1}`.** -/
theorem exists_isOneSideComponent_mem {B : Finset (Fin n)}
    (hB : IsOneSideNearMinCut e₀ x η B) :
    ∃ 𝒞, IsOneSideComponent e₀ x η 𝒞 ∧ B ∈ 𝒞 :=
  ⟨oneSideComp e₀ x η B, isOneSideComponent_oneSideComp hB,
    mem_oneSideComp.mpr .refl⟩

namespace IsOneSideComponent

/-- Components of `N_{η,≤1}` sharing a cut are equal. -/
theorem eq_of_mem_of_mem {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsOneSideComponent e₀ x η 𝒞) (hC' : IsOneSideComponent e₀ x η 𝒞')
    {S : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S ∈ 𝒞') : 𝒞 = 𝒞' := by
  have key : ∀ (𝒟 𝒟' : Finset (Finset (Fin n))), IsOneSideComponent e₀ x η 𝒟 →
      IsOneSideComponent e₀ x η 𝒟' → S ∈ 𝒟 → S ∈ 𝒟' → 𝒟' ⊆ 𝒟 := by
    intro 𝒟 𝒟' hD hD' hSD hSD' T hT
    have h := hD'.conn S hSD' T hT
    clear hT
    induction h with
    | refl => exact hSD
    | tail _ hstep ih => exact hD.maximal _ (hD'.mem _ hstep.2.1) ⟨_, ih, hstep.2.2.symm⟩
  exact Finset.Subset.antisymm (key 𝒞' 𝒞 hC' hC hS' hS) (key 𝒞 𝒞' hC hC' hS hS')

/-- **Cuts in different components of `N_{η,≤1}` do not cross.** -/
theorem not_crossing_of_ne {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsOneSideComponent e₀ x η 𝒞) (hC' : IsOneSideComponent e₀ x η 𝒞')
    (hne : 𝒞 ≠ 𝒞') {S S' : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞') :
    ¬ Crossing S S' := fun hcr =>
  hne (hC.eq_of_mem_of_mem hC' hS (hC'.maximal S (hC.mem S hS) ⟨S', hS', hcr⟩))

end IsOneSideComponent

namespace PolygonFamily

/-- A cut crossed on both sides in the set-theoretic sense lies in a polygon
of the family and is crossed on both sides there: its two crossers are
dragged into the same component by maximality, and the polygon then splits
them by side. -/
theorem crossedBoth_of_crossedBothSides (F : PolygonFamily x η e₀)
    (hS : IsRootedNearMinCut e₀ x η S) (h : CrossedBothSides e₀ x η S) :
    F.CrossedBoth S := by
  obtain ⟨A, B, hA, hB, hcA, hcB, hd⟩ := h
  obtain ⟨i, hSi⟩ := F.exists_index S hS ⟨A, hA, hcA.symm⟩
  have hC := F.isComp i
  have hAi : A ∈ F.comp i := hC.maximal A hA.nearMin hA.avoids ⟨S, hSi, hcA⟩
  have hBi : B ∈ F.comp i := hC.maximal B hB.nearMin hB.avoids ⟨S, hSi, hcB⟩
  exact ⟨i, hSi, (F.rep i).crossedOnBothSides_of_disjoint_sdiff hSi hAi hBi hcA
    hcB hd⟩

/-- The converse, which is Lemma 4.27: the left- and right-crossers a polygon
provides have disjoint outside parts. -/
theorem crossedBothSides_of_crossedBoth (F : PolygonFamily x η e₀)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (h : F.CrossedBoth S) : CrossedBothSides e₀ x η S := by
  obtain ⟨i, hS, ⟨A, hA, hlA⟩, ⟨B, hB, hrB⟩⟩ := h
  exact ⟨A, B, (F.isComp i).rootedNearMin hA, (F.isComp i).rootedNearMin hB,
    hlA.1, hrB.1,
    (F.rep i).sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
      (by linarith) (F.isComp i) hS hA hB hlA hrB⟩

/-- **The two readings of "crossed on both sides" agree.** -/
theorem crossedBoth_iff (F : PolygonFamily x η e₀) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hS : IsRootedNearMinCut e₀ x η S) :
    F.CrossedBoth S ↔ CrossedBothSides e₀ x η S :=
  ⟨F.crossedBothSides_of_crossedBoth hx hη0 hη,
   F.crossedBoth_of_crossedBothSides hS⟩

end PolygonFamily

/-! ### The events at a cut's own polygon points -/

namespace BadEventIndex

/-- The right event at `(i, p)`, unfolded: its charged edges are read off the
polygon's chosen right payload at `p`. -/
theorem ebad_mk_true (F : PolygonFamily x η e₀) (i : Fin F.N)
    (p : Fin (F.rep i).m) :
    (⟨i, p, true⟩ : BadEventIndex F).Ebad
      = badEdgesRight ((F.rep i).rightWitness p).cut
          ((F.rep i).rightWitness p).cutR ((F.rep i).rightWitness p).star :=
  rfl

/-- The left event at `(i, p)`, unfolded. -/
theorem ebad_mk_false (F : PolygonFamily x η e₀) (i : Fin F.N)
    (p : Fin (F.rep i).m) :
    (⟨i, p, false⟩ : BadEventIndex F).Ebad
      = badEdgesLeft ((F.rep i).leftWitness p).cut
          ((F.rep i).leftWitness p).cutL ((F.rep i).leftWitness p).star :=
  rfl

/-- Occurrence of the right event at `(i, p)`: activity together with the
raw predicate at the chosen payload. -/
theorem occurs_mk_true (F : PolygonFamily x η e₀) (i : Fin F.N)
    (p : Fin (F.rep i).m) (T : Finset (Sym2 (Fin n))) :
    (⟨i, p, true⟩ : BadEventIndex F).Occurs T ↔
      ((F.rep i).RightActive p ∧
        OccursRight ((F.rep i).rightWitness p).cut
          ((F.rep i).rightWitness p).cutL ((F.rep i).rightWitness p).cutR T) :=
  Iff.rfl

/-- Occurrence of the left event at `(i, p)`. -/
theorem occurs_mk_false (F : PolygonFamily x η e₀) (i : Fin F.N)
    (p : Fin (F.rep i).m) (T : Finset (Sym2 (Fin n))) :
    (⟨i, p, false⟩ : BadEventIndex F).Occurs T ↔
      ((F.rep i).LeftActive p ∧
        OccursLeft ((F.rep i).leftWitness p).cut
          ((F.rep i).leftWitness p).cutL ((F.rep i).leftWitness p).cutR T) :=
  Iff.rfl

end BadEventIndex

/-! ### `hsat` at the global index -/

/-- **Theorem 5.2's `hsat`, for the genuine bad events.**  A cut crossed on
both sides that the tree meets other than twice has an *occurring* event of
the family whose charged edges lie in `δ(S)` and carry `x`-mass at least
`1 − η`.

The event is one of the two at `S`'s own polygon points: both are active
because `S` itself is a cut crossed on both sides with those points, so
Definition 4.11's maximizers `L(p)`, `R(p)` exist.  Lemma 5.3 at the polygon
points chooses between them; the two accompanying facts are Lemma 5.1 (the
edges are inside `δ(S)`) and Lemma 5.6 at the chosen star (their mass). -/
theorem exists_occurring_badEvent_of_family (F : PolygonFamily x η e₀)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    {T : Finset (Sym2 (Fin n))} (hboth : F.CrossedBoth S)
    (hT : (cutEdges S ∩ T).card ≠ 2) :
    ∃ b : BadEventIndex F, b.Occurs T ∧ b.Ebad ⊆ cutEdges S ∧
      1 - η ≤ ∑ e ∈ b.Ebad, x e := by
  classical
  obtain ⟨i, hS, hcb⟩ := hboth
  have hC := F.isComp i
  have hract : (F.rep i).RightActive ((F.rep i).rightPoint S) :=
    (F.rep i).exists_isLp ⟨S, hS, rfl, hcb⟩
  have hlact : (F.rep i).LeftActive ((F.rep i).leftPoint S) :=
    (F.rep i).exists_isRp ⟨S, hS, rfl, hcb⟩
  obtain ⟨hLp, hLL, hLR, hLstar⟩ := (F.rep i).rightWitness_spec hract
  obtain ⟨hRp, hRL, hRR, hRstar⟩ := (F.rep i).leftWitness_spec hlact
  rcases (F.rep i).occursLeft_or_occursRight_of_cut_card_ne_two hx hη0 hη hC hS
    hcb hLp hLL hLR hRp hRL hRR hT with hocc | hocc
  · -- the left event at `S`'s left polygon point
    refine ⟨⟨i, (F.rep i).leftPoint S, false⟩, ?_, ?_, ?_⟩
    · exact (BadEventIndex.occurs_mk_false F i _ T).mpr ⟨hlact, hocc⟩
    · rw [BadEventIndex.ebad_mk_false]
      exact (badEdgesLeft_subset_arrowLeft _ _ _).trans
        ((F.rep i).arrowLeft_subset_cutEdges_of_isRp hx hη0 hη hC hS hcb hRp hRL)
    · rw [BadEventIndex.ebad_mk_false]
      exact (F.rep i).one_sub_le_sum_badEdgesLeft_chosen hx hη0 hη hC hRp.1 hRL
        hRstar
  · -- the right event at `S`'s right polygon point
    refine ⟨⟨i, (F.rep i).rightPoint S, true⟩, ?_, ?_, ?_⟩
    · exact (BadEventIndex.occurs_mk_true F i _ T).mpr ⟨hract, hocc⟩
    · rw [BadEventIndex.ebad_mk_true]
      exact (badEdgesRight_subset_arrowRight _ _ _).trans
        ((F.rep i).arrowRight_subset_cutEdges_of_isLp hx hη0 hη hC hS hcb hLp hLR)
    · rw [BadEventIndex.ebad_mk_true]
      exact (F.rep i).one_sub_le_sum_badEdgesRight_chosen hx hη0 hη hC hLp.1 hLR
        hLstar

/-! ### Theorem 5.2 -/

open Classical in
/-- **KKO22 Theorem 5.2 (Main theorem), at the genuine bad events.**

For a feasible subtour-LP point `x₀` with distinguished edge `e₀`, a
spanning-tree distribution `μ` with marginals `x = e₀.restrict x₀`, a polygon
family `F` of the `η`-near minimum cuts of `x₀`, `0 < η ≤ 1/10` and `α ≥ 0`,
there is a random slack vector `s*` depending only on the tree such that

* `s*` is nonnegative;
* for every rooted `η`-near minimum cut `S` crossed on both sides with
  `δ(S)_T` odd, `s*(δ(S)) ≥ α(1 − η)`;
* `E[s*ₑ] ≤ 18αηxₑ` for every edge.

Every hypothesis of `exists_slack_vector_of_family` is now discharged at the
event index of `BadEventIndex.lean`: `hsat` above, `hcharge`
(`separates_of_mem_ebad`), `hlocal` (`card_polyFilter_ebad_le_four'`, which
is Lemma 5.4's `2 + 2`) and `hprob` (`probEvent_occurs_le`, which is Lemma
5.5).  The abstract index `Fin k` of that statement is the event type
transported along `Fintype.equivFin`. -/
theorem exists_slack_vector_of_polygonFamily {x₀ : Sym2 (Fin n) → ℝ}
    (e₀ : RootEdge n) (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (F : PolygonFamily x₀ η e₀) (hα : 0 ≤ α) (hη0 : 0 < η) (hη : η < 1 / 10) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → F.CrossedBoth S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 18 * α * η * e₀.restrict x₀ e) := by
  classical
  let ε := Fintype.equivFin (BadEventIndex F)
  refine exists_slack_vector_of_family e₀ hx₀ μ F F.CrossedBoth
    (fun j => (ε.symm j).Ebad) (fun j => (ε.symm j).Occurs)
    (fun j => (ε.symm j).poly) hα (le_of_lt hη0) ?_ ?_ ?_ ?_
  · -- `hsat`
    intro S T hSnmc hcb hodd
    have hT : (cutEdges S ∩ T).card ≠ 2 := by
      intro h
      rw [h] at hodd
      obtain ⟨m, hm⟩ := hodd
      omega
    obtain ⟨b, hocc, hsub, hmass⟩ :=
      exists_occurring_badEvent_of_family F hx₀ hη0 hη hcb hT
    refine ⟨ε b, ?_, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hocc
    · simpa only [Equiv.symm_apply_apply] using hsub
    · have hnot : e₀.edge ∉ b.Ebad := fun hc =>
        RootEdge.edge_notMem_cutEdges hSnmc.avoids (hsub hc)
      simp only [Equiv.symm_apply_apply]
      rw [RootEdge.sum_restrict_of_notMem hnot]
      exact hmass
  · -- `hcharge`
    exact fun u v j h => BadEventIndex.separates_of_mem_ebad h
  · -- `hlocal`
    intro e i
    refine le_trans (Finset.card_le_card_of_injOn (fun j => ε.symm j) ?_ ?_)
      (BadEventIndex.card_polyFilter_ebad_le_four' F hx₀ hη0 hη e i)
    · intro j hj
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
    · exact fun a _ b _ h => ε.symm.injective h
  · -- `hprob`
    exact fun j => BadEventIndex.probEvent_occurs_le F hx₀ hη0 hη μ (ε.symm j)

open Classical in
/-- **KKO22 Theorem 5.2, in the paper's own quantifiers.**

> Let `x₀` be a feasible LP solution with support `E₀ = E ∪ {e₀}` and let `x`
> be `x₀` restricted to `E`.  For any distribution `μ` of spanning trees with
> marginals `x`, `0 < η ≤ 1/10` and `α > 0`, there is a random vector `s*`
> (the randomness depending exclusively on `T ∼ μ`) such that for any
> `η`-near minimum cut `S` crossed on both sides, if `δ(S)_T` is odd then
> `s*(δ(S)) ≥ α(1 − η)`; and `E[s*ₑ] ≤ 18αηxₑ` for every `e ∈ E`.

No implementation hypothesis survives in the statement: the polygon family is
built by `exists_polygonFamily`, the bad events and all three facts about them
are internal, and "crossed on both sides" is the polygon-free
`CrossedBothSides` (equivalent to Definition 4.13 by
`PolygonFamily.crossedBoth_iff`). -/
theorem exists_slack_vector_of_subtourLP {x₀ : Sym2 (Fin n) → ℝ}
    (e₀ : RootEdge n) (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (hα : 0 ≤ α) (hη0 : 0 < η) (hη : η < 1 / 10) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → CrossedBothSides e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 18 * α * η * e₀.restrict x₀ e) := by
  obtain ⟨F⟩ := exists_polygonFamily hx₀ (le_of_lt hη0) (by linarith) e₀
  obtain ⟨s, hpos, hcut, hexp⟩ :=
    exists_slack_vector_of_polygonFamily e₀ hx₀ μ F hα hη0 hη
  exact ⟨s, hpos, fun S T hS hcb hodd =>
    hcut S T hS (F.crossedBoth_of_crossedBothSides hS hcb) hodd, hexp⟩

end TSPGap

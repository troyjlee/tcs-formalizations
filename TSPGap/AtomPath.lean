/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma227
import TSPGap.Fact28

/-!
# The contracted-tree path adapter

KKO22 §5.3 works with *edge bundles* between the atoms of a degree cut, in the
measure conditioned on every atom inducing a tree.  Read literally that is a
spanning tree of a contracted multigraph, and Lemmas 5.17 and 5.23 talk about
paths in it.

**No quotient is built here.**  An atom is a `Finset (Fin n)` of vertices and a
bundle is a `Finset (Sym2 (Fin n))` of genuine LP edges, so `δ(u)` is already
`cutEdges u` and a bundle count is already `|T ∩ e|`.  The one notion that does
not translate itself is *the path between two atoms*, and that is what this
file supplies:

`OnAtomPath T u v a` — every walk from a vertex of `u` to a vertex of `v`
passes through a vertex of `a`.

## Why the universal form is the right one

`OnUVPath` (`TreeExchange.lean`) quantifies over all walks, and the same choice
pays off again.  Two facts are needed of the atom event, and each wants a
different quantifier:

* the tree exchange *produces* it, and produces only one pair `(u', v')` — the
  endpoints of the bundle edge that was swapped out;
* Lemma 2.27's exclusivity *consumes* it, and needs it for the pair realising
  the distance between the atoms.

`onAtomPath_of_onUVPath` bridges the two, and this is exactly where the
conditioning earns its keep: because `u` and `v` induce *connected* subgraphs,
a walk between any other pair can be extended inside the atoms to a `u'`–`v'`
walk, and those extensions stay inside atoms disjoint from `a`.  So the
one-pair statement upgrades to the all-pairs one, and no contracted graph is
needed to say it.

## Exclusivity

`not_onAtomPath_both` is Lemma 2.27's step 2 for atoms, by the same distance
argument — now with `setDist`, the minimum distance between two vertex sets.
Adding the two geodesic splits gives `2·d(u,a) ≤ 0`, so `u` and `a` share a
vertex, contradicting disjointness of atoms.  As before only connectivity is
used, never acyclicity.

## Main results

* `setDist` and its basic API.
* `OnAtomPath`, `onAtomPath_of_onUVPath` — the adapter.
* `setDist_add_setDist_le_of_onAtomPath`, `not_onAtomPath_both` — exclusivity.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Distance between vertex sets -/

/-- The least distance between a vertex of `A` and a vertex of `B`. -/
noncomputable def setDist (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : ℕ :=
  sInf {d | ∃ a ∈ A, ∃ b ∈ B, G.dist a b = d}

theorem setDist_le {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ A) (hb : b ∈ B) : setDist G A B ≤ G.dist a b :=
  Nat.sInf_le ⟨a, ha, b, hb, rfl⟩

/-- The minimum is attained. -/
theorem exists_setDist {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ a ∈ A, ∃ b ∈ B, G.dist a b = setDist G A B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hne : {d | ∃ a ∈ A, ∃ b ∈ B, G.dist a b = d}.Nonempty :=
    ⟨G.dist a b, a, ha, b, hb, rfl⟩
  exact Nat.sInf_mem hne

theorem setDist_comm (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    setDist G A B = setDist G B A := by
  unfold setDist
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, SimpleGraph.dist_comm⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, ha, b, hb, SimpleGraph.dist_comm⟩

/-- Two sets at distance zero meet. -/
theorem exists_mem_inter_of_setDist_eq_zero {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (hconn : G.Connected) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : setDist G A B = 0) : ∃ x, x ∈ A ∧ x ∈ B := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_setDist (G := G) hA hB
  rw [h] at hab
  have hEq : a = b := ((hconn.preconnected a b).dist_eq_zero_iff).mp hab
  exact ⟨a, ha, hEq ▸ hb⟩

/-! ### The atom path event -/

/-- `a` separates the atoms `u` and `v` in `T`: every walk from a vertex of `u`
to a vertex of `v` meets `a`. -/
def OnAtomPath (T : Finset (Sym2 (Fin n))) (u v a : Finset (Fin n)) : Prop :=
  ∀ u' ∈ u, ∀ v' ∈ v, ∀ p : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).Walk u' v',
    ∃ x ∈ a, x ∈ p.support

/-! ### Walks inside an atom -/

/-- A walk using only edges with both endpoints in `u`, started in `u`, stays
in `u`. -/
theorem support_subset_of_inside {u : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    {a b : Fin n}
    (p : (SimpleGraph.fromEdgeSet (↑(insidePart u T) : Set (Sym2 (Fin n)))).Walk a b) :
    a ∈ u → ∀ y ∈ p.support, y ∈ u := by
  induction p with
  | nil =>
      intro ha y hy
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      exact hy ▸ ha
  | cons hadj q ih =>
      intro ha y hy
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      have hmem := (mem_insidePart.mp (by simpa using hadj.1)).2
      rcases hy with rfl | hy
      · exact ha
      · exact ih (hmem _ (Sym2.mem_mk_right _ _)) y hy

/-- An inside walk is a walk of the whole tree, on the same vertices. -/
theorem exists_walk_of_inside {u : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    {a b : Fin n}
    (p : (SimpleGraph.fromEdgeSet (↑(insidePart u T) : Set (Sym2 (Fin n)))).Walk a b) :
    ∃ q : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).Walk a b,
      q.support = p.support := by
  have hedge : ∀ e ∈ p.edges,
      e ∈ (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).edgeSet := by
    intro e he
    have h1 := p.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at h1 ⊢
    exact ⟨by simpa using (mem_insidePart.mp (by simpa using h1.1)).1, h1.2⟩
  exact ⟨p.transfer _ hedge, p.support_transfer hedge⟩

/-! ### The adapter -/

/-- **From one pair of endpoints to the atom event.**  The tree exchange
delivers `OnUVPath T u' v' x` for the endpoints of a single swapped bundle
edge; because `u` and `v` induce connected subgraphs — which is exactly what
conditioning the atoms to be trees provides — this upgrades to the all-pairs
statement `OnAtomPath T u v a`.

The two atoms must be disjoint from `a`, so that the extensions inside them
cannot themselves meet `a`. -/
theorem onAtomPath_of_onUVPath {T : Finset (Sym2 (Fin n))} {u v a : Finset (Fin n)}
    {u' v' x : Fin n} (hu : InducesTree u T) (hv : InducesTree v T)
    (hu' : u' ∈ u) (hv' : v' ∈ v) (hx : x ∈ a)
    (hua : Disjoint u a) (hva : Disjoint v a)
    (h : OnUVPath T u' v' x) :
    OnAtomPath T u v a := by
  intro u'' hu'' v'' hv'' q
  by_contra hcon
  have hq : x ∉ q.support := fun hs => hcon ⟨x, hx, hs⟩
  obtain ⟨pu⟩ := hu.2 u' hu' u'' hu''
  obtain ⟨pv⟩ := hv.2 v'' hv'' v' hv'
  obtain ⟨pu', hpu'⟩ := exists_walk_of_inside pu
  obtain ⟨pv', hpv'⟩ := exists_walk_of_inside pv
  have hmem := h (pu'.append (q.append pv'))
  rw [SimpleGraph.Walk.mem_support_append_iff] at hmem
  rcases hmem with hxu | hxrest
  · rw [hpu'] at hxu
    exact Finset.disjoint_left.mp hua (support_subset_of_inside pu hu' x hxu) hx
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hxrest
    rcases hxrest with hxq | hxv
    · exact hq hxq
    · rw [hpv'] at hxv
      exact Finset.disjoint_left.mp hva (support_subset_of_inside pv hv'' x hxv) hx

/-! ### Exclusivity -/

/-- **The atom analogue of the geodesic split.**  Only connectivity is used. -/
theorem setDist_add_setDist_le_of_onAtomPath {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {u v a : Finset (Fin n)}
    (hu : u.Nonempty) (hv : v.Nonempty) (h : OnAtomPath T u v a) :
    setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) u a
        + setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) a v
      ≤ setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) u v := by
  obtain ⟨u₀, hu₀, v₀, hv₀, hduv⟩ :=
    exists_setDist (G := SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) hu hv
  obtain ⟨p, hp⟩ := hT.2.2.exists_walk_length_eq_dist u₀ v₀
  obtain ⟨x, hxa, hxp⟩ := h u₀ hu₀ v₀ hv₀ p
  have hspec := SimpleGraph.Walk.take_spec p hxp
  have hlen : (p.takeUntil x hxp).length + (p.dropUntil x hxp).length = p.length := by
    conv_rhs => rw [← hspec]
    rw [SimpleGraph.Walk.length_append]
  have h1 : setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) u a
      ≤ (p.takeUntil x hxp).length :=
    le_trans (setDist_le hu₀ hxa) (SimpleGraph.dist_le _)
  have h2 : setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) a v
      ≤ (p.dropUntil x hxp).length :=
    le_trans (setDist_le hxa hv₀) (SimpleGraph.dist_le _)
  omega

/-- **Step 2 for atoms.**  `a` cannot separate `u` from `v` while `u` separates
`v` from `a`: adding the two splits gives `2·d(u,a) ≤ 0`, so `u` and `a` would
meet, contradicting disjointness of atoms. -/
theorem not_onAtomPath_both {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    {u v a : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty) (ha : a.Nonempty)
    (hua : Disjoint u a) :
    ¬ (OnAtomPath T u v a ∧ OnAtomPath T v a u) := by
  rintro ⟨h1, h2⟩
  have k1 := setDist_add_setDist_le_of_onAtomPath hT hu hv h1
  have k2 := setDist_add_setDist_le_of_onAtomPath hT hv ha h2
  have c1 : setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) a v
      = setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) v a :=
    setDist_comm _ _ _
  have c2 : setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) v u
      = setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) u v :=
    setDist_comm _ _ _
  have hzero : setDist (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))) u a = 0 := by
    omega
  obtain ⟨y, hyu, hya⟩ :=
    exists_mem_inter_of_setDist_eq_zero hT.2.2 hu ha hzero
  exact Finset.disjoint_left.mp hua hyu hya

end TSPGap

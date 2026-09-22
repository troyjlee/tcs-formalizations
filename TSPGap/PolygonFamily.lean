import TSPGap.Polygon
import TSPGap.BlackBoxes
import TSPGap.PolygonRootedExistence

/-!
# Quantifying over polygons: the polygon family, and KKO22 Fact 4.9

`PolygonRep 𝒞` represents the near-minimum cuts of a *single* crossing
component.  KKO's arguments in §4–§5 mostly stay inside one component, but two
do not, and both are needed to finish Theorem 5.2:

* **Fact 4.9** — for any edge `{u,v}`, there is at most one polygon in which
  the endpoints lie in two different atoms, neither being that polygon's root;
* the resulting count of **four** bad events per edge (Lemma 5.4 gives `2 + 2`
  within a polygon, Fact 4.9 gives "at most one polygon").

This file supplies the missing expressiveness — a `PolygonFamily`, indexed by
`Fin N`, carrying one `PolygonRep` per crossing component — and then proves
Fact 4.9 from it.

**Where `e₀` enters, again.**  Fact 4.9's proof needs to know what the root
*is*, not merely that it exists: KKO's root is the atom containing the
endpoints of the distinguished edge `e₀`, and the proof turns on exactly that.
So `PolygonFamily` is indexed by a `RootEdge` and carries `root_eq`.  This is
the second place the `e₀` layer has proved load-bearing rather than cosmetic.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ}

/-- An atom containing `u` is `u`'s atom. -/
theorem atomOf_eq_of_mem_atoms {𝒞 : Finset (Finset (Fin n))}
    {a : Finset (Fin n)} (ha : a ∈ atoms 𝒞) {u : Fin n} (hu : u ∈ a) :
    atomOf 𝒞 u = a := by
  obtain ⟨w, rfl⟩ := mem_atoms.mp ha
  exact atomOf_eq_of_mem hu

/-- A **polygon family**: a polygon representation for every crossing
component of the `η`-near minimum cuts of `x`.

`comp` enumerates the components (injectively, so distinct indices really are
distinct polygons), `rep` gives each its representation, and `exists_index`
records that the components exhaust the near-minimum cuts.  `root_eq` pins the
root outside atom to the atom containing `e₀`'s endpoint, which is KKO's
convention and what Fact 4.9 needs. -/
structure PolygonFamily (x : Sym2 (Fin n) → ℝ) (η : ℝ) (e₀ : RootEdge n) where
  /-- The number of polygons. -/
  N : ℕ
  /-- The crossing components, one per polygon. -/
  comp : Fin N → Finset (Finset (Fin n))
  isComp : ∀ i, IsRootedCrossingComponent e₀ x η (comp i)
  comp_injective : Function.Injective comp
  /-- The polygon representation of each component. -/
  rep : ∀ i, PolygonRep (comp i)
  /-- The components exhaust the rooted `η`-near minimum cuts **that cross
  something** — KKO's `N_η ⊆ 2^{V ∖ {u₀,v₀}}` restricted to the regime §5
  consumes.  The restriction is forced: a cut crossing nothing sits in a
  singleton component, which has no polygon, `PolygonRep` demanding four
  outside atoms. -/
  exists_index : ∀ S, IsRootedNearMinCut e₀ x η S →
    (∃ T, IsRootedNearMinCut e₀ x η T ∧ Crossing S T) → ∃ i, S ∈ comp i
  /-- KKO's root convention (§4.2): the root atom is the atom containing
  the endpoint `u₀` of the distinguished edge.  It need not be an outside
  atom, which is why `PolygonRep` records it as an atom. -/
  root_eq : ∀ i, (rep i).rootAtom = atomOf (comp i) e₀.u₀

namespace PolygonFamily

variable {e₀ : RootEdge n} (F : PolygonFamily x η e₀)

/-- The root atom of polygon `i`. -/
def rootAtom (i : Fin F.N) : Finset (Fin n) := (F.rep i).rootAtom

theorem rootAtom_eq (i : Fin F.N) : F.rootAtom i = atomOf (F.comp i) e₀.u₀ :=
  F.root_eq i

/-- Polygon `i` **separates** the edge `{u,v}`: its endpoints lie in two
different atoms of the component, and neither of those is the root.

This is precisely the configuration in which the edge can be charged to a bad
event of polygon `i` — an edge with the root as an endpoint lies in no
`E→(S)` or `E←(S)` of that component. -/
def Separates (i : Fin F.N) (u v : Fin n) : Prop :=
  atomOf (F.comp i) u ≠ atomOf (F.comp i) v ∧
  atomOf (F.comp i) u ≠ F.rootAtom i ∧
  atomOf (F.comp i) v ≠ F.rootAtom i

/-- **KKO22 Fact 4.9.**  An edge is separated by at most one polygon.

The proof is KKO's.  If two distinct polygons `i ≠ j` both separated `{u,v}`,
Theorem 4.5 would give atoms `a` of the first and `a'` of the second with
`a ∪ a' = V`.  Both endpoints cannot lie in `a` (their atoms in polygon `i`
would coincide), nor both in `a'`; so one lies in each.  Now `u₀ ∈ a ∪ a'`
too — and whichever side it falls on, that side *is* the root atom there, so
the endpoint living on that side has the root as its atom, contradicting
`Separates`. -/
theorem eq_of_separates {i j : Fin F.N} {u v : Fin n}
    (hi : F.Separates i u v) (hj : F.Separates j u v) : i = j := by
  by_contra hne
  have hcne : F.comp i ≠ F.comp j := fun h => hne (F.comp_injective h)
  obtain ⟨a, ha, a', ha', hcov⟩ :=
    exists_atom_union_eq_univ_rooted (F.isComp i) (F.isComp j) hcne
  have hmem : ∀ w : Fin n, w ∈ a ∪ a' := by
    intro w; rw [hcov]; exact Finset.mem_univ w
  have hA : ∀ w ∈ a, atomOf (F.comp i) w = a :=
    fun w hw => atomOf_eq_of_mem_atoms ha hw
  have hA' : ∀ w ∈ a', atomOf (F.comp j) w = a' :=
    fun w hw => atomOf_eq_of_mem_atoms ha' hw
  rcases Finset.mem_union.mp (hmem e₀.u₀) with h0 | h0
  · -- `a` is polygon `i`'s root atom.
    have hroot : F.rootAtom i = a := by rw [F.rootAtom_eq i, hA _ h0]
    rcases Finset.mem_union.mp (hmem u) with hu | hu
    · exact hi.2.1 (by rw [hA _ hu, hroot])
    · rcases Finset.mem_union.mp (hmem v) with hv | hv
      · exact hi.2.2 (by rw [hA _ hv, hroot])
      · exact hj.1 (by rw [hA' _ hu, hA' _ hv])
  · -- `a'` is polygon `j`'s root atom.
    have hroot : F.rootAtom j = a' := by rw [F.rootAtom_eq j, hA' _ h0]
    rcases Finset.mem_union.mp (hmem u) with hu | hu
    · rcases Finset.mem_union.mp (hmem v) with hv | hv
      · exact hi.1 (by rw [hA _ hu, hA _ hv])
      · exact hj.2.2 (by rw [hA' _ hv, hroot])
    · exact hj.2.1 (by rw [hA' _ hu, hroot])

open Classical in
/-- **Fact 4.9 in counting form**, which is how Theorem 5.2 consumes it: the
polygons separating a given edge number at most one.  Combined with Lemma
5.4's `2 + 2` within a polygon, this is the "at most four bad events per
edge" bound that `MainTheorem.hdeg` asks for. -/
theorem card_separating_le_one (u v : Fin n) :
    (Finset.univ.filter fun i => F.Separates i u v).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun i hi j hj => ?_
  exact F.eq_of_separates (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

open Classical in
/-- **The per-edge bad-event count**, `4`: Fact 4.9's "at most one polygon"
multiplied by Lemma 5.4's "at most `2 + 2` within a polygon".

This is the bridge that discharges `MainTheorem.hdeg`.  The bad events are
carried by an arbitrary finite index `ι` together with `poly`, recording which
polygon each belongs to.  Two hypotheses replace `hdeg`, and both are
*per-polygon* statements: `hcharge`, that an edge is only ever charged in a
polygon that separates it (an edge meeting the root lies in no `E→` or `E←` of
that component), and `hlocal`, which is Lemma 5.4's count inside a single
polygon.

The proof is the obvious one: every index charging `e` sits in a separating
polygon, Fact 4.9 makes all those polygons equal, and so the whole set is
confined to a single polygon's share. -/
theorem card_badEvents_le_four {ι : Type*} [Fintype ι] (poly : ι → Fin F.N)
    (Ebad : ι → Finset (Sym2 (Fin n))) {u v : Fin n} {e : Sym2 (Fin n)}
    (hcharge : ∀ b, e ∈ Ebad b → F.Separates (poly b) u v)
    (hlocal : ∀ i, (Finset.univ.filter fun b => poly b = i ∧ e ∈ Ebad b).card ≤ 4) :
    (Finset.univ.filter fun b => e ∈ Ebad b).card ≤ 4 := by
  rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun b => e ∈ Ebad b) with
    hemp | ⟨b₀, hb₀⟩
  · rw [hemp]; simp
  · have hb₀' : e ∈ Ebad b₀ := (Finset.mem_filter.mp hb₀).2
    refine le_trans (Finset.card_le_card ?_) (hlocal (poly b₀))
    intro b hb
    have hbe : e ∈ Ebad b := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ b,
      F.eq_of_separates (hcharge b hbe) (hcharge b₀ hb₀'), hbe⟩

end PolygonFamily

/-! ### The family exists

Built from the rooted component decomposition and `polygonRep_exists`, so
that the box is actually *invoked* rather than merely stated.

Only components holding more than one cut are enumerated: a singleton has no
polygon, since `PolygonRep` demands four outside atoms.  Coverage is claimed
exactly for the cuts §5 consumes — those crossing something, which is the
crossed-on-both-sides regime. -/

open Classical in
/-- The rooted crossing components holding more than one cut. -/
noncomputable def bigRootedComps (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ)
    (η : ℝ) : Finset (Finset (Finset (Fin n))) :=
  ((univ.filter fun S => IsRootedNearMinCut e₀ x η S).image
    (rootedCrossComp e₀ x η)).filter fun 𝒟 => 2 ≤ 𝒟.card

open Classical in
theorem mem_bigRootedComps {e₀ : RootEdge n} {𝒟 : Finset (Finset (Fin n))} :
    𝒟 ∈ bigRootedComps e₀ x η ↔
      (∃ S, IsRootedNearMinCut e₀ x η S ∧ rootedCrossComp e₀ x η S = 𝒟) ∧
        2 ≤ 𝒟.card := by
  rw [bigRootedComps, mem_filter, mem_image]
  refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨?_, h.2⟩⟩
  · obtain ⟨S, hS, hSD⟩ := h.1
    exact ⟨S, (mem_filter.mp hS).2, hSD⟩
  · obtain ⟨S, hS, hSD⟩ := h.1
    exact ⟨S, mem_filter.mpr ⟨mem_univ _, hS⟩, hSD⟩

theorem isRootedCrossingComponent_of_mem_bigRootedComps {e₀ : RootEdge n}
    {𝒟 : Finset (Finset (Fin n))} (h : 𝒟 ∈ bigRootedComps e₀ x η) :
    IsRootedCrossingComponent e₀ x η 𝒟 := by
  obtain ⟨⟨S, hS, rfl⟩, _⟩ := mem_bigRootedComps.mp h
  exact isRootedCrossingComponent_rootedCrossComp hS

/-- A rooted cut that crosses another rooted cut lies in an enumerated
component: the two are distinct members of its reachability class. -/
theorem rootedCrossComp_mem_bigRootedComps {e₀ : RootEdge n}
    {S T : Finset (Fin n)} (hS : IsRootedNearMinCut e₀ x η S)
    (hT : IsRootedNearMinCut e₀ x η T) (hcr : Crossing S T) :
    rootedCrossComp e₀ x η S ∈ bigRootedComps e₀ x η := by
  have hSmem : S ∈ rootedCrossComp e₀ x η S := mem_rootedCrossComp.mpr .refl
  have hTmem : T ∈ rootedCrossComp e₀ x η S :=
    mem_rootedCrossComp.mpr (Relation.ReflTransGen.single ⟨hS, hT, hcr⟩)
  have hne : S ≠ T := by
    rintro rfl
    obtain ⟨_, h2, _, _⟩ := hcr
    rw [Finset.sdiff_self] at h2
    exact Finset.not_nonempty_empty h2
  refine mem_bigRootedComps.mpr ⟨⟨S, hS, rfl⟩, ?_⟩
  exact Finset.one_lt_card.mpr ⟨S, hSmem, T, hTmem, hne⟩

/-- **The polygon family exists.**  The rooted components with more than one
cut, enumerated, each carrying the representation `polygonRep_exists`
supplies — with its root atom pinned to the atom of `u₀`, which is what
makes `root_eq` dischargeable. -/
theorem exists_polygonFamily (hx : x ∈ subtourLP n) (hη0 : 0 ≤ η)
    (hη : η < 2 / 5) (e₀ : RootEdge n) : Nonempty (PolygonFamily x η e₀) := by
  classical
  have hisC : ∀ i : Fin (bigRootedComps e₀ x η).card,
      IsRootedCrossingComponent e₀ x η
        ((bigRootedComps e₀ x η).equivFin.symm i : Finset (Finset (Fin n))) :=
    fun i => isRootedCrossingComponent_of_mem_bigRootedComps
      ((bigRootedComps e₀ x η).equivFin.symm i).2
  have hcard : ∀ i : Fin (bigRootedComps e₀ x η).card,
      2 ≤ ((bigRootedComps e₀ x η).equivFin.symm i :
        Finset (Finset (Fin n))).card :=
    fun i => (mem_bigRootedComps.mp
      ((bigRootedComps e₀ x η).equivFin.symm i).2).2
  choose P hP using fun i => polygonRep_exists hx hη0 hη (hisC i) (hcard i)
  refine ⟨{ N := (bigRootedComps e₀ x η).card
            comp := fun i => ((bigRootedComps e₀ x η).equivFin.symm i :
              Finset (Finset (Fin n)))
            isComp := hisC
            comp_injective := ?_
            rep := P
            exists_index := ?_
            root_eq := hP }⟩
  · intro i j hij
    exact (bigRootedComps e₀ x η).equivFin.symm.injective (Subtype.ext hij)
  · rintro S hS ⟨T, hT, hcr⟩
    refine ⟨(bigRootedComps e₀ x η).equivFin
      ⟨rootedCrossComp e₀ x η S,
        rootedCrossComp_mem_bigRootedComps hS hT hcr⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact mem_rootedCrossComp.mpr .refl

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.InsideAtoms
import TSPGap.Theorem52

/-!
# KKO21 Fact 4.11: the left and right hierarchies of a one-side component

For a polygon `P` of a component `𝒞` of `N_{η,≤1}` (cuts crossed on at most one side):

* `PolygonRep.OpenLeft S` / `OpenRight S` (KKO21 Definition 4.10): `S ∈ 𝒞` is crossed on
  the left / on the right by no member of `𝒞`;
* `PolygonRep.openLeft_or_openRight` — **coverage**: every member is open on one side.
  KKO21 take this as the definition of "crossed on at most one side"; the Lean
  `CrossedBothSides` is set-theoretic (two crossers with *disjoint* outside differences),
  so coverage needs the two crossers of a cut on opposite sides to have disjoint
  differences, which is KKO22 Lemma 4.27 — a 3-cycle otherwise.  The arc data alone do
  not exclude that 3-cycle (three pairwise crossing arcs with a gap can have their two
  crossers meet outside the central arc), and neither does the absence of inside atoms;
  what excludes it is the `k`-cycle bound for near-minimum cuts of a subtour-LP point
  (`no_threeCycle`, `η ≤ 2/5`).  Hence the LP hypotheses on this interface.
* `PolygonRep.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight_of_nearMin` — Lemma 4.27
  for the members of any polygon of near-minimum cuts (the rooted-component version in
  `InsideAtoms.lean` is the same argument with the component's own near-minimality);
* `PolygonRep.not_crossing_of_openLeft` / `not_crossing_of_openRight` — Fact 4.11 proper:
  two members open on the same side do not cross, since a crossing is on the left or on the
  right and the sides exchange under swapping the two cuts;
* `oneSide_laminar_split` — the paper-facing statement consumed by `NearCycle.lean`: with
  the non-root atoms of small degree adjoined to both, the two families are laminar and
  cover `𝒞 ∪ 𝒜`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

/-- Rooted cuts that do not cross are nested or disjoint (KKO22 Fact 4.7 in reverse: the
fourth crossing condition is automatic). -/
theorem nested_or_disjoint_of_not_crossing {A B : Finset (Fin n)} (hA : AvoidsRootEdge e₀ A)
    (hB : AvoidsRootEdge e₀ B) (h : ¬ Crossing A B) : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  by_cases h1 : A ⊆ B
  · exact Or.inl h1
  by_cases h2 : B ⊆ A
  · exact Or.inr (Or.inl h2)
  by_cases h3 : Disjoint A B
  · exact Or.inr (Or.inr h3)
  exfalso
  obtain ⟨w, hw⟩ := not_disjoint_iff.mp h3
  obtain ⟨y, hy1, hy2⟩ := not_subset.mp h1
  obtain ⟨z, hz1, hz2⟩ := not_subset.mp h2
  exact h (crossing_of_avoidsRootEdge hA hB ⟨w, mem_inter.mpr hw⟩ ⟨y, mem_sdiff.mpr ⟨hy1, hy2⟩⟩
    ⟨z, mem_sdiff.mpr ⟨hz1, hz2⟩⟩)

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-! ### Lemma 4.27 for the members of a polygon of near-minimum cuts -/

/-- **KKO22 Lemma 4.27** for members: if `L` crosses `S` on the left and `R` crosses `S` on
the right, their outside differences are disjoint — otherwise `S, L, R` form a 3-cycle,
witnessed by the leftmost outside atom of `S` (in `L`, not in `R`), its rightmost one (in
`R`, not in `L`), a common element of `L ∖ S` and `R ∖ S`, and the root atom. -/
theorem sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight_of_nearMin
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    (hnm : ∀ T ∈ 𝒞, IsNearMinCut x η T) {S L R : Finset (Fin n)}
    (hS : S ∈ 𝒞) (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hcL : P.CrossesOnLeft L S) (hcR : P.CrossesOnRight R S) :
    Disjoint (L \ S) (R \ S) := by
  classical
  have hm := P.hm
  have hl1 := P.two_le_len S hS
  have hl2 := P.len_le S hS
  have hroot : S ∪ L ∪ R ≠ univ := by
    obtain ⟨v, hv⟩ := P.rootAtom_nonempty
    intro hcov
    have hmem : v ∈ S ∪ L ∪ R := hcov ▸ mem_univ v
    rcases mem_union.mp hmem with h | h
    · rcases mem_union.mp h with h' | h'
      · exact disjoint_left.mp (P.rootAtom_disjoint S hS) hv h'
      · exact disjoint_left.mp (P.rootAtom_disjoint L hL) hv h'
    · exact disjoint_left.mp (P.rootAtom_disjoint R hR) hv h
  by_contra hcon
  obtain ⟨w, hwL, hwR⟩ := not_disjoint_iff.mp hcon
  rw [mem_sdiff] at hwL hwR
  -- the leftmost outside atom of `S`: in `S ∩ L`, disjoint from `R`
  have haL_S : P.out (P.start S) ⊆ S := P.leftmost_atom hS
  have haL_L : P.out (P.start S) ⊆ L := (P.outside_eq_arc L hL _).mpr hcL.2
  have haL_R : Disjoint (P.out (P.start S)) R := by
    rcases atom_subset_or_disjoint (P.out_atom (P.start S)) hR with h | h
    · exact absurd ((P.outside_eq_arc R hR _).mp h) fun hmem =>
        P.not_crossesOnLeft_and_crossesOnRight hR hS ⟨⟨hcR.1, hmem⟩, hcR⟩
    · exact h
  -- the rightmost outside atom of `S`: in `S ∩ R`, disjoint from `L`
  obtain ⟨i₁, hi₁val, hi₁mem⟩ :=
    exists_last_mem_arcSet (P.start S) (l := P.len S) (by omega) (by omega)
  have haR_S : P.out i₁ ⊆ S := (P.outside_eq_arc S hS i₁).mpr hi₁mem
  have harcR := P.cross_arc R hR S hS hcR.1
  have harcL := P.cross_arc L hL S hS hcL.1
  have haR_R : P.out i₁ ⊆ R := by
    refine (P.outside_eq_arc R hR i₁).mpr ?_
    refine last_mem_arcSet_of_not_subset hi₁val (by omega) (mem_arcSet.mp hcR.2) (by omega) ?_
    intro hsub
    obtain ⟨v, hv⟩ := harcR.2.1
    rw [mem_sdiff] at hv
    exact hv.2 (hsub hv.1)
  have haR_L : Disjoint (P.out i₁) L := by
    rcases atom_subset_or_disjoint (P.out_atom i₁) hL with h | h
    · exact absurd ((P.outside_eq_arc L hL i₁).mp h)
        (last_notMem_arcSet_of_crossing hi₁val (by omega) (by have := P.len_le L hL; omega)
          (mem_arcSet.mp hcL.2) harcL)
    · exact h
  -- the 3-cycle `S, L, R`
  refine no_threeCycle hx hη0 hη (hnm S hS) (hnm L hL) (hnm R hR) ?_
  have hLR : Crossing L R := by
    refine ⟨⟨w, mem_inter.mpr ⟨hwL.1, hwR.1⟩⟩, ?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty (P.start S)
      exact ⟨v, mem_sdiff.mpr ⟨haL_L hv, disjoint_left.mp haL_R hv⟩⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty i₁
      exact ⟨v, mem_sdiff.mpr ⟨haR_R hv, disjoint_left.mp haR_L hv⟩⟩
    · intro hcov
      refine hroot ?_
      rw [union_assoc, hcov]
      simp
  exact
    { crossAB := hcL.1.symm
      crossBC := hLR
      crossCA := hcR.1
      union_ne := hroot
      interAB := fun hsub => by
        obtain ⟨v, hv⟩ := P.out_nonempty (P.start S)
        exact disjoint_left.mp haL_R hv (hsub (mem_inter.mpr ⟨haL_S hv, haL_L hv⟩))
      interBC := fun hsub => hwL.2 (hsub (mem_inter.mpr ⟨hwL.1, hwR.1⟩))
      interCA := fun hsub => by
        obtain ⟨v, hv⟩ := P.out_nonempty i₁
        exact disjoint_left.mp haR_L hv (hsub (mem_inter.mpr ⟨haR_R hv, haR_S hv⟩)) }

/-! ### Open on the left, open on the right (KKO21 Definition 4.10) -/

/-- `S` is **open on the left**: a member of `𝒞` crossed on the left by no member. -/
def OpenLeft (S : Finset (Fin n)) : Prop := S ∈ 𝒞 ∧ ∀ W ∈ 𝒞, ¬ P.CrossesOnLeft W S

/-- `S` is **open on the right**: a member of `𝒞` crossed on the right by no member. -/
def OpenRight (S : Finset (Fin n)) : Prop := S ∈ 𝒞 ∧ ∀ W ∈ 𝒞, ¬ P.CrossesOnRight W S

theorem OpenLeft.mem {S : Finset (Fin n)} (h : P.OpenLeft S) : S ∈ 𝒞 := h.1

theorem OpenRight.mem {S : Finset (Fin n)} (h : P.OpenRight S) : S ∈ 𝒞 := h.1

/-- A member not open on the left is crossed on the left by a member. -/
theorem exists_crossesOnLeft_of_not_openLeft {S : Finset (Fin n)} (hS : S ∈ 𝒞)
    (h : ¬ P.OpenLeft S) : ∃ W ∈ 𝒞, P.CrossesOnLeft W S := by
  by_contra hcon
  push Not at hcon
  exact h ⟨hS, hcon⟩

/-- A member not open on the right is crossed on the right by a member. -/
theorem exists_crossesOnRight_of_not_openRight {S : Finset (Fin n)} (hS : S ∈ 𝒞)
    (h : ¬ P.OpenRight S) : ∃ W ∈ 𝒞, P.CrossesOnRight W S := by
  by_contra hcon
  push Not at hcon
  exact h ⟨hS, hcon⟩

/-- **Coverage** (KKO21 Definition 4.10: `L, R` partition `𝒞`): every member of a component
of `N_{η,≤1}` is open on the left or on the right, by Lemma 4.27. -/
theorem openLeft_or_openRight (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {S : Finset (Fin n)} (hS : S ∈ 𝒞) :
    P.OpenLeft S ∨ P.OpenRight S := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨L, hL, hcL⟩ := P.exists_crossesOnLeft_of_not_openLeft hS hcon.1
  obtain ⟨R, hR, hcR⟩ := P.exists_crossesOnRight_of_not_openRight hS hcon.2
  exact hcomp.oneSide S hS ⟨L, R, hcomp.rootedNearMin hL, hcomp.rootedNearMin hR, hcL.1, hcR.1,
    P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight_of_nearMin hx hη0 hη hcomp.nearMin
      hS hL hR hcL hcR⟩

/-- **KKO21 Fact 4.11**, left: two members open on the left do not cross. -/
theorem not_crossing_of_openLeft {A B : Finset (Fin n)} (hA : P.OpenLeft A)
    (hB : P.OpenLeft B) : ¬ Crossing A B := by
  intro hc
  rcases P.crossesOnLeft_or_crossesOnRight hA.1 hB.1 hc with h | h
  · exact hB.2 A hA.1 h
  · exact hA.2 B hB.1 (P.crossesOnLeft_iff_crossesOnRight_swap.mpr h)

/-- **KKO21 Fact 4.11**, right: two members open on the right do not cross. -/
theorem not_crossing_of_openRight {A B : Finset (Fin n)} (hA : P.OpenRight A)
    (hB : P.OpenRight B) : ¬ Crossing A B := by
  intro hc
  rcases P.crossesOnLeft_or_crossesOnRight hA.1 hB.1 hc with h | h
  · exact hA.2 B hB.1 (P.crossesOnLeft_iff_crossesOnRight_swap.mp h)
  · exact hB.2 A hA.1 h

end PolygonRep

/-! ### The paper-facing statement -/

/-- A pairwise non-crossing subfamily of a rooted family, with atoms adjoined, is laminar. -/
theorem laminar_of_not_crossing (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {𝒟 : Finset (Finset (Fin n))} (h𝒟 : 𝒟 ⊆ 𝒞)
    (hnc : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, ¬ Crossing A B) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms 𝒞) :
    ∀ A ∈ 𝒟 ∪ 𝒜, ∀ B ∈ 𝒟 ∪ 𝒜, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  intro A hA B hB
  rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
  · exact nested_or_disjoint_of_not_crossing (hcomp.avoids A (h𝒟 hA)) (hcomp.avoids B (h𝒟 hB))
      (hnc A hA B hB)
  · rcases atom_subset_or_disjoint (h𝒜 B hB) (h𝒟 hA) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)
  · rcases atom_subset_or_disjoint (h𝒜 A hA) (h𝒟 hB) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · by_cases he : A = B
    · exact Or.inl (he ▸ subset_rfl)
    · exact Or.inr (Or.inr (atoms_disjoint (h𝒜 A hA) (h𝒜 B hB) he))

/-- **KKO21 Fact 4.11 with KKO22 Definition A.7.**  The relevant cuts of a component of
`N_{η,≤1}` — its members together with a set `𝒜` of non-root atoms — split into the members
open on the left and those open on the right, each with the atoms adjoined, and both families
are laminar.

The LP hypotheses are what the *coverage* half needs (Lemma 4.27 through the `k`-cycle
bound); the laminarity half is the arc calculus, and the atoms are laminar against
everything.  The degree condition in `h𝒜` is not used here; it is carried for the consumer's
call shape. -/
theorem oneSide_laminar_split (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞) (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom ∧ cutSum x A ≤ 2 + η) :
    ∃ 𝒞L 𝒞R : Finset (Finset (Fin n)), 𝒞L ∪ 𝒞R = 𝒞 ∪ 𝒜 ∧
      (∀ A ∈ 𝒞L, ∀ B ∈ 𝒞L, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) ∧
      (∀ A ∈ 𝒞R, ∀ B ∈ 𝒞R, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) := by
  classical
  refine ⟨𝒞.filter (fun S => P.OpenLeft S) ∪ 𝒜, 𝒞.filter (fun S => P.OpenRight S) ∪ 𝒜,
    ?_, ?_, ?_⟩
  · ext S
    simp only [mem_union, mem_filter]
    constructor
    · intro h
      rcases h with (⟨h, -⟩ | h) | (⟨h, -⟩ | h)
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr h
    · intro h
      rcases h with h | h
      · rcases P.openLeft_or_openRight hx hcomp hη0 hη h with hL | hR
        · exact Or.inl (Or.inl ⟨h, hL⟩)
        · exact Or.inr (Or.inl ⟨h, hR⟩)
      · exact Or.inl (Or.inr h)
  · exact laminar_of_not_crossing hcomp (filter_subset _ _)
      (fun A hA B hB => P.not_crossing_of_openLeft (mem_filter.mp hA).2 (mem_filter.mp hB).2)
      (fun A hA => (h𝒜 A hA).1)
  · exact laminar_of_not_crossing hcomp (filter_subset _ _)
      (fun A hA B hB => P.not_crossing_of_openRight (mem_filter.mp hA).2 (mem_filter.mp hB).2)
      (fun A hA => (h𝒜 A hA).1)

end TSPGap

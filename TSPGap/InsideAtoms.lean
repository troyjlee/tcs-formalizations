/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BlackBoxes
import TSPGap.ExcludedCycles

/-!
# Inside atoms and the separation lemma (KKO22 §4.3–4.4)

This file consumes the `k`-cycle black box (KKO22 Lemma 4.19 =
[BG08, Lemma 22], in `TSPGap/BlackBoxes.lean`) and delivers:

* `no_threeCycle` — for `η ≤ 2/5` no three near-minimum cuts form a
  3-cycle, since a `k`-cycle needs `k ≥ 2/η ≥ 5`;
* `sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight` — **KKO22
  Lemma 4.27**: if `L` crosses `S` on the left and `R` crosses `S` on the
  right, then `(L ∖ S) ∩ (R ∖ S) = ∅`.

Lemma 4.27 discharges the hypothesis left open by the edge trichotomy of
`TSPGap/Polygon.lean`: with it, `E←(S)` and `E→(S)` are automatically
disjoint, so the mass split `x(δ(S)) = x(E←) + x(E→) + x(E∘)` and the
bound `x(E∘(S)) ≤ 2η` hold for the genuine `S_L`, `S_R` of
Definition 4.17 with no side conditions (`sum_arrowCirc_le'`).

The proof is KKO22's: if the two differences met, `S`, `L`, `R` would
pairwise cross with no one of them containing the intersection of the
other two — a 3-cycle, which `no_threeCycle` forbids.  The two witnesses
that break the containments are the extreme outside atoms of `S`: the
leftmost lies in `S ∩ L` but not `R` (crossing sides are exclusive), the
rightmost in `S ∩ R` but not `L` (the arc lemmas
`last_mem_arcSet_of_not_subset` / `last_notMem_arcSet_of_crossing`).
-/

namespace TSPGap

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))} {S L R : Finset (Fin n)}

/-- From more than one element, one differing from any given one. -/
theorem exists_mem_ne {α : Type*} [DecidableEq α] {s : Finset α}
    (h : 1 < s.card) (a : α) : ∃ b ∈ s, b ≠ a := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h
  by_cases hca : c = a
  · exact ⟨d, hd, fun hda => hcd (hca.trans hda.symm)⟩
  · exact ⟨c, hc, hca⟩

/-- **KKO22 Lemma 4.6**: an `η`-near minimum cut that is a union of atoms
of a component `𝒞`, with at least two atoms on each side, belongs to `𝒞`.

Proof (KKO22's): otherwise `B` lies in a *different* component `𝒞'`, and
Theorem 4.5 supplies atoms `a ∈ A(𝒞)`, `a' ∈ A(𝒞')` covering `V`.  Each
of `a`, `a'` is inside `B` or disjoint from it — `a` because `B` is a
union of atoms of `𝒞`, `a'` because `B ∈ 𝒞'`.  In all four cases the
"two atoms on each side" hypothesis produces a vertex outside `a ∪ a'`,
contradicting the covering. -/
theorem mem_of_isNearMinCut_of_union_atoms {B : Finset (Fin n)}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hB : IsRootedNearMinCut e₀ x η B)
    (hunion : ∀ a ∈ atoms 𝒞, a ⊆ B ∨ Disjoint a B)
    (hin : 1 < ((atoms 𝒞).filter fun a => a ⊆ B).card)
    (hout : 1 < ((atoms 𝒞).filter fun a => Disjoint a B).card) :
    B ∈ 𝒞 := by
  classical
  by_contra hBnot
  obtain ⟨𝒞', hC', hB'⟩ := exists_isRootedCrossingComponent_mem hB
  have hne : 𝒞 ≠ 𝒞' := fun h => hBnot (h ▸ hB')
  obtain ⟨a, ha, a', ha', hcov⟩ := exists_atom_union_eq_univ_rooted hC hC' hne
  have hcovmem : ∀ v : Fin n, v ∈ a ∨ v ∈ a' := by
    intro v
    have : v ∈ a ∪ a' := by rw [hcov]; exact Finset.mem_univ v
    exact Finset.mem_union.mp this
  rcases hunion a ha with h1 | h1 <;>
    rcases atom_subset_or_disjoint ha' hB' with h2 | h2
  · -- both inside `B`: then `B = univ`
    exact hB.nearMin.ne_univ (eq_univ_of_subset_of_eq_univ (Finset.union_subset h1 h2) hcov)
  · -- `a ⊆ B`, `a'` outside: another atom inside `B` escapes both
    obtain ⟨b, hb, hba⟩ := exists_mem_ne hin a
    obtain ⟨hbmem, hbB⟩ := Finset.mem_filter.mp hb
    obtain ⟨v, hv⟩ := atoms_nonempty hbmem
    rcases hcovmem v with hva | hva'
    · exact Finset.disjoint_left.mp (atoms_disjoint hbmem ha hba) hv hva
    · exact Finset.disjoint_left.mp h2 hva' (hbB hv)
  · -- `a` outside, `a' ⊆ B`: another atom outside `B` escapes both
    obtain ⟨b, hb, hba⟩ := exists_mem_ne hout a
    obtain ⟨hbmem, hbB⟩ := Finset.mem_filter.mp hb
    obtain ⟨v, hv⟩ := atoms_nonempty hbmem
    rcases hcovmem v with hva | hva'
    · exact Finset.disjoint_left.mp (atoms_disjoint hbmem ha hba) hv hva
    · exact Finset.disjoint_left.mp hbB hv (h2 hva')
  · -- both outside `B`: then `B` is empty
    obtain ⟨v, hv⟩ := hB.nearMin.nonempty
    rcases hcovmem v with hva | hva'
    · exact Finset.disjoint_left.mp h1 hva hv
    · exact Finset.disjoint_left.mp h2 hva' hv

/-- **No 3-cycles** for `η ≤ 2/5` (KKO22 Lemma 4.19, specialized). -/
theorem no_threeCycle (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    (hS : IsNearMinCut x η S) (hL : IsNearMinCut x η L)
    (hR : IsNearMinCut x η R) : ¬ IsThreeCycle S L R := by
  intro h3
  have hcyc := h3.isKCycle
  have hnmc : ∀ i < 3, IsNearMinCut x η (cyc3 S L R i) := by
    intro i hi
    interval_cases i <;> simpa [cyc3]
  have hbound := kCycle_two_div_le hx hη0 hcyc hnmc
  have h5 : (5 : ℝ) ≤ 2 / η := by
    rw [le_div_iff₀ hη0]
    linarith
  norm_num at hbound
  linarith

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- The leftmost outside atom of `S` lies in `S`, lies in any cut
crossing `S` on the left, and is disjoint from any cut crossing `S` on
the right. -/
theorem leftmost_atom (hS : S ∈ 𝒞) :
    P.out (P.start S) ⊆ S := by
  refine (P.outside_eq_arc S hS (P.start S)).mpr ?_
  rw [mem_arcSet, sub_self]
  have := P.two_le_len S hS
  simp only [Fin.val_zero]
  omega

/-! ### Two arc lemmas Lemma 4.27 needs at its paper generality

Both depend only on the polygon encoding and Fact 4.26, so they sit here,
ahead of Lemma 4.27, rather than with the rest of the arc-calculus lift. -/

/-- Membership bridge: for an almost diagonal cut, an outside atom lies
inside it exactly when its index lies in the arc.  (For members of `𝒞`
this is `outside_eq_arc`; here the arc comes from `IsArcOf`.) -/
theorem out_subset_iff_mem_arc (P : PolygonRep 𝒞) {s : Fin P.m} {l : ℕ}
    (harcS : P.IsArcOf S s l) (i : Fin P.m) :
    P.out i ⊆ S ↔ i ∈ arcSet s l := by
  rw [← P.mem_outsideIn, harcS.1]

/-- The crossing dichotomy for an almost diagonal cut: a crossing member of
`𝒞` crosses it on the left or on the right.  This is the `S ∈ 𝒞` proof with
`cross_arc` replaced by Fact 4.26 and `S`'s own arc by the supplied data. -/
theorem crossesOnLeftArc_or_crossesOnRightArc (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {W : Finset (Fin n)} {s : Fin P.m}
    {l : ℕ} (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    (hW : W ∈ 𝒞) (hc : Crossing W S) :
    P.CrossesOnLeftArc W S s ∨ P.CrossesOnRightArc W S s l := by
  have harc := cross_arc_of_almostDiagonal hx hη0 hη hC P
    (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hW) hSad
    (P.isArcOf_of_mem hW) harcS hc
  have hne : P.start W ≠ s := start_ne_of_crossing_arcs harc
  rcases arc_mem_or_mem_of_inter hne harc.1 with h | h
  · exact Or.inl ⟨hc, mem_arcSet.mpr h⟩
  · exact Or.inr ⟨hc, mem_arcSet.mpr h⟩

/-- Crossing-side exclusivity for an almost diagonal cut. -/
theorem not_crossesOnLeftArc_and_crossesOnRightArc (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {W : Finset (Fin n)} {s : Fin P.m}
    {l : ℕ} (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    (hW : W ∈ 𝒞) :
    ¬ (P.CrossesOnLeftArc W S s ∧ P.CrossesOnRightArc W S s l) := by
  rintro ⟨⟨hc, hleft⟩, -, hright⟩
  have harc := cross_arc_of_almostDiagonal hx hη0 hη hC P
    (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hW) hSad
    (P.isArcOf_of_mem hW) harcS hc
  have hne : P.start W ≠ s := start_ne_of_crossing_arcs harc
  exact harc.2.2.2
    (arcSet_union_eq_univ hne (mem_arcSet.mp hleft) (mem_arcSet.mp hright))

/-- **KKO22 Lemma 4.27, at the paper's generality**: cuts of the component
crossing an *almost diagonal* cut `S` from opposite sides do not meet
outside `S`.

KKO state 4.27 with an almost diagonal central cut, and that generality is
load-bearing: Corollary 5.8 applies it with `S = L ∪ R`, which is almost
diagonal but not a member of `𝒞`.  Restricting to `S ∈ 𝒞` is what previously
forced Corollary 5.8 to route through the diagonal-emptiness argument and,
with it, an outside root.

The proof is the `S ∈ 𝒞` one with three substitutions: `outside_eq_arc` at
`S` becomes the `IsArcOf` bridge, `cross_arc` becomes Fact 4.26, and the
properness of `S ∪ L ∪ R` comes from `IsAlmostDiagonal.root_disjoint`
rather than from a polygon point.  The parameter tightens from `2/5` to
`1/5` because the three-cycle now has a `2η`-cut in it. -/
theorem sdiff_disjoint_of_crossesOnLeftArc_of_crossesOnRightArc
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {s : Fin P.m} {l : ℕ}
    (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hcL : P.CrossesOnLeftArc L S s) (hcR : P.CrossesOnRightArc R S s l) :
    Disjoint (L \ S) (R \ S) := by
  classical
  have hm := P.hm
  have hl1 : 1 ≤ l := harcS.2.1
  have hl2 : l < P.m := harcS.2.2
  have hroot : S ∪ L ∪ R ≠ Finset.univ := by
    obtain ⟨v, hv⟩ := P.rootAtom_nonempty
    intro hcov
    have hmem : v ∈ S ∪ L ∪ R := hcov ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact Finset.disjoint_left.mp hSad.root_disjoint hv h'
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint L hL) hv h'
    · exact Finset.disjoint_left.mp (P.rootAtom_disjoint R hR) hv h
  by_contra hcon
  obtain ⟨w, hwL, hwR⟩ := Finset.not_disjoint_iff.mp hcon
  rw [Finset.mem_sdiff] at hwL hwR
  -- the leftmost outside atom of `S`'s arc: in `S ∩ L`, disjoint from `R`
  have haL_S : P.out s ⊆ S := by
    refine (P.out_subset_iff_mem_arc harcS s).mpr ?_
    rw [mem_arcSet, sub_self]
    simp only [Fin.val_zero]
    omega
  have haL_L : P.out s ⊆ L := (P.outside_eq_arc L hL s).mpr hcL.2
  have haL_R : Disjoint (P.out s) R := by
    rcases atom_subset_or_disjoint (P.out_atom s) hR with h | h
    · exact absurd ((P.outside_eq_arc R hR s).mp h) (fun hmem =>
        P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 hη hC hSad harcS hR
          ⟨⟨hcR.1, hmem⟩, hcR⟩)
    · exact h
  have haL_ne : (P.out s).Nonempty := P.out_nonempty _
  -- the rightmost outside atom of `S`'s arc: in `S ∩ R`, disjoint from `L`
  obtain ⟨i₁, hi₁val, hi₁mem⟩ :=
    exists_last_mem_arcSet s (l := l) (by omega) (by omega)
  have haR_S : P.out i₁ ⊆ S := (P.out_subset_iff_mem_arc harcS i₁).mpr hi₁mem
  have hRad : P.IsAlmostDiagonal x η R :=
    P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hR
  have hLad : P.IsAlmostDiagonal x η L :=
    P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hL
  have harcR := cross_arc_of_almostDiagonal hx hη0 hη hC P hRad hSad
    (P.isArcOf_of_mem hR) harcS hcR.1
  have harcL := cross_arc_of_almostDiagonal hx hη0 hη hC P hLad hSad
    (P.isArcOf_of_mem hL) harcS hcL.1
  have haR_R : P.out i₁ ⊆ R := by
    refine (P.outside_eq_arc R hR i₁).mpr ?_
    refine last_mem_arcSet_of_not_subset hi₁val (by omega)
      (mem_arcSet.mp hcR.2) (by omega) ?_
    intro hsub
    obtain ⟨v, hv⟩ := harcR.2.1
    rw [Finset.mem_sdiff] at hv
    exact hv.2 (hsub hv.1)
  have haR_L : Disjoint (P.out i₁) L := by
    rcases atom_subset_or_disjoint (P.out_atom i₁) hL with h | h
    · exact absurd ((P.outside_eq_arc L hL i₁).mp h)
        (last_notMem_arcSet_of_crossing hi₁val (by omega)
          (by have := P.len_le L hL; omega) (mem_arcSet.mp hcL.2) harcL)
    · exact h
  have haR_ne : (P.out i₁).Nonempty := P.out_nonempty _
  -- assemble the 3-cycle, now at parameter `2η`
  refine no_threeCycle hx (by linarith : (0:ℝ) < 2 * η)
    (by linarith : 2 * η ≤ 2 / 5) hSad.nearMin
    ((hC.nearMin L hL).mono (by linarith))
    ((hC.nearMin R hR).mono (by linarith)) ?_
  have hLR : Crossing L R := by
    refine ⟨⟨w, Finset.mem_inter.mpr ⟨hwL.1, hwR.1⟩⟩, ?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := haL_ne
      exact ⟨v, Finset.mem_sdiff.mpr ⟨haL_L hv, Finset.disjoint_left.mp haL_R hv⟩⟩
    · obtain ⟨v, hv⟩ := haR_ne
      exact ⟨v, Finset.mem_sdiff.mpr ⟨haR_R hv, Finset.disjoint_left.mp haR_L hv⟩⟩
    · intro hcov
      refine hroot ?_
      rw [Finset.union_assoc, hcov]
      simp
  exact
    { crossAB := hcL.1.symm
      crossBC := hLR
      crossCA := hcR.1
      union_ne := hroot
      interAB := by
        obtain ⟨v, hv⟩ := haL_ne
        exact fun hsub => Finset.disjoint_left.mp haL_R hv
          (hsub (Finset.mem_inter.mpr ⟨haL_S hv, haL_L hv⟩))
      interBC := by
        intro hsub
        exact hwL.2 (hsub (Finset.mem_inter.mpr ⟨hwL.1, hwR.1⟩))
      interCA := by
        obtain ⟨v, hv⟩ := haR_ne
        exact fun hsub => Finset.disjoint_left.mp haR_L hv
          (hsub (Finset.mem_inter.mpr ⟨haR_R hv, haR_S hv⟩)) }

/-- **KKO22 Lemma 4.27** with the central cut a member of the component —
the special case of the almost diagonal form, kept under its own name so the
§4–§5 call sites are unchanged.

`CrossesOnLeft L S` is definitionally `CrossesOnLeftArc L S (start S)`, and
likewise on the right, so the arc data is just `S`'s own. -/
theorem sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) (hL : L ∈ 𝒞)
    (hR : R ∈ 𝒞) (hcL : P.CrossesOnLeft L S) (hcR : P.CrossesOnRight R S) :
    Disjoint (L \ S) (R \ S) :=
  P.sdiff_disjoint_of_crossesOnLeftArc_of_crossesOnRightArc hx hη0 hη hC
    (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hS)
    (P.isArcOf_of_mem hS) hL hR hcL hcR

/-! ### First consequence of Lemma 4.23: the `a₁ = b₁` case of the chain
lemma (KKO22 Lemma 4.29)

Two cuts crossing `S` on the right *from the same polygon point* meet `S`
in the same set.  In the arc encoding the outside-atom part is exact: the
shared outside atoms of `S` and a right-crossing `R` are the arc from
`start R` to the right end of `S` (`outsideIn_inter_right_eq_arc`), which
depends on `R` only through `start R`.  Lemma 4.23 then upgrades "same
outside atoms" to "same set", inside atoms included. -/

/-- Every cut of the component avoids some atom, and hence so does any
subset of it — the "root" hypothesis of Lemma 4.23. -/
theorem exists_atom_disjoint (P : PolygonRep 𝒞) (hS : S ∈ 𝒞) :
    ∃ a ∈ atoms 𝒞, Disjoint a S := by
  have hm := P.hm
  have hlen := P.len_le S hS
  -- an outside atom beyond the right end of `S`'s arc
  obtain ⟨i, hi⟩ : ∃ i : Fin P.m, i ∉ arcSet (P.start S) (P.len S) := by
    by_contra hcon
    push Not at hcon
    have hall : (arcSet (P.start S) (P.len S)) = Finset.univ :=
      Finset.eq_univ_of_forall hcon
    have hcard : (arcSet (P.start S) (P.len S)).card = P.len S :=
      arcSet_card _ (by omega)
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  refine ⟨P.out i, P.out_atom i, ?_⟩
  rcases atom_subset_or_disjoint (P.out_atom i) hS with h | h
  · exact absurd ((P.outside_eq_arc S hS i).mp h) hi
  · exact h

/-- **KKO22 Lemma 4.29, the case `a₁ = b₁`**: cuts crossing `S` on the
right from the same polygon point meet `S` identically. -/
theorem inter_eq_of_crossesOnRight_of_start_eq (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hcA : P.CrossesOnRight A S)
    (hcB : P.CrossesOnRight B S) (hstart : P.start A = P.start B) :
    S ∩ A = S ∩ B := by
  classical
  -- the two intersections have the same outside atoms, by the arc formula
  have houtA := P.outsideIn_inter_right_eq_arc hS hA hcA
  have houtB := P.outsideIn_inter_right_eq_arc hS hB hcB
  have hout : P.outsideIn (S ∩ A) = P.outsideIn (S ∩ B) := by
    rw [P.outsideIn_inter, P.outsideIn_inter, houtA, houtB, hstart]
  -- both are `2η`-near min cuts, unions of atoms, avoiding a common atom
  have hSA : IsNearMinCut x (η + η) (S ∩ A) :=
    nearMinCut_inter hx (hC.nearMin S hS) (hC.nearMin A hA) hcA.1.symm
  have hSB : IsNearMinCut x (η + η) (S ∩ B) :=
    nearMinCut_inter hx (hC.nearMin S hS) (hC.nearMin B hB) hcB.1.symm
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := fun a ha =>
    atom_subset_or_disjoint ha hS
  have hatA : ∀ a ∈ atoms 𝒞, a ⊆ S ∩ A ∨ Disjoint a (S ∩ A) :=
    unionOfAtoms_inter hatS (fun a ha => atom_subset_or_disjoint ha hA)
  have hatB : ∀ a ∈ atoms 𝒞, a ⊆ S ∩ B ∨ Disjoint a (S ∩ B) :=
    unionOfAtoms_inter hatS (fun a ha => atom_subset_or_disjoint ha hB)
  obtain ⟨r, hr, hrS⟩ := exists_atom_disjoint P hS
  -- the shared outside-atom arc is nonempty
  have hne : (P.outsideIn (S ∩ A)).Nonempty := by
    rw [P.outsideIn_inter, houtA]
    refine ⟨P.start A, mem_arcSet.mpr ?_⟩
    rw [sub_self]
    have hd := mem_arcSet.mp hcA.2
    simp only [Fin.val_zero]
    omega
  exact eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P hSA hSB hatA hatB hout hne
    ⟨r, hr, hrS.mono_right Finset.inter_subset_left,
      hrS.mono_right Finset.inter_subset_left⟩

/-- **KKO22 Lemma 4.29**, general case: of two cuts crossing `S` on the
right, the one whose polygon point is further right meets `S` in a
*smaller* set.

In the arc picture both `O(S ∩ A)` and `O(S ∩ B)` are arcs ending at the
right end of `S`, so the later-starting one is contained in the other;
that gives `O(A ∩ S ∩ B) = O(S ∩ B)`, and Lemma 4.23 turns it into
`A ∩ S ∩ B = S ∩ B`, i.e. `S ∩ B ⊆ A`. -/
theorem inter_subset_inter_of_crossesOnRight (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hcA : P.CrossesOnRight A S)
    (hcB : P.CrossesOnRight B S)
    (hlt : (P.start A - P.start S).val < (P.start B - P.start S).val) :
    B ∩ S ⊆ A ∩ S := by
  classical
  have hm := P.hm
  have hlenS := P.len_le S hS
  have hdα : (P.start A - P.start S).val < P.len S := mem_arcSet.mp hcA.2
  have hdβ : (P.start B - P.start S).val < P.len S := mem_arcSet.mp hcB.2
  have harcA := P.outsideIn_inter_right_eq_arc hS hA hcA
  have harcB := P.outsideIn_inter_right_eq_arc hS hB hcB
  -- the `B`-arc sits inside the `A`-arc: both end at the right end of `S`
  have hβα : (P.start B - P.start A).val
      = (P.start B - P.start S).val - (P.start A - P.start S).val :=
    val_sub_of_le (le_of_lt hlt)
  have hsub : P.outsideIn S ∩ P.outsideIn B ⊆ P.outsideIn S ∩ P.outsideIn A := by
    rw [harcA, harcB]
    refine arcSet_subset ?_ ?_
    · rw [hβα]; omega
    · omega
  -- outside atoms of `A ∩ S ∩ B` and of `S ∩ B` coincide
  have hout : P.outsideIn ((A ∩ S) ∩ B) = P.outsideIn (S ∩ B) := by
    rw [P.outsideIn_inter, P.outsideIn_inter, P.outsideIn_inter]
    ext i
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hiA, hiS⟩, hiB⟩
      exact ⟨hiS, hiB⟩
    · rintro ⟨hiS, hiB⟩
      exact ⟨⟨(Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hiS, hiB⟩))).2,
        hiS⟩, hiB⟩
  -- `B` crosses `A ∩ S`
  have hβmem : P.start B ∈ P.outsideIn S ∩ P.outsideIn A := by
    rw [harcA, mem_arcSet, hβα]
    omega
  have hβA : P.out (P.start B) ⊆ A :=
    P.mem_outsideIn.mp (Finset.mem_inter.mp hβmem).2
  have hβS : P.out (P.start B) ⊆ S :=
    P.mem_outsideIn.mp (Finset.mem_inter.mp hβmem).1
  have hβB : P.out (P.start B) ⊆ B := (P.outside_eq_arc B hB _).mpr (by
    rw [mem_arcSet, sub_self]
    have := P.two_le_len B hB
    simp only [Fin.val_zero]
    omega)
  -- `start A` is outside `B`'s arc: `B`'s arc cannot reach back past `S`'s start
  have hβs : P.start B ≠ P.start S := by
    intro h
    rw [h, sub_self] at hlt
    simp only [Fin.val_zero, Nat.not_lt_zero] at hlt
  have hsB : P.len B ≤ (P.start S - P.start B).val :=
    mem_arcSet_compl.mp (fun hmem =>
      P.not_crossesOnLeft_and_crossesOnRight hB hS ⟨⟨hcB.1, hmem⟩, hcB⟩)
  have hab := val_sub_add_val_sub hβs
  have hαB : P.out (P.start A) ∩ B = ∅ := by
    have hαβne : P.start A ≠ P.start B := by
      intro h
      rw [h] at hlt
      omega
    have hab2 := val_sub_add_val_sub hαβne
    have hαnot : P.start A ∉ arcSet (P.start B) (P.len B) := by
      rw [mem_arcSet_compl]
      omega
    rcases atom_subset_or_disjoint (P.out_atom (P.start A)) hB with h | h
    · exact absurd ((P.outside_eq_arc B hB _).mp h) hαnot
    · exact Finset.disjoint_iff_inter_eq_empty.mp h
  have hαA : P.out (P.start A) ⊆ A := (P.outside_eq_arc A hA _).mpr (by
    rw [mem_arcSet, sub_self]
    have := P.two_le_len A hA
    simp only [Fin.val_zero]
    omega)
  have hαS : P.out (P.start A) ⊆ S :=
    (P.outside_eq_arc S hS _).mpr (mem_arcSet.mpr hdα)
  have hcross : Crossing (A ∩ S) B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty (P.start B)
      exact ⟨v, Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨hβA hv, hβS hv⟩, hβB hv⟩⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty (P.start A)
      refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hαA hv, hαS hv⟩, ?_⟩⟩
      intro hvB
      have hmem : v ∈ P.out (P.start A) ∩ B := Finset.mem_inter.mpr ⟨hv, hvB⟩
      rw [hαB] at hmem
      exact absurd hmem (Finset.notMem_empty v)
    · -- an outside atom of `B` beyond `S`
      obtain ⟨j, hj⟩ := (P.cross_arc B hB S hS hcB.1).2.1
      rw [Finset.mem_sdiff] at hj
      have hjB : P.out j ⊆ B := (P.outside_eq_arc B hB j).mpr hj.1
      have hjS : Disjoint (P.out j) S := by
        rcases atom_subset_or_disjoint (P.out_atom j) hS with h | h
        · exact absurd ((P.outside_eq_arc S hS j).mp h) hj.2
        · exact h
      obtain ⟨v, hv⟩ := P.out_nonempty j
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hjB hv, fun hmem =>
        Finset.disjoint_left.mp hjS hv (Finset.mem_inter.mp hmem).2⟩⟩
    · -- `(A ∩ S) ∪ B ⊆ S ∪ B ≠ univ`
      intro hcov
      refine hcB.1.2.2.2 ?_
      rw [Finset.union_comm B S]
      refine Finset.eq_univ_of_forall fun v => ?_
      have hv : v ∈ (A ∩ S) ∪ B := by rw [hcov]; exact Finset.mem_univ v
      rcases Finset.mem_union.mp hv with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).2
      · exact Finset.mem_union_right _ h
  -- near-min-cut parameters, then Lemma 4.23
  have hAS : IsNearMinCut x (η + η) (A ∩ S) :=
    nearMinCut_inter hx (hC.nearMin A hA) (hC.nearMin S hS) hcA.1
  have hASB : IsNearMinCut x (η + η + η) ((A ∩ S) ∩ B) :=
    nearMinCut_inter hx hAS (hC.nearMin B hB) hcross
  have hSB : IsNearMinCut x (η + η + η) (S ∩ B) :=
    (nearMinCut_inter hx (hC.nearMin S hS) (hC.nearMin B hB)
      hcB.1.symm).mono (by linarith)
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := fun a ha =>
    atom_subset_or_disjoint ha hS
  have hatB : ∀ a ∈ atoms 𝒞, a ⊆ B ∨ Disjoint a B := fun a ha =>
    atom_subset_or_disjoint ha hB
  have hatASB : ∀ a ∈ atoms 𝒞, a ⊆ (A ∩ S) ∩ B ∨ Disjoint a ((A ∩ S) ∩ B) :=
    unionOfAtoms_inter
      (unionOfAtoms_inter (fun a ha => atom_subset_or_disjoint ha hA) hatS) hatB
  have hne : (P.outsideIn ((A ∩ S) ∩ B)).Nonempty := by
    rw [hout, P.outsideIn_inter, harcB]
    exact ⟨P.start B, mem_arcSet.mpr (by
      rw [sub_self]; simp only [Fin.val_zero]; omega)⟩
  obtain ⟨r, hr, hrS⟩ := P.exists_atom_disjoint hS
  have hkey : (A ∩ S) ∩ B = S ∩ B :=
    eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P hASB hSB hatASB
      (unionOfAtoms_inter hatS hatB) hout hne
      ⟨r, hr, hrS.mono_right (Finset.inter_subset_left.trans
        Finset.inter_subset_right),
        hrS.mono_right Finset.inter_subset_left⟩
  -- conclude
  intro v hv
  rw [Finset.mem_inter] at hv
  have hvSB : v ∈ S ∩ B := Finset.mem_inter.mpr ⟨hv.2, hv.1⟩
  rw [← hkey, Finset.mem_inter, Finset.mem_inter] at hvSB
  exact Finset.mem_inter.mpr ⟨hvSB.1.1, hvSB.1.2⟩

/-- **KKO22 Lemma 4.29**, combined form: among cuts crossing `S` on the
right, meeting `S` is monotone in the polygon point. -/
theorem inter_subset_inter_of_crossesOnRight_of_le (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hcA : P.CrossesOnRight A S)
    (hcB : P.CrossesOnRight B S)
    (hle : (P.start A - P.start S).val ≤ (P.start B - P.start S).val) :
    B ∩ S ⊆ A ∩ S := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hstart : P.start A = P.start B :=
      sub_left_inj.mp (Fin.val_injective heq)
    rw [Finset.inter_comm B S, Finset.inter_comm A S,
      P.inter_eq_of_crossesOnRight_of_start_eq hx hη0 (by linarith) hC hS hA hB
        hcA hcB hstart]
  · exact P.inter_subset_inter_of_crossesOnRight hx hη0 hη hC hS hA hB hcA hcB hlt

/-! ### The Chain Lemma (KKO22 Lemma 4.28)

The cuts crossing `S` on the right meet `S` in a **chain**, whose least
element is `S ∩ S_R`.  Both facts are corollaries of the antitonicity of
Lemma 4.29 together with the closed form
`|O(S ∩ R)| = len S − (start R − start S)`: minimizing the shared
outside-atom count (Definition 4.17) is the same as maximizing the
polygon-point offset, which by antitonicity is the same as minimizing the
intersection.

Only the right-hand version is proved here; the left-hand statement is
its mirror image (its arcs share the endpoint `start S` and nest by
length — `outsideIn_inter_left_eq_arc`), and needs the mirrored form of
Lemma 4.29. -/

/-- **KKO22 Lemma 4.28 (Chain Lemma)**, right version: intersections with
`S` of cuts crossing it on the right are totally ordered by inclusion. -/
theorem inter_chain_of_crossesOnRight (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hcA : P.CrossesOnRight A S)
    (hcB : P.CrossesOnRight B S) :
    A ∩ S ⊆ B ∩ S ∨ B ∩ S ⊆ A ∩ S := by
  rcases le_total (P.start A - P.start S).val (P.start B - P.start S).val
    with hle | hle
  · exact Or.inr (P.inter_subset_inter_of_crossesOnRight_of_le hx hη0 hη hC hS
      hA hB hcA hcB hle)
  · exact Or.inl (P.inter_subset_inter_of_crossesOnRight_of_le hx hη0 hη hC hS
      hB hA hcB hcA hle)

/-- **KKO22 Lemma 4.28**, the bottom of the chain: `S ∩ S_R` is contained
in `S ∩ A` for every `A` crossing `S` on the right. -/
theorem inter_isSR_subset (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hS : S ∈ 𝒞) {R A : Finset (Fin n)} (hR : P.IsSR S R) (hA : A ∈ 𝒞)
    (hcA : P.CrossesOnRight A S) :
    R ∩ S ⊆ A ∩ S := by
  obtain ⟨hRmem, hcR, hmin, -⟩ := hR
  -- minimal shared outside-atom count = maximal polygon-point offset
  have hcardR := P.card_outsideIn_inter_right hS hRmem hcR
  have hcardA := P.card_outsideIn_inter_right hS hA hcA
  have hdR : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcR.2
  have hdA : (P.start A - P.start S).val < P.len S := mem_arcSet.mp hcA.2
  have hle : (P.start A - P.start S).val ≤ (P.start R - P.start S).val := by
    have := hmin A hA hcA
    rw [hcardR, hcardA] at this
    omega
  exact P.inter_subset_inter_of_crossesOnRight_of_le hx hη0 hη hC hS hA hRmem
    hcA hcR hle

/-! ### KKO22 Lemma 5.1: cuts sharing a rightmost polygon point

If `A ⊆ B` are cuts of the component with the same right polygon point,
then `A_R = B_R` and `E→(A) = E→(B)`.  In the arc picture the two arcs
share their right endpoint, which makes the shared-outside-atom counts
literally equal,
`|O(A ∩ R)| = len A − (start R − start A) = len B − (start R − start B)
 = |O(B ∩ R)|`,
so Definition 4.17 optimizes the *same* objective for `A` and for `B`
over the same candidates — hence the same optimum. -/

/-- Outside atoms of a set difference, using that atoms are indivisible. -/
theorem outsideIn_sdiff (P : PolygonRep 𝒞) {R T : Finset (Fin n)}
    (hT : ∀ a ∈ atoms 𝒞, a ⊆ T ∨ Disjoint a T) :
    P.outsideIn (R \ T) = P.outsideIn R \ P.outsideIn T := by
  ext i
  rw [Finset.mem_sdiff, P.mem_outsideIn, P.mem_outsideIn, P.mem_outsideIn]
  constructor
  · intro h
    refine ⟨fun v hv => (Finset.mem_sdiff.mp (h hv)).1, fun hsub => ?_⟩
    obtain ⟨v, hv⟩ := P.out_nonempty i
    exact (Finset.mem_sdiff.mp (h hv)).2 (hsub hv)
  · rintro ⟨hR, hT'⟩
    rcases hT (P.out i) (P.out_atom i) with h | h
    · exact absurd h hT'
    · exact fun v hv => Finset.mem_sdiff.mpr ⟨hR hv, Finset.disjoint_left.mp h hv⟩

/-- **KKO22 Lemma 5.1, step 1**: a cut crossing `A` on the right also
crosses `B` on the right, when `A ⊆ B` share a right polygon point. -/
theorem crossesOnRight_of_shared_rightPoint (P : PolygonRep 𝒞)
    (hA : S ∈ 𝒞) {B R : Finset (Fin n)} (hB : B ∈ 𝒞) (hR : R ∈ 𝒞)
    (hsub : S ⊆ B) (hpt : P.rightPoint S = P.rightPoint B)
    (hcr : P.CrossesOnRight R S) :
    P.CrossesOnRight R B := by
  have harcsub : arcSet (P.start S) (P.len S) ⊆ arcSet (P.start B) (P.len B) := by
    intro i hi
    exact (P.outside_eq_arc B hB i).mp
      (fun v hv => hsub ((P.outside_eq_arc S hA i).mpr hi hv))
  refine ⟨⟨?_, ?_, ?_, P.union_ne_univ hR hB⟩, harcsub hcr.2⟩
  · obtain ⟨v, hv⟩ := hcr.1.1
    exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      hsub (Finset.mem_inter.mp hv).2⟩⟩
  · -- the atom at the shared right point lies in `R` but not in `B`
    have hmem := P.rightPoint_mem_arc_of_crossesOnRight hA hR hcr
    have hnot : P.rightPoint S ∉ arcSet (P.start B) (P.len B) := by
      rw [hpt]; exact P.rightPoint_notMem_arc hB
    have hinR : P.out (P.rightPoint S) ⊆ R :=
      (P.outside_eq_arc R hR _).mpr hmem
    have houtB : Disjoint (P.out (P.rightPoint S)) B := by
      rcases atom_subset_or_disjoint (P.out_atom (P.rightPoint S)) hB with h | h
      · exact absurd ((P.outside_eq_arc B hB _).mp h) hnot
      · exact h
    obtain ⟨v, hv⟩ := P.out_nonempty (P.rightPoint S)
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hinR hv, Finset.disjoint_left.mp houtB hv⟩⟩
  · obtain ⟨v, hv⟩ := hcr.1.2.2.1
    rw [Finset.mem_sdiff] at hv
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hsub hv.1, hv.2⟩⟩

/-- **KKO22 Lemma 5.1, the count identity**: sharing a right polygon
point makes the Definition 4.17 objective the same for `A` and `B`. -/
theorem card_outsideIn_inter_eq_of_shared_rightPoint (P : PolygonRep 𝒞)
    (hA : S ∈ 𝒞) {B R : Finset (Fin n)} (hB : B ∈ 𝒞) (hR : R ∈ 𝒞)
    (hsub : S ⊆ B) (hpt : P.rightPoint S = P.rightPoint B)
    (hlen : P.len S ≤ P.len B) (hcr : P.CrossesOnRight R S) :
    (P.outsideIn B ∩ P.outsideIn R).card
      = (P.outsideIn S ∩ P.outsideIn R).card := by
  have hcrB := P.crossesOnRight_of_shared_rightPoint hA hB hR hsub hpt hcr
  have h1 := P.card_outsideIn_inter_right hA hR hcr
  have h2 := P.card_outsideIn_inter_right hB hR hcrB
  have hg := P.val_start_sub_start_of_rightPoint_eq hA hB hpt hlen
  have hdS : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcr.2
  -- offsets from `B`'s start exceed those from `A`'s by the length gap
  have hoff : (P.start R - P.start B).val
      = (P.start R - P.start S).val + (P.len B - P.len S) := by
    have hsplit : P.start R - P.start B
        = (P.start R - P.start S) + (P.start S - P.start B) := by abel
    have hval := congrArg Fin.val hsplit
    rw [Fin.val_add, hg] at hval
    have hm := P.hm
    have hmB := P.len_le B hB
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    exact hval
  omega

/-- **KKO22 Lemma 5.1, first conclusion**: `A_R = B_R`. -/
theorem isSR_of_shared_rightPoint (P : PolygonRep 𝒞) (hA : S ∈ 𝒞)
    {B R : Finset (Fin n)} (hB : B ∈ 𝒞) (hsub : S ⊆ B)
    (hpt : P.rightPoint S = P.rightPoint B) (hlen : P.len S ≤ P.len B)
    (hSR : P.IsSR S R)
    (htrans : ∀ R' ∈ 𝒞, P.CrossesOnRight R' B → P.CrossesOnRight R' S) :
    P.IsSR B R := by
  obtain ⟨hRmem, hcr, hmin, htie⟩ := hSR
  refine ⟨hRmem,
    P.crossesOnRight_of_shared_rightPoint hA hB hRmem hsub hpt hcr, ?_, ?_⟩
  · intro R' hR' hcr'
    rw [P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hRmem hsub hpt hlen
        hcr,
      P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hR' hsub hpt hlen
        (htrans R' hR' hcr')]
    exact hmin R' hR' (htrans R' hR' hcr')
  · intro R' hR' hcr' hcard
    refine htie R' hR' (htrans R' hR' hcr') ?_
    rw [← P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hR' hsub hpt hlen
        (htrans R' hR' hcr'),
      ← P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hRmem hsub hpt hlen
        hcr]
    exact hcard

/-- **KKO22 Lemma 5.1, second conclusion**: `E→(A) = E→(B)`.

Given the shared right point, `O(R ∩ A) = O(R ∩ B)` on the nose, so
Lemma 4.23 gives `R ∩ A = R ∩ B`; the same input gives
`O(R ∖ A) = O(R ∖ B)` and hence `R ∖ A = R ∖ B`.  Both endpoints of every
edge of `E→` are thus unchanged. -/
theorem arrowRight_eq_of_shared_rightPoint (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hA : S ∈ 𝒞) {B R : Finset (Fin n)}
    (hB : B ∈ 𝒞) (hR : R ∈ 𝒞) (hsub : S ⊆ B)
    (hpt : P.rightPoint S = P.rightPoint B) (hlen : P.len S ≤ P.len B)
    (hcr : P.CrossesOnRight R S) :
    arrowRight S R = arrowRight B R := by
  classical
  have hcrB := P.crossesOnRight_of_shared_rightPoint hA hB hR hsub hpt hcr
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := fun a ha =>
    atom_subset_or_disjoint ha hA
  have hatB : ∀ a ∈ atoms 𝒞, a ⊆ B ∨ Disjoint a B := fun a ha =>
    atom_subset_or_disjoint ha hB
  have hatR : ∀ a ∈ atoms 𝒞, a ⊆ R ∨ Disjoint a R := fun a ha =>
    atom_subset_or_disjoint ha hR
  obtain ⟨r, hr, hrR⟩ := P.exists_atom_disjoint hR
  -- the two shared outside-atom sets coincide
  have hshared : P.outsideIn S ∩ P.outsideIn R = P.outsideIn B ∩ P.outsideIn R := by
    have e1 := P.outsideIn_inter_right_eq_arc hA hR hcr
    have e2 := P.outsideIn_inter_right_eq_arc hB hR hcrB
    have hg := P.val_start_sub_start_of_rightPoint_eq hA hB hpt hlen
    have hdS : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcr.2
    have hoff : (P.start R - P.start B).val
        = (P.start R - P.start S).val + (P.len B - P.len S) := by
      have hsplit : P.start R - P.start B
          = (P.start R - P.start S) + (P.start S - P.start B) := by abel
      have hval := congrArg Fin.val hsplit
      rw [Fin.val_add, hg] at hval
      have hm := P.hm
      have hmB := P.len_le B hB
      rw [Nat.mod_eq_of_lt (by omega)] at hval
      exact hval
    rw [e1, e2]
    congr 1
    omega
  -- `R ∩ A = R ∩ B` by Lemma 4.23
  have hnetop : (P.outsideIn (S ∩ R)).Nonempty := by
    rw [P.outsideIn_inter, P.outsideIn_inter_right_eq_arc hA hR hcr]
    have hdS : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcr.2
    refine ⟨P.start R, mem_arcSet.mpr ?_⟩
    rw [sub_self]
    simp only [Fin.val_zero]
    omega
  have hinter : S ∩ R = B ∩ R := by
    refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
      (nearMinCut_inter hx (hC.nearMin S hA) (hC.nearMin R hR) hcr.1.symm)
      (nearMinCut_inter hx (hC.nearMin B hB) (hC.nearMin R hR) hcrB.1.symm)
      (unionOfAtoms_inter hatS hatR) (unionOfAtoms_inter hatB hatR) ?_ hnetop
      ⟨r, hr, hrR.mono_right Finset.inter_subset_right,
        hrR.mono_right Finset.inter_subset_right⟩
    rw [P.outsideIn_inter, P.outsideIn_inter, hshared]
  -- `R ∖ A = R ∖ B` by Lemma 4.23 again
  have hnesd : (P.outsideIn (R \ S)).Nonempty := by
    rw [P.outsideIn_sdiff hatS]
    refine ⟨P.rightPoint S, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact P.mem_outsideIn.mpr ((P.outside_eq_arc R hR _).mpr
        (P.rightPoint_mem_arc_of_crossesOnRight hA hR hcr))
    · intro hmem
      exact P.rightPoint_notMem_arc hA
        ((P.outside_eq_arc S hA _).mp (P.mem_outsideIn.mp hmem))
  have hsdiff : R \ S = R \ B := by
    refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
      (nearMinCut_sdiff hx (hC.nearMin R hR) (hC.nearMin S hA) hcr.1)
      (nearMinCut_sdiff hx (hC.nearMin R hR) (hC.nearMin B hB) hcrB.1)
      (fun a ha => by
        rcases hatR a ha with h1 | h1
        · rcases hatS a ha with h2 | h2
          · exact Or.inr (Finset.disjoint_left.mpr fun v hv hv' =>
              (Finset.mem_sdiff.mp hv').2 (h2 hv))
          · exact Or.inl (fun v hv => Finset.mem_sdiff.mpr
              ⟨h1 hv, Finset.disjoint_left.mp h2 hv⟩)
        · exact Or.inr (h1.mono_right Finset.sdiff_subset))
      (fun a ha => by
        rcases hatR a ha with h1 | h1
        · rcases hatB a ha with h2 | h2
          · exact Or.inr (Finset.disjoint_left.mpr fun v hv hv' =>
              (Finset.mem_sdiff.mp hv').2 (h2 hv))
          · exact Or.inl (fun v hv => Finset.mem_sdiff.mpr
              ⟨h1 hv, Finset.disjoint_left.mp h2 hv⟩)
        · exact Or.inr (h1.mono_right Finset.sdiff_subset))
      ?_ hnesd
      ⟨r, hr, hrR.mono_right Finset.sdiff_subset,
        hrR.mono_right Finset.sdiff_subset⟩
    rw [P.outsideIn_sdiff hatS, P.outsideIn_sdiff hatB]
    have h1 : P.outsideIn R ∩ P.outsideIn S = P.outsideIn R ∩ P.outsideIn B := by
      rw [Finset.inter_comm, hshared, Finset.inter_comm]
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hiR, hiS⟩
      refine ⟨hiR, fun hiB => hiS ?_⟩
      have : i ∈ P.outsideIn R ∩ P.outsideIn B := Finset.mem_inter.mpr ⟨hiR, hiB⟩
      rw [← h1] at this
      exact (Finset.mem_inter.mp this).2
    · rintro ⟨hiR, hiB⟩
      refine ⟨hiR, fun hiS => hiB ?_⟩
      have : i ∈ P.outsideIn R ∩ P.outsideIn S := Finset.mem_inter.mpr ⟨hiR, hiS⟩
      rw [h1] at this
      exact (Finset.mem_inter.mp this).2
  unfold arrowRight
  rw [hinter, hsdiff]

/-! ### The mirror: left-hand counterparts

There is no need for a reflection construction on `PolygonRep`.  Unfolding
Definition 4.12 shows that the two crossing relations are literally the
same statement with the two cuts exchanged,

`CrossesOnLeft L S = Crossing L S ∧ start S ∈ arc L`,
`CrossesOnRight S L = Crossing S L ∧ start S ∈ arc L`,

so "L crosses S on the left" and "S crosses L on the right" differ only by
the symmetry of `Crossing` (`crossesOnLeft_iff_crossesOnRight_swap`).

For the left-hand analogue of Lemma 5.1 this yields something better than
a mirror argument: *sharing a left polygon point simply means having
equal starts*, and the Definition 4.17 objective on the left,
`|O(S ∩ L)| = len L − (start S − start L)`, depends on `S` only through
`start S`.  So the count identity — the step that needed the shared-right
endpoint computation on the right-hand side — is immediate here.  The
left versions below are therefore proved directly rather than transported.

(The one place a genuine reflection would still help is the left form of
Lemma 4.29/4.28, whose proof mirrors an argument rather than a
definition.) -/

/-- Crossing on the left and on the right are the same relation with the
arguments exchanged. -/
theorem crossesOnLeft_iff_crossesOnRight_swap (P : PolygonRep 𝒞)
    {L S : Finset (Fin n)} : P.CrossesOnLeft L S ↔ P.CrossesOnRight S L :=
  ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- The polygon point immediately left of a cut's start, as the point at
wrap-around distance `m - 1`. -/
theorem exists_pred_start (P : PolygonRep 𝒞) (T : Finset (Fin n)) :
    ∃ i : Fin P.m, (i - P.start T).val = P.m - 1 := by
  have hm := P.hm
  exact ⟨P.start T + ⟨P.m - 1, by omega⟩, by rw [add_sub_cancel_left]⟩

/-- That point lies outside the cut. -/
theorem pred_notMem_arc (P : PolygonRep 𝒞) (hS : S ∈ 𝒞) {i : Fin P.m}
    (hi : (i - P.start S).val = P.m - 1) :
    i ∉ arcSet (P.start S) (P.len S) := by
  have hm := P.hm
  have hlen := P.len_le S hS
  rw [mem_arcSet_compl, hi]
  omega

/-- ... but inside any cut crossing it on the left. -/
theorem pred_mem_arc_of_crossesOnLeft (P : PolygonRep 𝒞) (hS : S ∈ 𝒞)
    {L : Finset (Fin n)} (hL : L ∈ 𝒞) (hcl : P.CrossesOnLeft L S)
    {i : Fin P.m} (hi : (i - P.start S).val = P.m - 1) :
    i ∈ arcSet (P.start L) (P.len L) := by
  have hm := P.hm
  have hne : P.start L ≠ P.start S :=
    start_ne_of_crossing_arcs (P.cross_arc L hL S hS hcl.1)
  have hf : 0 < (P.start S - P.start L).val := by
    rcases Nat.eq_zero_or_pos (P.start S - P.start L).val with h0 | h0
    · exact absurd (sub_eq_zero.mp (Fin.val_injective (by simpa using h0))).symm
        hne
    · exact h0
  have hfl : (P.start S - P.start L).val < P.len L := mem_arcSet.mp hcl.2
  have hrel := val_sub_rel i (P.start L) (P.start S)
  rw [hi] at hrel
  have harith : P.m - 1 + (P.start S - P.start L).val
      = P.m + ((P.start S - P.start L).val - 1) := by omega
  rw [harith, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
  rw [mem_arcSet, hrel]
  omega

/-- **KKO22 Lemma 5.1, left version, step 1**: a cut crossing `A` on the
left also crosses `B` on the left, when `A ⊆ B` share a left polygon
point.  The witness that `L ⊄ B` is the atom immediately left of the
shared start, which lies in `L` but in no cut starting there. -/
theorem crossesOnLeft_of_shared_leftPoint (P : PolygonRep 𝒞)
    (hA : S ∈ 𝒞) {B L : Finset (Fin n)} (hB : B ∈ 𝒞) (hL : L ∈ 𝒞)
    (hsub : S ⊆ B) (hpt : P.start S = P.start B)
    (hcl : P.CrossesOnLeft L S) :
    P.CrossesOnLeft L B := by
  have hm := P.hm
  have hlenB := P.len_le B hB
  refine ⟨⟨?_, ?_, ?_, P.union_ne_univ hL hB⟩, by rw [← hpt]; exact hcl.2⟩
  · obtain ⟨v, hv⟩ := hcl.1.1
    exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      hsub (Finset.mem_inter.mp hv).2⟩⟩
  · -- the atom just left of the shared start: in `L`, not in `B`
    obtain ⟨i, hi⟩ := P.exists_pred_start S
    have hiB : (i - P.start B).val = P.m - 1 := by rw [← hpt]; exact hi
    have hinL : P.out i ⊆ L :=
      (P.outside_eq_arc L hL _).mpr
        (P.pred_mem_arc_of_crossesOnLeft hA hL hcl hi)
    have hnotB : Disjoint (P.out i) B := by
      rcases atom_subset_or_disjoint (P.out_atom i) hB with h | h
      · exact absurd ((P.outside_eq_arc B hB _).mp h) (P.pred_notMem_arc hB hiB)
      · exact h
    obtain ⟨v, hv⟩ := P.out_nonempty i
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hinL hv, Finset.disjoint_left.mp hnotB hv⟩⟩
  · obtain ⟨v, hv⟩ := hcl.1.2.2.1
    rw [Finset.mem_sdiff] at hv
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hsub hv.1, hv.2⟩⟩

/-- **KKO22 Lemma 5.1, left version**: `A_L = B_L` for `A ⊆ B` sharing a
left polygon point.  The count identity is immediate: the left objective
`|O(S ∩ L)| = len L − (start S − start L)` sees `S` only through
`start S`. -/
theorem isSL_of_shared_leftPoint (P : PolygonRep 𝒞) (hA : S ∈ 𝒞)
    {B L : Finset (Fin n)} (hB : B ∈ 𝒞) (hsub : S ⊆ B)
    (hpt : P.start S = P.start B) (hSL : P.IsSL S L)
    (htrans : ∀ L' ∈ 𝒞, P.CrossesOnLeft L' B → P.CrossesOnLeft L' S) :
    P.IsSL B L := by
  obtain ⟨hLmem, hcl, hmin, htie⟩ := hSL
  have hcount : ∀ L' ∈ 𝒞, P.CrossesOnLeft L' S →
      (P.outsideIn B ∩ P.outsideIn L').card
        = (P.outsideIn S ∩ P.outsideIn L').card := by
    intro L' hL' hcl'
    rw [P.card_outsideIn_inter_left hA hL' hcl',
      P.card_outsideIn_inter_left hB hL'
        (P.crossesOnLeft_of_shared_leftPoint hA hB hL' hsub hpt hcl'),
      hpt]
  refine ⟨hLmem,
    P.crossesOnLeft_of_shared_leftPoint hA hB hLmem hsub hpt hcl, ?_, ?_⟩
  · intro L' hL' hcl'
    rw [hcount L hLmem hcl, hcount L' hL' (htrans L' hL' hcl')]
    exact hmin L' hL' (htrans L' hL' hcl')
  · intro L' hL' hcl' hcard
    refine htie L' hL' (htrans L' hL' hcl') ?_
    rw [← hcount L' hL' (htrans L' hL' hcl'), ← hcount L hLmem hcl]
    exact hcard

/-- **KKO22 Lemma 5.1, left version, second conclusion**:
`E←(A) = E←(B)`. -/
theorem arrowLeft_eq_of_shared_leftPoint (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hA : S ∈ 𝒞) {B L : Finset (Fin n)}
    (hB : B ∈ 𝒞) (hL : L ∈ 𝒞) (hsub : S ⊆ B) (hpt : P.start S = P.start B)
    (hcl : P.CrossesOnLeft L S) :
    arrowLeft S L = arrowLeft B L := by
  classical
  have hm := P.hm
  have hlenA := P.len_le S hA
  have hclB := P.crossesOnLeft_of_shared_leftPoint hA hB hL hsub hpt hcl
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := fun a ha =>
    atom_subset_or_disjoint ha hA
  have hatB : ∀ a ∈ atoms 𝒞, a ⊆ B ∨ Disjoint a B := fun a ha =>
    atom_subset_or_disjoint ha hB
  have hatL : ∀ a ∈ atoms 𝒞, a ⊆ L ∨ Disjoint a L := fun a ha =>
    atom_subset_or_disjoint ha hL
  obtain ⟨r, hr, hrL⟩ := P.exists_atom_disjoint hL
  -- shared outside atoms agree: the left objective sees only `start`
  have hshared : P.outsideIn S ∩ P.outsideIn L
      = P.outsideIn B ∩ P.outsideIn L := by
    rw [P.outsideIn_inter_left_eq_arc hA hL hcl,
      P.outsideIn_inter_left_eq_arc hB hL hclB, hpt]
  -- the atom just left of the shared start witnesses nonemptiness
  obtain ⟨i, hi⟩ := P.exists_pred_start S
  have hnesd : (P.outsideIn (L \ S)).Nonempty := by
    rw [P.outsideIn_sdiff hatS]
    refine ⟨i, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact P.mem_outsideIn.mpr ((P.outside_eq_arc L hL _).mpr
        (P.pred_mem_arc_of_crossesOnLeft hA hL hcl hi))
    · intro hmem
      exact P.pred_notMem_arc hA hi
        ((P.outside_eq_arc S hA _).mp (P.mem_outsideIn.mp hmem))
  have hfl : (P.start S - P.start L).val < P.len L := mem_arcSet.mp hcl.2
  have hnetop : (P.outsideIn (S ∩ L)).Nonempty := by
    rw [P.outsideIn_inter, P.outsideIn_inter_left_eq_arc hA hL hcl]
    refine ⟨P.start S, mem_arcSet.mpr ?_⟩
    rw [sub_self]
    simp only [Fin.val_zero]
    omega
  have hinter : S ∩ L = B ∩ L := by
    refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
      (nearMinCut_inter hx (hC.nearMin S hA) (hC.nearMin L hL) hcl.1.symm)
      (nearMinCut_inter hx (hC.nearMin B hB) (hC.nearMin L hL) hclB.1.symm)
      (unionOfAtoms_inter hatS hatL) (unionOfAtoms_inter hatB hatL) ?_ hnetop
      ⟨r, hr, hrL.mono_right Finset.inter_subset_right,
        hrL.mono_right Finset.inter_subset_right⟩
    rw [P.outsideIn_inter, P.outsideIn_inter, hshared]
  have hsdiff : L \ S = L \ B := by
    refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
      (nearMinCut_sdiff hx (hC.nearMin L hL) (hC.nearMin S hA) hcl.1)
      (nearMinCut_sdiff hx (hC.nearMin L hL) (hC.nearMin B hB) hclB.1)
      (fun a ha => by
        rcases hatL a ha with h1 | h1
        · rcases hatS a ha with h2 | h2
          · exact Or.inr (Finset.disjoint_left.mpr fun v hv hv' =>
              (Finset.mem_sdiff.mp hv').2 (h2 hv))
          · exact Or.inl (fun v hv => Finset.mem_sdiff.mpr
              ⟨h1 hv, Finset.disjoint_left.mp h2 hv⟩)
        · exact Or.inr (h1.mono_right Finset.sdiff_subset))
      (fun a ha => by
        rcases hatL a ha with h1 | h1
        · rcases hatB a ha with h2 | h2
          · exact Or.inr (Finset.disjoint_left.mpr fun v hv hv' =>
              (Finset.mem_sdiff.mp hv').2 (h2 hv))
          · exact Or.inl (fun v hv => Finset.mem_sdiff.mpr
              ⟨h1 hv, Finset.disjoint_left.mp h2 hv⟩)
        · exact Or.inr (h1.mono_right Finset.sdiff_subset))
      ?_ hnesd
      ⟨r, hr, hrL.mono_right Finset.sdiff_subset,
        hrL.mono_right Finset.sdiff_subset⟩
    rw [P.outsideIn_sdiff hatS, P.outsideIn_sdiff hatB]
    have h1 : P.outsideIn L ∩ P.outsideIn S = P.outsideIn L ∩ P.outsideIn B := by
      rw [Finset.inter_comm, hshared, Finset.inter_comm]
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hiL, hiS⟩
      refine ⟨hiL, fun hiB => hiS ?_⟩
      have hmem : i ∈ P.outsideIn L ∩ P.outsideIn B :=
        Finset.mem_inter.mpr ⟨hiL, hiB⟩
      rw [← h1] at hmem
      exact (Finset.mem_inter.mp hmem).2
    · rintro ⟨hiL, hiB⟩
      refine ⟨hiL, fun hiS => hiB ?_⟩
      have hmem : i ∈ P.outsideIn L ∩ P.outsideIn S :=
        Finset.mem_inter.mpr ⟨hiL, hiS⟩
      rw [h1] at hmem
      exact (Finset.mem_inter.mp hmem).2
  unfold arrowLeft
  rw [hinter, hsdiff]

/-! ### KKO22 Lemma 5.7, geometric core

`S` crossed on both sides sits between `L = L(p_r)`, which extends it to
the left with the same right polygon point, and `R = R(p_l)`, which
extends it to the right with the same left point.  KKO's Figure 14 says
"the yellow region is empty", i.e. `L ∩ R = S`: on outside atoms this is
the arc identity `[start L, end S) ∩ [start S, end R) = [start S, end S)`,
and Lemma 4.23 upgrades it to vertex sets.

From `L ∩ R = S` the cut containment `δ(S) ⊆ δ(L) ∪ δ(R)` follows by pure
set reasoning, which is the second step of KKO's proof. -/

/-- **KKO22 Lemma 5.7, key step** (Figure 14): `L(p_r) ∩ R(p_l) = S`. -/
theorem inter_eq_of_extends_both_sides (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) {L R : Finset (Fin n)}
    (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hsubL : S ⊆ L) (hptL : P.rightPoint S = P.rightPoint L)
    (hlenL : P.len S < P.len L)
    (hptR : P.start S = P.start R) (hlenR : P.len S < P.len R)
    (hcross : Crossing L R) :
    L ∩ R = S := by
  classical
  have hm := P.hm
  have hlenSm := P.len_le S hS
  have hlenRm := P.len_le R hR
  have h2S := P.two_le_len S hS
  have hg : (P.start S - P.start L).val = P.len L - P.len S :=
    P.val_start_sub_start_of_rightPoint_eq hS hL hptL (le_of_lt hlenL)
  have hne : P.start L ≠ P.start S := by
    intro h
    rw [h, sub_self] at hg
    simp only [Fin.val_zero] at hg
    omega
  have hneR : P.start L ≠ P.start R := by rw [← hptR]; exact hne
  have hd : (P.start S - P.start L).val < P.len L := by omega
  have hdR : (P.start R - P.start L).val < P.len L := by rw [← hptR]; exact hd
  have harc := P.cross_arc L hL R hR hcross
  -- `R`'s arc cannot reach back to `L`'s start, else the two cover the polygon
  have hb : P.len R ≤ (P.start L - P.start R).val := by
    by_contra hcon
    push Not at hcon
    exact harc.2.2.2 (arcSet_union_eq_univ hneR hdR hcon)
  have hinter : P.outsideIn L ∩ P.outsideIn R = P.outsideIn S := by
    rw [P.outsideIn_eq_arc hL, P.outsideIn_eq_arc hR, P.outsideIn_eq_arc hS,
      arcSet_inter_of_mem_of_notMem hneR hdR hb, ← hptR]
    congr 1
    omega
  obtain ⟨r, hr, hrL⟩ := P.exists_atom_disjoint hL
  refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
    (nearMinCut_inter hx (hC.nearMin L hL) (hC.nearMin R hR) hcross)
    ((hC.nearMin S hS).mono (by linarith))
    (unionOfAtoms_inter (fun a ha => atom_subset_or_disjoint ha hL)
      (fun a ha => atom_subset_or_disjoint ha hR))
    (fun a ha => atom_subset_or_disjoint ha hS) ?_ ?_
    ⟨r, hr, hrL.mono_right Finset.inter_subset_left, hrL.mono_right hsubL⟩
  · rw [P.outsideIn_inter, hinter]
  · rw [P.outsideIn_inter, hinter, P.outsideIn_eq_arc hS]
    refine ⟨P.start S, mem_arcSet.mpr ?_⟩
    rw [sub_self]
    simp only [Fin.val_zero]
    omega

/-- **KKO22 Lemma 5.7, second step**: if `L ∩ R = S` then every edge of
`δ(S)` lies in `δ(L)` or `δ(R)`.  An edge of `δ(S)` has an endpoint in
`S = L ∩ R`, hence in both, and its other endpoint outside `L ∩ R`, hence
outside one of them. -/
theorem cutEdges_subset_union_of_inter_eq {S L R : Finset (Fin n)}
    (h : L ∩ R = S) : cutEdges S ⊆ cutEdges L ∪ cutEdges R := by
  intro e he
  rw [cutEdges_eq_betweenEdges, betweenEdges, Finset.mem_filter] at he
  obtain ⟨-, u, huS, v, hvS, rfl⟩ := he
  rw [Finset.mem_compl] at hvS
  rw [← h, Finset.mem_inter] at huS
  rcases Finset.mem_inter.not.mp (h ▸ hvS) with hv
  by_cases hvL : v ∈ L
  · refine Finset.mem_union_right _ ?_
    rw [cutEdges_eq_betweenEdges, betweenEdges, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, u, huS.2, v, Finset.mem_compl.mpr ?_, rfl⟩
    intro hvR
    exact hv ⟨hvL, hvR⟩
  · refine Finset.mem_union_left _ ?_
    rw [cutEdges_eq_betweenEdges, betweenEdges, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, u, huS.1, v, Finset.mem_compl.mpr hvL, rfl⟩

/-- The cut is the disjoint union of the three arrow sets. -/
theorem cutEdges_eq_arrow_union {S L R : Finset (Fin n)}
    (hd : Disjoint (L \ S) (R \ S)) :
    cutEdges S = (arrowLeft S L ∪ arrowRight S R) ∪ arrowCirc S L R := by
  have hsub : arrowLeft S L ∪ arrowRight S R ⊆ cutEdges S :=
    Finset.union_subset (arrowLeft_subset_cut S L) (arrowRight_subset_cut S R)
  have h2 : arrowCirc S L R
      = cutEdges S \ (arrowLeft S L ∪ arrowRight S R) := by
    rw [arrowCirc, sdiff_sdiff_left]
    rfl
  rw [h2, Finset.union_sdiff_of_subset hsub]

/-- Endpoint extraction for cut edges. -/
theorem mem_cutEdges_iff {S : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ cutEdges S ↔ ∃ u ∈ S, ∃ v, v ∉ S ∧ e = s(u, v) := by
  rw [cutEdges_eq_betweenEdges, betweenEdges, Finset.mem_filter]
  constructor
  · rintro ⟨-, u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, Finset.mem_compl.mp hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨Finset.mem_univ _, u, hu, v, Finset.mem_compl.mpr hv, rfl⟩

theorem mem_betweenEdges_iff {A B : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ betweenEdges A B ↔ ∃ u ∈ A, ∃ v ∈ B, e = s(u, v) := by
  rw [betweenEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-! ### `L ∪ R` is almost diagonal

Corollary 5.8's third case applies Lemma 4.27 with `U = L ∪ R` as the
central cut.  `U` is not a member of `𝒞`, which is exactly why 4.27 is
needed at the paper's generality. -/

/-- Unions of unions-of-atoms are unions of atoms. -/
theorem unionOfAtoms_union {S T : Finset (Fin n)}
    (hS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S)
    (hT : ∀ a ∈ atoms 𝒞, a ⊆ T ∨ Disjoint a T) :
    ∀ a ∈ atoms 𝒞, a ⊆ S ∪ T ∨ Disjoint a (S ∪ T) := by
  intro a ha
  rcases hS a ha with h1 | h1
  · exact Or.inl (h1.trans Finset.subset_union_left)
  · rcases hT a ha with h2 | h2
    · exact Or.inl (h2.trans Finset.subset_union_right)
    · exact Or.inr (Finset.disjoint_union_right.mpr ⟨h1, h2⟩)

/-- Outside atoms of a union, for cuts that are unions of atoms.  An atom
inside `S ∪ T` meets one of them, and being an atom it then sits inside
that one. -/
theorem outsideIn_union (P : PolygonRep 𝒞) {S T : Finset (Fin n)}
    (hS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S)
    (hT : ∀ a ∈ atoms 𝒞, a ⊆ T ∨ Disjoint a T) :
    P.outsideIn (S ∪ T) = P.outsideIn S ∪ P.outsideIn T := by
  ext i
  rw [Finset.mem_union, P.mem_outsideIn, P.mem_outsideIn, P.mem_outsideIn]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨v, hv⟩ := P.out_nonempty i
    rcases Finset.mem_union.mp (h hv) with hvS | hvT
    · exact Or.inl ((hS _ (P.out_atom i)).resolve_right
        fun hd => Finset.disjoint_left.mp hd hv hvS)
    · exact Or.inr ((hT _ (P.out_atom i)).resolve_right
        fun hd => Finset.disjoint_left.mp hd hv hvT)
  · rcases h with h | h
    · exact h.trans Finset.subset_union_left
    · exact h.trans Finset.subset_union_right

/-- **The union arc is proper.**  Two overlapping arcs of the component span
fewer than `m` polygon points — otherwise they would cover the polygon, which
Fact 4.8 forbids. -/
theorem union_arc_lt (P : PolygonRep 𝒞) {A B : Finset (Fin n)} (hA : A ∈ 𝒞)
    (hB : B ∈ 𝒞) (hd : (P.start B - P.start A).val < P.len A) :
    max (P.len A) ((P.start B - P.start A).val + P.len B) < P.m := by
  have hcov : arcSet (P.start A) (P.len A) ∪ arcSet (P.start B) (P.len B)
      ≠ Finset.univ := P.arcs_ne_univ A hA B hB
  by_contra hcon
  push Not at hcon
  refine hcov ?_
  rw [arcSet_union_of_mem hd hcov]
  refine Finset.eq_univ_of_forall fun i => ?_
  rw [mem_arcSet]
  exact lt_of_lt_of_le (Fin.is_lt _) hcon

/-- **Cuts sharing a vertex have meeting arcs.**

If the arcs were disjoint the two cuts would *cross*: their leftmost outside
atoms are nonempty and lie one in each difference (each is outside the other
cut precisely because the arcs miss each other), the shared vertex fills the
intersection, and the root atom keeps the union proper.  But crossing cuts
have crossing arcs (Observation 4.4), and crossing arcs meet.

So no cell structure is needed for this — contrary to what the shape of the
statement suggests, a shared vertex *does* force the outside arcs to
overlap, even when the shared vertex is an inside atom. -/
theorem arcs_meet_of_shared_vertex (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) {a : Fin n} (haA : a ∈ A) (haB : a ∈ B) :
    (arcSet (P.start A) (P.len A) ∩ arcSet (P.start B) (P.len B)).Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty,
    ← Finset.disjoint_iff_inter_eq_empty] at hcon
  have h2A := P.two_le_len A hA
  have h2B := P.two_le_len B hB
  have hAmem : P.start A ∈ arcSet (P.start A) (P.len A) := by
    rw [mem_arcSet, sub_self]; simp only [Fin.val_zero]; omega
  have hBmem : P.start B ∈ arcSet (P.start B) (P.len B) := by
    rw [mem_arcSet, sub_self]; simp only [Fin.val_zero]; omega
  obtain ⟨u, hu⟩ := P.out_nonempty (P.start A)
  obtain ⟨v, hv⟩ := P.out_nonempty (P.start B)
  have hcross : Crossing A B := by
    refine ⟨⟨a, Finset.mem_inter.mpr ⟨haA, haB⟩⟩, ⟨u, ?_⟩, ⟨v, ?_⟩,
      P.union_ne_univ hA hB⟩
    · refine Finset.mem_sdiff.mpr ⟨P.leftmost_atom hA hu, ?_⟩
      rcases atom_subset_or_disjoint (P.out_atom (P.start A)) hB with h | h
      · exact absurd ((P.outside_eq_arc B hB _).mp h)
          (fun hm => Finset.disjoint_left.mp hcon hAmem hm)
      · exact Finset.disjoint_left.mp h hu
    · refine Finset.mem_sdiff.mpr ⟨P.leftmost_atom hB hv, ?_⟩
      rcases atom_subset_or_disjoint (P.out_atom (P.start B)) hA with h | h
      · exact absurd ((P.outside_eq_arc A hA _).mp h)
          (fun hm => Finset.disjoint_right.mp hcon hBmem hm)
      · exact Finset.disjoint_left.mp h hv
  obtain ⟨w, hw⟩ := (P.cross_arc A hA B hB hcross).1
  rw [Finset.mem_inter] at hw
  exact Finset.disjoint_left.mp hcon hw.1 hw.2

/-- **Cuts sharing a vertex overlap in one of the two orientations.**

The undirected consequence of `arcs_meet_of_shared_vertex`.  Which of the two
disjuncts holds is the *orientation*, and it is not determined by this
data — see `lemma54_right_of_oriented_geometry`. -/
theorem overlap_of_shared_vertex (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) {a : Fin n} (haA : a ∈ A) (haB : a ∈ B) :
    (P.start B - P.start A).val < P.len A ∨
      (P.start A - P.start B).val < P.len B := by
  rcases eq_or_ne (P.start A) (P.start B) with heq | hne
  · have h2A := P.two_le_len A hA
    rw [heq, sub_self]
    simp only [Fin.val_zero]
    exact Or.inr (by have := P.two_le_len B hB; omega)
  · exact arc_mem_or_mem_of_inter hne
      (P.arcs_meet_of_shared_vertex hA hB haA haB)

/-- Cuts whose arcs nest do not cross: crossing cuts have crossing arcs, and
crossing arcs each leave the other. -/
theorem not_crossing_of_arc_subset (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hnest : arcSet (P.start B) (P.len B) ⊆ arcSet (P.start A) (P.len A)) :
    ¬ Crossing A B := by
  intro hc
  obtain ⟨j, hj⟩ := (P.cross_arc A hA B hB hc).2.2.1
  rw [Finset.mem_sdiff] at hj
  exact hj.2 (hnest hj.1)

/-- Two cuts that do not cross, share a vertex, and have a proper union are
nested as *sets*.  (`side_subset_of_not_crossing` with the two impossible
Venn cases discharged.) -/
theorem subset_or_subset_of_not_crossing {A B : Finset (Fin n)}
    (h : ¬ Crossing A B) (hinter : (A ∩ B).Nonempty)
    (hunion : A ∪ B ≠ Finset.univ) : A ⊆ B ∨ B ⊆ A := by
  rcases side_subset_of_not_crossing h with (h' | h') | (h' | h')
  · exact Or.inr h'
  · -- `Bᶜ ⊆ A` would cover `V`
    refine absurd (Finset.eq_univ_iff_forall.mpr fun v => ?_) hunion
    rw [Finset.mem_union]
    by_cases hv : v ∈ B
    · exact Or.inr hv
    · exact Or.inl (h' (Finset.mem_compl.mpr hv))
  · -- `B ⊆ Aᶜ` would empty the intersection
    obtain ⟨v, hv⟩ := hinter
    rw [Finset.mem_inter] at hv
    exact absurd hv.1 (Finset.mem_compl.mp (h' hv.2))
  · exact Or.inl (Finset.compl_subset_compl.mp h')

/-- **The nested configuration, isolated.**  If `B`'s arc sits inside `A`'s,
then one cut contains the other.

KKO's "WLOG `q` is the rightmost point of the interval `O(L(p) ∪ L(q))`"
*does* include this configuration — when the arcs nest, `L(q)` is the outer
interval and `q` is still its rightmost point — but their written proof
silently treats only proper overlap: neither cut crosses the other here, so
Claim 5.9's rightmost-atom step has nothing to bite on.  What §5.3 needs is
a case split, not a new assumption; the nested branch is
`lemma54_right_of_nested_geometry` below, and this lemma is its first move —
one cut simply contains the other. -/
theorem subset_of_arc_nested (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hnest : arcSet (P.start B) (P.len B) ⊆ arcSet (P.start A) (P.len A))
    (hinter : (A ∩ B).Nonempty) : A ⊆ B ∨ B ⊆ A :=
  subset_or_subset_of_not_crossing (P.not_crossing_of_arc_subset hA hB hnest)
    hinter (P.union_ne_univ hA hB)

/-- **The rightmost outside atom of `B` lies outside `A`**, when `B`'s arc
reaches past `A`'s right end.

This is the step KKO state twice in §5.3 without proof — "`L(q)`'s rightmost
atom is in `L(q)^∩R ∖ L(p)`", and in Claim 5.9 "the rightmost atom of `L(q)`
is in `L(q) ∖ L(p)`" — both consequences of `q` being the rightmost point of
the interval `O(L(p) ∪ L(q))`.  In offsets it is immediate: the last index of
`B`'s arc sits at offset `d + len B − 1` from `start A`, which is at least
`len A` exactly when `B` reaches past `A`. -/
theorem exists_last_atom_notMem (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hd : (P.start B - P.start A).val < P.len A)
    (hpast : P.len A < (P.start B - P.start A).val + P.len B) :
    ∃ i : Fin P.m, (i - P.start B).val = P.len B - 1 ∧
      P.out i ⊆ B ∧ ¬ (P.out i ⊆ A) := by
  have hm := P.hm
  have h2B := P.two_le_len B hB
  have hmB := P.len_le B hB
  have hlt := P.union_arc_lt hA hB hd
  obtain ⟨i, hival, himem⟩ :=
    exists_last_mem_arcSet (P.start B) (l := P.len B) (by omega) (by omega)
  refine ⟨i, hival, (P.outside_eq_arc B hB i).mpr himem, fun hsub => ?_⟩
  have h := mem_arcSet.mp ((P.outside_eq_arc A hA i).mp hsub)
  have hrel := val_sub_rel i (P.start A) (P.start B)
  rw [Nat.mod_eq_of_lt (by omega)] at hrel
  omega

/-- **The nested orientation gives containment of the cuts.**  If `L(p)`'s
arc sits inside `L(q)`'s and the two share a vertex, then `L(p) ⊆ L(q)` —
provided their right polygon points differ.  (The alternative `L(q) ⊆ L(p)`
would nest the arcs both ways, forcing the cuts to coincide.) -/
theorem subset_of_nested_arcs (P : PolygonRep 𝒞) {Lp Lq : Finset (Fin n)}
    (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hne : P.rightPoint Lp ≠ P.rightPoint Lq)
    (hnest : (P.start Lp - P.start Lq).val + P.len Lp ≤ P.len Lq)
    (hinter : (Lq ∩ Lp).Nonempty) : Lp ⊆ Lq := by
  have hm := P.hm
  have h2Lq := P.two_le_len Lq hLq
  have hmLp := P.len_le Lp hLp
  have hmLq := P.len_le Lq hLq
  have harc : arcSet (P.start Lp) (P.len Lp)
      ⊆ arcSet (P.start Lq) (P.len Lq) := arcSet_subset (by omega) (by omega)
  rcases P.subset_of_arc_nested hLq hLp harc hinter with h | h
  · -- `Lq ⊆ Lp` nests the arcs both ways, collapsing the pair
    exfalso
    have houts : P.outsideIn Lq ⊆ P.outsideIn Lp := fun i hi =>
      P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans h)
    rw [P.outsideIn_eq_arc hLq, P.outsideIn_eq_arc hLp] at houts
    have hconv := le_of_arcSet_subset houts (by omega) (by omega)
    rcases eq_or_ne (P.start Lp) (P.start Lq) with heq | hne2
    · have h0 : (P.start Lp - P.start Lq).val = 0 := by
        rw [heq, sub_self]
        simp only [Fin.val_zero]
      have h0' : (P.start Lq - P.start Lp).val = 0 := by
        rw [heq, sub_self]
        simp only [Fin.val_zero]
      have hlen : P.len Lp = P.len Lq := by omega
      exact hne (by rw [P.arc_injective Lp hLp Lq hLq heq hlen])
    · have hsum := val_sub_add_val_sub hne2
      omega
  · exact h

/-- **The nested inner arc is swallowed by a right-crosser containing its
start.**  If `L(p)`'s arc sits inside `L(q)`'s and `start L(p)` lies in the
arc of a cut crossing `L(q)` on the right, then all of `L(p)`'s arc does: the
crosser reaches past `L(q)`'s right end, hence past `L(p)`'s.  The apparent
wrap-around alternative would make the arcs of `L(q)` and the crosser cover
the polygon, which Fact 4.8 (`union_arc_lt`) forbids. -/
theorem arc_subset_of_nested_of_mem (P : PolygonRep 𝒞)
    {Lp Lq LqR : Finset (Fin n)} (hLq : Lq ∈ 𝒞) (hLqR : LqR ∈ 𝒞)
    (hcr : P.CrossesOnRight LqR Lq)
    (hnest : (P.start Lp - P.start Lq).val + P.len Lp ≤ P.len Lq)
    (hmem : P.start Lp ∈ arcSet (P.start LqR) (P.len LqR)) :
    arcSet (P.start Lp) (P.len Lp) ⊆ arcSet (P.start LqR) (P.len LqR) := by
  have hm := P.hm
  have hmLqR := P.len_le LqR hLqR
  have hdR : (P.start LqR - P.start Lq).val < P.len Lq := mem_arcSet.mp hcr.2
  have hcov := P.union_arc_lt hLq hLqR hdR
  -- the crosser reaches past `L(q)`'s right end
  have hrp := mem_arcSet.mp
    (P.rightPoint_mem_arc_of_crossesOnRight hLq hLqR hcr)
  have hrpv := P.val_rightPoint_sub_start hLq
  have hpastR : P.len Lq < (P.start LqR - P.start Lq).val + P.len LqR := by
    have hv := val_sub_of_le (s := P.start Lq) (α := P.start LqR)
      (β := P.rightPoint Lq) (by omega)
    omega
  rcases lt_or_ge (P.start Lp - P.start Lq).val (P.start LqR - P.start Lq).val
    with hlt | hge
  · -- wrap-around: the crosser would have to reach `start L(p)` from the
    -- left, covering the polygon together with `L(q)`
    exfalso
    have hne : P.start LqR ≠ P.start Lq := by
      intro heq
      rw [heq, sub_self] at hlt
      simp only [Fin.val_zero] at hlt
      omega
    have hsum := val_sub_add_val_sub hne
    have hrel := val_sub_rel (P.start Lp) (P.start LqR) (P.start Lq)
    rw [Nat.mod_eq_of_lt (by omega)] at hrel
    have hmemv := mem_arcSet.mp hmem
    omega
  · have hδ := val_sub_of_le (s := P.start Lq) (α := P.start LqR)
      (β := P.start Lp) hge
    exact arcSet_subset (by omega) (by omega)

/-- **The last outside atom of the outer cut lies outside the inner one** —
the nested counterpart of `exists_last_atom_notMem`.  Distinct right points
make the nesting strict at the right end, so `L(q)`'s rightmost atom sits at
an offset `L(p)`'s arc does not reach. -/
theorem exists_last_atom_notMem_of_nested (P : PolygonRep 𝒞)
    {Lp Lq : Finset (Fin n)} (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hne : P.rightPoint Lp ≠ P.rightPoint Lq)
    (hnest : (P.start Lp - P.start Lq).val + P.len Lp ≤ P.len Lq) :
    ∃ i : Fin P.m, (i - P.start Lq).val = P.len Lq - 1 ∧
      P.out i ⊆ Lq ∧ ¬ (P.out i ⊆ Lp) := by
  have hm := P.hm
  have h2Lp := P.two_le_len Lp hLp
  have h2Lq := P.two_le_len Lq hLq
  have hmLq := P.len_le Lq hLq
  -- distinct right points make the nesting strict at the right end
  have hstrict : (P.start Lp - P.start Lq).val + P.len Lp < P.len Lq := by
    rcases lt_or_eq_of_le hnest with h | h
    · exact h
    · exfalso
      have hrel := val_sub_rel (P.rightPoint Lp) (P.start Lq) (P.start Lp)
      rw [P.val_rightPoint_sub_start hLp, Nat.mod_eq_of_lt (by omega)] at hrel
      have h2 := P.val_rightPoint_sub_start hLq
      have hv : (P.rightPoint Lp - P.start Lq).val
          = (P.rightPoint Lq - P.start Lq).val := by omega
      exact hne (sub_left_inj.mp (Fin.val_injective hv))
  obtain ⟨i, hival, himem⟩ :=
    exists_last_mem_arcSet (P.start Lq) (l := P.len Lq) (by omega) (by omega)
  refine ⟨i, hival, (P.outside_eq_arc Lq hLq i).mpr himem, fun hsub => ?_⟩
  have hiA := mem_arcSet.mp ((P.outside_eq_arc Lp hLp i).mp hsub)
  have hv := val_sub_of_le (s := P.start Lq) (α := P.start Lp) (β := i)
    (by omega)
  omega

/-- **The last outside atom of a cut lies in its intersection with any
right-crosser**: the shared atoms form the tail of the cut's arc, and the
last atom is in every tail. -/
theorem out_last_subset_inter (P : PolygonRep 𝒞) {Lq LqR : Finset (Fin n)}
    (hLq : Lq ∈ 𝒞) (hcr : P.CrossesOnRight LqR Lq)
    (hUarc : P.IsArcOf (Lq ∩ LqR) (P.start LqR)
      (P.len Lq - (P.start LqR - P.start Lq).val))
    {i : Fin P.m} (hival : (i - P.start Lq).val = P.len Lq - 1) :
    P.out i ⊆ Lq ∩ LqR := by
  have hm := P.hm
  have h2Lq := P.two_le_len Lq hLq
  have hmLq := P.len_le Lq hLq
  have hγ : (P.start LqR - P.start Lq).val < P.len Lq := mem_arcSet.mp hcr.2
  refine (P.out_subset_iff_mem_arc hUarc i).mpr ?_
  rw [mem_arcSet]
  rcases eq_or_ne (P.start LqR) (P.start Lq) with heq | hne
  · rw [heq, hival, sub_self]
    simp only [Fin.val_zero]
    omega
  · have hsum := val_sub_add_val_sub hne
    have hrel := val_sub_rel i (P.start LqR) (P.start Lq)
    rw [hival, show P.len Lq - 1 + (P.start Lq - P.start LqR).val
        = P.m + (P.len Lq - 1 - (P.start LqR - P.start Lq).val) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
    omega

/-- **The first outside atom of `B` lies outside `A`** whenever `A`'s arc
starts strictly inside `B`'s — the left-side counterpart of both
`exists_last_atom_notMem` and its nested variant at once.  The leftmost
atom of `B` sits at `start B` itself, and `A`'s arc reaching back to it
would cover the polygon together with `B`'s (`union_arc_lt`), so a single
hypothesis serves the proper-overlap and nested configurations alike. -/
theorem out_start_notMem (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hne : P.start A ≠ P.start B)
    (hd : (P.start A - P.start B).val < P.len B) :
    P.out (P.start B) ⊆ B ∧ ¬ (P.out (P.start B) ⊆ A) := by
  have hm := P.hm
  have h2B := P.two_le_len B hB
  have hcov := P.union_arc_lt hB hA hd
  constructor
  · refine (P.outside_eq_arc B hB _).mpr (mem_arcSet.mpr ?_)
    rw [sub_self]
    simp only [Fin.val_zero]
    omega
  · intro hsub
    have hmem := mem_arcSet.mp ((P.outside_eq_arc A hA _).mp hsub)
    have he : 0 < (P.start A - P.start B).val := by
      rcases Nat.eq_zero_or_pos (P.start A - P.start B).val with h0 | h0
      · exact absurd (sub_eq_zero.mp (Fin.val_injective (by simpa using h0)))
          hne
      · exact h0
    have hsum := val_sub_add_val_sub hne
    omega

/-- The right polygon point of `B`, measured from `A`'s start. -/
theorem val_rightPoint_sub_start' (P : PolygonRep 𝒞) {A B : Finset (Fin n)}
    (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hd : (P.start B - P.start A).val < P.len A) :
    (P.rightPoint B - P.start A).val
      = (P.start B - P.start A).val + P.len B := by
  have hm := P.hm
  have hlt := P.union_arc_lt hA hB hd
  have hrel := val_sub_rel (P.rightPoint B) (P.start A) (P.start B)
  rw [P.val_rightPoint_sub_start hB, Nat.mod_eq_of_lt (by omega)] at hrel
  omega

/-- **`L ∪ R` is an almost diagonal cut**, with the union arc.  The three
fields come from uncrossing (`nearMinCut_union`), `unionOfAtoms_union`, and
the root atom missing both cuts; the arc is Fact 4.8 through
`arcSet_union_of_mem`. -/
theorem isAlmostDiagonal_union (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {L R : Finset (Fin n)} (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hcR : P.CrossesOnRight R L) :
    P.IsAlmostDiagonal x η (L ∪ R) ∧
      P.IsArcOf (L ∪ R) (P.start L)
        (max (P.len L) ((P.start R - P.start L).val + P.len R)) := by
  have hm := P.hm
  have hmL := P.len_le L hL
  have h2L := P.two_le_len L hL
  have hd : (P.start R - P.start L).val < P.len L := mem_arcSet.mp hcR.2
  have hcov : arcSet (P.start L) (P.len L) ∪ arcSet (P.start R) (P.len R)
      ≠ Finset.univ := P.arcs_ne_univ L hL R hR
  have hunion : P.outsideIn (L ∪ R) = arcSet (P.start L)
      (max (P.len L) ((P.start R - P.start L).val + P.len R)) := by
    rw [P.outsideIn_union (fun a ha => atom_subset_or_disjoint ha hL)
      (fun a ha => atom_subset_or_disjoint ha hR),
      P.outsideIn_eq_arc hL, P.outsideIn_eq_arc hR]
    exact arcSet_union_of_mem hd hcov
  have hlt : max (P.len L) ((P.start R - P.start L).val + P.len R) < P.m :=
    P.union_arc_lt hL hR hd
  have harc : P.IsArcOf (L ∪ R) (P.start L)
      (max (P.len L) ((P.start R - P.start L).val + P.len R)) :=
    ⟨hunion, by omega, hlt⟩
  refine ⟨⟨?_, ?_, ⟨_, _, harc⟩, ?_⟩, harc⟩
  · exact (nearMinCut_union hx (hC.nearMin L hL) (hC.nearMin R hR)
      hcR.1.symm).mono (by linarith)
  · exact unionOfAtoms_union (fun a ha => atom_subset_or_disjoint ha hL)
      (fun a ha => atom_subset_or_disjoint ha hR)
  · exact Finset.disjoint_union_right.mpr
      ⟨P.rootAtom_disjoint L hL, P.rootAtom_disjoint R hR⟩

/-- **KKO22 Corollary 5.8, second half**, reduced to its essential case.

The claim is `E←(L) ∩ E→(R) = ∅` when `R` crosses `L` on the right.  An
edge in both has one endpoint in `L` and one outside `L` (from `E←(L)`),
and one in `R` and one outside `R` (from `E→(R)`); matching the two
descriptions gives exactly two cases.

* If the endpoint outside `L` is *inside* `R`, it lies in
  `(L_L ∖ L) ∩ (R ∖ L)`, which Lemma 4.27 at `L` declares empty.
* If it is outside `R` as well, it lies outside `U = L ∪ R` entirely, so it
  lies in `(L_L ∖ U) ∩ (R_R ∖ U)`.

Both differences are now taken relative to the *same* cut `U`, which is what
makes the second case an instance of Lemma 4.27 as well — at `U`, which is
almost diagonal rather than a member of `𝒞`.  Stating the hypothesis this
way (rather than as `(L_L ∖ U) ∩ (R_R ∖ R)`) costs nothing, since the
endpoint that reaches it is outside `U` anyway. -/
theorem arrowLeft_disjoint_arrowRight_of_diag {L R LL RR : Finset (Fin n)}
    (h427L : Disjoint (LL \ L) (R \ L))
    (hdiag : Disjoint (LL \ (L ∪ R)) (RR \ (L ∪ R))) :
    Disjoint (arrowLeft L LL) (arrowRight R RR) := by
  classical
  rw [Finset.disjoint_left]
  intro e heL heR
  obtain ⟨u, hu, v, hv, huv⟩ := mem_betweenEdges_iff.mp heL
  obtain ⟨p, hp, q, hq, hpq⟩ := mem_betweenEdges_iff.mp heR
  rw [Finset.mem_inter] at hu hp
  rw [Finset.mem_sdiff] at hv hq
  have heq : s(u, v) = s(p, q) := huv ▸ hpq
  rcases Sym2.eq_iff.mp heq with ⟨-, h2⟩ | ⟨-, h2⟩
  · -- the endpoint outside `L` is also outside `R`: the diagonal region.
    -- It is outside `L ∪ R`, so both sides of `hdiag` are relative to `U`.
    have hvnot : v ∉ L ∪ R := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hv.2 h
      · exact hq.2 (h2 ▸ h)
    have hv1 : v ∈ LL \ (L ∪ R) := Finset.mem_sdiff.mpr ⟨hv.1, hvnot⟩
    have hv2 : v ∈ RR \ (L ∪ R) := by
      refine Finset.mem_sdiff.mpr ⟨?_, hvnot⟩
      rw [h2]; exact hq.1
    exact Finset.disjoint_left.mp hdiag hv1 hv2
  · -- the endpoint outside `L` is inside `R`: Lemma 4.27 at `L`
    have hvR : v ∈ R := h2 ▸ hp.1
    exact Finset.disjoint_left.mp h427L
      (Finset.mem_sdiff.mpr ⟨hv.1, hv.2⟩)
      (Finset.mem_sdiff.mpr ⟨hvR, hv.2⟩)

/-- **The diagonal region contains no outside atom.**

Offsets are measured from `start L`.  For a point `j` lying outside both
`L` and `R`, membership in `L_L` is the *suffix* condition
`(start L_L − start L) ≤ (j − start L)` and membership in `R_R` is the
*prefix* condition `(j − start L) < (start R_R − start L) + len R_R`.  A
diagonal outside atom satisfies both while the root satisfies neither, so
the offsets chain into
`d(root) < d(start L_L) ≤ d(i) < d(start R_R) + len R_R ≤ d(root)`.
Geometrically: outside `L ∪ R` is one arc, `L_L` covers a suffix of it
and `R_R` a prefix; a diagonal point makes them overlap, covering the arc
and leaving the root — which lies in no cut — nowhere to sit.

**Auxiliary, and off the mainline path.**  The argument places the root on
the arc and derives a numeric contradiction, so it needs `HasOutsideRoot` —
the root as a polygon *point* — which KKO22 §4.2 do not grant in general.
Corollary 5.8 no longer routes through it: with Lemma 4.27 available at the
paper's generality, the diagonal case is 4.27 at `L ∪ R`.  This is kept as a
clearly-named special case for the polygons that do have an outside root;
nothing in the development depends on it. -/
theorem no_outside_atom_diag (P : PolygonRep 𝒞) (hor : P.HasOutsideRoot)
    {L R LL RR : Finset (Fin n)}
    (hL : L ∈ 𝒞) (hR : R ∈ 𝒞) (hLLm : LL ∈ 𝒞) (hRRm : RR ∈ 𝒞)
    (hcR : P.CrossesOnRight R L) (hcLL : P.CrossesOnLeft LL L)
    (hcRR : P.CrossesOnRight RR R) :
    ∀ i : Fin P.m, ¬ (P.out i ⊆ (LL ∩ RR) \ (L ∪ R)) := by
  classical
  have hm := P.hm
  have h2L := P.two_le_len L hL
  have h2R := P.two_le_len R hR
  have h2LL := P.two_le_len LL hLLm
  have h2RR := P.two_le_len RR hRRm
  have hmLL := P.len_le LL hLLm
  have hmRR := P.len_le RR hRRm
  -- crossing-side exclusivity: each start lies outside the cut it crosses
  have hLLout : P.len L ≤ (P.start LL - P.start L).val :=
    mem_arcSet_compl.mp fun hmem =>
      P.not_crossesOnLeft_and_crossesOnRight hLLm hL ⟨hcLL, hcLL.1, hmem⟩
  have hRout : P.len R ≤ (P.start L - P.start R).val :=
    mem_arcSet_compl.mp fun hmem =>
      P.not_crossesOnLeft_and_crossesOnRight hR hL ⟨⟨hcR.1, hmem⟩, hcR⟩
  have hRRout : P.len RR ≤ (P.start R - P.start RR).val :=
    mem_arcSet_compl.mp fun hmem =>
      P.not_crossesOnLeft_and_crossesOnRight hRRm hR ⟨⟨hcRR.1, hmem⟩, hcRR⟩
  have hFL : (P.start L - P.start LL).val < P.len LL := mem_arcSet.mp hcLL.2
  have hρL : (P.start R - P.start L).val < P.len L := mem_arcSet.mp hcR.2
  have hτR : (P.start RR - P.start R).val < P.len R := mem_arcSet.mp hcRR.2
  -- distinctness, hence complementary offset sums
  have hneLL : P.start LL ≠ P.start L := by
    intro h
    rw [h, sub_self] at hLLout
    simp only [Fin.val_zero] at hLLout
    omega
  have hneR : P.start R ≠ P.start L := by
    intro h
    rw [h, sub_self] at hRout
    simp only [Fin.val_zero] at hRout
    omega
  have hneRR : P.start RR ≠ P.start R := by
    intro h
    rw [h, sub_self] at hRRout
    simp only [Fin.val_zero] at hRRout
    omega
  have hsumLL := val_sub_add_val_sub hneLL
  have hsumR := val_sub_add_val_sub hneR
  have hsumRR := val_sub_add_val_sub hneRR
  -- `start R_R` sits at offset `(start R_R − start R) + (start R − start L)`
  have hσ : (P.start RR - P.start L).val
      = (P.start RR - P.start R).val + (P.start R - P.start L).val := by
    have hrel := val_sub_rel (P.start RR) (P.start L) (P.start R)
    rw [Nat.mod_eq_of_lt (by omega)] at hrel
    exact hrel
  have hneRRL : P.start RR ≠ P.start L := by
    intro h
    rw [h, sub_self] at hσ
    simp only [Fin.val_zero] at hσ
    omega
  have hsumRRL := val_sub_add_val_sub hneRRL
  -- `L_L` does not swallow `L`, so its overlap with `L` is short
  have hcrossLL : P.len LL < P.len L + (P.start L - P.start LL).val := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := (P.cross_arc LL hLLm L hL hcLL.1).2.2.1
    rw [Finset.mem_sdiff] at hw
    refine hw.2 ?_
    have hwL := mem_arcSet.mp hw.1
    have hrel := val_sub_rel w (P.start LL) (P.start L)
    rw [Nat.mod_eq_of_lt (by omega)] at hrel
    rw [mem_arcSet]
    omega
  -- being outside `R` is an offset bound
  have houtR : ∀ j : Fin P.m, P.len L ≤ (j - P.start L).val →
      j ∉ arcSet (P.start R) (P.len R) →
      (P.start R - P.start L).val + P.len R ≤ (j - P.start L).val := by
    intro j hj hjR
    have h := mem_arcSet_compl.mp hjR
    have hjm : (j - P.start L).val < P.m := Fin.is_lt _
    have hrel := val_sub_rel j (P.start R) (P.start L)
    rw [show (j - P.start L).val + (P.start L - P.start R).val
        = P.m + ((j - P.start L).val - (P.start R - P.start L).val) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
    omega
  -- membership in `L_L` is a suffix condition
  have hmemLL : ∀ j : Fin P.m, P.len L ≤ (j - P.start L).val →
      (j ∈ arcSet (P.start LL) (P.len LL) ↔
        (P.start LL - P.start L).val ≤ (j - P.start L).val) := by
    intro j hj
    have hjm : (j - P.start L).val < P.m := Fin.is_lt _
    have hrel := val_sub_rel j (P.start LL) (P.start L)
    rw [mem_arcSet]
    constructor
    · intro hmem
      by_contra hcon
      push Not at hcon
      rw [Nat.mod_eq_of_lt (by omega)] at hrel
      omega
    · intro hge
      rw [show (j - P.start L).val + (P.start L - P.start LL).val
          = P.m + ((j - P.start L).val - (P.start LL - P.start L).val) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
      omega
  -- membership in `R_R` is a prefix condition
  have hmemRR : ∀ j : Fin P.m,
      (P.start R - P.start L).val + P.len R ≤ (j - P.start L).val →
      (j ∈ arcSet (P.start RR) (P.len RR) ↔
        (j - P.start L).val < (P.start RR - P.start L).val + P.len RR) := by
    intro j hj
    have hjm : (j - P.start L).val < P.m := Fin.is_lt _
    have hrel := val_sub_rel j (P.start RR) (P.start L)
    rw [show (j - P.start L).val + (P.start L - P.start RR).val
        = P.m + ((j - P.start L).val - (P.start RR - P.start L).val) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
    rw [mem_arcSet, hrel]
    omega
  -- now the chain
  intro i hsub
  obtain ⟨w, hw⟩ := P.out_nonempty i
  have hiLL : P.out i ⊆ LL := fun v hv =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp (hsub hv)).1).1
  have hiRR : P.out i ⊆ RR := fun v hv =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp (hsub hv)).1).2
  have hiaL : i ∉ arcSet (P.start L) (P.len L) := fun h =>
    (Finset.mem_sdiff.mp (hsub hw)).2
      (Finset.mem_union_left _ ((P.outside_eq_arc L hL i).mpr h hw))
  have hiaR : i ∉ arcSet (P.start R) (P.len R) := fun h =>
    (Finset.mem_sdiff.mp (hsub hw)).2
      (Finset.mem_union_right _ ((P.outside_eq_arc R hR i).mpr h hw))
  have hiL1 : P.len L ≤ (i - P.start L).val := mem_arcSet_compl.mp hiaL
  have hiL2 := houtR i hiL1 hiaR
  obtain ⟨r, hr⟩ := hor
  have hrL1 : P.len L ≤ (r - P.start L).val :=
    mem_arcSet_compl.mp (hr L hL)
  have hrL2 := houtR r hrL1 (hr R hR)
  have h1 := (hmemLL i hiL1).mp ((P.outside_eq_arc LL hLLm i).mp hiLL)
  have h2 := (hmemRR i hiL2).mp ((P.outside_eq_arc RR hRRm i).mp hiRR)
  have h3 := (hmemLL r hrL1).not.mp (fun hc => hr LL hLLm hc)
  have h4 := (hmemRR r hrL2).not.mp (fun hc => hr RR hRRm hc)
  push Not at h3 h4
  omega

/-- **KKO22 Corollary 5.8, second half**: for `R` crossing `L` on the
right, `E←(L) ∩ E→(R) = ∅`.

Three applications of Lemma 4.27, at `L`, at `R`, and at `U = L ∪ R`.  The
first two do double duty: besides settling their own endpoint cases they
show `L_L ∖ L` misses `R` and `R_R ∖ R` misses `L`, which is what makes
`L_L ∖ U` and `R_R ∖ U` nonempty and so discharges the `Crossing … U`
conditions for the third.  The arc conditions are free — `start U = start L`,
so "`L_L` crosses `U` on the left" is literally `L_L`'s own arc condition,
and `start R_R` lies in `R`'s arc, which sits inside the union arc.

This needs no root beyond the root *atom*: the earlier route through
`no_outside_atom_diag` (and with it Lemma 4.30 and an outside root) was an
artifact of Lemma 4.27 having been stated only for `S ∈ 𝒞`. -/
theorem arrowLeft_disjoint_arrowRight (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {L R LL RR : Finset (Fin n)}
    (hL : L ∈ 𝒞) (hR : R ∈ 𝒞) (hcR : P.CrossesOnRight R L)
    (hLL : P.IsSL L LL) (hRR : P.IsSR R RR) :
    Disjoint (arrowLeft L LL) (arrowRight R RR) := by
  -- Lemma 4.27 at `L`, and at `R` (where `L` crosses on the left)
  have h427L : Disjoint (LL \ L) (R \ L) :=
    P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hL hLL.1 hR hLL.2.1 hcR
  have hcL : P.CrossesOnLeft L R := ⟨hcR.1.symm, hcR.2⟩
  have h427R : Disjoint (L \ R) (RR \ R) :=
    P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hR hL hRR.1 hcL hRR.2.1
  refine arrowLeft_disjoint_arrowRight_of_diag h427L ?_
  -- Lemma 4.27 at the almost diagonal `U = L ∪ R`
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_union hx hC hL hR hcR
  have hm := P.hm
  have hmL := P.len_le L hL
  have h2L := P.two_le_len L hL
  have hd : (P.start R - P.start L).val < P.len L := mem_arcSet.mp hcR.2
  -- `LL ∖ L` misses `R` entirely (4.27 at `L`), so `LL ∖ U = LL ∖ L`
  have hLLU : ∀ v, v ∈ LL \ L → v ∉ L ∪ R := by
    intro v hv hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact (Finset.mem_sdiff.mp hv).2 h
    · exact Finset.disjoint_left.mp h427L hv
        (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hv).2⟩)
  -- symmetrically `RR ∖ R` misses `L`
  have hRRU : ∀ v, v ∈ RR \ R → v ∉ L ∪ R := by
    intro v hv hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.disjoint_left.mp h427R
        (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hv).2⟩) hv
    · exact (Finset.mem_sdiff.mp hv).2 h
  have hcLLU : P.CrossesOnLeftArc LL (L ∪ R) (P.start L) := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hLL.2.1.2⟩
    · obtain ⟨v, hv⟩ := hLL.2.1.1.1
      exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
        Finset.mem_union_left _ (Finset.mem_inter.mp hv).2⟩⟩
    · obtain ⟨v, hv⟩ := hLL.2.1.1.2.1
      exact ⟨v, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hLLU v hv⟩⟩
    · obtain ⟨v, hv⟩ := hLL.2.1.1.2.2.1
      exact ⟨v, Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hv).1,
          (Finset.mem_sdiff.mp hv).2⟩⟩
    · intro hcov
      obtain ⟨v, hv⟩ := P.rootAtom_nonempty
      have : v ∈ LL ∪ (L ∪ R) := hcov ▸ Finset.mem_univ v
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint LL hLL.1) hv h
      · exact Finset.disjoint_left.mp
          (Finset.disjoint_union_right.mpr
            ⟨P.rootAtom_disjoint L hL, P.rootAtom_disjoint R hR⟩) hv h
  have hcRRU : P.CrossesOnRightArc RR (L ∪ R) (P.start L)
      (max (P.len L) ((P.start R - P.start L).val + P.len R)) := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · obtain ⟨v, hv⟩ := hRR.2.1.1.1
      exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp hv).2⟩⟩
    · obtain ⟨v, hv⟩ := hRR.2.1.1.2.1
      exact ⟨v, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hRRU v hv⟩⟩
    · obtain ⟨v, hv⟩ := hRR.2.1.1.2.2.1
      exact ⟨v, Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1,
          (Finset.mem_sdiff.mp hv).2⟩⟩
    · intro hcov
      obtain ⟨v, hv⟩ := P.rootAtom_nonempty
      have : v ∈ RR ∪ (L ∪ R) := hcov ▸ Finset.mem_univ v
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint RR hRR.1) hv h
      · exact Finset.disjoint_left.mp
          (Finset.disjoint_union_right.mpr
            ⟨P.rootAtom_disjoint L hL, P.rootAtom_disjoint R hR⟩) hv h
    · -- `start RR` sits in `R`'s arc, which sits inside the union arc
      have hRRd : (P.start RR - P.start R).val < P.len R :=
        mem_arcSet.mp hRR.2.1.2
      have hUlt : max (P.len L) ((P.start R - P.start L).val + P.len R) < P.m :=
        hUarc.2.2
      have hrel := val_sub_rel (P.start RR) (P.start L) (P.start R)
      rw [Nat.mod_eq_of_lt (by omega)] at hrel
      rw [mem_arcSet]
      omega
  have h427U := P.sdiff_disjoint_of_crossesOnLeftArc_of_crossesOnRightArc
    hx hη0 (by linarith) hC hUad hUarc hLL.1 hRR.1 hcLLU hcRRU
  exact h427U

/-- **KKO22 Lemma 5.7**: `E∘(S) ⊆ E∘(L(p_r)) ∪ E∘(R(p_l))`.

Every input is a result proved above except `hcor58`, the second half of
Corollary 5.8 (`E←(L) ∩ E→(R) = ∅` when `R` crosses `L` on the right),
which KKO dispatch with "a similar argument"; it is the one step of this
lemma still owed.  The rest is the edge chase: an edge of `E∘(S)` lies in
`δ(L) ∪ δ(R)` by `cutEdges_subset_union_of_inter_eq`, and the arrow
decompositions of `δ(L)`, `δ(R)` push it into `E←(L)` or `E→(R)`.  In
either case its endpoint outside `S` is trapped between two sets that
Lemma 4.27 declares disjoint. -/
theorem arrowCirc_subset_union {S L R SL SR LL LR RL RR : Finset (Fin n)}
    (hinterLR : L ∩ R = S)
    (hEleft : arrowLeft S SL = arrowLeft R RL)
    (hEright : arrowRight S SR = arrowRight L LR)
    (hdL : Disjoint (LL \ L) (LR \ L)) (hdR : Disjoint (RL \ R) (RR \ R))
    (h427L : Disjoint (LL \ L) (R \ L)) (h427R : Disjoint (L \ R) (RR \ R))
    (hcor58 : Disjoint (arrowLeft L LL) (arrowRight R RR)) :
    arrowCirc S SL SR ⊆ arrowCirc L LL LR ∪ arrowCirc R RL RR := by
  classical
  intro e he
  by_contra hcon
  rw [Finset.mem_union] at hcon
  push Not at hcon
  obtain ⟨hcL, hcR⟩ := hcon
  rw [arrowCirc, Finset.mem_sdiff, Finset.mem_sdiff] at he
  obtain ⟨⟨heS, henL⟩, henR⟩ := he
  rw [hEleft] at henL
  rw [hEright] at henR
  -- the edge lies in `δ(L)` or `δ(R)`
  have hsplit := cutEdges_subset_union_of_inter_eq hinterLR heS
  -- membership in `δ(L)` forces `E←(L)`; in `δ(R)` forces `E→(R)`
  have hstepL : e ∈ cutEdges L → e ∈ arrowLeft L LL := by
    intro hL
    rw [cutEdges_eq_arrow_union hdL, Finset.mem_union, Finset.mem_union] at hL
    rcases hL with (h | h) | h
    · exact h
    · exact absurd h henR
    · exact absurd h hcL
  have hstepR : e ∈ cutEdges R → e ∈ arrowRight R RR := by
    intro hR
    rw [cutEdges_eq_arrow_union hdR, Finset.mem_union, Finset.mem_union] at hR
    rcases hR with (h | h) | h
    · exact absurd h henL
    · exact h
    · exact absurd h hcR
  -- endpoints of the edge relative to `S = L ∩ R`
  obtain ⟨a, haS, b, hbS, hab⟩ := mem_cutEdges_iff.mp heS
  rcases Finset.mem_union.mp hsplit with hL | hR
  · -- `e ∈ E←(L)`: its outside endpoint sits in `LL ∖ L`
    have heL := hstepL hL
    obtain ⟨u, hu, v, hv, huv⟩ := mem_betweenEdges_iff.mp heL
    rw [Finset.mem_inter] at hu
    rw [Finset.mem_sdiff] at hv
    -- `v ∉ L` hence `v ∉ S`, so `v` is the outside endpoint and `u ∈ S`
    have hvS : v ∉ S := by
      intro hvS'
      rw [← hinterLR] at hvS'
      exact hv.2 (Finset.mem_inter.mp hvS').1
    have huS : u ∈ S := by
      have heq : s(a, b) = s(u, v) := hab ▸ huv
      rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1 ▸ haS
      · exact absurd (h1 ▸ haS) hvS
    have huR : u ∈ R := by
      rw [← hinterLR] at huS
      exact (Finset.mem_inter.mp huS).2
    by_cases hvR : v ∈ R
    · -- both `LL ∖ L` and `R ∖ L`: Lemma 4.27 at `L`
      exact Finset.disjoint_left.mp h427L
        (Finset.mem_sdiff.mpr ⟨hv.1, hv.2⟩)
        (Finset.mem_sdiff.mpr ⟨hvR, hv.2⟩)
    · -- otherwise the edge also crosses `R`, contradicting Corollary 5.8
      have hRcut : e ∈ cutEdges R :=
        mem_cutEdges_iff.mpr ⟨u, huR, v, hvR, huv⟩
      exact Finset.disjoint_left.mp hcor58 heL (hstepR hRcut)
  · -- `e ∈ E→(R)`: symmetric, with Lemma 4.27 at `R`
    have heR := hstepR hR
    obtain ⟨u, hu, v, hv, huv⟩ := mem_betweenEdges_iff.mp heR
    rw [Finset.mem_inter] at hu
    rw [Finset.mem_sdiff] at hv
    have hvS : v ∉ S := by
      intro hvS'
      rw [← hinterLR] at hvS'
      exact hv.2 (Finset.mem_inter.mp hvS').2
    have huS : u ∈ S := by
      have heq : s(a, b) = s(u, v) := hab ▸ huv
      rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1 ▸ haS
      · exact absurd (h1 ▸ haS) hvS
    have huL : u ∈ L := by
      rw [← hinterLR] at huS
      exact (Finset.mem_inter.mp huS).1
    by_cases hvL : v ∈ L
    · -- both `L ∖ R` and `RR ∖ R`: Lemma 4.27 at `R`
      exact Finset.disjoint_left.mp h427R
        (Finset.mem_sdiff.mpr ⟨hvL, hv.2⟩)
        (Finset.mem_sdiff.mpr ⟨hv.1, hv.2⟩)
    · -- otherwise the edge also crosses `L`, contradicting Corollary 5.8
      have hLcut : e ∈ cutEdges L :=
        mem_cutEdges_iff.mpr ⟨u, huL, v, hvL, huv⟩
      exact Finset.disjoint_left.mp hcor58 (hstepL hLcut) heR

/-! ### Towards KKO22 Lemma 5.4

Lemma 5.4 ("every edge is mapped to a constant number of bad events")
says: for polygon points `p ≠ q` and an edge `e = {a,b}` with
`a ∈ L(p) ∩ L(q)`, `e` cannot lie in both `E(B→(p))` and `E(B→(q))`.

Its first step is Fact 4.8, proved below.  The rest needs machinery this
development does not yet have, and it is worth being precise about what:

* the sets `L(p)^∩R = L(p) ∩ L(p)_R` and `L*(p)` (the cut crossing
  `L(p)^∩R` on the left maximizing the shared outside atoms) from the
  display defining `E(B→(p))`.  `L(p)^∩R` is an *intersection of two
  cuts*, so it is not a member of `𝒞`, and `CrossesOnLeft _ L(p)^∩R` is
  not even statable in the present encoding: `start` and `len` are
  constrained only on `𝒞`.  Supporting it means implementing Definition
  4.25 (almost diagonal cuts: `2η`-near min cuts whose outside atoms form
  a contiguous arc) and extending the arc calculus to them.  That is the
  encoding extension the roadmap anticipated, and it is the real
  prerequisite for §5.4.
* Claim 5.9 (`L(p)_R` crosses `L(q)` on the right), whose proof is a
  crossing-transfer argument in the style of §5.1.
* the Definition 4.17 comparison `|O(L(p)_R ∩ L(q))| < |O(L(q)_R ∩ L(q))|`,
  which should reduce to the closed form `card_outsideIn_inter_right`
  once the previous two are available. -/

/-- **`L(p)^∩R` is an almost diagonal cut**, with an explicit arc.

This is what Definition 4.25 buys: the intersection `S ∩ R` of a cut with
one crossing it on the right — the shape of `L(p) ∩ L(p)_R` — is a
`2η`-near min cut, a union of atoms, and its outside atoms are the arc
from `start R` to the right end of `S`.  Before Definition 4.25 this
object had no arc and so could not appear in a statement at all; it is
the missing prerequisite of Lemma 5.4. -/
theorem isAlmostDiagonal_inter (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞)
    {R : Finset (Fin n)} (hR : R ∈ 𝒞) (hcr : P.CrossesOnRight R S) :
    P.IsAlmostDiagonal x η (S ∩ R) ∧
      P.IsArcOf (S ∩ R) (P.start R)
        (P.len S - (P.start R - P.start S).val) := by
  have hm := P.hm
  have hmS := P.len_le S hS
  have hd : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcr.2
  have harc : P.IsArcOf (S ∩ R) (P.start R)
      (P.len S - (P.start R - P.start S).val) := by
    refine ⟨?_, by omega, by omega⟩
    rw [P.outsideIn_inter, P.outsideIn_inter_right_eq_arc hS hR hcr]
  refine ⟨⟨?_, ?_, ⟨_, _, harc⟩, ?_⟩, harc⟩
  · have h := nearMinCut_inter hx (hC.nearMin S hS) (hC.nearMin R hR) hcr.1.symm
    exact h.mono (by linarith)
  · exact unionOfAtoms_inter (fun a ha => atom_subset_or_disjoint ha hS)
      (fun a ha => atom_subset_or_disjoint ha hR)
  · exact (P.rootAtom_disjoint S hS).mono_right Finset.inter_subset_left

/-- **`R(p)^∩L` is an almost diagonal cut**, with an explicit arc — the
mirror of `isAlmostDiagonal_inter`.  The intersection `S ∩ L` of a cut with
one crossing it on the *left* is a `2η`-near min cut whose outside atoms
form the arc from `start S` covering the overlap; it shares its **left**
end with `S` where `S ∩ R` shared its right end. -/
theorem isAlmostDiagonal_inter_left (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞)
    {L : Finset (Fin n)} (hL : L ∈ 𝒞) (hcl : P.CrossesOnLeft L S) :
    P.IsAlmostDiagonal x η (S ∩ L) ∧
      P.IsArcOf (S ∩ L) (P.start S)
        (P.len L - (P.start S - P.start L).val) := by
  have hm := P.hm
  have hmL := P.len_le L hL
  have hd : (P.start S - P.start L).val < P.len L := mem_arcSet.mp hcl.2
  have harc : P.IsArcOf (S ∩ L) (P.start S)
      (P.len L - (P.start S - P.start L).val) := by
    refine ⟨?_, by omega, by omega⟩
    rw [P.outsideIn_inter, P.outsideIn_inter_left_eq_arc hS hL hcl]
  refine ⟨⟨?_, ?_, ⟨_, _, harc⟩, ?_⟩, harc⟩
  · have h := nearMinCut_inter hx (hC.nearMin S hS) (hC.nearMin L hL) hcl.1.symm
    exact h.mono (by linarith)
  · exact unionOfAtoms_inter (fun a ha => atom_subset_or_disjoint ha hS)
      (fun a ha => atom_subset_or_disjoint ha hL)
  · exact (P.rootAtom_disjoint S hS).mono_right Finset.inter_subset_left

/-! ### Lifting the arc calculus to almost diagonal cuts

With Fact 4.26 available, the two calculus lemmas that Lemma 4.29 rests
on generalise: the crossing-side exclusivity and the closed form for the
outside atoms shared with a right-crossing cut.  Both proofs are the
originals with `cross_arc` replaced by `cross_arc_of_almostDiagonal` and
`(start S, len S)` by the supplied arc data. -/

/-- An almost diagonal cut is avoided by some atom: its arc is proper, so
some outside atom lies beyond it.  (The `𝒞` version is
`exists_atom_disjoint`.) -/
theorem exists_atom_disjoint_of_isArcOf (P : PolygonRep 𝒞) {s : Fin P.m}
    {l : ℕ} (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l) :
    ∃ a ∈ atoms 𝒞, Disjoint a S := by
  obtain ⟨heq, hl1, hl2⟩ := harcS
  obtain ⟨i, hi⟩ : ∃ i : Fin P.m, i ∉ arcSet s l := by
    by_contra hcon
    push Not at hcon
    have hall : arcSet s l = Finset.univ := Finset.eq_univ_of_forall hcon
    have hcard : (arcSet s l).card = l := arcSet_card _ (le_of_lt hl2)
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  refine ⟨P.out i, P.out_atom i, ?_⟩
  rcases hSad.unionOfAtoms (P.out i) (P.out_atom i) with h | h
  · exact absurd ((P.out_subset_iff_mem_arc ⟨heq, hl1, hl2⟩ i).mp h) hi
  · exact h

/-- The closed form for the shared outside atoms, for an almost diagonal
cut crossed on the right. -/
theorem outsideIn_inter_rightArc_eq_arc (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {W : Finset (Fin n)} {s : Fin P.m}
    {l : ℕ} (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    (hW : W ∈ 𝒞) (hcr : P.CrossesOnRightArc W S s l) :
    P.outsideIn S ∩ P.outsideIn W
      = arcSet (P.start W) (l - (P.start W - s).val) := by
  have hm := P.hm
  obtain ⟨heq, hl1, hl2⟩ := harcS
  obtain ⟨hc, hmem⟩ := hcr
  have harc := cross_arc_of_almostDiagonal hx hη0 hη hC P
    (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hW) hSad
    (P.isArcOf_of_mem hW) ⟨heq, hl1, hl2⟩ hc
  have hne : P.start W ≠ s := start_ne_of_crossing_arcs harc
  have hsL : s ∉ arcSet (P.start W) (P.len W) := fun hmem' =>
    P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 hη hC hSad
      ⟨heq, hl1, hl2⟩ hW ⟨⟨hc, hmem'⟩, hc, hmem⟩
  have hd := mem_arcSet.mp hmem
  have hb := mem_arcSet_compl.mp hsL
  rw [heq, P.outsideIn_eq_arc hW, arcSet_inter_of_mem_of_notMem hne.symm hd hb]
  have hle : l - (P.start W - s).val ≤ P.len W := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := harc.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_subset (by omega) (by omega) hw.1)
  rw [min_eq_right hle]

/-- The closed form for shared outside atoms, for an almost diagonal cut
crossed on the **left**.  Mirror of `outsideIn_inter_rightArc_eq_arc`;
note these arcs all begin at `s`, so they nest by length. -/
theorem outsideIn_inter_leftArc_eq_arc (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {L : Finset (Fin n)} {s : Fin P.m}
    {l : ℕ} (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    (hL : L ∈ 𝒞) (hcl : P.CrossesOnLeftArc L S s) :
    P.outsideIn S ∩ P.outsideIn L
      = arcSet s (P.len L - (s - P.start L).val) := by
  have hm := P.hm
  obtain ⟨heq, hl1, hl2⟩ := harcS
  obtain ⟨hc, hmem⟩ := hcl
  have harc := cross_arc_of_almostDiagonal hx hη0 hη hC P
    (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hL) hSad
    (P.isArcOf_of_mem hL) ⟨heq, hl1, hl2⟩ hc
  have hne : P.start L ≠ s := start_ne_of_crossing_arcs harc
  have hsR : P.start L ∉ arcSet s l := fun hmem' =>
    P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 hη hC hSad
      ⟨heq, hl1, hl2⟩ hL ⟨⟨hc, hmem⟩, hc, hmem'⟩
  have hd := mem_arcSet.mp hmem
  have hb := mem_arcSet_compl.mp hsR
  have hmlL := P.len_le L hL
  rw [Finset.inter_comm, P.outsideIn_eq_arc hL, heq,
    arcSet_inter_of_mem_of_notMem hne hd hb]
  have hle : P.len L - (s - P.start L).val ≤ l := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := harc.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_subset (by omega) (by omega) hw.1)
  rw [min_eq_right hle]

/-- **KKO22 Lemma 4.29 for almost diagonal cuts.**  The same antitonicity,
with `S` an almost diagonal cut carrying arc `[s, s+l)` rather than a
member of `𝒞`.

The proof is the original with `S`'s arc data supplied as parameters and
its four `𝒞`-dependent appeals routed through the almost-diagonal
counterparts.  The near-min-cut parameters shift from `2η/3η` to `3η/4η`
because `S` is itself a `2η`-cut — which is exactly why KKO state this
form under `η ≤ 1/10`, since Lemma 4.23 needs `4η ≤ 2/5`. -/
theorem inter_subset_inter_of_crossesOnRightArc (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {s : Fin P.m} {l : ℕ}
    (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    {A B : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hcA : P.CrossesOnRightArc A S s l) (hcB : P.CrossesOnRightArc B S s l)
    (hlt : (P.start A - s).val < (P.start B - s).val) :
    B ∩ S ⊆ A ∩ S := by
  classical
  have hm := P.hm
  have hl1 := harcS.2.1
  have hlenS := harcS.2.2
  have hdα : (P.start A - s).val < l := mem_arcSet.mp hcA.2
  have hdβ : (P.start B - s).val < l := mem_arcSet.mp hcB.2
  have harcA := P.outsideIn_inter_rightArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hA hcA
  have harcB := P.outsideIn_inter_rightArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hB hcB
  have hβα : (P.start B - P.start A).val
      = (P.start B - s).val - (P.start A - s).val :=
    val_sub_of_le (le_of_lt hlt)
  have hsub : P.outsideIn S ∩ P.outsideIn B ⊆ P.outsideIn S ∩ P.outsideIn A := by
    rw [harcA, harcB]
    refine arcSet_subset ?_ ?_
    · rw [hβα]; omega
    · omega
  have hout : P.outsideIn ((A ∩ S) ∩ B) = P.outsideIn (S ∩ B) := by
    rw [P.outsideIn_inter, P.outsideIn_inter, P.outsideIn_inter]
    ext i
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hiA, hiS⟩, hiB⟩
      exact ⟨hiS, hiB⟩
    · rintro ⟨hiS, hiB⟩
      exact ⟨⟨(Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hiS, hiB⟩))).2,
        hiS⟩, hiB⟩
  have hβmem : P.start B ∈ P.outsideIn S ∩ P.outsideIn A := by
    rw [harcA, mem_arcSet, hβα]
    omega
  have hβA : P.out (P.start B) ⊆ A :=
    P.mem_outsideIn.mp (Finset.mem_inter.mp hβmem).2
  have hβS : P.out (P.start B) ⊆ S :=
    P.mem_outsideIn.mp (Finset.mem_inter.mp hβmem).1
  have hβB : P.out (P.start B) ⊆ B := (P.outside_eq_arc B hB _).mpr (by
    rw [mem_arcSet, sub_self]
    have := P.two_le_len B hB
    simp only [Fin.val_zero]
    omega)
  have hβs : P.start B ≠ s := by
    intro h
    rw [h, sub_self] at hlt
    simp only [Fin.val_zero, Nat.not_lt_zero] at hlt
  have hsB : P.len B ≤ (s - P.start B).val :=
    mem_arcSet_compl.mp (fun hmem =>
      P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 (by linarith) hC
        hSad harcS hB ⟨⟨hcB.1, hmem⟩, hcB⟩)
  have hab := val_sub_add_val_sub hβs
  have hαB : P.out (P.start A) ∩ B = ∅ := by
    have hαβne : P.start A ≠ P.start B := by
      intro h
      rw [h] at hlt
      omega
    have hab2 := val_sub_add_val_sub hαβne
    have hαnot : P.start A ∉ arcSet (P.start B) (P.len B) := by
      rw [mem_arcSet_compl]
      omega
    rcases atom_subset_or_disjoint (P.out_atom (P.start A)) hB with h | h
    · exact absurd ((P.outside_eq_arc B hB _).mp h) hαnot
    · exact Finset.disjoint_iff_inter_eq_empty.mp h
  have hαA : P.out (P.start A) ⊆ A := (P.outside_eq_arc A hA _).mpr (by
    rw [mem_arcSet, sub_self]
    have := P.two_le_len A hA
    simp only [Fin.val_zero]
    omega)
  have hαS : P.out (P.start A) ⊆ S :=
    (P.out_subset_iff_mem_arc harcS _).mpr (mem_arcSet.mpr hdα)
  have hcross : Crossing (A ∩ S) B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty (P.start B)
      exact ⟨v, Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨hβA hv, hβS hv⟩, hβB hv⟩⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty (P.start A)
      refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hαA hv, hαS hv⟩, ?_⟩⟩
      intro hvB
      have hmem : v ∈ P.out (P.start A) ∩ B := Finset.mem_inter.mpr ⟨hv, hvB⟩
      rw [hαB] at hmem
      exact absurd hmem (Finset.notMem_empty v)
    · obtain ⟨j, hj⟩ := (cross_arc_of_almostDiagonal hx hη0 (by linarith) hC P
        (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hB) hSad
        (P.isArcOf_of_mem hB) harcS hcB.1).2.1
      rw [Finset.mem_sdiff] at hj
      have hjB : P.out j ⊆ B := (P.outside_eq_arc B hB j).mpr hj.1
      have hjS : Disjoint (P.out j) S := by
        rcases hSad.unionOfAtoms (P.out j) (P.out_atom j) with h | h
        · exact absurd ((P.out_subset_iff_mem_arc harcS j).mp h) hj.2
        · exact h
      obtain ⟨v, hv⟩ := P.out_nonempty j
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hjB hv, fun hmem =>
        Finset.disjoint_left.mp hjS hv (Finset.mem_inter.mp hmem).2⟩⟩
    · intro hcov
      refine hcB.1.2.2.2 ?_
      rw [Finset.union_comm B S]
      refine Finset.eq_univ_of_forall fun v => ?_
      have hv : v ∈ (A ∩ S) ∪ B := by rw [hcov]; exact Finset.mem_univ v
      rcases Finset.mem_union.mp hv with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).2
      · exact Finset.mem_union_right _ h
  have hAS : IsNearMinCut x (η + 2 * η) (A ∩ S) :=
    nearMinCut_inter hx (hC.nearMin A hA) hSad.nearMin hcA.1
  have hASB : IsNearMinCut x (η + 2 * η + η) ((A ∩ S) ∩ B) :=
    nearMinCut_inter hx hAS (hC.nearMin B hB) hcross
  have hSB : IsNearMinCut x (η + 2 * η + η) (S ∩ B) :=
    (nearMinCut_inter hx hSad.nearMin (hC.nearMin B hB) hcB.1.symm).mono
      (by linarith)
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := hSad.unionOfAtoms
  have hatB : ∀ a ∈ atoms 𝒞, a ⊆ B ∨ Disjoint a B := fun a ha =>
    atom_subset_or_disjoint ha hB
  have hatASB : ∀ a ∈ atoms 𝒞, a ⊆ (A ∩ S) ∩ B ∨ Disjoint a ((A ∩ S) ∩ B) :=
    unionOfAtoms_inter
      (unionOfAtoms_inter (fun a ha => atom_subset_or_disjoint ha hA) hatS) hatB
  have hne : (P.outsideIn ((A ∩ S) ∩ B)).Nonempty := by
    rw [hout, P.outsideIn_inter, harcB]
    refine ⟨P.start B, mem_arcSet.mpr ?_⟩
    rw [sub_self]
    simp only [Fin.val_zero]
    omega
  obtain ⟨r, hr, hrS⟩ := P.exists_atom_disjoint_of_isArcOf hSad harcS
  have hkey : (A ∩ S) ∩ B = S ∩ B :=
    eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P hASB hSB hatASB
      (unionOfAtoms_inter hatS hatB) hout hne
      ⟨r, hr, hrS.mono_right (Finset.inter_subset_left.trans
        Finset.inter_subset_right),
        hrS.mono_right Finset.inter_subset_left⟩
  intro v hv
  rw [Finset.mem_inter] at hv
  have hvSB : v ∈ S ∩ B := Finset.mem_inter.mpr ⟨hv.2, hv.1⟩
  rw [← hkey, Finset.mem_inter, Finset.mem_inter] at hvSB
  exact Finset.mem_inter.mpr ⟨hvSB.1.1, hvSB.1.2⟩

/-- **KKO22 Lemma 4.29 for almost diagonal cuts — equal starts.**  Cuts
crossing the almost diagonal `S` on the right from the same polygon point
meet `S` identically.  (`inter_eq_of_crossesOnRight_of_start_eq` with `S`'s
arc supplied as data.) -/
theorem inter_eq_of_crossesOnRightArc_of_start_eq (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {s : Fin P.m} {l : ℕ}
    (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    {A B : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hcA : P.CrossesOnRightArc A S s l) (hcB : P.CrossesOnRightArc B S s l)
    (hstart : P.start A = P.start B) : S ∩ A = S ∩ B := by
  classical
  have hm := P.hm
  have hdA : (P.start A - s).val < l := mem_arcSet.mp hcA.2
  have houtA := P.outsideIn_inter_rightArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hA hcA
  have houtB := P.outsideIn_inter_rightArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hB hcB
  have hout : P.outsideIn (S ∩ A) = P.outsideIn (S ∩ B) := by
    rw [P.outsideIn_inter, P.outsideIn_inter, houtA, houtB, hstart]
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := hSad.unionOfAtoms
  obtain ⟨r, hr, hrS⟩ := P.exists_atom_disjoint_of_isArcOf hSad harcS
  refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
    (nearMinCut_inter hx hSad.nearMin (hC.nearMin A hA) hcA.1.symm)
    (nearMinCut_inter hx hSad.nearMin (hC.nearMin B hB) hcB.1.symm)
    (unionOfAtoms_inter hatS (fun a ha => atom_subset_or_disjoint ha hA))
    (unionOfAtoms_inter hatS (fun a ha => atom_subset_or_disjoint ha hB))
    hout ?_
    ⟨r, hr, hrS.mono_right Finset.inter_subset_left,
      hrS.mono_right Finset.inter_subset_left⟩
  rw [P.outsideIn_inter, houtA]
  refine ⟨P.start A, mem_arcSet.mpr ?_⟩
  rw [sub_self]
  simp only [Fin.val_zero]
  omega

/-- **KKO22 Lemma 4.29, left form — equal overlaps.**  Cuts crossing `S`
on the left with the *same* shared outside-atom count meet `S` in the same
set.  (The left analogue of `inter_eq_of_crossesOnRight_of_start_eq`.) -/
theorem inter_eq_of_crossesOnLeftArc_of_len_eq (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {s : Fin P.m} {l : ℕ}
    (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    {A B : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hcA : P.CrossesOnLeftArc A S s) (hcB : P.CrossesOnLeftArc B S s)
    (heq : P.len A - (s - P.start A).val = P.len B - (s - P.start B).val) :
    S ∩ A = S ∩ B := by
  classical
  have hm := P.hm
  have hl1 := harcS.2.1
  have hdA : (s - P.start A).val < P.len A := mem_arcSet.mp hcA.2
  have harcA := P.outsideIn_inter_leftArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hA hcA
  have harcB := P.outsideIn_inter_leftArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hB hcB
  have hout : P.outsideIn (S ∩ A) = P.outsideIn (S ∩ B) := by
    rw [P.outsideIn_inter, P.outsideIn_inter, harcA, harcB, heq]
  have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := hSad.unionOfAtoms
  obtain ⟨r, hr, hrS⟩ := P.exists_atom_disjoint_of_isArcOf hSad harcS
  refine eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P
    (nearMinCut_inter hx hSad.nearMin (hC.nearMin A hA) hcA.1.symm)
    (nearMinCut_inter hx hSad.nearMin (hC.nearMin B hB) hcB.1.symm)
    (unionOfAtoms_inter hatS (fun a ha => atom_subset_or_disjoint ha hA))
    (unionOfAtoms_inter hatS (fun a ha => atom_subset_or_disjoint ha hB))
    hout ?_
    ⟨r, hr, hrS.mono_right Finset.inter_subset_left,
      hrS.mono_right Finset.inter_subset_left⟩
  rw [P.outsideIn_inter, harcA]
  refine ⟨s, mem_arcSet.mpr ?_⟩
  rw [sub_self]
  simp only [Fin.val_zero]
  omega

/-- **KKO22 Lemma 4.29, left form.**  Among cuts crossing `S` on the left,
meeting `S` is *monotone* in the shared outside-atom count — the opposite
direction from the right-hand form, because these arcs share their left
endpoint `s` and nest by length.

This is the form Lemma 5.4 invokes, and it is why `L*` is defined by
*maximizing* the overlap where `S_R` minimizes it: the maximizer is the
top of this chain. -/
theorem inter_subset_inter_of_crossesOnLeftArc (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) {s : Fin P.m} {l : ℕ}
    (hSad : P.IsAlmostDiagonal x η S) (harcS : P.IsArcOf S s l)
    {A B : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞)
    (hcA : P.CrossesOnLeftArc A S s) (hcB : P.CrossesOnLeftArc B S s)
    (hle : P.len A - (s - P.start A).val ≤ P.len B - (s - P.start B).val) :
    A ∩ S ⊆ B ∩ S := by
  classical
  have hm := P.hm
  have hl1 := harcS.2.1
  have hlS := harcS.2.2
  have hmA := P.len_le A hA
  have hmB := P.len_le B hB
  have hdA : (s - P.start A).val < P.len A := mem_arcSet.mp hcA.2
  have hdB : (s - P.start B).val < P.len B := mem_arcSet.mp hcB.2
  have harcA := P.outsideIn_inter_leftArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hA hcA
  have harcB := P.outsideIn_inter_leftArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hB hcB
  -- overlap lengths are bounded by `l`
  have hboundB : P.len B - (s - P.start B).val ≤ l := by
    have hsb : arcSet s (P.len B - (s - P.start B).val) ⊆ arcSet s l := by
      rw [← harcB, ← harcS.1]
      exact Finset.inter_subset_left
    have hc := Finset.card_le_card hsb
    rwa [arcSet_card _ (by omega), arcSet_card _ (by omega)] at hc
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [Finset.inter_comm A S, Finset.inter_comm B S]
    exact le_of_eq (P.inter_eq_of_crossesOnLeftArc_of_len_eq hx hη0 hη hC hSad
      harcS hA hB hcA hcB heq)
  · -- strict: the atom just past `A`'s overlap witnesses the crossing
    have hsub : P.outsideIn S ∩ P.outsideIn A ⊆ P.outsideIn S ∩ P.outsideIn B := by
      rw [harcA, harcB]
      exact arcSet_mono hle
    have hout : P.outsideIn ((B ∩ S) ∩ A) = P.outsideIn (S ∩ A) := by
      rw [P.outsideIn_inter, P.outsideIn_inter, P.outsideIn_inter]
      ext i
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hiB, hiS⟩, hiA⟩
        exact ⟨hiS, hiA⟩
      · rintro ⟨hiS, hiA⟩
        exact ⟨⟨(Finset.mem_inter.mp
          (hsub (Finset.mem_inter.mpr ⟨hiS, hiA⟩))).2, hiS⟩, hiA⟩
    -- `s` lies in both overlaps
    have hsmemA : s ∈ P.outsideIn S ∩ P.outsideIn A := by
      rw [harcA, mem_arcSet, sub_self]
      simp only [Fin.val_zero]
      omega
    have hsS : P.out s ⊆ S := P.mem_outsideIn.mp (Finset.mem_inter.mp hsmemA).1
    have hsA : P.out s ⊆ A := P.mem_outsideIn.mp (Finset.mem_inter.mp hsmemA).2
    have hsB : P.out s ⊆ B := by
      have hmem : s ∈ P.outsideIn S ∩ P.outsideIn B := hsub hsmemA
      exact P.mem_outsideIn.mp (Finset.mem_inter.mp hmem).2
    -- the witness index just past `A`'s overlap
    obtain ⟨j, hjval⟩ : ∃ j : Fin P.m,
        (j - s).val = P.len A - (s - P.start A).val :=
      ⟨s + ⟨P.len A - (s - P.start A).val, by omega⟩, by rw [add_sub_cancel_left]⟩
    have hjmemB : j ∈ P.outsideIn S ∩ P.outsideIn B := by
      rw [harcB, mem_arcSet, hjval]
      omega
    have hjS : P.out j ⊆ S := P.mem_outsideIn.mp (Finset.mem_inter.mp hjmemB).1
    have hjB : P.out j ⊆ B := P.mem_outsideIn.mp (Finset.mem_inter.mp hjmemB).2
    have hjA : Disjoint (P.out j) A := by
      rcases atom_subset_or_disjoint (P.out_atom j) hA with h | h
      · exfalso
        have : j ∈ P.outsideIn S ∩ P.outsideIn A :=
          Finset.mem_inter.mpr ⟨P.mem_outsideIn.mpr hjS, P.mem_outsideIn.mpr h⟩
        rw [harcA, mem_arcSet, hjval] at this
        omega
      · exact h
    have hcross : Crossing (B ∩ S) A := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨v, hv⟩ := P.out_nonempty s
        exact ⟨v, Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨hsB hv, hsS hv⟩, hsA hv⟩⟩
      · obtain ⟨v, hv⟩ := P.out_nonempty j
        exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hjB hv, hjS hv⟩,
          Finset.disjoint_left.mp hjA hv⟩⟩
      · obtain ⟨k, hk⟩ := (cross_arc_of_almostDiagonal hx hη0 (by linarith) hC P
          (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hA) hSad
          (P.isArcOf_of_mem hA) harcS hcA.1).2.1
        rw [Finset.mem_sdiff] at hk
        have hkA : P.out k ⊆ A := (P.outside_eq_arc A hA k).mpr hk.1
        have hkS : Disjoint (P.out k) S := by
          rcases hSad.unionOfAtoms (P.out k) (P.out_atom k) with h | h
          · exact absurd ((P.out_subset_iff_mem_arc harcS k).mp h) hk.2
          · exact h
        obtain ⟨v, hv⟩ := P.out_nonempty k
        exact ⟨v, Finset.mem_sdiff.mpr ⟨hkA hv, fun hmem =>
          Finset.disjoint_left.mp hkS hv (Finset.mem_inter.mp hmem).2⟩⟩
      · intro hcov
        refine hcA.1.2.2.2 ?_
        refine Finset.eq_univ_of_forall fun v => ?_
        have hv : v ∈ (B ∩ S) ∪ A := by rw [hcov]; exact Finset.mem_univ v
        rcases Finset.mem_union.mp hv with h | h
        · exact Finset.mem_union_right _ (Finset.mem_inter.mp h).2
        · exact Finset.mem_union_left _ h
    have hBS : IsNearMinCut x (η + 2 * η) (B ∩ S) :=
      nearMinCut_inter hx (hC.nearMin B hB) hSad.nearMin hcB.1
    have hBSA : IsNearMinCut x (η + 2 * η + η) ((B ∩ S) ∩ A) :=
      nearMinCut_inter hx hBS (hC.nearMin A hA) hcross
    have hSA : IsNearMinCut x (η + 2 * η + η) (S ∩ A) :=
      (nearMinCut_inter hx hSad.nearMin (hC.nearMin A hA) hcA.1.symm).mono
        (by linarith)
    have hatS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S := hSad.unionOfAtoms
    have hatA : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A := fun a ha =>
      atom_subset_or_disjoint ha hA
    obtain ⟨r, hr, hrS⟩ := P.exists_atom_disjoint_of_isArcOf hSad harcS
    have hne : (P.outsideIn ((B ∩ S) ∩ A)).Nonempty := by
      rw [hout, P.outsideIn_inter, harcA]
      refine ⟨s, mem_arcSet.mpr ?_⟩
      rw [sub_self]
      simp only [Fin.val_zero]
      omega
    have hkey : (B ∩ S) ∩ A = S ∩ A :=
      eq_of_outsideIn_eq hx (by linarith) (by linarith) hC P hBSA hSA
        (unionOfAtoms_inter (unionOfAtoms_inter
          (fun a ha => atom_subset_or_disjoint ha hB) hatS) hatA)
        (unionOfAtoms_inter hatS hatA) hout hne
        ⟨r, hr, hrS.mono_right (Finset.inter_subset_left.trans
          Finset.inter_subset_right),
          hrS.mono_right Finset.inter_subset_left⟩
    intro v hv
    rw [Finset.mem_inter] at hv
    have hvSA : v ∈ S ∩ A := Finset.mem_inter.mpr ⟨hv.2, hv.1⟩
    rw [← hkey, Finset.mem_inter, Finset.mem_inter] at hvSA
    exact Finset.mem_inter.mpr ⟨hvSA.1.1, hvSA.1.2⟩

/-- **KKO22 Lemma 4.28, the left chain's bottom**: `S ∩ S_L` is contained
in `S ∩ A` for every `A` crossing `S` on the left.  Definition 4.17's
minimal overlap is the *shortest* of the left-anchored overlap arcs, and
they nest by length (the left form of Lemma 4.29). -/
theorem inter_isSL_subset (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hS : S ∈ 𝒞) {L A : Finset (Fin n)} (hL : P.IsSL S L) (hA : A ∈ 𝒞)
    (hcA : P.CrossesOnLeft A S) :
    L ∩ S ⊆ A ∩ S := by
  obtain ⟨hLmem, hcL, hmin, -⟩ := hL
  have hm := P.hm
  have hcardL := P.card_outsideIn_inter_left hS hLmem hcL
  have hcardA := P.card_outsideIn_inter_left hS hA hcA
  have hdL : (P.start S - P.start L).val < P.len L := mem_arcSet.mp hcL.2
  have hdA : (P.start S - P.start A).val < P.len A := mem_arcSet.mp hcA.2
  have hle : P.len L - (P.start S - P.start L).val
      ≤ P.len A - (P.start S - P.start A).val := by
    have := hmin A hA hcA
    rw [hcardL, hcardA] at this
    omega
  exact P.inter_subset_inter_of_crossesOnLeftArc hx hη0 hη hC
    (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hS)
    (P.isArcOf_of_mem hS) hLmem hA (P.crossesOnLeftArc_of_mem.mpr hcL)
    (P.crossesOnLeftArc_of_mem.mpr hcA) hle

/-! ### KKO22 Lemma 5.4, step (4): the final contradiction

`L(p)` is a candidate for `L*(q)`, so its overlap with `L(q)^∩R` is at
most the maximal one; by the left form of Lemma 4.29 — where larger
overlap means larger intersection — its intersection is contained in
`L*(q)`'s.  The shared endpoint `a` therefore lies in `L*(q)`, which is
exactly what `e ∈ E(B→(q))` forbids. -/

/-- Any left-crosser meets the almost diagonal cut inside `L*`. -/
theorem inter_subset_isLStar (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {s : Fin P.m} {l : ℕ} (hSad : P.IsAlmostDiagonal x η S)
    (harcS : P.IsArcOf S s l) {Lp W : Finset (Fin n)} (hLp : Lp ∈ 𝒞)
    (hcLp : P.CrossesOnLeftArc Lp S s) (hW : P.IsLStar S s W) :
    Lp ∩ S ⊆ W ∩ S := by
  obtain ⟨hWmem, hcW, hmax⟩ := hW
  have hm := P.hm
  have hmLp := P.len_le Lp hLp
  have hmW := P.len_le W hWmem
  have harcLp := P.outsideIn_inter_leftArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hLp hcLp
  have harcW := P.outsideIn_inter_leftArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hWmem hcW
  have hcard := hmax Lp hLp hcLp
  rw [harcLp, harcW, arcSet_card _ (by omega), arcSet_card _ (by omega)]
    at hcard
  exact P.inter_subset_inter_of_crossesOnLeftArc hx hη0 hη hC hSad harcS hLp
    hWmem hcLp hcW hcard

/-- **KKO22 Lemma 5.4, step (4).**  The shared endpoint `a` of the edge
lies in `L*`, so it cannot lie in `L(q)^∩R ∖ L*(q)` — contradicting
`e ∈ E(B→(q))`. -/
theorem not_mem_sdiff_isLStar (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {s : Fin P.m} {l : ℕ} (hSad : P.IsAlmostDiagonal x η S)
    (harcS : P.IsArcOf S s l) {Lp W : Finset (Fin n)} {a : Fin n}
    (hLp : Lp ∈ 𝒞) (hcLp : P.CrossesOnLeftArc Lp S s) (hW : P.IsLStar S s W)
    (ha : a ∈ Lp) (haS : a ∈ S) : a ∉ S \ W := by
  intro hbad
  have hmem : a ∈ W ∩ S :=
    P.inter_subset_isLStar hx hη0 hη hC hSad harcS hLp hcLp hW
      (Finset.mem_inter.mpr ⟨ha, haS⟩)
  exact (Finset.mem_sdiff.mp hbad).2 (Finset.mem_inter.mp hmem).1

/-- Any right-crosser meets the almost diagonal cut inside `R*` — the
mirror of `inter_subset_isLStar`.  The right-anchored overlap arcs share
`S`'s right end, so maximal overlap means leftmost start; the strict case
is Lemma 4.29's antitone form, and equal counts force equal starts, where
Lemma 4.23 gives equality outright. -/
theorem inter_subset_isRStar (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {s : Fin P.m} {l : ℕ} (hSad : P.IsAlmostDiagonal x η S)
    (harcS : P.IsArcOf S s l) {Rp W : Finset (Fin n)} (hRp : Rp ∈ 𝒞)
    (hcRp : P.CrossesOnRightArc Rp S s l) (hW : P.IsRStar S s l W) :
    Rp ∩ S ⊆ W ∩ S := by
  obtain ⟨hWmem, hcW, hmax⟩ := hW
  have hm := P.hm
  have hl2 := harcS.2.2
  have hdRp : (P.start Rp - s).val < l := mem_arcSet.mp hcRp.2
  have hdW : (P.start W - s).val < l := mem_arcSet.mp hcW.2
  have harcRp := P.outsideIn_inter_rightArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hRp hcRp
  have harcW := P.outsideIn_inter_rightArc_eq_arc hx hη0 (by linarith) hC hSad
    harcS hWmem hcW
  have hcard := hmax Rp hRp hcRp
  rw [harcRp, harcW, arcSet_card _ (by omega), arcSet_card _ (by omega)]
    at hcard
  rcases lt_or_eq_of_le (show (P.start W - s).val ≤ (P.start Rp - s).val
    by omega) with hlt | heq
  · exact P.inter_subset_inter_of_crossesOnRightArc hx hη0 hη hC hSad harcS
      hWmem hRp hcW hcRp hlt
  · have hstart : P.start Rp = P.start W :=
      sub_left_inj.mp (Fin.val_injective heq.symm)
    rw [Finset.inter_comm Rp S, Finset.inter_comm W S]
    exact le_of_eq (P.inter_eq_of_crossesOnRightArc_of_start_eq hx hη0 hη hC
      hSad harcS hRp hWmem hcRp hcW hstart)

/-- The mirror of `not_mem_sdiff_isLStar`: the shared endpoint lies in
`R*`, so it cannot lie in `R(q)^∩L ∖ R*(q)`. -/
theorem not_mem_sdiff_isRStar (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {s : Fin P.m} {l : ℕ} (hSad : P.IsAlmostDiagonal x η S)
    (harcS : P.IsArcOf S s l) {Rp W : Finset (Fin n)} {a : Fin n}
    (hRp : Rp ∈ 𝒞) (hcRp : P.CrossesOnRightArc Rp S s l)
    (hW : P.IsRStar S s l W) (ha : a ∈ Rp) (haS : a ∈ S) : a ∉ S \ W := by
  intro hbad
  have hmem : a ∈ W ∩ S :=
    P.inter_subset_isRStar hx hη0 hη hC hSad harcS hRp hcRp hW
      (Finset.mem_inter.mpr ⟨ha, haS⟩)
  exact (Finset.mem_sdiff.mp hbad).2 (Finset.mem_inter.mp hmem).1

/-- **KKO22 Lemma 5.4, the Definition 4.17 comparison.**  Of two cuts
crossing `S` on the right, the one whose start lies *outside* the other's
arc shares strictly fewer outside atoms with `S`.

This is the paper's "to prove the inequality it's enough to show that the
leftmost outside atom of `L(q)_R` is not in `L(p)_R`": not containing the
other's start forces starting strictly further right, and the closed form
`|O(S ∩ ·)| = len S − offset` turns that into the strict inequality. -/
theorem card_inter_lt_of_start_notMem (P : PolygonRep 𝒞) (hS : S ∈ 𝒞)
    {W W' : Finset (Fin n)} (hW : W ∈ 𝒞) (hW' : W' ∈ 𝒞)
    (hcW : P.CrossesOnRight W S) (hcW' : P.CrossesOnRight W' S)
    (hnot : P.start W' ∉ arcSet (P.start W) (P.len W)) :
    (P.outsideIn S ∩ P.outsideIn W).card
      < (P.outsideIn S ∩ P.outsideIn W').card := by
  have hm := P.hm
  have hmS := P.len_le S hS
  have hd : (P.start W - P.start S).val < P.len S := mem_arcSet.mp hcW.2
  have hd' : (P.start W' - P.start S).val < P.len S := mem_arcSet.mp hcW'.2
  -- `W` reaches past `S`'s right point, so its arc covers `S`'s tail
  have hrp := mem_arcSet.mp (P.rightPoint_mem_arc_of_crossesOnRight hS hW hcW)
  have hrpv := P.val_rightPoint_sub_start hS
  have hlen : P.len S - (P.start W - P.start S).val < P.len W := by
    have hv := val_sub_of_le (s := P.start S) (α := P.start W)
      (β := P.rightPoint S) (by omega)
    omega
  -- so `W'` must start strictly to the right of `W`
  have hlt : (P.start W' - P.start S).val < (P.start W - P.start S).val := by
    by_contra hcon
    push Not at hcon
    refine hnot (mem_arcSet.mpr ?_)
    have hv := val_sub_of_le (s := P.start S) (α := P.start W)
      (β := P.start W') hcon
    omega
  rw [P.card_outsideIn_inter_right hS hW hcW,
    P.card_outsideIn_inter_right hS hW' hcW']
  omega

/-- A set crossing `C` is not contained in any subset of `C`: the
crossing supplies a point of `A` outside `C`, hence outside `B ⊆ C`.

This is KKO's step "`L(q) ⊆ L(p)_R` implies `L(p) ⊄ L(q)`", with
`A = L(p)`, `C = L(p)_R`, `B = L(q)`. -/
theorem not_subset_of_crossing_of_subset {A B C : Finset (Fin n)}
    (hc : Crossing A C) (hsub : B ⊆ C) : ¬ (A ⊆ B) := by
  intro h
  obtain ⟨v, hv⟩ := hc.2.1
  rw [Finset.mem_sdiff] at hv
  exact hv.2 (hsub (h hv.1))

/-- **KKO22 Claim 5.9, first half**: `L(q)` crosses `L(p)` on the right.

The four crossing conditions come from four different places, which is
why the claim takes a paragraph in the paper: the intersection from the
shared edge endpoint `a`; `L(q) ∖ L(p)` from `q` being the rightmost
point (`hright`); `L(p) ∖ L(q)` from the contradiction hypothesis
`L(q) ⊆ L(p)_R` via `not_subset_of_crossing_of_subset`; and the proper
union from the root.  The *side* is then read off the arc, which is
where the `LeFrom` ordering enters. -/
theorem crossesOnRight_of_rightmost (P : PolygonRep 𝒞)
    {Lp Lq LpR : Finset (Fin n)} (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hcross : Crossing Lp LpR) (hsub : Lq ⊆ LpR)
    (hinter : (Lq ∩ Lp).Nonempty) (hright : (Lq \ Lp).Nonempty)
    (hside : P.start Lq ∈ arcSet (P.start Lp) (P.len Lp)) :
    P.CrossesOnRight Lq Lp := by
  refine ⟨⟨hinter, hright, ?_, P.union_ne_univ hLq hLp⟩, hside⟩
  obtain ⟨v, hv, hv'⟩ :=
    Finset.not_subset.mp (not_subset_of_crossing_of_subset hcross hsub)
  exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩

/-- **KKO22 Claim 5.9, second half**: a cut crossing `S` and sharing a
vertex with `S_R` outside `S` crosses `S` on the **right**.

This is the claim's closing paragraph.  If the crossing were on the left,
Lemma 4.27 would make `W ∖ S` and `S_R ∖ S` disjoint — but the witness
lies in both.  (In Claim 5.9, `W = L(p)_R`, `S = L(q)`, and the witness
is the edge endpoint `b`.) -/
theorem crossesOnRight_of_witness (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 5) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hS : S ∈ 𝒞) {W SR : Finset (Fin n)} (hW : W ∈ 𝒞) (hSR : SR ∈ 𝒞)
    (hcross : Crossing W S) (hcR : P.CrossesOnRight SR S)
    {b : Fin n} (hbW : b ∈ W \ S) (hbR : b ∈ SR \ S) :
    P.CrossesOnRight W S := by
  rcases P.crossesOnLeft_or_crossesOnRight hW hS hcross with hleft | hright
  · exact absurd hbR (Finset.disjoint_left.mp
      (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 hη hC hS hW
        hSR hleft hcR) hbW)
  · exact hright

/-- The mirror of `crossesOnRight_of_rightmost`: a cut sharing a vertex
with `R(p)`, not contained in it, whose arc contains `R(p)`'s start,
crosses it on the **left**. -/
theorem crossesOnLeft_of_leftmost (P : PolygonRep 𝒞)
    {Rp Rq RpL : Finset (Fin n)} (hRp : Rp ∈ 𝒞) (hRq : Rq ∈ 𝒞)
    (hcross : Crossing Rp RpL) (hsub : Rq ⊆ RpL)
    (hinter : (Rq ∩ Rp).Nonempty) (hleft : (Rq \ Rp).Nonempty)
    (hside : P.start Rp ∈ arcSet (P.start Rq) (P.len Rq)) :
    P.CrossesOnLeft Rq Rp := by
  refine ⟨⟨hinter, hleft, ?_, P.union_ne_univ hRq hRp⟩, hside⟩
  obtain ⟨v, hv, hv'⟩ :=
    Finset.not_subset.mp (not_subset_of_crossing_of_subset hcross hsub)
  exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩

/-- The mirror of `crossesOnRight_of_witness`: a cut crossing `S` and
sharing a vertex with `S_L` outside `S` crosses `S` on the **left** —
crossing on the right would make `W ∖ S` and `S_L ∖ S` disjoint by
Lemma 4.27, against the witness. -/
theorem crossesOnLeft_of_witness (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 5) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hS : S ∈ 𝒞) {W SL : Finset (Fin n)} (hW : W ∈ 𝒞) (hSL : SL ∈ 𝒞)
    (hcross : Crossing W S) (hcL : P.CrossesOnLeft SL S)
    {b : Fin n} (hbW : b ∈ W \ S) (hbL : b ∈ SL \ S) :
    P.CrossesOnLeft W S := by
  rcases P.crossesOnLeft_or_crossesOnRight hW hS hcross with hleft | hright
  · exact hleft
  · exact absurd hbW (Finset.disjoint_left.mp
      (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 hη hC hS hSL
        hW hcL hright) hbL)

/-- **KKO22 Claim 5.9, the minimality step**: a cut crossing `S` on the
right and *contained* in `S_R` equals `S_R`.

Definition 4.17 picks `S_R` minimizing the shared outside-atom count and
breaks ties by smallest length.  Containment makes the count of the
candidate no larger, so minimality forces equality of counts, and then
the tie-break forces equality of the cuts. -/
theorem eq_of_isSR_of_subset (P : PolygonRep 𝒞) (hS : S ∈ 𝒞)
    {SR W : Finset (Fin n)} (hSR : P.IsSR S SR) (hW : W ∈ 𝒞)
    (hcW : P.CrossesOnRight W S) (hsub : W ⊆ SR) :
    W = SR := by
  obtain ⟨hSRmem, hcSR, hmin, htie⟩ := hSR
  have hsubOut : P.outsideIn W ⊆ P.outsideIn SR := fun i hi =>
    P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans hsub)
  have hcard : (P.outsideIn S ∩ P.outsideIn W).card
      = (P.outsideIn S ∩ P.outsideIn SR).card :=
    le_antisymm
      (Finset.card_le_card (Finset.inter_subset_inter_left hsubOut))
      (hmin W hW hcW)
  -- equal counts pin the start, containment and the tie-break the length
  have e1 := P.card_outsideIn_inter_right hS hW hcW
  have e2 := P.card_outsideIn_inter_right hS hSRmem hcSR
  have hd1 := mem_arcSet.mp hcW.2
  have hd2 := mem_arcSet.mp hcSR.2
  have hstart : P.start W = P.start SR := by
    have hv : (P.start W - P.start S).val = (P.start SR - P.start S).val := by
      omega
    exact sub_left_inj.mp (Fin.val_injective hv)
  have hlen1 : P.len W ≤ P.len SR := by
    have c1 := P.card_outsideIn hW
    have c2 := P.card_outsideIn hSRmem
    rw [← c1, ← c2]
    exact Finset.card_le_card hsubOut
  exact P.arc_injective W hW SR hSRmem hstart
    (le_antisymm hlen1 (htie W hW hcW hcard))

/-- The mirror of `eq_of_isSR_of_subset`: a cut crossing `S` on the left
and *contained* in `S_L` equals `S_L`.  Containment bounds the overlap
count one way and Definition 4.17's minimality the other; equal counts and
the tie-break then pin the arc via the converse arc lemma. -/
theorem eq_of_isSL_of_subset (P : PolygonRep 𝒞)
    {SL W : Finset (Fin n)} (hSL : P.IsSL S SL) (hW : W ∈ 𝒞)
    (hcW : P.CrossesOnLeft W S) (hsub : W ⊆ SL) :
    W = SL := by
  obtain ⟨hSLmem, hcSL, hmin, htie⟩ := hSL
  have hm := P.hm
  have h2W := P.two_le_len W hW
  have hmSL := P.len_le SL hSLmem
  have hsubOut : P.outsideIn W ⊆ P.outsideIn SL := fun i hi =>
    P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans hsub)
  have hcard : (P.outsideIn S ∩ P.outsideIn W).card
      = (P.outsideIn S ∩ P.outsideIn SL).card :=
    le_antisymm
      (Finset.card_le_card (Finset.inter_subset_inter_left hsubOut))
      (hmin W hW hcW)
  -- the tie-break bounds the length one way, containment the other —
  -- and containment also pins the start, via the converse arc lemma
  have hlen2 := htie W hW hcW hcard
  have harcsub : arcSet (P.start W) (P.len W)
      ⊆ arcSet (P.start SL) (P.len SL) := by
    rw [← P.outsideIn_eq_arc hW, ← P.outsideIn_eq_arc hSLmem]
    exact hsubOut
  have hconv := le_of_arcSet_subset harcsub (by omega) (by omega)
  have h0 : (P.start W - P.start SL).val = 0 := by omega
  have hstart : P.start W = P.start SL :=
    sub_eq_zero.mp (Fin.val_injective (by simpa using h0))
  exact P.arc_injective W hW SL hSLmem hstart (by omega)

/-- **KKO22 Claim 5.9**, assembled: `L(p)_R` crosses `L(q)` on the right.

The two hypotheses `hover` and `hpast` are the encoded content of KKO's
"WLOG `q` is the rightmost point in the interval `O(L(p) ∪ L(q))`".  The
paper's justification for that interval existing is Fact 4.8, but Fact 4.8
only says the two arcs do not *cover* the polygon — it does not say they
*overlap*, and without overlap the union is not an interval at all (`a` could
lie in an inside atom common to both cuts).  So the overlap is carried
explicitly as `hover`, and `q` being strictly rightmost as `hpast`.

The proof is the paper's.  `L(p)_R` meets `L(q)` at `a` and leaves it at `b`,
so it crosses `L(q)` unless `L(q) ⊆ L(p)_R`; and in that case `L(q)` is
itself a candidate for `L(p)_R` — it crosses `L(p)` on the right, the
rightmost-atom fact supplying `L(q) ⊄ L(p)` — so Definition 4.17's minimality
forces `L(q) = L(p)_R`, which `b` contradicts.  The *side* is then Lemma 4.27
through `crossesOnRight_of_witness`, with `b` as the witness. -/
theorem crossesOnRight_isSR_of_rightmost (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Lp Lq LpR LqR : Finset (Fin n)} (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hLpR : P.IsSR Lp LpR) (hLqR : P.IsSR Lq LqR)
    (hover : (P.start Lq - P.start Lp).val < P.len Lp)
    (hpast : P.len Lp < (P.start Lq - P.start Lp).val + P.len Lq)
    {a b : Fin n} (haLp : a ∈ Lp) (haLq : a ∈ Lq) (haLpR : a ∈ LpR)
    (hbLpR : b ∈ LpR) (hbLq : b ∉ Lq) (hbLqR : b ∈ LqR) :
    P.CrossesOnRight LpR Lq := by
  -- the rightmost outside atom of `L(q)` lies outside `L(p)`
  obtain ⟨i, -, hiLq, hiLp⟩ := P.exists_last_atom_notMem hLp hLq hover hpast
  obtain ⟨w, hw⟩ := P.out_nonempty i
  have hwq : w ∈ Lq := hiLq hw
  have hwp : w ∉ Lp := by
    rcases atom_subset_or_disjoint (P.out_atom i) hLp with h | h
    · exact absurd h hiLp
    · exact Finset.disjoint_left.mp h hw
  have hrightmost : (Lq \ Lp).Nonempty := ⟨w, Finset.mem_sdiff.mpr ⟨hwq, hwp⟩⟩
  have hside : P.start Lq ∈ arcSet (P.start Lp) (P.len Lp) :=
    mem_arcSet.mpr hover
  -- `L(p)_R` crosses `L(q)`
  have hcross : Crossing LpR Lq := by
    refine ⟨⟨a, Finset.mem_inter.mpr ⟨haLpR, haLq⟩⟩,
      ⟨b, Finset.mem_sdiff.mpr ⟨hbLpR, hbLq⟩⟩, ?_, P.union_ne_univ hLpR.1 hLq⟩
    -- `L(q) ⊄ L(p)_R`, else Definition 4.17 forces `L(q) = L(p)_R`
    rcases Finset.eq_empty_or_nonempty (Lq \ LpR) with hemp | hne
    · exfalso
      have hsub : Lq ⊆ LpR := Finset.sdiff_eq_empty_iff_subset.mp hemp
      have hcq : P.CrossesOnRight Lq Lp :=
        P.crossesOnRight_of_rightmost hLp hLq hLpR.2.1.1.symm hsub
          ⟨a, Finset.mem_inter.mpr ⟨haLq, haLp⟩⟩ hrightmost hside
      have := P.eq_of_isSR_of_subset hLp hLpR hLq hcq hsub
      exact hbLq (this ▸ hbLpR)
    · exact hne
  -- the side, from Lemma 4.27 with `b` as witness
  exact P.crossesOnRight_of_witness hx hη0 hη hC hLq hLpR.1 hLqR.1 hcross
    hLqR.2.1 (Finset.mem_sdiff.mpr ⟨hbLpR, hbLq⟩)
    (Finset.mem_sdiff.mpr ⟨hbLqR, hbLq⟩)

/-- **Claim 5.9's mirror, assembled**: `R(p)_L` crosses `R(q)` on the left.

On this side no rightmost-atom fact is needed and no nested branch arises:
the polygon points *are* the arcs' left ends, so `p ≠ q` plus the
orientation `start R(p) ∈ O(R(q))` put `R(q)`'s first atom outside `R(p)`
(`out_start_notMem`) in the proper-overlap and nested configurations
alike. -/
theorem crossesOnLeft_isSL_of_leftmost (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Rp Rq RpL RqL : Finset (Fin n)} (hRp : Rp ∈ 𝒞) (hRq : Rq ∈ 𝒞)
    (hRpL : P.IsSL Rp RpL) (hRqL : P.IsSL Rq RqL)
    (hne : P.start Rp ≠ P.start Rq)
    (hover : (P.start Rp - P.start Rq).val < P.len Rq)
    {a b : Fin n} (haRp : a ∈ Rp) (haRq : a ∈ Rq) (haRpL : a ∈ RpL)
    (hbRpL : b ∈ RpL) (hbRq : b ∉ Rq) (hbRqL : b ∈ RqL) :
    P.CrossesOnLeft RpL Rq := by
  -- the first outside atom of `R(q)` lies outside `R(p)`
  obtain ⟨hiRq, hiRp⟩ := P.out_start_notMem hRp hRq hne hover
  obtain ⟨w, hw⟩ := P.out_nonempty (P.start Rq)
  have hwq : w ∈ Rq := hiRq hw
  have hwp : w ∉ Rp := by
    rcases atom_subset_or_disjoint (P.out_atom (P.start Rq)) hRp with h | h
    · exact absurd h hiRp
    · exact Finset.disjoint_left.mp h hw
  have hleftmost : (Rq \ Rp).Nonempty := ⟨w, Finset.mem_sdiff.mpr ⟨hwq, hwp⟩⟩
  have hside : P.start Rp ∈ arcSet (P.start Rq) (P.len Rq) :=
    mem_arcSet.mpr hover
  -- `R(p)_L` crosses `R(q)`
  have hcross : Crossing RpL Rq := by
    refine ⟨⟨a, Finset.mem_inter.mpr ⟨haRpL, haRq⟩⟩,
      ⟨b, Finset.mem_sdiff.mpr ⟨hbRpL, hbRq⟩⟩, ?_, P.union_ne_univ hRpL.1 hRq⟩
    -- `R(q) ⊄ R(p)_L`, else Definition 4.17 forces `R(q) = R(p)_L`
    rcases Finset.eq_empty_or_nonempty (Rq \ RpL) with hemp | hne'
    · exfalso
      have hsub : Rq ⊆ RpL := Finset.sdiff_eq_empty_iff_subset.mp hemp
      have hcq : P.CrossesOnLeft Rq Rp :=
        P.crossesOnLeft_of_leftmost hRp hRq hRpL.2.1.1.symm hsub
          ⟨a, Finset.mem_inter.mpr ⟨haRq, haRp⟩⟩ hleftmost hside
      have := P.eq_of_isSL_of_subset hRpL hRq hcq hsub
      exact hbRq (this ▸ hbRpL)
    · exact hne'
  -- the side, from Lemma 4.27 with `b` as witness
  exact P.crossesOnLeft_of_witness hx hη0 hη hC hRq hRpL.1 hRqL.1 hcross
    hRqL.2.1 (Finset.mem_sdiff.mpr ⟨hbRpL, hbRq⟩)
    (Finset.mem_sdiff.mpr ⟨hbRqL, hbRq⟩)

/-- **KKO22 Lemma 5.4, the Definition 4.17 step**: `L(p)` does not sit inside
`L(q)^∩R`.

KKO argue by comparing overlap counts — "it's enough to show that the
leftmost outside atom of `L(q)_R` is not in `L(p)_R`".  The Chain Lemma gives
it in one move instead, with no offset arithmetic: `L(q)_R ∩ L(q)` is the
*bottom* of the chain of right-crossers of `L(q)`, and by Claim 5.9 `L(p)_R`
is one of them, so

  `L(p) ⊆ L(q) ∩ L(q)_R ⊆ L(q) ∩ L(p)_R ⊆ L(p)_R`,

and `L(p) ⊆ L(p)_R` contradicts `L(p)_R` crossing `L(p)`. -/
theorem not_subset_inter_isSR (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Lp Lq LpR LqR : Finset (Fin n)} (hLq : Lq ∈ 𝒞)
    (hLpR : P.IsSR Lp LpR) (hLqR : P.IsSR Lq LqR)
    (hclaim59 : P.CrossesOnRight LpR Lq) : ¬ (Lp ⊆ Lq ∩ LqR) := by
  intro hsub
  have hchain : LqR ∩ Lq ⊆ LpR ∩ Lq :=
    P.inter_isSR_subset hx hη0 hη hC hLq hLqR hLpR.1 hclaim59
  have hLpLpR : Lp ⊆ LpR := by
    intro v hv
    have hvq : v ∈ Lq ∩ LqR := hsub hv
    rw [Finset.mem_inter] at hvq
    exact (Finset.mem_inter.mp
      (hchain (Finset.mem_inter.mpr ⟨hvq.2, hvq.1⟩))).1
  obtain ⟨v, hv⟩ := hLpR.2.1.1.2.2.1
  rw [Finset.mem_sdiff] at hv
  exact hv.2 (hLpLpR hv.1)

/-- The mirror of `not_subset_inter_isSR`: `R(p)` does not sit inside
`R(q)^∩L`, by the left chain — `R(q)_L ∩ R(q)` is the bottom of the chain
of left-crossers of `R(q)`, and `R(p)_L` is one of them. -/
theorem not_subset_inter_isSL (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Rp Rq RpL RqL : Finset (Fin n)} (hRq : Rq ∈ 𝒞)
    (hRpL : P.IsSL Rp RpL) (hRqL : P.IsSL Rq RqL)
    (hclaim : P.CrossesOnLeft RpL Rq) : ¬ (Rp ⊆ Rq ∩ RqL) := by
  intro hsub
  have hchain : RqL ∩ Rq ⊆ RpL ∩ Rq :=
    P.inter_isSL_subset hx hη0 hη hC hRq hRqL hRpL.1 hclaim
  have hRpRpL : Rp ⊆ RpL := by
    intro v hv
    have hvq : v ∈ Rq ∩ RqL := hsub hv
    rw [Finset.mem_inter] at hvq
    exact (Finset.mem_inter.mp
      (hchain (Finset.mem_inter.mpr ⟨hvq.2, hvq.1⟩))).1
  obtain ⟨v, hv⟩ := hRpL.2.1.1.2.2.1
  rw [Finset.mem_sdiff] at hv
  exact hv.2 (hRpRpL hv.1)

/-! ### The side of the crossing, via the pair `(L(p), L(q)_R)`

`hside` — `start L(q)_R ∈ O(L(p))` — is precisely "`L(p)` crosses `L(q)_R` on
the left".  Both cuts are members of `𝒞`, so the ordinary crossing dichotomy
applies, and the right side is excluded by geometry: in the nested
configuration, `start L(p) ∈ O(L(q)_R)` would swallow `L(p)`'s arc whole
(`arc_subset_of_nested_of_mem`), contradicting the crossing.  These two
lemmas are that route, used by `lemma54_right_of_nested_geometry`. -/

/-- The charged edge makes `L(p)` and `L(q)_R` cross, once `L(p)` is known not
to sit inside `L(q)_R`: `a` is in both, and `b` is in `L(q)_R` but not `L(p)`. -/
theorem crossing_of_charged (P : PolygonRep 𝒞) {Lp LqR : Finset (Fin n)}
    (hLp : Lp ∈ 𝒞) (hLqR : LqR ∈ 𝒞) {a b : Fin n}
    (haLp : a ∈ Lp) (haLqR : a ∈ LqR) (hbLqR : b ∈ LqR) (hbLp : b ∉ Lp)
    (hnotsub : ¬ (Lp ⊆ LqR)) : Crossing Lp LqR := by
  refine ⟨⟨a, Finset.mem_inter.mpr ⟨haLp, haLqR⟩⟩, ?_,
    ⟨b, Finset.mem_sdiff.mpr ⟨hbLqR, hbLp⟩⟩, P.union_ne_univ hLp hLqR⟩
  rcases Finset.eq_empty_or_nonempty (Lp \ LqR) with hemp | hne
  · exact absurd (Finset.sdiff_eq_empty_iff_subset.mp hemp) hnotsub
  · exact hne

/-- **`hside` is the left side of the dichotomy for `(L(p), L(q)_R)`.**

So `hside` follows from: `L(p)` crosses `L(q)_R`, and `L(p)` does not cross
it *on the right* — `start L(p) ∈ O(L(q)_R)` would say `L(q)_R` wraps far
enough right to swallow `L(p)`'s left end. -/
theorem hside_of_not_crossesOnRight (P : PolygonRep 𝒞)
    {Lp LqR : Finset (Fin n)} (hLp : Lp ∈ 𝒞) (hLqR : LqR ∈ 𝒞)
    (hcross : Crossing Lp LqR)
    (hnot : P.start Lp ∉ arcSet (P.start LqR) (P.len LqR)) :
    P.start LqR ∈ arcSet (P.start Lp) (P.len Lp) := by
  rcases P.crossesOnLeft_or_crossesOnRight hLp hLqR hcross with h | h
  · exact h.2
  · exact absurd h.2 hnot

/-- **§5.3's argument, in the proper-overlap orientation.**

Deliberately *not* named "Lemma 5.4": KKO's lemma is about two polygon
points, and this is the conditional core that §5.3's proof runs once the
configuration has been oriented, with

  * `hover` — `start L(q)` lies in `L(p)`'s arc (the orientation);
  * `hpast` — `L(q)`'s arc reaches past `L(p)`'s right end (`q` rightmost).

Given those, the edge `{a,b}` cannot be charged on the right at both points.
The chain is the paper's: Claim 5.9 puts `L(p)_R` across `L(q)` on the
right, the Chain Lemma keeps `L(p)` out of `L(q)^∩R`, so `L(p)` is a
candidate for `L*(q)`; Lemma 4.29 then puts `L(p) ∩ L(q)^∩R` inside
`L*(q)`, landing `a` in `L*(q)` — exactly what being charged at `q` forbids.

KKO assert "`L(p)` crosses `L(q)^∩R` on the left" without argument.  The
crossing itself is where Claim 5.9, the Chain Lemma step, and the
rightmost-atom fact get used; the *side* then falls out of the crossing
dichotomy for the almost diagonal cut `L(q)^∩R`: crossing on the right
would put `start L(p)` in the tail of `L(q)`'s arc, wrapping
`O(L(p) ∪ L(q))` around the whole polygon, against Fact 4.8
(`union_arc_lt`).

When `hpast` fails the arcs nest instead of properly overlapping, and this
argument does not run — `lemma54_right_of_nested_geometry` handles that
configuration, and `lemma54_right` assembles the case split. -/
theorem lemma54_right_of_oriented_geometry (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Lp Lq LpR LqR LqStar : Finset (Fin n)}
    (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hLpR : P.IsSR Lp LpR) (hLqR : P.IsSR Lq LqR)
    (hLqStar : P.IsChosenLStar (Lq ∩ LqR) (P.start LqR) LqStar)
    (hover : (P.start Lq - P.start Lp).val < P.len Lp)
    (hpast : P.len Lp < (P.start Lq - P.start Lp).val + P.len Lq)
    {a b : Fin n} (haLp : a ∈ Lp) (haLpR : a ∈ LpR)
    (haq : a ∈ (Lq ∩ LqR) \ LqStar)
    (hbLpR : b ∈ LpR) (hbLq : b ∉ Lq) (hbLqR : b ∈ LqR) : False := by
  have haqi := (Finset.mem_sdiff.mp haq).1
  have haLq : a ∈ Lq := (Finset.mem_inter.mp haqi).1
  -- Claim 5.9, then the Chain Lemma step, then `L(q)^∩R`'s arc
  have hclaim59 := P.crossesOnRight_isSR_of_rightmost hx hη0 (by linarith) hC
    hLp hLq hLpR hLqR hover hpast haLp haLq haLpR hbLpR hbLq hbLqR
  have hnotsub := P.not_subset_inter_isSR hx hη0 hη hC hLq hLpR hLqR hclaim59
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_inter hx hη0 hC hLq hLqR.1 hLqR.2.1
  -- the rightmost outside atom of `L(q)`: inside `L(q)^∩R`, outside `L(p)`
  have hγ : (P.start LqR - P.start Lq).val < P.len Lq :=
    mem_arcSet.mp hLqR.2.1.2
  obtain ⟨i, hival, hiLq, hiLp⟩ :=
    P.exists_last_atom_notMem hLp hLq hover hpast
  have hiU : P.out i ⊆ Lq ∩ LqR :=
    P.out_last_subset_inter hLq hLqR.2.1 hUarc hival
  obtain ⟨w, hw⟩ := P.out_nonempty i
  have hwLp : w ∉ Lp := by
    rcases atom_subset_or_disjoint (P.out_atom i) hLp with h | h
    · exact absurd h hiLp
    · exact Finset.disjoint_left.mp h hw
  -- `L(p)` crosses `L(q)^∩R`
  have hcross : Crossing Lp (Lq ∩ LqR) := by
    refine ⟨⟨a, Finset.mem_inter.mpr ⟨haLp, haqi⟩⟩, ?_,
      ⟨w, Finset.mem_sdiff.mpr ⟨hiU hw, hwLp⟩⟩, ?_⟩
    · rcases Finset.eq_empty_or_nonempty (Lp \ (Lq ∩ LqR)) with hemp | hne
      · exact absurd (Finset.sdiff_eq_empty_iff_subset.mp hemp) hnotsub
      · exact hne
    · intro hcov
      obtain ⟨v, hv⟩ := P.rootAtom_nonempty
      have hmem : v ∈ Lp ∪ (Lq ∩ LqR) := hcov ▸ Finset.mem_univ v
      rcases Finset.mem_union.mp hmem with h | h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint Lp hLp) hv h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint Lq hLq) hv
          (Finset.mem_inter.mp h).1
  -- ... and on the left: crossing on the right would put `start L(p)` in
  -- the tail of `L(q)`'s arc, wrapping `O(L(p) ∪ L(q))` around the polygon
  have hside : P.start LqR ∈ arcSet (P.start Lp) (P.len Lp) := by
    have hlt := P.union_arc_lt hLp hLq hover
    have h2Lp := P.two_le_len Lp hLp
    rcases P.crossesOnLeftArc_or_crossesOnRightArc hx hη0 (by linarith) hC
      hUad hUarc hLp hcross with h | h
    · exact h.2
    · have hmemU := mem_arcSet.mp h.2
      have hrel := val_sub_rel (P.start LqR) (P.start Lp) (P.start Lq)
      rw [Nat.mod_eq_of_lt (by omega)] at hrel
      rw [mem_arcSet, hrel]
      rcases eq_or_ne (P.start Lp) (P.start LqR) with heq | hne2
      · have h0 : (P.start LqR - P.start Lp).val = 0 := by
          rw [heq, sub_self]
          simp only [Fin.val_zero]
        omega
      · have hsum := val_sub_add_val_sub hne2
        omega
  rcases hLqStar with hstar | ⟨-, hnone⟩
  · exact P.not_mem_sdiff_isLStar hx hη0 hη hC hUad hUarc hLp ⟨hcross, hside⟩
      hstar haLp haqi haq
  · -- `L*(q) = ∅` because nothing crosses `L(q)^∩R` on the left — but
    -- `L(p)` just did
    exact hnone Lp hLp ⟨hcross, hside⟩

/-- **§5.3's argument, in the nested orientation.**

KKO's "WLOG `q` is the rightmost point of `O(L(p) ∪ L(q))`" includes the
case where `L(p)`'s arc sits *inside* `L(q)`'s — `L(q)` is then the outer
interval and `q` still its rightmost point — but their written proof
silently treats only proper overlap.  This is the missing branch.  Neither
`hover` nor `hpast` holds here; what replaces them is `hnest`, together with
the two points being distinct (`hne` — for `p = q` the exclusion is false as
stated, a hypothesis the paper omits and its counting application always
supplies).

The endgame is the same as in the oriented core, but every ingredient is
reached differently: nesting plus the shared endpoint give `L(p) ⊆ L(q)`
outright; Claim 5.9's crossing needs no rightmost atom (`L(q) ⊆ L(p)_R`
would swallow `L(p)`, against `L(p)_R` crossing `L(p)`); the Chain Lemma
step then keeps `L(p)` outside `L(q)^∩R`, hence outside `L(q)_R`, so the
charged edge makes `L(p)` cross `L(q)_R` — on the *left*, because
`start L(p) ∈ O(L(q)_R)` would swallow `L(p)`'s arc whole
(`arc_subset_of_nested_of_mem`).  The last outside atom of the outer cut
supplies the missing point of `(L(q)^∩R) ∖ L(p)`, and Lemma 4.29 lands `a`
in `L*(q)` as before.

Note `IsLp`-maximality of the cuts is never used: only membership in `𝒞`
and the distinct right points matter. -/
theorem lemma54_right_of_nested_geometry (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Lp Lq LpR LqR LqStar : Finset (Fin n)}
    (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hLpR : P.IsSR Lp LpR) (hLqR : P.IsSR Lq LqR)
    (hLqStar : P.IsChosenLStar (Lq ∩ LqR) (P.start LqR) LqStar)
    (hne : P.rightPoint Lp ≠ P.rightPoint Lq)
    (hnest : (P.start Lp - P.start Lq).val + P.len Lp ≤ P.len Lq)
    {a b : Fin n} (haLp : a ∈ Lp) (haLpR : a ∈ LpR)
    (haq : a ∈ (Lq ∩ LqR) \ LqStar)
    (hbLpR : b ∈ LpR) (hbLq : b ∉ Lq) (hbLqR : b ∈ LqR) : False := by
  have haqi := (Finset.mem_sdiff.mp haq).1
  have haLq : a ∈ Lq := (Finset.mem_inter.mp haqi).1
  have haLqR : a ∈ LqR := (Finset.mem_inter.mp haqi).2
  -- nesting plus the shared endpoint put `L(p)` inside `L(q)`
  have hsubpq : Lp ⊆ Lq := P.subset_of_nested_arcs hLp hLq hne hnest
    ⟨a, Finset.mem_inter.mpr ⟨haLq, haLp⟩⟩
  have hbLp : b ∉ Lp := fun h => hbLq (hsubpq h)
  -- Claim 5.9: `L(p)_R` crosses `L(q)` on the right.  `L(q) ⊆ L(p)_R`
  -- would swallow `L(p)`, against `L(p)_R` crossing `L(p)`
  have hclaim59 : P.CrossesOnRight LpR Lq := by
    have hcross : Crossing LpR Lq := by
      refine ⟨⟨a, Finset.mem_inter.mpr ⟨haLpR, haLq⟩⟩,
        ⟨b, Finset.mem_sdiff.mpr ⟨hbLpR, hbLq⟩⟩, ?_,
        P.union_ne_univ hLpR.1 hLq⟩
      rcases Finset.eq_empty_or_nonempty (Lq \ LpR) with hemp | hne'
      · exfalso
        have hsub : Lq ⊆ LpR := Finset.sdiff_eq_empty_iff_subset.mp hemp
        obtain ⟨v, hv⟩ := hLpR.2.1.1.2.2.1
        rw [Finset.mem_sdiff] at hv
        exact hv.2 (hsub (hsubpq hv.1))
      · exact hne'
    exact P.crossesOnRight_of_witness hx hη0 (by linarith) hC hLq hLpR.1
      hLqR.1 hcross hLqR.2.1 (Finset.mem_sdiff.mpr ⟨hbLpR, hbLq⟩)
      (Finset.mem_sdiff.mpr ⟨hbLqR, hbLq⟩)
  -- the Chain Lemma keeps `L(p)` out of `L(q)^∩R`, hence out of `L(q)_R`
  have hnotsub : ¬ (Lp ⊆ Lq ∩ LqR) :=
    P.not_subset_inter_isSR hx hη0 hη hC hLq hLpR hLqR hclaim59
  have hnotsubR : ¬ (Lp ⊆ LqR) := fun h =>
    hnotsub (Finset.subset_inter hsubpq h)
  have hcrossR : Crossing Lp LqR :=
    P.crossing_of_charged hLp hLqR.1 haLp haLqR hbLqR hbLp hnotsubR
  -- ... and on the left: `start L(p) ∈ O(L(q)_R)` would swallow `L(p)`'s
  -- arc whole, against the crossing
  have hside : P.start LqR ∈ arcSet (P.start Lp) (P.len Lp) := by
    refine P.hside_of_not_crossesOnRight hLp hLqR.1 hcrossR fun hmem => ?_
    exact P.not_crossing_of_arc_subset hLqR.1 hLp
      (P.arc_subset_of_nested_of_mem hLq hLqR.1 hLqR.2.1 hnest hmem)
      hcrossR.symm
  -- the last outside atom of the outer cut: inside `L(q)^∩R`, outside `L(p)`
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_inter hx hη0 hC hLq hLqR.1 hLqR.2.1
  obtain ⟨i, hival, hiLq, hiLp⟩ :=
    P.exists_last_atom_notMem_of_nested hLp hLq hne hnest
  have hiU : P.out i ⊆ Lq ∩ LqR :=
    P.out_last_subset_inter hLq hLqR.2.1 hUarc hival
  obtain ⟨w, hw⟩ := P.out_nonempty i
  have hwLp : w ∉ Lp := by
    rcases atom_subset_or_disjoint (P.out_atom i) hLp with h | h
    · exact absurd h hiLp
    · exact Finset.disjoint_left.mp h hw
  -- `L(p)` crosses `L(q)^∩R` on the left, and Lemma 4.29 lands `a` in `L*(q)`
  have hcross : Crossing Lp (Lq ∩ LqR) := by
    refine ⟨⟨a, Finset.mem_inter.mpr ⟨haLp, haqi⟩⟩, ?_,
      ⟨w, Finset.mem_sdiff.mpr ⟨hiU hw, hwLp⟩⟩, ?_⟩
    · rcases Finset.eq_empty_or_nonempty (Lp \ (Lq ∩ LqR)) with hemp | hne'
      · exact absurd (Finset.sdiff_eq_empty_iff_subset.mp hemp) hnotsub
      · exact hne'
    · intro hcov
      obtain ⟨v, hv⟩ := P.rootAtom_nonempty
      have hmem : v ∈ Lp ∪ (Lq ∩ LqR) := hcov ▸ Finset.mem_univ v
      rcases Finset.mem_union.mp hmem with h | h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint Lp hLp) hv h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint Lq hLq) hv
          (Finset.mem_inter.mp h).1
  rcases hLqStar with hstar | ⟨-, hnone⟩
  · exact P.not_mem_sdiff_isLStar hx hη0 hη hC hUad hUarc hLp ⟨hcross, hside⟩
      hstar haLp haqi haq
  · -- `L*(q) = ∅` because nothing crosses `L(q)^∩R` on the left — but
    -- `L(p)` just did
    exact hnone Lp hLp ⟨hcross, hside⟩

/-- **KKO22 Lemma 5.4, right version, assembled.**  Two distinct polygon
points cannot both charge the edge `{a, b}` on the right through the shared
endpoint `a`.

The arcs of `L(p)` and `L(q)` meet (`overlap_of_shared_vertex` — the
overlap KKO's Fact 4.8 does not actually supply), and in each of the two
orientations either the far arc reaches past the near one's right end —
KKO's proper-overlap picture, `lemma54_right_of_oriented_geometry` — or it
is contained, the nested branch their written proof skips,
`lemma54_right_of_nested_geometry` with the outer cut playing `L(q)`.

`hne` is the distinctness of the two points, which the paper's statement
omits: for `p = q` the exclusion is false, and the counting application
(`card_rightCharging_le_two`) only ever compares distinct points. -/
theorem lemma54_right (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Lp Lq LpR LqR LpStar LqStar : Finset (Fin n)}
    (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hLpR : P.IsSR Lp LpR) (hLqR : P.IsSR Lq LqR)
    (hLpStar : P.IsChosenLStar (Lp ∩ LpR) (P.start LpR) LpStar)
    (hLqStar : P.IsChosenLStar (Lq ∩ LqR) (P.start LqR) LqStar)
    (hne : P.rightPoint Lp ≠ P.rightPoint Lq) {a b : Fin n}
    (hap : a ∈ (Lp ∩ LpR) \ LpStar) (haq : a ∈ (Lq ∩ LqR) \ LqStar)
    (hbp : b ∈ LpR \ (Lp ∩ LpR)) (hbq : b ∈ LqR \ (Lq ∩ LqR)) : False := by
  obtain ⟨hapi, -⟩ := Finset.mem_sdiff.mp hap
  obtain ⟨haqi, -⟩ := Finset.mem_sdiff.mp haq
  obtain ⟨haLp, haLpR⟩ := Finset.mem_inter.mp hapi
  obtain ⟨haLq, haLqR⟩ := Finset.mem_inter.mp haqi
  obtain ⟨hbLpR, hbp'⟩ := Finset.mem_sdiff.mp hbp
  obtain ⟨hbLqR, hbq'⟩ := Finset.mem_sdiff.mp hbq
  have hbLp : b ∉ Lp := fun h => hbp' (Finset.mem_inter.mpr ⟨h, hbLpR⟩)
  have hbLq : b ∉ Lq := fun h => hbq' (Finset.mem_inter.mpr ⟨h, hbLqR⟩)
  rcases P.overlap_of_shared_vertex hLp hLq haLp haLq with hover | hover
  · rcases lt_or_ge (P.len Lp) ((P.start Lq - P.start Lp).val + P.len Lq)
      with hpast | hnest
    · exact P.lemma54_right_of_oriented_geometry hx hη0 hη hC hLp hLq hLpR
        hLqR hLqStar hover hpast haLp haLpR haq hbLpR hbLq hbLqR
    · exact P.lemma54_right_of_nested_geometry hx hη0 hη hC hLq hLp hLqR
        hLpR hLpStar hne.symm hnest haLq haLqR hap hbLqR hbLp hbLpR
  · rcases lt_or_ge (P.len Lq) ((P.start Lp - P.start Lq).val + P.len Lp)
      with hpast | hnest
    · exact P.lemma54_right_of_oriented_geometry hx hη0 hη hC hLq hLp hLqR
        hLpR hLpStar hover hpast haLq haLqR hap hbLqR hbLp hbLpR
    · exact P.lemma54_right_of_nested_geometry hx hη0 hη hC hLp hLq hLpR
        hLqR hLqStar hne hnest haLp haLpR haq hbLpR hbLq hbLqR

/-- **§5.3's argument, mirrored to the left — the single oriented core.**

For the left bad events the cuts are `R(p)`, `R(q)` with *left* polygon
points `p`, `q`, the crossers `R_L` cross on the left, and `R*` maximizes
over *right*-crossers of `R(q)^∩L`.  The chain is the mirror of the right
side's — Claim 5.9's mirror, the left chain step, the crossing of
`R(q)^∩L`, then `R*`-maximality landing `a` in `R*(q)`.

Unlike the right side, no nested branch arises: the polygon points are the
arcs' left ends, so `hne` (that is, `p ≠ q`) and the orientation `hover`
put `R(q)`'s *first* atom outside `R(p)` in the proper-overlap and nested
configurations alike, and the side of the final crossing is excluded by
`union_arc_lt` in both.  This asymmetry is the encoding's central fact at
work — left-anchored objects are measured directly by the interval
representation. -/
theorem lemma54_left_of_oriented_geometry (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Rp Rq RpL RqL RqStar : Finset (Fin n)}
    (hRp : Rp ∈ 𝒞) (hRq : Rq ∈ 𝒞)
    (hRpL : P.IsSL Rp RpL) (hRqL : P.IsSL Rq RqL)
    (hRqStar : P.IsChosenRStar (Rq ∩ RqL) (P.start Rq)
      (P.len RqL - (P.start Rq - P.start RqL).val) RqStar)
    (hne : P.start Rp ≠ P.start Rq)
    (hover : (P.start Rp - P.start Rq).val < P.len Rq)
    {a b : Fin n} (haRp : a ∈ Rp) (haRpL : a ∈ RpL)
    (haq : a ∈ (Rq ∩ RqL) \ RqStar)
    (hbRpL : b ∈ RpL) (hbRq : b ∉ Rq) (hbRqL : b ∈ RqL) : False := by
  have haqi := (Finset.mem_sdiff.mp haq).1
  have haRq : a ∈ Rq := (Finset.mem_inter.mp haqi).1
  -- Claim 5.9's mirror, then the left chain step, then `R(q)^∩L`'s arc
  have hclaim := P.crossesOnLeft_isSL_of_leftmost hx hη0 (by linarith) hC
    hRp hRq hRpL hRqL hne hover haRp haRq haRpL hbRpL hbRq hbRqL
  have hnotsub := P.not_subset_inter_isSL hx hη0 hη hC hRq hRpL hRqL hclaim
  obtain ⟨hUad, hUarc⟩ :=
    P.isAlmostDiagonal_inter_left hx hη0 hC hRq hRqL.1 hRqL.2.1
  -- the first outside atom of `R(q)`: inside `R(q)^∩L`, outside `R(p)`
  obtain ⟨hiRq, hiRp⟩ := P.out_start_notMem hRp hRq hne hover
  have hdL : (P.start Rq - P.start RqL).val < P.len RqL :=
    mem_arcSet.mp hRqL.2.1.2
  have hiU : P.out (P.start Rq) ⊆ Rq ∩ RqL := by
    refine (P.out_subset_iff_mem_arc hUarc _).mpr (mem_arcSet.mpr ?_)
    rw [sub_self]
    simp only [Fin.val_zero]
    omega
  obtain ⟨w, hw⟩ := P.out_nonempty (P.start Rq)
  have hwRp : w ∉ Rp := by
    rcases atom_subset_or_disjoint (P.out_atom (P.start Rq)) hRp with h | h
    · exact absurd h hiRp
    · exact Finset.disjoint_left.mp h hw
  -- `R(p)` crosses `R(q)^∩L`
  have hcross : Crossing Rp (Rq ∩ RqL) := by
    refine ⟨⟨a, Finset.mem_inter.mpr ⟨haRp, haqi⟩⟩, ?_,
      ⟨w, Finset.mem_sdiff.mpr ⟨hiU hw, hwRp⟩⟩, ?_⟩
    · rcases Finset.eq_empty_or_nonempty (Rp \ (Rq ∩ RqL)) with hemp | hne'
      · exact absurd (Finset.sdiff_eq_empty_iff_subset.mp hemp) hnotsub
      · exact hne'
    · intro hcov
      obtain ⟨v, hv⟩ := P.rootAtom_nonempty
      have hmem : v ∈ Rp ∪ (Rq ∩ RqL) := hcov ▸ Finset.mem_univ v
      rcases Finset.mem_union.mp hmem with h | h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint Rp hRp) hv h
      · exact Finset.disjoint_left.mp (P.rootAtom_disjoint Rq hRq) hv
          (Finset.mem_inter.mp h).1
  -- ... and on the right: crossing on the left would put `start R(q)` in
  -- `R(p)`'s arc, covering the polygon together with `R(q)`'s
  have hside : P.start Rp ∈ arcSet (P.start Rq)
      (P.len RqL - (P.start Rq - P.start RqL).val) := by
    rcases P.crossesOnLeftArc_or_crossesOnRightArc hx hη0 (by linarith) hC
      hUad hUarc hRp hcross with h | h
    · exfalso
      have hmem := mem_arcSet.mp h.2
      have hcov := P.union_arc_lt hRq hRp hover
      have he : 0 < (P.start Rp - P.start Rq).val := by
        rcases Nat.eq_zero_or_pos (P.start Rp - P.start Rq).val with h0 | h0
        · exact absurd (sub_eq_zero.mp (Fin.val_injective (by simpa using h0)))
            hne
        · exact h0
      have hsum := val_sub_add_val_sub hne
      omega
    · exact h.2
  rcases hRqStar with hstar | ⟨-, hnone⟩
  · exact P.not_mem_sdiff_isRStar hx hη0 hη hC hUad hUarc hRp ⟨hcross, hside⟩
      hstar haRp haqi haq
  · -- `R*(q) = ∅` because nothing crosses `R(q)^∩L` on the right — but
    -- `R(p)` just did
    exact hnone Rp hRp ⟨hcross, hside⟩

/-- **KKO22 Lemma 5.4, left version, assembled.**  Two distinct polygon
points cannot both charge the edge `{a, b}` on the left through the shared
endpoint `a`.

Only the orientation split remains: whichever of the two cuts' arcs
contains the other's start plays `R(q)` in the oriented core, and `p ≠ q`
— here literally `start R(p) ≠ start R(q)`, since the points *are* the
starts — feeds both branches. -/
theorem lemma54_left (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {Rp Rq RpL RqL RpStar RqStar : Finset (Fin n)}
    (hRp : Rp ∈ 𝒞) (hRq : Rq ∈ 𝒞)
    (hRpL : P.IsSL Rp RpL) (hRqL : P.IsSL Rq RqL)
    (hRpStar : P.IsChosenRStar (Rp ∩ RpL) (P.start Rp)
      (P.len RpL - (P.start Rp - P.start RpL).val) RpStar)
    (hRqStar : P.IsChosenRStar (Rq ∩ RqL) (P.start Rq)
      (P.len RqL - (P.start Rq - P.start RqL).val) RqStar)
    (hne : P.start Rp ≠ P.start Rq) {a b : Fin n}
    (hap : a ∈ (Rp ∩ RpL) \ RpStar) (haq : a ∈ (Rq ∩ RqL) \ RqStar)
    (hbp : b ∈ RpL \ (Rp ∩ RpL)) (hbq : b ∈ RqL \ (Rq ∩ RqL)) : False := by
  obtain ⟨hapi, -⟩ := Finset.mem_sdiff.mp hap
  obtain ⟨haqi, -⟩ := Finset.mem_sdiff.mp haq
  obtain ⟨haRp, haRpL⟩ := Finset.mem_inter.mp hapi
  obtain ⟨haRq, haRqL⟩ := Finset.mem_inter.mp haqi
  obtain ⟨hbRpL, hbp'⟩ := Finset.mem_sdiff.mp hbp
  obtain ⟨hbRqL, hbq'⟩ := Finset.mem_sdiff.mp hbq
  have hbRp : b ∉ Rp := fun h => hbp' (Finset.mem_inter.mpr ⟨h, hbRpL⟩)
  have hbRq : b ∉ Rq := fun h => hbq' (Finset.mem_inter.mpr ⟨h, hbRqL⟩)
  rcases P.overlap_of_shared_vertex hRp hRq haRp haRq with hover | hover
  · exact P.lemma54_left_of_oriented_geometry hx hη0 hη hC hRq hRp hRqL
      hRpL hRpStar hne.symm hover haRq haRqL hap hbRqL hbRp hbRpL
  · exact P.lemma54_left_of_oriented_geometry hx hη0 hη hC hRp hRq hRpL
      hRqL hRqStar hne hover haRp haRpL haq hbRpL hbRq hbRqL

/-- **KKO22 Fact 4.8**: the outside atoms of two cuts never exhaust the
polygon.

KKO argue from the root atom lying in neither cut: "then there must be a
polygon point which is in neither of them".  That last step reads the
polygon's cell structure and is invisible to the interval encoding when the
root is an inside atom — which KKO22 §4.2 explicitly allow — so it is
carried by `PolygonRep.arcs_ne_univ` and recorded here under its paper
name. -/
theorem arc_union_ne_univ (P : PolygonRep 𝒞) {S S' : Finset (Fin n)}
    (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞) :
    arcSet (P.start S) (P.len S) ∪ arcSet (P.start S') (P.len S')
      ≠ Finset.univ :=
  P.arcs_ne_univ S hS S' hS'

/-- **`O(S ∪ S')` is a contiguous interval** for two cuts of the
component whose arcs overlap — KKO22's step "by Fact 4.8,
`O(L(p) ∪ L(q)) ≠ O(A(𝒞))`, so it forms a contiguous interval".

Fact 4.8 supplies the non-covering hypothesis that `arcSet_union_of_mem`
needs, so the two combine directly. -/
theorem outsideIn_union_eq_arc (P : PolygonRep 𝒞) (hS : S ∈ 𝒞)
    {S' : Finset (Fin n)} (hS' : S' ∈ 𝒞)
    (hmem : (P.start S' - P.start S).val < P.len S) :
    P.outsideIn S ∪ P.outsideIn S'
      = arcSet (P.start S)
          (max (P.len S) ((P.start S' - P.start S).val + P.len S')) := by
  rw [P.outsideIn_eq_arc hS, P.outsideIn_eq_arc hS']
  exact arcSet_union_of_mem hmem (P.arc_union_ne_univ hS hS')

/-- Fact 4.8 at the level of vertices: two cuts of the component never
cover `V`.  (Already available as `union_ne_univ`; recorded here under
its paper name.) -/
theorem union_ne_univ_of_mem (P : PolygonRep 𝒞) {S S' : Finset (Fin n)}
    (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞) : S ∪ S' ≠ Finset.univ :=
  P.union_ne_univ hS hS'

/-! ### KKO22 Lemma 5.6: the bad-event edge sets are heavy

For a polygon point `p`, `E(B→(p)) = E(L^∩R ∖ L*, L_R ∖ L^∩R)`, and KKO
observe that with `L* ⊆ L^∩R ⊆ L_R` these two sides are disjoint with
union `L_R ∖ L*`, a `2η`-near min cut.  Lemma 2.8 then gives the mass
bound `≥ 1 − η` directly.  Both steps are available: the nesting identity
is elementary, and Lemma 2.8 is `le_pairSum_of_union` from the Phase 1
uncrossing toolkit. -/

/-- The disjoint decomposition behind Lemma 5.6: for `Z ⊆ X ⊆ Y`,
`(X ∖ Z) ⊎ (Y ∖ X) = Y ∖ Z`. -/
theorem sdiff_union_sdiff_of_subset {X Y Z : Finset (Fin n)} (hZX : Z ⊆ X)
    (hXY : X ⊆ Y) :
    (X \ Z) ∪ (Y \ X) = Y \ Z ∧ Disjoint (X \ Z) (Y \ X) := by
  constructor
  · ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hv, hv'⟩ | ⟨hv, hv'⟩)
      · exact ⟨hXY hv, hv'⟩
      · exact ⟨hv, fun hz => hv' (hZX hz)⟩
    · rintro ⟨hv, hv'⟩
      by_cases hx : v ∈ X
      · exact Or.inl ⟨hx, hv'⟩
      · exact Or.inr ⟨hv, hx⟩
  · exact Finset.disjoint_left.mpr fun v hv hv' =>
      (Finset.mem_sdiff.mp hv').2 (Finset.mem_sdiff.mp hv).1

/-- **KKO22 Lemma 5.6**: the bad-event edge set `E(B→(p))` carries
`x`-mass at least `1 − η`.

Stated in the paper's shape with `X = L^∩R`, `Z = L*`, `Y = L_R`: the two
sides of the edge set are `X ∖ Z` and `Y ∖ X`, whose union is the
`2η`-near minimum cut `Y ∖ Z`. -/
theorem one_sub_le_sum_badEdges (hx : x ∈ subtourLP n)
    {X Y Z : Finset (Fin n)} (hZX : Z ⊆ X) (hXY : X ⊆ Y)
    (h1 : (X \ Z).Nonempty) (h1' : X \ Z ≠ Finset.univ)
    (h2 : (Y \ X).Nonempty) (h2' : Y \ X ≠ Finset.univ)
    (hnmc : IsNearMinCut x (2 * η) (Y \ Z)) :
    1 - η ≤ ∑ e ∈ betweenEdges (X \ Z) (Y \ X), x e := by
  obtain ⟨hunion, hdisj⟩ := sdiff_union_sdiff_of_subset hZX hXY
  rw [sum_betweenEdges x hdisj]
  have hcut : cutSum x ((X \ Z) ∪ (Y \ X)) ≤ 2 + 2 * η := by
    rw [hunion]
    exact hnmc.cut_le
  have := le_pairSum_of_union hx hdisj h1 h1' h2 h2' hcut
  linarith

/-! ### KKO22 Corollary 5.8 and Lemma 5.3

Corollary 5.8 is Lemma 4.27 read on edges: an edge of `E←(S)` has an
endpoint in `S_L ∖ S` and an edge of `E→(S)` one in `S_R ∖ S`, and those
two sets are disjoint.

Lemma 5.3 says that if the tree crosses `S` a number of times other than
two, a bad event occurs at one of `S`'s two polygon points.  Its
deterministic core — proved here — is the trichotomy count: `δ(S)` is the
disjoint union of `E←(S)`, `E→(S)` and `E∘(S)`, so if the tree meets the
first two exactly once each and the third not at all, it meets `δ(S)`
exactly twice.

KKO's polygon-point form is this statement transported along
`E←(S) = E←(R(p_l))` and `E→(S) = E→(L(p_r))` (Lemma 5.1, whose
right-hand half is `arrowRight_eq_of_shared_rightPoint` above) together
with `E∘(S) ⊆ E∘(L(p_r)) ∪ E∘(R(p_l))` (Lemma 5.7, not yet formalized).
Once those are in place the transport is definitional rewriting. -/

/-- **KKO22 Corollary 5.8**: the two arrow edge sets of a cut crossed on
both sides are disjoint. -/
theorem disjoint_arrowLeft_arrowRight_of_crossing (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞) {L R : Finset (Fin n)}
    (hL : L ∈ 𝒞) (hR : R ∈ 𝒞) (hcL : P.CrossesOnLeft L S)
    (hcR : P.CrossesOnRight R S) :
    Disjoint (arrowLeft S L) (arrowRight S R) :=
  disjoint_arrowLeft_arrowRight
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 hη hC hS hL hR
      hcL hcR)

/-- **KKO22 Lemma 5.3**, deterministic core: if the tree meets `E←(S)`
and `E→(S)` exactly once each and misses `E∘(S)`, it meets `δ(S)`
exactly twice. -/
theorem cut_card_eq_two_of_counts {S L R : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))} (hd : Disjoint (L \ S) (R \ S))
    (h1 : (arrowLeft S L ∩ T).card = 1)
    (h2 : (arrowRight S R ∩ T).card = 1)
    (h3 : (arrowCirc S L R ∩ T).card = 0) :
    (cutEdges S ∩ T).card = 2 := by
  classical
  have hLR := disjoint_arrowLeft_arrowRight (S := S) hd
  have hcirc : Disjoint (arrowLeft S L ∪ arrowRight S R) (arrowCirc S L R) := by
    have hrw : arrowCirc S L R
        = cutEdges S \ (arrowLeft S L ∪ arrowRight S R) := by
      rw [arrowCirc, sdiff_sdiff_left]
      rfl
    rw [hrw]
    exact Finset.disjoint_sdiff
  have d1 : Disjoint (arrowLeft S L ∩ T) (arrowRight S R ∩ T) :=
    hLR.mono Finset.inter_subset_left Finset.inter_subset_left
  have d2 : Disjoint (arrowLeft S L ∩ T ∪ arrowRight S R ∩ T)
      (arrowCirc S L R ∩ T) := by
    refine hcirc.mono ?_ Finset.inter_subset_left
    exact Finset.union_subset
      (Finset.inter_subset_left.trans Finset.subset_union_left)
      (Finset.inter_subset_left.trans Finset.subset_union_right)
  rw [cutEdges_eq_arrow_union hd, Finset.union_inter_distrib_right,
    Finset.union_inter_distrib_right, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, h1, h2, h3]

/-- **KKO22 Lemma 5.3** (All cuts are satisfied), in the paper's
polygon-point form.

If the tree does not meet `δ(S)` exactly twice, then a bad event occurs
at one of `S`'s two polygon points — that is, either the left pair at
`R = R(p_l)` fails (`|E←(R) ∩ T| ≠ 1` or `|E∘(R) ∩ T| ≠ 0`) or the right
pair at `L = L(p_r)` does.

The three geometric inputs are the ones established above: Lemma 5.1 on
each side supplies `E←(S) = E←(R)` and `E→(S) = E→(L)`, and Lemma 5.7
supplies `E∘(S) ⊆ E∘(L) ∪ E∘(R)`.  Given those, the argument is the
counting core: the two arrow counts transfer verbatim to `S`, the
leftover count at `S` is forced to zero, and `δ(S)` is met exactly
twice. -/
theorem bad_event_at_polygon_points {S L R SL SR LL LR RL RR : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))}
    (hinterLR : L ∩ R = S)
    (hEleft : arrowLeft S SL = arrowLeft R RL)
    (hEright : arrowRight S SR = arrowRight L LR)
    (hdS : Disjoint (SL \ S) (SR \ S))
    (hdL : Disjoint (LL \ L) (LR \ L)) (hdR : Disjoint (RL \ R) (RR \ R))
    (h427L : Disjoint (LL \ L) (R \ L)) (h427R : Disjoint (L \ R) (RR \ R))
    (hcor58 : Disjoint (arrowLeft L LL) (arrowRight R RR))
    (hT : (cutEdges S ∩ T).card ≠ 2) :
    ((arrowLeft R RL ∩ T).card ≠ 1 ∨ (arrowCirc R RL RR ∩ T).card ≠ 0) ∨
      ((arrowRight L LR ∩ T).card ≠ 1 ∨
        (arrowCirc L LL LR ∩ T).card ≠ 0) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
  refine hT (cut_card_eq_two_of_counts hdS ?_ ?_ ?_)
  · rw [hEleft]; exact h1
  · rw [hEright]; exact h3
  · -- the leftover edges of `S` are covered by those of `L` and `R`
    have hsub := arrowCirc_subset_union hinterLR hEleft hEright hdL hdR h427L
      h427R hcor58
    rw [Finset.card_eq_zero] at h2 h4
    have hE : arrowCirc S SL SR ∩ T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      rw [Finset.mem_inter] at he
      rcases Finset.mem_union.mp (hsub he.1) with h | h
      · have hmem : e ∈ arrowCirc L LL LR ∩ T := Finset.mem_inter.mpr ⟨h, he.2⟩
        rw [h4] at hmem
        exact absurd hmem (Finset.notMem_empty e)
      · have hmem : e ∈ arrowCirc R RL RR ∩ T := Finset.mem_inter.mpr ⟨h, he.2⟩
        rw [h2] at hmem
        exact absurd hmem (Finset.notMem_empty e)
    rw [hE, Finset.card_empty]

/-- **KKO22 Lemma 5.3**, contrapositive: if the tree does not meet `δ(S)`
exactly twice, one of the three bad events at `S` occurs. -/
theorem bad_event_of_cut_card_ne_two {S L R : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))} (hd : Disjoint (L \ S) (R \ S))
    (h : (cutEdges S ∩ T).card ≠ 2) :
    (arrowLeft S L ∩ T).card ≠ 1 ∨ (arrowRight S R ∩ T).card ≠ 1 ∨
      (arrowCirc S L R ∩ T).card ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (cut_card_eq_two_of_counts hd hcon.1 hcon.2.1 hcon.2.2)

/-- With Lemma 4.27, the `E∘` bound of the trichotomy holds for the
genuine `S_L`, `S_R` with no side condition. -/
theorem sum_arrowCirc_le' (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 5) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hS : S ∈ 𝒞) (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hcL : P.CrossesOnLeft L S) (hcR : P.CrossesOnRight R S) :
    ∑ e ∈ arrowCirc S L R, x e ≤ 2 * η :=
  sum_arrowCirc_le hx (hC.nearMin S hS) (hC.nearMin L hL) (hC.nearMin R hR)
    hcL.1 hcR.1
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 hη hC hS hL hR
      hcL hcR)

end PolygonRep

end TSPGap

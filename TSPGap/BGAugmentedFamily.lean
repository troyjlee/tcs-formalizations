/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGPolygonCore
import TSPGap.Components

/-!
# Augmenting a component by unions of its atoms

KKO22 prove Lemma 4.23 and Fact 4.26 by contracting the atoms of a component `𝒞` and
working in the component `𝒞'` of the contracted graph.  This module supplies what lets the
BG08 core do the same work *without* a contraction layer (`audits/qa/q17`):

* `exists_cross_of_union_atoms`: a proper nonempty union of atoms of a crossing-connected
  family with two atoms on each side crosses a member — the combinatorial core of KKO22
  Lemma 4.6, from KKO22 Theorem 4.5 (`exists_atomOf_union_atomOf_eq_univ`, already root-free
  in `Components.lean`) applied to the singleton family `{A}`;
* `conn_insert`: inserting a set crossing a member keeps the cross graph connected;
* `isBGFamily_symmetrize_of_cross`: the non-rooted constructor of a BG family (every member
  crosses a member), and `isBGFamily_of_nearMin`, its `η < 2/5` instance with `NoKCycle _ 4`;
* `Inside.mono` / `symmetrize_mono`: outside elements of the augmented family are outside
  for `𝒞`;
* the polygon translation: `exists_out_eq_atomOf` (an outside element's atom is some
  `P.out i`), `mem_iff_atomOf_subset` (membership in a union of atoms), and the traces of a
  single atom and of a co-atom (`card_outsideIn_le_one`, `card_outsideIn_ge`).
-/

namespace TSPGap
open Finset

variable {n : ℕ}

namespace BG

/-! ### Unions of atoms -/

section UnionAtoms

variable {𝒞 : Finset (Finset (Fin n))} {A : Finset (Fin n)}

/-- Membership in a union of atoms is containment of the atom. -/
theorem mem_iff_atomOf_subset (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A) (v : Fin n) :
    v ∈ A ↔ atomOf 𝒞 v ⊆ A := by
  constructor
  · intro hv
    rcases hAat _ (mem_atoms.mpr ⟨v, rfl⟩) with h | h
    · exact h
    · exact absurd hv (disjoint_left.mp h (mem_atomOf_self 𝒞 v))
  · intro h
    exact h (mem_atomOf_self 𝒞 v)

/-- The complement of a union of atoms is a union of atoms. -/
theorem compl_union_atoms (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A) :
    ∀ a ∈ atoms 𝒞, a ⊆ Aᶜ ∨ Disjoint a Aᶜ := by
  intro a ha
  rcases hAat a ha with h | h
  · exact Or.inr (disjoint_left.mpr fun x hx hx' => (mem_compl.mp hx') (h hx))
  · exact Or.inl (subset_compl_iff_disjoint_right.mpr h)

/-- An atom inside an atom is that atom. -/
theorem eq_of_atom_subset_atom {a b : Finset (Fin n)} (ha : a ∈ atoms 𝒞) (hb : b ∈ atoms 𝒞)
    (h : a ⊆ b) : a = b := by
  by_contra hne
  obtain ⟨v, hv⟩ := atoms_nonempty ha
  exact disjoint_left.mp (atoms_disjoint ha hb hne) hv (h hv)

/-- With at most one atom inside it, a nonempty union of atoms is a single atom. -/
theorem eq_atom_of_card_le_one (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A)
    (hne : A.Nonempty) (h1 : ((atoms 𝒞).filter (· ⊆ A)).card ≤ 1) :
    ∃ a ∈ atoms 𝒞, A = a := by
  obtain ⟨v, hv⟩ := hne
  refine ⟨atomOf 𝒞 v, mem_atoms.mpr ⟨v, rfl⟩, subset_antisymm ?_ ((mem_iff_atomOf_subset hAat v).mp hv)⟩
  intro w hw
  have hw' : atomOf 𝒞 w ∈ (atoms 𝒞).filter (· ⊆ A) :=
    mem_filter.mpr ⟨mem_atoms.mpr ⟨w, rfl⟩, (mem_iff_atomOf_subset hAat w).mp hw⟩
  have hv' : atomOf 𝒞 v ∈ (atoms 𝒞).filter (· ⊆ A) :=
    mem_filter.mpr ⟨mem_atoms.mpr ⟨v, rfl⟩, (mem_iff_atomOf_subset hAat v).mp hv⟩
  rw [← card_le_one.mp h1 _ hw' _ hv']
  exact mem_atomOf_self 𝒞 w

/-- With at most one atom outside it, a proper union of atoms is the complement of an
atom. -/
theorem compl_eq_atom_of_card_le_one (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A)
    (hne : A ≠ univ) (h1 : ((atoms 𝒞).filter fun a => Disjoint a A).card ≤ 1) :
    ∃ a ∈ atoms 𝒞, Aᶜ = a := by
  refine eq_atom_of_card_le_one (compl_union_atoms hAat) ?_ ?_
  · by_contra h
    rw [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at h
    exact hne h
  · refine le_trans (card_le_card ?_) h1
    intro a ha
    rw [mem_filter] at ha ⊢
    exact ⟨ha.1, subset_compl_iff_disjoint_right.mp ha.2⟩

/-- From more than one element, one differing from any given one. -/
theorem exists_mem_ne' {s : Finset (Finset (Fin n))} (h : 1 < s.card) (a : Finset (Fin n)) :
    ∃ b ∈ s, b ≠ a := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h
  by_cases hca : c = a
  · exact ⟨d, hd, fun hda => hcd (hca.trans hda.symm)⟩
  · exact ⟨c, hc, hca⟩

/-- **A union of atoms with two atoms on each side crosses a member** (the combinatorial
core of KKO22 Lemma 4.6): otherwise `{A}` and `𝒞` are separated families, Theorem 4.5 gives
an atom of each covering `V`, and each of the four cases loses an atom. -/
theorem exists_cross_of_union_atoms (hCne : 𝒞.Nonempty)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hproper : ∀ S ∈ 𝒞, S.Nonempty ∧ S ≠ univ) (hAne : A.Nonempty) (hAU : A ≠ univ)
    (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A)
    (hin : 1 < ((atoms 𝒞).filter (· ⊆ A)).card)
    (hout : 1 < ((atoms 𝒞).filter fun a => Disjoint a A).card) :
    ∃ S ∈ 𝒞, Crossing A S := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨p, q, hpq⟩ := exists_atomOf_union_atomOf_eq_univ hCne ⟨A, mem_singleton_self A⟩ hconn
    (fun D hD D' hD' => by
      rw [mem_singleton] at hD hD'
      subst hD; subst hD'
      exact .refl)
    hproper (fun C hC D hD => by
      rw [mem_singleton] at hD
      subst hD
      exact fun h => hcon C hC h.symm)
  have hq : atomOf {A} q = A ∨ atomOf {A} q = Aᶜ := by
    by_cases hqA : q ∈ A
    · left
      ext v
      simp [mem_atomOf, hqA]
    · right
      ext v
      simp [mem_atomOf, hqA]
  have hcov : ∀ v : Fin n, v ∈ atomOf 𝒞 p ∨ v ∈ atomOf {A} q := fun v =>
    mem_union.mp (hpq ▸ mem_univ v)
  have hp : atomOf 𝒞 p ∈ atoms 𝒞 := mem_atoms.mpr ⟨p, rfl⟩
  rcases hAat _ hp with h1 | h1 <;> rcases hq with h2 | h2
  · -- both inside `A`: `A = univ`
    refine hAU (eq_univ_iff_forall.mpr fun v => ?_)
    rcases hcov v with hv | hv
    · exact h1 hv
    · rwa [h2] at hv
  · -- `a ⊆ A`, `a' = Aᶜ`: another atom inside `A` escapes both
    obtain ⟨b, hb, hba⟩ := exists_mem_ne' hin (atomOf 𝒞 p)
    obtain ⟨hbmem, hbA⟩ := mem_filter.mp hb
    obtain ⟨v, hv⟩ := atoms_nonempty hbmem
    rcases hcov v with hva | hva
    · exact disjoint_left.mp (atoms_disjoint hbmem hp hba) hv hva
    · rw [h2] at hva
      exact (mem_compl.mp hva) (hbA hv)
  · -- `a` outside, `a' = A`: another atom outside `A` escapes both
    obtain ⟨b, hb, hba⟩ := exists_mem_ne' hout (atomOf 𝒞 p)
    obtain ⟨hbmem, hbA⟩ := mem_filter.mp hb
    obtain ⟨v, hv⟩ := atoms_nonempty hbmem
    rcases hcov v with hva | hva
    · exact disjoint_left.mp (atoms_disjoint hbmem hp hba) hv hva
    · rw [h2] at hva
      exact disjoint_left.mp hbA hv hva
  · -- both outside `A`: `A = ∅`
    obtain ⟨v, hv⟩ := hAne
    rcases hcov v with hva | hva
    · exact disjoint_left.mp h1 hva hv
    · rw [h2] at hva
      exact (mem_compl.mp hva) hv

end UnionAtoms

/-! ### Connectivity of augmented families -/

section Connectivity

variable {𝒞 𝒟 : Finset (Finset (Fin n))}

/-- Reversing a crossing path. -/
theorem reflTransGen_symm {S T : Finset (Fin n)}
    (h : Relation.ReflTransGen (fun A B => A ∈ 𝒟 ∧ B ∈ 𝒟 ∧ Crossing A B) S T) :
    Relation.ReflTransGen (fun A B => A ∈ 𝒟 ∧ B ∈ 𝒟 ∧ Crossing A B) T S := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

/-- A crossing path in a subfamily is one in the family. -/
theorem reflTransGen_mono (hsub : 𝒞 ⊆ 𝒟) {S T : Finset (Fin n)}
    (h : Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T) :
    Relation.ReflTransGen (fun A B => A ∈ 𝒟 ∧ B ∈ 𝒟 ∧ Crossing A B) S T := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨hsub hbc.1, hsub hbc.2.1, hbc.2.2⟩

/-- A family every member of which reaches a connected subfamily is connected. -/
theorem conn_of_reach (hsub : 𝒞 ⊆ 𝒟)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hreach : ∀ S ∈ 𝒟, ∃ S' ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒟 ∧ B ∈ 𝒟 ∧ Crossing A B) S S') :
    ∀ S ∈ 𝒟, ∀ T ∈ 𝒟,
      Relation.ReflTransGen (fun A B => A ∈ 𝒟 ∧ B ∈ 𝒟 ∧ Crossing A B) S T := by
  intro S hS T hT
  obtain ⟨S', hS', h1⟩ := hreach S hS
  obtain ⟨T', hT', h2⟩ := hreach T hT
  exact h1.trans ((reflTransGen_mono hsub (hconn S' hS' T' hT')).trans (reflTransGen_symm h2))

/-- Inserting a set crossing a member keeps the cross graph connected. -/
theorem conn_insert {A : Finset (Fin n)}
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hA : ∃ S ∈ 𝒞, Crossing A S) :
    ∀ S ∈ insert A 𝒞, ∀ T ∈ insert A 𝒞,
      Relation.ReflTransGen
        (fun A' B => A' ∈ insert A 𝒞 ∧ B ∈ insert A 𝒞 ∧ Crossing A' B) S T := by
  refine conn_of_reach (subset_insert A 𝒞) hconn fun S hS => ?_
  rcases mem_insert.mp hS with rfl | hS'
  · obtain ⟨S₀, hS₀, hc⟩ := hA
    exact ⟨S₀, hS₀, .single ⟨mem_insert_self _ _, mem_insert_of_mem hS₀, hc⟩⟩
  · exact ⟨S, hS', .refl⟩

/-- **The non-rooted BG family constructor**: the symmetric closure of a family, every
member of which crosses a member, with a connected cross graph, no 3-cycle and no comb in
the closure. -/
theorem isBGFamily_symmetrize_of_cross (hcross : ∀ S ∈ 𝒞, ∃ T ∈ 𝒞, Crossing S T)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hno3 : NoKCycle (symmetrize 𝒞) 3) (hnocomb : NoComb (symmetrize 𝒞)) :
    IsBGFamily (symmetrize 𝒞) where
  sym := fun _ hS => compl_mem_symmetrize hS
  conn := by
    refine conn_of_reach (subset_symmetrize 𝒞) hconn fun S hS => ?_
    rcases mem_symmetrize.mp hS with h | h
    · exact ⟨S, h, .refl⟩
    · obtain ⟨T, hT, hc⟩ := hcross _ h
      exact ⟨T, hT, .single ⟨hS, mem_symmetrize_of_mem hT, by simpa using hc.compl_left⟩⟩
  no3 := hno3
  nocomb := hnocomb
  nonempty := by
    intro S hS
    rcases mem_symmetrize.mp hS with h | h
    · obtain ⟨T, hT, hc⟩ := hcross _ h
      exact hc.1.mono inter_subset_left
    · obtain ⟨T, hT, hc⟩ := hcross _ h
      obtain ⟨w, hw, -⟩ := hc.exists_notMem
      exact ⟨w, by simpa using hw⟩

/-- The BG family of near-minimum cuts, `η < 2/5`, with its no-4-cycle certificate. -/
theorem isBGFamily_of_nearMin {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) {η : ℝ}
    (hη : η < 2 / 5) (hnm : ∀ S ∈ 𝒞, IsNearMinCut x η S)
    (hcross : ∀ S ∈ 𝒞, ∃ T ∈ 𝒞, Crossing S T)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T) :
    IsBGFamily (symmetrize 𝒞) ∧ NoKCycle (symmetrize 𝒞) 4 :=
  have hnm' : ∀ S ∈ symmetrize 𝒞, IsNearMinCut x η S :=
    fun _ hS => isNearMinCut_of_mem_symmetrize hnm hS
  ⟨isBGFamily_symmetrize_of_cross hcross hconn (noKCycle_of_nearMin hx hnm' hη.le (by norm_num))
    (noComb_of_nearMin hx hnm' hη), noKCycle_of_nearMin hx hnm' hη.le le_rfl⟩

end Connectivity

/-! ### Outside elements and the polygon -/

section Outside

variable {𝒞 𝒟 : Finset (Finset (Fin n))}

theorem symmetrize_mono (h : 𝒞 ⊆ 𝒟) : symmetrize 𝒞 ⊆ symmetrize 𝒟 := by
  intro S hS
  rcases mem_symmetrize.mp hS with h' | h'
  · exact mem_symmetrize_of_mem (h h')
  · exact mem_symmetrize.mpr (Or.inr (h h'))

/-- A cycle of a subfamily is a cycle of the family: inside elements stay inside. -/
theorem Inside.mono {F F' : Finset (Finset (Fin n))} (h : F ⊆ F') {v : Fin n}
    (hv : Inside F v) : Inside F' v :=
  let ⟨k, C, hC, hmem, hav⟩ := hv
  ⟨k, C, hC, fun i hi => h (hmem i hi), hav⟩

/-- An outside element's atom is one of the polygon's outside atoms. -/
theorem exists_out_eq_atomOf (P : PolygonRep 𝒞) {v : Fin n}
    (hv : ¬ Inside (symmetrize 𝒞) v) : ∃ i, P.out i = atomOf 𝒞 v := by
  have ha : atomOf 𝒞 v ∈ atoms 𝒞 := mem_atoms.mpr ⟨v, rfl⟩
  have ha' : atomOf 𝒞 v ∈ atoms (symmetrize 𝒞) := by rw [atoms_symmetrize]; exact ha
  have : atomOf 𝒞 v ∈ univ.image P.out := (P.outside_iff_no_avoiding_kCycle _ ha).mpr (by
    rw [hasAvoidingKCycle_iff_inside ha' (mem_atomOf_self 𝒞 v)]
    exact hv)
  obtain ⟨i, -, hi⟩ := mem_image.mp this
  exact ⟨i, hi⟩

/-- Membership of an outside element in a union of atoms, read off `P.outsideIn`. -/
theorem mem_iff_mem_outsideIn (P : PolygonRep 𝒞) {A : Finset (Fin n)}
    (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A) {v : Fin n} {i : Fin P.m}
    (hi : P.out i = atomOf 𝒞 v) : v ∈ A ↔ i ∈ P.outsideIn A := by
  rw [PolygonRep.mem_outsideIn, hi, mem_iff_atomOf_subset hAat]

/-- The trace of a single atom has at most one index. -/
theorem card_outsideIn_le_one (P : PolygonRep 𝒞) {a : Finset (Fin n)} (ha : a ∈ atoms 𝒞) :
    (P.outsideIn a).card ≤ 1 := by
  refine card_le_one.mpr fun i hi j hj => P.out_injective ?_
  rw [PolygonRep.mem_outsideIn] at hi hj
  rw [eq_of_atom_subset_atom (P.out_atom i) ha hi, eq_of_atom_subset_atom (P.out_atom j) ha hj]

/-- The trace of the complement of an atom misses at most one index. -/
theorem card_outsideIn_ge (P : PolygonRep 𝒞) {A : Finset (Fin n)}
    (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A) {a : Finset (Fin n)} (ha : a ∈ atoms 𝒞)
    (hAc : Aᶜ = a) : P.m - 1 ≤ (P.outsideIn A).card := by
  have h1 : (P.outsideIn A)ᶜ.card ≤ 1 := by
    refine card_le_one.mpr fun i hi j hj => P.out_injective ?_
    rw [mem_compl, PolygonRep.mem_outsideIn] at hi hj
    have key : ∀ k : Fin P.m, ¬ P.out k ⊆ A → P.out k = a := by
      intro k hk
      rcases hAat _ (P.out_atom k) with h | h
      · exact absurd h hk
      · exact eq_of_atom_subset_atom (P.out_atom k) ha
          (hAc ▸ subset_compl_iff_disjoint_right.mpr h)
    rw [key i hi, key j hj]
  rw [card_compl, Fintype.card_fin] at h1
  omega

end Outside

/-! ### Augmenting a rooted component -/

section Augment

variable {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n} {𝒞 : Finset (Finset (Fin n))}

/-- The BG family of a rooted component with one near-minimum union of atoms crossing a
member adjoined. -/
theorem isBGFamily_insert (hx : x ∈ subtourLP n) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hns : 2 ≤ 𝒞.card) {ε' : ℝ} (hε' : ε' < 2 / 5) (hηε : η ≤ ε') {A : Finset (Fin n)}
    (hA : IsNearMinCut x ε' A) (hAc : ∃ S ∈ 𝒞, Crossing A S) :
    IsBGFamily (symmetrize (insert A 𝒞)) ∧ NoKCycle (symmetrize (insert A 𝒞)) 4 := by
  refine isBGFamily_of_nearMin hx hε' ?_ ?_ (conn_insert hC.conn hAc)
  · intro S hS
    rcases mem_insert.mp hS with rfl | hS'
    · exact hA
    · exact (hC.nearMin S hS').mono hηε
  · intro S hS
    rcases mem_insert.mp hS with rfl | hS'
    · obtain ⟨T, hT, hc⟩ := hAc
      exact ⟨T, mem_insert_of_mem hT, hc⟩
    · obtain ⟨T, hT, hc⟩ := exists_cross hns hC.conn hS'
      exact ⟨T, mem_insert_of_mem hT, hc⟩

/-- The same with two sets adjoined. -/
theorem isBGFamily_insert₂ (hx : x ∈ subtourLP n) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hns : 2 ≤ 𝒞.card) {ε' : ℝ} (hε' : ε' < 2 / 5) (hηε : η ≤ ε') {A B : Finset (Fin n)}
    (hA : IsNearMinCut x ε' A) (hB : IsNearMinCut x ε' B) (hAc : ∃ S ∈ 𝒞, Crossing A S)
    (hBc : ∃ S ∈ 𝒞, Crossing B S) :
    IsBGFamily (symmetrize (insert A (insert B 𝒞))) ∧
      NoKCycle (symmetrize (insert A (insert B 𝒞))) 4 := by
  refine isBGFamily_of_nearMin hx hε' ?_ ?_ (conn_insert (conn_insert hC.conn hBc) ?_)
  · intro S hS
    rcases mem_insert.mp hS with rfl | hS'
    · exact hA
    rcases mem_insert.mp hS' with rfl | hS''
    · exact hB
    · exact (hC.nearMin S hS'').mono hηε
  · intro S hS
    rcases mem_insert.mp hS with rfl | hS'
    · obtain ⟨T, hT, hc⟩ := hAc
      exact ⟨T, mem_insert_of_mem (mem_insert_of_mem hT), hc⟩
    rcases mem_insert.mp hS' with rfl | hS''
    · obtain ⟨T, hT, hc⟩ := hBc
      exact ⟨T, mem_insert_of_mem (mem_insert_of_mem hT), hc⟩
    · obtain ⟨T, hT, hc⟩ := exists_cross hns hC.conn hS''
      exact ⟨T, mem_insert_of_mem (mem_insert_of_mem hT), hc⟩
  · obtain ⟨T, hT, hc⟩ := hAc
    exact ⟨T, mem_insert_of_mem hT, hc⟩

/-- A near-minimum union of atoms crossing a member of the component contains at least two
outside atoms and misses at least two: its trace has between `2` and `m - 2` indices. -/
theorem trace_bounds_of_cross (hx : x ∈ subtourLP n) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (P : PolygonRep 𝒞) {ε' : ℝ} (hε' : ε' < 2 / 5) (hηε : η ≤ ε') {A : Finset (Fin n)}
    (hA : IsNearMinCut x ε' A) (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A)
    (hAc : ∃ S ∈ 𝒞, Crossing A S) :
    2 ≤ (P.outsideIn A).card ∧ (P.outsideIn A).card ≤ P.m - 2 := by
  classical
  obtain ⟨hF, -⟩ := isBGFamily_insert hx hC P.nontrivial hε' hηε hA hAc
  obtain ⟨T, hT, hc⟩ := hAc
  have hsub : symmetrize 𝒞 ⊆ symmetrize (insert A 𝒞) := symmetrize_mono (subset_insert A 𝒞)
  obtain ⟨⟨v₁, h₁A, h₁T, h₁o⟩, ⟨v₂, h₂A, h₂T, h₂o⟩, ⟨v₃, h₃A, h₃T, h₃o⟩, ⟨v₄, h₄A, h₄T, h₄o⟩⟩ :=
    hF.outside_regions (mem_symmetrize_of_mem (mem_insert_self A 𝒞))
      (mem_symmetrize_of_mem (mem_insert_of_mem hT)) hc
  obtain ⟨i₁, e₁⟩ := exists_out_eq_atomOf P fun h => h₁o (h.mono hsub)
  obtain ⟨i₂, e₂⟩ := exists_out_eq_atomOf P fun h => h₂o (h.mono hsub)
  obtain ⟨i₃, e₃⟩ := exists_out_eq_atomOf P fun h => h₃o (h.mono hsub)
  obtain ⟨i₄, e₄⟩ := exists_out_eq_atomOf P fun h => h₄o (h.mono hsub)
  have hi₁ : i₁ ∈ P.outsideIn A := (mem_iff_mem_outsideIn P hAat e₁).mp h₁A
  have hi₂ : i₂ ∈ P.outsideIn A := (mem_iff_mem_outsideIn P hAat e₂).mp h₂A
  have hi₃ : i₃ ∉ P.outsideIn A := fun h => h₃A ((mem_iff_mem_outsideIn P hAat e₃).mpr h)
  have hi₄ : i₄ ∉ P.outsideIn A := fun h => h₄A ((mem_iff_mem_outsideIn P hAat e₄).mpr h)
  have h12 : i₁ ≠ i₂ := by
    intro e
    have hv : v₂ ∈ atomOf 𝒞 v₁ := by
      rw [← e₁, e, e₂]
      exact mem_atomOf_self 𝒞 v₂
    exact h₂T (atomOf_subset_of_mem hT h₁T hv)
  have h34 : i₃ ≠ i₄ := by
    intro e
    have hv : v₄ ∈ atomOf 𝒞 v₃ := by
      rw [← e₃, e, e₄]
      exact mem_atomOf_self 𝒞 v₄
    exact h₄T (atomOf_subset_of_mem hT h₃T hv)
  constructor
  · have hsub' : ({i₁, i₂} : Finset (Fin P.m)) ⊆ P.outsideIn A := by
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact hi₁
      · rw [mem_singleton.mp hi]
        exact hi₂
    have := card_le_card hsub'
    rwa [card_pair h12] at this
  · have hdisj : Disjoint (P.outsideIn A) {i₃, i₄} := by
      rw [disjoint_left]
      intro i hi hi'
      rcases mem_insert.mp hi' with rfl | hi'
      · exact hi₃ hi
      · rw [mem_singleton.mp hi'] at hi
        exact hi₄ hi
    have h1 := card_le_univ (P.outsideIn A ∪ {i₃, i₄})
    rw [card_union_eq_card_add_card.mpr hdisj, card_pair h34, Fintype.card_fin] at h1
    omega

end Augment

end BG

end TSPGap

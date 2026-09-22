/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerMatrices
import TSPGap.PolygonConfigurations

/-!
# From Tucker configurations to cycles and combs (BG08 Proposition 6, Corollary 7)

The polygon core reads a symmetric family `F` of cuts on its atoms: the row of `S ∈ F` is
the set of atoms inside `S` (`atomRow`), restricted to the outside atoms `O`; the pivot
normalization at `p ∈ O` (`CircularOnes.pivotFamily`) replaces the rows containing `p` by
the rows of the complements, so every pivot row is the atom row of a member of `F`
disjoint from `p` (`exists_of_mem_pivotFamily`).

BG08's proof of Proposition 6 then turns each Tucker configuration of the pivot family into
a forbidden structure of `F`:

* `M_IV` is a comb (handle: the transversal), `M_V` is a comb after complementing the
  four-element row — `noComb_of_config_MIV`, `noComb_of_config_MV`;
* the three-row instances of `M_I` and `M_III` are 3-cycles;
* the longer instances of `M_I`, `M_II`, `M_III` are *induced* cycles (after complementing
  the big rows), which BG08 Proposition 5 turns into cycles avoiding an outside atom.

This file has the setup, the comb lemmas and the 3-cycle lemmas; Proposition 5 and the
induced-cycle lemmas follow.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

namespace Tucker

/-- The atoms of `F` lying inside `S`. -/
def atomRow (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (atoms F).filter (· ⊆ S)

theorem mem_atomRow {F : Finset (Finset (Fin n))} {S a : Finset (Fin n)} :
    a ∈ atomRow F S ↔ a ∈ atoms F ∧ a ⊆ S := Finset.mem_filter

/-- The family `F` read on the atoms of `O`. -/
def rowsOn (F : Finset (Finset (Fin n))) (O : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Fin n))) :=
  F.image fun S => atomRow F S ∩ O

/-- An atom not inside a cut is disjoint from it. -/
theorem atom_disjoint_of_not_subset {F : Finset (Finset (Fin n))} {a S : Finset (Fin n)}
    (ha : a ∈ atoms F) (hS : S ∈ F) (h : ¬ a ⊆ S) : Disjoint a S :=
  (atom_subset_or_disjoint ha hS).resolve_left h

/-- An atom not inside a cut lies inside the complement. -/
theorem atom_subset_compl_of_not_subset {F : Finset (Finset (Fin n))} {a S : Finset (Fin n)}
    (ha : a ∈ atoms F) (hS : S ∈ F) (h : ¬ a ⊆ S) : a ⊆ Sᶜ :=
  Finset.subset_compl_iff_disjoint_right.mpr (atom_disjoint_of_not_subset ha hS h)

/-- An atom inside a cut is disjoint from the complement. -/
theorem atom_disjoint_compl_of_subset {a S : Finset (Fin n)} (h : a ⊆ S) : Disjoint a Sᶜ :=
  Finset.disjoint_left.mpr fun _ hx hx' => (Finset.mem_compl.mp hx') (h hx)

/-- An atom inside the complement is not inside the cut. -/
theorem not_subset_of_subset_compl {F : Finset (Finset (Fin n))} {a S : Finset (Fin n)}
    (ha : a ∈ atoms F) (h : a ⊆ Sᶜ) : ¬ a ⊆ S := fun h' =>
  (atoms_nonempty ha).ne_empty (Finset.eq_empty_of_forall_notMem fun _ hx =>
    (Finset.mem_compl.mp (h hx)) (h' hx))

section Pivot

variable {F : Finset (Finset (Fin n))} {O : Finset (Finset (Fin n))} {p : Finset (Fin n)}

/-- **A pivot row is the atom row of a member of `F` avoiding the pivot.** -/
theorem exists_of_mem_pivotFamily (hsym : ∀ S ∈ F, Sᶜ ∈ F) (hO : O ⊆ atoms F) (hp : p ∈ O)
    {R : Finset (Finset (Fin n))} (hR : R ∈ CircularOnes.pivotFamily O p (rowsOn F O)) :
    ∃ S ∈ F, Disjoint p S ∧ R = atomRow F S ∩ O.erase p := by
  obtain ⟨R₀, hR₀, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR₀
  by_cases hpS : p ⊆ S
  · refine ⟨Sᶜ, hsym S hS, atom_disjoint_compl_of_subset hpS, ?_⟩
    rw [CircularOnes.pivotRow_of_mem (Finset.mem_inter.mpr ⟨mem_atomRow.mpr ⟨hO hp, hpS⟩, hp⟩)]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_inter, mem_atomRow, Finset.mem_erase, not_and]
    constructor
    · rintro ⟨ha, hna⟩
      refine ⟨⟨hO ha, ?_⟩, ?_, ha⟩
      · exact atom_subset_compl_of_not_subset (hO ha) hS fun h => hna ⟨hO ha, h⟩ ha
      · rintro rfl
        exact hna ⟨hO hp, hpS⟩ hp
    · rintro ⟨⟨ha, hac⟩, hne, haO⟩
      exact ⟨haO, fun h _ => not_subset_of_subset_compl ha hac h.2⟩
  · refine ⟨S, hS, atom_disjoint_of_not_subset (hO hp) hS hpS, ?_⟩
    have hnot : p ∉ atomRow F S ∩ O := fun h => hpS (mem_atomRow.mp (Finset.mem_inter.mp h).1).2
    rw [CircularOnes.pivotRow_of_notMem hnot, Finset.inter_erase, Finset.erase_eq_of_notMem hnot]

/-- The rows and atoms of a configuration of the pivot family, as members of `F` avoiding
the pivot and distinct outside atoms other than the pivot. -/
theorem config_rows (hsym : ∀ S ∈ F, Sᶜ ∈ F) (hO : O ⊆ atoms F) (hp : p ∈ O) {r c : ℕ}
    {M : Pattern r c} (hcol : ∀ j, ∃ i, j ∈ M i)
    (h : HasConfig (CircularOnes.pivotFamily O p (rowsOn F O)) M) :
    ∃ (S : Fin r → Finset (Fin n)) (γ : Fin c → Finset (Fin n)),
      (∀ i, S i ∈ F) ∧ (∀ i, Disjoint p (S i)) ∧ Function.Injective γ ∧
        (∀ j, γ j ∈ O ∧ γ j ≠ p) ∧ ∀ i j, (γ j ⊆ S i ↔ j ∈ M i) := by
  obtain ⟨ρ, γ, hρ, hspec⟩ := h
  choose S hS hpS hρS using fun i => exists_of_mem_pivotFamily hsym hO hp (hρ i)
  have hγ : ∀ j, γ j ∈ O ∧ γ j ≠ p := fun j => by
    obtain ⟨i, hi⟩ := hcol j
    have := (hspec i j).mpr hi
    rw [hρS i, Finset.mem_inter, Finset.mem_erase] at this
    exact ⟨this.2.2, this.2.1⟩
  refine ⟨S, γ, hS, hpS, γ.injective, hγ, fun i j => ?_⟩
  rw [← hspec i j, hρS i, Finset.mem_inter, mem_atomRow, Finset.mem_erase]
  exact ⟨fun h => ⟨⟨hO (hγ j).1, h⟩, (hγ j).2, (hγ j).1⟩, fun h => h.1.2⟩

end Pivot

/-! ### The combs: `M_IV` and `M_V` -/

section Combs

variable {F : Finset (Finset (Fin n))}

/-- A cell of the first comb form containing an atom is nonempty. -/
theorem cell_nonempty_of_atom {H T₁ T₂ T₃ a : Finset (Fin n)} (ha : a ∈ atoms F)
    (h1 : a ⊆ H) (h2 : a ⊆ T₁) (h3 : Disjoint a T₃) (h4 : Disjoint a T₂) :
    ((H ∩ T₁) \ (T₃ ∪ T₂)).Nonempty :=
  (atoms_nonempty ha).mono (Finset.subset_sdiff.mpr
    ⟨Finset.subset_inter h1 h2, Finset.disjoint_union_right.mpr ⟨h3, h4⟩⟩)

/-- `M_IV`: three pairwise disjoint pairs and a transversal form a comb with the
transversal as handle. -/
theorem isComb_of_config_MIV {S : Fin 4 → Finset (Fin n)} {γ : Fin 6 → Finset (Fin n)}
    (hS : ∀ i, S i ∈ F) (hγ : ∀ j, γ j ∈ atoms F)
    (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MIV i)) : IsComb (S 3) (S 0) (S 1) (S 2) := by
  have sub : ∀ i j, j ∈ MIV i → γ j ⊆ S i := fun i j h => (hspec i j).mpr h
  have dis : ∀ i j, j ∉ MIV i → Disjoint (γ j) (S i) := fun i j h =>
    atom_disjoint_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  have subc : ∀ i j, j ∉ MIV i → γ j ⊆ (S i)ᶜ := fun i j h =>
    atom_subset_compl_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  have disc : ∀ i j, j ∈ MIV i → Disjoint (γ j) (S i)ᶜ := fun i j h =>
    atom_disjoint_compl_of_subset (sub i j h)
  refine ⟨⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩, ⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩⟩
  · exact cell_nonempty_of_atom (hγ 1) (sub 3 1 (by decide)) (sub 0 1 (by decide))
      (dis 2 1 (by decide)) (dis 1 1 (by decide))
  · exact cell_nonempty_of_atom (hγ 3) (sub 3 3 (by decide)) (sub 1 3 (by decide))
      (dis 0 3 (by decide)) (dis 2 3 (by decide))
  · exact cell_nonempty_of_atom (hγ 5) (sub 3 5 (by decide)) (sub 2 5 (by decide))
      (dis 1 5 (by decide)) (dis 0 5 (by decide))
  · exact cell_nonempty_of_atom (hγ 0) (subc 3 0 (by decide)) (sub 0 0 (by decide))
      (dis 2 0 (by decide)) (dis 1 0 (by decide))
  · exact cell_nonempty_of_atom (hγ 2) (subc 3 2 (by decide)) (sub 1 2 (by decide))
      (dis 0 2 (by decide)) (dis 2 2 (by decide))
  · exact cell_nonempty_of_atom (hγ 4) (subc 3 4 (by decide)) (sub 2 4 (by decide))
      (dis 1 4 (by decide)) (dis 0 4 (by decide))

/-- `M_V`: after complementing the four-element row, a comb with handle `{0,3,4}`, teeth
`{0,1}`, `{2,3}` and the complement; the pivot atom witnesses the last cell on the
complement side of the handle. -/
theorem isComb_of_config_MV {S : Fin 4 → Finset (Fin n)} {γ : Fin 5 → Finset (Fin n)}
    {p : Finset (Fin n)} (hS : ∀ i, S i ∈ F) (hγ : ∀ j, γ j ∈ atoms F) (hp : p ∈ atoms F)
    (hpS : ∀ i, Disjoint p (S i))
    (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MV i)) : IsComb (S 3) (S 0) (S 2) (S 1)ᶜ := by
  have sub : ∀ i j, j ∈ MV i → γ j ⊆ S i := fun i j h => (hspec i j).mpr h
  have dis : ∀ i j, j ∉ MV i → Disjoint (γ j) (S i) := fun i j h =>
    atom_disjoint_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  have subc : ∀ i j, j ∉ MV i → γ j ⊆ (S i)ᶜ := fun i j h =>
    atom_subset_compl_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  have disc : ∀ i j, j ∈ MV i → Disjoint (γ j) (S i)ᶜ := fun i j h =>
    atom_disjoint_compl_of_subset (sub i j h)
  refine ⟨⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩, ⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩⟩
  · exact cell_nonempty_of_atom (hγ 0) (sub 3 0 (by decide)) (sub 0 0 (by decide))
      (disc 1 0 (by decide)) (dis 2 0 (by decide))
  · exact cell_nonempty_of_atom (hγ 3) (sub 3 3 (by decide)) (sub 2 3 (by decide))
      (dis 0 3 (by decide)) (disc 1 3 (by decide))
  · exact cell_nonempty_of_atom (hγ 4) (sub 3 4 (by decide)) (subc 1 4 (by decide))
      (dis 2 4 (by decide)) (dis 0 4 (by decide))
  · exact cell_nonempty_of_atom (hγ 1) (subc 3 1 (by decide)) (sub 0 1 (by decide))
      (disc 1 1 (by decide)) (dis 2 1 (by decide))
  · exact cell_nonempty_of_atom (hγ 2) (subc 3 2 (by decide)) (sub 2 2 (by decide))
      (dis 0 2 (by decide)) (disc 1 2 (by decide))
  · exact cell_nonempty_of_atom hp
      (Finset.subset_compl_iff_disjoint_right.mpr (hpS 3))
      (Finset.subset_compl_iff_disjoint_right.mpr (hpS 1)) (hpS 2) (hpS 0)

end Combs

/-! ### The 3-cycles: `MI 0` and `MIII 0` -/

section ThreeCycles

variable {F : Finset (Finset (Fin n))}

/-- A 3-cycle cell containing an atom is nonempty. -/
theorem cell3_nonempty_of_atom {A B C a : Finset (Fin n)} (ha : a ∈ atoms F) (h1 : a ⊆ A)
    (h2 : a ⊆ B) (h3 : Disjoint a C) : ((A ∩ B) \ C).Nonempty :=
  (atoms_nonempty ha).mono (Finset.subset_sdiff.mpr ⟨Finset.subset_inter h1 h2, h3⟩)

/-- A vertex of an atom disjoint from three sets keeps their union from being everything. -/
theorem union3_ne_univ_of_atom {A B C a : Finset (Fin n)} (ha : a ∈ atoms F) (h1 : Disjoint a A)
    (h2 : Disjoint a B) (h3 : Disjoint a C) : A ∪ B ∪ C ≠ Finset.univ := by
  obtain ⟨v, hv⟩ := atoms_nonempty ha
  intro h
  have := Finset.mem_univ v
  rw [← h, Finset.mem_union, Finset.mem_union] at this
  rcases this with (h | h) | h
  · exact Finset.disjoint_left.mp h1 hv h
  · exact Finset.disjoint_left.mp h2 hv h
  · exact Finset.disjoint_left.mp h3 hv h

/-- **BG08 Definition 1** from the three cells and the union condition. -/
theorem isThreeCycle_of_cells {A B C : Finset (Fin n)} (hAB : ((A ∩ B) \ C).Nonempty)
    (hBC : ((B ∩ C) \ A).Nonempty) (hCA : ((C ∩ A) \ B).Nonempty)
    (hU : A ∪ B ∪ C ≠ Finset.univ) : IsThreeCycle A B C := by
  have hsd : ∀ {X Y Z : Finset (Fin n)}, ((X ∩ Y) \ Z).Nonempty → (X ∩ Y).Nonempty :=
    fun h => h.mono Finset.sdiff_subset
  have hdiff : ∀ {X Y Z : Finset (Fin n)}, ((X ∩ Y) \ Z).Nonempty → (Y \ Z).Nonempty :=
    fun h => h.mono (Finset.sdiff_subset_sdiff Finset.inter_subset_right le_rfl)
  have hdiff' : ∀ {X Y Z : Finset (Fin n)}, ((X ∩ Y) \ Z).Nonempty → (X \ Z).Nonempty :=
    fun h => h.mono (Finset.sdiff_subset_sdiff Finset.inter_subset_left le_rfl)
  have hns : ∀ {X Y Z : Finset (Fin n)}, ((X ∩ Y) \ Z).Nonempty → ¬ (X ∩ Y ⊆ Z) := by
    rintro X Y Z ⟨x, hx⟩ hsub
    rw [Finset.mem_sdiff] at hx
    exact hx.2 (hsub hx.1)
  have hu2 : ∀ {X Y Z : Finset (Fin n)}, X ∪ Y ∪ Z ≠ Finset.univ → X ∪ Y ≠ Finset.univ :=
    fun h h' => h (Finset.univ_subset_iff.mp (h' ▸ Finset.subset_union_left))
  refine ⟨⟨hsd hAB, hdiff hCA, hdiff' hBC, hu2 hU⟩, ⟨hsd hBC, hdiff hAB, hdiff' hCA, ?_⟩,
    ⟨hsd hCA, hdiff hBC, hdiff' hAB, ?_⟩, hU, hns hAB, hns hBC, hns hCA⟩
  · exact hu2 (X := B) (Y := C) (Z := A) (by rwa [Finset.union_right_comm, Finset.union_comm B A])
  · exact hu2 (X := C) (Y := A) (Z := B) (by rwa [Finset.union_comm C A, Finset.union_right_comm])

/-- A 3-cycle of members of `F` contradicts `NoKCycle F 3`. -/
theorem NoKCycle.three {A B C : Finset (Fin n)} (h : NoKCycle F 3) (hA : A ∈ F) (hB : B ∈ F)
    (hC : C ∈ F) (hcyc : IsThreeCycle A B C) : False := by
  refine h (cyc3 A B C) hcyc.isKCycle fun i hi => ?_
  interval_cases i <;> simp [cyc3, hA, hB, hC]

/-- `MI 0`: the three rows form a 3-cycle. -/
theorem isThreeCycle_of_config_MI0 {S : Fin 3 → Finset (Fin n)} {γ : Fin 3 → Finset (Fin n)}
    {p : Finset (Fin n)} (hS : ∀ i, S i ∈ F) (hγ : ∀ j, γ j ∈ atoms F) (hp : p ∈ atoms F)
    (hpS : ∀ i, Disjoint p (S i)) (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MI 0 i)) :
    IsThreeCycle (S 0) (S 1) (S 2) := by
  have sub : ∀ i j, j ∈ MI 0 i → γ j ⊆ S i := fun i j h => (hspec i j).mpr h
  have dis : ∀ i j, j ∉ MI 0 i → Disjoint (γ j) (S i) := fun i j h =>
    atom_disjoint_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  refine isThreeCycle_of_cells ?_ ?_ ?_ (union3_ne_univ_of_atom hp (hpS 0) (hpS 1) (hpS 2))
  · exact cell3_nonempty_of_atom (hγ 1) (sub 0 1 (by decide)) (sub 1 1 (by decide))
      (dis 2 1 (by decide))
  · exact cell3_nonempty_of_atom (hγ 2) (sub 1 2 (by decide)) (sub 2 2 (by decide))
      (dis 0 2 (by decide))
  · exact cell3_nonempty_of_atom (hγ 0) (sub 2 0 (by decide)) (sub 0 0 (by decide))
      (dis 1 0 (by decide))

/-- `MIII 0`: the two pairs and the complement of the claw's centre row form a 3-cycle; the
private atom of the centre row lies outside the union. -/
theorem isThreeCycle_of_config_MIII0 {S : Fin 3 → Finset (Fin n)} {γ : Fin 4 → Finset (Fin n)}
    (hS : ∀ i, S i ∈ F) (hγ : ∀ j, γ j ∈ atoms F)
    (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MIII 0 i)) : IsThreeCycle (S 0) (S 1) (S 2)ᶜ := by
  have sub : ∀ i j, j ∈ MIII 0 i → γ j ⊆ S i := fun i j h => (hspec i j).mpr h
  have dis : ∀ i j, j ∉ MIII 0 i → Disjoint (γ j) (S i) := fun i j h =>
    atom_disjoint_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  have subc : ∀ i j, j ∉ MIII 0 i → γ j ⊆ (S i)ᶜ := fun i j h =>
    atom_subset_compl_of_not_subset (hγ j) (hS i) fun h' => h ((hspec i j).mp h')
  have disc : ∀ i j, j ∈ MIII 0 i → Disjoint (γ j) (S i)ᶜ := fun i j h =>
    atom_disjoint_compl_of_subset (sub i j h)
  refine isThreeCycle_of_cells ?_ ?_ ?_
    (union3_ne_univ_of_atom (hγ 3) (dis 0 3 (by decide)) (dis 1 3 (by decide))
      (disc 2 3 (by decide)))
  · exact cell3_nonempty_of_atom (hγ 1) (sub 0 1 (by decide)) (sub 1 1 (by decide))
      (disc 2 1 (by decide))
  · exact cell3_nonempty_of_atom (hγ 2) (sub 1 2 (by decide)) (subc 2 2 (by decide))
      (dis 0 2 (by decide))
  · exact cell3_nonempty_of_atom (hγ 0) (subc 2 0 (by decide)) (sub 0 0 (by decide))
      (dis 1 0 (by decide))

end ThreeCycles

end Tucker

end TSPGap

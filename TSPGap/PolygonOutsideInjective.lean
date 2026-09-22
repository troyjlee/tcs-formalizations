/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGAugmentedFamily

/-!
# KKO22 Lemma 4.23: a near-minimum union of atoms is determined by its outside atoms

`eq_of_outsideIn_eq`, formerly a black box in `TSPGap/BlackBoxes.lean`: within a rooted
crossing component `𝒞` with polygon `P`, two near-minimum cuts that are unions of atoms of
`𝒞`, have the same nonempty set of outside atoms and are both avoided by some atom coincide.

KKO prove it by contracting the atoms; here (`audits/qa/q17`) the component is augmented
instead.  A union of atoms with two atoms on each side crosses a member
(`exists_cross_of_union_atoms`), so `symmetrize (insert A (insert B 𝒞))` is a BG family
of cuts of value `< 12/5` and BG08 Proposition 20 (`eq_of_same_trace`) applies: equal traces
on the outside atoms of `𝒞` are equal traces on the (fewer) outside elements of the augmented
family.  The degenerate shapes — a single atom, or the complement of one — are excluded by
counting: a member crossing something has between `2` and `m - 2` outside atoms
(`trace_bounds_of_cross`), a single atom at most one, and a co-atom at least `m - 1`.
-/

namespace TSPGap
open Finset BG

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η ε : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

/-- **KKO22 Lemma 4.23.**  Within a component `𝒞` with polygon `P`, two `ε`-near minimum
cuts (`ε < 2/5`) that are unions of atoms of `𝒞`, have the *same nonempty* set of outside
atoms, and are both avoided by some atom, coincide. -/
theorem eq_of_outsideIn_eq (hx : x ∈ subtourLP n) (hη : η < 2 / 5) (hε : ε < 2 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (P : PolygonRep 𝒞)
    {A B : Finset (Fin n)} (hA : IsNearMinCut x ε A) (hB : IsNearMinCut x ε B)
    (hAat : ∀ a ∈ atoms 𝒞, a ⊆ A ∨ Disjoint a A)
    (hBat : ∀ a ∈ atoms 𝒞, a ⊆ B ∨ Disjoint a B)
    (hout : P.outsideIn A = P.outsideIn B) (hne : (P.outsideIn A).Nonempty)
    (hroot : ∃ a ∈ atoms 𝒞, Disjoint a A ∧ Disjoint a B) : A = B := by
  classical
  have hε' : max η ε < 2 / 5 := max_lt hη hε
  have hηε : η ≤ max η ε := le_max_left _ _
  have hA' : IsNearMinCut x (max η ε) A := hA.mono (le_max_right _ _)
  have hB' : IsNearMinCut x (max η ε) B := hB.mono (le_max_right _ _)
  have hm := P.hm
  have hproper : ∀ S ∈ 𝒞, S.Nonempty ∧ S ≠ univ := fun S hS =>
    ⟨(hC.nearMin S hS).nonempty, (hC.nearMin S hS).ne_univ⟩
  have cross_of : ∀ X : Finset (Fin n), IsNearMinCut x (max η ε) X →
      (∀ a ∈ atoms 𝒞, a ⊆ X ∨ Disjoint a X) → 1 < ((atoms 𝒞).filter (· ⊆ X)).card →
      1 < ((atoms 𝒞).filter fun a => Disjoint a X).card → ∃ S ∈ 𝒞, Crossing X S :=
    fun X hX hXat hin hout' => exists_cross_of_union_atoms hC.nonempty hC.conn hproper
      hX.nonempty hX.ne_univ hXat hin hout'
  have hcB : (P.outsideIn B).card = (P.outsideIn A).card := by rw [hout]
  by_cases hA2 : 1 < ((atoms 𝒞).filter (· ⊆ A)).card ∧
      1 < ((atoms 𝒞).filter fun a => Disjoint a A).card
  · by_cases hB2 : 1 < ((atoms 𝒞).filter (· ⊆ B)).card ∧
        1 < ((atoms 𝒞).filter fun a => Disjoint a B).card
    · -- the main case: both cross a member, and Proposition 20 applies in the augmented family
      obtain ⟨hF, h4⟩ := isBGFamily_insert₂ hx hC P.nontrivial hε' hηε hA' hB'
        (cross_of A hA' hAat hA2.1 hA2.2) (cross_of B hB' hBat hB2.1 hB2.2)
      have hsub : symmetrize 𝒞 ⊆ symmetrize (insert A (insert B 𝒞)) :=
        symmetrize_mono fun S hS => mem_insert_of_mem (mem_insert_of_mem hS)
      refine hF.eq_of_same_trace h4 (mem_symmetrize_of_mem (mem_insert_self _ _))
        (mem_symmetrize_of_mem (mem_insert_of_mem (mem_insert_self _ _))) fun v hv => ?_
      obtain ⟨i, hi⟩ := exists_out_eq_atomOf P fun h => hv (h.mono hsub)
      rw [mem_iff_mem_outsideIn P hAat hi, mem_iff_mem_outsideIn P hBat hi, hout]
    · -- `A` crosses a member, `B` is an atom or a co-atom: the traces cannot agree
      exfalso
      obtain ⟨h1, h2⟩ := trace_bounds_of_cross hx hC P hε' hηε hA' hAat
        (cross_of A hA' hAat hA2.1 hA2.2)
      rw [not_and_or, not_lt, not_lt] at hB2
      rcases hB2 with hB2 | hB2
      · obtain ⟨b, hb, hBb⟩ := eq_atom_of_card_le_one hBat hB.nonempty hB2
        have := card_outsideIn_le_one P hb
        rw [← hBb] at this
        omega
      · obtain ⟨b, hb, hBb⟩ := compl_eq_atom_of_card_le_one hBat hB.ne_univ hB2
        have := card_outsideIn_ge P hBat hb hBb
        omega
  · rw [not_and_or, not_lt, not_lt] at hA2
    by_cases hB2 : 1 < ((atoms 𝒞).filter (· ⊆ B)).card ∧
        1 < ((atoms 𝒞).filter fun a => Disjoint a B).card
    · -- `B` crosses a member, `A` is an atom or a co-atom
      exfalso
      obtain ⟨h1, h2⟩ := trace_bounds_of_cross hx hC P hε' hηε hB' hBat
        (cross_of B hB' hBat hB2.1 hB2.2)
      rcases hA2 with hA2 | hA2
      · obtain ⟨a, ha, hAa⟩ := eq_atom_of_card_le_one hAat hA.nonempty hA2
        have := card_outsideIn_le_one P ha
        rw [← hAa] at this
        omega
      · obtain ⟨a, ha, hAa⟩ := compl_eq_atom_of_card_le_one hAat hA.ne_univ hA2
        have := card_outsideIn_ge P hAat ha hAa
        omega
    · -- neither crosses a member
      rw [not_and_or, not_lt, not_lt] at hB2
      rcases hA2 with hA2 | hA2 <;> rcases hB2 with hB2 | hB2
      · -- two atoms with a common outside atom inside: the same atom
        obtain ⟨a, ha, hAa⟩ := eq_atom_of_card_le_one hAat hA.nonempty hA2
        obtain ⟨b, hb, hBb⟩ := eq_atom_of_card_le_one hBat hB.nonempty hB2
        obtain ⟨i, hi⟩ := hne
        have hiB : i ∈ P.outsideIn B := hout ▸ hi
        rw [PolygonRep.mem_outsideIn] at hi hiB
        have ea : P.out i = a := eq_of_atom_subset_atom (P.out_atom i) ha (by rw [← hAa]; exact hi)
        have eb : P.out i = b := eq_of_atom_subset_atom (P.out_atom i) hb (by rw [← hBb]; exact hiB)
        rw [hAa, hBb, ← ea, ← eb]
      · -- an atom against a co-atom: at most one index against at least `m - 1`
        exfalso
        obtain ⟨a, ha, hAa⟩ := eq_atom_of_card_le_one hAat hA.nonempty hA2
        obtain ⟨b, hb, hBb⟩ := compl_eq_atom_of_card_le_one hBat hB.ne_univ hB2
        have h1 := card_outsideIn_le_one P ha
        have h2 := card_outsideIn_ge P hBat hb hBb
        rw [← hAa] at h1
        omega
      · exfalso
        obtain ⟨a, ha, hAa⟩ := compl_eq_atom_of_card_le_one hAat hA.ne_univ hA2
        obtain ⟨b, hb, hBb⟩ := eq_atom_of_card_le_one hBat hB.nonempty hB2
        have h1 := card_outsideIn_ge P hAat ha hAa
        have h2 := card_outsideIn_le_one P hb
        rw [← hBb] at h2
        omega
      · -- two co-atoms both missing the common avoided atom: the same co-atom
        obtain ⟨a, ha, hAa⟩ := compl_eq_atom_of_card_le_one hAat hA.ne_univ hA2
        obtain ⟨b, hb, hBb⟩ := compl_eq_atom_of_card_le_one hBat hB.ne_univ hB2
        obtain ⟨r₀, hr₀, hrA, hrB⟩ := hroot
        have e1 : r₀ = a := eq_of_atom_subset_atom hr₀ ha
          (hAa ▸ subset_compl_iff_disjoint_right.mpr hrA)
        have e2 : r₀ = b := eq_of_atom_subset_atom hr₀ hb
          (hBb ▸ subset_compl_iff_disjoint_right.mpr hrB)
        rw [← compl_compl A, ← compl_compl B, hAa, hBb, ← e1, ← e2]

end TSPGap

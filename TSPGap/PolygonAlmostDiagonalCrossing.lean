/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGAugmentedFamily

/-!
# KKO22 Fact 4.26: crossing almost diagonal cuts have crossing arcs

`cross_arc_of_almostDiagonal`, formerly a black box in `TSPGap/BlackBoxes.lean`: for
`η < 1/5`, two crossing almost diagonal cuts of a rooted crossing component have crossing
arcs of outside atoms.

KKO derive it from Lemma 4.24 by contraction; here (`audits/qa/q17`) the four regions of the
crossing pair give two atoms on each side of each cut, so both cross a member of the
component (`exists_cross_of_union_atoms`), the augmented family
`symmetrize (insert A (insert B 𝒞))` is a BG family of `2η`-near minimum cuts, and BG08
Corollary 14 four times (`outside_regions`) puts an outside element — outside for `𝒞` as
well — in each of the four regions; their atoms are indices in the four regions of the arcs.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

namespace BG

/-- Two elements of `X`, one in `Y` and one not, lie in two atoms inside `X`. -/
theorem one_lt_card_filter_subset {X Y : Finset (Fin n)}
    (hXat : ∀ a ∈ atoms 𝒞, a ⊆ X ∨ Disjoint a X) (hYat : ∀ a ∈ atoms 𝒞, a ⊆ Y ∨ Disjoint a Y)
    {u w : Fin n} (huX : u ∈ X) (hwX : w ∈ X) (huY : u ∈ Y) (hwY : w ∉ Y) :
    1 < ((atoms 𝒞).filter (· ⊆ X)).card := by
  refine one_lt_card.mpr ⟨atomOf 𝒞 u,
    mem_filter.mpr ⟨mem_atoms.mpr ⟨u, rfl⟩, (mem_iff_atomOf_subset hXat u).mp huX⟩, atomOf 𝒞 w,
    mem_filter.mpr ⟨mem_atoms.mpr ⟨w, rfl⟩, (mem_iff_atomOf_subset hXat w).mp hwX⟩, ?_⟩
  intro e
  have hw : w ∈ atomOf 𝒞 u := by
    rw [e]
    exact mem_atomOf_self 𝒞 w
  exact hwY ((mem_iff_atomOf_subset hYat u).mp huY hw)

/-- Two elements outside `X`, one in `Y` and one not, lie in two atoms outside `X`. -/
theorem one_lt_card_filter_disjoint {X Y : Finset (Fin n)}
    (hXat : ∀ a ∈ atoms 𝒞, a ⊆ X ∨ Disjoint a X) (hYat : ∀ a ∈ atoms 𝒞, a ⊆ Y ∨ Disjoint a Y)
    {u w : Fin n} (huX : u ∉ X) (hwX : w ∉ X) (huY : u ∈ Y) (hwY : w ∉ Y) :
    1 < ((atoms 𝒞).filter fun a => Disjoint a X).card := by
  have := one_lt_card_filter_subset (compl_union_atoms hXat) hYat (mem_compl.mpr huX)
    (mem_compl.mpr hwX) huY hwY
  convert this using 2
  ext a
  simp only [mem_filter]
  rw [subset_compl_iff_disjoint_right]

end BG

open BG

/-- **KKO22 Fact 4.26**, first part: crossing almost diagonal cuts have crossing arcs. -/
theorem cross_arc_of_almostDiagonal (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 5)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (P : PolygonRep 𝒞) {A B : Finset (Fin n)} {a b : Fin P.m} {la lb : ℕ}
    (hA : P.IsAlmostDiagonal x η A) (hB : P.IsAlmostDiagonal x η B)
    (harcA : P.IsArcOf A a la) (harcB : P.IsArcOf B b lb)
    (hcross : Crossing A B) :
    Crossing (arcSet a la) (arcSet b lb) := by
  classical
  have hε' : 2 * η < 2 / 5 := by linarith
  have hηε : η ≤ 2 * η := by linarith
  have hproper : ∀ S ∈ 𝒞, S.Nonempty ∧ S ≠ univ := fun S hS =>
    ⟨(hC.nearMin S hS).nonempty, (hC.nearMin S hS).ne_univ⟩
  obtain ⟨v₁, hv₁⟩ := hcross.1
  obtain ⟨v₂, hv₂⟩ := hcross.2.1
  obtain ⟨v₃, hv₃⟩ := hcross.2.2.1
  obtain ⟨v₄, hv₄A, hv₄B⟩ := hcross.exists_notMem
  rw [mem_inter] at hv₁
  rw [mem_sdiff] at hv₂ hv₃
  have hAc : ∃ S ∈ 𝒞, Crossing A S :=
    exists_cross_of_union_atoms hC.nonempty hC.conn hproper hA.nearMin.nonempty
      hA.nearMin.ne_univ hA.unionOfAtoms
      (one_lt_card_filter_subset hA.unionOfAtoms hB.unionOfAtoms hv₁.1 hv₂.1 hv₁.2 hv₂.2)
      (one_lt_card_filter_disjoint hA.unionOfAtoms hB.unionOfAtoms hv₃.2 hv₄A hv₃.1 hv₄B)
  have hBc : ∃ S ∈ 𝒞, Crossing B S :=
    exists_cross_of_union_atoms hC.nonempty hC.conn hproper hB.nearMin.nonempty
      hB.nearMin.ne_univ hB.unionOfAtoms
      (one_lt_card_filter_subset hB.unionOfAtoms hA.unionOfAtoms hv₁.2 hv₃.1 hv₁.1 hv₃.2)
      (one_lt_card_filter_disjoint hB.unionOfAtoms hA.unionOfAtoms hv₂.2 hv₄B hv₂.1 hv₄A)
  obtain ⟨hF, -⟩ := isBGFamily_insert₂ hx hC P.nontrivial hε' hηε hA.nearMin hB.nearMin hAc hBc
  have hsub : symmetrize 𝒞 ⊆ symmetrize (insert A (insert B 𝒞)) :=
    symmetrize_mono fun S hS => mem_insert_of_mem (mem_insert_of_mem hS)
  obtain ⟨⟨w₁, h₁A, h₁B, h₁o⟩, ⟨w₂, h₂A, h₂B, h₂o⟩, ⟨w₃, h₃A, h₃B, h₃o⟩, ⟨w₄, h₄A, h₄B, h₄o⟩⟩ :=
    hF.outside_regions (mem_symmetrize_of_mem (mem_insert_self _ _))
      (mem_symmetrize_of_mem (mem_insert_of_mem (mem_insert_self _ _))) hcross
  obtain ⟨i₁, e₁⟩ := exists_out_eq_atomOf P fun h => h₁o (h.mono hsub)
  obtain ⟨i₂, e₂⟩ := exists_out_eq_atomOf P fun h => h₂o (h.mono hsub)
  obtain ⟨i₃, e₃⟩ := exists_out_eq_atomOf P fun h => h₃o (h.mono hsub)
  obtain ⟨i₄, e₄⟩ := exists_out_eq_atomOf P fun h => h₄o (h.mono hsub)
  rw [← harcA.1, ← harcB.1]
  exact crossing_of_witnesses ((mem_iff_mem_outsideIn P hA.unionOfAtoms e₁).mp h₁A)
    ((mem_iff_mem_outsideIn P hB.unionOfAtoms e₁).mp h₁B)
    ((mem_iff_mem_outsideIn P hA.unionOfAtoms e₂).mp h₂A)
    (fun h => h₂B ((mem_iff_mem_outsideIn P hB.unionOfAtoms e₂).mpr h))
    ((mem_iff_mem_outsideIn P hB.unionOfAtoms e₃).mp h₃B)
    (fun h => h₃A ((mem_iff_mem_outsideIn P hA.unionOfAtoms e₃).mpr h))
    (fun h => h₄A ((mem_iff_mem_outsideIn P hA.unionOfAtoms e₄).mpr h))
    (fun h => h₄B ((mem_iff_mem_outsideIn P hB.unionOfAtoms e₄).mpr h))

end TSPGap

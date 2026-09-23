/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedHappyEvents
import TSPGap.PolygonEvent

/-!
# The piece degree partition against the polygon partition

KKO21 Remark 5.20: at a polygon cut `u` with polygon partition `A, B, C`
(Definition 4.20, from the near-cycle presenting `u`), the degree partition
`A', B', C'` of `δ(u)` (Definition 5.18) satisfies `A' ⊆ A`, `B' ⊆ B`,
`C ⊆ C'`, "by Definition 4.31" — the leftmost and rightmost atoms `a₁`,
`a_{m−1}` of the polygon are hierarchy cuts strictly inside `u` whose outward
edges are exactly `A` and `B`, each of mass `≥ 1 − ε_η`, so they are the
qualifying descendants the degree partition is built on.

On pieces the statement is the **inclusion form**, never an equality of
projected sides:

`(P.A ⊆ pieces over A ∧ P.B ⊆ pieces over B) ∨ (P.A ⊆ pieces over B ∧
P.B ⊆ pieces over A)`, and `pieces over C ⊆ P.C`

(`DegreePartitionOn.PolygonCompatible`).  It is a **theorem** of the
descendant clause `ControlsDescendants` at the two boundary atoms
(`polygonCompatible_of_controls`), the orientation being fixed by the masses
of the two sides.  Its two consequences are what §7.2 consumes:

* 2-1-1 happiness on pieces w.r.t. `P` makes the polygon `u` happy on the
  projected tree (`PolygonCompatible.happy_of_twoOneOneHappyOn`) — the pieces
  over `A` are among `P.A ∪ P.C`, so exactly one is present, likewise `B`,
  and none over `C`;
* a wrong-side mass bound stated on the piece sides transfers to the polygon
  sides with the honest loss `w(P.C) ≤ 2ε₁ + ε_η`
  (`PolygonCompatible.sum_inter_side_le`), in the orientation the
  compatibility fixes.

⚠️ This is the compatibility of the *degree* partition with the polygon
partition at one cut; it is distinct from `NearCycle.PartitionCompatible`,
the presentation compatibility up to reversal that `MainPaymentCore` takes.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-! ### The boundary atoms of a near-cycle -/

namespace NearCycle

variable (N : NearCycle x εη)

theorem lastIdx_add_one : N.lastIdx + 1 = 0 := by
  rw [Fin.ext_iff, Fin.val_add, NearCycle.lastIdx, Fin.val_last, Fin.val_zero]
  show (N.k + 2 + (1 : Fin (N.k + 3)).val) % (N.k + 3) = 0
  rw [Fin.val_one]
  exact Nat.mod_self _

theorem zero_ne_lastIdx : (0 : Fin (N.k + 3)) ≠ N.lastIdx := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_zero, NearCycle.lastIdx, Fin.val_last] at this
  omega

theorem one_ne_lastIdx : (1 : Fin (N.k + 3)) ≠ N.lastIdx := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_one, NearCycle.lastIdx, Fin.val_last] at this
  omega

/-- `A = E(a₀, a₁)`. -/
theorem partA_eq : N.partA = betweenEdges (N.atom 0) (N.atom 1) := rfl

/-- `B = E(a_{m−1}, a₀)`. -/
theorem partB_eq : N.partB = betweenEdges (N.atom N.lastIdx) (N.atom 0) := by
  unfold NearCycle.partB NearCycle.group
  rw [N.lastIdx_add_one]

end NearCycle

/-! ### The boundary atoms are qualifying descendants -/

namespace Hierarchy

variable {H : Hierarchy x e₀ εη} {N : NearCycle x εη} {u : Finset (Fin n)}

/-- The presented cut's edges are the root atom's. -/
theorem Presents.cutEdges_root_eq (hN : H.Presents N u) : cutEdges N.root = cutEdges u := by
  rw [hN.1, cutEdges_compl]

/-- The outward edges of the leftmost atom `a₁` are `A`. -/
theorem Presents.cutEdges_inter_eq_partA (hN : H.Presents N u) :
    cutEdges (N.atom 1) ∩ cutEdges u = N.partA := by
  have h1 : IsChildOf H.cuts (N.atom 1) u := hN.atom_isChildOf Fin.zero_lt_one.ne'
  rw [EdgeRefinement.cutEdges_inter_cutEdges_of_subset h1.2.2.1.subset, ← hN.1, N.partA_eq,
    betweenEdges_comm]
  rfl

/-- The outward edges of the rightmost atom `a_{m−1}` are `B`. -/
theorem Presents.cutEdges_inter_eq_partB (hN : H.Presents N u) :
    cutEdges (N.atom N.lastIdx) ∩ cutEdges u = N.partB := by
  have h1 : IsChildOf H.cuts (N.atom N.lastIdx) u :=
    hN.atom_isChildOf (Ne.symm N.zero_ne_lastIdx)
  rw [EdgeRefinement.cutEdges_inter_cutEdges_of_subset h1.2.2.1.subset, ← hN.1, N.partB_eq]
  rfl

end Hierarchy

namespace EdgeRefinement

variable {R : EdgeRefinement x Dr ε₁}

/-! ### The compatibility -/

/-- **The degree/polygon compatibility, in inclusion form**: each piece side lies
over one polygon side, and every piece over `C` is a piece of `P.C`. -/
def DegreePartitionOn.PolygonCompatible {u : Finset (Fin n)} (P : R.DegreePartitionOn εη u)
    (N : NearCycle x εη) : Prop :=
  ((P.A ⊆ R.piecesOver N.partA ∧ P.B ⊆ R.piecesOver N.partB)
      ∨ (P.A ⊆ R.piecesOver N.partB ∧ P.B ⊆ R.piecesOver N.partA))
    ∧ R.piecesOver N.partC ⊆ P.C

/-- A side of positive mass is not contained in the pieces over two disjoint edge sets. -/
theorem not_subset_both {X : Finset R.Piece} {c : ℝ} (hc : 0 < c)
    (hX : c ≤ ∑ q ∈ X, R.weight q) {F G : Finset (Sym2 (Fin n))} (hFG : Disjoint F G)
    (hF : X ⊆ R.piecesOver F) (hG : X ⊆ R.piecesOver G) : False := by
  have hempty : X = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    exact Finset.disjoint_left.mp hFG (R.mem_piecesOver.mp (hF hq)) (R.mem_piecesOver.mp (hG hq))
  rw [hempty, Finset.sum_empty] at hX
  linarith

/-- **Remark 5.20 on pieces**: the descendant clause at the two boundary atoms
of the presenting near-cycle gives the compatibility. -/
theorem DegreePartitionOn.polygonCompatible_of_controls {H : Hierarchy x e₀ εη}
    {u : Finset (Fin n)} (P : R.DegreePartitionOn εη u) (hctrl : P.ControlsDescendants H)
    {N : NearCycle x εη} (hN : H.Presents N u) (hx : ∀ e, 0 ≤ x e)
    (hεη₁ : εη ≤ ε₁) (hε₁1 : ε₁ < 1) : P.PolygonCompatible N := by
  classical
  have hA1 : IsChildOf H.cuts (N.atom 1) u := hN.atom_isChildOf Fin.zero_lt_one.ne'
  have hB1 : IsChildOf H.cuts (N.atom N.lastIdx) u :=
    hN.atom_isChildOf (Ne.symm N.zero_ne_lastIdx)
  have hAmass : 1 - ε₁ ≤ ∑ g ∈ cutEdges (N.atom 1) ∩ cutEdges u, x g := by
    rw [hN.cutEdges_inter_eq_partA]
    have := N.one_sub_le_group_mass 0
    unfold NearCycle.partA
    linarith
  have hBmass : 1 - ε₁ ≤ ∑ g ∈ cutEdges (N.atom N.lastIdx) ∩ cutEdges u, x g := by
    rw [hN.cutEdges_inter_eq_partB]
    have := N.one_sub_le_group_mass N.lastIdx
    unfold NearCycle.partB
    linarith
  have hcA := hctrl (N.atom 1) hA1.1 hA1.2.2.1 hAmass
  have hcB := hctrl (N.atom N.lastIdx) hB1.1 hB1.2.2.1 hBmass
  rw [hN.cutEdges_inter_eq_partA] at hcA
  rw [hN.cutEdges_inter_eq_partB] at hcB
  have hdisj := N.partA_disjoint_partB
  have hc0 : (0 : ℝ) < 1 - ε₁ := by linarith
  -- the orientation
  have horient : (P.A ⊆ R.piecesOver N.partA ∧ P.B ⊆ R.piecesOver N.partB)
      ∨ (P.A ⊆ R.piecesOver N.partB ∧ P.B ⊆ R.piecesOver N.partA) := by
    rcases hcA with ⟨hAA, -⟩ | ⟨hBA, -⟩ <;> rcases hcB with ⟨hAB, -⟩ | ⟨hBB, -⟩
    · exact (not_subset_both hc0 P.xA1 hdisj hAA hAB).elim
    · exact Or.inl ⟨hAA, hBB⟩
    · exact Or.inr ⟨hAB, hBA⟩
    · exact (not_subset_both hc0 P.xB1 hdisj.symm hBB hBA).elim
  refine ⟨horient, fun q hq => ?_⟩
  -- a piece over `C` lies over `δ(u)` and over neither side
  have hqC : R.base q ∈ N.partC := R.mem_piecesOver.mp hq
  have hqcut : q ∈ R.piecesOver (cutEdges u) := by
    rw [R.mem_piecesOver, ← hN.cutEdges_root_eq]
    exact Finset.mem_sdiff.mp hqC |>.1
  have hnotAB : R.base q ∉ N.partA ∪ N.partB := (Finset.mem_sdiff.mp hqC).2
  rw [P.part] at hqcut
  rcases Finset.mem_union.mp hqcut with hAB | hC
  · exfalso
    rcases Finset.mem_union.mp hAB with hA | hB
    · rcases horient with ⟨h, -⟩ | ⟨h, -⟩
      · exact hnotAB (Finset.mem_union_left _ (R.mem_piecesOver.mp (h hA)))
      · exact hnotAB (Finset.mem_union_right _ (R.mem_piecesOver.mp (h hA)))
    · rcases horient with ⟨-, h⟩ | ⟨-, h⟩
      · exact hnotAB (Finset.mem_union_right _ (R.mem_piecesOver.mp (h hB)))
      · exact hnotAB (Finset.mem_union_left _ (R.mem_piecesOver.mp (h hB)))
  · exact hC

/-! ### Consequence 1: 2-1-1 happiness on pieces makes the polygon happy -/

/-- The 2-1-1 event is symmetric in the two sides. -/
theorem TwoOneOneHappyOn.swap {u u' : Finset (Fin n)} {A B C Ť : Finset R.Piece}
    (h : R.TwoOneOneHappyOn u u' A B C Ť) : R.TwoOneOneHappyOn u u' B A C Ť :=
  ⟨h.2.1, h.1, h.2.2⟩

/-- On a transversal, exactly one piece lies over a polygon side whose pieces
are among `X ∪ C` and contain `X`, when `X` holds one piece and `C` none. -/
theorem card_project_inter_eq_one {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    {Y : Finset (Sym2 (Fin n))} {X X' C : Finset R.Piece}
    (hcov : R.piecesOver Y ⊆ (X ∪ X') ∪ C) (hX : X ⊆ R.piecesOver Y)
    (hX' : Disjoint X' (R.piecesOver Y))
    (h1 : (Ť ∩ X).card = 1) (h0 : (Ť ∩ C).card = 0) :
    (R.project Ť ∩ Y).card = 1 := by
  rw [← R.card_inter_piecesOver_of_transversal htr]
  have hle : Ť ∩ R.piecesOver Y ⊆ (Ť ∩ X) ∪ (Ť ∩ C) := by
    intro q hq
    obtain ⟨hqT, hqY⟩ := Finset.mem_inter.mp hq
    rcases Finset.mem_union.mp (hcov hqY) with hXX | hC
    · rcases Finset.mem_union.mp hXX with hX1 | hX2
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hqT, hX1⟩)
      · exact absurd hqY (Finset.disjoint_left.mp hX' hX2)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hqT, hC⟩)
  have hup : (Ť ∩ R.piecesOver Y).card ≤ 1 := by
    calc (Ť ∩ R.piecesOver Y).card ≤ ((Ť ∩ X) ∪ (Ť ∩ C)).card := Finset.card_le_card hle
      _ ≤ (Ť ∩ X).card + (Ť ∩ C).card := Finset.card_union_le _ _
      _ = 1 := by rw [h1, h0]
  have hlow : 1 ≤ (Ť ∩ R.piecesOver Y).card := by
    rw [← h1]
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl Ť) hX)
  omega

/-- The one-orientation core: `P.A` over `A`, `P.B` over `B`. -/
theorem happy_of_twoOneOneHappyOn_aux {u u' : Finset (Fin n)} (N : NearCycle x εη)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hcut : cutEdges N.root = cutEdges u)
    (hA : A ⊆ R.piecesOver N.partA) (hB : B ⊆ R.piecesOver N.partB)
    (hC : R.piecesOver N.partC ⊆ C)
    {Ť : Finset R.Piece} (htr : R.IsTransversal Ť) (h : R.TwoOneOneHappyOn u u' A B C Ť) :
    N.Happy (R.project Ť) := by
  classical
  have hdisj := N.partA_disjoint_partB
  have hcovA : R.piecesOver N.partA ⊆ (A ∪ B) ∪ C := by
    rw [← hpart, ← hcut]; exact R.piecesOver_mono N.partA_subset_cutEdges_root
  have hcovB : R.piecesOver N.partB ⊆ (B ∪ A) ∪ C := by
    rw [Finset.union_comm B A, ← hpart, ← hcut]
    exact R.piecesOver_mono N.partB_subset_cutEdges_root
  have hBA : Disjoint B (R.piecesOver N.partA) := by
    refine Finset.disjoint_of_subset_left hB ?_
    rw [← R.model_fiberOver, ← R.model_fiberOver]
    exact R.model.disjoint_fiberOver hdisj.symm
  have hAB : Disjoint A (R.piecesOver N.partB) := by
    refine Finset.disjoint_of_subset_left hA ?_
    rw [← R.model_fiberOver, ← R.model_fiberOver]
    exact R.model.disjoint_fiberOver hdisj
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.inter_comm, card_project_inter_eq_one htr hcovA hA hBA h.1 h.2.2.1]
    decide
  · rw [Finset.inter_comm, card_project_inter_eq_one htr hcovB hB hAB h.2.1 h.2.2.1]
    decide
  · rw [Finset.inter_comm, ← Finset.card_eq_zero, ← R.card_inter_piecesOver_of_transversal htr]
    have hle : Ť ∩ R.piecesOver N.partC ⊆ Ť ∩ C :=
      Finset.inter_subset_inter (Finset.Subset.refl Ť) hC
    have := Finset.card_le_card hle
    rw [h.2.2.1] at this
    omega

/-- **KKO21 Remark 5.20's consequence on pieces**: a tree 2-1-1 happy w.r.t. the
piece degree partition makes the polygon happy on the projection. -/
theorem DegreePartitionOn.PolygonCompatible.happy_of_twoOneOneHappyOn {H : Hierarchy x e₀ εη}
    {u u' : Finset (Fin n)} {P : R.DegreePartitionOn εη u} {N : NearCycle x εη}
    (hc : P.PolygonCompatible N) (hN : H.Presents N u)
    {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (h : R.TwoOneOneHappyOn u u' P.A P.B P.C Ť) : N.Happy (R.project Ť) := by
  rcases hc with ⟨⟨hA, hB⟩ | ⟨hA, hB⟩, hC⟩
  · exact happy_of_twoOneOneHappyOn_aux N P.part hN.cutEdges_root_eq hA hB hC htr h
  · exact happy_of_twoOneOneHappyOn_aux N (by rw [P.part, Finset.union_comm P.A P.B])
      hN.cutEdges_root_eq hB hA hC htr h.swap

/-! ### Consequence 2: wrong-side masses transfer to the polygon sides -/

/-- The one-orientation core: a bound on the pieces of a bundle in the side `X`
lying over `Y` bounds the bundle's mass on `Y`, up to `w(C)`. -/
theorem sum_inter_le_of_piece_side {u : Finset (Fin n)} (hx : ∀ e, 0 ≤ x e)
    {X X' C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (X ∪ X') ∪ C)
    {Y Y' : Finset (Sym2 (Fin n))} (hYcut : Y ⊆ cutEdges u) (hYY' : Disjoint Y Y')
    (hX' : X' ⊆ R.piecesOver Y')
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ edgeFinset n) {c : ℝ}
    (hc : ∑ q ∈ R.piecesOver E ∩ X, R.weight q ≤ c) :
    ∑ g ∈ E ∩ Y, x g ≤ c + ∑ q ∈ C, R.weight q := by
  classical
  have hwnn : ∀ q, 0 ≤ R.weight q := R.weight_nonneg hx
  rw [← R.sum_piecesOver (Finset.inter_subset_left.trans hE)]
  have hsub : R.piecesOver (E ∩ Y) ⊆ (R.piecesOver E ∩ X) ∪ C := by
    intro q hq
    have hqEY := R.mem_piecesOver.mp hq
    have hqE : q ∈ R.piecesOver E := R.mem_piecesOver.mpr (Finset.mem_inter.mp hqEY).1
    have hqY : R.base q ∈ Y := (Finset.mem_inter.mp hqEY).2
    have hqcut : q ∈ R.piecesOver (cutEdges u) := R.mem_piecesOver.mpr (hYcut hqY)
    rw [hpart] at hqcut
    rcases Finset.mem_union.mp hqcut with hXX | hC
    · rcases Finset.mem_union.mp hXX with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hqE, h1⟩)
      · exact absurd hqY (Finset.disjoint_left.mp hYY'.symm (R.mem_piecesOver.mp (hX' h2)))
    · exact Finset.mem_union_right _ hC
  calc ∑ q ∈ R.piecesOver (E ∩ Y), R.weight q
      ≤ ∑ q ∈ (R.piecesOver E ∩ X) ∪ C, R.weight q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hwnn q
    _ ≤ (∑ q ∈ R.piecesOver E ∩ X, R.weight q) + ∑ q ∈ C, R.weight q := by
        have h := Finset.sum_union_inter (s₁ := R.piecesOver E ∩ X) (s₂ := C) (f := R.weight)
        have h0 : 0 ≤ ∑ q ∈ (R.piecesOver E ∩ X) ∩ C, R.weight q :=
          Finset.sum_nonneg fun q _ => hwnn q
        linarith
    _ ≤ c + ∑ q ∈ C, R.weight q := by linarith

/-- **The wrong-side masses of case (iii) transfer to the polygon partition**, in
the orientation the compatibility fixes, with the loss `w(P.C) ≤ 2ε₁ + ε_η`:
the bounds `w(e(P.B)) ≤ c`, `w(f(P.A)) ≤ c'` on the piece sides give
`x(e ∩ B), x(f ∩ A) ≤ c + 2ε₁ + ε_η` (resp. with `A`, `B` exchanged). -/
theorem DegreePartitionOn.PolygonCompatible.sum_inter_side_le {H : Hierarchy x e₀ εη}
    {u : Finset (Fin n)} {P : R.DegreePartitionOn εη u} {N : NearCycle x εη}
    (hc : P.PolygonCompatible N) (hN : H.Presents N u) (hx : ∀ e, 0 ≤ x e)
    {E F : Finset (Sym2 (Fin n))} (hE : E ⊆ edgeFinset n) (hF : F ⊆ edgeFinset n) {c c' : ℝ}
    (hcB : ∑ q ∈ R.piecesOver E ∩ P.B, R.weight q ≤ c)
    (hcA : ∑ q ∈ R.piecesOver F ∩ P.A, R.weight q ≤ c') :
    ((∑ g ∈ E ∩ N.partB, x g ≤ c + (2 * ε₁ + εη)
        ∧ ∑ g ∈ F ∩ N.partA, x g ≤ c' + (2 * ε₁ + εη))
      ∨ (∑ g ∈ E ∩ N.partA, x g ≤ c + (2 * ε₁ + εη)
        ∧ ∑ g ∈ F ∩ N.partB, x g ≤ c' + (2 * ε₁ + εη))) := by
  have hCw := P.xC
  have hAcut : N.partA ⊆ cutEdges u := hN.cutEdges_root_eq ▸ N.partA_subset_cutEdges_root
  have hBcut : N.partB ⊆ cutEdges u := hN.cutEdges_root_eq ▸ N.partB_subset_cutEdges_root
  have hdisj := N.partA_disjoint_partB
  rcases hc with ⟨⟨hA, hB⟩ | ⟨hA, hB⟩, -⟩
  · left
    constructor
    · have := sum_inter_le_of_piece_side hx (X := P.B) (X' := P.A) (C := P.C)
        (by rw [P.part, Finset.union_comm P.A P.B]) hBcut hdisj.symm hA hE hcB
      linarith
    · have := sum_inter_le_of_piece_side hx (X := P.A) (X' := P.B) (C := P.C) P.part
        hAcut hdisj hB hF hcA
      linarith
  · right
    constructor
    · have := sum_inter_le_of_piece_side hx (X := P.B) (X' := P.A) (C := P.C)
        (by rw [P.part, Finset.union_comm P.A P.B]) hAcut hdisj hA hE hcB
      linarith
    · have := sum_inter_le_of_piece_side hx (X := P.A) (X' := P.B) (C := P.C) P.part
        hBcut hdisj.symm hB hF hcA
      linarith

end EdgeRefinement

end TSPGap

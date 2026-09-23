/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BadCount
import TSPGap.PolygonFamily
import TSPGap.SubtreeProbability

/-!
# The global bad-event index (KKO22 Theorem 5.2's event family)

Theorem 5.2's proof quantifies over the bad events `B→(p)`, `B←(p)` of all
polygons at once.  This file defines that family.

**Identity versus payload.**  The design invariant, which the per-polygon
count of four (`card_badEvents_le_four_of_polygon`) depends on: an event's
*identity* is exactly the triple (polygon, polygon point, direction) —
`BadEventIndex` has no other fields — while the witness cuts `L(p)`/`R(p)`,
their `S_L`/`S_R`, and the star are stored in one shared **chosen payload**
(`PolygonRep.rightWitness` / `leftWitness`), fixed once by choice and looked
up by every reference to the event.  Storing witnesses in the index instead
would let alternate maximizers create duplicate events at one point and
direction, breaking the count.

**Activity.**  KKO's events exist only at points carrying an `L(p)` (resp.
`R(p)`).  Rather than filtering the index, inactive events are *harmless*:
their payload defaults to `∅`s, so they charge no edges
(`Ebad_eq_empty_of_not_active`), and their occurrence predicate conjoins
activity, so they never occur.  Every Theorem 5.2 hypothesis about them
holds trivially.
-/

namespace TSPGap

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
variable {𝒞 : Finset (Finset (Fin n))}

/-- The witness tuple of a bad event: the anchor cut (`L(p)` for a right
event, `R(p)` for a left one), its two Definition 4.17 crossers, and the
chosen star. -/
structure EventWitness (n : ℕ) where
  /-- The anchor cut: `L(p)` (right events) or `R(p)` (left events). -/
  cut : Finset (Fin n)
  /-- Its `S_L`. -/
  cutL : Finset (Fin n)
  /-- Its `S_R`. -/
  cutR : Finset (Fin n)
  /-- The chosen `L*` (right events) or `R*` (left events). -/
  star : Finset (Fin n)

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- A right event is active at `p` when `L(p)` exists. -/
def RightActive (p : Fin P.m) : Prop := ∃ L, P.IsLp p L

/-- A left event is active at `p` when `R(p)` exists. -/
def LeftActive (p : Fin P.m) : Prop := ∃ R, P.IsRp p R

/-- At an active point the full right-event witness tuple exists: `L(p)`
comes with the activity, its crossers from `CrossedOnBothSides` through
Definition 4.17, and the chosen star unconditionally. -/
theorem exists_rightWitness {p : Fin P.m} (h : P.RightActive p) :
    ∃ w : EventWitness n, P.IsLp p w.cut ∧ P.IsSL w.cut w.cutL ∧
      P.IsSR w.cut w.cutR ∧
      P.IsChosenLStar (w.cut ∩ w.cutR) (P.start w.cutR) w.star := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨LL, hLL⟩ := P.exists_isSL hL.2.2.1.1
  obtain ⟨LR, hLR⟩ := P.exists_isSR hL.2.2.1.2
  obtain ⟨Ls, hLs⟩ := P.exists_isChosenLStar (L ∩ LR) (P.start LR)
  exact ⟨⟨L, LL, LR, Ls⟩, hL, hLL, hLR, hLs⟩

/-- The mirror at an active left point. -/
theorem exists_leftWitness {p : Fin P.m} (h : P.LeftActive p) :
    ∃ w : EventWitness n, P.IsRp p w.cut ∧ P.IsSL w.cut w.cutL ∧
      P.IsSR w.cut w.cutR ∧
      P.IsChosenRStar (w.cut ∩ w.cutL) (P.start w.cut)
        (P.len w.cutL - (P.start w.cut - P.start w.cutL).val) w.star := by
  obtain ⟨R, hR⟩ := h
  obtain ⟨RL, hRL⟩ := P.exists_isSL hR.2.2.1.1
  obtain ⟨RR, hRR⟩ := P.exists_isSR hR.2.2.1.2
  obtain ⟨Rs, hRs⟩ := P.exists_isChosenRStar (R ∩ RL) (P.start R)
    (P.len RL - (P.start R - P.start RL).val)
  exact ⟨⟨R, RL, RR, Rs⟩, hR, hRL, hRR, hRs⟩

open Classical in
/-- **The chosen right payload** at `p`: one witness tuple, fixed once and
shared by every reference to the event; junk `∅`s at inactive points. -/
noncomputable def rightWitness (p : Fin P.m) : EventWitness n :=
  if h : P.RightActive p then (P.exists_rightWitness h).choose
  else ⟨∅, ∅, ∅, ∅⟩

open Classical in
/-- **The chosen left payload** — the mirror. -/
noncomputable def leftWitness (p : Fin P.m) : EventWitness n :=
  if h : P.LeftActive p then (P.exists_leftWitness h).choose
  else ⟨∅, ∅, ∅, ∅⟩

theorem rightWitness_spec {p : Fin P.m} (h : P.RightActive p) :
    P.IsLp p (P.rightWitness p).cut ∧
      P.IsSL (P.rightWitness p).cut (P.rightWitness p).cutL ∧
      P.IsSR (P.rightWitness p).cut (P.rightWitness p).cutR ∧
      P.IsChosenLStar ((P.rightWitness p).cut ∩ (P.rightWitness p).cutR)
        (P.start (P.rightWitness p).cutR) (P.rightWitness p).star := by
  simp only [rightWitness, dif_pos h]
  exact (P.exists_rightWitness h).choose_spec

theorem leftWitness_spec {p : Fin P.m} (h : P.LeftActive p) :
    P.IsRp p (P.leftWitness p).cut ∧
      P.IsSL (P.leftWitness p).cut (P.leftWitness p).cutL ∧
      P.IsSR (P.leftWitness p).cut (P.leftWitness p).cutR ∧
      P.IsChosenRStar ((P.leftWitness p).cut ∩ (P.leftWitness p).cutL)
        (P.start (P.leftWitness p).cut)
        (P.len (P.leftWitness p).cutL
          - (P.start (P.leftWitness p).cut
              - P.start (P.leftWitness p).cutL).val)
        (P.leftWitness p).star := by
  simp only [leftWitness, dif_pos h]
  exact (P.exists_leftWitness h).choose_spec

theorem rightWitness_of_not_active {p : Fin P.m} (h : ¬ P.RightActive p) :
    P.rightWitness p = ⟨∅, ∅, ∅, ∅⟩ := by
  simp only [rightWitness, dif_neg h]

theorem leftWitness_of_not_active {p : Fin P.m} (h : ¬ P.LeftActive p) :
    P.leftWitness p = ⟨∅, ∅, ∅, ∅⟩ := by
  simp only [leftWitness, dif_neg h]

/-- **The separation core of `hcharge`.**  A vertex of a cut and a vertex of
another cut lying outside the first inhabit different atoms, and neither
atom is the root — the root atom meets no cut of the component. -/
theorem atomOf_ne_of_charged (P : PolygonRep 𝒞) {S T : Finset (Fin n)}
    (hS : S ∈ 𝒞) (hT : T ∈ 𝒞) {a b : Fin n}
    (haS : a ∈ S) (hbT : b ∈ T) (hbS : b ∉ S) :
    atomOf 𝒞 a ≠ atomOf 𝒞 b ∧ atomOf 𝒞 a ≠ P.rootAtom ∧
      atomOf 𝒞 b ≠ P.rootAtom := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hb' : b ∈ atomOf 𝒞 a := h ▸ mem_atomOf_self 𝒞 b
    exact hbS ((mem_atomOf.mp hb' S hS).mp haS)
  · have ha' : a ∈ P.rootAtom := h ▸ mem_atomOf_self 𝒞 a
    exact Finset.disjoint_left.mp (P.rootAtom_disjoint S hS) ha' haS
  · have hb' : b ∈ P.rootAtom := h ▸ mem_atomOf_self 𝒞 b
    exact Finset.disjoint_left.mp (P.rootAtom_disjoint T hT) hb' hbT

end PolygonRep

/-- With empty data nothing is charged: the inner side of the bad-edge set
is empty. -/
theorem badEdgesRight_empty : badEdgesRight (∅ : Finset (Fin n)) ∅ ∅ = ∅ := by
  ext e
  simp [badEdgesRight, PolygonRep.mem_betweenEdges_iff]

/-- The mirror. -/
theorem badEdgesLeft_empty : badEdgesLeft (∅ : Finset (Fin n)) ∅ ∅ = ∅ := by
  ext e
  simp [badEdgesLeft, PolygonRep.mem_betweenEdges_iff]

/-! ### Star geometry for Lemma 5.6

KKO's proof of Lemma 5.6 is a one-line disjoint-union display,

  `(L^∩R ∖ L*) ⊎ (L_R ∖ L) = L_R ∖ L*`,

prefaced by "observe that `L*(p)` crosses `L(p)_R`".  Two facts are doing
silent work there: the crossing itself (which uncrossing needs to make
`L_R ∖ L*` a `2η`-near min cut), and `L* ∩ L_R ⊆ L` — without which the
right-to-left inclusion of the display is false.  Both are proved here,
in both orientations, together with the disjoint-union lemma in the
generality the genuine `L*` needs (`Disjoint Z (Y ∖ X)` in place of the
old `Z ⊆ X`, which held only for `L* = ∅`).

These are §5.3 geometry and belong with it in `InsideAtoms.lean`; they
are developed here to keep build iterations cheap, and can move in a
cleanup pass. -/

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **`L* ∩ L_R ⊆ L`** — the silent inclusion in Lemma 5.6's display.

If `L* ⊆ L` there is nothing to prove.  Otherwise `L*` crosses `L`, and
the side decides: crossing on the left, Lemma 4.27 against the
right-crosser `L_R` keeps `L* ∖ L` and `L_R ∖ L` apart, which is the
claim; crossing on the right is impossible, since `L*`'s arc would start
left of `L_R`'s (side exclusivity at the almost diagonal `L^∩R`) and end
inside `L`'s (the arcs of `L*` and `L^∩R` cross), nesting it inside `L`'s
arc against Observation 4.4. -/
theorem star_inter_isSR_subset (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {L LR W : Finset (Fin n)} (hL : L ∈ 𝒞) (hLR : LR ∈ 𝒞) (hW : W ∈ 𝒞)
    (hcr : P.CrossesOnRight LR L)
    (hcW : P.CrossesOnLeftArc W (L ∩ LR) (P.start LR)) :
    W ∩ LR ⊆ L := by
  classical
  by_cases hsub : W ⊆ L
  · exact fun v hv => hsub (Finset.mem_inter.mp hv).1
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_inter hx hη0 hC hL hLR hcr
  have hcrossWU : Crossing W (L ∩ LR) := hcW.1
  have hcross : Crossing W L := by
    obtain ⟨a, ha⟩ := hcrossWU.1
    obtain ⟨w, hw⟩ := hcrossWU.2.2.1
    rw [Finset.mem_inter] at ha
    rw [Finset.mem_sdiff] at hw
    obtain ⟨v, hv, hv'⟩ := Finset.not_subset.mp hsub
    exact ⟨⟨a, Finset.mem_inter.mpr ⟨ha.1, (Finset.mem_inter.mp ha.2).1⟩⟩,
      ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩,
      ⟨w, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hw.1).1, hw.2⟩⟩,
      P.union_ne_univ hW hL⟩
  rcases P.crossesOnLeft_or_crossesOnRight hW hL hcross with hleft | hright
  · have hdisj := P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
      (by linarith) hC hL hW hLR hleft hcr
    intro v hv
    rw [Finset.mem_inter] at hv
    by_contra hvL
    exact Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mpr ⟨hv.1, hvL⟩)
      (Finset.mem_sdiff.mpr ⟨hv.2, hvL⟩)
  · exfalso
    have hWU : P.start W ∉ arcSet (P.start LR)
        (P.len L - (P.start LR - P.start L).val) := fun h =>
      P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 (by linarith)
        hC hUad hUarc hW ⟨hcW, hcrossWU, h⟩
    have harcs := cross_arc_of_almostDiagonal hx hη0 (by linarith) hC P
      (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hW) hUad
      (P.isArcOf_of_mem hW) hUarc hcrossWU
    obtain ⟨j, hj⟩ := harcs.2.2.1
    rw [Finset.mem_sdiff] at hj
    have hm := P.hm
    have hmL := P.len_le L hL
    have hdR : (P.start LR - P.start L).val < P.len L := mem_arcSet.mp hcr.2
    have hdW : (P.start W - P.start L).val < P.len L := mem_arcSet.mp hright.2
    have hWnotU := mem_arcSet_compl.mp hWU
    have hUW : (P.start LR - P.start W).val < P.len W := mem_arcSet.mp hcW.2
    -- `start W` lies strictly left of `start LR` in `L`'s arc
    rcases lt_or_ge (P.start W - P.start L).val (P.start LR - P.start L).val
      with hlt | hge
    · have hjU := mem_arcSet.mp hj.1
      have hjW := mem_arcSet_compl.mp hj.2
      have hjL : (j - P.start L).val
          = (j - P.start LR).val + (P.start LR - P.start L).val := by
        have hrel := val_sub_rel j (P.start L) (P.start LR)
        rw [Nat.mod_eq_of_lt (by omega)] at hrel
        exact hrel
      have hjWval : (j - P.start W).val
          = (j - P.start L).val - (P.start W - P.start L).val :=
        val_sub_of_le (s := P.start L) (α := P.start W) (β := j) (by omega)
      have harcsub : arcSet (P.start W) (P.len W)
          ⊆ arcSet (P.start L) (P.len L) := arcSet_subset (by omega) (by omega)
      exact (P.not_crossing_of_arc_subset hL hW harcsub) hcross.symm
    · have := val_sub_of_le (s := P.start L) (α := P.start LR)
        (β := P.start W) hge
      omega

/-- **`L*` crosses `L_R`** — KKO's "observe".  The shared vertex and the
missing part of `L^∩R` come from `L*` crossing `L^∩R`; the vertex of `L*`
outside `L_R` is its leftmost atom, whose index precedes `start L_R`
because `L*` starts outside `L^∩R`'s arc yet cannot start in `L_R`'s tail
without wrapping the polygon (`union_arc_lt`). -/
theorem star_crossing_isSR (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {L LR W : Finset (Fin n)} (hL : L ∈ 𝒞) (hLR : LR ∈ 𝒞) (hW : W ∈ 𝒞)
    (hcr : P.CrossesOnRight LR L)
    (hcW : P.CrossesOnLeftArc W (L ∩ LR) (P.start LR)) :
    Crossing W LR := by
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_inter hx hη0 hC hL hLR hcr
  have hcrossWU : Crossing W (L ∩ LR) := hcW.1
  refine ⟨?_, ?_, ?_, P.union_ne_univ hW hLR⟩
  · obtain ⟨a, ha⟩ := hcrossWU.1
    rw [Finset.mem_inter] at ha
    exact ⟨a, Finset.mem_inter.mpr ⟨ha.1, (Finset.mem_inter.mp ha.2).2⟩⟩
  · -- the leftmost atom of `W` lies outside `L_R`
    have hWU : P.start W ∉ arcSet (P.start LR)
        (P.len L - (P.start LR - P.start L).val) := fun h =>
      P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 (by linarith)
        hC hUad hUarc hW ⟨hcW, hcrossWU, h⟩
    have hm := P.hm
    have hmL := P.len_le L hL
    have hdR : (P.start LR - P.start L).val < P.len L := mem_arcSet.mp hcr.2
    have hUW : (P.start LR - P.start W).val < P.len W := mem_arcSet.mp hcW.2
    have hWnotU := mem_arcSet_compl.mp hWU
    have hWLR : P.start W ∉ arcSet (P.start LR) (P.len LR) := by
      intro hmem
      have hoff := mem_arcSet.mp hmem
      have hne : P.start W ≠ P.start LR := by
        intro h
        rw [h, sub_self] at hWnotU
        simp only [Fin.val_zero] at hWnotU
        omega
      have hsum := val_sub_add_val_sub hne
      have hcov := P.union_arc_lt hLR hW hoff
      omega
    obtain ⟨u, hu⟩ := P.out_nonempty (P.start W)
    have huW : u ∈ W := P.leftmost_atom hW hu
    have huLR : u ∉ LR := by
      rcases atom_subset_or_disjoint (P.out_atom (P.start W)) hLR with h | h
      · exact absurd ((P.outside_eq_arc LR hLR _).mp h) hWLR
      · exact Finset.disjoint_left.mp h hu
    exact ⟨u, Finset.mem_sdiff.mpr ⟨huW, huLR⟩⟩
  · obtain ⟨w, hw⟩ := hcrossWU.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact ⟨w, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hw.1).2, hw.2⟩⟩

/-- **`R* ∩ R_L ⊆ R`** — the left mirror of `star_inter_isSR_subset`.
Simpler than the right side: `R^∩L` shares `R`'s start, so `R*` crossing
`R` on the left would put `start R` in `R*`'s arc, which side exclusivity
at `R^∩L` forbids outright. -/
theorem star_inter_isSL_subset (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {R RL W : Finset (Fin n)} (hR : R ∈ 𝒞) (hRL : RL ∈ 𝒞) (hW : W ∈ 𝒞)
    (hcl : P.CrossesOnLeft RL R)
    (hcW : P.CrossesOnRightArc W (R ∩ RL) (P.start R)
      (P.len RL - (P.start R - P.start RL).val)) :
    W ∩ RL ⊆ R := by
  classical
  by_cases hsub : W ⊆ R
  · exact fun v hv => hsub (Finset.mem_inter.mp hv).1
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_inter_left hx hη0 hC hR hRL hcl
  have hcrossWU : Crossing W (R ∩ RL) := hcW.1
  have hcross : Crossing W R := by
    obtain ⟨a, ha⟩ := hcrossWU.1
    obtain ⟨w, hw⟩ := hcrossWU.2.2.1
    rw [Finset.mem_inter] at ha
    rw [Finset.mem_sdiff] at hw
    obtain ⟨v, hv, hv'⟩ := Finset.not_subset.mp hsub
    exact ⟨⟨a, Finset.mem_inter.mpr ⟨ha.1, (Finset.mem_inter.mp ha.2).1⟩⟩,
      ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩,
      ⟨w, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hw.1).1, hw.2⟩⟩,
      P.union_ne_univ hW hR⟩
  rcases P.crossesOnLeft_or_crossesOnRight hW hR hcross with hleft | hright
  · exact absurd ⟨⟨hcrossWU, hleft.2⟩, hcW⟩
      (P.not_crossesOnLeftArc_and_crossesOnRightArc hx hη0 (by linarith)
        hC hUad hUarc hW)
  · have hdisj := P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
      (by linarith) hC hR hRL hW hcl hright
    intro v hv
    rw [Finset.mem_inter] at hv
    by_contra hvR
    exact Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mpr ⟨hv.2, hvR⟩)
      (Finset.mem_sdiff.mpr ⟨hv.1, hvR⟩)

/-- **`R*` crosses `R_L`** — the left mirror of `star_crossing_isSR`.  The
vertex of `R*` outside `R_L` sits in an atom of `R*` past `R^∩L`'s arc,
which ends exactly where `R_L`'s does. -/
theorem star_crossing_isSL (hx : x ∈ subtourLP n) (hη0 : 0 < η)
    (hη : η < 1 / 10) (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {R RL W : Finset (Fin n)} (hR : R ∈ 𝒞) (hRL : RL ∈ 𝒞) (hW : W ∈ 𝒞)
    (hcl : P.CrossesOnLeft RL R)
    (hcW : P.CrossesOnRightArc W (R ∩ RL) (P.start R)
      (P.len RL - (P.start R - P.start RL).val)) :
    Crossing W RL := by
  obtain ⟨hUad, hUarc⟩ := P.isAlmostDiagonal_inter_left hx hη0 hC hR hRL hcl
  have hcrossWU : Crossing W (R ∩ RL) := hcW.1
  refine ⟨?_, ?_, ?_, P.union_ne_univ hW hRL⟩
  · obtain ⟨a, ha⟩ := hcrossWU.1
    rw [Finset.mem_inter] at ha
    exact ⟨a, Finset.mem_inter.mpr ⟨ha.1, (Finset.mem_inter.mp ha.2).2⟩⟩
  · -- an atom of `W` past `R^∩L`'s arc lies outside `R_L`
    have harcs := cross_arc_of_almostDiagonal hx hη0 (by linarith) hC P
      (P.isAlmostDiagonal_of_mem (le_of_lt hη0) hC.nearMin hW) hUad
      (P.isArcOf_of_mem hW) hUarc hcrossWU
    obtain ⟨j, hj⟩ := harcs.2.1
    rw [Finset.mem_sdiff] at hj
    have hm := P.hm
    have hmRL := P.len_le RL hRL
    have hdL : (P.start R - P.start RL).val < P.len RL := mem_arcSet.mp hcl.2
    have hWU : (P.start W - P.start R).val
        < P.len RL - (P.start R - P.start RL).val := mem_arcSet.mp hcW.2
    have hdW : (P.start W - P.start RL).val
        = (P.start W - P.start R).val + (P.start R - P.start RL).val := by
      have hrel := val_sub_rel (P.start W) (P.start RL) (P.start R)
      rw [Nat.mod_eq_of_lt (by omega)] at hrel
      exact hrel
    have hcov := P.union_arc_lt hRL hW (by omega)
    have hjW := mem_arcSet.mp hj.1
    have hjU := mem_arcSet_compl.mp hj.2
    have hjRL : (j - P.start RL).val
        = (j - P.start W).val + (P.start W - P.start RL).val := by
      have hrel := val_sub_rel j (P.start RL) (P.start W)
      rw [Nat.mod_eq_of_lt (by omega)] at hrel
      exact hrel
    have hjR : (j - P.start R).val
        = (j - P.start RL).val - (P.start R - P.start RL).val :=
      val_sub_of_le (s := P.start RL) (α := P.start R) (β := j) (by omega)
    have hjnotRL : j ∉ arcSet (P.start RL) (P.len RL) :=
      mem_arcSet_compl.mpr (by omega)
    have hjWatom : P.out j ⊆ W := (P.outside_eq_arc W hW j).mpr hj.1
    obtain ⟨u, hu⟩ := P.out_nonempty j
    have huW : u ∈ W := hjWatom hu
    have huRL : u ∉ RL := by
      rcases atom_subset_or_disjoint (P.out_atom j) hRL with h | h
      · exact absurd ((P.outside_eq_arc RL hRL _).mp h) hjnotRL
      · exact Finset.disjoint_left.mp h hu
    exact ⟨u, Finset.mem_sdiff.mpr ⟨huW, huRL⟩⟩
  · obtain ⟨w, hw⟩ := hcrossWU.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact ⟨w, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hw.1).2, hw.2⟩⟩

end PolygonRep

/-- **Lemma 5.6's disjoint union, in the generality the genuine star
needs**: `Z` need not sit inside `X` — it suffices that `Z` misses
`Y ∖ X`, and then `(X ∖ Z) ⊎ (Y ∖ X) = Y ∖ Z`.  (The old `Z ⊆ X` special
case covered only `L* = ∅`.) -/
theorem one_sub_le_sum_badEdges_of_disjoint
    (hx : x ∈ subtourLP n) {X Y Z : Finset (Fin n)} (hXY : X ⊆ Y)
    (hZ : Disjoint Z (Y \ X))
    (h1 : (X \ Z).Nonempty) (h1' : X \ Z ≠ Finset.univ)
    (h2 : (Y \ X).Nonempty) (h2' : Y \ X ≠ Finset.univ)
    (hnmc : IsNearMinCut x (2 * η) (Y \ Z)) :
    1 - η ≤ ∑ e ∈ betweenEdges (X \ Z) (Y \ X), x e := by
  have hunion : (X \ Z) ∪ (Y \ X) = Y \ Z := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hv, hv'⟩ | ⟨hv, hv'⟩)
      · exact ⟨hXY hv, hv'⟩
      · exact ⟨hv, fun hz => Finset.disjoint_left.mp hZ hz
          (Finset.mem_sdiff.mpr ⟨hv, hv'⟩)⟩
    · rintro ⟨hv, hv'⟩
      by_cases hxv : v ∈ X
      · exact Or.inl ⟨hxv, hv'⟩
      · exact Or.inr ⟨hv, hxv⟩
  have hdisj : Disjoint (X \ Z) (Y \ X) := Finset.disjoint_left.mpr
    fun v hv hv' => (Finset.mem_sdiff.mp hv').2 (Finset.mem_sdiff.mp hv).1
  rw [sum_betweenEdges x hdisj]
  have hcut : cutSum x ((X \ Z) ∪ (Y \ X)) ≤ 2 + 2 * η := by
    rw [hunion]
    exact hnmc.cut_le
  have := le_pairSum_of_union hx hdisj h1 h1' h2 h2' hcut
  linarith

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **KKO22 Lemma 5.6 at the chosen star, right events**: the charged edge
set carries `x`-mass at least `1 − η`, whether the star is a genuine
maximizer (heavy cut `L_R ∖ L*`, via the crossing and the silent
inclusion) or the chosen `∅` (heavy cut `L_R` itself). -/
theorem one_sub_le_sum_badEdgesRight_chosen (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {L LR W : Finset (Fin n)} (hL : L ∈ 𝒞) (hSR : P.IsSR L LR)
    (hstar : P.IsChosenLStar (L ∩ LR) (P.start LR) W) :
    1 - η ≤ ∑ e ∈ badEdgesRight L LR W, x e := by
  have hLRmem := hSR.1
  have hcr := hSR.2.1
  have hcrossLLR : Crossing LR L := hcr.1
  have hXY : L ∩ LR ⊆ LR := Finset.inter_subset_right
  have h2 : (LR \ (L ∩ LR)).Nonempty := by
    obtain ⟨w, hw⟩ := hcrossLLR.2.1
    rw [Finset.mem_sdiff] at hw
    exact ⟨w, Finset.mem_sdiff.mpr
      ⟨hw.1, fun hc => hw.2 (Finset.mem_inter.mp hc).1⟩⟩
  have h2' : LR \ (L ∩ LR) ≠ Finset.univ := fun h =>
    (hC.nearMin LR hLRmem).ne_univ
      (Finset.univ_subset_iff.mp (h ▸ Finset.sdiff_subset))
  rw [badEdgesRight]
  rcases hstar with hmax | ⟨rfl, -⟩
  · have hWmem := hmax.1
    have hcW := hmax.2.1
    have hsub := P.star_inter_isSR_subset hx hη0 hη hC hL hLRmem hWmem hcr hcW
    have hcrossWLR := P.star_crossing_isSR hx hη0 hη hC hL hLRmem hWmem hcr hcW
    have hZ : Disjoint W (LR \ (L ∩ LR)) := Finset.disjoint_left.mpr
      fun v hv hv' => by
        rw [Finset.mem_sdiff] at hv'
        exact hv'.2 (Finset.mem_inter.mpr
          ⟨hsub (Finset.mem_inter.mpr ⟨hv, hv'.1⟩), hv'.1⟩)
    have h1 : ((L ∩ LR) \ W).Nonempty := hcW.1.2.2.1
    have h1' : (L ∩ LR) \ W ≠ Finset.univ := fun h =>
      (hC.nearMin L hL).ne_univ (Finset.univ_subset_iff.mp
        (h ▸ (Finset.sdiff_subset.trans Finset.inter_subset_left)))
    refine one_sub_le_sum_badEdges_of_disjoint hx hXY hZ h1 h1' h2 h2' ?_
    rw [two_mul]
    exact nearMinCut_sdiff hx (hC.nearMin LR hLRmem) (hC.nearMin W hWmem)
      hcrossWLR.symm
  · have hZ : Disjoint (∅ : Finset (Fin n)) (LR \ (L ∩ LR)) :=
      Finset.disjoint_left.mpr fun v hv => absurd hv (Finset.notMem_empty v)
    have h1 : ((L ∩ LR) \ ∅).Nonempty := by
      rw [Finset.sdiff_empty]
      obtain ⟨a, ha⟩ := hcrossLLR.1
      rw [Finset.mem_inter] at ha
      exact ⟨a, Finset.mem_inter.mpr ⟨ha.2, ha.1⟩⟩
    have h1' : (L ∩ LR) \ ∅ ≠ Finset.univ := by
      rw [Finset.sdiff_empty]
      exact fun h => (hC.nearMin L hL).ne_univ
        (Finset.univ_subset_iff.mp (h ▸ Finset.inter_subset_left))
    refine one_sub_le_sum_badEdges_of_disjoint hx hXY hZ h1 h1' h2 h2' ?_
    rw [Finset.sdiff_empty]
    exact (hC.nearMin LR hLRmem).mono (by linarith)

/-- **KKO22 Lemma 5.6 at the chosen star, left events** — the mirror. -/
theorem one_sub_le_sum_badEdgesLeft_chosen (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {R RL W : Finset (Fin n)} (hR : R ∈ 𝒞) (hSL : P.IsSL R RL)
    (hstar : P.IsChosenRStar (R ∩ RL) (P.start R)
      (P.len RL - (P.start R - P.start RL).val) W) :
    1 - η ≤ ∑ e ∈ badEdgesLeft R RL W, x e := by
  have hRLmem := hSL.1
  have hcl := hSL.2.1
  have hcrossRRL : Crossing RL R := hcl.1
  have hXY : R ∩ RL ⊆ RL := Finset.inter_subset_right
  have h2 : (RL \ (R ∩ RL)).Nonempty := by
    obtain ⟨w, hw⟩ := hcrossRRL.2.1
    rw [Finset.mem_sdiff] at hw
    exact ⟨w, Finset.mem_sdiff.mpr
      ⟨hw.1, fun hc => hw.2 (Finset.mem_inter.mp hc).1⟩⟩
  have h2' : RL \ (R ∩ RL) ≠ Finset.univ := fun h =>
    (hC.nearMin RL hRLmem).ne_univ
      (Finset.univ_subset_iff.mp (h ▸ Finset.sdiff_subset))
  rw [badEdgesLeft]
  rcases hstar with hmax | ⟨rfl, -⟩
  · have hWmem := hmax.1
    have hcW := hmax.2.1
    have hsub := P.star_inter_isSL_subset hx hη0 hη hC hR hRLmem hWmem hcl hcW
    have hcrossWRL := P.star_crossing_isSL hx hη0 hη hC hR hRLmem hWmem hcl hcW
    have hZ : Disjoint W (RL \ (R ∩ RL)) := Finset.disjoint_left.mpr
      fun v hv hv' => by
        rw [Finset.mem_sdiff] at hv'
        exact hv'.2 (Finset.mem_inter.mpr
          ⟨hsub (Finset.mem_inter.mpr ⟨hv, hv'.1⟩), hv'.1⟩)
    have h1 : ((R ∩ RL) \ W).Nonempty := hcW.1.2.2.1
    have h1' : (R ∩ RL) \ W ≠ Finset.univ := fun h =>
      (hC.nearMin R hR).ne_univ (Finset.univ_subset_iff.mp
        (h ▸ (Finset.sdiff_subset.trans Finset.inter_subset_left)))
    refine one_sub_le_sum_badEdges_of_disjoint hx hXY hZ h1 h1' h2 h2' ?_
    rw [two_mul]
    exact nearMinCut_sdiff hx (hC.nearMin RL hRLmem) (hC.nearMin W hWmem)
      hcrossWRL.symm
  · have hZ : Disjoint (∅ : Finset (Fin n)) (RL \ (R ∩ RL)) :=
      Finset.disjoint_left.mpr fun v hv => absurd hv (Finset.notMem_empty v)
    have h1 : ((R ∩ RL) \ ∅).Nonempty := by
      rw [Finset.sdiff_empty]
      obtain ⟨a, ha⟩ := hcrossRRL.1
      rw [Finset.mem_inter] at ha
      exact ⟨a, Finset.mem_inter.mpr ⟨ha.2, ha.1⟩⟩
    have h1' : (R ∩ RL) \ ∅ ≠ Finset.univ := by
      rw [Finset.sdiff_empty]
      exact fun h => (hC.nearMin R hR).ne_univ
        (Finset.univ_subset_iff.mp (h ▸ Finset.inter_subset_left))
    refine one_sub_le_sum_badEdges_of_disjoint hx hXY hZ h1 h1' h2 h2' ?_
    rw [Finset.sdiff_empty]
    exact (hC.nearMin RL hRLmem).mono (by linarith)

end PolygonRep

/-! ### Lemma 5.1 without the transfer hypothesis

`isSR_of_shared_rightPoint` and `isSL_of_shared_leftPoint` carry the
hypothesis that every crosser of the *larger* cut crosses the smaller —
which is false in general: a `B`-crosser can start left of `A`'s arc, or
can contain `A` outright.  KKO's proof compares the two Definition 4.17
candidate pools instead ("any cut which crosses `B` but not `A` … would
have a larger intersection with `O(B)`"), and their parenthetical about
tie-breaking hides a real argument.  Both are made rigorous here:

  * a `B`-crosser either crosses `A`, or starts left of `A`'s arc, or
    contains `A` — and in the latter two cases its overlap with `O(B)` is
    at least `len A`, while every `A`-crosser's is at most `len A`;
  * for the tie-break, an equal-count containment forces equal starts,
    and the nested-arc dichotomy then rules out a shorter competitor.

Also proved: the containments `A ⊆ B` themselves, from the shared polygon
point and the length comparison — the hypothesis every use site needs.
These belong with §5.1 in `InsideAtoms.lean`; developed here for cheap
iteration. -/

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **Cuts sharing a right polygon point are nested by length.** -/
theorem subset_of_shared_rightPoint (hA : S ∈ 𝒞) {B : Finset (Fin n)}
    (hB : B ∈ 𝒞) (hpt : P.rightPoint S = P.rightPoint B)
    (hlen : P.len S ≤ P.len B) : S ⊆ B := by
  have hm := P.hm
  have h2S := P.two_le_len S hA
  have hmB := P.len_le B hB
  have hg := P.val_start_sub_start_of_rightPoint_eq hA hB hpt hlen
  have harcsub : arcSet (P.start S) (P.len S)
      ⊆ arcSet (P.start B) (P.len B) := arcSet_subset (by omega) (by omega)
  obtain ⟨i, hival, himem⟩ := exists_last_mem_arcSet (P.start S)
    (l := P.len S) (by omega) (by omega)
  obtain ⟨v, hv⟩ := P.out_nonempty i
  have hvS : v ∈ S := (P.outside_eq_arc S hA i).mpr himem hv
  have hvB : v ∈ B := (P.outside_eq_arc B hB i).mpr (harcsub himem) hv
  rcases P.subset_of_arc_nested hB hA harcsub
    ⟨v, Finset.mem_inter.mpr ⟨hvB, hvS⟩⟩ with h | h
  · have houts : P.outsideIn B ⊆ P.outsideIn S := fun j hj =>
      P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hj).trans h)
    rw [P.outsideIn_eq_arc hB, P.outsideIn_eq_arc hA] at houts
    have hconv := le_of_arcSet_subset houts (by omega) (by omega)
    have h0 : (P.start B - P.start S).val = 0 := by omega
    have hst : P.start B = P.start S :=
      sub_eq_zero.mp (Fin.val_injective (by simpa using h0))
    have heq := P.arc_injective B hB S hA hst (by omega)
    exact heq ▸ Finset.Subset.refl S
  · exact h

/-- **Cuts sharing a left polygon point are nested by length.** -/
theorem subset_of_shared_leftPoint (hA : S ∈ 𝒞) {B : Finset (Fin n)}
    (hB : B ∈ 𝒞) (hst : P.start S = P.start B)
    (hlen : P.len S ≤ P.len B) : S ⊆ B := by
  have hm := P.hm
  have h2S := P.two_le_len S hA
  have hmB := P.len_le B hB
  have harcsub : arcSet (P.start S) (P.len S)
      ⊆ arcSet (P.start B) (P.len B) := by
    rw [hst]
    exact arcSet_mono hlen
  obtain ⟨v, hv⟩ := P.out_nonempty (P.start S)
  have hvS : v ∈ S := P.leftmost_atom hA hv
  have hvB : v ∈ B := by
    have hout : P.out (P.start B) ⊆ B := P.leftmost_atom hB
    rw [← hst] at hout
    exact hout hv
  rcases P.subset_of_arc_nested hB hA harcsub
    ⟨v, Finset.mem_inter.mpr ⟨hvB, hvS⟩⟩ with h | h
  · have houts : P.outsideIn B ⊆ P.outsideIn S := fun j hj =>
      P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hj).trans h)
    rw [P.outsideIn_eq_arc hB, P.outsideIn_eq_arc hA] at houts
    have hconv := le_of_arcSet_subset houts (by omega) (by omega)
    have h0 : (P.start B - P.start S).val = 0 := by
      rw [← hst, sub_self]
      simp only [Fin.val_zero]
    have heq := P.arc_injective B hB S hA hst.symm (by omega)
    exact heq ▸ Finset.Subset.refl S
  · exact h

/-- **KKO22 Lemma 5.1, first conclusion, unconditionally**: `A_R = B_R`
holds with no transfer hypothesis — the Definition 4.17 comparison runs
across the two candidate pools directly. -/
theorem isSR_of_shared_rightPoint' (hA : S ∈ 𝒞) {B R : Finset (Fin n)}
    (hB : B ∈ 𝒞) (hsub : S ⊆ B) (hpt : P.rightPoint S = P.rightPoint B)
    (hlen : P.len S ≤ P.len B) (hSR : P.IsSR S R) : P.IsSR B R := by
  obtain ⟨hRmem, hcr, hmin, htie⟩ := hSR
  have hm := P.hm
  have h2S := P.two_le_len S hA
  have hmB := P.len_le B hB
  have hg := P.val_start_sub_start_of_rightPoint_eq hA hB hpt hlen
  have hdS : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcr.2
  -- a `B`-crosser meeting `A`'s arc and not containing `A` crosses `A`
  have hcrS_of : ∀ R' ∈ 𝒞, P.CrossesOnRight R' B → ¬ S ⊆ R' →
      P.len B - P.len S ≤ (P.start R' - P.start B).val →
      P.CrossesOnRight R' S := by
    intro R' hR' hcr' hnsub hbig
    have hd' : (P.start R' - P.start B).val < P.len B := mem_arcSet.mp hcr'.2
    have hrp' := mem_arcSet.mp
      (P.rightPoint_mem_arc_of_crossesOnRight hB hR' hcr')
    have hrpB := P.val_rightPoint_sub_start hB
    have hrpR' : (P.rightPoint B - P.start R').val
        = (P.rightPoint B - P.start B).val - (P.start R' - P.start B).val :=
      val_sub_of_le (s := P.start B) (α := P.start R') (β := P.rightPoint B)
        (by omega)
    have hside : P.start R' ∈ arcSet (P.start S) (P.len S) := by
      rw [mem_arcSet]
      have := val_sub_of_le (s := P.start B) (α := P.start S)
        (β := P.start R') (by omega)
      omega
    refine ⟨⟨?_, ?_, ?_, P.union_ne_univ hR' hA⟩, hside⟩
    · obtain ⟨i, hival, himem⟩ := exists_last_mem_arcSet (P.start S)
        (l := P.len S) (by omega) (by omega)
      have hiB : (i - P.start B).val = P.len B - 1 := by
        have hrel := val_sub_rel i (P.start B) (P.start S)
        rw [hival, hg, Nat.mod_eq_of_lt (by omega)] at hrel
        omega
      have hiR' : i ∈ arcSet (P.start R') (P.len R') := by
        rw [mem_arcSet]
        have := val_sub_of_le (s := P.start B) (α := P.start R') (β := i)
          (by omega)
        omega
      obtain ⟨v, hv⟩ := P.out_nonempty i
      exact ⟨v, Finset.mem_inter.mpr
        ⟨(P.outside_eq_arc R' hR' i).mpr hiR' hv,
         (P.outside_eq_arc S hA i).mpr himem hv⟩⟩
    · have hiR' : P.rightPoint B ∈ arcSet (P.start R') (P.len R') :=
        P.rightPoint_mem_arc_of_crossesOnRight hB hR' hcr'
      have hnotS : P.rightPoint B ∉ arcSet (P.start S) (P.len S) := by
        rw [← hpt]
        exact P.rightPoint_notMem_arc hA
      obtain ⟨v, hv⟩ := P.out_nonempty (P.rightPoint B)
      have hvR' : v ∈ R' := (P.outside_eq_arc R' hR' _).mpr hiR' hv
      have hvS : v ∉ S := by
        rcases atom_subset_or_disjoint (P.out_atom (P.rightPoint B)) hA
          with h | h
        · exact absurd ((P.outside_eq_arc S hA _).mp h) hnotS
        · exact Finset.disjoint_left.mp h hv
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hvR', hvS⟩⟩
    · obtain ⟨v, hv, hv'⟩ := Finset.not_subset.mp hnsub
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩
  -- a crosser containing `A` overlaps `O(B)` in at least `len A` atoms
  have hgeS_of : ∀ R' : Finset (Fin n), S ⊆ R' →
      P.len S ≤ (P.outsideIn B ∩ P.outsideIn R').card := by
    intro R' hsub'
    have hsubO : P.outsideIn S ⊆ P.outsideIn B ∩ P.outsideIn R' := fun i hi =>
      Finset.mem_inter.mpr
        ⟨P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans hsub),
         P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans hsub')⟩
    have hcard := Finset.card_le_card hsubO
    rwa [P.card_outsideIn hA] at hcard
  have hRcount : (P.outsideIn B ∩ P.outsideIn R).card
      = P.len S - (P.start R - P.start S).val := by
    rw [P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hRmem hsub hpt
        hlen hcr,
      P.card_outsideIn_inter_right hA hRmem hcr]
  refine ⟨hRmem,
    P.crossesOnRight_of_shared_rightPoint hA hB hRmem hsub hpt hcr, ?_, ?_⟩
  · intro R' hR' hcr'
    by_cases hsub' : S ⊆ R'
    · have hge := hgeS_of R' hsub'
      omega
    · rcases lt_or_ge (P.start R' - P.start B).val (P.len B - P.len S)
        with hsm | hbig
      · have h' := P.card_outsideIn_inter_right hB hR' hcr'
        have hd' : (P.start R' - P.start B).val < P.len B :=
          mem_arcSet.mp hcr'.2
        omega
      · have hcrS := hcrS_of R' hR' hcr' hsub' hbig
        rw [P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hRmem hsub
            hpt hlen hcr,
          P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hR' hsub hpt
            hlen hcrS]
        exact hmin R' hR' hcrS
  · intro R' hR' hcr' hcard
    by_cases hsub' : S ⊆ R'
    · -- the corner: equal counts force equal starts, and the nested-arc
      -- dichotomy rules out a shorter competitor
      have hge := hgeS_of R' hsub'
      have h' := P.card_outsideIn_inter_right hB hR' hcr'
      have hd' : (P.start R' - P.start B).val < P.len B := mem_arcSet.mp hcr'.2
      have hd'eq : (P.start R' - P.start B).val = P.len B - P.len S := by omega
      have hdS0 : (P.start R - P.start S).val = 0 := by omega
      have hdB_R : (P.start R - P.start B).val = P.len B - P.len S := by
        have hsplit : P.start R - P.start B
            = (P.start R - P.start S) + (P.start S - P.start B) := by abel
        have hval := congrArg Fin.val hsplit
        rw [Fin.val_add, hg] at hval
        rw [Nat.mod_eq_of_lt (by omega)] at hval
        omega
      have hstart : P.start R' = P.start R := by
        have hveq : (P.start R' - P.start B).val
            = (P.start R - P.start B).val := by omega
        exact sub_left_inj.mp (Fin.val_injective hveq)
      by_contra hltlen
      push Not at hltlen
      have harc' : arcSet (P.start R') (P.len R')
          ⊆ arcSet (P.start R) (P.len R) := by
        rw [hstart]
        exact arcSet_mono (by omega)
      have hrpR := mem_arcSet.mp
        (P.rightPoint_mem_arc_of_crossesOnRight hA hRmem hcr)
      have hrpvS := P.val_rightPoint_sub_start hA
      have hvR : (P.rightPoint S - P.start R).val
          = (P.rightPoint S - P.start S).val - (P.start R - P.start S).val :=
        val_sub_of_le (s := P.start S) (α := P.start R) (β := P.rightPoint S)
          (by omega)
      have hrp' := mem_arcSet.mp
        (P.rightPoint_mem_arc_of_crossesOnRight hB hR' hcr')
      have hrpvB := P.val_rightPoint_sub_start hB
      have hvR' : (P.rightPoint B - P.start R').val
          = (P.rightPoint B - P.start B).val - (P.start R' - P.start B).val :=
        val_sub_of_le (s := P.start B) (α := P.start R') (β := P.rightPoint B)
          (by omega)
      have hinterRR' : (R ∩ R').Nonempty := by
        obtain ⟨i, hival, himem⟩ := exists_last_mem_arcSet (P.start S)
          (l := P.len S) (by omega) (by omega)
        have hoffR := val_sub_of_le (s := P.start S) (α := P.start R) (β := i)
          (by omega)
        have hiR : i ∈ arcSet (P.start R) (P.len R) := by
          rw [mem_arcSet]
          omega
        have hiR' : i ∈ arcSet (P.start R') (P.len R') := by
          rw [mem_arcSet]
          have h1 : (i - P.start R').val = (i - P.start R).val := by
            rw [hstart]
          omega
        obtain ⟨v, hv⟩ := P.out_nonempty i
        exact ⟨v, Finset.mem_inter.mpr
          ⟨(P.outside_eq_arc R hRmem i).mpr hiR hv,
           (P.outside_eq_arc R' hR' i).mpr hiR' hv⟩⟩
      rcases P.subset_of_arc_nested hRmem hR' harc' hinterRR' with h | h
      · have houts : P.outsideIn R ⊆ P.outsideIn R' := fun j hj =>
          P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hj).trans h)
        rw [P.outsideIn_eq_arc hRmem, P.outsideIn_eq_arc hR'] at houts
        have hconv := le_of_arcSet_subset houts (by omega)
          (by have := P.len_le R' hR'; omega)
        omega
      · obtain ⟨v, hv⟩ := hcr.1.2.2.1
        rw [Finset.mem_sdiff] at hv
        exact absurd (h (hsub' hv.1)) hv.2
    · rcases lt_or_ge (P.start R' - P.start B).val (P.len B - P.len S)
        with hsm | hbig
      · have h' := P.card_outsideIn_inter_right hB hR' hcr'
        have hd' : (P.start R' - P.start B).val < P.len B :=
          mem_arcSet.mp hcr'.2
        omega
      · have hcrS := hcrS_of R' hR' hcr' hsub' hbig
        refine htie R' hR' hcrS ?_
        rw [← P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hR' hsub
            hpt hlen hcrS,
          ← P.card_outsideIn_inter_eq_of_shared_rightPoint hA hB hRmem hsub
            hpt hlen hcr]
        exact hcard

/-- **KKO22 Lemma 5.1, left version, unconditionally**: `A_L = B_L` with no
transfer hypothesis.  Simpler than the right side: the left objective of
`A_L` is *strictly* below `len A` (an atom of `A` escapes `A_L`'s arc),
while a crosser containing `A` overlaps in at least `len A` — so the
containment case never ties, and no corner arises. -/
theorem isSL_of_shared_leftPoint' (hA : S ∈ 𝒞) {B L : Finset (Fin n)}
    (hB : B ∈ 𝒞) (hsub : S ⊆ B) (hpt : P.start S = P.start B)
    (hSL : P.IsSL S L) : P.IsSL B L := by
  obtain ⟨hLmem, hcl, hmin, htie⟩ := hSL
  have hcount : ∀ L' ∈ 𝒞, P.CrossesOnLeft L' S →
      (P.outsideIn B ∩ P.outsideIn L').card
        = (P.outsideIn S ∩ P.outsideIn L').card := by
    intro L' hL' hcl'
    rw [P.card_outsideIn_inter_left hA hL' hcl',
      P.card_outsideIn_inter_left hB hL'
        (P.crossesOnLeft_of_shared_leftPoint hA hB hL' hsub hpt hcl'),
      hpt]
  have hLcount : (P.outsideIn S ∩ P.outsideIn L).card < P.len S := by
    have harcs := P.cross_arc L hLmem S hA hcl.1
    obtain ⟨j, hj⟩ := harcs.2.2.1
    rw [Finset.mem_sdiff] at hj
    have hssub : P.outsideIn S ∩ P.outsideIn L ⊂ P.outsideIn S := by
      refine (Finset.ssubset_iff_of_subset Finset.inter_subset_left).mpr
        ⟨j, ?_, ?_⟩
      · rw [P.outsideIn_eq_arc hA]
        exact hj.1
      · intro hmem
        refine hj.2 ?_
        have := (Finset.mem_inter.mp hmem).2
        rwa [P.outsideIn_eq_arc hLmem] at this
    have hlt := Finset.card_lt_card hssub
    rwa [P.card_outsideIn hA] at hlt
  have hgeS_of : ∀ L' : Finset (Fin n), S ⊆ L' →
      P.len S ≤ (P.outsideIn B ∩ P.outsideIn L').card := by
    intro L' hsub'
    have hsubO : P.outsideIn S ⊆ P.outsideIn B ∩ P.outsideIn L' := fun i hi =>
      Finset.mem_inter.mpr
        ⟨P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans hsub),
         P.mem_outsideIn.mpr ((P.mem_outsideIn.mp hi).trans hsub')⟩
    have hcard := Finset.card_le_card hsubO
    rwa [P.card_outsideIn hA] at hcard
  have hclS_of : ∀ L' ∈ 𝒞, P.CrossesOnLeft L' B → ¬ S ⊆ L' →
      P.CrossesOnLeft L' S := by
    intro L' hL' hcl' hnsub
    have hside : P.start S ∈ arcSet (P.start L') (P.len L') := by
      rw [hpt]
      exact hcl'.2
    refine ⟨⟨?_, ?_, ?_, P.union_ne_univ hL' hA⟩, hside⟩
    · obtain ⟨v, hv⟩ := P.out_nonempty (P.start S)
      exact ⟨v, Finset.mem_inter.mpr
        ⟨(P.outside_eq_arc L' hL' _).mpr hside hv, P.leftmost_atom hA hv⟩⟩
    · obtain ⟨v, hv⟩ := hcl'.1.2.1
      rw [Finset.mem_sdiff] at hv
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hv.1, fun hc => hv.2 (hsub hc)⟩⟩
    · obtain ⟨v, hv, hv'⟩ := Finset.not_subset.mp hnsub
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩
  refine ⟨hLmem,
    P.crossesOnLeft_of_shared_leftPoint hA hB hLmem hsub hpt hcl, ?_, ?_⟩
  · intro L' hL' hcl'
    by_cases hsub' : S ⊆ L'
    · have hge := hgeS_of L' hsub'
      have hL := hcount L hLmem hcl
      omega
    · have hclS := hclS_of L' hL' hcl' hsub'
      rw [hcount L hLmem hcl, hcount L' hL' hclS]
      exact hmin L' hL' hclS
  · intro L' hL' hcl' hcard
    by_cases hsub' : S ⊆ L'
    · exfalso
      have hge := hgeS_of L' hsub'
      have hL := hcount L hLmem hcl
      omega
    · have hclS := hclS_of L' hL' hcl' hsub'
      refine htie L' hL' hclS ?_
      rw [← hcount L' hL' hclS, ← hcount L hLmem hcl]
      exact hcard

end PolygonRep

/-! ### Lemma 5.7 and Lemma 5.3, at the polygon points

KKO's Lemma 5.7 splits into a proper configuration — `S ⊊ L(p_r)` and
`S ⊊ R(p_l)`, where the two extensions cross and `L ∩ R = S` by Lemma
4.23 — and degenerate ones, where a coincidence like `L(p_r) = S` reduces
the transfer to witness uniqueness.  The degenerate routing never touches
the crossing-dependent disjointness facts: `S`'s own trichotomy plus
Lemma 5.1's arrow equalities carry each disjunct into an event. -/

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **`R(p_l)` crosses `L(p_r)` on the right**, in the proper
configuration.  The side is `start R = start S ∈ O(L)`; the witnesses are
the atom at the shared right point (in `R`, past `L`'s arc) and `L`'s
leftmost atom (which `R`'s arc cannot reach without covering the polygon
together with `L`'s, against Fact 4.8). -/
theorem crossesOnRight_of_extends_both_sides (hS : S ∈ 𝒞)
    {L R : Finset (Fin n)} (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hsubL : S ⊆ L) (hsubR : S ⊆ R)
    (hptL : P.rightPoint S = P.rightPoint L) (hlenL : P.len S < P.len L)
    (hstR : P.start S = P.start R) (hlenR : P.len S < P.len R) :
    P.CrossesOnRight R L := by
  have hm := P.hm
  have h2S := P.two_le_len S hS
  have hmL := P.len_le L hL
  have hmR := P.len_le R hR
  have hg := P.val_start_sub_start_of_rightPoint_eq hS hL hptL (le_of_lt hlenL)
  -- `R`'s arc cannot reach back to `L`'s start
  have hcov : P.len R + (P.len L - P.len S) ≤ P.m := by
    by_contra hcon
    push Not at hcon
    refine P.arcs_ne_univ L hL R hR ?_
    ext j
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_arcSet]
    have hrel := val_sub_rel j (P.start L) (P.start S)
    by_cases hj : (j - P.start S).val < P.len R
    · refine Or.inr ?_
      have h1 : (j - P.start R).val = (j - P.start S).val := by rw [hstR]
      omega
    · refine Or.inl ?_
      push Not at hj
      rw [hg] at hrel
      have hjm : (j - P.start S).val < P.m := Fin.is_lt _
      rw [show (j - P.start S).val + (P.len L - P.len S)
          = P.m + ((j - P.start S).val + (P.len L - P.len S) - P.m) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
      omega
  refine ⟨⟨?_, ?_, ?_, P.union_ne_univ hR hL⟩, ?_⟩
  · obtain ⟨v, hv⟩ := P.out_nonempty (P.start S)
    have hvS : v ∈ S := P.leftmost_atom hS hv
    exact ⟨v, Finset.mem_inter.mpr ⟨hsubR hvS, hsubL hvS⟩⟩
  · -- the atom at the shared right point: in `R`, not in `L`
    have hmemR : P.rightPoint S ∈ arcSet (P.start R) (P.len R) := by
      rw [mem_arcSet]
      have h1 : (P.rightPoint S - P.start R).val
          = (P.rightPoint S - P.start S).val := by rw [hstR]
      have h2 := P.val_rightPoint_sub_start hS
      omega
    have hnotL : P.rightPoint S ∉ arcSet (P.start L) (P.len L) := by
      rw [hptL]
      exact P.rightPoint_notMem_arc hL
    obtain ⟨v, hv⟩ := P.out_nonempty (P.rightPoint S)
    have hvR : v ∈ R := (P.outside_eq_arc R hR _).mpr hmemR hv
    have hvL : v ∉ L := by
      rcases atom_subset_or_disjoint (P.out_atom (P.rightPoint S)) hL with h | h
      · exact absurd ((P.outside_eq_arc L hL _).mp h) hnotL
      · exact Finset.disjoint_left.mp h hv
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvR, hvL⟩⟩
  · -- `L`'s leftmost atom: in `L`, not in `R`
    have hne : P.start S ≠ P.start L := by
      intro h
      rw [h, sub_self] at hg
      simp only [Fin.val_zero] at hg
      omega
    have hsum := val_sub_add_val_sub hne
    have hnotR : P.start L ∉ arcSet (P.start R) (P.len R) := by
      have h1 : (P.start L - P.start R).val = (P.start L - P.start S).val := by
        rw [hstR]
      rw [mem_arcSet]
      intro hlt
      omega
    obtain ⟨v, hv⟩ := P.out_nonempty (P.start L)
    have hvL : v ∈ L := P.leftmost_atom hL hv
    have hvR : v ∉ R := by
      rcases atom_subset_or_disjoint (P.out_atom (P.start L)) hR with h | h
      · exact absurd ((P.outside_eq_arc R hR _).mp h) hnotR
      · exact Finset.disjoint_left.mp h hv
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvL, hvR⟩⟩
  · have h1 : (P.start R - P.start L).val = (P.start S - P.start L).val := by
      rw [hstR]
    rw [mem_arcSet]
    omega

/-- **KKO22 Lemma 5.3 at the polygon points, all configurations**: if the
tree does not meet `δ(S)` exactly twice, a bad event occurs at one of
`S`'s two polygon points, stated with the events' own witness data.

The proper configuration routes through Lemma 5.7's geometry
(`bad_event_at_polygon_points` with `L ∩ R = S` and the six disjointness
facts); each degenerate one routes through `S`'s own trichotomy, with
Lemma 5.1's arrow equalities and witness uniqueness carrying the
disjuncts into the events. -/
theorem occursLeft_or_occursRight_of_cut_card_ne_two
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hS : S ∈ 𝒞)
    (hboth : P.CrossedOnBothSides S)
    {L LL LR R RL RR : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hLp : P.IsLp (P.rightPoint S) L) (hLL : P.IsSL L LL) (hLR : P.IsSR L LR)
    (hRp : P.IsRp (P.leftPoint S) R) (hRL : P.IsSL R RL) (hRR : P.IsSR R RR)
    (hT : (cutEdges S ∩ T).card ≠ 2) :
    OccursLeft R RL RR T ∨ OccursRight L LL LR T := by
  classical
  have hLmem := hLp.1
  have hRmem := hRp.1
  have hptL : P.rightPoint S = P.rightPoint L := hLp.2.1.symm
  have hstR : P.start S = P.start R := hRp.2.1.symm
  have hlenL : P.len S ≤ P.len L := hLp.2.2.2 S hS rfl hboth
  have hlenR : P.len S ≤ P.len R := hRp.2.2.2 S hS rfl hboth
  have hsubL : S ⊆ L := P.subset_of_shared_rightPoint hS hLmem hptL hlenL
  have hsubR : S ⊆ R := P.subset_of_shared_leftPoint hS hRmem hstR hlenR
  obtain ⟨SL, hSL⟩ := P.exists_isSL hboth.1
  obtain ⟨SR, hSR⟩ := P.exists_isSR hboth.2
  -- Lemma 5.1, both sides
  have hSLR : P.IsSL R SL :=
    P.isSL_of_shared_leftPoint' hS hRmem hsubR hstR hSL
  have hSLeq : SL = RL := PolygonRep.IsSL.unique P hRmem hSLR hRL
  have hEleft : PolygonRep.arrowLeft S SL = PolygonRep.arrowLeft R RL := by
    rw [← hSLeq]
    exact P.arrowLeft_eq_of_shared_leftPoint hx hη0 (by linarith) hC hS hRmem
      hSL.1 hsubR hstR hSL.2.1
  have hSRL : P.IsSR L SR :=
    P.isSR_of_shared_rightPoint' hS hLmem hsubL hptL hlenL hSR
  have hSReq : SR = LR := PolygonRep.IsSR.unique P hLmem hSRL hLR
  have hEright : PolygonRep.arrowRight S SR = PolygonRep.arrowRight L LR := by
    rw [← hSReq]
    exact P.arrowRight_eq_of_shared_rightPoint hx hη0 (by linarith) hC hS hLmem
      hSR.1 hsubL hptL hlenL hSR.2.1
  have hdS : Disjoint (SL \ S) (SR \ S) :=
    P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hS hSL.1 hSR.1 hSL.2.1 hSR.2.1
  by_cases hLS : L = S
  · -- degenerate: the right event *is* `S`'s trichotomy
    have hLL' : P.IsSL S LL := hLS ▸ hLL
    have hLR' : P.IsSR S LR := hLS ▸ hLR
    have h1 : SL = LL := PolygonRep.IsSL.unique P hS hSL hLL'
    have h2 : SR = LR := PolygonRep.IsSR.unique P hS hSR hLR'
    rcases PolygonRep.bad_event_of_cut_card_ne_two hdS hT with h | h | h
    · exact Or.inl (Or.inl (by rw [← hEleft]; exact h))
    · exact Or.inr (Or.inl (by rw [← hEright]; exact h))
    · refine Or.inr (Or.inr ?_)
      rw [show PolygonRep.arrowCirc L LL LR = PolygonRep.arrowCirc S SL SR by
        rw [hLS, ← h1, ← h2]]
      exact Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  · by_cases hRS : R = S
    · -- degenerate: the left event *is* `S`'s trichotomy
      have hRL' : P.IsSL S RL := hRS ▸ hRL
      have hRR' : P.IsSR S RR := hRS ▸ hRR
      have h1 : SL = RL := PolygonRep.IsSL.unique P hS hSL hRL'
      have h2 : SR = RR := PolygonRep.IsSR.unique P hS hSR hRR'
      rcases PolygonRep.bad_event_of_cut_card_ne_two hdS hT with h | h | h
      · exact Or.inl (Or.inl (by rw [← hEleft]; exact h))
      · exact Or.inr (Or.inl (by rw [← hEright]; exact h))
      · refine Or.inl (Or.inr ?_)
        rw [show PolygonRep.arrowCirc R RL RR = PolygonRep.arrowCirc S SL SR by
          rw [hRS, ← h1, ← h2]]
        exact Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    · -- proper: both extensions are strict, and they cross
      have hlenLs : P.len S < P.len L := lt_of_le_of_ne hlenL fun h =>
        hLS (P.eq_of_rightPoint_eq_of_len_eq hLmem hS hptL.symm h.symm)
      have hlenRs : P.len S < P.len R := lt_of_le_of_ne hlenR fun h =>
        hRS (P.arc_injective R hRmem S hS hstR.symm h.symm)
      have hcrRL := P.crossesOnRight_of_extends_both_sides hS hLmem hRmem
        hsubL hsubR hptL hlenLs hstR hlenRs
      have hinterLR : L ∩ R = S := P.inter_eq_of_extends_both_sides hx hη0
        (by linarith) hC hS hLmem hRmem hsubL hptL hlenLs hstR hlenRs
        hcrRL.1.symm
      exact (PolygonRep.bad_event_at_polygon_points hinterLR hEleft hEright
        hdS
        (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
          (by linarith) hC hLmem hLL.1 hLR.1 hLL.2.1 hLR.2.1)
        (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
          (by linarith) hC hRmem hRL.1 hRR.1 hRL.2.1 hRR.2.1)
        (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
          (by linarith) hC hLmem hLL.1 hRmem hLL.2.1 hcrRL)
        (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0
          (by linarith) hC hRmem hLmem hRR.1 ⟨hcrRL.1.symm, hcrRL.2⟩ hRR.2.1)
        (P.arrowLeft_disjoint_arrowRight hx hη0 hη hC hLmem hRmem hcrRL hLL
          hRR)
        hT).imp
        (fun hl => hl.imp id fun hc =>
          Finset.card_pos.mp (Nat.pos_of_ne_zero hc))
        (fun hr => hr.imp id fun hc =>
          Finset.card_pos.mp (Nat.pos_of_ne_zero hc))

end PolygonRep

/-! ### Corollary 2.12, instantiated at the arrow edge sets

Lemma 5.5's wrappers take the `E→`/`E←` count-one probability as the
hypothesis `hcor`; here it is discharged from Corollary 2.12 (proved in
`SubtreeProbability.lean`).  For `E→(L) = E(L ∩ L_R, L_R ∖ L)` the two
sides are disjoint `2η`-near min cuts (uncrossing) with union the `η`-cut
`L_R`, so the corollary's `ε`-sum is `2η + 2η + η` — exactly KKO's
`1 − 2.5η`. -/

/-- **`hcor` for the right events.** -/
theorem one_sub_le_probEvent_arrowRight (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x))
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {L LR : Finset (Fin n)} (hL : L ∈ 𝒞) (hLR : LR ∈ 𝒞)
    (hcr : Crossing LR L) :
    1 - 2.5 * η
      ≤ μ.probEvent (fun T => (PolygonRep.arrowRight L LR ∩ T).card = 1) := by
  have hA := nearMinCut_inter hx (hC.nearMin L hL) (hC.nearMin LR hLR) hcr.symm
  have hB := nearMinCut_sdiff hx (hC.nearMin LR hLR) (hC.nearMin L hL) hcr
  have hunion : (L ∩ LR) ∪ (LR \ L) = LR := by
    ext w
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hw : w ∈ L
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨h, hw⟩
  have hd : Disjoint (L ∩ LR) (LR \ L) := Finset.disjoint_left.mpr
    fun w hw hw' => (Finset.mem_sdiff.mp hw').2 (Finset.mem_inter.mp hw).1
  have havoid : AvoidsRootEdge e₀ ((L ∩ LR) ∪ (LR \ L)) :=
    hunion.symm ▸ hC.avoids LR hLR
  have hAB : IsNearMinCut x η ((L ∩ LR) ∪ (LR \ L)) :=
    hunion.symm ▸ hC.nearMin LR hLR
  have h := prob_exactlyOne_betweenEdges hx μ havoid hd hA hB hAB
  simp only [PolygonRep.arrowRight]
  linarith

/-- **`hcor` for the left events** — the mirror at `E←(R)`. -/
theorem one_sub_le_probEvent_arrowLeft (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x))
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {R RL : Finset (Fin n)} (hR : R ∈ 𝒞) (hRL : RL ∈ 𝒞)
    (hcl : Crossing RL R) :
    1 - 2.5 * η
      ≤ μ.probEvent (fun T => (PolygonRep.arrowLeft R RL ∩ T).card = 1) := by
  have hA := nearMinCut_inter hx (hC.nearMin R hR) (hC.nearMin RL hRL) hcl.symm
  have hB := nearMinCut_sdiff hx (hC.nearMin RL hRL) (hC.nearMin R hR) hcl
  have hunion : (R ∩ RL) ∪ (RL \ R) = RL := by
    ext w
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hw : w ∈ R
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨h, hw⟩
  have hd : Disjoint (R ∩ RL) (RL \ R) := Finset.disjoint_left.mpr
    fun w hw hw' => (Finset.mem_sdiff.mp hw').2 (Finset.mem_inter.mp hw).1
  have havoid : AvoidsRootEdge e₀ ((R ∩ RL) ∪ (RL \ R)) :=
    hunion.symm ▸ hC.avoids RL hRL
  have hAB : IsNearMinCut x η ((R ∩ RL) ∪ (RL \ R)) :=
    hunion.symm ▸ hC.nearMin RL hRL
  have h := prob_exactlyOne_betweenEdges hx μ havoid hd hA hB hAB
  simp only [PolygonRep.arrowLeft]
  linarith

/-- **The global bad-event index**: a polygon of the family, one of its
polygon points, and a direction — `true` for the right event `B→(p)`,
`false` for the left event `B←(p)`.  Nothing else: the witness cuts live in
the shared chosen payload, so alternate maximizers cannot create duplicate
events. -/
structure BadEventIndex (F : PolygonFamily x η e₀) where
  /-- Which polygon the event belongs to. -/
  poly : Fin F.N
  /-- The active polygon point. -/
  pt : Fin (F.rep poly).m
  /-- The direction: `true` = right (`B→`), `false` = left (`B←`). -/
  dir : Bool

namespace BadEventIndex

variable {F : PolygonFamily x η e₀}

/-- The index is exactly a dependent triple. -/
def equivSigma (F : PolygonFamily x η e₀) :
    BadEventIndex F ≃ Σ i : Fin F.N, Fin (F.rep i).m × Bool where
  toFun b := ⟨b.poly, b.pt, b.dir⟩
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

instance : Fintype (BadEventIndex F) :=
  Fintype.ofEquiv _ (equivSigma F).symm

instance : DecidableEq (BadEventIndex F) :=
  (equivSigma F).decidableEq

/-- Events agree once their three identity fields do (the point compared by
value, so no dependent transport is needed). -/
theorem eq_of_fields {b b' : BadEventIndex F} (hpoly : b.poly = b'.poly)
    (hpt : (b.pt : ℕ) = (b'.pt : ℕ)) (hdir : b.dir = b'.dir) : b = b' := by
  obtain ⟨i, p, d⟩ := b
  obtain ⟨i', p', d'⟩ := b'
  dsimp only at hpoly hpt hdir
  subst hpoly
  rw [Fin.ext hpt, hdir]

/-- The chosen witness payload of an event. -/
noncomputable def witness (b : BadEventIndex F) : EventWitness n :=
  if b.dir then (F.rep b.poly).rightWitness b.pt
  else (F.rep b.poly).leftWitness b.pt

/-- An event is active when its anchor cut exists at its point. -/
def Active (b : BadEventIndex F) : Prop :=
  if b.dir then (F.rep b.poly).RightActive b.pt
  else (F.rep b.poly).LeftActive b.pt

/-- **`E(B)`**, the charged edge set of an event, read off its payload.
Inactive events charge nothing — their junk payload has empty bad-edge
sets — so no activity guard is needed here. -/
noncomputable def Ebad (b : BadEventIndex F) : Finset (Sym2 (Fin n)) :=
  if b.dir then badEdgesRight b.witness.cut b.witness.cutR b.witness.star
  else badEdgesLeft b.witness.cut b.witness.cutL b.witness.star

/-- **The occurrence predicate** of an event, conjoined with activity so
that inactive events never occur (with junk data the raw predicates would
hold vacuously — an arrow count of zero is not one). -/
def Occurs (b : BadEventIndex F) (T : Finset (Sym2 (Fin n))) : Prop :=
  b.Active ∧
    (if b.dir then OccursRight b.witness.cut b.witness.cutL b.witness.cutR T
     else OccursLeft b.witness.cut b.witness.cutL b.witness.cutR T)

theorem not_occurs_of_not_active {b : BadEventIndex F}
    (h : ¬ b.Active) (T : Finset (Sym2 (Fin n))) : ¬ b.Occurs T :=
  fun hocc => h hocc.1

/-! ### Unfolding along the direction -/

theorem witness_of_dir_true {b : BadEventIndex F} (h : b.dir = true) :
    b.witness = (F.rep b.poly).rightWitness b.pt := by
  simp [witness, h]

theorem witness_of_dir_false {b : BadEventIndex F} (h : b.dir = false) :
    b.witness = (F.rep b.poly).leftWitness b.pt := by
  simp [witness, h]

theorem active_of_dir_true {b : BadEventIndex F} (h : b.dir = true) :
    b.Active ↔ (F.rep b.poly).RightActive b.pt := by
  simp [Active, h]

theorem active_of_dir_false {b : BadEventIndex F} (h : b.dir = false) :
    b.Active ↔ (F.rep b.poly).LeftActive b.pt := by
  simp [Active, h]

theorem ebad_of_dir_true {b : BadEventIndex F} (h : b.dir = true) :
    b.Ebad = badEdgesRight ((F.rep b.poly).rightWitness b.pt).cut
      ((F.rep b.poly).rightWitness b.pt).cutR
      ((F.rep b.poly).rightWitness b.pt).star := by
  simp [Ebad, witness, h]

theorem ebad_of_dir_false {b : BadEventIndex F} (h : b.dir = false) :
    b.Ebad = badEdgesLeft ((F.rep b.poly).leftWitness b.pt).cut
      ((F.rep b.poly).leftWitness b.pt).cutL
      ((F.rep b.poly).leftWitness b.pt).star := by
  simp [Ebad, witness, h]

theorem occurs_of_dir_true {b : BadEventIndex F} (h : b.dir = true)
    (hact : b.Active) :
    b.Occurs = fun T => OccursRight ((F.rep b.poly).rightWitness b.pt).cut
      ((F.rep b.poly).rightWitness b.pt).cutL
      ((F.rep b.poly).rightWitness b.pt).cutR T := by
  funext T
  simp [Occurs, witness, h, hact]

theorem occurs_of_dir_false {b : BadEventIndex F} (h : b.dir = false)
    (hact : b.Active) :
    b.Occurs = fun T => OccursLeft ((F.rep b.poly).leftWitness b.pt).cut
      ((F.rep b.poly).leftWitness b.pt).cutL
      ((F.rep b.poly).leftWitness b.pt).cutR T := by
  funext T
  simp [Occurs, witness, h, hact]

/-- **Inactive events charge nothing**: their payload is the junk tuple,
whose bad-edge sets are empty. -/
theorem ebad_eq_empty_of_not_active {b : BadEventIndex F}
    (h : ¬ b.Active) : b.Ebad = ∅ := by
  cases hdir : b.dir
  · rw [ebad_of_dir_false hdir,
      (F.rep b.poly).leftWitness_of_not_active
        (fun ha => h ((active_of_dir_false hdir).mpr ha))]
    exact badEdgesLeft_empty
  · rw [ebad_of_dir_true hdir,
      (F.rep b.poly).rightWitness_of_not_active
        (fun ha => h ((active_of_dir_true hdir).mpr ha))]
    exact badEdgesRight_empty

/-- The contrapositive, in the form the counting uses: an event that
charges an edge is active. -/
theorem active_of_mem_ebad {b : BadEventIndex F} {e : Sym2 (Fin n)}
    (h : e ∈ b.Ebad) : b.Active := by
  by_contra hact
  rw [ebad_eq_empty_of_not_active hact] at h
  exact absurd h (Finset.notMem_empty e)

/-- `E(B)` in payload form, right events. -/
theorem ebad_witness_of_dir_true {b : BadEventIndex F} (h : b.dir = true) :
    b.Ebad = badEdgesRight b.witness.cut b.witness.cutR b.witness.star := by
  simp [Ebad, h]

/-- `E(B)` in payload form, left events. -/
theorem ebad_witness_of_dir_false {b : BadEventIndex F} (h : b.dir = false) :
    b.Ebad = badEdgesLeft b.witness.cut b.witness.cutL b.witness.star := by
  simp [Ebad, h]

/-! ### The payload's properties, transported to a fixed polygon

The counting and charging arguments run inside the polygon `i` an event
belongs to, while the payload's specification is stated over
`F.rep b.poly`.  The two agree along `b.poly = i`, and the bundles below
perform that transport once — by substitution, per event, with the anchor
point compared by value so no dependent cast appears. -/

/-- The right payload's specification over the event's polygon: memberships,
Definition 4.17 data, the chosen star, and the anchor identity
`rightPoint L(p) = p` (by value). -/
theorem witness_spec_right_at {b : BadEventIndex F} {i : Fin F.N}
    (hpoly : b.poly = i) (hdir : b.dir = true) (hact : b.Active) :
    b.witness.cut ∈ F.comp i ∧
      (F.rep i).IsSL b.witness.cut b.witness.cutL ∧
      (F.rep i).IsSR b.witness.cut b.witness.cutR ∧
      (F.rep i).IsChosenLStar (b.witness.cut ∩ b.witness.cutR)
        ((F.rep i).start b.witness.cutR) b.witness.star ∧
      (((F.rep i).rightPoint b.witness.cut : ℕ) = (b.pt : ℕ)) := by
  subst hpoly
  have hract := (active_of_dir_true hdir).mp hact
  have hw := witness_of_dir_true (b := b) hdir
  obtain ⟨h1, h2, h3, h4⟩ := (F.rep b.poly).rightWitness_spec hract
  rw [hw]
  exact ⟨h1.1, h2, h3, h4, congrArg Fin.val h1.2.1⟩

/-- The left payload's specification over the event's polygon — the mirror,
with the anchor identity `leftPoint R(p) = p` (by value). -/
theorem witness_spec_left_at {b : BadEventIndex F} {i : Fin F.N}
    (hpoly : b.poly = i) (hdir : b.dir = false) (hact : b.Active) :
    b.witness.cut ∈ F.comp i ∧
      (F.rep i).IsSL b.witness.cut b.witness.cutL ∧
      (F.rep i).IsSR b.witness.cut b.witness.cutR ∧
      (F.rep i).IsChosenRStar (b.witness.cut ∩ b.witness.cutL)
        ((F.rep i).start b.witness.cut)
        ((F.rep i).len b.witness.cutL
          - ((F.rep i).start b.witness.cut
              - (F.rep i).start b.witness.cutL).val) b.witness.star ∧
      (((F.rep i).leftPoint b.witness.cut : ℕ) = (b.pt : ℕ)) := by
  subst hpoly
  have hlact := (active_of_dir_false hdir).mp hact
  have hw := witness_of_dir_false (b := b) hdir
  obtain ⟨h1, h2, h3, h4⟩ := (F.rep b.poly).leftWitness_spec hlact
  rw [hw]
  exact ⟨h1.1, h2, h3, h4, congrArg Fin.val h1.2.1⟩

/-! ### `hcharge`: a charged edge separates two non-root atoms -/

/-- **Theorem 5.2's `hcharge`.**  An edge charged by an event has one
endpoint in the anchor cut and the other in the crosser but outside the
anchor, so the two endpoints inhabit distinct atoms of the event's
component, neither of them the root. -/
theorem separates_of_mem_ebad {b : BadEventIndex F} {u v : Fin n}
    (h : s(u, v) ∈ b.Ebad) : F.Separates b.poly u v := by
  have hact := active_of_mem_ebad h
  cases hdir : b.dir
  · have hspec := witness_spec_left_at rfl hdir hact
    rw [ebad_witness_of_dir_false hdir] at h
    simp only [badEdgesLeft] at h
    obtain ⟨a', ha', b', hb', hab⟩ := PolygonRep.mem_betweenEdges_iff.mp h
    have ha'cut : a' ∈ b.witness.cut :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp ha').1).1
    have hb'L : b' ∈ b.witness.cutL := (Finset.mem_sdiff.mp hb').1
    have hb'cut : b' ∉ b.witness.cut := fun hc =>
      (Finset.mem_sdiff.mp hb').2 (Finset.mem_inter.mpr ⟨hc, hb'L⟩)
    have hsep := (F.rep b.poly).atomOf_ne_of_charged hspec.1 hspec.2.1.1
      ha'cut hb'L hb'cut
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hsep.1, hsep.2.1, hsep.2.2⟩
    · exact ⟨hsep.1.symm, hsep.2.2, hsep.2.1⟩
  · have hspec := witness_spec_right_at rfl hdir hact
    rw [ebad_witness_of_dir_true hdir] at h
    simp only [badEdgesRight] at h
    obtain ⟨a', ha', b', hb', hab⟩ := PolygonRep.mem_betweenEdges_iff.mp h
    have ha'cut : a' ∈ b.witness.cut :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp ha').1).1
    have hb'R : b' ∈ b.witness.cutR := (Finset.mem_sdiff.mp hb').1
    have hb'cut : b' ∉ b.witness.cut := fun hc =>
      (Finset.mem_sdiff.mp hb').2 (Finset.mem_inter.mpr ⟨hc, hb'R⟩)
    have hsep := (F.rep b.poly).atomOf_ne_of_charged hspec.1 hspec.2.2.1.1
      ha'cut hb'R hb'cut
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hsep.1, hsep.2.1, hsep.2.2⟩
    · exact ⟨hsep.1.symm, hsep.2.2, hsep.2.1⟩

/-! ### `hlocal`: at most four events of one polygon charge an edge -/

/-- **Theorem 5.2's `hlocal`**, for a named edge: the events of polygon `i`
charging `{u, v}` number at most four.  This is
`card_badEvents_le_four_of_polygon` instantiated at the index, with the
payload's transported specification supplying every hypothesis and
`eq_of_fields` turning the anchor identities into the injectivity. -/
theorem card_polyFilter_ebad_le_four (F : PolygonFamily x η e₀)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (u v : Fin n) (i : Fin F.N) :
    (Finset.univ.filter fun b : BadEventIndex F =>
      b.poly = i ∧ s(u, v) ∈ b.Ebad).card ≤ 4 := by
  classical
  refine (F.rep i).card_badEvents_le_four_of_polygon (u := u) (v := v)
    (dir := fun b => b.dir) (L := fun b => b.witness.cut)
    (LR := fun b => b.witness.cutR) (Lstar := fun b => b.witness.star)
    (R := fun b => b.witness.cut) (RL := fun b => b.witness.cutL)
    (Rstar := fun b => b.witness.star) hx hη0 hη (F.isComp i)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro b hb hdir
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    exact (witness_spec_right_at hpoly hdir (active_of_mem_ebad hbe)).1
  · intro b hb hdir
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    exact (witness_spec_right_at hpoly hdir (active_of_mem_ebad hbe)).2.2.1
  · intro b hb hdir
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    exact (witness_spec_right_at hpoly hdir (active_of_mem_ebad hbe)).2.2.2.1
  · intro b hb hdir
    obtain ⟨-, -, hbe⟩ := Finset.mem_filter.mp hb
    rwa [ebad_witness_of_dir_true hdir] at hbe
  · intro b hb b' hb' hdir hdir' hpt
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    obtain ⟨-, hpoly', hbe'⟩ := Finset.mem_filter.mp hb'
    have h1 := (witness_spec_right_at hpoly hdir
      (active_of_mem_ebad hbe)).2.2.2.2
    have h2 := (witness_spec_right_at hpoly' hdir'
      (active_of_mem_ebad hbe')).2.2.2.2
    refine eq_of_fields (hpoly.trans hpoly'.symm) ?_ (hdir.trans hdir'.symm)
    rw [← h1, ← h2]
    exact congrArg Fin.val hpt
  · intro b hb hdir
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    exact (witness_spec_left_at hpoly hdir (active_of_mem_ebad hbe)).1
  · intro b hb hdir
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    exact (witness_spec_left_at hpoly hdir (active_of_mem_ebad hbe)).2.1
  · intro b hb hdir
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    exact (witness_spec_left_at hpoly hdir (active_of_mem_ebad hbe)).2.2.2.1
  · intro b hb hdir
    obtain ⟨-, -, hbe⟩ := Finset.mem_filter.mp hb
    rwa [ebad_witness_of_dir_false hdir] at hbe
  · intro b hb b' hb' hdir hdir' hpt
    obtain ⟨-, hpoly, hbe⟩ := Finset.mem_filter.mp hb
    obtain ⟨-, hpoly', hbe'⟩ := Finset.mem_filter.mp hb'
    have h1 := (witness_spec_left_at hpoly hdir
      (active_of_mem_ebad hbe)).2.2.2.2
    have h2 := (witness_spec_left_at hpoly' hdir'
      (active_of_mem_ebad hbe')).2.2.2.2
    refine eq_of_fields (hpoly.trans hpoly'.symm) ?_ (hdir.trans hdir'.symm)
    rw [← h1, ← h2]
    exact congrArg Fin.val hpt

/-- **`hlocal` for an arbitrary edge** — diagonal elements charge nothing,
so the named-edge form covers everything. -/
theorem card_polyFilter_ebad_le_four' (F : PolygonFamily x η e₀)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (e : Sym2 (Fin n)) (i : Fin F.N) :
    (Finset.univ.filter fun b : BadEventIndex F =>
      b.poly = i ∧ e ∈ b.Ebad).card ≤ 4 := by
  induction e using Sym2.ind with
  | _ u v => exact card_polyFilter_ebad_le_four F hx hη0 hη u v i

/-! ### `hprob`: every event occurs with probability at most `4.5η` -/

/-- The occurrence predicate in payload form, right events. -/
theorem occurs_witness_of_dir_true {b : BadEventIndex F} (h : b.dir = true)
    (hact : b.Active) :
    b.Occurs = fun T =>
      OccursRight b.witness.cut b.witness.cutL b.witness.cutR T := by
  funext T
  simp [Occurs, h, hact]

/-- The occurrence predicate in payload form, left events. -/
theorem occurs_witness_of_dir_false {b : BadEventIndex F} (h : b.dir = false)
    (hact : b.Active) :
    b.Occurs = fun T =>
      OccursLeft b.witness.cut b.witness.cutL b.witness.cutR T := by
  funext T
  simp [Occurs, h, hact]

/-- **Theorem 5.2's `hprob`.**  At an active event this is Lemma 5.5 with
`hcor` discharged from Corollary 2.12; an inactive event never occurs, so
its probability is zero. -/
theorem probEvent_occurs_le (F : PolygonFamily x η e₀) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (μ : TreeDist n (e₀.restrict x))
    (b : BadEventIndex F) : μ.probEvent b.Occurs ≤ 4.5 * η := by
  by_cases hact : b.Active
  · cases hdir : b.dir
    · rw [occurs_witness_of_dir_false hdir hact]
      have hspec := witness_spec_left_at rfl hdir hact
      exact probEvent_occursLeft_le μ hx hη0 (by linarith) (F.rep b.poly)
        (F.isComp b.poly) hspec.1 hspec.2.1.1 hspec.2.2.1.1
        hspec.2.1.2.1 hspec.2.2.1.2.1
        (one_sub_le_probEvent_arrowLeft hx μ (F.isComp b.poly) hspec.1
          hspec.2.1.1 hspec.2.1.2.1.1)
    · rw [occurs_witness_of_dir_true hdir hact]
      have hspec := witness_spec_right_at rfl hdir hact
      exact probEvent_occursRight_le μ hx hη0 (by linarith) (F.rep b.poly)
        (F.isComp b.poly) hspec.1 hspec.2.1.1 hspec.2.2.1.1
        hspec.2.1.2.1 hspec.2.2.1.2.1
        (one_sub_le_probEvent_arrowRight hx μ (F.isComp b.poly) hspec.1
          hspec.2.2.1.1 hspec.2.2.1.2.1.1)
  · have hocc : b.Occurs = fun _ => False := by
      funext T
      exact propext ⟨fun h => hact h.1, False.elim⟩
    have h0 : μ.probEvent (fun _ => False) = 0 := by
      simp only [TreeDist.probEvent]
      rw [Finset.filter_congr_decidable]
      simp
    rw [hocc, h0]
    linarith

end BadEventIndex

end TSPGap

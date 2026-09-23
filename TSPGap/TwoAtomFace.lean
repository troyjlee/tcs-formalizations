/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleSetup

/-!
# Conditioning two atoms to be trees

The two-atom analogue of `ThreeAtomFace.lean`.  The relevant maximum face is

`twoAtomInternal u v := internalEdges u ∪ internalEdges v`

at budget

`twoAtomBudget u v := (|u| - 1) + (|v| - 1)`.

For a spanning tree and two nonempty disjoint atoms, this face is full exactly
when both atoms induce trees.  Once they do, the union `u ∪ v` induces a
tree exactly when the supported bundle between them is present.  The latter
equivalence needs `SupportComplete`: an abstract bundle may omit ambient
zero-marginal edges between the atoms, so support completeness is what turns
the full between-edge count into the bundle count.

## Main results

* `twoAtomInternal`, `twoAtomBudget`.
* `card_inter_twoAtom_split`, `card_inter_twoAtom_le`.
* `card_inter_twoAtom_eq_iff` — the maximum face is the two tree events.
* `inducesTreeOn_union_iff_bundle_present` — after the two tree events, the
  union-tree event is the bundle-present face on supported trees.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### The two-atom maximum face -/

/-- The internal edges of the two atoms, excluding the edges between them. -/
def twoAtomInternal (u v : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  internalEdges u ∪ internalEdges v

/-- The largest number of internal edges two nonempty atoms can carry in a tree. -/
def twoAtomBudget (u v : Finset (Fin n)) : ℕ :=
  (u.card - 1) + (v.card - 1)

/-- The count on the two-atom face splits into the two internal-edge counts. -/
theorem card_inter_twoAtom_split {T : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (huv : Disjoint u v) :
    (T ∩ twoAtomInternal u v).card
      = (internalEdges u ∩ T).card + (internalEdges v ∩ T).card := by
  classical
  have hd : Disjoint (T ∩ internalEdges u) (T ∩ internalEdges v) :=
    (disjoint_internalEdges huv).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [twoAtomInternal, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint hd]
  rw [Finset.inter_comm T (internalEdges u), Finset.inter_comm T (internalEdges v)]

/-- A spanning tree meets the two-atom internal face in at most its budget. -/
theorem card_inter_twoAtom_le {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {u v : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v) :
    (T ∩ twoAtomInternal u v).card ≤ twoAtomBudget u v := by
  have hu := card_internal_inter_add_one_le hT hune
  have hv := card_internal_inter_add_one_le hT hvne
  have hsplit := card_inter_twoAtom_split (T := T) huv
  rw [twoAtomBudget, hsplit]
  omega

/-- **The two-atom face event is exactly the two tree events.** -/
theorem card_inter_twoAtom_eq_iff {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {u v : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v) :
    (T ∩ twoAtomInternal u v).card = twoAtomBudget u v
      ↔ InducesTreeOn u T ∧ InducesTreeOn v T := by
  have hu := card_internal_inter_add_one_le hT hune
  have hv := card_internal_inter_add_one_le hT hvne
  have hsplit := card_inter_twoAtom_split (T := T) huv
  rw [inducesTreeOn_iff_card hT, inducesTreeOn_iff_card hT,
    twoAtomBudget, hsplit]
  have hu1 : 1 ≤ u.card := Finset.card_pos.mpr hune
  have hv1 : 1 ≤ v.card := Finset.card_pos.mpr hvne
  constructor
  · intro h
    exact ⟨by omega, by omega⟩
  · rintro ⟨hu', hv'⟩
    omega

/-! ### The union tree is the bundle-present face -/

/-- On a supported spanning tree where `u` and `v` already induce trees,
their union induces a tree exactly when the support-complete bundle between
them is present once.

The reverse implication only needs that a present bundle edge lies between
the atoms.  The forward implication uses the support half of
`SupportComplete` to rule out the unique `u`–`v` tree edge living outside the
abstract bundle. -/
theorem inducesTreeOn_union_iff_bundle_present
    {w : Finset (Sym2 (Fin n)) → ℝ} {E : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (hSC : SupportComplete w E u v)
    {T : Finset (Sym2 (Fin n))} (hwT : w T ≠ 0)
    (hT : IsSpanningTree n T) (hu : InducesTree u T) (hv : InducesTree v T)
    (huv : Disjoint u v) :
    InducesTreeOn (u ∪ v) T ↔ (T ∩ E).card = 1 := by
  have hTu : InducesTreeOn u T := ⟨hT, hu⟩
  have hTv : InducesTreeOn v T := ⟨hT, hv⟩
  have hucard := (inducesTreeOn_iff_card hT u).mp hTu
  have hvcard := (inducesTreeOn_iff_card hT v).mp hTv
  have hbundle := inter_bundle_eq_of_supportComplete hSC hwT
  constructor
  · intro hunion
    have hunioncard := (inducesTreeOn_iff_card hT (u ∪ v)).mp hunion
    have hbetween := card_between_eq_one_of_counts huv hucard hvcard hunioncard
    rw [hbundle]
    simpa [Finset.inter_comm] using hbetween
  · intro hpresent
    have hbetween : (betweenEdges u v ∩ T).card = 1 := by
      rw [Finset.inter_comm, ← hbundle]
      exact hpresent
    have hsplit := card_internal_union_inter huv T
    have huvcard : (u ∪ v).card = u.card + v.card :=
      Finset.card_union_of_disjoint huv
    rw [inducesTreeOn_iff_card hT]
    omega

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MainPaymentCore
import TSPGap.RefinedPolygonCompatibility

/-!
# Two presentations of one cut have the same polygon partition up to reversal

`Hierarchy.Presents N S` fixes the root `a₀ = Sᶜ` and the *set* of atoms (the
children of `S`) but not their cyclic order.  The payment core
(`PaymentCertificate.paymentCore`) needs the polygon partition `A, B, C` of a
near-cycle cut to be the same, up to swapping `A` and `B`, for every near-cycle
presenting it (`NearCycle.PartitionCompatible`).

No uniqueness of the cyclic order is needed.  The root sees at least `1 − ε` of
each **boundary** atom `a₁, a_{m−1}` (Theorem A.3's first item, at `i = 0` and
`i = m − 1`) and at most `ε` of all the **middle** atoms together (its third
item).  So a boundary atom of one presentation, being some atom of the other,
cannot be a middle atom there when `ε < 1/2`; the two boundary atoms therefore
agree up to reversal, and with them `A = E(a₀, a₁)`, `B = E(a_{m−1}, a₀)` up to
swap, and `C = δ(a₀) ∖ (A ∪ B)` exactly.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

namespace NearCycle

variable (N : NearCycle x εη)

/-- Distinct indices carry distinct atoms. -/
theorem atom_ne_of_ne {i j : Fin (N.k + 3)} (hij : i ≠ j) : N.atom i ≠ N.atom j := by
  intro h
  have hd := N.atom_disjoint i j hij
  rw [h] at hd
  exact (N.atom_nonempty j).ne_empty (disjoint_self.mp hd)

/-- An atom that is neither the root nor a boundary atom is a middle atom. -/
theorem atom_subset_middleAtoms {t : Fin (N.k + 3)} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htl : t ≠ N.lastIdx) : N.atom t ⊆ middleAtoms N.k N.atom := by
  intro v hv
  refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hv⟩
  · have h0 : t.val ≠ 0 := fun h => ht0 (Fin.ext h)
    have h1 : t.val ≠ 1 := fun h => ht1 (Fin.ext (by rw [h, Fin.val_one]))
    omega
  · have hl : t.val ≠ N.k + 2 := fun h => htl (Fin.ext (by rw [h, NearCycle.lastIdx, Fin.val_last]))
    have := t.isLt
    omega

/-- The root sees at most `ε` of a middle atom. -/
theorem sum_root_atom_le_of_middle (hx : ∀ e, 0 ≤ x e) {t : Fin (N.k + 3)} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (htl : t ≠ N.lastIdx) :
    ∑ e ∈ betweenEdges N.root (N.atom t), x e ≤ εη := by
  have hsub : betweenEdges N.root (N.atom t)
      ⊆ betweenEdges (N.atom 0) (middleAtoms N.k N.atom) := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
    exact mem_betweenEdges_iff.mpr ⟨a, ha, b, N.atom_subset_middleAtoms ht0 ht1 htl hb, rfl⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx e)).trans N.root_middle_le

/-- An atom the root sees with mass at least `1 − ε` is a boundary atom (`ε < 1/2`). -/
theorem eq_one_or_lastIdx_of_root_mass (hx : ∀ e, 0 ≤ x e) (hε : εη < 1 / 2)
    {t : Fin (N.k + 3)} (ht0 : t ≠ 0)
    (h : 1 - εη ≤ ∑ e ∈ betweenEdges N.root (N.atom t), x e) : t = 1 ∨ t = N.lastIdx := by
  by_contra hcon
  push Not at hcon
  have := N.sum_root_atom_le_of_middle hx ht0 hcon.1 hcon.2
  linarith

/-- The root sees at least `1 − ε` of the leftmost atom. -/
theorem one_sub_le_sum_root_atom_one : 1 - εη ≤ ∑ e ∈ betweenEdges N.root (N.atom 1), x e := by
  have := N.adjacent_mass 0
  rwa [zero_add] at this

/-- The root sees at least `1 − ε` of the rightmost atom. -/
theorem one_sub_le_sum_root_atom_lastIdx :
    1 - εη ≤ ∑ e ∈ betweenEdges N.root (N.atom N.lastIdx), x e := by
  have := N.adjacent_mass N.lastIdx
  rwa [N.lastIdx_add_one, betweenEdges_comm] at this

end NearCycle

/-- **Two presentations of one cut agree up to reversal**: the polygon partitions of any
two near-cycles presenting `S` coincide up to swapping `A` and `B`. -/
theorem Hierarchy.Presents.partitionCompatible {H : Hierarchy x e₀ εη} (hx : ∀ e, 0 ≤ x e)
    (hε : εη < 1 / 2) {S : Finset (Fin n)} {N M : NearCycle x εη}
    (hN : H.Presents N S) (hM : H.Presents M S) : N.PartitionCompatible M := by
  have hroot : N.root = M.root := by rw [hN.1, hM.1]
  have hroot' : N.atom 0 = M.atom 0 := hroot
  -- `M`'s boundary atoms are atoms of `N` that the root sees heavily
  have hbd : ∀ t : Fin (M.k + 3), t ≠ 0 →
      1 - εη ≤ ∑ e ∈ betweenEdges M.root (M.atom t), x e →
      M.atom t = N.atom 1 ∨ M.atom t = N.atom N.lastIdx := by
    intro t ht hmass
    obtain ⟨t', ht'0, ht'eq⟩ := (hN.2 _).mp (hM.atom_isChildOf ht)
    rw [← ht'eq, ← hroot] at hmass
    rcases N.eq_one_or_lastIdx_of_root_mass hx hε ht'0 hmass with h | h
    · exact Or.inl (by rw [← ht'eq, h])
    · exact Or.inr (by rw [← ht'eq, h])
  have h1 := hbd 1 Fin.zero_lt_one.ne' M.one_sub_le_sum_root_atom_one
  have hL := hbd M.lastIdx (Ne.symm M.zero_ne_lastIdx) M.one_sub_le_sum_root_atom_lastIdx
  have hne : M.atom 1 ≠ M.atom M.lastIdx := M.atom_ne_of_ne M.one_ne_lastIdx
  rcases h1 with h1 | h1 <;> rcases hL with hL | hL
  · exact absurd (h1.trans hL.symm) hne
  · -- same orientation
    left
    have hA : N.partA = M.partA := by
      rw [NearCycle.partA_eq, NearCycle.partA_eq, hroot', h1]
    have hB : N.partB = M.partB := by
      rw [NearCycle.partB_eq, NearCycle.partB_eq, hroot', hL]
    refine ⟨hA, hB, ?_⟩
    unfold NearCycle.partC
    rw [hroot, hA, hB]
  · -- reversed
    right
    have hA : N.partA = M.partB := by
      rw [NearCycle.partA_eq, NearCycle.partB_eq, hroot', hL, betweenEdges_comm]
    have hB : N.partB = M.partA := by
      rw [NearCycle.partB_eq, NearCycle.partA_eq, hroot', h1, betweenEdges_comm]
    refine ⟨hA, hB, ?_⟩
    unfold NearCycle.partC
    rw [hroot, hA, hB, Finset.union_comm]
  · exact absurd (h1.trans hL.symm) hne

end TSPGap

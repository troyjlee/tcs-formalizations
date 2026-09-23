/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonIndep

/-!
# KKO21 Observation 4.32

For a polygon cut `S` and a descendant cut `u`, `δ(u) ∩ δ(S)` lies inside one
of the three parts `A`, `B`, `C` of the polygon partition of `S`.

Only the **weak** form is proved — a disjunction of three containments, with
no nonemptiness and no "exactly one" clause — because that is all Corollaries
5.9(iii)–5.11 consume.

The argument is entirely laminar.  `Hierarchy.exists_child_superset`
(`TheoremB3`) puts the descendant inside a single child `a` of `S`; the child
is `N.atom t` for some `t ≠ 0` by `H.Presents N S`; and then every edge of
`δ(u) ∩ δ(S)` runs from the root atom `a₀` to `a ⊆ atom t`
(`cut_inter_root_subset_between`), so it lies in `E(a₀, a_t)`, which is `A`
when `t = 1`, `B` when `t` is last, and inside `C` otherwise — the last case
because an edge of `E(a₀, a_t)` cannot also join `a₀` to `a₁` or to `a_last`
when the atoms are disjoint.

The direct consumer is `disjoint_partA_or_partB`: whichever part contains
`δ(u) ∩ δ(S)`, at least one of `A`, `B` misses `δ(u)` entirely.  That is what
makes the outside contribution to `δ(u)_T` a single Bernoulli under the
max-flow event, `A_T = B_T = 1` forcing at most one edge.  Alongside it,
`cutEdges_subset_internal_union_cut` matches Corollary 5.9(iii)'s domain
hypothesis `F ⊆ E(S) ∪ δ(S)`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Edges of a subcut split into internal and crossing ones -/

/-- `δ(u) ⊆ E(S) ∪ δ(S)` for `u ⊆ S`: Corollary 5.9(iii)'s domain. -/
theorem cutEdges_subset_internal_union_cut {u S : Finset (Fin n)} (huS : u ⊆ S) :
    cutEdges u ⊆ internalEdges S ∪ cutEdges S := by
  intro e he
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_cutEdges_iff''.mp he
  rw [Finset.mem_compl] at hq
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  by_cases hqS : q ∈ S
  · refine Finset.mem_union_left _ ?_
    rw [mem_internalEdges]
    refine ⟨fun hd => hpq (Sym2.mk_isDiag_iff.mp hd), ?_⟩
    rw [forall_mem_sym2_iff]
    exact ⟨huS hp, hqS⟩
  · exact Finset.mem_union_right _
      (mem_cutEdges_iff''.mpr ⟨p, huS hp, q, Finset.mem_compl.mpr hqS, rfl⟩)

/-! ### The near-cycle half -/

namespace NearCycle

variable {ε : ℝ} (P : NearCycle x ε)

theorem lastIdx_add_one : P.lastIdx + 1 = 0 := by
  simp [NearCycle.lastIdx]

theorem partA_eq : P.partA = betweenEdges (P.atom 0) (P.atom 1) := by
  unfold NearCycle.partA NearCycle.group
  rw [zero_add]

theorem partB_eq : P.partB = betweenEdges (P.atom P.lastIdx) (P.atom 0) := by
  unfold NearCycle.partB NearCycle.group
  rw [P.lastIdx_add_one]

/-- **Every crossing edge of a descendant of `a_t` joins `a₀` to `a_t`.** -/
theorem cut_inter_root_subset_between {S' : Finset (Fin n)} {t : Fin (P.k + 3)}
    (ht : t ≠ 0) (hS' : S' ⊆ P.atom t) :
    cutEdges S' ∩ cutEdges P.root ⊆ betweenEdges (P.atom 0) (P.atom t) := by
  intro e he
  obtain ⟨heS', heroot⟩ := Finset.mem_inter.mp he
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_cutEdges_iff''.mp heroot
  rw [Finset.mem_compl] at hq
  -- the root end is not in `S'`, so the other end is
  have hdisj : Disjoint (P.atom t) P.root := P.atom_disjoint t 0 ht
  have hqS' : q ∈ S' := by
    obtain ⟨a, ha, b, hb, hab⟩ := mem_cutEdges_iff''.mp heS'
    rw [Finset.mem_compl] at hb
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (Finset.disjoint_left.mp hdisj (hS' ha) hp) not_false
    · exact ha
  exact NearCycle.mem_betweenEdges_iff'.mpr ⟨p, hp, q, hS' hqS', rfl⟩

/-- An edge joining `a₀` to `a_t` with `t ∉ {0, s}` is not in the group `E(a₀, a_s)`. -/
theorem notMem_between_of_ne {t s : Fin (P.k + 3)} (ht : t ≠ 0) (hts : t ≠ s)
    {e : Sym2 (Fin n)} (he : e ∈ betweenEdges (P.atom 0) (P.atom t)) :
    e ∉ betweenEdges (P.atom 0) (P.atom s) := by
  intro hc
  obtain ⟨p, hp, q, hq, rfl⟩ := NearCycle.mem_betweenEdges_iff'.mp he
  obtain ⟨u, hu, v, hv, huv⟩ := NearCycle.mem_betweenEdges_iff'.mp hc
  rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (Finset.disjoint_left.mp (P.atom_disjoint t s hts) hq hv) not_false
  · exact absurd (Finset.disjoint_left.mp (P.atom_disjoint t 0 ht) hq hu) not_false

/-- **KKO21 Observation 4.32, weak form**, at the near-cycle. -/
theorem observation_4_32_atom {S' : Finset (Fin n)} {t : Fin (P.k + 3)}
    (ht : t ≠ 0) (hS' : S' ⊆ P.atom t) :
    cutEdges S' ∩ cutEdges P.root ⊆ P.partA
      ∨ cutEdges S' ∩ cutEdges P.root ⊆ P.partB
      ∨ cutEdges S' ∩ cutEdges P.root ⊆ P.partC := by
  have hsub := P.cut_inter_root_subset_between ht hS'
  by_cases h1 : t = 1
  · subst h1
    exact Or.inl (by rw [P.partA_eq]; exact hsub)
  by_cases hl : t = P.lastIdx
  · subst hl
    refine Or.inr (Or.inl ?_)
    rw [P.partB_eq, betweenEdges_comm (P.atom P.lastIdx) (P.atom 0)]
    exact hsub
  -- the middle atoms
  refine Or.inr (Or.inr fun e he => ?_)
  obtain ⟨-, heroot⟩ := Finset.mem_inter.mp he
  refine Finset.mem_sdiff.mpr ⟨heroot, fun hc => ?_⟩
  rcases Finset.mem_union.mp hc with hA | hB
  · rw [P.partA_eq] at hA
    exact P.notMem_between_of_ne ht h1 (hsub he) hA
  · rw [P.partB_eq, betweenEdges_comm (P.atom P.lastIdx) (P.atom 0)] at hB
    exact P.notMem_between_of_ne ht hl (hsub he) hB

end NearCycle

/-! ### The hierarchy half -/

namespace Hierarchy

variable {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη)

/-- **KKO21 Observation 4.32, weak form.**  For a near-cycle cut `S` presented
by `N` and a strict descendant cut `u`, the crossing edges `δ(u) ∩ δ(S)` lie
inside one of `A`, `B`, `C`. -/
theorem observation_4_32 {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) {N : NearCycle x εη} (hN : H.Presents N S) :
    cutEdges u ∩ cutEdges S ⊆ N.partA
      ∨ cutEdges u ∩ cutEdges S ⊆ N.partB
      ∨ cutEdges u ∩ cutEdges S ⊆ N.partC := by
  obtain ⟨a, hchild, hua⟩ := H.exists_child_superset hu hS hlt
  obtain ⟨t, ht0, hta⟩ := (hN.2 a).mp hchild
  have hroot : cutEdges S = cutEdges N.root := by rw [hN.1, cutEdges_compl]
  have huat : u ⊆ N.atom t := by rw [hta]; exact hua
  rw [hroot]
  exact N.observation_4_32_atom ht0 huat

/-- **The direct consumer**: at least one of `A`, `B` misses `δ(u)` entirely.
Under the max-flow event `A_T = B_T = 1`, so the crossing contribution of
`δ(u)` is then a single Bernoulli. -/
theorem disjoint_partA_or_partB {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) {N : NearCycle x εη} (hN : H.Presents N S) :
    Disjoint (cutEdges u) N.partA ∨ Disjoint (cutEdges u) N.partB := by
  have hroot : cutEdges N.root = cutEdges S := by rw [hN.1, cutEdges_compl]
  have hAcut : N.partA ⊆ cutEdges S := hroot ▸ N.partA_subset_cutEdges_root
  have hBcut : N.partB ⊆ cutEdges S := hroot ▸ N.partB_subset_cutEdges_root
  rcases H.observation_4_32 hS hu hlt hN with hA | hB | hC
  · -- inside `A`, so disjoint from `B`
    refine Or.inr (Finset.disjoint_left.mpr fun e he heB => ?_)
    have : e ∈ N.partA := hA (Finset.mem_inter.mpr ⟨he, hBcut heB⟩)
    exact absurd (Finset.disjoint_left.mp N.partA_disjoint_partB this heB) not_false
  · -- inside `B`, so disjoint from `A`
    refine Or.inl (Finset.disjoint_left.mpr fun e he heA => ?_)
    have : e ∈ N.partB := hB (Finset.mem_inter.mpr ⟨he, hAcut heA⟩)
    exact absurd (Finset.disjoint_left.mp N.partA_disjoint_partB heA this) not_false
  · -- inside `C`, so disjoint from both
    refine Or.inl (Finset.disjoint_left.mpr fun e he heA => ?_)
    have hCe : e ∈ N.partC := hC (Finset.mem_inter.mpr ⟨he, hAcut heA⟩)
    exact (Finset.mem_sdiff.mp hCe).2 (Finset.mem_union_left _ heA)

end Hierarchy

end TSPGap

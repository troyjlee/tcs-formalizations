/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SharpNearCycleProbability
import TSPGap.SharpHierarchyCharging

/-!
# The sharp happy-polygon payment at a one-side component

Both laminar families contain every relevant atom. The member intervals are
selected in the same rooted coordinates used by the sharp probability
proofs; the old generic near-cycle estimate is not used.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {η α : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

/-- **KKO22 Theorem A.12**, with its `44αη` cost and an identified polygon. -/
theorem exists_happySlack_of_oneSideComponent_sharp
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : PolygonRep 𝒞) (hcomp : IsOneSideComponent e₀ x₀ η 𝒞)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom ∧ cutSum x₀ A ≤ 2 + η)
    (hα : 0 ≤ α) (hη : 0 < η) (hη' : η ≤ 1 / 100) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      N.root = P.rootAtom ∧
      (∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
        ↔ A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom) ∧
      (∀ T e, 0 ≤ s T e) ∧
      (∀ S ∈ 𝒞 ∪ 𝒜, ∃ i j : Fin (N.k + 3), N.interval i j = S ∧
        0 < i ∧ i ≤ j ∧ ¬ (i = 1 ∧ j = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (i = 1 → N.LeftHappy T) → (j = N.lastIdx → N.RightHappy T) →
          α * (1 - 7 * η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ α * (44 * η) * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s T e = 0) := by
  classical
  obtain ⟨hcover, r, hr⟩ := oneSide_no_inside_atoms P hx₀ hcomp (by linarith)
  let R : P.Rooted := ⟨r, hr, hcover⟩
  obtain ⟨k, hk⟩ : ∃ k, P.m = k + 3 := ⟨P.m - 3, by have := P.hm; omega⟩
  obtain ⟨hadj, hdeg, hmid⟩ := oneSide_structure P hx₀ hcomp hη hη' hk r hr
  let N := P.toNearCycle hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid
  have hNroot : N.root = P.rootAtom :=
    P.toNearCycle_root hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid hr
  have hNatom : ∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
      ↔ A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom := fun A =>
    P.toNearCycle_atom_iff hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid hr
  have hread : ∀ i : Fin (N.k + 3), N.atom i = P.ivl R i.val i.val :=
    P.toNearCycle_atom_eq_ivl R hk (e₀.restrict x₀) (7 * η) hadj hdeg hmid
  have hI := P.nearCycle_interval_eq_ivl R N hk hread
  have hlast : N.lastIdx.val = P.m - 1 := by change k + 2 = P.m - 1; omega
  have hex : ∀ S : Finset (Fin n), ∃ ij : Fin (N.k + 3) × Fin (N.k + 3),
      S ∈ 𝒞 ∪ 𝒜 → N.interval ij.1 ij.2 = S ∧
        0 < ij.1 ∧ ij.1 ≤ ij.2 ∧ ¬ (ij.1 = 1 ∧ ij.2 = N.lastIdx) ∧
        (S ∈ 𝒞 → P.lo R S = ij.1.val ∧ P.hi R S = ij.2.val) ∧
        (S ∈ 𝒞 ∨ ij.1 = ij.2) := by
    intro S
    by_cases hS : S ∈ 𝒞
    · have hlo := P.one_le_lo R hS
      have hhi := P.hi_lt R hS
      have hlt := P.lo_lt_hi R hS
      let i : Fin (N.k + 3) := ⟨P.lo R S, by omega⟩
      let j : Fin (N.k + 3) := ⟨P.hi R S, by omega⟩
      refine ⟨(i, j), fun _ => ⟨?_, ?_, ?_, ?_, fun _ => ⟨rfl, rfl⟩, Or.inl hS⟩⟩
      · rw [hI]
        exact (P.eq_ivl R hS).symm
      · change 0 < P.lo R S
        omega
      · change P.lo R S ≤ P.hi R S
        omega
      · rintro ⟨h1, h2⟩
        have hv1 := congrArg Fin.val h1
        have hv2 := congrArg Fin.val h2
        change P.lo R S = 1 at hv1
        change P.hi R S = N.lastIdx.val at hv2
        rw [hlast] at hv2
        have hlen := P.len_le S hS
        have heq : P.hi R S = P.lo R S + P.len S - 1 := rfl
        omega
    · by_cases hA : S ∈ 𝒜
      · obtain ⟨t, ht, hts⟩ := (hNatom S).mpr ⟨(h𝒜 S hA).1, (h𝒜 S hA).2.1⟩
        refine ⟨(t, t), fun _ => ⟨?_, Fin.pos_iff_ne_zero.mpr ht, le_rfl, ?_,
          fun hc => False.elim (hS hc), Or.inr rfl⟩⟩
        · rw [N.interval_self, hts]
        · rintro ⟨h1, h2⟩
          have hc := congrArg Fin.val (h1.symm.trans h2)
          change 1 = N.lastIdx.val at hc
          have := P.hm
          omega
      · exact ⟨(0, 0), fun hc => False.elim (by simp [hS, hA] at hc)⟩
  choose idx hidx using hex
  let CL := 𝒞.filter P.OpenLeft ∪ 𝒜
  let CR := 𝒞.filter P.OpenRight ∪ 𝒜
  have hCL : CL ⊆ 𝒞 ∪ 𝒜 := union_subset_union (filter_subset _ _) (Subset.refl _)
  have hCR : CR ⊆ 𝒞 ∪ 𝒜 := union_subset_union (filter_subset _ _) (Subset.refl _)
  have hcoverC : CL ∪ CR = 𝒞 ∪ 𝒜 := by
    ext S
    simp only [CL, CR, mem_union, mem_filter]
    have hsplit : S ∈ 𝒞 → P.OpenLeft S ∨ P.OpenRight S :=
      P.openLeft_or_openRight hx₀ hcomp hη (by linarith)
    tauto
  have hlamL : ∀ A ∈ CL, ∀ B ∈ CL, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B :=
    laminar_of_not_crossing hcomp (filter_subset _ _)
      (fun A hA B hB => P.not_crossing_of_openLeft (mem_filter.mp hA).2 (mem_filter.mp hB).2)
      (fun A hA => (h𝒜 A hA).1)
  have hlamR : ∀ A ∈ CR, ∀ B ∈ CR, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B :=
    laminar_of_not_crossing hcomp (filter_subset _ _)
      (fun A hA B hB => P.not_crossing_of_openRight (mem_filter.mp hA).2 (mem_filter.mp hB).2)
      (fun A hA => (h𝒜 A hA).1)
  have hFunion : CL.image idx ∪ CR.image idx = (𝒞 ∪ 𝒜).image idx := by
    rw [← image_union, hcoverC]
  have hpair : ∀ p ∈ CL.image idx ∪ CR.image idx, ∃ S ∈ 𝒞 ∪ 𝒜, idx S = p := by
    intro p hp
    rwa [hFunion, mem_image] at hp
  have hlam : ∀ D : Finset (Finset (Fin n)), D ⊆ 𝒞 ∪ 𝒜 →
      (∀ A ∈ D, ∀ B ∈ D, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) → IntervalLaminar (D.image idx) := by
    intro D hD hset
    refine intervalLaminar_of_setLaminar N _ ?_
    intro p hp q hq
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hp
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hq
    rw [(hidx A (hD hA)).1, (hidx B (hD hB)).1]
    exact hset A hA B hB
  have hboth : ∀ p ∈ CL.image idx ∪ CR.image idx, p.1 = p.2 →
      p ∈ CL.image idx ∧ p ∈ CR.image idx := by
    intro p hp heq
    obtain ⟨S, hS, rfl⟩ := hpair p hp
    have hA : S ∈ 𝒜 := by
      rcases mem_union.mp hS with hc | ha
      · have hcoords := (hidx S hS).2.2.2.2.1 hc
        have hlt := P.lo_lt_hi R hc
        have he := congrArg Fin.val heq
        omega
      · exact ha
    exact ⟨mem_image_of_mem idx (mem_union_right _ hA), mem_image_of_mem idx (mem_union_right _ hA)⟩
  have hprob : ∀ p ∈ CL.image idx ∪ CR.image idx,
      μ.probEvent (N.Fails p) ≤ if p.1 = p.2 then 21 * η else 11 * η := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := hpair p hp
    have hi := hidx S hS
    have hnm : IsNearMinCut x₀ η S := by
      rcases mem_union.mp hS with hc | ha
      · exact hcomp.nearMin S hc
      · obtain ⟨t, ht, hts⟩ := (hNatom S).mpr ⟨(h𝒜 S ha).1, (h𝒜 S ha).2.1⟩
        have hpos : 1 ≤ t.val := Fin.pos_iff_ne_zero.mpr ht
        have hav : AvoidsRootEdge e₀ S := by
          rw [← hts, hread t]
          exact P.ivl_avoids R hcomp hpos
        exact ⟨hts ▸ N.atom_nonempty t, fun h => hav.1 (h ▸ mem_univ _), (h𝒜 S ha).2.2⟩
    refine P.prob_fails_sharp_read R hx₀ μ hcomp hη (by linarith) N hk hread hNroot
      hi.2.1 ?_ ?_ ?_
    · rw [hi.1]
      exact hi.2.2.2.2.2
    · rw [hi.1]
      exact hi.2.2.2.2.1
    · rwa [hi.1]
  obtain ⟨s, hnn, hpay, hcost, hsupp⟩ := N.exists_happySlack_of_hierarchies_sharp μ
    (CL.image idx) (CR.image idx) (hlam CL hCL hlamL) (hlam CR hCR hlamR)
    hα (RootEdge.restrict_nonneg hx₀.1) (by linarith) hη.le
    (fun p hp => by obtain ⟨S, hS, rfl⟩ := hpair p hp; exact (hidx S hS).2.2.1)
    (fun p hp => by obtain ⟨S, hS, rfl⟩ := hpair p hp; exact (hidx S hS).2.1)
    (fun p hp => by obtain ⟨S, hS, rfl⟩ := hpair p hp; exact (hidx S hS).2.2.2.1)
    hboth hprob
  refine ⟨N, s, hNroot, hNatom, hnn, ?_, hcost, hsupp⟩
  intro S hS
  have hi := hidx S hS
  refine ⟨(idx S).1, (idx S).2, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
  intro T hodd hL hR
  have hp : idx S ∈ CL.image idx ∪ CR.image idx := by
    rw [hFunion]
    exact mem_image_of_mem idx hS
  have h := hpay (idx S) hp T (by rwa [hi.1]) hL hR
  rwa [hi.1] at h

end TSPGap

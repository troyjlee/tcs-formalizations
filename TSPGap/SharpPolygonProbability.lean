/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SharpCutProbability

/-!
# Appendix A failure bounds at a genuine one-side polygon

The strict-parent/common-crosser theorem supplies the interior-cut witness.
The root-neighbour and adjacent-pair estimates supply the boundary and atom
witnesses. No generic `7η` replacement is made for a relevant cut itself.
-/

namespace TSPGap.PolygonRep

open Finset NearCycle

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}
variable (P : PolygonRep 𝒞) (R : P.Rooted)

/-- Non-root intervals are disjoint from the root atom. -/
theorem ivl_disjoint_root {a b : ℕ} (ha : 1 ≤ a) :
    Disjoint (P.ivl R a b) P.rootAtom :=
  disjoint_left.mpr fun _ hv hr => P.root_notMem_ivl R ha hr hv

/-- Non-root intervals avoid both endpoints of the distinguished edge. -/
theorem ivl_avoids (hcomp : IsOneSideComponent e₀ x η 𝒞) {a b : ℕ} (ha : 1 ≤ a) :
    AvoidsRootEdge e₀ (P.ivl R a b) := by
  obtain ⟨hu, hv⟩ := P.rootEdge_mem_root R hcomp
  rw [R.hr] at hu hv
  exact ⟨P.root_notMem_ivl R ha hu, P.root_notMem_ivl R ha hv⟩

/-- A right-hierarchy member not at the right boundary has the crossing
chain used by the sharp probability kernel. -/
theorem prob_cut_two_openRight (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A : Finset (Fin n)}
    (hA : P.OpenRight A) (hr : P.hi R A < P.m - 1) :
    1 - 8.5 * η ≤ μ.probEvent (fun T => (cutEdges A ∩ T).card = 2) := by
  obtain ⟨B, hAB⟩ := P.exists_strictParentR R hcomp
    (P.exists_strictAncR R hx hcomp hη0 hη hA hr)
  obtain ⟨C, hC, hCA, hCB⟩ := P.exists_crossesOnLeft_of_strictParentR R hx hcomp hη0 hη hAB
  have hB := hAB.1.2.1.1
  have ha := (P.crossesOnLeft_iff R hC hA.1).mp hCA
  have hb := (P.crossesOnLeft_iff R hC hB).mp hCB
  have hstrict := hAB.1.2.2.2
  have hu : A ∪ C = P.ivl R (P.lo R C) (P.hi R A) := by
    ext v
    simp only [mem_union, mem_ivl, P.mem_iff_pos R hA.1, P.mem_iff_pos R hC]
    omega
  have hBU : Crossing B (A ∪ C) := by
    rw [hu, P.eq_ivl R hB]
    exact (P.crossing_ivl R (P.one_le_lo R hC) hb.1 (by omega)
      hstrict (P.hi_lt R hB)).symm
  exact prob_cut_two_of_crossing_chain hx μ
    (hcomp.nearMin A hA.1) (hcomp.nearMin B hB) (hcomp.nearMin C hC)
    (hcomp.avoids A hA.1) (hcomp.avoids B hB) (hcomp.avoids C hC)
    hAB.1.2.2.1 hCA.1.symm hCB.1.symm hBU

/-- **KKO22 Lemma A.9**, in the rooted polygon coordinates, with the
stronger `8.5η` estimate available from separate group deficiencies. -/
theorem prob_cut_two_member (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A : Finset (Fin n)} (hA : A ∈ 𝒞)
    (hl : 1 < P.lo R A) (hr : P.hi R A < P.m - 1) :
    1 - 8.5 * η ≤ μ.probEvent (fun T => (cutEdges A ∩ T).card = 2) := by
  rcases P.openLeft_or_openRight hx hcomp hη0 hη hA with h | h
  · refine P.reflect.prob_cut_two_openRight R.reflect hx μ hcomp hη0 hη
      ((P.reflect_openRight R).mpr h) ?_
    rw [P.reflect_hi R hA]
    change P.m - P.lo R A < P.m - 1
    have := P.hi_lt R hA
    have := P.lo_lt_hi R hA
    omega
  · exact P.prob_cut_two_openRight R hx μ hcomp hη0 hη h hr

/-- A set containing either root-neighbour atom has at least `1-η`
mass going to the root, provided the set is disjoint from the root. -/
theorem root_mass_ge_of_boundary (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞) (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    {A : Finset (Fin n)} (hd : Disjoint A P.rootAtom)
    (hboundary : P.ivl R 1 1 ⊆ A ∨ P.ivl R (P.m - 1) (P.m - 1) ⊆ A) :
    1 - η ≤ ∑ e ∈ betweenEdges A P.rootAtom, e₀.restrict x e := by
  have hm : ∀ {t : ℕ}, (P.ivl R t t ⊆ A) →
      1 - η ≤ pairSum x (P.ivl R t t) (P.out R.r) →
      1 - η ≤ ∑ e ∈ betweenEdges A P.rootAtom, e₀.restrict x e := by
    intro t ht hmass
    have hd' : Disjoint (P.ivl R t t) (P.out R.r) := by
      rw [R.hr]
      exact hd.mono_left ht
    have heq : (∑ e ∈ betweenEdges (P.ivl R t t) (P.out R.r), e₀.restrict x e) =
        pairSum x (P.ivl R t t) (P.out R.r) := by
      rw [sum_betweenEdges _ hd', pairSum_comm,
        P.pairSum_restrict_root_eq R hcomp hd'.symm, pairSum_comm]
    rw [← heq] at hmass
    rw [R.hr] at hmass
    refine hmass.trans (sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · intro e he
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff'.mp he
      exact mem_betweenEdges_iff'.mpr ⟨a, ht ha, b, hb, rfl⟩
    · exact fun e _ _ => RootEdge.restrict_nonneg hx.1 e
  rcases hboundary with h | h
  · exact hm h (P.root_neighbor_left R hx hcomp hη0 hη)
  · exact hm h (P.root_neighbor_right R hx hcomp hη0 hη)

/-- **KKO22 Lemma A.11**, for a member at either end of the polygon. -/
theorem prob_side_one_member (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A : Finset (Fin n)} (hA : A ∈ 𝒞)
    (hend : P.lo R A = 1 ∨ P.hi R A = P.m - 1) :
    1 - 5 * η ≤ μ.probEvent
      (fun T => ((cutEdges A \ betweenEdges A P.rootAtom) ∩ T).card = 1) := by
  obtain ⟨C, hC, hcross⟩ := BG.exists_cross P.nontrivial hcomp.conn hA
  have hboundary : P.ivl R 1 1 ⊆ A ∨ P.ivl R (P.m - 1) (P.m - 1) ⊆ A := by
    have hlo := P.one_le_lo R hA
    have hhi := P.hi_lt R hA
    have hlen := P.lo_lt_hi R hA
    rcases hend with h | h
    · left
      intro v hv
      rw [P.mem_ivl R] at hv
      rw [P.mem_iff_pos R hA]
      omega
    · right
      intro v hv
      rw [P.mem_ivl R] at hv
      rw [P.mem_iff_pos R hA]
      omega
  have hdis := (P.rootAtom_disjoint A hA).symm
  exact prob_side_one_of_crossing hx μ (hcomp.nearMin A hA) (hcomp.nearMin C hC)
    (hcomp.avoids A hA) (hcomp.avoids C hC) hcross hdis
    (P.rootAtom_disjoint C hC).symm
    (P.root_mass_ge_of_boundary R hx hcomp hη0 hη hdis hboundary)

/-- **KKO22 Lemma A.10**, for an interior relevant atom. -/
theorem prob_cut_two_atom (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {t : ℕ} (ht : 1 < t) (htm : t + 1 < P.m)
    (hA : IsNearMinCut x η (P.ivl R t t)) :
    1 - 21 * η ≤ μ.probEvent (fun T => (cutEdges (P.ivl R t t) ∩ T).card = 2) := by
  have hB := P.atom_nearMin R hx hcomp hη0 hη (t := t - 1) (by omega) (by omega)
  have hC := P.atom_nearMin R hx hcomp hη0 hη (t := t + 1) (by omega) (by omega)
  have hAB := P.pair_nearMin R hx hcomp hη0 hη (i := t - 1) (by omega) (by omega)
  have hAC := P.pair_nearMin R hx hcomp hη0 hη (i := t) (by omega) (by omega)
  have hu1 : P.ivl R t t ∪ P.ivl R (t - 1) (t - 1) = P.ivl R (t - 1) (t - 1 + 1) := by
    ext v
    simp only [mem_union, mem_ivl]
    omega
  have hu2 : P.ivl R t t ∪ P.ivl R (t + 1) (t + 1) = P.ivl R t (t + 1) :=
    P.ivl_union_of R (by omega) (by omega) (by omega)
  exact prob_cut_two_of_near_neighbors hx μ hA hB hC
    (by rw [hu1]; exact hAB) (by rw [hu2]; exact hAC)
    (P.ivl_avoids R hcomp (by omega)) (P.ivl_avoids R hcomp (by omega))
    (P.ivl_avoids R hcomp (by omega))
    (P.disjoint_ivl_of_lt R (by omega)).symm
    (P.disjoint_ivl_of_lt R (by omega)) (P.disjoint_ivl_of_lt R (by omega))

/-- **KKO22 Lemma A.11**, for the first relevant atom. -/
theorem prob_side_one_first_atom (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    (hA : IsNearMinCut x η (P.ivl R 1 1)) :
    1 - 12 * η ≤ μ.probEvent
      (fun T => ((cutEdges (P.ivl R 1 1) \
        betweenEdges (P.ivl R 1 1) P.rootAtom) ∩ T).card = 1) := by
  have hm := P.hm
  have hB := P.atom_nearMin R hx hcomp hη0 hη (t := 2) (by omega) (by omega)
  have hAB := P.pair_nearMin R hx hcomp hη0 hη (i := 1) (by omega) (by omega)
  have hu : P.ivl R 1 1 ∪ P.ivl R 2 2 = P.ivl R 1 2 :=
    P.ivl_union_of R (by omega) (by omega) (by omega)
  exact prob_side_one_of_near_neighbor hx μ hA hB (by rw [hu]; exact hAB)
    (P.ivl_avoids R hcomp le_rfl) (P.ivl_avoids R hcomp (by omega))
    (P.disjoint_ivl_of_lt R (by omega))
    (P.ivl_disjoint_root R le_rfl) (P.ivl_disjoint_root R (by omega))
    (P.root_mass_ge_of_boundary R hx hcomp hη0 hη (P.ivl_disjoint_root R le_rfl)
      (Or.inl (Subset.refl _)))

/-- The last relevant atom, by reflection of the first-atom estimate. -/
theorem prob_side_one_last_atom (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    (hA : IsNearMinCut x η (P.ivl R (P.m - 1) (P.m - 1))) :
    1 - 12 * η ≤ μ.probEvent
      (fun T => ((cutEdges (P.ivl R (P.m - 1) (P.m - 1)) \
        betweenEdges (P.ivl R (P.m - 1) (P.m - 1)) P.rootAtom) ∩ T).card = 1) := by
  have hm := P.hm
  have heq := P.reflect_ivl R (a := P.m - 1) (b := P.m - 1) (by omega) (by omega)
  rw [show P.m - (P.m - 1) = 1 by omega] at heq
  have h := P.reflect.prob_side_one_first_atom R.reflect hx μ hcomp hη0 hη
    (by rw [heq]; exact hA)
  have hroot : P.reflect.rootAtom = P.rootAtom := by
    rw [← R.reflect.hr, ← R.hr]
    simp [Rooted.reflect, reflect]
  simpa only [heq, hroot] using h

end TSPGap.PolygonRep

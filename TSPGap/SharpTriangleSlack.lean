/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TheoremB3
import TSPGap.SharpCutProbability

/-!
# Sharp triangle payment

All failure events use the single group between the two children. Its
one-edge probability is Corollary 2.12 at the three original cut bounds.
-/

namespace TSPGap

open Finset NearCycle

variable {n : ℕ} {X Y : Finset (Fin n)}

open Classical in
/-- **KKO22 Lemma A.13**, at cost `1.5αε`. No exact-one assertion is
made about the root groups: their odd parity is all payment requires. -/
theorem exists_happySlack_triangle_sharp {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {ε α : ℝ} (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (hd : Disjoint X Y) (hX : IsNearMinCut x₀ ε X) (hY : IsNearMinCut x₀ ε Y)
    (hS : IsNearMinCut x₀ ε (X ∪ Y)) (havoid : AvoidsRootEdge e₀ (X ∪ Y))
    (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    ∃ (N : NearCycle (e₀.restrict x₀) ε)
      (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      N.root = (X ∪ Y)ᶜ ∧
      (∀ A : Finset (Fin n),
        (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A) ↔ (A = X ∨ A = Y)) ∧
      (∀ T e, 0 ≤ s T e) ∧
      (∀ S : Finset (Fin n), (S = X ∨ S = Y) → ∃ a b : Fin (N.k + 3),
        N.interval a b = S ∧ 0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
          α * (1 - ε) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ α * (1.5 * ε) * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s T e = 0) := by
  classical
  have hXav : AvoidsRootEdge e₀ X := havoid.mono Finset.subset_union_left
  have hYav : AvoidsRootEdge e₀ Y := havoid.mono Finset.subset_union_right
  have hSne : (X ∪ Y).Nonempty := hS.nonempty
  have hSnu : X ∪ Y ≠ Finset.univ := hS.ne_univ
  have hdCX : Disjoint ((X ∪ Y)ᶜ : Finset (Fin n)) X :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv1) (Finset.mem_union_left _ hv2)
  have hdYC : Disjoint Y ((X ∪ Y)ᶜ : Finset (Fin n)) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2) (Finset.mem_union_right _ hv1)
  -- Theorem A.3's mass conditions, over the restricted vector
  have hCX : 1 - ε ≤ ∑ e ∈ betweenEdges ((X ∪ Y)ᶜ) X, e₀.restrict x₀ e := by
    rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges_right hXav),
      sum_betweenEdges x₀ hdCX, pairSum_comm]
    exact triangle_le_pairSum_compl hx₀ hd hX.cut_le hY.cut_le hX.nonempty hX.ne_univ
      hSne hSnu
  have hXY : 1 - ε ≤ ∑ e ∈ betweenEdges X Y, e₀.restrict x₀ e := by
    rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges_right hYav),
      sum_betweenEdges x₀ hd]
    have h := le_pairSum_of_union hx₀ hd hX.nonempty hX.ne_univ hY.nonempty hY.ne_univ
      hS.cut_le
    linarith
  have hYC : 1 - ε ≤ ∑ e ∈ betweenEdges Y ((X ∪ Y)ᶜ), e₀.restrict x₀ e := by
    rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges_left hYav),
      sum_betweenEdges x₀ hdYC]
    have h := triangle_le_pairSum_compl (X := Y) (Y := X) hx₀ hd.symm hY.cut_le hX.cut_le
      hY.nonempty hY.ne_univ (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm])
    rwa [Finset.union_comm Y X] at h
  have hCc : cutSum (e₀.restrict x₀) ((X ∪ Y)ᶜ) ≤ 2 + ε := by
    rw [cutSum_compl, cutSum_restrict havoid]
    exact hS.cut_le
  have hXc : cutSum (e₀.restrict x₀) X ≤ 2 + ε := by
    rw [cutSum_restrict hXav]; exact hX.cut_le
  have hYc : cutSum (e₀.restrict x₀) Y ≤ 2 + ε := by
    rw [cutSum_restrict hYav]; exact hY.cut_le
  set N := triangleNearCycle (e₀.restrict x₀) ε X Y hX.nonempty hY.nonempty
    (compl_nonempty_of_ne_univ hSnu) hd hε hCX hXY hYC hCc hXc hYc with hN
  have hlast : N.lastIdx = 2 := rfl
  have hI1 : N.interval 1 1 = X := N.interval_self 1
  have hI2 : N.interval 2 2 = Y := N.interval_self 2
  have houter : N.outerCut = X ∪ Y := by
    change ((X ∪ Y)ᶜ)ᶜ = X ∪ Y
    exact compl_compl _
  have hdx : (X ∪ Y) \ X = Y := by
    ext v
    simp only [mem_sdiff, mem_union]
    have hdis : v ∈ X → v ∉ Y := fun hv => disjoint_left.mp hd hv
    tauto
  have hdy : (X ∪ Y) \ Y = X := by
    ext v
    simp only [mem_sdiff, mem_union]
    have hdis : v ∈ X → v ∉ Y := fun hv => disjoint_left.mp hd hv
    tauto
  have hYX : betweenEdges Y X = betweenEdges X Y := by
    ext e
    rw [mem_betweenEdges_iff', mem_betweenEdges_iff']
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b, hb, a, ha, Sym2.eq_swap⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b, hb, a, ha, Sym2.eq_swap⟩
  have hsX : N.sideEdges X = betweenEdges X Y := by
    rw [N.sideEdges_eq_betweenEdges (by rw [houter]; exact subset_union_left), houter, hdx]
  have hsY : N.sideEdges Y = betweenEdges X Y := by
    rw [N.sideEdges_eq_betweenEdges (by rw [houter]; exact subset_union_right),
      houter, hdy, hYX]
  let Q := fun T : Finset (Sym2 (Fin n)) => (betweenEdges X Y ∩ T).card ≠ 1
  let s := fun T e => if e ∈ betweenEdges X Y ∧ Q T then α * e₀.restrict x₀ e else 0
  have hsnn : ∀ T e, 0 ≤ s T e := by
    intro T e
    dsimp [s]
    split
    · exact mul_nonneg hα (RootEdge.restrict_nonneg hx₀.1 e)
    · exact le_rfl
  have hq : μ.probEvent Q ≤ 1.5 * ε := by
    have h := prob_exactlyOne_betweenEdges hx₀ μ havoid hd hX hY hS
    rw [show Q = fun T => ¬ (betweenEdges X Y ∩ T).card = 1 from rfl, μ.probEvent_not]
    linarith
  have hcost : ∀ e, μ.expect (fun T => s T e) ≤ α * (1.5 * ε) * e₀.restrict x₀ e := by
    intro e
    by_cases he : e ∈ betweenEdges X Y
    · have heq : (fun T => s T e) = fun T => if Q T then α * e₀.restrict x₀ e else 0 := by
        funext T
        simp [s, he]
      have hi : μ.expect (fun T => if Q T then α * e₀.restrict x₀ e else 0) =
          (α * e₀.restrict x₀ e) * μ.probEvent Q := by
        rw [TreeDist.expect, μ.probEvent_eq_sum, mul_sum]
        refine sum_congr rfl fun T _ => ?_
        by_cases h : Q T
        · simp only [if_pos h]
          ring
        · simp [h]
      rw [heq, hi]
      have hx : 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1 e
      nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hα hx)]
    · simp only [s, he, false_and, if_false]
      simp only [TreeDist.expect, mul_zero, sum_const_zero]
      exact mul_nonneg (mul_nonneg hα (by positivity)) (RootEdge.restrict_nonneg hx₀.1 e)
  have hpay : ∀ S, (S = X ∨ S = Y) → ∀ T, Q T →
      α * (1 - ε) ≤ ∑ e ∈ cutEdges S, s T e := by
    intro S hS T hQ
    have hsub : betweenEdges X Y ⊆ cutEdges S := by
      rcases hS with hS | hS
      · subst S
        exact between_subset_cut_of_subsets (Subset.refl X) hd.symm
      · subst S
        rw [← hYX]
        exact between_subset_cut_of_subsets (Subset.refl Y) hd
    have heq : (∑ e ∈ cutEdges S, s T e) = α * ∑ e ∈ betweenEdges X Y, e₀.restrict x₀ e := by
      simp only [s, hQ, and_true]
      rw [sum_ite_mem, inter_eq_right.mpr hsub, mul_sum]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hXY hα
  refine ⟨N, s, rfl, ?_, hsnn, ?_, hcost, ?_⟩
  · intro A
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases fin_three_cases t with rfl | rfl | rfl
      · exact absurd rfl ht
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, triangle_one_ne_zero, rfl⟩
      · exact ⟨2, triangle_two_ne_zero, rfl⟩
  · intro S hS0
    rcases hS0 with hS0 | hS0
    · subst S
      refine ⟨1, 1, hI1, triangle_zero_lt_one, le_rfl, ?_, ?_⟩
      · rintro ⟨_, hc⟩
        exact triangle_one_ne_two (hc.trans hlast)
      · intro T hodd hL _
        apply hpay X (Or.inl rfl) T
        have h : ¬ N.CutHappy X T := by
          intro hc
          have heven := N.even_cut_of_cutHappy_left (j := 1) le_rfl
            (by rw [hlast]; change (1 : Fin 3) < 2; decide) (hL rfl) (by rwa [hI1])
          rw [hI1] at heven
          exact (Nat.not_even_iff_odd.mpr hodd) heven
        simpa only [CutHappy, hsX] using h
    · subst S
      refine ⟨2, 2, hI2, triangle_zero_lt_two, le_rfl, ?_, ?_⟩
      · rintro ⟨hc, _⟩
        exact triangle_two_ne_one hc
      · intro T hodd _ hR
        apply hpay Y (Or.inr rfl) T
        have h : ¬ N.CutHappy Y T := by
          intro hc
          have heven := N.even_cut_of_cutHappy_right (i := 2)
            (by change (1 : Fin 3) < 2; decide)
            (by rw [hlast]) (hR hlast.symm) (by simpa only [hlast, hI2] using hc)
          have heven' : Even (cutEdges Y ∩ T).card := by simpa only [hlast, hI2] using heven
          exact (Nat.not_even_iff_odd.mpr hodd) heven'
        simpa only [CutHappy, hsY] using h
  · intro T e he
    have hnot : e ∉ betweenEdges X Y := he 1 triangle_one_ne_zero
      (by change (1 : Fin 3) + 1 ≠ 0; decide)
    simp [s, hnot]

end TSPGap

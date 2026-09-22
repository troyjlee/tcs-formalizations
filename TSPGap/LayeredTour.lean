/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RandomJoinTour

/-!
# Tours from slack feasible on all odd cuts

Use the all-cut guarantee of a layered slack directly. The root correction
handles root-separating cuts, and has zero cost. No second repair or
single-threshold mixing formula is applied to the combined slack.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {β : ℝ}

/-- The all-cut slack condition suffices for the O-join polyhedron. -/
theorem ojoinFeasible_of_all_cut_slack (e₀ : RootEdge n)
    (hx : ∀ e, 0 ≤ e₀.restrict x₀ e) {T : Finset (Sym2 (Fin n))}
    (hT : ∀ e ∈ T, ¬ e.IsDiag) {Z : Sym2 (Fin n) → ℝ} (hβ : β ≤ 1 / 2)
    (hlower : ∀ e, -(β * e₀.restrict x₀ e) ≤ Z e)
    (hcut : ∀ S, S.Nonempty → S ≠ univ → e₀.edge ∉ cutEdges S →
      Odd (cutEdges S ∩ T).card →
      1 ≤ cutSum (e₀.restrict x₀) S / 2 + ∑ e ∈ cutEdges S, Z e) :
    OJoinFeasible (oddVerts T) (ojoinVec e₀ x₀ Z (fun _ => 0)) := by
  classical
  have hnn : ∀ e, 0 ≤ ojoinVec e₀ x₀ Z (fun _ => 0) e := by
    intro e
    unfold ojoinVec
    split
    · norm_num
    · have hm := mul_le_mul_of_nonneg_right hβ (hx e)
      linarith only [hlower e, hm]
  refine ⟨hnn, ?_⟩
  intro S ho
  by_cases he : e₀.edge ∈ cutEdges S
  · have hroot : ojoinVec e₀ x₀ Z (fun _ => 0) e₀.edge = 1 := by simp [ojoinVec]
    rw [← hroot]
    exact single_le_sum (fun e _ => hnn e) he
  · have hodd := odd_cutEdges_inter_of_odd_inter_oddVerts hT ho
    have hne : S.Nonempty := by
      rcases eq_empty_or_nonempty S with rfl | h
      · simp [cutEdges] at hodd
      · exact h
    have hnu : S ≠ univ := by
      rintro rfl
      simp [cutEdges] at hodd
    have hsum : (∑ e ∈ cutEdges S, ojoinVec e₀ x₀ Z (fun _ => 0) e) =
        cutSum (e₀.restrict x₀) S / 2 + ∑ e ∈ cutEdges S, Z e := by
      have hterm : ∀ e ∈ cutEdges S,
          ojoinVec e₀ x₀ Z (fun _ => 0) e = e₀.restrict x₀ e / 2 + Z e := by
        intro e hmem
        simp only [ojoinVec, if_neg (show e ≠ e₀.edge from fun h => he (h ▸ hmem)),
          add_zero]
      rw [sum_congr rfl hterm, sum_add_distrib, ← sum_div, cutSum]
    rw [hsum]
    exact hcut S hne hnu he hodd

/-- An edgewise expected saving and all-cut feasibility give the same tour saving. -/
theorem exists_tour_of_all_cut_slack (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) (e₀ : RootEdge n) (hce₀ : c e₀.edge = 0)
    (hx : ∀ e, 0 ≤ e₀.restrict x₀ e) (μ : TreeDist n (e₀.restrict x₀))
    (Z : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) {gain : ℝ} (hβ : β ≤ 1 / 2)
    (hlower : ∀ T e, -(β * e₀.restrict x₀ e) ≤ Z T e)
    (hcut : ∀ S, S.Nonempty → S ≠ univ → e₀.edge ∉ cutEdges S →
      ∀ T, μ.prob T ≠ 0 → Odd (cutEdges S ∩ T).card →
      1 ≤ cutSum (e₀.restrict x₀) S / 2 + ∑ e ∈ cutEdges S, Z T e)
    (hexp : ∀ e, μ.expect (fun T => Z T e) ≤ -(gain * e₀.restrict x₀ e)) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - gain) * lpCost c x₀ := by
  classical
  have hcx : (∑ e ∈ edgeFinset n, c e * e₀.restrict x₀ e) = lpCost c x₀ := by
    rw [lpCost]
    refine sum_congr rfl fun e _ => ?_
    rcases eq_or_ne e e₀.edge with rfl | hne
    · rw [hce₀]; ring
    · rw [RootEdge.restrict, Function.update_of_ne hne]
  apply exists_tour_of_random_join hn hc μ (fun T => ojoinVec e₀ x₀ (Z T) (fun _ => 0))
  · intro T hT
    exact ojoinFeasible_of_all_cut_slack e₀ hx (μ.support_spanningTree T hT).1 hβ
      (hlower T) (fun S hS hSu he ho => hcut S hS hSu he T hT ho)
  · have hrewrite : ∀ T : Finset (Sym2 (Fin n)),
        (∑ e ∈ edgeFinset n, c e * ojoinVec e₀ x₀ (Z T) (fun _ => 0) e) =
          ∑ e ∈ edgeFinset n, (c e * (e₀.restrict x₀ e / 2) + c e * Z T e) := by
      intro T
      refine sum_congr rfl fun e _ => ?_
      rcases eq_or_ne e e₀.edge with rfl | hne
      · rw [hce₀]; ring
      · rw [ojoinVec, if_neg hne]; ring
    simp only [hrewrite, μ.expect_add, μ.expect_sum_eq, μ.expect_sum,
      μ.expect_const, μ.expect_mul_left, hcx]
    have hsum := sum_le_sum fun e (_ : e ∈ edgeFinset n) =>
      add_le_add (le_refl (c e * (e₀.restrict x₀ e / 2)))
        (mul_le_mul_of_nonneg_left (hexp e) (hc.nonneg e))
    have hid : (∑ e ∈ edgeFinset n,
        (c e * (e₀.restrict x₀ e / 2) + c e * -(gain * e₀.restrict x₀ e))) =
        (1 / 2 - gain) * lpCost c x₀ := by
      rw [← hcx, mul_sum]
      exact sum_congr rfl fun e _ => by ring
    rw [hid] at hsum
    linarith only [hsum]

end TSPGap

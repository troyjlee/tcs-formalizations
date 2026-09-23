/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OJoin

/-!
# From feasible random joins to a tour

The probabilistic method, Edmonds--Johnson, Euler and metric shortcutting
need only a feasible join vector on each supported tree and an expected
cost bound. They do not depend on the payment construction or its constants.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- A feasible random join with the stated expected cost gives a tour of that cost. -/
theorem exists_tour_of_random_join (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) (μ : TreeDist n x)
    (y : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) {bound : ℝ}
    (hy : ∀ T, μ.prob T ≠ 0 → OJoinFeasible (oddVerts T) (y T))
    (hcost : μ.expect (fun T => (∑ e ∈ T, c e) + ∑ e ∈ edgeFinset n, c e * y T e)
      ≤ bound) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ bound := by
  classical
  obtain ⟨T, hTprob, hTcost⟩ := TreeDist.exists_le_expect μ
    (fun T => (∑ e ∈ T, c e) + ∑ e ∈ edgeFinset n, c e * y T e)
  have hTtree := μ.support_spanningTree T hTprob
  obtain ⟨J, hJdiag, hJoin, hJcost⟩ :=
    exists_join_le_of_feasible (c := c) hc.nonneg (even_card_oddVerts T hTtree.1)
      (hy T hTprob)
  have hodd : ∀ v : Fin n, (Odd (degreeIn J v) ↔ Odd (degreeIn T v)) := by
    intro v
    have h1 : v ∈ oddVerts J ↔ Odd (degreeIn J v) := by simp [oddVerts]
    have h2 : v ∈ oddVerts T ↔ Odd (degreeIn T v) := by simp [oddVerts]
    rw [← h1, ← h2, hJoin]
  have heven : ∀ v : Fin n, Even (degreeIn T v + degreeIn J v) := by
    intro v
    rw [Nat.even_add, ← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, hodd v]
  obtain ⟨v, W, hWall, hWcost⟩ :=
    exists_spanning_closed_walk (c := c) hTtree hJdiag heven
  obtain ⟨w, hham, hwcost⟩ :=
    exists_hamiltonianCycle_le_of_spanning_walk hc hn W hWall
  refine ⟨v, w, hham, hwcost.trans (hWcost.trans ?_)⟩
  exact (add_le_add (le_refl (∑ e ∈ T, c e)) hJcost).trans (hTcost.trans hcost)

end TSPGap

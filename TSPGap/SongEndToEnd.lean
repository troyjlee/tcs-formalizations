/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongLayeredExistence
import TSPGap.LayeredTour
import TSPGap.MaxEntropyExistence
import TSPGap.Split

/-!
# Song's explicit integrality-gap bound

Construct the layered slack on an actual maximum-entropy law, apply the
all-cut join argument, and remove the root-edge assumption by vertex
splitting. The existing kkoEps and kko_gap statements remain unchanged.
-/

namespace TSPGap.Song

/-- Song's rooted tour bound, with all threshold certificates constructed. -/
theorem exists_tour_of_rootEdge {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) (hce₀ : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - targetGap) * lpCost c x₀ := by
  obtain ⟨μ, hμ⟩ := exists_maxEntropy_treeDist hx₀ e₀ hx₀e
  obtain ⟨Z, hlower, hcut, hexp⟩ := exists_layeredSlack e₀ hx₀ hx₀e (by omega) hμ
  exact exists_tour_of_all_cut_slack hn hc e₀ hce₀ (RootEdge.restrict_nonneg hx₀.1) μ Z
    (show ThresholdSlack.beta H ≤ 1 / 2 by norm_num [ThresholdSlack.beta, H])
    hlower hcut hexp

end TSPGap.Song

namespace TSPGap

/-- Every metric TSP instance has a tour within 3/2 - 2.05522e-30 of any subtour LP point. -/
theorem song_gap {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - Song.targetGap) * lpCost c x :=
  gap_of_rooted_gap
    (fun _ hm _ hc' _ hx' e₀ he₀ hce₀ =>
      Song.exists_tour_of_rootEdge hm hc' hx' e₀ he₀ hce₀) hn hc hx

end TSPGap

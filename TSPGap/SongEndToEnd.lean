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
splitting. `song_gap_exact` retains the exact finite saving, and
`song_gap_strict` gives Song's strict improvement over `2.05522e-30` with
one saving valid for every instance. `song_gap` rounds to the displayed
constant for convenient numerical use.
-/

namespace TSPGap.Song

/-- Song's rooted tour bound with the exact finite saving and all certificates constructed. -/
theorem exists_tour_of_rootEdge_exact {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) (hce₀ : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤
        (3 / 2 - ThresholdSlack.totalGain H layers kappa) * lpCost c x₀ := by
  obtain ⟨μ, hμ⟩ := exists_maxEntropy_treeDist hx₀ e₀ hx₀e
  obtain ⟨Z, hZ⟩ := exists_thresholdLayers e₀ hx₀ hx₀e (by omega) hμ
  obtain ⟨hlower, hcut, _⟩ :=
    layered_slack_of_certificates (restrict_isRestrictedLP hx₀) Z hZ
  exact exists_tour_of_all_cut_slack hn hc e₀ hce₀ (RootEdge.restrict_nonneg hx₀.1)
    μ (ThresholdSlack.combined Z layers)
    (show ThresholdSlack.beta H ≤ 1 / 2 by norm_num [ThresholdSlack.beta, H])
    hlower hcut (ThresholdSlack.combined_expect hZ)

/-- Song's rooted tour bound rounded to the displayed saving. -/
theorem exists_tour_of_rootEdge {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) (hce₀ : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - targetGap) * lpCost c x₀ := by
  obtain ⟨v, w, hw, hcost⟩ := exists_tour_of_rootEdge_exact hn hc hx₀ e₀ hx₀e hce₀
  refine ⟨v, w, hw, hcost.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left totalGain_gt_target.le _)
    (Finset.sum_nonneg fun e _ => mul_nonneg (hc.nonneg e) (hx₀.1 e))

end TSPGap.Song

namespace TSPGap

/-- Every metric TSP instance admits the exact saving from Song's finite layering. -/
theorem song_gap_exact {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤
        (3 / 2 - ThresholdSlack.totalGain Song.H Song.layers Song.kappa) * lpCost c x :=
  gap_of_rooted_gap
    (fun _ hm _ hc' _ hx' e₀ he₀ hce₀ =>
      Song.exists_tour_of_rootEdge_exact hm hc' hx' e₀ he₀ hce₀) hn hc hx

/-- Song's strict integrality-gap bound: one saving above `2.05522e-30`
works uniformly for all metric instances and feasible subtour-LP points. -/
theorem song_gap_strict :
    ∃ ε : ℝ, Song.targetGap < ε ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ (c : Sym2 (Fin n) → ℝ), IsMetric c →
        ∀ (x : Sym2 (Fin n) → ℝ), x ∈ subtourLP n →
          ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
            w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - ε) * lpCost c x :=
  ⟨ThresholdSlack.totalGain Song.H Song.layers Song.kappa, Song.totalGain_gt_target,
    fun _ hn _ hc _ hx => song_gap_exact hn hc hx⟩

/-- Every metric TSP instance has a tour within 3/2 - 2.05522e-30 of any subtour LP point. -/
theorem song_gap {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - Song.targetGap) * lpCost c x :=
  gap_of_rooted_gap
    (fun _ hm _ hc' _ hx' e₀ he₀ hce₀ =>
      Song.exists_tour_of_rootEdge hm hc' hx' e₀ he₀ hce₀) hn hc hx

end TSPGap

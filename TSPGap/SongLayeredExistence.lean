/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongThresholdSlack
import TSPGap.SongLayered

/-!
# Song's layered slack on the actual tree law

Choose each threshold certificate on the same base law, then apply the
finite layering theorem. All hierarchies and refinements are internal to
the individual producers; no independence between layers is required.
-/

namespace TSPGap.Song
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ}

/-- All layers are produced from the same maximum-entropy distribution. -/
theorem exists_thresholdLayers (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ) :
    ∃ Z : ℕ → TreeSlack n, ∀ i < layers, ThresholdSlackCertificate e₀ μ
      (ThresholdSlack.level H layers (i + 1)) (ThresholdSlack.increment H layers i)
      (kappa (ThresholdSlack.level H layers (i + 1))) (Z i) := by
  classical
  have hN : 0 < layers := by norm_num [layers]
  have hex : ∀ i : Fin layers, ∃ Z : TreeSlack n, ThresholdSlackCertificate e₀ μ
      (ThresholdSlack.level H layers (i.val + 1)) (ThresholdSlack.increment H layers i.val)
      (kappa (ThresholdSlack.level H layers (i.val + 1))) Z := by
    intro i
    exact exists_thresholdSlack e₀ hx₀ hx₀e hn hμ (ThresholdSlack.level_pos H_pos hN i.val)
      (ThresholdSlack.level_le H_pos.le hN (by omega))
      (ThresholdSlack.increment_nonneg H_pos.le layers i.val)
  choose Z hZ using hex
  refine ⟨fun i => if hi : i < layers then Z ⟨i, hi⟩ else fun _ _ => 0, ?_⟩
  intro i hi
  simpa only [dif_pos hi] using hZ ⟨i, hi⟩

/-- Actual slack with Song's saving and feasibility for every non-root-separating odd cut. -/
theorem exists_layeredSlack (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ) :
    ∃ Z : TreeSlack n,
      (∀ T e, -(ThresholdSlack.beta H * e₀.restrict x₀ e) ≤ Z T e) ∧
      (∀ S, S.Nonempty → S ≠ Finset.univ → e₀.edge ∉ cutEdges S →
        ∀ T, μ.prob T ≠ 0 → Odd (cutEdges S ∩ T).card →
        1 ≤ cutSum (e₀.restrict x₀) S / 2 + ∑ e ∈ cutEdges S, Z T e) ∧
      (∀ e, μ.expect (fun T => Z T e) ≤ -(targetGap * e₀.restrict x₀ e)) := by
  obtain ⟨Z, hZ⟩ := exists_thresholdLayers e₀ hx₀ hx₀e hn hμ
  exact ⟨ThresholdSlack.combined Z layers,
    layered_slack_of_certificates (restrict_isRestrictedLP hx₀) Z hZ⟩

end TSPGap.Song

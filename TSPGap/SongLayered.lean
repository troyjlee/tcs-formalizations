/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LayeredSlack
import TSPGap.SongArithmetic

/-!
# Song's layered bound from threshold certificates

The finite-sum estimate is unconditional arithmetic. The slack conclusion
takes single-threshold certificates as inputs. `SongLayeredExistence`
constructs those inputs, and `SongEndToEnd` supplies the resulting tour
theorem without changing `kkoEps` or `kko_gap`.
-/

namespace TSPGap.Song

theorem lowerBound_le_totalGain {N : ℕ} (hN : 0 < N) :
    lowerBound N ≤ ThresholdSlack.totalGain H N kappa := by
  exact ThresholdSlack.totalGain_lower_bound H_pos.le hN
    (repair_nonneg H_pos.le H_lt_one) (fun _ hu huH => kappa_envelope hu huH)

/-- One million is substituted only into a closed rational expression. -/
theorem totalGain_gt_target : targetGap < ThresholdSlack.totalGain H layers kappa := by
  have hnum := final_arithmetic
  have hbound := lowerBound_le_totalGain (show 0 < layers by norm_num [layers])
  linarith

/-- The resulting slack bounds, with the threshold certificates made explicit.
Different layers may use different hierarchies and refined coordinate types
internally; their exported functions must all live on this one base law. -/
theorem layered_slack_of_certificates {n : ℕ} {x : Sym2 (Fin n) → ℝ}
    {e₀ : RootEdge n} {μ : TreeDist n x} (hx : IsRestrictedLP e₀ x)
    (Z : ℕ → TreeSlack n)
    (hc : ∀ i < layers, ThresholdSlackCertificate e₀ μ
      (ThresholdSlack.level H layers (i + 1)) (ThresholdSlack.increment H layers i)
      (kappa (ThresholdSlack.level H layers (i + 1))) (Z i)) :
    (∀ T e, -(ThresholdSlack.beta H * x e) ≤ ThresholdSlack.combined Z layers T e) ∧
    (∀ S, S.Nonempty → S ≠ Finset.univ → e₀.edge ∉ cutEdges S →
      ∀ T, μ.prob T ≠ 0 → Odd (cutEdges S ∩ T).card →
      1 ≤ cutSum x S / 2 + ∑ e ∈ cutEdges S, ThresholdSlack.combined Z layers T e) ∧
    (∀ e, μ.expect (fun T => ThresholdSlack.combined Z layers T e) ≤ -(targetGap * x e)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T e
    simpa only [ThresholdSlack.level_last H (show 0 < layers by norm_num [layers])] using
      ThresholdSlack.combined_lower hc le_rfl T e
  · intro S hS hSu he T hT ho
    exact ThresholdSlack.combined_cut_feasible_of_root_notMem H_pos.le hx hc hS hSu he hT ho
  · intro e
    have h := ThresholdSlack.combined_expect hc e
    have hg := mul_le_mul_of_nonneg_right totalGain_gt_target.le (hx.nonneg e)
    exact h.trans (neg_le_neg hg)

end TSPGap.Song

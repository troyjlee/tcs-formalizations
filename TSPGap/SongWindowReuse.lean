/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Package
import TSPGap.SongParameters

/-!
# Reusing the proved window package at Song's parameters

The existing conditioned Lemma A.1 package can be reused with an analytic
error parameter different from the graph parameter h. Set e = (0.399/0.22)h
and l = (K-0.51)/(0.399/0.22). Its two tail inputs then match the Song
budgets exactly. Keeping a restriction mass of 0.499, rather than rounding
it to 0.49, clears p using the old, proved 0.267 layer tails.

The mean packet and 0.499 restriction mass still need the original-law
conditioning construction. This is not a substitution in the old graph
theorem, whose partition hypotheses remain too narrow.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Analytic error matching the supplied lower tail to the old package. -/
noncomputable def windowError : ℝ := (0.399 / 0.22) * h
/-- Analytic transferred-tail multiplier; not the graph parameter K. -/
noncomputable def windowBudget : ℝ := (K - 0.51) / (0.399 / 0.22)

/-- Parameter matching and the original-space margin, all exact rationals. -/
theorem window_reuse_parameters :
    0 ≤ windowError ∧ windowError ≤ 0.001 ∧
    0 ≤ windowBudget ∧ windowBudget ≤ 100 ∧
    0.22 * windowError = 0.399 * h ∧ windowBudget * windowError = (K - 0.51) * h ∧
    p < 0.499 * (0.0024 * windowBudget * windowError ^ 2) := by
  norm_num [windowError, windowBudget, K, h, p]

/-- The old analytic package's fixed mean ranges. These must be derived
from Song's graph hypotheses, not confused with the graph error parameter. -/
structure WindowMeanBounds (ν : Finset ι → ℝ) (A B V E : Finset ι) : Prop where
  a_lower : 0.997 ≤ expCard ν A
  a_away_upper : expCard ν (A \ E) ≤ 0.5024
  b_lower : 0.4977 ≤ expCard ν B
  b_upper : expCard ν B ≤ 1.0026
  v_lower : 0.997 ≤ expCard ν V
  v_upper : expCard ν V ≤ 1.502
  ab_lower : 1.9989 ≤ expCard ν (A ∪ B)
  ab_upper : expCard ν (A ∪ B) ≤ 2.502
  bv_upper : expCard ν (B ∪ V) ≤ 2.5054
  away_lower : 2.4966 ≤ expCard ν (((A ∪ B) \ E) ∪ V)
  away_upper : expCard ν (((A ∪ B) \ E) ∪ V) ≤ 3.0025

/-- Clear Song's probability from the valid older tail argument, with no
additional premise giving an unconditional 0.63 B tail in the window law. -/
theorem window_reused_kernel {ν : Finset ι → ℝ} {rank : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight rank ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B V E : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) (hE : E ⊆ A ∪ B)
    (hpres : ∀ T, ν T ≠ 0 → (T ∩ E).card = 1)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (((A ∪ B) \ E) ∪ V)).card)
    (H : WindowMeanBounds ν A B V E)
    (hlow : 0.399 * h ≤ weightMass ν (fun T => (T ∩ (((A ∪ B) \ E) ∪ V)).card ≤ 2))
    (htail : (K - 0.51) * h ≤ weightMass ν (fun T => (T ∩ (A ∪ V)).card ≤ 2)) :
    p < 0.499 * weightMass ν
      (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) := by
  obtain ⟨he0, hecap, hl0, hlcap, heq, hlq, hp⟩ := window_reuse_parameters
  have hk := lemma_A1_conditioned_budget hst hr hnn htot hAB hAV hBV hE hpres hbase
    he0 hecap hl0 hlcap H.a_lower H.a_away_upper H.b_lower H.b_upper
    H.v_lower H.v_upper H.ab_lower H.ab_upper H.bv_upper H.away_lower H.away_upper
    (by rw [heq]; exact hlow) (by rw [hlq]; exact htail)
  exact hp.trans_le (mul_le_mul_of_nonneg_left hk (by norm_num))

/-- The prospective face-times-presence/avoidance floor clears 0.499.
The factor for the two-atom face must not be dropped in the assembly. -/
theorem window_reuse_mass_budget :
    (0.499 : ℝ) < (1 - 2 * d₀) * (1 / 2 - h - 2 * r - 3 * d₀) := by
  norm_num [h, r, d₀]

omit [DecidableEq ι] in
/-- Transfer the reused kernel's strict bound through an actual restriction
and a supported happy-event identification. -/
theorem window_reused_unwind {μ ν : Finset ι → ℝ} (hμ : WeightNonneg μ)
    {P C Q : Finset ι → Prop} {M : ℝ}
    (hp : p < 0.499 * weightMass ν P) (hM : 0.499 ≤ M)
    (hunwind : weightMass ν P * M = weightMass μ (fun T => P T ∧ C T))
    (hQ : ∀ T, μ T ≠ 0 → P T ∧ C T → Q T) : p < weightMass μ Q := by
  have hp0 : 0 < p := by norm_num [p]
  have hP0 : 0 ≤ weightMass ν P := by linarith only [hp, hp0]
  have hm : 0.499 * weightMass ν P ≤ weightMass ν P * M := by
    nlinarith only [mul_le_mul_of_nonneg_right hM hP0]
  rw [hunwind] at hm
  apply (hp.trans_le hm).trans_le
  classical
  unfold weightMass
  apply sum_le_sum
  intro T _
  by_cases hz : μ T = 0
  · simp [hz]
  by_cases he : P T ∧ C T
  · simp [he, hQ T hz he]
  · simp only [if_neg he]
    split_ifs <;> first | exact hμ T | exact le_rfl

end TSPGap.Song

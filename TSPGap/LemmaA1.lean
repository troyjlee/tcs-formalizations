/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma523

/-!
# KKO21 Lemma A.1: the 2-1-1 kernel

The first ingredient is the short PF₂ bootstrap used in the paper.  If a
probability sequence has at least `0.22ε` mass in ranks at most two and at
least `1/4` mass at rank three, then rank two itself has mass at least
`0.2ε`, for `ε ≤ 0.001`.

The proof uses the full PF₂ inequalities rather than adjacent
log-concavity.  Besides `p₁p₃ ≤ p₂²`, the nonadjacent instance
`p₀p₃ ≤ p₁p₂` handles the possible zero cells without division.
-/

namespace TSPGap

/-! ### The PF₂ bootstrap -/

/-- **The log-concavity bootstrap in KKO21 Lemma A.1.**  A nonnegative PF₂
sequence with `p₃ ≥ 0.14` and `p₀+p₁+p₂ ≥ 0.22ε` must have
`p₂ ≥ 0.2ε`, provided `0 ≤ ε ≤ 0.001`.

The constants have ample room: if `p₂ < 0.2ε`, PF₂ gives
`p₁ ≤ 0.00143p₂` and `p₀ ≤ 0.00143p₁`, contradicting the
lower bound on the first three cells. -/
theorem pf2_rank_two_ge {p : ℕ → ℝ} (hnn : SeqNonneg p) (hpf : PF2 p)
    {ε : ℝ} (_hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (h3 : (0.14 : ℝ) ≤ p 3)
    (hle2 : 0.22 * ε ≤ p 0 + p 1 + p 2) :
    0.2 * ε ≤ p 2 := by
  by_contra h2
  have hp0 := hnn 0
  have hp1 := hnn 1
  have hp2 := hnn 2
  have h2lt : p 2 < 0.2 * ε := lt_of_not_ge h2
  have h13 := hpf 1 2 (by omega)
  have h03 := hpf 0 2 (by omega)
  norm_num at h13 h03
  have h3p1 : 0.14 * p 1 ≤ p 1 * p 3 := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h3 hp1
  have h2sq : p 2 * p 2 ≤ (0.2 * ε) * p 2 :=
    mul_le_mul_of_nonneg_right h2lt.le hp2
  have h1fine : p 1 ≤ (10 / 7) * ε * p 2 := by
    linarith
  have h1coarse : p 1 ≤ 0.00143 * p 2 := by
    have hcoef : (10 / 7) * ε ≤ 0.00143 := by linarith
    exact le_trans h1fine (mul_le_mul_of_nonneg_right hcoef hp2)
  have h3p0 : 0.14 * p 0 ≤ p 0 * p 3 := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h3 hp0
  have hp1p2 : p 1 * p 2 ≤ p 1 * (0.2 * ε) :=
    mul_le_mul_of_nonneg_left h2lt.le hp1
  have h0fine : p 0 ≤ (10 / 7) * ε * p 1 := by
    linarith
  have h0coarse : p 0 ≤ 0.00143 * p 1 := by
    have hcoef : (10 / 7) * ε ≤ 0.00143 := by linarith
    exact le_trans h0fine (mul_le_mul_of_nonneg_right hcoef hp1)
  linarith

/-- The weight-level form of `pf2_rank_two_ge`.  Stability supplies a
Bernoulli rank law, hence PF₂, while the event `{N ≤ 2}` is split into its
three point masses without any support assumption. -/
theorem weightMass_rank_two_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (h3 : (0.14 : ℝ) ≤ weightMass w (fun T => (T ∩ F).card = 3))
    (hle2 : 0.22 * ε ≤ weightMass w (fun T => (T ∩ F).card ≤ 2)) :
    0.2 * ε ≤ weightMass w (fun T => (T ∩ F).card = 2) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  let p : ℕ → ℝ := fun k => weightMass w (fun T => (T ∩ F).card = k)
  have hpnn : SeqNonneg p := fun k => weightMass_nonneg hnn _
  have hppf : PF2 p := by
    intro i j hij
    change weightMass w (fun T => (T ∩ F).card = i)
        * weightMass w (fun T => (T ∩ F).card = j + 1)
      ≤ weightMass w (fun T => (T ∩ F).card = i + 1)
        * weightMass w (fun T => (T ∩ F).card = j)
    rw [hlaw i, hlaw (j + 1), hlaw (i + 1), hlaw j]
    exact Bernoulli.pf2_probCount q (fun k => ⟨(hq k).1.le, (hq k).2⟩) i j hij
  have hsplit := weightMass_three_cells w (fun T => (T ∩ F).card ≤ 2)
    (fun T => (T ∩ F).card) fun _ h => h
  have hcell : ∀ k : ℕ, k ≤ 2 →
      weightMass w (fun T => (T ∩ F).card ≤ 2 ∧ (T ∩ F).card = k) = p k := by
    intro k hk
    exact weightMass_congr fun T => by
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by omega, h⟩
  rw [hsplit, hcell 0 (by omega), hcell 1 (by omega), hcell 2 (by omega)] at hle2
  exact pf2_rank_two_ge hpnn hppf hε0 hεcap h3 hle2

end TSPGap

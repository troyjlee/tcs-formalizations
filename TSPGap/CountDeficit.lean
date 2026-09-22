/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankTail
import TSPGap.CountEstimates
import TSPGap.LogConcave

/-!
# Lower tails from a mean deficit and order-two inequalities

For Lemma 5.22, the existing mean ceiling is `3 - 1.49ε`. Plain Markov
gives only `0.496ε` below level three. The Bernoulli count law's `PF2`
inequalities improve this to `1.48ε`, for `ε ≤ 0.0002`.

If `L = p₀ + p₁ + p₂` were that small, the mean ceiling forces
`p₃ ≥ 1 - 4L > 1/2`. Then `p₁ p₃ ≤ p₂²` and `p₀ p₃ ≤ p₁ p₂`
give `p₁ ≤ 2L²` and `p₀ ≤ p₁`. Consequently the deficit below mean
three is at most `L + 6L²`, contradicting a deficit of `1.49ε`.

This supplies a rigorous replacement for the paper's informal Markov
step, without asserting the false bound `P[X ≤ 2] ≥ 3 - E[X]`.
The payment constants are not changed by this module.
-/

namespace TSPGap

open Finset

/-- The first moment dominates its truncation at any integer level. -/
theorem truncated_mean_le {p : ℕ → ℝ} (hp : SeqNonneg p) {N k : ℕ}
    (hk : k ≤ N) (htot : ∑ i ∈ range N, p i = 1) :
    (∑ i ∈ range k, (i : ℝ) * p i) + k * (1 - ∑ i ∈ range k, p i)
      ≤ ∑ i ∈ range N, (i : ℝ) * p i := by
  have hmass := sum_range_add_sum_Ico p hk
  rw [htot] at hmass
  have htail : (k : ℝ) * ∑ i ∈ Ico k N, p i
      ≤ ∑ i ∈ Ico k N, (i : ℝ) * p i := by
    rw [mul_sum]
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (mem_Ico.mp hi).1) (hp i)
  rw [← sum_range_add_sum_Ico (fun i => (i : ℝ) * p i) hk]
  nlinarith

/-- Two elementary moment consequences at levels three and four. -/
theorem deficit_three_bounds {p : ℕ → ℝ} (hp : SeqNonneg p) {N : ℕ}
    (hN : 4 ≤ N) (htot : ∑ i ∈ range N, p i = 1) :
    3 - (∑ i ∈ range N, (i : ℝ) * p i) ≤ 3 * p 0 + 2 * p 1 + p 2 ∧
    4 - (∑ i ∈ range N, (i : ℝ) * p i) - 4 * (p 0 + p 1 + p 2) ≤ p 3 := by
  have h3 := truncated_mean_le hp (by omega : 3 ≤ N) htot
  have h4 := truncated_mean_le hp hN htot
  norm_num [sum_range_succ] at h3 h4
  constructor <;> nlinarith [hp 1, hp 2]

/-- The numerical PF2 repair for the lower-tail input of Lemma 5.22. -/
theorem lower_tail_three_ge_of_pf2_deficit
    {p₀ p₁ p₂ p₃ μ ε : ℝ}
    (h0 : 0 ≤ p₀) (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂)
    (h02 : p₀ * p₃ ≤ p₁ * p₂) (h12 : p₁ * p₃ ≤ p₂ ^ 2)
    (hdef : 3 - μ ≤ 3 * p₀ + 2 * p₁ + p₂)
    (h3 : 4 - μ - 4 * (p₀ + p₁ + p₂) ≤ p₃)
    (hεcap : ε ≤ 0.0002) (hμ : μ ≤ 3 - 1.49 * ε) :
    1.48 * ε ≤ p₀ + p₁ + p₂ := by
  by_contra h
  push Not at h
  let L := p₀ + p₁ + p₂
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hL : L < 1.48 * ε := h
  have hLcap : L < 0.000296 := by linarith
  have hp3 : 1 / 2 < p₃ := by dsimp [L] at hLcap; linarith
  have hp2L : p₂ ≤ L := by dsimp [L]; linarith
  have hp2p3 : p₂ ≤ p₃ := by linarith
  have hp01 : p₀ ≤ p₁ := by
    have hm := mul_le_mul_of_nonneg_left hp2p3 h1
    exact le_of_mul_le_mul_right (h02.trans hm) (by linarith)
  have hp1L : p₁ ≤ 2 * L ^ 2 := by
    have hs : p₂ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h2 hp2L 2
    nlinarith
  have hδ : 1.49 * ε ≤ L + 6 * L ^ 2 := by dsimp [L] at hp1L ⊢; nlinarith
  have hLsq : L ^ 2 ≤ (1.48 * ε) ^ 2 := pow_le_pow_left₀ hL0 hL.le 2
  have hεsq : ε ^ 2 ≤ 0.0002 * ε := by nlinarith
  nlinarith

/-- A Bernoulli count with mean at most `3 - 1.49ε` has lower tail
at least `1.48ε`. No lower bound on the mean is needed. -/
theorem Bernoulli.probCount_le_two_ge_of_deficit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hεcap : ε ≤ 0.0002) (hμ : ∑ i, q i ≤ 3 - 1.49 * ε) :
    1.48 * ε ≤ probCount q 0 + probCount q 1 + probCount q 2 := by
  have hnn : SeqNonneg (probCount q) := by
    intro k
    rw [probCount_eq_coeff]
    exact (pf2_bernoulli_prod q univ fun i _ => hq i).1 k
  have hpf := pf2_probCount q hq
  have htotal := sum_range_probCount_eq_one q
    (show Fintype.card ι ≤ Fintype.card ι + 3 by omega)
  have hmean := sum_range_mul_probCount q
    (show Fintype.card ι ≤ Fintype.card ι + 3 by omega)
  have hb := deficit_three_bounds hnn (by omega : 4 ≤ Fintype.card ι + 3 + 1) htotal
  rw [hmean] at hb
  exact lower_tail_three_ge_of_pf2_deficit (hnn 0) (hnn 1) (hnn 2)
    (hpf 0 2 (by omega)) (by simpa [pow_two] using hpf 1 2 (by omega))
    hb.1 hb.2 hεcap hμ

/-- The normalized stable-weight version, ready for either the simple-edge
or refined-piece instance of Lemma 5.22. -/
theorem weightMass_le_two_ge_of_deficit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {ε : ℝ}
    (hεcap : ε ≤ 0.0002) (hμ : expCard w F ≤ 3 - 1.49 * ε) :
    1.48 * ε ≤ weightMass w (fun T => (T ∩ F).card ≤ 2) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard w F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hq' : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨(hq i).1.le, (hq i).2⟩
  have h := Bernoulli.probCount_le_two_ge_of_deficit hq' hεcap
    (by rw [← hmean]; exact hμ)
  rw [← hlaw 0, ← hlaw 1, ← hlaw 2] at h
  have hsplit : weightMass w (fun T => (T ∩ F).card ≤ 2) =
      weightMass w (fun T => (T ∩ F).card = 0) +
      weightMass w (fun T => (T ∩ F).card = 1) +
      weightMass w (fun T => (T ∩ F).card = 2) := by
    simp only [weightMass, ← sum_add_distrib]
    refine sum_congr rfl fun T _ => ?_
    by_cases h0 : (T ∩ F).card = 0
    · simp [h0]
    by_cases h1 : (T ∩ F).card = 1
    · simp [h1]
    by_cases h2 : (T ∩ F).card = 2
    · simp [h2]
    have hn : ¬ (T ∩ F).card ≤ 2 := by omega
    simp [h0, h1, h2, hn]
  rw [hsplit]
  exact h

/-- The analogous point-mass bootstrap. A fixed positive mass at level
three prevents the mean deficit from hiding at levels zero and one. -/
theorem point_mass_two_ge_of_pf2_deficit
    {p₀ p₁ p₂ p₃ μ ε : ℝ}
    (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h3 : 0.1 ≤ p₃)
    (h02 : p₀ * p₃ ≤ p₁ * p₂) (h12 : p₁ * p₃ ≤ p₂ ^ 2)
    (hdef : 3 - μ ≤ 3 * p₀ + 2 * p₁ + p₂)
    (hεcap : ε ≤ 0.0002) (hμ : μ ≤ 3 - 1.6 * ε) :
    1.5 * ε ≤ p₂ := by
  by_contra h
  push Not at h
  have hp2p3 : p₂ ≤ p₃ := by linarith
  have hp01 : p₀ ≤ p₁ := by
    have hm := mul_le_mul_of_nonneg_left hp2p3 h1
    exact le_of_mul_le_mul_right (h02.trans hm) (by linarith)
  have hp1 : p₁ ≤ 10 * p₂ ^ 2 := by nlinarith
  have hδ : 1.6 * ε ≤ p₂ + 50 * p₂ ^ 2 := by linarith
  have hsq : p₂ ^ 2 ≤ (1.5 * ε) ^ 2 := pow_le_pow_left₀ h2 h.le 2
  have hεsq : ε ^ 2 ≤ 0.0002 * ε := by nlinarith
  nlinarith

/-- With the existing first-stage factor `0.12`, the improved lower-tail
input `1.48ε`, upper-tail input `0.59`, and layer mass `ε` suffice for
the original `0.005ε²` thinning threshold after unwinding mass `0.499`. -/
theorem lemma522_recovered_constant {ε : ℝ} (hεcap : ε ≤ 0.0002) :
    0.005 * ε ^ 2 * (1 - 2 * (0.577 * 0.147 * ε)) ≤
      0.499 * ε * 0.12 * (0.577 * 0.147 * ε) * (1 - 3 * (0.577 * 0.147 * ε)) := by
  have hεsq : ε ^ 2 * ε ≤ 0.0002 * ε ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hεcap (sq_nonneg ε)]
  nlinarith [sq_nonneg ε]

/-- The exact Bernoulli counterexample to the coefficient-one Markov claim:
`Bin(3, 1-d/3)` has mean `3-d`, but its lower tail is smaller than `d`. -/
theorem binomial_three_tail_lt_deficit {d : ℝ} (hd : 0 < d) (hd3 : d < 3) :
    1 - (1 - d / 3) ^ 3 < d := by
  have hpos : 0 < d ^ 2 * (9 - d) := mul_pos (sq_pos_of_pos hd) (by linarith)
  nlinarith

end TSPGap

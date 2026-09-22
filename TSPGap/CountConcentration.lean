/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountDeficit

/-!
# Concentration at two from a small lower tail

For the larger Lemma 5.27 threshold, the crude first-moment estimate loses
three times the lower tail. PF₂ makes the zero cell quadratic in that tail,
so the loss is only twice the tail plus the mean excess and a quadratic
correction. This file does not change the end-to-end probability budget.
-/

namespace TSPGap
open Finset

/-- The scalar PF₂ concentration estimate used in the repaired Eq. (56). -/
theorem concentration_two_of_pf2
    {p₀ p₁ p₂ μ ε : ℝ} (h0 : 0 ≤ p₀) (h1 : 0 ≤ p₁)
    (hpf : p₀ * p₂ ≤ p₁ ^ 2)
    (hmoment : 3 - μ - 3 * p₀ - 2 * p₁ ≤ p₂)
    (htail : p₀ + p₁ ≤ 17.25 * ε)
    (hεcap : ε ≤ 0.0002) (hmean : μ ≤ 2 + 3.2 * ε) :
    1 - 38 * ε ≤ p₂ := by
  let L := p₀ + p₁
  have hL0 : 0 ≤ L := add_nonneg h0 h1
  have hL : L ≤ 17.25 * ε := htail
  have hLcap : L ≤ 0.00345 := by linarith
  have hp2 : 1 / 2 ≤ p₂ := by dsimp [L] at hLcap; linarith
  have hp1L : p₁ ≤ L := by dsimp [L]; linarith
  have hs : p₁ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h1 hp1L 2
  have hp0 : p₀ ≤ 2 * L ^ 2 := by nlinarith
  have hsq : L ^ 2 ≤ (17.25 * ε) ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have hεsq : ε ^ 2 ≤ 0.0002 * ε := by nlinarith
  dsimp [L] at hp0 hsq hL
  nlinarith

/-- A Bernoulli sum with small lower tail and mean just above two is
concentrated at two; the zero cell is controlled by PF₂. -/
theorem Bernoulli.probCount_two_ge_of_small_lower_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (htail : probCount q 0 + probCount q 1 ≤ 17.25 * ε)
    (hεcap : ε ≤ 0.0002) (hmean : ∑ i, q i ≤ 2 + 3.2 * ε) :
    1 - 38 * ε ≤ probCount q 2 := by
  have hnn : SeqNonneg (probCount q) := by
    intro k
    rw [probCount_eq_coeff]
    exact (pf2_bernoulli_prod q univ fun i _ => hq i).1 k
  have hpf := pf2_probCount q hq
  have htotal := sum_range_probCount_eq_one q
    (show Fintype.card ι ≤ Fintype.card ι + 3 by omega)
  have hsum := sum_range_mul_probCount q
    (show Fintype.card ι ≤ Fintype.card ι + 3 by omega)
  have hm := truncated_mean_le hnn
    (by omega : 3 ≤ Fintype.card ι + 3 + 1) htotal
  rw [hsum] at hm
  norm_num [sum_range_succ] at hm
  exact concentration_two_of_pf2 (hnn 0) (hnn 1)
    (by simpa [pow_two] using hpf 0 1 (by omega))
    (by linarith) htail hεcap hmean

/-- Stable fixed-rank count adapter, valid for ordinary edges and pieces. -/
theorem weightMass_two_ge_of_small_lower_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι] {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {ε : ℝ}
    (htail : weightMass w (fun T => (T ∩ F).card ≤ 1) ≤ 17.25 * ε)
    (hεcap : ε ≤ 0.0002) (hmean : expCard w F ≤ 2 + 3.2 * ε) :
    1 - 38 * ε ≤ weightMass w (fun T => (T ∩ F).card = 2) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmeanq := expCard_eq_sum_of_rankLaw hlaw
  have hsplit : weightMass w (fun T => (T ∩ F).card ≤ 1) =
      weightMass w (fun T => (T ∩ F).card = 0) +
      weightMass w (fun T => (T ∩ F).card = 1) := by
    simp only [weightMass, ← sum_add_distrib]
    refine sum_congr rfl fun T _ => ?_
    by_cases h0 : (T ∩ F).card = 0
    · simp [h0]
    by_cases h1 : (T ∩ F).card = 1
    · simp [h1]
    have hnot : ¬ (T ∩ F).card ≤ 1 := by omega
    simp [h0, h1, hnot]
  rw [hsplit, hlaw 0, hlaw 1] at htail
  rw [hlaw 2]
  exact Bernoulli.probCount_two_ge_of_small_lower_tail
    (fun i => ⟨(hq i).1.le, (hq i).2⟩) htail hεcap
    (by rw [← hmeanq]; exact hmean)

end TSPGap

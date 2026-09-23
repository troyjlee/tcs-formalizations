/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Package

/-!
# KKO21 Lemma 5.15: the low tail of a 2-2 good bundle

For a 2-2 good half bundle `e = (u,v)`, with `X := (δ(u)∖e)_T + (δ(v)∖e)_T`
under the two-atom face: whenever `δ(u)_T = δ(v)_T = 2` one has `X ∈ {2, 4}`
(the bundle is one-hot), so 2-2 goodness gives `P[X ≤ 2] + P[X ≥ 4] ≥ 3ε`.
KKO then bound `P[X ≥ 4]` through the mean and log-concavity and conclude
`P[X ≤ 2] ≥ 0.4ε`.

This file proves that analytic step over an abstract stable law
(`lemma_5_15_low_tail`): a baseline of one, mean in `[2.4966, 3 + 2.19ε]`,
and the goodness input.  With `p₀ = 0`,

`E[X] ≥ p₁ + 2p₂ + 3p₃ + 4p_{≥4} = 3 − 2p₁ − p₂ + p_{≥4}`,

so `p_{≥4} ≤ 2.19ε + 2p₁ + p₂`; PF₂ gives `p₁ ≤ p₂²/p₃ ≤ p₂²/0.14`; and if
`s := p_{≤2} < 0.4ε` then `p_{≥4} ≤ 2.19ε + 1.006 s`, whence
`s + p_{≥4} < 2.994ε < 3ε`, a contradiction.  The three-count `p₃ ≥ 0.14`
is `weightMass_eq_three_ge_of_baseline`.

The instantiation at the two-atom face of a spanning-tree law, together
with the count identity behind "`X ∈ {2,4}`", is the graph-facing layer,
done where Lemma A.1 is assembled.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mean dominates the truncated moment `p₁ + 2p₂ + 3p₃ + 4p_{≥4}`. -/
theorem expCard_ge_truncated_moment {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) :
    weightMass w (fun T => (T ∩ F).card = 1)
      + 2 * weightMass w (fun T => (T ∩ F).card = 2)
      + 3 * weightMass w (fun T => (T ∩ F).card = 3)
      + 4 * weightMass w (fun T => 4 ≤ (T ∩ F).card)
      ≤ expCard w F := by
  classical
  simp only [weightMass, expCard, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  have hw := hnn S
  rcases Nat.lt_or_ge (S ∩ F).card 4 with h4 | h4
  · rcases (by omega : (S ∩ F).card = 0 ∨ (S ∩ F).card = 1 ∨ (S ∩ F).card = 2
        ∨ (S ∩ F).card = 3) with hc | hc | hc | hc <;> simp [hc] <;> nlinarith
  · have h1 : (S ∩ F).card ≠ 1 := by omega
    have h2 : (S ∩ F).card ≠ 2 := by omega
    have h3 : (S ∩ F).card ≠ 3 := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    have : (4 : ℝ) ≤ ((S ∩ F).card : ℝ) := by exact_mod_cast h4
    nlinarith

/-- The four cells partition the mass when the count is never zero. -/
theorem weightMass_four_cells_of_baseline {w : Finset ι → ℝ}
    (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card) :
    weightMass w (fun T => (T ∩ F).card = 1)
      + weightMass w (fun T => (T ∩ F).card = 2)
      + weightMass w (fun T => (T ∩ F).card = 3)
      + weightMass w (fun T => 4 ≤ (T ∩ F).card) = 1 := by
  classical
  rw [← htot, totalMass]
  simp only [weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · have hb := hbase S h0
    rcases Nat.lt_or_ge (S ∩ F).card 4 with h4 | h4
    · rcases (by omega : (S ∩ F).card = 1 ∨ (S ∩ F).card = 2
          ∨ (S ∩ F).card = 3) with hc | hc | hc <;> simp [hc]
    · have h1 : (S ∩ F).card ≠ 1 := by omega
      have h2 : (S ∩ F).card ≠ 2 := by omega
      have h3 : (S ∩ F).card ≠ 3 := by omega
      rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
      ring

/-- **Lemma 5.15's low tail.**  Baseline one, mean in `[2.4966, 3 + 2.19ε]`,
and `P[X ≤ 2] + P[X ≥ 4] ≥ 3ε` give `P[X ≤ 2] ≥ 0.4ε`. -/
theorem lemma_5_15_low_tail {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ F).card)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hm1 : 2.4966 ≤ expCard w F) (hm2 : expCard w F ≤ 3 + 2.19 * ε)
    (hgood : 3 * ε ≤ weightMass w (fun T => (T ∩ F).card ≤ 2)
      + weightMass w (fun T => 4 ≤ (T ∩ F).card)) :
    0.4 * ε ≤ weightMass w (fun T => (T ∩ F).card ≤ 2) := by
  classical
  -- the three-count
  have hp3 := weightMass_eq_three_ge_of_baseline hst hr hnn htot hbase hm1
    (by linarith)
  -- PF₂ at `(1, 2)` from the rank law
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hpf : weightMass w (fun T => (T ∩ F).card = 1)
        * weightMass w (fun T => (T ∩ F).card = 3)
      ≤ weightMass w (fun T => (T ∩ F).card = 2)
        * weightMass w (fun T => (T ∩ F).card = 2) := by
    rw [hlaw 1, hlaw 3, hlaw 2]
    have := Bernoulli.pf2_probCount q (fun k => ⟨(hq k).1.le, (hq k).2⟩) 1 2
      (by omega)
    simpa using this
  -- the cells
  have hmom := expCard_ge_truncated_moment hnn F
  have hpart := weightMass_four_cells_of_baseline htot hbase
  have hle2 : weightMass w (fun T => (T ∩ F).card ≤ 2)
      = weightMass w (fun T => (T ∩ F).card = 1)
        + weightMass w (fun T => (T ∩ F).card = 2) := by
    have h := weightMass_three_cells w (fun T => (T ∩ F).card ≤ 2)
      (fun T => (T ∩ F).card) fun _ h => h
    have hc0 : weightMass w (fun T => (T ∩ F).card ≤ 2 ∧ (T ∩ F).card = 0) = 0 := by
      refine (weightMass_congr_of_support (B := fun _ => False) ?_).trans
        (weightMass_false w)
      intro S hS
      have := hbase S hS
      constructor
      · rintro ⟨-, h0⟩; omega
      · intro h; exact h.elim
    have hc1 : weightMass w (fun T => (T ∩ F).card ≤ 2 ∧ (T ∩ F).card = 1)
        = weightMass w (fun T => (T ∩ F).card = 1) :=
      weightMass_congr fun T => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    have hc2 : weightMass w (fun T => (T ∩ F).card ≤ 2 ∧ (T ∩ F).card = 2)
        = weightMass w (fun T => (T ∩ F).card = 2) :=
      weightMass_congr fun T => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [h, hc0, hc1, hc2, zero_add]
  rw [hle2] at hgood ⊢
  set p1 := weightMass w (fun T => (T ∩ F).card = 1) with hp1
  set p2 := weightMass w (fun T => (T ∩ F).card = 2) with hp2
  set p3 := weightMass w (fun T => (T ∩ F).card = 3) with hp3def
  set p4 := weightMass w (fun T => 4 ≤ (T ∩ F).card) with hp4
  have hp1nn : 0 ≤ p1 := weightMass_nonneg hnn _
  have hp2nn : 0 ≤ p2 := weightMass_nonneg hnn _
  have hp4nn : 0 ≤ p4 := weightMass_nonneg hnn _
  by_contra hcon
  have hs : p1 + p2 < 0.4 * ε := lt_of_not_ge hcon
  -- `p₄ ≤ 2.19ε + 2p₁ + p₂`
  have hp4le : p4 ≤ 2.19 * ε + 2 * p1 + p2 := by linarith
  -- `p₁ ≤ p₂² / 0.14 ≤ 0.00286 p₂` since `p₂ < 0.0004`
  have hp1le : 0.14 * p1 ≤ p2 * p2 := by nlinarith
  have hp2small : p2 < 0.0004 := by linarith
  have hp1le' : p1 ≤ 0.00286 * p2 := by nlinarith
  linarith

end TSPGap

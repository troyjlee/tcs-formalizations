/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BernoulliLowerTail
import TSPGap.SongBadIncidentLayer

/-!
# Song's bad-incident analytic kernel (Lemma 14)

With `A = δ↑(u)` and `B = δ(v)`, the paper's variables are `X = A_T`
and `Y = B_T - 1`. Splitting at `P[A_T + B_T = 3] = 63.02h`, both
branches give strictly more than `8h` for `A_T = 1, B_T = 2`.
This theorem takes the nested-law means explicitly; it does not yet
construct that law or transfer its probability to bundle goodness.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `7/16` lower tail after removing the sure success in B. -/
theorem weightMass_le_two_ge_seven_sixteenths {w : Finset ι → ℝ} {rank : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight rank w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {B : Finset ι}
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card) (hmean : expCard w B ≤ 5 / 2) :
    (7 / 16 : ℝ) ≤ weightMass w (fun T => (T ∩ B).card ≤ 2) := by
  obtain ⟨m, q, hq, hs, hl⟩ := exists_shift_of_baseline hst hr hnn htot hbase
  have h := bernoulli_le_one_ge_seven_sixteenths q hq (by rw [hs]; linarith)
  rw [← hl 0, ← hl 1] at h
  have hor := weightMass_or w (fun T => (T ∩ B).card = 1) (fun T => (T ∩ B).card = 2)
  have hand : weightMass w (fun T => (T ∩ B).card = 1 ∧ (T ∩ B).card = 2) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    constructor
    · rintro ⟨h1, h2⟩; omega
    · intro hf; exact hf.elim
  have he : weightMass w (fun T => (T ∩ B).card = 1 ∨ (T ∩ B).card = 2) =
      weightMass w (fun T => (T ∩ B).card ≤ 2) := by
    refine weightMass_congr_of_support fun T hT => ?_
    have := hbase T hT
    omega
  rw [he, hand] at hor
  norm_num at h
  linarith

/-- The complete analytic kernel of Song's Lemma 14, with exact parameters. -/
theorem bad_incident_kernel {ν : Finset ι → ℝ} {rank : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight rank ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ B).card)
    (hA1 : 1 / 2 + kGood * h - d₀ / 2 ≤ expCard ν A)
    (hA2 : expCard ν A ≤ 1 + d₀)
    (hB1 : 3 / 2 + kGood * h - 9 / 2 * d₀ ≤ expCard ν B)
    (hB2 : expCard ν B ≤ 5 / 2 - kGood * h + 4 * d₀) :
    8 * h < weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2) := by
  by_cases hP3 : 63.02 * h ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3)
  · have hAle : (0.4999 : ℝ) ≤ weightMass ν (fun T => (T ∩ A).card ≤ 1) := by
      have ht := two_mul_weightMass_le_one_ge hnn A
      rw [htot] at ht
      norm_num [d₀] at hA2
      linarith
    have hBge : (0.39 : ℝ) ≤ weightMass ν (fun T => 2 ≤ (T ∩ B).card) := by
      apply weightMass_two_le_ge_of_baseline hst hr hnn htot hbase
      norm_num [h, kGood, d₀] at hB1 ⊢
      linarith
    have hAge : (0.393469 : ℝ) ≤ weightMass ν (fun T => 1 ≤ (T ∩ A).card) := by
      have ht := one_sub_exp_le_weightMass_one_le hst hr hnn htot A
      have he : Real.exp (-expCard ν A) ≤ Real.exp (-(1 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        norm_num [h, kGood, d₀] at hA1 ⊢
        linarith
      linarith [he.trans exp_neg_half_le]
    have hBle : (7 / 16 : ℝ) ≤ weightMass ν (fun T => (T ∩ B).card ≤ 2) := by
      apply weightMass_le_two_ge_seven_sixteenths hst hr hnn htot hbase
      norm_num [h, kGood, d₀] at hB2 ⊢
      linarith
    have hlow : (0.1721426875 : ℝ) ≤ weightMass ν (fun T => (T ∩ A).card ≤ 0 + 1) *
        weightMass ν (fun T => 1 + 1 ≤ (T ∩ B).card) := by
      have ht := mul_le_mul hAle hBge (by norm_num) (weightMass_nonneg hnn _)
      norm_num at ht ⊢
      linarith
    have hhigh : (0.1721426875 : ℝ) ≤ weightMass ν (fun T => 0 + 1 ≤ (T ∩ A).card) *
        weightMass ν (fun T => (T ∩ B).card ≤ 1 + 1) := by
      have ht := mul_le_mul hAge hBle (by norm_num) (weightMass_nonneg hnn _)
      norm_num at ht ⊢
      linarith
    have ht := three_cell_bound_shifted hst hr hnn htot hAB 0 1
      (fun _ _ => Nat.zero_le _) hbase (ε := 0.1721426875)
      (by norm_num) (by norm_num) hlow hhigh
    norm_num at ht
    norm_num [h] at hP3 ⊢
    linarith only [ht, hP3]
  · exact bad_incident_thin hst hr hnn htot hAB hbase hA1 hA2 hB1 hB2 (lt_of_not_ge hP3)

end TSPGap.Song

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The three-count mean profiles for the capacity applications

These are numerical input checks, not probability lower bounds. The
capacity theorem and coefficient-extraction theorem are separate obligations.
The inputs below are exactly the mean intervals already proved in the
indexed Lemmas 5.21 and 5.22, with the last count shifted by one in 5.21.

The profile controls every nonempty subset of size *at most* the level,
not merely subsets of size exactly the level.
-/

namespace TSPGap

/-- Three levels of the absolute subset-mean error profile at target `(1,1,1)`. -/
def ThreeMeanProfile (μ : Fin 3 → ℝ) (b : Fin 3 → ℝ) : Prop :=
  ∀ (S : Finset (Fin 3)) (k : Fin 3), S.Nonempty → S.card ≤ k.val + 1 →
    |(∑ i ∈ S, μ i) - (S.card : ℝ)| ≤ 1 - b k

/-- The seven nonempty-subset checks suffice, provided later profile levels
are no larger. This is the interface used by both numerical adapters. -/
theorem threeMeanProfile_of_seven {a b c b₁ b₂ b₃ : ℝ}
    (hb21 : b₂ ≤ b₁) (hb32 : b₃ ≤ b₂)
    (ha : |a - 1| ≤ 1 - b₁) (hb : |b - 1| ≤ 1 - b₁)
    (hc : |c - 1| ≤ 1 - b₁)
    (hab : |a + b - 2| ≤ 1 - b₂)
    (hac : |a + c - 2| ≤ 1 - b₂)
    (hbc : |b + c - 2| ≤ 1 - b₂)
    (habc : |a + b + c - 3| ≤ 1 - b₃) :
    ThreeMeanProfile ![a, b, c] ![b₁, b₂, b₃] := by
  intro S k hS hk
  fin_cases S <;> fin_cases k <;>
    norm_num [Finset.Nonempty, Fin.sum_univ_succ, Finset.sum_insert,
      Finset.sum_singleton] at *
  all_goals simp only [abs_le] at *
  all_goals constructor <;> linarith

/-- Shifted Lemma 5.21 means. `v` is the original, unshifted final count. -/
theorem lemma521_capacity_profile {a b v ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 0.0002)
    (ha : 0.5 ≤ a ∧ a ≤ 1.5) (hb : 0.5 ≤ b ∧ b ≤ 1.5)
    (hv : 1.5 ≤ v ∧ v ≤ 2.01)
    (hab : 1.499 ≤ a + b ∧ a + b ≤ 2.01)
    (hav : 2 + 1.9 * ε ≤ a + v ∧ a + v ≤ 3.01)
    (hbv : 2 + 1.9 * ε ≤ b + v ∧ b + v ≤ 3.01)
    (habv : 3 + 1.8 * ε ≤ a + b + v ∧ a + b + v ≤ 4.01) :
    ThreeMeanProfile ![a, b, v - 1] ![0.499, 1.9 * ε, 1.8 * ε] := by
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

/-- Lemma 5.22 uses the proved `1.49 ε` deficit, not the paper's sharper
mean assumptions. This still clears the first Gurvits objective. -/
theorem lemma522_capacity_profile {a b v ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 0.0002)
    (ha : 0.4977 ≤ a ∧ a ≤ 1.5) (hb : 0.4977 ≤ b ∧ b ≤ 1.5)
    (hv : 0.9989 ≤ v ∧ v ≤ 1.502)
    (hab : 1.9989 ≤ a + b ∧ a + b ≤ 2.502)
    (hav : 1.99 ≤ a + v ∧ a + v ≤ 3 - 1.49 * ε)
    (hbv : 1.99 ≤ b + v ∧ b + v ≤ 3 - 1.49 * ε)
    (habv : 2.99 ≤ a + b + v ∧ a + b + v ≤ 4 - 1.6 * ε) :
    ThreeMeanProfile ![a, b, v] ![0.497, 1.49 * ε, 1.49 * ε] := by
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

/-- The proposed 5.21 coefficient after the `exp(3) ≤ 21` extraction and
the already proved conditioning-mass floor. No probability claim is made here. -/
theorem lemma521_capacity_budget (ε : ℝ) :
    0.04 * ε ^ 2 ≤ 0.499 * (0.499 * (1.9 * ε) * (1.8 * ε)) / 21 := by
  nlinarith [sq_nonneg ε]

/-- The corresponding safe 5.22 coefficient, using the repaired means. -/
theorem lemma522_capacity_budget (ε : ℝ) :
    0.026 * ε ^ 2 ≤ 0.499 * (0.497 * (1.49 * ε) * (1.49 * ε)) / 21 := by
  nlinarith [sq_nonneg ε]

end TSPGap

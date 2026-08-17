/-
# A closed-form `κ` for Theorem 1.9

`Schedule.exists_isRobustSunflower_of_kappa` is Theorem 1.9 for every `κ` clearing

  `128·L ≤ κa`,    `2048·L²·log(8/b) ≤ κa`,    `4096·L·(log₂w + 1) ≤ κa`,

with `L = schedL κ b = log₂⌈κ⌉ + log₂⌈16/b⌉ + 4`. This file exhibits one:

  `κ₀ := (2^20/a)·(lg(16/b) + lg w + lg(1/a) + 20)³`,

verifies the three conditions for it, and reads off Theorem 1.9 with no hypothesis on `κ` at
all (`exists_isRobustSunflower`).

## Why this shape

The conditions are self-referential — `L` is about `log κ` while `κ` must beat `L²` — so the
cube is what absorbs the feedback: writing `S` for the bracket, `lg κ₀ ≤ 40 + lg(1/a) + 6S`,
hence `L ≤ 48 + lg(1/a) + lg(16/b) + 6S ≤ 10S`, and then `κ₀a = 2^20·S³` beats `2048·(10S)²·S`
because `2^20 ≥ 204800`. Everything is done with the base-`1.9` logarithm `lg` of `Lg.lean`,
whose toolkit (`natlog_le_lg`, `lg_le_double`, `lg_two_le`) is what makes the `Nat.log`s in the
schedule comparable to real logarithms; `Real.log x ≤ lg x` for `x ≥ 1` (`log_le_lg`) converts
the one natural logarithm in the conditions.

## What it says

The explicit closed form below is cubic in a bracket containing `lg w`; for fixed `a, b` its
elementary asymptotic shape is therefore `Θ((log w)³)`. `Schedule.lean` records a sharper
schedule-level heuristic, but that sharper unpadded closed form is not proved here. The padded
construction in `KappaZeroPad.lean` does attain the source's `O(log w·log log w)` shape; see
formalization note A3.
-/
import Sunflower.Schedule

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## Two `lg` facts -/

/-- `lg` dominates the natural logarithm, since the base `1.9` is below `e`. -/
lemma log_le_lg {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ lg x := by
  have hb0 : (0 : ℝ) < Real.log 1.9 := Real.log_pos (by norm_num)
  have hb1 : Real.log 1.9 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.9)
    linarith
  have hx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  rw [lg, Real.logb, le_div_iff₀ hb0]
  nlinarith [hx0, hb1]

lemma lg_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x := by
  rw [lg]
  exact Real.logb_nonneg one_lt_base hx

/-! ## The constant -/

/-- **The closed-form spread constant of Theorem 1.9.** -/
noncomputable def kappaZero (w : ℕ) (a b : ℝ) : ℝ :=
  (2 ^ 20 / a) * (lg (16 / b) + lg w + lg (1 / a) + 20) ^ 3

/-- **The three schedule conditions hold at `κ₀`**, together with `1 < κ₀`.

Writing `S` for the bracket: `lg κ₀ ≤ 40 + lg(1/a) + 6S`, so `L ≤ 48 + lg(1/a) + lg(16/b) + 6S
≤ 10S`, and `κ₀·a = 2^20·S³` beats each of `128·L`, `2048·L²·log(8/b) ≤ 204800·S³` and
`4096·L·(log₂w+1) ≤ 40960·S²`. -/
private lemma kappaZero_conds {w : ℕ} {a b : ℝ} (hw : 2 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b ≤ 1) :
    1 < kappaZero w a b
    ∧ 128 * ((schedL (kappaZero w a b) b : ℕ) : ℝ) ≤ kappaZero w a b * a
    ∧ 2048 * ((schedL (kappaZero w a b) b : ℕ) : ℝ) ^ 2 * Real.log (8 / b)
        ≤ kappaZero w a b * a
    ∧ 4096 * ((schedL (kappaZero w a b) b : ℕ) : ℝ) * ((Nat.log 2 w : ℝ) + 1)
        ≤ kappaZero w a b * a := by
  have hane : a ≠ 0 := ne_of_gt ha
  -- the three logarithms in the bracket
  have hb16 : (2 : ℝ) ≤ 16 / b := by rw [le_div_iff₀ hb0]; linarith
  have hB : 1 < lg (16 / b) := one_lt_lg hb16
  have hW : 1 < lg (w : ℝ) := one_lt_lg (by exact_mod_cast hw)
  have hA : 0 ≤ lg (1 / a) := lg_nonneg (by rw [le_div_iff₀ ha]; linarith)
  set S : ℝ := lg (16 / b) + lg (w : ℝ) + lg (1 / a) + 20 with hSdef
  -- every fact that needs the *definition* of `S`, before making it opaque
  have hS22 : 22 ≤ S := by rw [hSdef]; linarith
  have hSp : 0 < S := by linarith
  have hκS : kappaZero w a b * a = 2 ^ 20 * S ^ 3 := by
    rw [kappaZero, hSdef]; field_simp
  have hκpos : 0 < kappaZero w a b := by rw [kappaZero, ← hSdef]; positivity
  have hsplit : lg (kappaZero w a b) = lg ((2 : ℝ) ^ (20 : ℕ) / a) + lg (S ^ 3) := by
    have h1 : kappaZero w a b = ((2 : ℝ) ^ (20 : ℕ) / a) * S ^ 3 := by
      rw [kappaZero, ← hSdef]
    rw [h1]
    simp only [lg]
    exact Real.logb_mul (by positivity) (by positivity)
  have hAB : lg (1 / a) + lg (16 / b) ≤ S := by rw [hSdef]; linarith
  have hwlog : ((Nat.log 2 w : ℝ) + 1) ≤ S := by
    have h1 : ((Nat.log 2 w : ℕ) : ℝ) ≤ lg (w : ℝ) := natlog_le_lg (by omega)
    rw [hSdef]; linarith
  have hlog0 : 0 ≤ Real.log (8 / b) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hb0]; linarith
  have hlogb : Real.log (8 / b) ≤ S := by
    have h1 : Real.log (8 / b) ≤ Real.log (16 / b) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have h2 : Real.log (16 / b) ≤ lg (16 / b) := log_le_lg (by linarith)
    rw [hSdef]; linarith
  clear_value S
  -- powers of `S`
  have hcube : (22 : ℝ) ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ (by norm_num) hS22 3
  have hsq22 : (484 : ℝ) ≤ S ^ 2 := by nlinarith [hS22, hSp]
  have hκ1 : 1 < kappaZero w a b := by
    have h3 : kappaZero w a b * a ≤ kappaZero w a b := mul_le_of_le_one_right hκpos.le ha1
    have h4 : (2 : ℝ) ^ 20 * 22 ^ 3 ≤ 2 ^ 20 * S ^ 3 := by linarith [hcube]
    have h5 : (1 : ℝ) < 2 ^ 20 * 22 ^ 3 := by norm_num
    linarith [hκS, h3, h4, h5]
  -- `L ≤ 10·S`
  have hL : ((schedL (kappaZero w a b) b : ℕ) : ℝ) ≤ 10 * S := by
    have hlgκ : lg (kappaZero w a b) ≤ 40 + lg (1 / a) + 6 * S := by
      have hpow : lg (S ^ 3) = 3 * lg S := by
        simp only [lg]; rw [Real.logb_pow]; push_cast; ring
      have hdiv : lg ((2 : ℝ) ^ (20 : ℕ) / a) = lg ((2 : ℝ) ^ (20 : ℕ)) + lg (1 / a) := by
        have h1 : ((2 : ℝ) ^ (20 : ℕ) / a) = (2 : ℝ) ^ (20 : ℕ) * (1 / a) := by
          rw [div_eq_mul_inv, one_div]
        rw [h1]
        simp only [lg]
        exact Real.logb_mul (by positivity) (by positivity)
      have h20 : lg ((2 : ℝ) ^ (20 : ℕ)) ≤ 40 := by
        have h1 : lg ((2 : ℝ) ^ (20 : ℕ)) = 20 * lg 2 := by
          simp only [lg]; rw [Real.logb_pow]; push_cast; ring
        have h2 := lg_two_le
        rw [h1]; linarith
      have hlgS : lg S ≤ 2 * S := lg_le_double hSp
      rw [hsplit, hdiv, hpow]
      calc lg ((2 : ℝ) ^ (20 : ℕ)) + lg (1 / a) + 3 * lg S
          ≤ 40 + lg (1 / a) + 3 * (2 * S) := by
            refine add_le_add (add_le_add h20 le_rfl) ?_
            exact mul_le_mul_of_nonneg_left hlgS (by norm_num)
        _ = 40 + lg (1 / a) + 6 * S := by ring
    have hceilκ : 1 ≤ ⌈kappaZero w a b⌉₊ := Nat.one_le_ceil_iff.mpr hκpos
    have h1 : ((Nat.log 2 ⌈kappaZero w a b⌉₊ : ℕ) : ℝ) ≤ 2 + lg (kappaZero w a b) := by
      have hnl := natlog_le_lg hceilκ
      have hc2 : (⌈kappaZero w a b⌉₊ : ℝ) ≤ 2 * kappaZero w a b := by
        have := Nat.ceil_lt_add_one hκpos.le
        linarith
      have hmono : lg (⌈kappaZero w a b⌉₊ : ℝ) ≤ lg (2 * kappaZero w a b) :=
        lg_mono (by exact_mod_cast hceilκ) hc2
      have hmul : lg (2 * kappaZero w a b) = lg 2 + lg (kappaZero w a b) := by
        simp only [lg]
        exact Real.logb_mul (by norm_num) (ne_of_gt hκpos)
      have := lg_two_le
      linarith
    have hceilb : 1 ≤ ⌈16 / b⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    have h2 : ((Nat.log 2 ⌈16 / b⌉₊ : ℕ) : ℝ) ≤ 2 + lg (16 / b) := by
      have hnl := natlog_le_lg hceilb
      have hc2 : (⌈16 / b⌉₊ : ℝ) ≤ 2 * (16 / b) := by
        have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 16 / b)
        linarith
      have hmono : lg (⌈16 / b⌉₊ : ℝ) ≤ lg (2 * (16 / b)) :=
        lg_mono (by exact_mod_cast hceilb) hc2
      have hmul : lg (2 * (16 / b)) = lg 2 + lg (16 / b) := by
        simp only [lg]
        exact Real.logb_mul (by norm_num) (by positivity)
      have := lg_two_le
      linarith
    have hLeq : ((schedL (kappaZero w a b) b : ℕ) : ℝ)
        = ((Nat.log 2 ⌈kappaZero w a b⌉₊ : ℕ) : ℝ) + ((Nat.log 2 ⌈16 / b⌉₊ : ℕ) : ℝ) + 4 := by
      rw [schedL]; push_cast; ring
    rw [hLeq]
    linarith
  have hLnn : (0 : ℝ) ≤ ((schedL (kappaZero w a b) b : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨hκ1, ?_, ?_, ?_⟩
  · -- `128·L ≤ 1280·S ≤ 2^20·S³`
    have h1 : 1280 * S ≤ 2 ^ 20 * S ^ 3 := by nlinarith [hsq22, hSp]
    linarith [hL, h1, hκS]
  · -- `2048·L²·log(8/b) ≤ 204800·S³ ≤ 2^20·S³`
    have hsq : ((schedL (kappaZero w a b) b : ℕ) : ℝ) ^ 2 ≤ 100 * S ^ 2 := by
      nlinarith [hL, hLnn, hSp]
    calc 2048 * ((schedL (kappaZero w a b) b : ℕ) : ℝ) ^ 2 * Real.log (8 / b)
        ≤ 2048 * (100 * S ^ 2) * Real.log (8 / b) := by
          refine mul_le_mul_of_nonneg_right ?_ hlog0
          linarith [hsq]
      _ ≤ 2048 * (100 * S ^ 2) * S := by
          refine mul_le_mul_of_nonneg_left hlogb (by positivity)
      _ = 204800 * S ^ 3 := by ring
      _ ≤ 2 ^ 20 * S ^ 3 := by nlinarith [hSp, hcube]
      _ = kappaZero w a b * a := hκS.symm
  · -- `4096·L·(log₂w+1) ≤ 40960·S² ≤ 2^20·S³`
    have hnn : (0 : ℝ) ≤ ((Nat.log 2 w : ℝ) + 1) := by positivity
    calc 4096 * ((schedL (kappaZero w a b) b : ℕ) : ℝ) * ((Nat.log 2 w : ℝ) + 1)
        ≤ 4096 * (10 * S) * ((Nat.log 2 w : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          linarith [hL]
      _ ≤ 4096 * (10 * S) * S := by
          refine mul_le_mul_of_nonneg_left hwlog (by positivity)
      _ = 40960 * S ^ 2 := by ring
      _ ≤ 2 ^ 20 * S ^ 3 := by nlinarith [hS22, hSp, hsq22]
      _ = kappaZero w a b * a := hκS.symm

/-! ## Theorem 1.9, closed form -/

/-- **ALWZ Theorem 1.9.** For `0 < a, b ≤ 1` and `w ≥ 2`, every `w`-uniform family of size at
least `κ₀^w` contains an `(a,b)`-robust sunflower, where

`κ₀ = (2^20/a)·(lg(16/b) + lg w + lg(1/a) + 20)³`.

Nothing is assumed about `κ`: the three schedule conditions are verified for `κ₀` above. -/
theorem exists_isRobustSunflower {𝓕 : Finset (Finset α)} {X : Finset α} {w : ℕ} {a b : ℝ}
    (hw : 2 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hu : IsUniform w 𝓕) (hsub : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : kappaZero w a b ^ w ≤ (𝓕.card : ℝ)) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  obtain ⟨h0, h1, h2, h3⟩ := kappaZero_conds hw ha ha1 hb0 hb1
  exact exists_isRobustSunflower_of_kappa h0 hw hu hsub hcard ha ha1 hb0 hb1 h1 h2 h3

end Sunflower

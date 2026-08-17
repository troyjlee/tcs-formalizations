/-
# The closed-form `κ` on the padded bottom — ALWZ's shape

`SchedulePad.exists_isRobustSunflower_of_kappa_pad` is Theorem 1.9 for every `κ` clearing

  `128·L ≤ κa`,    `1024·L·log(8/b) ≤ κa`,    `4096·L·(log₂w + 1) ≤ κa`,

the middle condition now linear in `L`. That changes what a closed-form `κ` has to look like,
and for the better:

  `κ₀ := (2^20/a)·(lg(1/a) + lg(16/b) + lg lg w + 40)·(lg w + lg(16/b))`.

Write `U` for the first bracket and `V` for the second. `U` collects only *doubly* logarithmic
data, `V` the singly logarithmic; `L ≤ 5U`, and `κ₀·a = 2^20·U·V` clears `640·U`, `5120·U·V`
and `20480·U·V` at once.

**For fixed `a, b` this is `κ₀ = O(lg w · lg lg w)` — ALWZ's own shape.** The current explicit
unpadded constant `KappaZero.kappaZero` is cubic in a bracket containing `lg w`, hence has
shape `Θ((lg w)³)` for fixed `a,b`; a sharper schedule-level heuristic is not an exported
closed-form theorem. The padding construction (`DummyPad`, `PadBottom`) supplies the sharper
formalized endpoint; see formalization note A3.

The self-reference resolves differently than before: there, one bracket had to dominate
everything and the cube absorbed `lg κ₀`; here `lg κ₀ ≤ 40 + lg(1/a) + lg U + lg V`, and the
point is that `lg V ≤ 2 + lg lg w + 2·lg(16/b)` carries no `lg w` — so `L` stays doubly
logarithmic in `w` and only `V` is singly logarithmic.
-/
import Sunflower.SchedulePad
import Sunflower.KappaZero

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-- `lg (x + y) ≤ lg 2 + lg x + lg y` for `x, y ≥ 1`: the sum is at most twice the product. -/
lemma lg_add_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : lg (x + y) ≤ lg 2 + lg x + lg y := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hsum : x + y ≤ 2 * x * y := by nlinarith
  calc lg (x + y) ≤ lg (2 * x * y) := lg_mono (by positivity) hsum
    _ = lg 2 + lg x + lg y := by
        simp only [lg]
        rw [Real.logb_mul (by positivity) (ne_of_gt hy0), Real.logb_mul (by norm_num)
          (ne_of_gt hx0)]

/-- **The closed-form spread constant on the padded bottom.** -/
noncomputable def kappaZeroPad (w : ℕ) (a b : ℝ) : ℝ :=
  (2 ^ 20 / a) * (lg (1 / a) + lg (16 / b) + lg (lg w) + 40) * (lg w + lg (16 / b))

/-- The three conditions of `SchedulePad`, at `kappaZeroPad`. -/
private lemma kappaZeroPad_conds {w : ℕ} {a b : ℝ} (hw : 2 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b ≤ 1) :
    1 < kappaZeroPad w a b
    ∧ 128 * ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) ≤ kappaZeroPad w a b * a
    ∧ 1024 * ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) * Real.log (8 / b)
        ≤ kappaZeroPad w a b * a
    ∧ 4096 * ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) * ((Nat.log 2 w : ℝ) + 1)
        ≤ kappaZeroPad w a b * a := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hb16 : (2 : ℝ) ≤ 16 / b := by rw [le_div_iff₀ hb0]; linarith
  have hB : 1 < lg (16 / b) := one_lt_lg hb16
  have hW : 1 < lg (w : ℝ) := one_lt_lg hw2R
  have hA : 0 ≤ lg (1 / a) := lg_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hLL : 0 < lg (lg (w : ℝ)) := lg_lg_pos hw2R
  set U : ℝ := lg (1 / a) + lg (16 / b) + lg (lg (w : ℝ)) + 40 with hUdef
  set V : ℝ := lg (w : ℝ) + lg (16 / b) with hVdef
  -- facts needing the definitions
  have hU41 : 41 ≤ U := by rw [hUdef]; linarith
  have hUpos : 0 < U := by linarith
  have hV2 : 2 ≤ V := by rw [hVdef]; linarith
  have hVpos : 0 < V := by linarith
  have hBV : lg (16 / b) ≤ V := by rw [hVdef]; linarith
  have hκa : kappaZeroPad w a b * a = 2 ^ 20 * U * V := by
    rw [kappaZeroPad, ← hUdef, ← hVdef]
    field_simp
  have hκpos : 0 < kappaZeroPad w a b := by
    rw [kappaZeroPad, ← hUdef, ← hVdef]
    positivity
  have hwlog : ((Nat.log 2 w : ℝ) + 1) ≤ V := by
    have h1 : ((Nat.log 2 w : ℕ) : ℝ) ≤ lg (w : ℝ) := natlog_le_lg (by omega)
    rw [hVdef]; linarith
  have hlogb : Real.log (8 / b) ≤ lg (16 / b) := by
    have h1 : Real.log (8 / b) ≤ Real.log (16 / b) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact le_trans h1 (log_le_lg (by linarith))
  have hlog0 : 0 ≤ Real.log (8 / b) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hb0]; linarith
  -- `lg κ₀ ≤ 42 + lg(1/a) + 2U + lg lg w + 2·lg(16/b)`, hence `L ≤ 5U`
  have hlgV : lg V ≤ 2 + lg (lg (w : ℝ)) + 2 * lg (16 / b) := by
    have h1 : lg V ≤ lg 2 + lg (lg (w : ℝ)) + lg (lg (16 / b)) := by
      rw [hVdef]
      exact lg_add_le (le_of_lt hW) (le_of_lt hB)
    have h2 := lg_two_le
    have h3 : lg (lg (16 / b)) ≤ 2 * lg (16 / b) := lg_le_double (lt_trans one_pos hB)
    linarith
  have hlgU : lg U ≤ 2 * U := lg_le_double hUpos
  have h20 : lg ((2 : ℝ) ^ (20 : ℕ)) ≤ 40 := by
    have h1 : lg ((2 : ℝ) ^ (20 : ℕ)) = 20 * lg 2 := by
      simp only [lg]; rw [Real.logb_pow]; push_cast; ring
    have h2 := lg_two_le
    rw [h1]; linarith
  have hsplit : lg (kappaZeroPad w a b)
      = lg ((2 : ℝ) ^ (20 : ℕ)) + lg (1 / a) + lg U + lg V := by
    have h1 : lg (kappaZeroPad w a b) = lg ((2 ^ 20 / a) * U) + lg V := by
      rw [kappaZeroPad, ← hUdef, ← hVdef]
      simp only [lg]
      exact Real.logb_mul (by positivity) (ne_of_gt hVpos)
    have h2 : lg ((2 ^ 20 / a) * U) = lg ((2 : ℝ) ^ (20 : ℕ) / a) + lg U := by
      simp only [lg]
      exact Real.logb_mul (by positivity) (ne_of_gt hUpos)
    have h3 : lg ((2 : ℝ) ^ (20 : ℕ) / a) = lg ((2 : ℝ) ^ (20 : ℕ)) + lg (1 / a) := by
      have h4 : ((2 : ℝ) ^ (20 : ℕ) / a) = (2 : ℝ) ^ (20 : ℕ) * (1 / a) := by
        rw [div_eq_mul_inv, one_div]
      rw [h4]
      simp only [lg]
      exact Real.logb_mul (by positivity) (by positivity)
    rw [h1, h2, h3]
  have hκ1 : 1 < kappaZeroPad w a b := by
    have h1 : (2 : ℝ) ^ 20 * 41 * 2 ≤ 2 ^ 20 * U * V := by nlinarith [hU41, hV2, hUpos]
    have h2 : kappaZeroPad w a b * a ≤ kappaZeroPad w a b := mul_le_of_le_one_right hκpos.le ha1
    have h3 : (1 : ℝ) < 2 ^ 20 * 41 * 2 := by norm_num
    linarith [hκa]
  clear_value U V
  -- from here on `U`, `V` are opaque; `hUdef` is the only link to their contents
  have hlgκ : lg (kappaZeroPad w a b)
      ≤ 42 + lg (1 / a) + 2 * U + lg (lg (w : ℝ)) + 2 * lg (16 / b) :=
    calc lg (kappaZeroPad w a b)
        = lg ((2 : ℝ) ^ (20 : ℕ)) + lg (1 / a) + lg U + lg V := hsplit
      _ ≤ 40 + lg (1 / a) + 2 * U + (2 + lg (lg (w : ℝ)) + 2 * lg (16 / b)) :=
          add_le_add (add_le_add (add_le_add h20 le_rfl) hlgU) hlgV
      _ = 42 + lg (1 / a) + 2 * U + lg (lg (w : ℝ)) + 2 * lg (16 / b) := by ring
  have hL : ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) ≤ 5 * U := by
    have hceilκ : 1 ≤ ⌈kappaZeroPad w a b⌉₊ := Nat.one_le_ceil_iff.mpr hκpos
    have h1 : ((Nat.log 2 ⌈kappaZeroPad w a b⌉₊ : ℕ) : ℝ) ≤ 2 + lg (kappaZeroPad w a b) := by
      have hnl := natlog_le_lg hceilκ
      have hc2 : (⌈kappaZeroPad w a b⌉₊ : ℝ) ≤ 2 * kappaZeroPad w a b := by
        have := Nat.ceil_lt_add_one hκpos.le
        linarith
      have hmono : lg (⌈kappaZeroPad w a b⌉₊ : ℝ) ≤ lg (2 * kappaZeroPad w a b) :=
        lg_mono (by exact_mod_cast hceilκ) hc2
      have hmul : lg (2 * kappaZeroPad w a b) = lg 2 + lg (kappaZeroPad w a b) := by
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
    have hLeq : ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ)
        = ((Nat.log 2 ⌈kappaZeroPad w a b⌉₊ : ℕ) : ℝ) + ((Nat.log 2 ⌈16 / b⌉₊ : ℕ) : ℝ) + 4 := by
      rw [schedL]; push_cast; ring
    rw [hLeq]
    linarith [hUdef]
  have hLnn : (0 : ℝ) ≤ ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨hκ1, ?_, ?_, ?_⟩
  · -- `128·L ≤ 640·U ≤ 2^20·U·V`
    calc 128 * ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) ≤ 128 * (5 * U) := by linarith
      _ = 640 * U := by ring
      _ ≤ 2 ^ 20 * U * V := by nlinarith [hUpos, hV2]
      _ = kappaZeroPad w a b * a := hκa.symm
  · -- `1024·L·log(8/b) ≤ 5120·U·B ≤ 2^20·U·V`
    calc 1024 * ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) * Real.log (8 / b)
        ≤ 1024 * (5 * U) * Real.log (8 / b) := by
          refine mul_le_mul_of_nonneg_right ?_ hlog0
          linarith
      _ ≤ 1024 * (5 * U) * V := by
          refine mul_le_mul_of_nonneg_left (le_trans hlogb hBV) (by positivity)
      _ = 5120 * (U * V) := by ring
      _ ≤ 2 ^ 20 * U * V := by nlinarith [hUpos, hVpos]
      _ = kappaZeroPad w a b * a := hκa.symm
  · -- `4096·L·(log₂w+1) ≤ 20480·U·V ≤ 2^20·U·V`
    have hnn : (0 : ℝ) ≤ ((Nat.log 2 w : ℝ) + 1) := by positivity
    calc 4096 * ((schedL (kappaZeroPad w a b) b : ℕ) : ℝ) * ((Nat.log 2 w : ℝ) + 1)
        ≤ 4096 * (5 * U) * ((Nat.log 2 w : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          linarith
      _ ≤ 4096 * (5 * U) * V := by
          refine mul_le_mul_of_nonneg_left hwlog (by positivity)
      _ = 20480 * (U * V) := by ring
      _ ≤ 2 ^ 20 * U * V := by nlinarith [hUpos, hVpos]
      _ = kappaZeroPad w a b * a := hκa.symm

/-- **ALWZ Theorem 1.9, at ALWZ's own constant shape.** For `0 < a, b ≤ 1` and `w ≥ 2`, every
`w`-uniform family of size at least `κ₀^w` contains an `(a,b)`-robust sunflower, where

`κ₀ = (2^20/a)·(lg(1/a) + lg(16/b) + lg lg w + 40)·(lg w + lg(16/b))`.

For fixed `a, b` that is `O(lg w · lg lg w)` — the paper's shape. Compare
`KappaZero.exists_isRobustSunflower`, which goes through the heaviest size class and pays an
extra `lg lg w`. -/
theorem exists_isRobustSunflower_pad {𝓕 : Finset (Finset α)} {X : Finset α} {w : ℕ} {a b : ℝ}
    (hw : 2 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hu : IsUniform w 𝓕) (hsub : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : kappaZeroPad w a b ^ w ≤ (𝓕.card : ℝ)) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  obtain ⟨h0, h1, h2, h3⟩ := kappaZeroPad_conds hw ha ha1 hb0 hb1
  exact exists_isRobustSunflower_of_kappa_pad h0 hw hu hsub hcard ha ha1 hb0 hb1 h1 h2 h3

end Sunflower

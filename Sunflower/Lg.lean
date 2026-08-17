/-
# The base-1.9 logarithm of ALWZ

The `lg` convention (arXiv v3) and its basic estimates, split out of `ALWZ.lean`
so that the spread-lemma assembly can use them. See `Sunflower.ALWZ` for why the
base is `1.9`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Sunflower

/-- The logarithm used throughout ALWZ, base `1.9`. The unusual base is not an aesthetic
choice: it is exactly what makes `log log w > 0` at `w = 2`. See the module docstring. -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 1.9 x

lemma one_lt_base : (1 : ℝ) < 1.9 := by norm_num

/-- `lg 2 > 1`: the point of the base-1.9 convention. -/
lemma one_lt_lg_two : 1 < lg 2 := by
  have h : Real.logb 1.9 1.9 < Real.logb 1.9 2 :=
    Real.logb_lt_logb one_lt_base (by norm_num) (by norm_num)
  rwa [Real.logb_self_eq_one one_lt_base] at h

/-- Under the base-1.9 convention, `log log 2 > 0`, as required at `w = 2`. -/
theorem lg_lg_two_pos : 0 < lg (lg 2) :=
  Real.logb_pos one_lt_base one_lt_lg_two

/-- Under the base-2 reading, `log log 2 = 0`. See the formalization notes for the resulting
boundary issue in the pre-v3 statement. -/
theorem logb_two_logb_two_two : Real.logb 2 (Real.logb 2 2) = 0 := by
  rw [Real.logb_self_eq_one (by norm_num), Real.logb_one]

/-- `lg` is monotone (the base `1.9` exceeds `1`). -/
lemma lg_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lg x ≤ lg y :=
  Real.logb_le_logb_of_le one_lt_base hx hxy

/-- For `2 ≤ x`, `lg x > 1`. -/
lemma one_lt_lg {x : ℝ} (hx : 2 ≤ x) : 1 < lg x :=
  lt_of_lt_of_le one_lt_lg_two (lg_mono two_pos hx)

/-- For `2 ≤ x`, `lg (lg x) ≥ lg (lg 2)`. -/
lemma lg_lg_le_lg_lg {x : ℝ} (hx : 2 ≤ x) : lg (lg 2) ≤ lg (lg x) :=
  lg_mono (lt_trans one_pos one_lt_lg_two) (lg_mono two_pos hx)

/-- For `2 ≤ x`, `lg (lg x) > 0` — the positivity supplied by the base-1.9 convention. -/
lemma lg_lg_pos {x : ℝ} (hx : 2 ≤ x) : 0 < lg (lg x) :=
  lt_of_lt_of_le lg_lg_two_pos (lg_lg_le_lg_lg hx)


end Sunflower

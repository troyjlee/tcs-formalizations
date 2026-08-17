/-
# The schedule, in closed form — Theorem 1.9 on the Rao route

`RaoSatisfying.rao_isSatisfying` takes the slice schedule `(v, j)` as parameters, with eight
side conditions. This file chooses them:

  `v = ⌈2⁴⁵·n/R⌉,   j = ⌈3·log(4w/ε)⌉ + 1`,

and shows one condition on `R` discharges everything:

  `2⁵⁵ · δ⁻¹ · (log(w/ε) + 1) ≤ R`.

The two facts doing the work are Rao's ground-set bound `w·R ≤ n` (`RaoSpread.card_ground_ge`),
which makes `v ≥ w` and keeps the sampled fraction `jv/n` below `δ/32`, and the `2/3`-round
count `j > 3·log(4w/ε)`. Every inequality closes with large slack, which is what lets a single
power of two absorb all the ceilings.

The endpoint is the improved ALWZ Theorem 1.9: `exists_isRobustSunflower_rao`, with

  `κ₀ = raoKappa 2⁶⁰ a b w = (2⁶⁰/a) · lg(w/b)`,

which is `O(lg w)` for fixed `a, b` — against `O(lg w · lg lg w)` for the formalized ALWZ
`exists_isRobustSunflower_pad`. The dichotomy (`exists_rao_spread_link`), the trimming
reduction (`isSatisfying_of_trimmed`), and the final assembly all live in `RaoRobust`; here
they are fed the schedule.

Rao's technical range is `δ, ε ≤ 1/2`, but nothing in the formalized chase needs it: the
`ε/4 + ε/2 < ε` split is internal to `rao_isSatisfying`, and the chase below only uses
`ε ≤ 1 ≤ w`. So Theorem 1.9 is exported directly at ALWZ's full range `0 < a, b ≤ 1`, with no
`min(a, 1/2)` wrapper.
-/
import Sunflower.RaoRobust
import Sunflower.Lg

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α]

/-! ## The schedule chase -/

/-- **BCW's Theorem 3, schedule in closed form.** An absolutely `R`-spread `w`-uniform family
at the trimmed threshold `R^w ≤ |𝓗| ≤ R^w + 1` is `(δ, ε)`-satisfying as soon as

  `2⁵⁵ · δ⁻¹ · (log(w/ε) + 1) ≤ R`. -/
theorem rao_isSatisfying_of_kappa {X : Finset α} {𝓗 : Finset (Finset α)} {w : ℕ} {R δ ε : ℝ}
    (hu : IsUniform w 𝓗) (hsp : IsRaoSpread R w 𝓗) (hSX : ∀ T ∈ 𝓗, T ⊆ X)
    (hFge : R ^ w ≤ ((𝓗.card : ℕ) : ℝ)) (hFle : ((𝓗.card : ℕ) : ℝ) ≤ R ^ w + 1)
    (hne : 𝓗.Nonempty) (hw1 : 1 ≤ w)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 2 ^ 55 * δ⁻¹ * (Real.log ((w : ℝ) / ε) + 1) ≤ R) :
    IsSatisfying δ ε X 𝓗 := by
  classical
  have hw1R : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1
  -- `L = log(w/ε) ≥ 0`, since `w/ε ≥ 1`
  have hwε1 : (1 : ℝ) ≤ (w : ℝ) / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hw1R, hε1]
  set L : ℝ := Real.log ((w : ℝ) / ε) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hwε1
  -- clear the `δ⁻¹`: `2⁵⁵(L+1) ≤ δR`
  have hRδ : (2 : ℝ) ^ 55 * (L + 1) ≤ δ * R := by
    calc (2 : ℝ) ^ 55 * (L + 1) = δ * (2 ^ 55 * δ⁻¹ * (L + 1)) := by
          rw [show δ * (2 ^ 55 * δ⁻¹ * (L + 1)) = (δ * δ⁻¹) * (2 ^ 55 * (L + 1)) from by ring,
            mul_inv_cancel₀ (ne_of_gt hδ0), one_mul]
      _ ≤ δ * R := mul_le_mul_of_nonneg_left hR hδ0.le
  have hδR0 : (0 : ℝ) < δ * R := lt_of_lt_of_le (by nlinarith [hL0]) hRδ
  have hR0 : (0 : ℝ) < R := by nlinarith [hδR0, hδ0]
  have hδRle : δ * R ≤ R := by nlinarith [hδ1, hR0]
  have hR2 : (2 : ℝ) ^ 55 ≤ R := by nlinarith [hRδ, hL0, hδRle]
  have hR1 : (1 : ℝ) ≤ R := by nlinarith [hR2]
  -- Rao's ground-set bound, and its consequences
  have hn_ge : (w : ℝ) * R ≤ (X.card : ℝ) := card_ground_ge hR1 hw1 hu hSX hsp hFge
  have hn0R : (0 : ℝ) < (X.card : ℝ) := by nlinarith [hn_ge, hw1R, hR1]
  have hnR : R ≤ (X.card : ℝ) := by nlinarith [hn_ge, hw1R, hR0]
  -- the schedule
  set jr : ℝ := 3 * Real.log ((w : ℝ) / (ε / 4)) with hjrdef
  set j : ℕ := ⌈jr⌉₊ + 1 with hjdef
  set v : ℕ := ⌈(2 : ℝ) ^ 45 * (X.card : ℝ) / R⌉₊ with hvdef
  -- bounds on `jr` and `j`
  have hwε4 : (w : ℝ) / (ε / 4) = 4 * ((w : ℝ) / ε) := by
    rw [div_div_eq_mul_div]
    ring
  have hjr_pos : 0 < jr := by
    rw [hjrdef, hwε4]
    have h4 : (1 : ℝ) < 4 * ((w : ℝ) / ε) := by nlinarith [hwε1]
    nlinarith [Real.log_pos h4]
  have hjr_le : jr ≤ 3 * L + 9 / 2 := by
    rw [hjrdef, hwε4, Real.log_mul (by norm_num) (by positivity), ← hLdef]
    have hlog4 : Real.log 4 ≤ 3 / 2 := by
      have h4 : (4 : ℝ) = 2 * 2 := by norm_num
      rw [h4, Real.log_mul (by norm_num) (by norm_num)]
      nlinarith [Real.log_two_lt_d9]
    linarith
  have hj_gt : jr < (j : ℝ) := by
    rw [hjdef]
    push_cast
    linarith [Nat.le_ceil jr]
  have hj_ub : (j : ℝ) ≤ jr + 2 := by
    rw [hjdef]
    push_cast
    linarith [Nat.ceil_lt_add_one hjr_pos.le]
  have hj1R : (j : ℝ) + 1 ≤ 9 * (L + 1) := by linarith [hj_ub, hjr_le, hL0]
  -- bounds on `v`
  have hv_lb : (2 : ℝ) ^ 45 * (X.card : ℝ) / R ≤ (v : ℝ) := Nat.le_ceil _
  have hv_ub : (v : ℝ) ≤ (2 : ℝ) ^ 45 * (X.card : ℝ) / R + 1 := by
    rw [hvdef]
    exact (Nat.ceil_lt_add_one (div_nonneg (by positivity) hR0.le)).le
  have hv1 : 1 ≤ v :=
    Nat.ceil_pos.mpr (div_pos (mul_pos (by positivity) hn0R) hR0)
  have hv0R : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hwv_r : (w : ℝ) ≤ (v : ℝ) := by
    have h3 : (w : ℝ) ≤ (2 : ℝ) ^ 45 * (X.card : ℝ) / R := by
      rw [le_div_iff₀ hR0]
      nlinarith [hn_ge, hn0R.le]
    linarith [hv_lb]
  have hwv : w ≤ v := by exact_mod_cast hwv_r
  have hδn : δ * R ≤ δ * (X.card : ℝ) := by nlinarith [hnR, hδ0]
  -- the sampled fraction stays below `δ/32`
  have hstrong : ((j : ℝ) + 1) * (v : ℝ) ≤ δ * (X.card : ℝ) / 32 := by
    have hvR : (v : ℝ) * R ≤ (2 : ℝ) ^ 45 * (X.card : ℝ) + R := by
      have h2 : (v : ℝ) * R ≤ ((2 : ℝ) ^ 45 * (X.card : ℝ) / R + 1) * R :=
        mul_le_mul_of_nonneg_right hv_ub hR0.le
      calc (v : ℝ) * R ≤ ((2 : ℝ) ^ 45 * (X.card : ℝ) / R + 1) * R := h2
        _ = (2 : ℝ) ^ 45 * (X.card : ℝ) + R := by
            rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hR0)]
    have hA55 : ((j : ℝ) + 1) * 2 ^ 55 ≤ 9 * (δ * R) := by nlinarith [hj1R, hRδ]
    have hA55' : ((j : ℝ) + 1) * 2 ^ 55 ≤ 9 * (δ * (X.card : ℝ)) := by linarith
    have hA0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    have h5 : ((j : ℝ) + 1) * ((v : ℝ) * R)
        ≤ ((j : ℝ) + 1) * ((2 : ℝ) ^ 45 * (X.card : ℝ) + R) :=
      mul_le_mul_of_nonneg_left hvR hA0
    have hint1 : ((j : ℝ) + 1) * 2 ^ 55 * (X.card : ℝ) ≤ 9 * (δ * R) * (X.card : ℝ) :=
      mul_le_mul_of_nonneg_right hA55 hn0R.le
    have hint2 : ((j : ℝ) + 1) * 2 ^ 55 * R ≤ 9 * (δ * (X.card : ℝ)) * R :=
      mul_le_mul_of_nonneg_right hA55' hR0.le
    have h6 : ((j : ℝ) + 1) * (v : ℝ) * R ≤ (δ * (X.card : ℝ) / 32) * R := by
      nlinarith [h5, hint1, hint2]
    exact le_of_mul_le_mul_right h6 hR0
  have hkey : ((j : ℝ) + 1) * (v : ℝ) ≤ (X.card : ℝ) / 2 := by
    nlinarith [hstrong, hδ1, hn0R]
  -- the natural-number side conditions
  have hjv : j * v + v ≤ X.card := by
    have hc : ((j * v + v : ℕ) : ℝ) = ((j : ℝ) + 1) * (v : ℝ) := by push_cast; ring
    have h : ((j * v + v : ℕ) : ℝ) ≤ ((X.card : ℕ) : ℝ) := by
      rw [hc]
      linarith [hkey, hn0R]
    exact_mod_cast h
  have hjvn : j * v ≤ X.card := le_trans (Nat.le_add_right _ _) hjv
  have hsub_cast : ((X.card - j * v : ℕ) : ℝ) = (X.card : ℝ) - (j : ℝ) * (v : ℝ) := by
    rw [Nat.cast_sub hjvn]
    push_cast
    ring
  have hjv_half : (j : ℝ) * (v : ℝ) ≤ (X.card : ℝ) / 2 := by
    nlinarith [hkey, hv0R.le]
  have hw255 : (w : ℝ) * 2 ^ 55 ≤ (X.card : ℝ) := by
    nlinarith [hn_ge, mul_nonneg (sub_nonneg.mpr hR2) (by positivity : (0 : ℝ) ≤ (w : ℝ))]
  have hwn : w < X.card - j * v := by
    have hr : (w : ℝ) < ((X.card - j * v : ℕ) : ℝ) := by
      rw [hsub_cast]
      linarith [hw255, hw1R, hjv_half]
    exact_mod_cast hr
  have hw3 : 3 * w ≤ 2 * (X.card - j * v) := by
    have hr : ((3 * w : ℕ) : ℝ) ≤ ((2 * (X.card - j * v) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, hsub_cast]
      push_cast
      linarith [hw255, hw1R, hjv_half]
    exact_mod_cast hr
  -- the `κ` condition
  have hprod : (2 : ℝ) ^ (45 : ℕ) ≤ R * ((v : ℝ) / (X.card : ℝ)) := by
    have h1 : (2 : ℝ) ^ 45 * (X.card : ℝ) ≤ (v : ℝ) * R := by
      have := hv_lb
      rwa [div_le_iff₀ hR0] at this
    rw [← mul_div_assoc, le_div_iff₀ hn0R]
    linarith [h1]
  have hRv : 1 ≤ R * ((v : ℝ) / (X.card : ℝ)) := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (45 : ℕ) := by norm_num
    linarith [hprod]
  have hκ : 45 ≤ Real.logb 2 R + Real.logb 2 ((v : ℝ) / (X.card : ℝ)) := by
    have h45 : Real.logb 2 ((2 : ℝ) ^ (45 : ℕ)) = 45 := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity) hprod
    rw [h45] at hmono
    rwa [Real.logb_mul (ne_of_gt hR0) (by positivity)] at hmono
  -- the round count
  have hj : 3 * Real.log ((w : ℝ) / (ε / 4)) < (j : ℝ) := hj_gt
  -- the tail
  have htail : Real.exp (((j * v : ℕ) : ℝ) * Real.log 2 - δ * ((X.card : ℕ) : ℝ) / 2)
      ≤ ε / 2 := by
    have hjv_log : ((j * v : ℕ) : ℝ) * Real.log 2 ≤ δ * (X.card : ℝ) / 32 := by
      have hc : ((j * v : ℕ) : ℝ) = (j : ℝ) * (v : ℝ) := by push_cast; ring
      have h1 : ((j * v : ℕ) : ℝ) ≤ ((j : ℝ) + 1) * (v : ℝ) := by
        rw [hc]
        nlinarith [hv0R.le]
      have hlog2 : Real.log 2 ≤ 1 := by nlinarith [Real.log_two_lt_d9]
      have h2 : (0 : ℝ) ≤ ((j * v : ℕ) : ℝ) := by positivity
      nlinarith [hstrong, h1, hlog2, h2, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hlog2ε : Real.log (2 / ε) ≤ L + 1 := by
      have hew : (2 : ℝ) ≤ Real.exp 1 * (w : ℝ) := by
        have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (w : ℝ) :=
          mul_le_mul_of_nonneg_left hw1R (Real.exp_pos 1).le
        nlinarith [Real.exp_one_gt_d9]
      have h2e : (2 : ℝ) / ε ≤ Real.exp 1 * ((w : ℝ) / ε) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hε0 hε0]
        nlinarith [hew, hε0]
      have hlog := Real.log_le_log (by positivity) h2e
      rwa [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp,
        ← hLdef, add_comm 1 L] at hlog
    have hL1n : L + 1 ≤ δ * (X.card : ℝ) / 4 := by
      linarith [hRδ, hδn, hL0]
    have hA : ((j * v : ℕ) : ℝ) * Real.log 2 - δ * ((X.card : ℕ) : ℝ) / 2
        ≤ - Real.log (2 / ε) := by
      linarith [hjv_log, hlog2ε, hL1n, hL0]
    calc Real.exp (((j * v : ℕ) : ℝ) * Real.log 2 - δ * ((X.card : ℕ) : ℝ) / 2)
        ≤ Real.exp (- Real.log (2 / ε)) := Real.exp_le_exp.mpr hA
      _ = ε / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  exact rao_isSatisfying hu hsp hSX hFle hFge hR1 hne hw1 hv1 hwv hjv hw3 hwn hRv hκ
    hδ0 hδ1 hε0 hj htail

/-- **The untrimmed form.** The trimming reduction composed with the schedule: a family with
`R^w ≤ |𝓕|` and no upper bound is `(δ, ε)`-satisfying under the same condition on `R`. This
is the interface everything downstream consumes — BCW's Theorem 3, both disjointness lemmas,
and the robust-sunflower assembly. -/
theorem isSatisfying_of_raoSpread {X : Finset α} {𝓕 : Finset (Finset α)} {w : ℕ} {R δ ε : ℝ}
    (hw : 1 ≤ w) (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hcard : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 2 ^ 55 * δ⁻¹ * (Real.log ((w : ℝ) / ε) + 1) ≤ R) :
    IsSatisfying δ ε X 𝓕 := by
  have hw1R : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := by
    nlinarith [mul_inv_cancel₀ (ne_of_gt hδ0), inv_pos.mpr hδ0, hδ1]
  have hwε1 : (1 : ℝ) ≤ (w : ℝ) / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hw1R, hε1]
  have hL0 : 0 ≤ Real.log ((w : ℝ) / ε) := Real.log_nonneg hwε1
  have hR1 : (1 : ℝ) ≤ R := by
    nlinarith [hR, hδinv1, hL0,
      mul_nonneg (le_trans zero_le_one hδinv1) hL0]
  refine isSatisfying_of_trimmed hR1 hδ0.le hδ1 hcard ?_
  intro 𝓗 hsub hge hle
  have hne : 𝓗.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (1 : ℝ) ≤ R ^ w := one_le_pow₀ hR1
    have h2 : (0 : ℝ) < ((𝓗.card : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans h1 hge)
    exact_mod_cast h2
  exact rao_isSatisfying_of_kappa (fun _ hS => hu (hsub hS)) (hsp.subset hsub)
    (fun T hT => hSX T (hsub hT)) hge hle hne hw hδ0 hδ1 hε0 hε1 hR

end Rao

variable {α : Type*} [DecidableEq α]

/-! ## Theorem 1.9, improved -/

/-- The Rao-route threshold: `κ₀ = (C/a)·lg(w/b)`. For fixed `a, b` this is `O(lg w)`,
against the `O(lg w · lg lg w)` of `kappaZeroPad`. -/
noncomputable def raoKappa (C a b : ℝ) (w : ℕ) : ℝ := C / a * lg ((w : ℝ) / b)

open Rao in
/-- **ALWZ Theorem 1.9 with Rao's threshold.** For `w ≥ 2` and `0 < a, b ≤ 1`, every
`w`-uniform family of size at least `((2⁶⁰/a)·lg(w/b))^w` contains an `(a, b)`-robust
sunflower.

The pipeline: the absolute-spread dichotomy extracts a core `Z` whose link is large and
absolutely spread (`exists_rao_spread_link`); trimming reduces the link to the threshold
`R^{w'} ≤ |𝓗| ≤ R^{w'} + 1` (`isSatisfying_of_trimmed`); the coding argument makes the
trimmed link `(a, b)`-satisfying (`rao_isSatisfying_of_kappa`, using
`lg((w−|Z|)/b) ≤ lg(w/b)`); and the members above `Z` assemble into the robust sunflower
(`isRobustSunflower_of_link_satisfying`). -/
theorem exists_isRobustSunflower_rao {w : ℕ} {a b : ℝ} (hw : 2 ≤ w)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    {X : Finset α} {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕) (hSX : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : raoKappa (2 ^ 60) a b w ^ w ≤ ((𝓕.card : ℕ) : ℝ)) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  classical
  have hw1 : 1 ≤ w := by omega
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  -- `w/b ≥ 2`, so `lg(w/b) > 1`, so `κ₀ > 1`
  have hwb2 : (2 : ℝ) ≤ (w : ℝ) / b := by
    rw [le_div_iff₀ hb0]
    nlinarith [hw2R, hb1, hb0]
  have hlg1 : 1 < lg ((w : ℝ) / b) := one_lt_lg hwb2
  have hCa1 : (1 : ℝ) ≤ 2 ^ 60 / a := by
    rw [le_div_iff₀ ha0]
    nlinarith [ha1]
  have hR1 : 1 < raoKappa (2 ^ 60) a b w := by
    rw [raoKappa]
    nlinarith [hlg1, hCa1]
  refine exists_isRobustSunflower_of_link hR1 hw1 hu hSX hcard ?_
  intro Z hZX hZlt hlarge hsp
  refine isSatisfying_of_trimmed hR1.le ha0.le ha1 hlarge ?_
  intro 𝓗 hsub hge hle
  -- the link data, restricted to the trimmed subfamily
  have hulink : IsUniform (w - Z.card) (link 𝓕 Z) := hu.link Z
  have hu' : IsUniform (w - Z.card) 𝓗 := fun _ hS => hulink (hsub hS)
  have hsp' : IsRaoSpread (raoKappa (2 ^ 60) a b w) (w - Z.card) 𝓗 := hsp.subset hsub
  have hSX' : ∀ T ∈ 𝓗, T ⊆ X \ Z := by
    intro T hT
    obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp (hsub hT)
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hSX S hS hx.1, hx.2⟩
  have hne' : 𝓗.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (1 : ℝ) ≤ raoKappa (2 ^ 60) a b w ^ (w - Z.card) := one_le_pow₀ hR1.le
    have h2 : (0 : ℝ) < ((𝓗.card : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans h1 hge)
    exact_mod_cast h2
  have hw'1 : 1 ≤ w - Z.card := by omega
  refine rao_isSatisfying_of_kappa hu' hsp' hSX' hge hle hne' hw'1 ha0 ha1 hb0 hb1 ?_
  -- the constant chase: `2⁵⁵·a⁻¹·(log(w'/b) + 1) ≤ (2⁶⁰/a)·lg(w/b)`
  have hw'1R : (1 : ℝ) ≤ ((w - Z.card : ℕ) : ℝ) := by exact_mod_cast hw'1
  have hdivle : ((w - Z.card : ℕ) : ℝ) / b ≤ (w : ℝ) / b := by
    rw [div_le_div_iff₀ hb0 hb0]
    have hle' : ((w - Z.card : ℕ) : ℝ) ≤ (w : ℝ) := by
      exact_mod_cast (by omega : w - Z.card ≤ w)
    nlinarith [hle', hb0]
  have hlogw'b : Real.log (((w - Z.card : ℕ) : ℝ) / b) ≤ Real.log ((w : ℝ) / b) :=
    Real.log_le_log (div_pos (lt_of_lt_of_le zero_lt_one hw'1R) hb0) hdivle
  have hlog2wb : (0.693 : ℝ) ≤ Real.log ((w : ℝ) / b) := by
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hwb2
    nlinarith [Real.log_two_gt_d9]
  have hlog19_pos : (0 : ℝ) < Real.log 1.9 := Real.log_pos (by norm_num)
  have hlog19_lt1 : Real.log 1.9 < 1 := by
    have h1 : (1.9 : ℝ) < Real.exp 1 :=
      lt_of_lt_of_le (by norm_num) (le_of_lt Real.exp_one_gt_d9)
    have h2 := Real.log_lt_log (by norm_num : (0 : ℝ) < 1.9) h1
    rwa [Real.log_exp] at h2
  have hlgwb : Real.log ((w : ℝ) / b) ≤ lg ((w : ℝ) / b) := by
    have h0 : (0 : ℝ) ≤ Real.log ((w : ℝ) / b) := by nlinarith [hlog2wb]
    simp only [lg, Real.logb]
    rw [le_div_iff₀ hlog19_pos]
    nlinarith [h0, hlog19_lt1]
  have ha0' : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  rw [raoKappa, show (2 : ℝ) ^ 60 / a = 2 ^ 60 * a⁻¹ from div_eq_mul_inv _ _]
  nlinarith [mul_le_mul_of_nonneg_left hlogw'b ha0'.le,
    mul_le_mul_of_nonneg_left hlgwb ha0'.le,
    mul_le_mul_of_nonneg_left hlog2wb ha0'.le]

end Sunflower

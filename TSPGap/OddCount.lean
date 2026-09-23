/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.EvenCount
import TSPGap.Lemma517Counts

/-!
# The odd-parity shift

KKO's Corollaries 5.10 and 5.11 bound an *odd*-parity probability by writing
the count as `1 + BS(q − 1)` and applying Corollary 2.17 to the residual.  The
two ingredients are already in the development under other names, in
`Lemma517Counts`:

* `exists_eq_one_of_probCount_zero` — if `P[X = 0] = 0` then some coordinate
  is sure (`probCount q 0 = ∏(1 − qᵢ)`);
* `probCount_succ_update_zero`, `sum_update_zero`, `update_zero_mem_Icc` — the
  residual `q' = q` with that coordinate zeroed, `P[X = k+1] = P[X' = k]`,
  `∑ q' = ∑ q − 1`.

`oddCount_le` assembles them with `EvenCount`'s parity bridge: the odd mass of
`X` is the even mass of `X'`, reindexed by `k ↦ k + 1`, so the bound is
`(1 + e^{−2(E − 1)})/2` at mean `E ≤ 2.2`.

⚠️ **The normalization matters.**  `oddCount_le` demands `totalMass w = 1`.
For a *subweight* the hypothesis `W[count = 0] = 0` is satisfied vacuously by
the zero weight, where no coordinate is sure and no such bound holds — so the
unnormalized wrapper `weightMass_le_of_transfer` never extracts a coordinate
itself: it multiplies a bound already proved for the normalized law by the
subweight's mass, which is correct (and trivial) at mass zero.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Reindexing the odd layers -/

/-- The odd layers below `M + 2` are the even layers below `M + 1`, shifted. -/
theorem filter_odd_eq_image (M : ℕ) :
    (Finset.range (M + 2)).filter (fun k => Odd k)
      = ((Finset.range (M + 1)).filter (fun k => Even k)).image (· + 1) := by
  ext jj
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Nat.odd_iff, Nat.even_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨jj - 1, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    exact ⟨by omega, by omega⟩

/-! ### The odd-parity bound -/

set_option maxHeartbeats 1000000 in
/-- **The odd-parity bound after removing a sure coordinate.**  Under a stable
fixed-rank normalized law whose count over `D` never vanishes, the odd mass is
at most `(1 + e^{−2(E[|T∩D|] − 1)})/2`, provided `E[|T∩D|] ≤ 2.2`. -/
theorem oddCount_le {w : Finset ι → ℝ} {r : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (D : Finset ι) (hzero : weightMass w (fun T => (T ∩ D).card = 0) = 0)
    (hmean : expCard w D ≤ 2.2) :
    weightMass w (fun T => Odd (T ∩ D).card)
      ≤ (1 + Real.exp (-2 * (expCard w D - 1))) / 2 := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot D
  have hmean' : expCard w D = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  -- a sure coordinate
  have hq0 : Bernoulli.probCount q 0 = 0 := by rw [← hlaw 0]; exact hzero
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero hq0
  set q' : Fin m → ℝ := Function.update q j 0 with hq'
  have hq'sum : ∑ i, q' i = expCard w D - 1 := by
    rw [hq', sum_update_zero, hj, ← hmean']
  have hq'nn : ∀ i, 0 ≤ q' i := fun i =>
    (update_zero_mem_Icc (fun i => Set.mem_Icc.mpr ⟨(hq i).1.le, (hq i).2⟩) j i).1
  -- the odd mass as a filtered layer sum
  have hterm : ∀ jj : ℕ, weightMass w (fun S => (S ∩ D).card = jj ∧ Odd (S ∩ D).card)
      = if Odd jj then Bernoulli.probCount q jj else 0 := by
    intro jj
    by_cases he : Odd jj
    · rw [if_pos he, ← hlaw jj]
      exact weightMass_congr fun S => ⟨fun h => h.1, fun h => ⟨h, h ▸ he⟩⟩
    · rw [if_neg he,
        show (fun S : Finset ι => (S ∩ D).card = jj ∧ Odd (S ∩ D).card) = fun _ => False from ?_,
        weightMass_false]
      funext S
      exact propext ⟨fun h => he (h.1 ▸ h.2), fun h => h.elim⟩
  have hsmall : weightMass w (fun T => Odd (T ∩ D).card)
      = ∑ k ∈ (Finset.range (D.card + 1)).filter (fun k => Odd k),
          Bernoulli.probCount q k := by
    rw [weightMass_layer_partition w D (fun T => Odd (T ∩ D).card),
      Finset.sum_congr rfl (fun jj _ => hterm jj), ← Finset.sum_filter]
  -- extend the range to `max D.card m + 2`
  have hext : ∑ k ∈ (Finset.range (D.card + 1)).filter (fun k => Odd k),
        Bernoulli.probCount q k
      = ∑ k ∈ (Finset.range (max D.card m + 2)).filter (fun k => Odd k),
          Bernoulli.probCount q k := by
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      have := Finset.mem_range.mp hk1
      have := le_max_left D.card m
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk2⟩
    · obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      have hgt : D.card < k := by
        by_contra hc
        exact hk' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk2⟩)
      rw [← hlaw k]
      exact weightMass_card_eq_zero w hgt
  -- reindex to the even layers of the residual
  have hshift : ∑ k ∈ (Finset.range (max D.card m + 2)).filter (fun k => Odd k),
        Bernoulli.probCount q k
      = ∑ k ∈ (Finset.range (max D.card m + 1)).filter (fun k => Even k),
          Bernoulli.probCount q' k := by
    rw [filter_odd_eq_image, Finset.sum_image (fun a _ b _ h => by omega)]
    exact Finset.sum_congr rfl fun k _ => probCount_succ_update_zero hj k
  rw [hsmall, hext, hshift,
    sum_even_probCount q' (by rw [Fintype.card_fin]; exact le_max_right D.card m), ← hq'sum]
  exact Bernoulli.evenMass_le_of_sum_le q' hq'nn (by rw [hq'sum]; linarith)

/-! ### The Weierstrass product bound

`∏(1 − qᵢ) ≥ 1 − ∑ qᵢ`, and hence a *lower* bound on `P[X = 0]` — the
ingredient the `β > 1/2` branch of Corollary 5.10 needs, where the coefficient
`1 − 2β` is negative and an upper bound on the odd mass is useless. -/

theorem one_sub_sum_le_prod_finset (s : Finset ι) (q : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ q i) (h1 : ∀ i ∈ s, q i ≤ 1) :
    1 - ∑ i ∈ s, q i ≤ ∏ i ∈ s, (1 - q i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hq0 : 0 ≤ q a := h0 a (Finset.mem_insert_self a s)
    have hq1 : q a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have ihs := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hSnn : 0 ≤ ∑ i ∈ s, q i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - q a)
      (by linarith : (0:ℝ) ≤ (∏ i ∈ s, (1 - q i)) - (1 - ∑ i ∈ s, q i)),
      mul_nonneg hq0 hSnn]

/-- **Weierstrass**: `∏(1 − qᵢ) ≥ 1 − ∑ qᵢ`. -/
theorem one_sub_sum_le_prod (q : ι → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1) :
    1 - ∑ i, q i ≤ ∏ i, (1 - q i) :=
  one_sub_sum_le_prod_finset Finset.univ q (fun i _ => h0 i) (fun i _ => h1 i)

/-- The `probCount 0` corollary: `P[X = 0] ≥ 1 − ∑ qᵢ`. -/
theorem probCount_zero_ge (q : ι → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1) :
    1 - ∑ i, q i ≤ Bernoulli.probCount q 0 := by
  rw [probCount_zero_eq_prod]
  exact one_sub_sum_le_prod q h0 h1

set_option maxHeartbeats 1000000 in
/-- **The odd mass from below.**  A count that never vanishes puts at least
`2 − E` on the value one, hence at least that on the odd values. -/
theorem oddCount_ge {w : Finset ι → ℝ} {r : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (D : Finset ι) (hzero : weightMass w (fun T => (T ∩ D).card = 0) = 0) :
    2 - expCard w D ≤ weightMass w (fun T => Odd (T ∩ D).card) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot D
  have hmean' : expCard w D = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hq0 : Bernoulli.probCount q 0 = 0 := by rw [← hlaw 0]; exact hzero
  obtain ⟨j, hj⟩ := exists_eq_one_of_probCount_zero hq0
  set q' : Fin m → ℝ := Function.update q j 0 with hq'
  have hq'sum : ∑ i, q' i = expCard w D - 1 := by
    rw [hq', sum_update_zero, hj, ← hmean']
  have hIcc := update_zero_mem_Icc (q := q)
    (fun i => Set.mem_Icc.mpr ⟨(hq i).1.le, (hq i).2⟩) j
  have hone : 2 - expCard w D ≤ weightMass w (fun T => (T ∩ D).card = 1) := by
    have hs : Bernoulli.probCount q 1 = Bernoulli.probCount q' 0 := by
      have h := probCount_succ_update_zero hj 0
      simpa using h
    rw [hlaw 1, hs]
    have := probCount_zero_ge q' (fun i => (hIcc i).1) (fun i => (hIcc i).2)
    rw [hq'sum] at this
    linarith
  refine le_trans hone (weightMass_mono hnn fun S hS => ?_)
  rw [hS]
  exact odd_one

/-! ### The two-branch bound

Corollary 5.10's exact identity is `P[odd] = a(1 − 2β) + β`, with `a` the odd
probability of the inside count and `β` the probability that the single
crossing edge is present.  The deviation `d` of the total mean from `2` is
carried **symbolically** — KKO's rounded `0.001` is *too coarse*: it gives
`(1 + e^{−1.998})/2 = 0.5678031`, above the `0.5678` they claim.  The deviation
actually proved (`Corollary510.mean_bounds_of_part`) is `ε_M + 4.5ε_η`, which
is `≈ 0.00025` and clears the `0.0005` this file's numerics assume. -/

/-- `7.383 ≤ e²`, from `Real.exp_one_gt_d9`. -/
theorem exp_two_ge : (7.383 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 1]

/-- `e^{2d−2} ≤ 0.1356` for `d ≤ 0.0005`. -/
theorem exp_two_mul_sub_two_le {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 0.0005) :
    Real.exp (2 * d - 2) ≤ 0.1356 := by
  have h1 : Real.exp (2 * d - 2) ≤ Real.exp (-1.999) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp (1.999 : ℝ) = Real.exp 2 * Real.exp (-0.001) := by
    rw [← Real.exp_add]; norm_num
  have hlow : (0.999 : ℝ) ≤ Real.exp (-0.001) := by
    have := Real.add_one_le_exp (-0.001 : ℝ); linarith
  have hpos : (0 : ℝ) < Real.exp 1.999 := Real.exp_pos _
  have hge : (7.3756 : ℝ) ≤ Real.exp 1.999 := by
    rw [hsplit]; nlinarith [exp_two_ge, Real.exp_pos (-0.001 : ℝ)]
  have hneg : Real.exp (-1.999 : ℝ) = 1 / Real.exp 1.999 := by
    rw [Real.exp_neg]; ring
  rw [hneg] at h1
  have : (1 : ℝ) / Real.exp 1.999 ≤ 1 / 7.3756 := by
    apply one_div_le_one_div_of_le (by norm_num) hge
  linarith [h1, this]

/-- **The two-branch bound.**  `β ≤ 1/2` uses the odd upper bound together with
`1 − 2β ≤ e^{−2β}`; `β > 1/2` — where `1 − 2β` is negative — uses the
Weierstrass lower bound and `2β(1 − β) ≤ 1/2`. -/
theorem odd_split_le {a β E d : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hd0 : 0 ≤ d)
    (hE1 : 2 - d ≤ E) (hE2 : E ≤ 2 + d)
    (hup : β ≤ 1 / 2 → a ≤ (1 + Real.exp (-2 * (E - β - 1))) / 2)
    (hlow : 1 / 2 < β → 2 - (E - β) ≤ a) :
    a * (1 - 2 * β) + β ≤ max ((1 + Real.exp (2 * d - 2)) / 2) (1 / 2 + d) := by
  rcases le_or_gt β (1 / 2) with hb | hb
  · refine le_trans ?_ (le_max_left _ _)
    have hA := hup hb
    have h2β : 0 ≤ 1 - 2 * β := by linarith
    have hstep : a * (1 - 2 * β) ≤ (1 + Real.exp (-2 * (E - β - 1))) / 2 * (1 - 2 * β) :=
      mul_le_mul_of_nonneg_right hA h2β
    -- push the exponent up using `E ≥ 2 − d`
    have hexp : Real.exp (-2 * (E - β - 1)) ≤ Real.exp (2 * β + 2 * d - 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpos : (0 : ℝ) < Real.exp (2 * β + 2 * d - 2) := Real.exp_pos _
    -- `1 − 2β ≤ e^{−2β}` closes the product
    have hkey : Real.exp (2 * β + 2 * d - 2) * (1 - 2 * β) ≤ Real.exp (2 * d - 2) := by
      have h1 := Bernoulli.one_sub_two_mul_le_exp β
      have hmul : Real.exp (2 * β + 2 * d - 2) * (1 - 2 * β)
          ≤ Real.exp (2 * β + 2 * d - 2) * Real.exp (-2 * β) :=
        mul_le_mul_of_nonneg_left h1 hpos.le
      rw [← Real.exp_add] at hmul
      have : 2 * β + 2 * d - 2 + -2 * β = 2 * d - 2 := by ring
      rwa [this] at hmul
    nlinarith [mul_le_mul_of_nonneg_right hexp h2β, hkey, hstep]
  · refine le_trans ?_ (le_max_right _ _)
    have hL := hlow hb
    have h2β : 1 - 2 * β < 0 := by linarith
    have hstep : a * (1 - 2 * β) ≤ (2 - (E - β)) * (1 - 2 * β) :=
      mul_le_mul_of_nonpos_right hL h2β.le
    have hLge : β - d ≤ 2 - (E - β) := by linarith
    have hstep2 : (2 - (E - β)) * (1 - 2 * β) ≤ (β - d) * (1 - 2 * β) :=
      mul_le_mul_of_nonpos_right hLge h2β.le
    have hexpand : (β - d) * (1 - 2 * β) = β - 2 * β ^ 2 - d + 2 * (d * β) := by ring
    nlinarith [sq_nonneg (β - 1 / 2), mul_nonneg hd0 (sub_nonneg.mpr hβ1)]

/-- The numeric instantiation, at any deviation `d ≤ 0.0005`; Corollary 5.10
supplies `ε_M + 4.5ε_η` (`Corollary510.mean_bounds_of_part`). -/
theorem odd_split_le_num {a β E d : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hd0 : 0 ≤ d)
    (hd : d ≤ 0.0005) (hE1 : 2 - d ≤ E) (hE2 : E ≤ 2 + d)
    (hup : β ≤ 1 / 2 → a ≤ (1 + Real.exp (-2 * (E - β - 1))) / 2)
    (hlow : 1 / 2 < β → 2 - (E - β) ≤ a) :
    a * (1 - 2 * β) + β ≤ 0.5678 := by
  refine le_trans (odd_split_le hβ0 hβ1 hd0 hE1 hE2 hup hlow) (max_le ?_ ?_)
  · have := exp_two_mul_sub_two_le hd0 hd
    linarith
  · linarith

/-! ### The even-parity kernel, for Corollary 5.11

Corollary 5.11 bounds the *even* mass of the inner `A`-count, whose mean is
near `1` rather than `2`, so there is no sure coordinate to strip: the upper
branch is `evenCount_le` directly, and the lower branch is
`Conditioning.le_weightMass_avoid` (`P[X = 0] ≥ 1 − E[X]`), which is the same
Weierstrass content already available at the mass level.  The algebra is
identical to `odd_split_le`. -/

/-- **The two-branch bound at mean one.**  `β ≤ 1/2` uses the even upper bound
with `1 − 2β ≤ e^{−2β}`; `β > 1/2` uses `α ≥ 1 − μ`. -/
theorem even_split_le {α β μ d : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hd0 : 0 ≤ d)
    (hμ1 : 1 - d - β ≤ μ) (hμ2 : μ ≤ 1 + d - β)
    (hup : β ≤ 1 / 2 → α ≤ (1 + Real.exp (-2 * μ)) / 2)
    (hlow : 1 / 2 < β → 1 - μ ≤ α) :
    α * (1 - 2 * β) + β ≤ max ((1 + Real.exp (2 * d - 2)) / 2) (1 / 2 + d) := by
  rcases le_or_gt β (1 / 2) with hb | hb
  · refine le_trans ?_ (le_max_left _ _)
    have hA := hup hb
    have h2β : 0 ≤ 1 - 2 * β := by linarith
    have hstep : α * (1 - 2 * β) ≤ (1 + Real.exp (-2 * μ)) / 2 * (1 - 2 * β) :=
      mul_le_mul_of_nonneg_right hA h2β
    have hexp : Real.exp (-2 * μ) ≤ Real.exp (2 * β + 2 * d - 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpos : (0 : ℝ) < Real.exp (2 * β + 2 * d - 2) := Real.exp_pos _
    have hkey : Real.exp (2 * β + 2 * d - 2) * (1 - 2 * β) ≤ Real.exp (2 * d - 2) := by
      have h1 := Bernoulli.one_sub_two_mul_le_exp β
      have hmul : Real.exp (2 * β + 2 * d - 2) * (1 - 2 * β)
          ≤ Real.exp (2 * β + 2 * d - 2) * Real.exp (-2 * β) :=
        mul_le_mul_of_nonneg_left h1 hpos.le
      rw [← Real.exp_add] at hmul
      have heq : 2 * β + 2 * d - 2 + -2 * β = 2 * d - 2 := by ring
      rwa [heq] at hmul
    nlinarith [mul_le_mul_of_nonneg_right hexp h2β, hkey, hstep]
  · refine le_trans ?_ (le_max_right _ _)
    have hL := hlow hb
    have h2β : 1 - 2 * β < 0 := by linarith
    have hstep : α * (1 - 2 * β) ≤ (1 - μ) * (1 - 2 * β) :=
      mul_le_mul_of_nonpos_right hL h2β.le
    have hLge : β - d ≤ 1 - μ := by linarith
    have hstep2 : (1 - μ) * (1 - 2 * β) ≤ (β - d) * (1 - 2 * β) :=
      mul_le_mul_of_nonpos_right hLge h2β.le
    have hexpand : (β - d) * (1 - 2 * β) = β - 2 * β ^ 2 - d + 2 * (d * β) := by ring
    nlinarith [sq_nonneg (β - 1 / 2), mul_nonneg hd0 (sub_nonneg.mpr hβ1)]

/-- `7.389 ≤ e²`, the sharper anchor Corollary 5.11 needs. -/
theorem exp_two_ge_sharp : (7.389 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 1]

/-- `e^{2d−2} ≤ 0.13542` for `d ≤ 0.00026`.  ⚠️ `exp_two_mul_sub_two_le` is
deliberately too coarse for this margin: it is stated at `d ≤ 0.0005`, i.e.
exponent `−1.999`, whereas here the exponent is `−1.99948`. -/
theorem exp_two_mul_sub_two_le_sharp {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 0.00026) :
    Real.exp (2 * d - 2) ≤ 0.13542 := by
  have h1 : Real.exp (2 * d - 2) ≤ Real.exp (-1.99948) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp (1.99948 : ℝ) = Real.exp 2 * Real.exp (-0.00052) := by
    rw [← Real.exp_add]; norm_num
  have hlow : (0.99948 : ℝ) ≤ Real.exp (-0.00052) := by
    have := Real.add_one_le_exp (-0.00052 : ℝ); linarith
  have hge : (7.385 : ℝ) ≤ Real.exp 1.99948 := by
    rw [hsplit]
    nlinarith [exp_two_ge_sharp, Real.exp_pos (-0.00052 : ℝ)]
  have hneg : Real.exp (-1.99948 : ℝ) = 1 / Real.exp 1.99948 := by
    rw [Real.exp_neg]; ring
  rw [hneg] at h1
  have h2 : (1 : ℝ) / Real.exp 1.99948 ≤ 1 / 7.385 :=
    one_div_le_one_div_of_le (by norm_num) hge
  have h3 : (1 : ℝ) / 7.385 ≤ 0.13542 := by norm_num
  linarith

/-- The numeric instantiation for Corollary 5.11, at `d ≤ 0.00026`. -/
theorem even_split_le_num {α β μ d : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hd0 : 0 ≤ d)
    (hd : d ≤ 0.00026) (hμ1 : 1 - d - β ≤ μ) (hμ2 : μ ≤ 1 + d - β)
    (hup : β ≤ 1 / 2 → α ≤ (1 + Real.exp (-2 * μ)) / 2)
    (hlow : 1 / 2 < β → 1 - μ ≤ α) :
    α * (1 - 2 * β) + β ≤ 0.56771 := by
  refine le_trans (even_split_le hβ0 hβ1 hd0 hμ1 hμ2 hup hlow) (max_le ?_ ?_)
  · have := exp_two_mul_sub_two_le_sharp hd0 hd
    linarith
  · linarith

/-! ### The zero-safe unnormalized wrapper -/

/-- **Cross-multiplied transfer.**  A bound for the normalized law becomes a
bound for a subweight, multiplied by its mass.  Zero-safe: at mass zero both
sides vanish, and — unlike a route that first extracts a sure coordinate —
nothing is claimed about the zero weight, for which `W[count = 0] = 0` holds
vacuously. -/
theorem weightMass_le_of_transfer {v ν : Finset ι → ℝ} {P : Finset ι → Prop} {c : ℝ}
    (htr : weightMass v P = weightMass ν P * totalMass v)
    (hbound : weightMass ν P ≤ c) (hM : 0 ≤ totalMass v) :
    weightMass v P ≤ c * totalMass v := by
  rw [htr]
  exact mul_le_mul_of_nonneg_right hbound hM

end TSPGap

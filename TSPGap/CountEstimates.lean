/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Conditioning

/-!
# Bernoulli estimates for Lemma 5.7

The probabilistic estimates Lemma 5.7 spends, specialized to the counts it
actually uses, plus the two numerical constants.

* **Mean identity.**  `expCard_eq_sum_layer` reads the expected count off
  the layer masses, `sum_atomProb_mem` gives the Bernoulli marginals, and
  `expCard_eq_sum_of_rankLaw` combines them: under a Bernoulli rank law the
  expected count is `∑ qᵢ`.
* **`P[X = 0] ≤ exp(−E X)`.**  Direct from the product formula:
  `∏(1 − qᵢ) ≤ ∏ exp(−qᵢ) = exp(−∑ qᵢ)`.  No tail machinery — Lemma 5.7's
  only tail use is at `k = 1`, where this suffices, so the shifted-Poisson
  comparison is not needed at all.
* **`P[X = 2] ≥ 0.25`** for a mean in `[3/2, 2 + 1/1000]`, wrapping the
  axiom-clean `poi_le_probCount`.  All three branches `l = 0, 1, 2` of that
  theorem's existential must clear the constant, and `l = 0` at mean `3/2`
  is genuinely tight — `poi(3/2, 2) = 0.2510…` — so interval splitting
  cannot prove it.  What does is the anchor `p² e^{−p} ≥ (3/2)² e^{−3/2}`
  on `[3/2, 2]`, itself from `exp u ≤ (1 − u/2)⁻²` and
  `(1 + 2u/3)(1 − u/2) ≥ 1`.
* The constants: `one_sub_exp_ge` (`1 − e^{−x} ≥ 0.98x` for `x ≤ 1 / 50`) and
  the `0.25` above.  Every exponential bound here comes from
  `Real.add_one_le_exp` and `Real.exp_one_lt_d9`/`_gt_d9` alone — no
  series-remainder estimates.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The mean identity -/

/-- The expected count is the layer-weighted sum of the layer masses. -/
theorem expCard_eq_sum_layer (w : Finset ι → ℝ) (F : Finset ι) {N : ℕ}
    (hN : F.card ≤ N) :
    expCard w F
      = ∑ k ∈ Finset.range (N + 1),
          (k : ℝ) * weightMass w (fun S => (S ∩ F).card = k) := by
  classical
  have hlayer : ∀ k : ℕ, weightMass w (fun S => (S ∩ F).card = k)
      = ∑ S : Finset ι, (if (S ∩ F).card = k then w S else 0) := by
    intro k
    rw [weightMass]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases h : (S ∩ F).card = k <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => by rw [hlayer k, Finset.mul_sum],
    Finset.sum_comm, expCard]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hmem : (S ∩ F).card ∈ Finset.range (N + 1) := by
    have hle : (S ∩ F).card ≤ F.card :=
      Finset.card_le_card Finset.inter_subset_right
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem ((S ∩ F).card) hmem
    (fun k _ hk => by rw [if_neg (fun hc => hk hc.symm), mul_zero]),
    if_pos rfl, mul_comm]

omit [Fintype ι] in
/-- Every subset splitting of `E` carries total Bernoulli mass one. -/
theorem sum_atom_on (E : Finset ι) (q : ι → ℝ) :
    ∑ t ∈ E.powerset, (∏ j ∈ t, q j) * ∏ j ∈ E \ t, (1 - q j) = 1 := by
  classical
  have h := Finset.prod_add (fun j => q j) (fun j => 1 - q j) E
  rw [Finset.prod_congr rfl (fun j _ => by ring :
      ∀ j ∈ E, q j + (1 - q j) = 1), Finset.prod_const_one] at h
  exact h.symm

/-- **The Bernoulli marginals**: coordinate `i` succeeds with probability
`q i`. -/
theorem sum_atomProb_mem (q : ι → ℝ) (i : ι) :
    ∑ t : Finset ι, (if i ∈ t then (1:ℝ) else 0) * Bernoulli.atomProb q t
      = q i := by
  classical
  have hsplit : (Finset.univ : Finset ι)
      = insert i ((Finset.univ : Finset ι).erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  rw [← Finset.powerset_univ, hsplit,
    Finset.sum_powerset_insert (Finset.notMem_erase i _)]
  have hzero : ∑ t ∈ ((Finset.univ : Finset ι).erase i).powerset,
      (if i ∈ t then (1:ℝ) else 0) * Bernoulli.atomProb q t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have hti : i ∉ t := fun hc =>
      Finset.notMem_erase i _ (Finset.mem_powerset.mp ht hc)
    rw [if_neg hti, zero_mul]
  have hshift : ∀ t ∈ ((Finset.univ : Finset ι).erase i).powerset,
      (if i ∈ insert i t then (1:ℝ) else 0)
          * Bernoulli.atomProb q (insert i t)
        = q i * ((∏ j ∈ t, q j)
          * ∏ j ∈ (Finset.univ : Finset ι).erase i \ t, (1 - q j)) := by
    intro t ht
    have hti : i ∉ t := fun hc =>
      Finset.notMem_erase i _ (Finset.mem_powerset.mp ht hc)
    have hsdiff : (Finset.univ : Finset ι) \ insert i t
        = (Finset.univ : Finset ι).erase i \ t := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_univ,
        Finset.mem_erase, true_and]
      tauto
    rw [if_pos (Finset.mem_insert_self i t), one_mul, Bernoulli.atomProb,
      Finset.prod_insert hti, hsdiff, mul_assoc]
  rw [hzero, zero_add, Finset.sum_congr rfl hshift, ← Finset.mul_sum,
    sum_atom_on, mul_one]

theorem probCount_eq_zero_of_card_lt (q : ι → ℝ) {k : ℕ}
    (hk : Fintype.card ι < k) : Bernoulli.probCount q k = 0 := by
  classical
  rw [Bernoulli.probCount_def,
    Finset.powersetCard_eq_empty.mpr (by simpa using hk), Finset.sum_empty]

/-- **The Bernoulli mean**: `∑ k · P[X = k] = ∑ qᵢ`. -/
theorem sum_range_mul_probCount (q : ι → ℝ) {N : ℕ} (hN : Fintype.card ι ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) * Bernoulli.probCount q k
      = ∑ i, q i := by
  classical
  -- expand each layer and replace the index by the cardinality
  have hexp : ∀ k ∈ Finset.range (N + 1),
      (k : ℝ) * Bernoulli.probCount q k
        = ∑ t ∈ (Finset.univ : Finset ι).powersetCard k,
            (t.card : ℝ) * Bernoulli.atomProb q t := by
    intro k _
    rw [Bernoulli.probCount_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.mp ht).2]
  -- regroup the layers into the whole powerset
  have hgroup : ∑ k ∈ Finset.range (Fintype.card ι + 1),
      ∑ t ∈ (Finset.univ : Finset ι).powersetCard k,
        (t.card : ℝ) * Bernoulli.atomProb q t
      = ∑ t : Finset ι, (t.card : ℝ) * Bernoulli.atomProb q t := by
    rw [← Finset.powerset_univ, ← Finset.card_univ]
    exact (Finset.sum_powerset (Finset.univ : Finset ι) _).symm
  have hext : ∑ k ∈ Finset.range (N + 1),
      ∑ t ∈ (Finset.univ : Finset ι).powersetCard k,
        (t.card : ℝ) * Bernoulli.atomProb q t
      = ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ∑ t ∈ (Finset.univ : Finset ι).powersetCard k,
          (t.card : ℝ) * Bernoulli.atomProb q t := by
    have hsub : Finset.range (Fintype.card ι + 1) ⊆ Finset.range (N + 1) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact Finset.mem_range.mpr (by omega)
    refine (Finset.sum_subset hsub ?_).symm
    intro k _ hk
    have hlt : ¬ (k < Fintype.card ι + 1) := fun hc => hk (Finset.mem_range.mpr hc)
    have hklt : (Finset.univ : Finset ι).card < k := by
      rw [Finset.card_univ]
      omega
    rw [Finset.powersetCard_eq_empty.mpr hklt, Finset.sum_empty]
  -- the marginals
  have hcard : ∀ t : Finset ι,
      ((t.card : ℝ)) = ∑ i, (if i ∈ t then (1:ℝ) else 0) := by
    intro t
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_congr rfl hexp, hext, hgroup,
    Finset.sum_congr rfl fun t _ => by rw [hcard t, Finset.sum_mul],
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_atomProb_mem q i

/-- **The mean identity**: under a Bernoulli rank law on `F`, the expected
count is `∑ qᵢ`. -/
theorem expCard_eq_sum_of_rankLaw {w : Finset ι → ℝ} {F : Finset ι} {m : ℕ}
    {q : Fin m → ℝ}
    (hlaw : ∀ k, weightMass w (fun S => (S ∩ F).card = k)
      = Bernoulli.probCount q k) :
    expCard w F = ∑ i, q i := by
  classical
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  rw [expCard_eq_sum_layer w F (N := max F.card m) (le_max_left _ _),
    Finset.sum_congr rfl fun k _ => by rw [hlaw k]]
  exact sum_range_mul_probCount q (by rw [hcard]; exact le_max_right _ _)

/-! ### The exponential bound at zero -/

theorem probCount_zero_eq_prod (q : ι → ℝ) :
    Bernoulli.probCount q 0 = ∏ i, (1 - q i) := by
  classical
  rw [Bernoulli.probCount_def, Finset.powersetCard_zero, Finset.sum_singleton,
    Bernoulli.atomProb, Finset.prod_empty, one_mul, Finset.sdiff_empty]

/-- **`P[X = 0] ≤ exp(−E X)`**, straight from the product formula. -/
theorem probCount_zero_le_exp (q : ι → ℝ) (h1 : ∀ i, q i ≤ 1) :
    Bernoulli.probCount q 0 ≤ Real.exp (-∑ i, q i) := by
  classical
  rw [probCount_zero_eq_prod, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => by linarith [h1 i]) fun i _ => ?_
  linarith [Real.add_one_le_exp (-q i)]

/-! ### Numerical constants -/

/-- `1 − e^{−x} ≥ 0.98 x` for `0 ≤ x ≤ 1 / 50`. -/
theorem one_sub_exp_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 50) :
    0.98 * x ≤ 1 - Real.exp (-x) := by
  have hexp : (1 : ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hx1 : (0:ℝ) < 1 + x := by linarith
  have hneg : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have h1 : (1 : ℝ) / Real.exp x ≤ 1 / (1 + x) :=
    one_div_le_one_div_of_le hx1 hexp
  have h2 : (1 : ℝ) / (1 + x) ≤ 1 - 0.98 * x := by
    rw [div_le_iff₀ hx1]
    nlinarith
  rw [hneg]
  linarith

theorem exp_half_le : Real.exp 0.5 ≤ 5/3 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hsq : Real.exp 0.5 * Real.exp 0.5 = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : 0 < Real.exp 0.5 := Real.exp_pos _
  nlinarith [hsq, h1, hpos]

theorem exp_three_halves_le : Real.exp 1.5 ≤ 4.5 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hpos1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hcube : Real.exp 1.5 * Real.exp 1.5
      = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hpos : 0 < Real.exp 1.5 := Real.exp_pos _
  nlinarith [hcube, h1, hpos, hpos1]

theorem exp_two_le : Real.exp 2 ≤ 7.39 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [hsq, h1, hpos]

theorem exp_one_point_three_ge : (3.334 : ℝ) ≤ Real.exp 1.3 := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h2 : (1.3 : ℝ) ≤ Real.exp 0.3 := by
    linarith [Real.add_one_le_exp (0.3 : ℝ)]
  have hsplit : Real.exp 1.3 = Real.exp 1 * Real.exp 0.3 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [hsplit, h1, h2]

theorem exp_neg_two_ge : (0.135 : ℝ) ≤ Real.exp (-2) := by
  have h : (1:ℝ) / 7.39 ≤ 1 / Real.exp 2 :=
    one_div_le_one_div_of_le (Real.exp_pos 2) exp_two_le
  rw [Real.exp_neg, ← one_div]
  linarith [h]

theorem exp_neg_half_ge : (0.6 : ℝ) ≤ Real.exp (-0.5) := by
  have h : (1:ℝ) / (5/3) ≤ 1 / Real.exp 0.5 :=
    one_div_le_one_div_of_le (Real.exp_pos 0.5) exp_half_le
  rw [Real.exp_neg, ← one_div]
  linarith [h]

/-- A base bounded away from zero, raised to a tiny power, is near one. -/
theorem rpow_ge_of_small {a t : ℝ} (ha : 0.3 ≤ a) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 1000) : (0.998 : ℝ) ≤ a ^ t := by
  have hapos : (0:ℝ) < a := by linarith
  have hexp13 : Real.exp (-1.3) ≤ 0.3 := by
    have h : (1:ℝ) / Real.exp 1.3 ≤ 1 / 3.334 :=
      one_div_le_one_div_of_le (by norm_num) exp_one_point_three_ge
    rw [Real.exp_neg, ← one_div]
    linarith [h]
  have hlog : -1.3 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le hapos]
    linarith
  have hprod : -1.3 * t ≤ Real.log a * t :=
    mul_le_mul_of_nonneg_right hlog ht0
  rw [Real.rpow_def_of_pos hapos]
  nlinarith [Real.add_one_le_exp (Real.log a * t), hprod]

/-! ### The `k = 2` point mass -/

/-- `exp u ≤ (1 − u/2)⁻²` for `u < 2`: the only upper bound on `exp` used
in this file, and it comes from `Real.add_one_le_exp` alone. -/
theorem exp_le_inv_sq {u : ℝ} (hu : u ≤ 0.51) :
    Real.exp u ≤ (1 / (1 - u/2)) * (1 / (1 - u/2)) := by
  have hhalf : (0:ℝ) < 1 - u/2 := by linarith
  have hpos : 0 < Real.exp (u/2) := Real.exp_pos _
  have hstep : Real.exp (u/2) ≤ 1 / (1 - u/2) := by
    have h := Real.add_one_le_exp (-(u/2))
    have hinv : Real.exp (-(u/2)) = 1 / Real.exp (u/2) := by
      rw [Real.exp_neg, one_div]
    rw [hinv] at h
    rw [le_div_iff₀ hhalf]
    have h' : (1 - u/2) * Real.exp (u/2) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
      nlinarith [hmul]
    linarith [h']
  have hsplit : Real.exp u = Real.exp (u/2) * Real.exp (u/2) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul hstep hstep (Real.exp_pos _).le (by positivity)

/-- The anchor: `p² e^{−p}` is at least its value at `3/2` throughout
`[3/2, 2]`. -/
theorem sq_mul_exp_neg_ge {p : ℝ} (h1 : 1.5 ≤ p) (h2 : p ≤ 2) :
    2.25 * Real.exp (-1.5) ≤ p ^ 2 * Real.exp (-p) := by
  set u : ℝ := p - 1.5 with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hu5 : u ≤ 0.5 := by rw [hu]; linarith
  have hhalf : (0:ℝ) < 1 - u/2 := by linarith
  have hexpu := exp_le_inv_sq (u := u) (by linarith)
  have hbern : 1 ≤ (1 + 2*u/3) * (1 - u/2) := by nlinarith
  have hsq : Real.exp u ≤ (1 + 2*u/3) * (1 + 2*u/3) := by
    have hd : (0:ℝ) < (1 - u/2) * (1 - u/2) := by positivity
    have hstep : (1 / (1 - u/2)) * (1 / (1 - u/2))
        ≤ (1 + 2*u/3) * (1 + 2*u/3) := by
      rw [div_mul_div_comm, one_mul, div_le_iff₀ hd]
      nlinarith [hbern]
    linarith [hexpu, hstep]
  have hupos : 0 < Real.exp u := Real.exp_pos _
  have hepos : 0 < Real.exp (-1.5) := Real.exp_pos _
  have hp : p = 1.5 * (1 + 2*u/3) := by rw [hu]; ring
  have hexpp : Real.exp (-p) = Real.exp (-1.5) * (1 / Real.exp u) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_add,
      show (-1.5 : ℝ) + -u = -p from by rw [hu]; ring]
  have hfrac : (2.25 : ℝ) ≤ 2.25 * ((1 + 2*u/3) * (1 + 2*u/3)) / Real.exp u := by
    rw [le_div_iff₀ hupos]
    nlinarith [hsq]
  have hrw : p ^ 2 * Real.exp (-p)
      = (2.25 * ((1 + 2*u/3) * (1 + 2*u/3)) / Real.exp u) * Real.exp (-1.5) := by
    rw [hexpp, hp]
    field_simp
    ring
  rw [hrw]
  nlinarith [hfrac, hepos]

/-- The `l = 1` anchor: `y e^{−y} ≥ 0.3` for `y ∈ [1/2, 1.001]`. -/
theorem mul_exp_neg_ge {y : ℝ} (h1 : 0.5 ≤ y) (h2 : y ≤ 1.001) :
    (0.3 : ℝ) ≤ y * Real.exp (-y) := by
  set u : ℝ := y - 0.5 with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hu5 : u ≤ 0.501 := by rw [hu]; linarith
  have hhalf : (0:ℝ) < 1 - u/2 := by linarith
  have hexpu := exp_le_inv_sq (u := u) (by linarith)
  have hfactor : (0:ℝ) ≤ 1 - 1.75*u + 0.5*u^2 := by
    nlinarith [sq_nonneg u, hu0, hu5]
  have hbern : 1 ≤ (1 + 2*u) * ((1 - u/2) * (1 - u/2)) := by
    nlinarith [mul_nonneg hu0 hfactor]
  have hsq : Real.exp u ≤ 1 + 2*u := by
    have hd : (0:ℝ) < (1 - u/2) * (1 - u/2) := by positivity
    have hstep : (1 / (1 - u/2)) * (1 / (1 - u/2)) ≤ 1 + 2*u := by
      rw [div_mul_div_comm, one_mul, div_le_iff₀ hd]
      nlinarith [hbern]
    linarith [hexpu, hstep]
  have hupos : 0 < Real.exp u := Real.exp_pos _
  have hy : y = 0.5 * (1 + 2*u) := by rw [hu]; ring
  have hexpy : Real.exp (-y) = Real.exp (-0.5) * (1 / Real.exp u) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_add,
      show (-0.5 : ℝ) + -u = -y from by rw [hu]; ring]
  have hfrac : (1 : ℝ) ≤ (1 + 2*u) / Real.exp u := by
    rw [le_div_iff₀ hupos]
    linarith [hsq]
  have hrw : y * Real.exp (-y)
      = ((1 + 2*u) / Real.exp u) * (0.5 * Real.exp (-0.5)) := by
    rw [hexpy, hy]
    field_simp
  rw [hrw]
  nlinarith [hfrac, exp_neg_half_ge]

/-- **The `k = 2` point mass is at least `0.25`** for a mean in
`[3/2, 2 + 1/1000]`. -/
theorem probCount_two_ge (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 1.5 ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 2 + 1 / 1000) :
    (0.25 : ℝ) ≤ Bernoulli.probCount q 2 := by
  classical
  obtain ⟨l, hl2, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 2
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  simp only [Nat.cast_ofNat]
  set p : ℝ := ∑ i, q i with hp
  have hfac : ∀ a : ℝ, 0.3 ≤ a → (0.998 : ℝ) ≤ a ^ max (p - 2) 0 := by
    intro a ha
    rcases le_or_gt p 2 with hle | hgt
    · rw [show max (p - 2) 0 = 0 from max_eq_right (by linarith), Real.rpow_zero]
      norm_num
    · exact rpow_ge_of_small ha (le_max_right _ _)
        (max_le (by linarith) (by norm_num))
  have hfact2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  have hfact1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
  have hfact0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
  interval_cases l
  · -- `l = 0`
    rw [Nat.cast_zero, sub_zero, show (2 - 0 : ℕ) = 2 from rfl,
      Bernoulli.poi, hfact2, show ((2:ℕ) : ℝ) + 1 = 3 from by norm_num]
    rcases le_or_gt p 2 with hle | hgt
    · rw [show max (p - 2) 0 = 0 from max_eq_right (by linarith), Real.rpow_zero,
        mul_one]
      have hanchor := sq_mul_exp_neg_ge h1 hle
      have hge : (0.5 : ℝ) ≤ 2.25 * Real.exp (-1.5) := by
        have h : (1:ℝ) / 4.5 ≤ 1 / Real.exp 1.5 :=
          one_div_le_one_div_of_le (Real.exp_pos 1.5) exp_three_halves_le
        rw [Real.exp_neg, ← one_div]
        linarith [h]
      have hcomm : Real.exp (-p) * p ^ 2 = p ^ 2 * Real.exp (-p) := by ring
      rw [hcomm]
      linarith [hanchor, hge]
    · have hf := hfac (1 - p/3) (by linarith)
      have hsplit : Real.exp (-p) = Real.exp (-2) * Real.exp (-(p - 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hlow : (0.999 : ℝ) ≤ Real.exp (-(p - 2)) := by
        linarith [Real.add_one_le_exp (-(p - 2))]
      have hpsq : (4 : ℝ) ≤ p ^ 2 := by nlinarith
      have hpoi : (0.269 : ℝ) ≤ Real.exp (-p) * p ^ 2 / 2 := by
        rw [hsplit]
        have hmul1 : (0.135 : ℝ) * 0.999
            ≤ Real.exp (-2) * Real.exp (-(p - 2)) :=
          mul_le_mul exp_neg_two_ge hlow (by norm_num) (Real.exp_pos _).le
        have hmul2 : ((0.135 : ℝ) * 0.999) * 4
            ≤ (Real.exp (-2) * Real.exp (-(p - 2))) * p ^ 2 :=
          mul_le_mul hmul1 hpsq (by norm_num) (by positivity)
        linarith [hmul2]
      have hprod : (0.269 : ℝ) * 0.998
          ≤ (Real.exp (-p) * p ^ 2 / 2) * (1 - p/3) ^ max (p - 2) 0 :=
        mul_le_mul hpoi hf (by norm_num) (by positivity)
      linarith [hprod]
  · -- `l = 1`
    rw [Nat.cast_one, show (2 - 1 : ℕ) = 1 from rfl,
      Bernoulli.poi, hfact1, show (1:ℝ) + 1 = 2 from by norm_num]
    have hanchor := mul_exp_neg_ge (y := p - 1) (by linarith) (by linarith)
    have hf := hfac (1 - (p - 1)/2) (by linarith)
    have hcomm : Real.exp (-(p - 1)) * (p - 1) ^ 1 / 1
        = (p - 1) * Real.exp (-(p - 1)) := by ring
    rw [hcomm]
    nlinarith [hanchor, hf]
  · -- `l = 2`
    rw [show ((2 : ℕ) : ℝ) = 2 from by norm_num, show (2 - 2 : ℕ) = 0 from rfl,
      Bernoulli.poi, hfact0, show ((0:ℕ) : ℝ) + 1 = 1 from by norm_num]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hlp
    have hlow : (0.999 : ℝ) ≤ Real.exp (-(p - 2)) := by
      linarith [Real.add_one_le_exp (-(p - 2))]
    have hf := hfac (1 - (p - 2)/1) (by linarith)
    have hcomm : Real.exp (-(p - 2)) * (p - 2) ^ 0 / 1
        = Real.exp (-(p - 2)) := by
      rw [pow_zero]
      ring
    rw [hcomm]
    nlinarith [hlow, hf]

end TSPGap

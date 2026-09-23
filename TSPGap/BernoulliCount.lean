/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Hoeffding

/-!
# Counting probabilities of Bernoulli sums

The point masses `P[X = k]` (`probCount`) and tails `P[X ≥ k]` (`probGE`) of a sum `X` of
independent Bernoullis, their expression as expectations of indicators, the evaluation of
`P[X = k]` on a **three-valued** configuration (`|O|` sure successes, `Z` sure failures, the
rest i.i.d. `x`-Bernoullis) as a shifted binomial mass (`probCount_threeValued`), the
vanishing of `P[X = k]` below the number of sure successes (`probCount_eq_zero_of_lt`),
the falling-factorial identity `C(n,k) (p/n)^k = p^k/k! · ∏ (1 - i/n)` (`cast_choose_mul_pow`),
and the Poisson point mass `poi`.

Split off `Poisson.lean` on 2026-09-11 so that the binomial–Poisson comparison
(`BinomialPoisson.lean`) can use these without sitting downstream of its own consumer.
-/

namespace TSPGap
namespace Bernoulli

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Poisson point mass `e^{-p} p^m / m!`. -/
noncomputable def poi (p : ℝ) (m : ℕ) : ℝ := Real.exp (-p) * p ^ m / m.factorial

/-- The probability that exactly `k` of the independent Bernoullis with
success probabilities `q` succeed. -/
def probCount (q : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.univ.powersetCard k, atomProb q t

theorem probCount_def (q : ι → ℝ) (k : ℕ) :
    probCount q k = ∑ t ∈ Finset.univ.powersetCard k, atomProb q t := rfl

/-- `P[X = k]` is the expectation of the indicator of `{k}`. -/
theorem expect_indicator (k : ℕ) (q : ι → ℝ) :
    expect (fun m => if m = k then (1 : ℝ) else 0) q = probCount q k := by
  classical
  rw [expect_def, probCount_def,
    show Finset.univ.powersetCard k
        = Finset.univ.filter (fun t : Finset ι => t.card = k) by ext t; simp,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t.card = k <;> simp [h]

/-! ### Three-valued configurations -/

/-- The mean of a three-valued configuration: `O` sure successes, `Z` sure
failures, and the rest `x`-Bernoullis. -/
theorem sum_threeValued (q : ι → ℝ) (O Z : Finset ι) (x : ℝ)
    (hO : ∀ i ∈ O, q i = 1) (hZ : ∀ i ∈ Z, q i = 0)
    (hx : ∀ i, i ∉ O → i ∉ Z → q i = x) (hOZ : Disjoint O Z) :
    ∑ i, q i = (O.card : ℝ) + ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
  classical
  have hsplit := Finset.sum_sdiff (f := q) (Finset.subset_univ (O ∪ Z))
  have h1 : ∑ i ∈ O ∪ Z, q i = (O.card : ℝ) := by
    rw [Finset.sum_union hOZ, Finset.sum_congr rfl hO,
      Finset.sum_congr rfl hZ, Finset.sum_const, Finset.sum_const]
    simp
  have h2 : ∑ i ∈ Finset.univ \ (O ∪ Z), q i
      = ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
    have hval : ∀ i ∈ Finset.univ \ (O ∪ Z), q i = x := by
      intro i hi
      have hi' := (Finset.mem_sdiff.mp hi).2
      exact hx i (fun h => hi' (Finset.mem_union_left _ h))
        (fun h => hi' (Finset.mem_union_right _ h))
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  linarith [hsplit]

/-- `P[X = k]` for a three-valued configuration is a shifted binomial
point mass: with `ℓ = |O|` sure successes and `r` remaining `x`-Bernoullis,
`P[X = k] = C(r, k-ℓ) x^{k-ℓ} (1-x)^{r-(k-ℓ)}`. -/
theorem probCount_threeValued (q : ι → ℝ) (O Z : Finset ι) (x : ℝ)
    (hO : ∀ i ∈ O, q i = 1) (hZ : ∀ i ∈ Z, q i = 0)
    (hx : ∀ i, i ∉ O → i ∉ Z → q i = x) (hOZ : Disjoint O Z)
    (k : ℕ) (hlk : O.card ≤ k) :
    probCount q k
      = ((Finset.univ \ (O ∪ Z)).card.choose (k - O.card) : ℝ)
        * (x ^ (k - O.card)
          * (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - (k - O.card))) := by
  classical
  -- atoms outside the family `O ⊆ t`, `t ∩ Z = ∅` vanish
  have hvanish : ∀ t ∈ Finset.univ.powersetCard k, atomProb q t ≠ 0 →
      O ⊆ t ∧ Disjoint t Z := by
    intro t _ hne
    constructor
    · by_contra hOt
      obtain ⟨i, hiO, hit⟩ := Finset.not_subset.mp hOt
      refine hne ?_
      unfold atomProb
      rw [Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩)
        (by rw [hO i hiO]; ring), mul_zero]
    · rw [Finset.disjoint_left]
      intro i hit hiZ
      refine hne ?_
      unfold atomProb
      rw [Finset.prod_eq_zero hit (hZ i hiZ), zero_mul]
  have hfilter : probCount q k
      = ∑ t ∈ (Finset.univ.powersetCard k).filter
          (fun t => O ⊆ t ∧ Disjoint t Z), atomProb q t :=
    (Finset.sum_filter_of_ne hvanish).symm
  -- reindex the surviving atoms by `t ↦ t \ O`
  have hbij : ∑ t ∈ (Finset.univ.powersetCard k).filter
        (fun t => O ⊆ t ∧ Disjoint t Z), atomProb q t
      = ∑ _s ∈ (Finset.univ \ (O ∪ Z)).powersetCard (k - O.card),
          (x ^ (k - O.card)
            * (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - (k - O.card))) := by
    refine Finset.sum_bij' (fun t _ => t \ O) (fun s _ => s ∪ O)
      ?_ ?_ ?_ ?_ ?_
    · -- maps into the target family
      intro t ht
      rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
      obtain ⟨⟨-, htk⟩, hOt, htZ⟩ := ht
      rw [Finset.mem_powersetCard]
      constructor
      · intro i hi
        obtain ⟨hit, hiO⟩ := Finset.mem_sdiff.mp hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun hmem => ?_⟩
        rcases Finset.mem_union.mp hmem with h | h
        · exact hiO h
        · exact Finset.disjoint_left.mp htZ hit h
      · rw [Finset.card_sdiff_of_subset hOt, htk]
    · -- maps back
      intro s hs
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨hsR, hsc⟩ := hs
      have hsO : Disjoint s O := by
        rw [Finset.disjoint_left]
        intro i his hiO
        exact (Finset.mem_sdiff.mp (hsR his)).2 (Finset.mem_union_left _ hiO)
      have hsZ : Disjoint s Z := by
        rw [Finset.disjoint_left]
        intro i his hiZ
        exact (Finset.mem_sdiff.mp (hsR his)).2 (Finset.mem_union_right _ hiZ)
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right,
        Finset.disjoint_union_left.mpr ⟨hsZ, hOZ⟩⟩
      rw [Finset.card_union_of_disjoint hsO, hsc]
      omega
    · -- left inverse
      intro t ht
      rw [Finset.mem_filter] at ht
      exact Finset.sdiff_union_of_subset ht.2.1
    · -- right inverse
      intro s hs
      rw [Finset.mem_powersetCard] at hs
      have hsO : Disjoint s O := by
        rw [Finset.disjoint_left]
        intro i his hiO
        exact (Finset.mem_sdiff.mp (hs.1 his)).2 (Finset.mem_union_left _ hiO)
      exact Finset.union_sdiff_cancel_right hsO
    · -- values
      intro t ht
      rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
      obtain ⟨⟨-, htk⟩, hOt, htZ⟩ := ht
      unfold atomProb
      have h1 : ∏ i ∈ t, q i = x ^ (k - O.card) := by
        conv_lhs => rw [← Finset.sdiff_union_of_subset hOt]
        rw [Finset.prod_union Finset.sdiff_disjoint]
        have ha : ∏ i ∈ t \ O, q i = x ^ (k - O.card) := by
          have hxall : ∀ i ∈ t \ O, q i = x := by
            intro i hi
            obtain ⟨hit, hiO⟩ := Finset.mem_sdiff.mp hi
            exact hx i hiO (Finset.disjoint_left.mp htZ hit)
          rw [Finset.prod_congr rfl hxall, Finset.prod_const,
            Finset.card_sdiff_of_subset hOt, htk]
        have hb : ∏ i ∈ O, q i = 1 := by
          rw [Finset.prod_congr rfl hO, Finset.prod_const_one]
        rw [ha, hb, mul_one]
      have h2 : ∏ i ∈ Finset.univ \ t, (1 - q i)
          = (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - (k - O.card)) := by
        have hZsub : Z ⊆ Finset.univ \ t := by
          intro i hiZ
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,
            fun hit => Finset.disjoint_left.mp htZ hit hiZ⟩
        conv_lhs => rw [← Finset.sdiff_union_of_subset hZsub]
        rw [Finset.prod_union Finset.sdiff_disjoint]
        have ha : ∏ i ∈ (Finset.univ \ t) \ Z, (1 - q i)
            = (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - (k - O.card)) := by
          have hxall : ∀ i ∈ (Finset.univ \ t) \ Z, (1 : ℝ) - q i = 1 - x := by
            intro i hi
            obtain ⟨hi1, hiZ⟩ := Finset.mem_sdiff.mp hi
            have hit := (Finset.mem_sdiff.mp hi1).2
            rw [hx i (fun h => hit (hOt h)) hiZ]
          rw [Finset.prod_congr rfl hxall, Finset.prod_const]
          congr 1
          have e1 : ((Finset.univ \ t) \ Z).card
              = (Finset.univ \ t).card - Z.card :=
            Finset.card_sdiff_of_subset hZsub
          have e2 : (Finset.univ \ t).card = Fintype.card ι - k := by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ t), htk, Finset.card_univ]
          have e3 : (Finset.univ \ (O ∪ Z)).card
              = Fintype.card ι - (O.card + Z.card) := by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
              Finset.card_union_of_disjoint hOZ, Finset.card_univ]
          have e4 : k ≤ Fintype.card ι := by
            rw [← htk, ← Finset.card_univ]
            exact Finset.card_le_card (Finset.subset_univ t)
          have e5 : Z.card ≤ Fintype.card ι - k := by
            rw [← e2]
            exact Finset.card_le_card hZsub
          have e6 : O.card + Z.card ≤ Fintype.card ι := by
            rw [← Finset.card_union_of_disjoint hOZ, ← Finset.card_univ]
            exact Finset.card_le_card (Finset.subset_univ _)
          omega
        have hb : ∏ i ∈ Z, ((1 : ℝ) - q i) = 1 := by
          have : ∀ i ∈ Z, (1 : ℝ) - q i = 1 := fun i hi => by
            rw [hZ i hi]; ring
          rw [Finset.prod_congr rfl this, Finset.prod_const_one]
        rw [ha, hb, mul_one]
      rw [h1, h2]
  rw [hfilter, hbij, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-! ### The falling-factorial identity -/

/-- `(n choose k) · k! = ∏_{i<k} (n - i)` in `ℝ`. -/
theorem cast_choose_mul_factorial (n : ℕ) :
    ∀ k : ℕ, k ≤ n → (n.choose k : ℝ) * (k.factorial : ℝ)
      = ∏ i ∈ Finset.range k, ((n : ℝ) - i) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ihm := ih (by omega)
    have hcR : (n.choose (m + 1) : ℝ) * ((m : ℝ) + 1)
        = (n.choose m : ℝ) * ((n : ℝ) - m) := by
      have hc := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq n m)
      push_cast [Nat.cast_sub (by omega : m ≤ n)] at hc
      linarith [hc]
    rw [Finset.prod_range_succ, ← ihm]
    have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    linear_combination (m.factorial : ℝ) * hcR

/-- `(n choose k)(p/n)^k = p^k/k! · ∏_{i=1}^{k-1}(1 - i/n)`. -/
theorem cast_choose_mul_pow (n k : ℕ) (hkn : k ≤ n) (hn : 0 < n) (p : ℝ) :
    (n.choose k : ℝ) * (p / n) ^ k
      = p ^ k / (k.factorial : ℝ)
        * ∏ i ∈ Finset.Icc 1 (k - 1), (1 - (i : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hIcc : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hprod : ∏ i ∈ Finset.range k, ((n : ℝ) - i)
      = (n : ℝ) * ∏ i ∈ Finset.Ico 1 k, ((n : ℝ) - i) := by
    rw [Finset.prod_range_eq_mul_Ico _ hk]
    norm_num
  have hdiv : ∏ i ∈ Finset.Ico 1 k, (1 - (i : ℝ) / n)
      = (∏ i ∈ Finset.Ico 1 k, ((n : ℝ) - i)) / (n : ℝ) ^ (k - 1) := by
    have h1 : ∀ i ∈ Finset.Ico 1 k, (1 - (i : ℝ) / n) = ((n : ℝ) - i) / n := by
      intro i _
      field_simp
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, Finset.prod_const,
      Nat.card_Ico]
  have hC : (n.choose k : ℝ)
      = (n : ℝ) * (∏ i ∈ Finset.Ico 1 k, ((n : ℝ) - i)) / (k.factorial : ℝ) := by
    rw [eq_div_iff hkfac]
    exact (cast_choose_mul_factorial n k hkn).trans hprod
  have hnk : (n : ℝ) ^ k = (n : ℝ) * (n : ℝ) ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hIcc, hdiv, div_pow, hnk, hC]
  field_simp

/-! ### Tails -/

/-! ### KKO21 Lemma 2.22: the Poisson tail bound -/

/-- The probability that at least `k` of the independent Bernoullis with
success probabilities `q` succeed. -/
def probGE (q : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.univ.powerset.filter (fun t => k ≤ t.card), atomProb q t

theorem probGE_def (q : ι → ℝ) (k : ℕ) :
    probGE q k = ∑ t ∈ Finset.univ.powerset.filter (fun t => k ≤ t.card),
      atomProb q t := rfl

/-- `P[X ≥ k]` is the expectation of the indicator of `{k, k+1, …}`. -/
theorem expect_indicator_ge (k : ℕ) (q : ι → ℝ) :
    expect (fun m => if k ≤ m then (1 : ℝ) else 0) q = probGE q k := by
  classical
  rw [expect_def, probGE_def, Finset.powerset_univ, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : k ≤ t.card <;> simp [h]

/-- The counting probabilities below `k` and the tail `P[X ≥ k]` sum to
one. -/
theorem sum_probCount_add_probGE (q : ι → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, probCount q j) + probGE q k = 1 := by
  classical
  have hmaps : ∀ t ∈ Finset.univ.powerset.filter
      (fun t : Finset ι => t.card < k), t.card ∈ Finset.range k :=
    fun t ht => Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (atomProb q)
  have hfibers : ∀ j ∈ Finset.range k,
      ∑ t ∈ (Finset.univ.powerset.filter
          (fun t : Finset ι => t.card < k)).filter (fun t => t.card = j),
        atomProb q t = probCount q j := by
    intro j hj
    rw [probCount_def]
    refine Finset.sum_congr ?_ fun t _ => rfl
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, -⟩, hcard⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨hsub, by have := Finset.mem_range.mp hj; omega⟩, hcard⟩
  rw [Finset.sum_congr rfl hfibers] at hfib
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ.powerset
    (fun t : Finset ι => t.card < k) (atomProb q)
  rw [sum_atomProb] at hsplit
  have hnot : Finset.univ.powerset.filter (fun t : Finset ι => ¬ t.card < k)
      = Finset.univ.powerset.filter (fun t : Finset ι => k ≤ t.card) := by
    ext t
    simp only [Finset.mem_filter, Nat.not_lt]
  rw [hnot] at hsplit
  rw [hfib, probGE_def]
  exact hsplit

/-- With `|O|` sure successes, fewer than `|O|` total successes is
impossible. -/
theorem probCount_eq_zero_of_lt (q : ι → ℝ) (O : Finset ι)
    (hO : ∀ i ∈ O, q i = 1) {j : ℕ} (hj : j < O.card) :
    probCount q j = 0 := by
  classical
  rw [probCount_def]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htj : t.card = j := (Finset.mem_powersetCard.mp ht).2
  have hOt : ¬ O ⊆ t := fun hsub => by
    have h := Finset.card_le_card hsub
    omega
  obtain ⟨i, hiO, hit⟩ := Finset.not_subset.mp hOt
  unfold atomProb
  rw [Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩)
    (by rw [hO i hiO]; ring), mul_zero]

end Bernoulli
end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BernoulliCount
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The binomial lower tail below the mean against shifted Poisson tails

`binomial_lowerTail_le_shifted_poisson` ([Hoe56, Theorem 4] with the binomial→Poisson
limit; the analytic heart of KKO21 Lemma 2.22): for an integer threshold `j` below the mean
`m x` of `Bin(m, x)`, some shift `a ≤ j` has `P[Bin(m,x) ≤ j] ≤ P[Poi(m x − a) ≤ j − a]`.
Design record: `BINPOI_DESIGN.md`.

**The finite part** (`exists_shift_binomTail_le`, this checkpoint): pad the binomial to any
finite index type, take Hoeffding's three-valued maximiser of the lower tail
(`exists_max_three_valued`, `Hoeffding.lean`) with `ℓ` sure successes, `t` copies of `a` and
some zeros.  Positivity of the binomial tail forces `ℓ ≤ j` and `t ≥ 1`
(`probCount_eq_zero_of_lt`).  Zeros are excluded by the **split perturbation**
(`probLE_split`): replacing a zero and an `a` by two `a/2` keeps the mean and changes the
tail by `(a²/4)(b_K − b_{K−1})`, `b` the mass of `Bin(t−1, a)` at the residual threshold
`K = j − ℓ`; the coefficient is identified from the corner values of `expect_pair`, and it is
positive exactly when `K < t a`, i.e. `j < m x`, through the division-free identity
`K (1−a) b_K = (t − K) a b_{K−1}` (`binom_succ_mul`).  So the maximiser has no zeros and
the tail is bounded by `P[Bin(N − ℓ, (m x − ℓ)/(N − ℓ)) ≤ j − ℓ]`.

This is Hoeffding's second-difference argument for Theorem 4 specialised to the indicator
of `{≤ j}`; it uses only `j < m x`, so no upper clause on the threshold is needed.
-/

namespace TSPGap
namespace Bernoulli

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Binomial masses and tails -/

/-- The binomial point mass `C(t,k) a^k (1-a)^{t-k}`. -/
noncomputable def binom (t : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  (t.choose k : ℝ) * a ^ k * (1 - a) ^ (t - k)

/-- The binomial lower tail with `n` terms, `P[Bin(t,a) ≤ n - 1]`. -/
noncomputable def binomTail (t : ℕ) (a : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, binom t a k

theorem binom_nonneg {t : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    0 ≤ binom t a k := by
  unfold binom
  have : 0 ≤ 1 - a := by linarith
  positivity

theorem binom_pos {t : ℕ} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℕ} (hk : k ≤ t) :
    0 < binom t a k := by
  unfold binom
  have h1 : (0 : ℝ) < t.choose k := by exact_mod_cast Nat.choose_pos hk
  have : 0 < 1 - a := by linarith
  positivity

theorem binom_zero (t : ℕ) (a : ℝ) : binom t a 0 = (1 - a) ^ t := by
  simp [binom]

/-- The division-free ratio identity: `K (1-a) b_K = (t - K) a b_{K-1}` for the masses of
`Bin(t-1, a)`, `1 ≤ K ≤ t`. -/
theorem binom_succ_mul {t K : ℕ} (hK : 1 ≤ K) (hKt : K ≤ t) (a : ℝ) :
    (K : ℝ) * (1 - a) * binom (t - 1) a K = ((t : ℝ) - K) * a * binom (t - 1) a (K - 1) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel, binom]
  by_cases hlt : K' < t'
  · have hch : ((t'.choose (K' + 1) : ℕ) : ℝ) * (K' + 1) =
        (t'.choose K' : ℝ) * ((t' : ℝ) - K') := by
      have h := Nat.choose_succ_right_eq t' K'
      have hle : K' ≤ t' := hlt.le
      have : ((t'.choose (K' + 1) * (K' + 1) : ℕ) : ℝ) =
          ((t'.choose K' * (t' - K') : ℕ) : ℝ) := by rw [h]
      push_cast [hle] at this
      exact this
    have hpow : (1 - a) ^ (t' - (K' + 1)) * (1 - a) = (1 - a) ^ (t' - K') := by
      rw [← pow_succ]
      congr 1
      omega
    have ht : ((t' + 1 : ℕ) : ℝ) - ((K' + 1 : ℕ) : ℝ) = (t' : ℝ) - K' := by push_cast; ring
    rw [ht]
    calc ((K' + 1 : ℕ) : ℝ) * (1 - a) * ((t'.choose (K' + 1) : ℝ) * a ^ (K' + 1) *
          (1 - a) ^ (t' - (K' + 1)))
        = ((t'.choose (K' + 1) : ℝ) * (K' + 1)) * a ^ (K' + 1) *
            ((1 - a) ^ (t' - (K' + 1)) * (1 - a)) := by push_cast; ring
      _ = ((t'.choose K' : ℝ) * ((t' : ℝ) - K')) * a ^ (K' + 1) * (1 - a) ^ (t' - K') := by
            rw [hch, hpow]
      _ = ((t' : ℝ) - K') * a * ((t'.choose K' : ℝ) * a ^ K' * (1 - a) ^ (t' - K')) := by ring
  · -- `K = t`: both sides vanish
    have hK : K' = t' := by omega
    subst hK
    simp [Nat.choose_succ_self]

/-! ### The lower tail of a Bernoulli sum -/

/-- The probability that at most `c` of the independent Bernoullis succeed. -/
def probLE (q : ι → ℝ) (c : ℕ) : ℝ := ∑ k ∈ range (c + 1), probCount q k

/-- `P[X ≤ c]` is the expectation of the indicator of `{0, …, c}`. -/
theorem expect_indicator_le (c : ℕ) (q : ι → ℝ) :
    expect (fun m => if m ≤ c then (1 : ℝ) else 0) q = probLE q c := by
  classical
  have hind : ∀ m : ℕ, (if m ≤ c then (1 : ℝ) else 0) =
      ∑ k ∈ range (c + 1), if m = k then (1 : ℝ) else 0 := by
    intro m
    rw [sum_ite_eq]
    simp
  rw [probLE, expect_def]
  simp_rw [hind, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← expect_indicator, expect_def]

theorem atomProb_nonneg (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (t : Finset ι) :
    0 ≤ atomProb q t := by
  unfold atomProb
  refine mul_nonneg (prod_nonneg fun i _ => (hq i).1) (prod_nonneg fun i _ => ?_)
  have := (hq i).2
  linarith

theorem probLE_nonneg (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (c : ℕ) :
    0 ≤ probLE q c :=
  sum_nonneg fun _ _ => sum_nonneg fun t _ => atomProb_nonneg q hq t

/-- The lower tail of a three-valued configuration: a binomial tail with `|O|` fewer terms
(`probCount_threeValued` termwise, `probCount_eq_zero_of_lt` below `|O|`). -/
theorem probLE_threeValued (q : ι → ℝ) (O Z : Finset ι) (x : ℝ)
    (hO : ∀ i ∈ O, q i = 1) (hZ : ∀ i ∈ Z, q i = 0)
    (hx : ∀ i, i ∉ O → i ∉ Z → q i = x) (hOZ : Disjoint O Z) (c : ℕ) :
    probLE q c = binomTail (univ \ (O ∪ Z)).card x (c + 1 - O.card) := by
  classical
  rw [probLE, binomTail]
  by_cases hc : O.card ≤ c + 1
  · rw [← sum_range_add_sum_Ico _ hc, sum_eq_zero (fun k hk =>
      probCount_eq_zero_of_lt q O hO (mem_range.mp hk)), zero_add,
      sum_Ico_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    rw [probCount_threeValued q O Z x hO hZ hx hOZ (O.card + k) (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, binom]
    ring
  · push Not at hc
    rw [Nat.sub_eq_zero_of_le hc.le, range_zero, sum_empty]
    exact sum_eq_zero fun k hk =>
      probCount_eq_zero_of_lt q O hO (by have := mem_range.mp hk; omega)

/-! ### Three-valued configurations under updates -/

/-- `q` is `1` on `O`, `0` on `Z`, and `a` elsewhere. -/
def IsThreeValued (q : ι → ℝ) (O Z : Finset ι) (a : ℝ) : Prop :=
  (∀ i ∈ O, q i = 1) ∧ (∀ i ∈ Z, q i = 0) ∧ (∀ i, i ∉ O → i ∉ Z → q i = a) ∧ Disjoint O Z

theorem IsThreeValued.probLE {q : ι → ℝ} {O Z : Finset ι} {a : ℝ}
    (h : IsThreeValued q O Z a) (c : ℕ) :
    probLE q c = binomTail (univ \ (O ∪ Z)).card a (c + 1 - O.card) :=
  probLE_threeValued q O Z a h.1 h.2.1 h.2.2.1 h.2.2.2 c

theorem IsThreeValued.sum {q : ι → ℝ} {O Z : Finset ι} {a : ℝ} (h : IsThreeValued q O Z a) :
    ∑ i, q i = (O.card : ℝ) + ((univ \ (O ∪ Z)).card : ℝ) * a :=
  sum_threeValued q O Z a h.1 h.2.1 h.2.2.1 h.2.2.2

omit [Fintype ι] in
/-- Setting a coordinate to `1`. -/
theorem IsThreeValued.update_one {q : ι → ℝ} {O Z : Finset ι} {a : ℝ}
    (h : IsThreeValued q O Z a) (k : ι) :
    IsThreeValued (Function.update q k 1) (insert k O) (Z.erase k) a := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hiO hiZ => ?_, ?_⟩
  · rw [mem_insert] at hi
    rcases hi with rfl | hi
    · simp
    · by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik]; exact h.1 i hi
  · rw [mem_erase] at hi
    rw [Function.update_of_ne hi.1]
    exact h.2.1 i hi.2
  · rw [mem_insert, not_or] at hiO
    rw [mem_erase, not_and] at hiZ
    rw [Function.update_of_ne hiO.1]
    exact h.2.2.1 i hiO.2 (hiZ hiO.1)
  · rw [disjoint_left]
    intro i hi hi'
    rw [mem_insert] at hi
    rw [mem_erase] at hi'
    rcases hi with rfl | hi
    · exact hi'.1 rfl
    · exact disjoint_left.mp h.2.2.2 hi hi'.2

omit [Fintype ι] in
/-- Setting a coordinate to `0`. -/
theorem IsThreeValued.update_zero {q : ι → ℝ} {O Z : Finset ι} {a : ℝ}
    (h : IsThreeValued q O Z a) (k : ι) :
    IsThreeValued (Function.update q k 0) (O.erase k) (insert k Z) a := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hiO hiZ => ?_, ?_⟩
  · rw [mem_erase] at hi
    rw [Function.update_of_ne hi.1]
    exact h.1 i hi.2
  · rw [mem_insert] at hi
    rcases hi with rfl | hi
    · simp
    · by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik]; exact h.2.1 i hi
  · rw [mem_erase, not_and] at hiO
    rw [mem_insert, not_or] at hiZ
    rw [Function.update_of_ne hiZ.1]
    exact h.2.2.1 i (hiO hiZ.1) hiZ.2
  · rw [disjoint_left]
    intro i hi hi'
    rw [mem_erase] at hi
    rw [mem_insert] at hi'
    rcases hi' with rfl | hi'
    · exact hi.1 rfl
    · exact disjoint_left.mp h.2.2.2 hi.2 hi'

/-! ### The split perturbation -/

/-- The complement of `insert j (O ∪ Z)` has one element fewer. -/
theorem card_sdiff_insert_union (O Z : Finset ι) {j : ι} (hj : j ∉ O ∪ Z) :
    (univ \ insert j (O ∪ Z)).card = (univ \ (O ∪ Z)).card - 1 := by
  rw [sdiff_insert, card_erase_of_mem (mem_sdiff.mpr ⟨mem_univ _, hj⟩)]

/-- **The split perturbation.**  At a three-valued vector with a zero at `i` and the middle
value `a` at `j`, replacing both by `a/2` changes the lower tail at a threshold `c ≥ |O|` by
`(a²/4)(b_K - b_{K-1})`, `b` the mass of `Bin(t-1, a)`, `K = c - |O|`, `t` the number of
`a`-coordinates (`b_{-1} = 0`). -/
theorem probLE_split {q : ι → ℝ} {O Z : Finset ι} {a : ℝ} (h : IsThreeValued q O Z a)
    {i j : ι} (hi : i ∈ Z) (hj : j ∉ O ∪ Z) {c : ℕ} (hc : O.card ≤ c) :
    probLE (Function.update (Function.update q i (a / 2)) j (a / 2)) c =
      probLE q c + a ^ 2 / 4 *
        (binom ((univ \ (O ∪ Z)).card - 1) a (c - O.card) -
          if 1 ≤ c - O.card then binom ((univ \ (O ∪ Z)).card - 1) a (c - O.card - 1) else 0) := by
  classical
  have hij : i ≠ j := fun h' => hj (mem_union.mpr (Or.inr (h' ▸ hi)))
  have hjO : j ∉ O := fun h' => hj (mem_union.mpr (Or.inl h'))
  have hjZ : j ∉ Z := fun h' => hj (mem_union.mpr (Or.inr h'))
  have hiO : i ∉ O := disjoint_right.mp h.2.2.2 hi
  set g : ℕ → ℝ := fun m => if m ≤ c then 1 else 0 with hg
  obtain ⟨A, B, C, hpair⟩ := expect_pair g q hij
  have hqi : q i = 0 := h.2.1 i hi
  have hqj : q j = a := h.2.2.1 j hjO hjZ
  -- the value at `q` itself and at the split vector
  have hE0 : expect g q = A + B * a := by
    have := hpair 0 a
    rw [← hqi, Function.update_eq_self, ← hqj, Function.update_eq_self] at this
    rw [this, hqi, hqj]; ring
  have hEs : expect g (Function.update (Function.update q i (a / 2)) j (a / 2)) =
      A + B * a + C * (a ^ 2 / 4) := by
    rw [hpair]; ring
  -- the corner values
  have h00 := hpair 0 0
  have h10 := hpair 1 0
  have h11 := hpair 1 1
  have hC : C = expect g (Function.update (Function.update q i 1) j 1) -
      2 * expect g (Function.update (Function.update q i 1) j 0) +
      expect g (Function.update (Function.update q i 0) j 0) := by
    rw [h00, h10, h11]; ring
  -- evaluate the corners as binomial tails with `t - 1` trials
  set t := (univ \ (O ∪ Z)).card with ht
  have hcard : (univ \ insert j (O ∪ Z)).card = t - 1 := card_sdiff_insert_union O Z hj
  have hU : insert i O ∪ Z.erase i = O ∪ Z := by
    ext k
    simp only [mem_union, mem_insert, mem_erase]
    constructor
    · rintro ((rfl | hk) | ⟨-, hk⟩)
      · exact Or.inr hi
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (hk | hk)
      · exact Or.inl (Or.inr hk)
      · by_cases hki : k = i
        · exact Or.inl (Or.inl hki)
        · exact Or.inr ⟨hki, hk⟩
  have hP00 : probLE (Function.update (Function.update q i 0) j 0) c =
      binomTail (t - 1) a (c + 1 - O.card) := by
    have h' := (h.update_zero i).update_zero j
    rw [h'.probLE, erase_eq_of_notMem hiO, erase_eq_of_notMem hjO,
      show O ∪ insert j (insert i Z) = insert j (O ∪ Z) by
        rw [insert_eq_of_mem hi, union_insert], hcard]
  have hP10 : probLE (Function.update (Function.update q i 1) j 0) c =
      binomTail (t - 1) a (c + 1 - (O.card + 1)) := by
    have h' := (h.update_one i).update_zero j
    rw [h'.probLE, erase_eq_of_notMem (by rw [mem_insert, not_or]; exact ⟨hij.symm, hjO⟩),
      show insert i O ∪ insert j (Z.erase i) = insert j (O ∪ Z) by
        rw [union_insert, hU], hcard, card_insert_of_notMem hiO]
  have hP11 : probLE (Function.update (Function.update q i 1) j 1) c =
      binomTail (t - 1) a (c + 1 - (O.card + 2)) := by
    have h' := (h.update_one i).update_one j
    rw [h'.probLE, erase_eq_of_notMem (by rw [mem_erase, not_and]; exact fun _ => hjZ),
      show insert j (insert i O) ∪ Z.erase i = insert j (O ∪ Z) by
        rw [insert_union, hU], hcard, card_insert_of_notMem (by
          rw [mem_insert, not_or]; exact ⟨hij.symm, hjO⟩), card_insert_of_notMem hiO]
  -- assemble
  rw [expect_indicator_le] at hE0 hEs
  rw [hC, expect_indicator_le, expect_indicator_le, expect_indicator_le, hP00, hP10, hP11] at hEs
  rw [hEs, hE0]
  -- the tails differ by single masses
  set K := c - O.card with hK
  have h1 : c + 1 - O.card = K + 1 := by omega
  have h2 : c + 1 - (O.card + 1) = K := by omega
  have h3 : c + 1 - (O.card + 2) = K - 1 := by omega
  rw [h1, h2, h3, binomTail, binomTail, binomTail, sum_range_succ]
  by_cases hK1 : 1 ≤ K
  · rw [if_pos hK1]
    obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [hK', Nat.add_sub_cancel, sum_range_succ]
    ring
  · rw [if_neg hK1]
    have hK0 : K = 0 := by omega
    rw [hK0]
    simp only [Nat.zero_sub, range_zero, sum_empty]
    ring

/-! ### The finite padded-binomial bound -/

/-- **The finite checkpoint.**  Among `Fintype.card ι ≥ m` Bernoullis, Hoeffding's
three-valued maximiser of `P[S ≤ j]` at mean `m x` has `ℓ ≤ j` sure successes, no zeros,
and `Fintype.card ι - ℓ` copies of some `a ∈ (0,1)`; hence
`P[Bin(m,x) ≤ j] ≤ P[Bin(card ι - ℓ, a) ≤ j - ℓ]` with `ℓ + (card ι - ℓ) a = m x`. -/
theorem exists_shift_binomTail_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {m : ℕ}
    (hm : m ≤ Fintype.card ι) {j : ℕ} (hj : (j : ℝ) < m * x) :
    ∃ (ℓ : ℕ) (a : ℝ), ℓ ≤ j ∧ 0 < a ∧ a < 1 ∧
      (ℓ : ℝ) + ((Fintype.card ι - ℓ : ℕ) : ℝ) * a = m * x ∧
      binomTail m x (j + 1) ≤ binomTail (Fintype.card ι - ℓ) a (j + 1 - ℓ) := by
  classical
  -- the padded binomial
  obtain ⟨s, -, hs⟩ := exists_subset_card_eq (s := (univ : Finset ι)) (n := m) (by
    rw [card_univ]; exact hm)
  set q₀ : ι → ℝ := fun i => if i ∈ s then x else 0 with hq₀
  have h₀ : IsThreeValued q₀ ∅ (univ \ s) x := by
    refine ⟨fun i hi => absurd hi (notMem_empty i), fun i hi => ?_, fun i _ hi => ?_,
      disjoint_empty_left _⟩
    · show (if i ∈ s then x else 0) = 0
      rw [if_neg (mem_sdiff.mp hi).2]
    · show (if i ∈ s then x else 0) = x
      rw [mem_sdiff, not_and, not_not] at hi
      rw [if_pos (hi (mem_univ i))]
  have hcompl : univ \ (∅ ∪ (univ \ s)) = s := by
    rw [empty_union, Finset.sdiff_sdiff_eq_self (subset_univ s)]
  have hsum₀ : ∑ i, q₀ i = m * x := by
    rw [h₀.sum, hcompl, hs, card_empty]; push_cast; ring
  have hIcc₀ : ∀ i, q₀ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i; simp only [hq₀]; split_ifs <;> constructor <;> linarith
  have hP₀ : probLE q₀ j = binomTail m x (j + 1) := by
    rw [h₀.probLE, hcompl, hs, card_empty, Nat.sub_zero]
  -- positivity of the binomial tail
  have hpos : 0 < binomTail m x (j + 1) := by
    rw [binomTail]
    refine lt_of_lt_of_le ?_ (single_le_sum (fun k _ => binom_nonneg hx0.le hx1.le k)
      (mem_range.mpr (Nat.succ_pos j)))
    rw [binom_zero]
    have : 0 < 1 - x := by linarith
    positivity
  -- Hoeffding's maximiser
  have hmx0 : (0 : ℝ) ≤ m * x := by positivity
  have hmxn : (m : ℝ) * x ≤ Fintype.card ι := by
    calc (m : ℝ) * x ≤ m * 1 := by gcongr
      _ = m := mul_one _
      _ ≤ Fintype.card ι := by exact_mod_cast hm
  obtain ⟨q, hqIcc, hqsum, ⟨a, ha0, ha1, h3v⟩, hmax⟩ :=
    exists_max_three_valued (fun m => if m ≤ j then (1 : ℝ) else 0) (m * x) hmx0 hmxn
  set O := univ.filter fun i => q i = 1 with hO
  set Z := univ.filter fun i => q i = 0 with hZ
  have h : IsThreeValued q O Z a := by
    refine ⟨fun i hi => (mem_filter.mp hi).2, fun i hi => (mem_filter.mp hi).2,
      fun i hiO hiZ => ?_, ?_⟩
    · rcases h3v i with h1 | h1 | h1
      · have : i ∈ Z := mem_filter.mpr ⟨mem_univ i, h1⟩
        exact absurd this hiZ
      · exact h1
      · have : i ∈ O := mem_filter.mpr ⟨mem_univ i, h1⟩
        exact absurd this hiO
    · rw [disjoint_left]
      intro i hi hi'
      have := (mem_filter.mp hi).2
      have := (mem_filter.mp hi').2
      linarith
  obtain ⟨t, ht⟩ : ∃ t, t = (univ \ (O ∪ Z)).card := ⟨_, rfl⟩
  have hle : binomTail m x (j + 1) ≤ probLE q j := by
    have := hmax q₀ hIcc₀ hsum₀
    rwa [expect_indicator_le, expect_indicator_le, hP₀] at this
  rw [h.probLE, ← ht] at hle
  have hmean : (O.card : ℝ) + (t : ℝ) * a = m * x := by rw [ht, ← h.sum, hqsum]
  -- `ℓ ≤ j`
  have hℓ : O.card ≤ j := by
    by_contra hcon
    rw [Nat.sub_eq_zero_of_le (by omega)] at hle
    have h0 : binomTail t a 0 = 0 := by simp [binomTail]
    linarith
  -- `t ≥ 1`
  have ht1 : 1 ≤ t := by
    by_contra hcon
    have ht0 : t = 0 := by omega
    rw [ht0] at hmean
    push_cast at hmean
    have : (O.card : ℝ) ≤ j := by exact_mod_cast hℓ
    linarith
  -- no zeros: otherwise the split increases the tail
  have hZ0 : Z = ∅ := by
    by_contra hne
    obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hne
    obtain ⟨j', hj'⟩ : (univ \ (O ∪ Z)).Nonempty := card_pos.mp (by omega)
    have hj'' : j' ∉ O ∪ Z := (mem_sdiff.mp hj').2
    have hsplit := probLE_split h hi hj'' hℓ
    rw [← ht] at hsplit
    -- the split vector is admissible
    set q' := Function.update (Function.update q i (a / 2)) j' (a / 2) with hq'
    have hq'Icc : ∀ k, q' k ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      simp only [hq', Function.update_apply]
      split_ifs
      · constructor <;> linarith
      · constructor <;> linarith
      · exact hqIcc k
    have hq'sum : ∑ k, q' k = m * x := by
      rw [hq', sum_update_pair q (fun h' => hj'' (mem_union.mpr (Or.inr (by rw [← h']; exact hi)))),
        hqsum, h.2.1 i hi, h.2.2.1 j' (fun h' => hj'' (mem_union.mpr (Or.inl h')))
          (fun h' => hj'' (mem_union.mpr (Or.inr h')))]
      ring
    have hmax' := hmax q' hq'Icc hq'sum
    rw [expect_indicator_le, expect_indicator_le, hsplit] at hmax'
    -- the coefficient is positive
    obtain ⟨K, hK⟩ : ∃ K, K = j - O.card := ⟨_, rfl⟩
    rw [← hK] at hmax'
    have hKt : (K : ℝ) < t * a := by
      have : (K : ℝ) = j - O.card := by rw [hK]; push_cast [hℓ]; ring
      linarith
    have hKt' : K < t := by
      have : (t : ℝ) * a < t := by
        have : (0 : ℝ) < t := by exact_mod_cast ht1
        nlinarith
      exact_mod_cast (lt_trans hKt this)
    have hcoef : 0 < binom (t - 1) a K - if 1 ≤ K then binom (t - 1) a (K - 1) else 0 := by
      by_cases hK1 : 1 ≤ K
      · rw [if_pos hK1]
        have hid := binom_succ_mul hK1 hKt'.le a
        have hb : 0 < binom (t - 1) a (K - 1) := binom_pos ha0 ha1 (by omega)
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
        have h1a : 0 < 1 - a := by linarith
        have hlin : (K : ℝ) * (1 - a) < ((t : ℝ) - K) * a := by
          have : ((t : ℝ) - K) * a - K * (1 - a) = t * a - K := by ring
          linarith
        have h3 : (K : ℝ) * (1 - a) * binom (t - 1) a (K - 1) <
            K * (1 - a) * binom (t - 1) a K := by
          rw [hid]
          exact mul_lt_mul_of_pos_right hlin hb
        exact sub_pos.mpr (lt_of_mul_lt_mul_left h3 (mul_pos hK0 h1a).le)
      · rw [if_neg hK1]
        rw [sub_zero]
        exact binom_pos ha0 ha1 (by omega)
    have : 0 < a ^ 2 / 4 * (binom (t - 1) a K - if 1 ≤ K then binom (t - 1) a (K - 1) else 0) :=
      by positivity
    linarith
  -- conclude
  have htcard : t = Fintype.card ι - O.card := by
    rw [ht, hZ0, union_empty, card_univ_sdiff]
  refine ⟨O.card, a, hℓ, ha0, ha1, ?_, ?_⟩
  · rw [← htcard]; exact hmean
  · rw [← htcard]; exact hle

/-! ### The point-mass limit

`Bin(M, λ/M)` at a fixed index tends to `Poi(λ)`, with `M` an independent size.  The
falling-factorial identity `cast_choose_mul_pow` isolates the three factors: a finite product
tending to `1`, the exponential limit `(1 + (−λ)/M)^M → e^{−λ}`, and `(1 − λ/M)^i → 1`.
No convergence of distributions is used. -/

open Filter Topology

/-- **The point-mass limit**: `C(M,i) (λ/M)^i (1 − λ/M)^{M−i} → e^{−λ} λ^i / i!`. -/
theorem binom_tendsto_poi (lam : ℝ) (i : ℕ) :
    Tendsto (fun M : ℕ => binom M (lam / M) i) atTop (𝓝 (poi lam i)) := by
  have hdiv : Tendsto (fun M : ℕ => lam / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat lam
  -- the finite product of the falling factors
  have hP : Tendsto (fun M : ℕ => ∏ r ∈ Icc 1 (i - 1), (1 - (r : ℝ) / M)) atTop (𝓝 1) := by
    have h1 : (1 : ℝ) = ∏ _r ∈ Icc 1 (i - 1), (1 : ℝ) := by simp
    rw [h1]
    refine tendsto_finsetProd _ fun r _ => ?_
    have := tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
    simpa using tendsto_const_nhds.sub this
  -- the exponential limit
  have hE : Tendsto (fun M : ℕ => (1 - lam / M) ^ M) atTop (𝓝 (Real.exp (-lam))) := by
    refine (Real.tendsto_one_add_div_pow_exp (-lam)).congr fun M => ?_
    congr 1
    ring
  -- the fixed power
  have hbase : Tendsto (fun M : ℕ => 1 - lam / M) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hdiv
  have hI : Tendsto (fun M : ℕ => (1 - lam / M) ^ i) atTop (𝓝 1) := by
    simpa using hbase.pow i
  have hlim : Tendsto (fun M : ℕ => lam ^ i / (i.factorial : ℝ) *
      (∏ r ∈ Icc 1 (i - 1), (1 - (r : ℝ) / M)) * ((1 - lam / M) ^ M / (1 - lam / M) ^ i))
      atTop (𝓝 (lam ^ i / (i.factorial : ℝ) * 1 * (Real.exp (-lam) / 1))) :=
    ((tendsto_const_nhds (x := lam ^ i / (i.factorial : ℝ))).mul hP).mul
      (hE.div hI one_ne_zero)
  have hval : lam ^ i / (i.factorial : ℝ) * 1 * (Real.exp (-lam) / 1) = poi lam i := by
    rw [poi]; ring
  rw [hval] at hlim
  -- the two agree once `M` is large
  refine hlim.congr' ?_
  have hM1 : ∀ᶠ M : ℕ in atTop, i + 1 ≤ M := eventually_atTop.mpr ⟨i + 1, fun M h => h⟩
  have hM2 : ∀ᶠ M : ℕ in atTop, lam < M :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop lam
  have hM3 : ∀ᶠ M : ℕ in atTop, -lam < M :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (-lam)
  filter_upwards [hM1, hM2, hM3] with M hiM hlamM hlamM'
  have hM0 : 0 < M := by omega
  have hM0R : (0 : ℝ) < M := by exact_mod_cast hM0
  have hbase0 : 1 - lam / M ≠ 0 := by
    have : lam / M < 1 := (div_lt_one hM0R).mpr hlamM
    intro h
    rw [sub_eq_zero] at h
    exact absurd h.symm (ne_of_lt this)
  have hiM' : i ≤ M := by omega
  have hsplit : (1 - lam / M) ^ (M - i) = (1 - lam / M) ^ M / (1 - lam / M) ^ i := by
    rw [eq_div_iff (pow_ne_zero i hbase0), ← pow_add]
    congr 1
    omega
  rw [binom, hsplit, cast_choose_mul_pow M i hiM' hM0 lam]

/-- The finite lower tail of `Bin(M, λ/M)` tends to the Poisson tail. -/
theorem binomTail_tendsto_poi (lam : ℝ) (n : ℕ) :
    Tendsto (fun M : ℕ => binomTail M (lam / M) n) atTop (𝓝 (∑ i ∈ range n, poi lam i)) :=
  tendsto_finsetSum _ fun i _ => binom_tendsto_poi lam i

/-! ### The comparison -/

/-- **The binomial lower tail below the mean is dominated by a shifted Poisson tail**, for
every integer threshold `j < m x` — no upper clause on `j` is needed.  The finite bound
`exists_shift_binomTail_le` is applied on `Fin (m + n)` for every `n`, and the finitely many
shifts are separated by an argmax argument, so no limit of maxima is formed. -/
theorem exists_shift_binomTail_le_poisson {m : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {j : ℕ} (hj : (j : ℝ) < m * x) :
    ∃ a : ℕ, a ≤ j ∧
      binomTail m x (j + 1) ≤ ∑ i ∈ range (j + 1 - a), poi ((m : ℝ) * x - a) i := by
  classical
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [Nat.cast_zero, zero_mul] at hj
      linarith
    · exact h
  have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
  have hjm : j < m := by
    have : (j : ℝ) < m := by nlinarith
    exact_mod_cast this
  -- the padded bound, for every extra size `n`
  have hfin : ∀ n : ℕ, ∃ s ∈ range (j + 1), binomTail m x (j + 1) ≤
      binomTail ((m - s) + n) (((m : ℝ) * x - s) / (((m - s) + n : ℕ) : ℝ)) (j + 1 - s) := by
    intro n
    obtain ⟨s, a, hsj, ha0, ha1, hmean, hble⟩ :=
      exists_shift_binomTail_le (ι := Fin (m + n)) hx0 hx1
        (by rw [Fintype.card_fin]; omega) hj
    rw [Fintype.card_fin, show m + n - s = (m - s) + n from by omega] at hmean hble
    have hpos : (0 : ℝ) < (((m - s) + n : ℕ) : ℝ) := by
      have : 0 < (m - s) + n := by omega
      exact_mod_cast this
    have ha : a = ((m : ℝ) * x - s) / (((m - s) + n : ℕ) : ℝ) := by
      rw [eq_div_iff (ne_of_gt hpos)]
      linarith [hmean]
    refine ⟨s, mem_range.mpr (by omega), ?_⟩
    rw [← ha]
    exact hble
  -- each shift converges
  have hBlim : ∀ s : ℕ, Tendsto (fun n : ℕ => binomTail ((m - s) + n)
      (((m : ℝ) * x - s) / (((m - s) + n : ℕ) : ℝ)) (j + 1 - s)) atTop
      (𝓝 (∑ i ∈ range (j + 1 - s), poi ((m : ℝ) * x - s) i)) := by
    intro s
    have hcomp : Tendsto (fun n : ℕ => (m - s) + n) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_left n (m - s)) tendsto_id
    have := (binomTail_tendsto_poi ((m : ℝ) * x - s) (j + 1 - s)).comp hcomp
    simpa [Function.comp_def] using this
  -- the argmax over the finitely many shifts
  obtain ⟨a, ha, hamax⟩ := exists_max_image (range (j + 1))
    (fun s => ∑ i ∈ range (j + 1 - s), poi ((m : ℝ) * x - s) i)
    ⟨j, mem_range.mpr (Nat.lt_succ_self j)⟩
  refine ⟨a, by have := mem_range.mp ha; omega, ?_⟩
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ n in atTop, ∀ s ∈ range (j + 1),
      binomTail ((m - s) + n) (((m : ℝ) * x - s) / (((m - s) + n : ℕ) : ℝ)) (j + 1 - s)
        < binomTail m x (j + 1) := by
    rw [eventually_all_finset]
    intro s hs
    exact (hBlim s).eventually_lt_const (lt_of_le_of_lt (hamax s hs) hcon)
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨s, hs, hsle⟩ := hfin n
  exact absurd hsle (not_le.mpr (hn s hs))

set_option linter.unusedVariables false in
/-- **The box, verbatim** ([Hoe56, Theorem 4] with the binomial→Poisson limit).  The upper
clause `hjUpper` is not needed and is ignored. -/
theorem _root_.TSPGap.binomial_lowerTail_le_shifted_poisson {m : ℕ} {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) {j : ℕ} (hj : (j : ℝ) < m * x)
    (hjUpper : (m : ℝ) * x ≤ j + 1) :
    ∃ a : ℕ, a ≤ j ∧
      ∑ i ∈ Finset.range (j + 1),
          (m.choose i : ℝ) * x ^ i * (1 - x) ^ (m - i)
        ≤ ∑ i ∈ Finset.range (j + 1 - a),
            Real.exp (-((m : ℝ) * x - a)) * ((m : ℝ) * x - a) ^ i
              / i.factorial := by
  clear hjUpper
  obtain ⟨a, ha, hle⟩ := exists_shift_binomTail_le_poisson hx0 hx1 hj
  exact ⟨a, ha, by simpa [binomTail, binom, poi] using hle⟩

end Bernoulli
end TSPGap

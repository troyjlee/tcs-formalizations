/-
# The bridge in the other direction

`Sunflower.Bridge` transports a `p`-biased bound to the fixed-size model
(`fixedCount_le_two_mul_pBiased`), which is what the Janson chain consumes. Theorem 1.9 needs
the converse: the width-schedule iteration produces a bound on `failCount X σ m₀` — a count of
*`m₀`-element* subsets — while `IsSatisfying` (Definition 1.5) asks about a `p`-biased set.

Conditioning on `|R|` gives, for a **decreasing** event `P`,

  `Pr_p[P] ≤ f(m₀) + Pr_p[|R| < m₀]`,   `f(m) = fixedCount X P m / C(|X|, m)`,

since `f` is antitone in `m` (`Bridge.fixedCount_antitone_mul`) and `f ≤ 1` below `m₀`. So the
converse costs exactly one thing the development did not have: a **lower tail** for `|R|`.
`Bridge`'s Markov bound is the wrong direction — it controls `Pr[|R| > m₀]`, and Markov says
nothing about a variable falling below its mean.

This file supplies the missing estimate at the cheapest honest strength, Chebyshev:

* `expected_card_sq`, `variance_card` — the exact second moment, `E|R|² = p²n² + p(1−p)n`, by
  the same double count over `X × X` that `Bridge.expected_card` does over `X`
  (`pBiased_mem` on the diagonal, `pBiased_mem_pair` off it);
* `pBiased_card_lt_le` — `Pr[|R| < m₀]·(pn − m₀)² ≤ p(1−p)n`, hence `≤ 4/(pn)` at `2m₀ ≤ pn`;
* `pBiased_le_fixedCount_add_tail` and `pBiased_le_fixedCount_add_chebyshev` — the bridge
  itself, division-free.

Chebyshev rather than Chernoff is deliberate, and it suffices: ALWZ's Corollary 2.9 replaces
the ground set by a much larger one before sampling, and enlarging `X` is free here
(`pBiased_marginal_sdiff`: dummy elements outside every member do not change the probability,
and `IsSpread` never mentions the ground set). Once `p·|X| ≳ 1/β` the `4/(p|X|)` tail is below
`β`, with no exponential inequality anywhere.
-/
import Sunflower.Bridge
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset

set_option maxHeartbeats 800000

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## The second moment of `|R|` -/

/-- `E|R|² = p²·n² + p(1−p)·n`, by double counting over `X × X`: the diagonal contributes
`Pr[i ∈ R] = p` and the off-diagonal `Pr[i, j ∈ R] = p²`. -/
lemma expected_card_sq (X : Finset α) (p : ℝ) :
    ∑ R ∈ X.powerset, wt X p R * ((R.card : ℝ)) ^ 2
      = p ^ 2 * (X.card : ℝ) ^ 2 + p * (1 - p) * (X.card : ℝ) := by
  classical
  -- `|R|² = ∑_{i,j} 1_{i ∈ R} 1_{j ∈ R}`
  have hsq : ∀ R ∈ X.powerset, ((R.card : ℝ)) ^ 2
      = ∑ i ∈ X, ∑ j ∈ X, (if i ∈ R then (1 : ℝ) else 0) * (if j ∈ R then (1 : ℝ) else 0) := by
    intro R hR
    rw [Finset.mem_powerset] at hR
    have hcard : (R.card : ℝ) = ∑ i ∈ X, (if i ∈ R then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hR]
    rw [sq, hcard, Finset.sum_mul_sum]
  -- swap the sums
  have hswap : ∑ R ∈ X.powerset, wt X p R * ((R.card : ℝ)) ^ 2
      = ∑ i ∈ X, ∑ j ∈ X,
          ∑ R ∈ X.powerset, wt X p R
            * ((if i ∈ R then (1 : ℝ) else 0) * (if j ∈ R then (1 : ℝ) else 0)) := by
    rw [Finset.sum_congr rfl fun R hR => by rw [hsq R hR, Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun R _ => Finset.mul_sum _ _ _, Finset.sum_comm]
  rw [hswap]
  -- each inner sum is `Pr[i ∈ R ∧ j ∈ R]`
  have hpair : ∀ i ∈ X, ∀ j ∈ X,
      ∑ R ∈ X.powerset, wt X p R
          * ((if i ∈ R then (1 : ℝ) else 0) * (if j ∈ R then (1 : ℝ) else 0))
        = if i = j then p else p ^ 2 := by
    intro i hi j hj
    have hrw : ∑ R ∈ X.powerset, wt X p R
        * ((if i ∈ R then (1 : ℝ) else 0) * (if j ∈ R then (1 : ℝ) else 0))
        = pBiased X p (fun R => i ∈ R ∧ j ∈ R) := by
      rw [pBiased_eq_sum_wt]
      refine Finset.sum_congr rfl fun R _ => ?_
      by_cases h1 : i ∈ R <;> by_cases h2 : j ∈ R <;> simp [h1, h2]
    rw [hrw]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [pBiased_congr X p (P := fun R => i ∈ R ∧ i ∈ R) (Q := fun R => i ∈ R)
        fun R => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩]
      exact pBiased_mem hi p
    · rw [if_neg hij]
      exact pBiased_mem_pair hi hj hij p
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hpair i hi j hj]
  -- `∑_{i,j} (p or p²) = n·p + (n² − n)·p²`
  have hsplit : ∀ i j : α, (if i = j then p else p ^ 2)
      = p ^ 2 + (if i = j then p - p ^ 2 else 0) := by
    intro i j
    by_cases h : i = j <;> simp [h]
  calc ∑ i ∈ X, ∑ j ∈ X, (if i = j then p else p ^ 2)
      = ∑ i ∈ X, ∑ j ∈ X, (p ^ 2 + (if i = j then p - p ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = ∑ i ∈ X, ((X.card : ℝ) * p ^ 2 + (p - p ^ 2)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_ite_eq X i (fun _ => p - p ^ 2), if_pos hi]
    _ = (X.card : ℝ) * ((X.card : ℝ) * p ^ 2 + (p - p ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = p ^ 2 * (X.card : ℝ) ^ 2 + p * (1 - p) * (X.card : ℝ) := by ring

/-- `Var|R| = p(1−p)·n`, exactly. -/
lemma variance_card (X : Finset α) (p : ℝ) :
    ∑ R ∈ X.powerset, wt X p R * ((p * X.card) - (R.card : ℝ)) ^ 2
      = p * (1 - p) * (X.card : ℝ) := by
  classical
  have hexp : ∀ R ∈ X.powerset, wt X p R * ((p * X.card) - (R.card : ℝ)) ^ 2
      = (p * X.card) ^ 2 * wt X p R - 2 * (p * X.card) * (wt X p R * (R.card : ℝ))
        + wt X p R * ((R.card : ℝ)) ^ 2 := by
    intro R _
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_wt, expected_card, expected_card_sq]
  ring

/-! ## Chebyshev: the lower tail -/

/-- **Chebyshev for `|R|`**: `Pr[|R| < m₀]·(p·n − m₀)² ≤ p(1−p)·n`. -/
theorem pBiased_card_lt_le (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m₀ : ℕ}
    (hm₀ : (m₀ : ℝ) ≤ p * X.card) :
    pBiased X p (fun R => R.card < m₀) * (p * X.card - m₀) ^ 2
      ≤ p * (1 - p) * (X.card : ℝ) := by
  classical
  rw [pBiased_eq_sum_wt, Finset.sum_mul, ← variance_card X p]
  refine Finset.sum_le_sum fun R _ => ?_
  by_cases h : R.card < m₀
  · rw [if_pos h, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg hp0 hp1 R)
    have h1 : (R.card : ℝ) < m₀ := by exact_mod_cast h
    nlinarith [h1, hm₀]
  · rw [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (wt_nonneg hp0 hp1 R) (sq_nonneg _)

/-- The tail in the form the bridge uses: at `2m₀ ≤ p·n`, `Pr[|R| < m₀] ≤ 4/(p·n)`. -/
theorem pBiased_card_lt_le_four_div (X : Finset α) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {m₀ : ℕ} (hm₀ : 2 * (m₀ : ℝ) ≤ p * X.card) (hX : 0 < X.card) :
    pBiased X p (fun R => R.card < m₀) ≤ 4 / (p * (X.card : ℝ)) := by
  have hXR : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX
  have hpn : (0 : ℝ) < p * (X.card : ℝ) := by positivity
  have hm₀' : (m₀ : ℝ) ≤ p * X.card := by
    have : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hcheb := pBiased_card_lt_le X hp0.le hp1 hm₀'
  have hnn : 0 ≤ pBiased X p (fun R => R.card < m₀) := by
    rw [pBiased_eq_sum_wt]
    refine Finset.sum_nonneg fun R _ => ?_
    by_cases h : R.card < m₀
    · rw [if_pos h, mul_one]; exact wt_nonneg hp0.le hp1 R
    · rw [if_neg h, mul_zero]
  -- `(pn − m₀)² ≥ (pn/2)²`
  have hhalf : (p * (X.card : ℝ) / 2) ^ 2 ≤ (p * X.card - m₀) ^ 2 := by
    have h1 : p * (X.card : ℝ) / 2 ≤ p * X.card - m₀ := by linarith
    have h2 : (0 : ℝ) ≤ p * (X.card : ℝ) / 2 := by positivity
    nlinarith [h1, h2]
  rw [le_div_iff₀ hpn]
  nlinarith [hcheb, hnn, hhalf, hpn, hp0, hp1]

/-! ## Chernoff: the lower tail, exponentially

Chebyshev needs `p·|X| ≳ 1/β`, which forces the ground-set enlargement. The exponential bound
needs only `p·|X| ≳ log(1/β)`, which the spread hypothesis already supplies (`κ ≤ |X|`), so it
removes the enlargement from the path entirely. It costs one identity: the moment generating
function of `|R|` is `(pz + 1 − p)^{|X|}`, by the same `Finset.prod_add` that makes the weights
sum to `1` (`sum_pBiasedWeight`). -/

/-- **The moment generating function of `|R|`**: `E z^{|R|} = (p·z + 1 − p)^{|X|}`. -/
lemma mgf_card (X : Finset α) (p z : ℝ) :
    ∑ R ∈ X.powerset, wt X p R * z ^ R.card = (p * z + (1 - p)) ^ X.card := by
  classical
  have h := Finset.prod_add (fun _ : α => p * z) (fun _ : α => 1 - p) X
  simp only [Finset.prod_const] at h
  rw [h]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hRX : R ⊆ X := Finset.mem_powerset.mp hR
  rw [wt_of_subset hRX, Finset.card_sdiff_of_subset hRX, mul_pow]
  ring

/-- **Chernoff's lower tail, MGF form**: for `0 < z ≤ 1`,
`Pr[|R| < m₀]·z^{m₀} ≤ (p·z + 1 − p)^{|X|}`. -/
theorem pBiased_card_lt_mul_pow_le (X : Finset α) {p z : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hz0 : 0 < z) (hz1 : z ≤ 1) (m₀ : ℕ) :
    pBiased X p (fun R => R.card < m₀) * z ^ m₀ ≤ (p * z + (1 - p)) ^ X.card := by
  classical
  rw [pBiased_eq_sum_wt, ← mgf_card X p z, Finset.sum_mul]
  refine Finset.sum_le_sum fun R _ => ?_
  by_cases h : R.card < m₀
  · rw [if_pos h, mul_one]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hz0.le hz1 h.le)
      (wt_nonneg hp0 hp1 R)
  · rw [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (wt_nonneg hp0 hp1 R) (by positivity)

/-- **The lower tail, exponentially.** At `z = 1/2`:
`Pr[|R| < m₀] ≤ exp(m₀·log 2 − p·|X|/2)`.

So `m₀ ≤ p·|X|/4` already gives `exp(−p·|X|/8)`: exponentially small in `p·|X|`, where
Chebyshev gives only `4/(p·|X|)`. -/
theorem pBiased_card_lt_le_exp (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m₀ : ℕ) :
    pBiased X p (fun R => R.card < m₀)
      ≤ Real.exp ((m₀ : ℝ) * Real.log 2 - p * (X.card : ℝ) / 2) := by
  have hmgf := pBiased_card_lt_mul_pow_le X hp0 hp1 (z := 1 / 2) (by norm_num) (by norm_num) m₀
  -- `(1 − p/2)^n ≤ exp(−p·n/2)`
  have hstep : (p * (1 / 2) + (1 - p)) ^ X.card ≤ Real.exp (- (p * (X.card : ℝ) / 2)) := by
    have hbase : p * (1 / 2) + (1 - p) = 1 + (- (p / 2)) := by ring
    have hle : (1 : ℝ) + (- (p / 2)) ≤ Real.exp (- (p / 2)) := Real.add_one_le_exp _ |>.trans_eq' (by ring)
    have hnn : (0 : ℝ) ≤ 1 + (- (p / 2)) := by linarith
    calc (p * (1 / 2) + (1 - p)) ^ X.card = (1 + (- (p / 2))) ^ X.card := by rw [hbase]
      _ ≤ (Real.exp (- (p / 2))) ^ X.card := pow_le_pow_left₀ hnn hle _
      _ = Real.exp (- (p / 2) * X.card) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = Real.exp (- (p * (X.card : ℝ) / 2)) := by ring_nf
  -- divide by `(1/2)^{m₀}`
  have hpow : ((1 : ℝ) / 2) ^ m₀ = Real.exp (- ((m₀ : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [one_div, inv_pow]
  have hpos : (0 : ℝ) < ((1 : ℝ) / 2) ^ m₀ := by positivity
  rw [← le_div_iff₀ hpos] at hmgf
  refine le_trans hmgf ?_
  rw [div_le_iff₀ hpos, hpow, ← Real.exp_add]
  refine le_trans hstep (Real.exp_le_exp.mpr ?_)
  linarith

/-! ## The reverse bridge -/

omit [DecidableEq α] in
/-- The count of "small" sets in a layer (strict version of `Bridge.fixedCount_card_le`). -/
lemma fixedCount_card_lt (X : Finset α) (m₀ m : ℕ) :
    fixedCount X (fun R => R.card < m₀) m = if m < m₀ then X.card.choose m else 0 := by
  classical
  rw [fixedCount]
  by_cases h : m < m₀
  · rw [if_pos h, Finset.filter_true_of_mem, Finset.card_powersetCard]
    exact fun R hR => (Finset.mem_powersetCard.mp hR).2 ▸ h
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun R hR => by rw [(Finset.mem_powersetCard.mp hR).2]; exact h

/-- The layer weights sum to `1`. -/
lemma sum_layer_weights (X : Finset α) (p : ℝ) :
    ∑ m ∈ Finset.range (X.card + 1),
        (X.card.choose m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m)) = 1 := by
  classical
  have h1 := pBiased_eq_sum_layers X p (fun _ => True)
  have h2 : pBiased X p (fun _ => True) = 1 := by
    rw [pBiased_eq_sum_wt]
    simpa using sum_wt X p
  have h3 : ∀ m, fixedCount X (fun _ => True) m = X.card.choose m := by
    intro m
    rw [fixedCount, Finset.filter_true_of_mem fun _ _ => trivial, Finset.card_powersetCard]
  calc ∑ m ∈ Finset.range (X.card + 1),
        (X.card.choose m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m))
      = ∑ m ∈ Finset.range (X.card + 1),
          (fixedCount X (fun _ => True) m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m)) :=
        Finset.sum_congr rfl fun m _ => by rw [h3 m]
    _ = pBiased X p (fun _ => True) := h1.symm
    _ = 1 := h2

/-- **The reverse bridge.** For a decreasing event `P`,

`Pr_p[P] · C(n, m₀) ≤ fixedCount X P m₀ + Pr_p[|R| < m₀] · C(n, m₀)`,

i.e. the `p`-biased probability is at most the fixed-size probability at `m₀` plus the lower
tail. Below `m₀` the layer is bounded by `1`; at and above it, antitonicity of the fixed-size
probability applies and the layer weights sum to at most `1`. -/
theorem pBiased_le_fixedCount_add_tail {X : Finset α} {P : Finset α → Prop} [DecidablePred P]
    (hP : Decreasing P) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m₀ : ℕ} (_hm₀n : m₀ ≤ X.card) :
    pBiased X p P * (X.card.choose m₀ : ℝ)
      ≤ (fixedCount X P m₀ : ℝ)
        + pBiased X p (fun R => R.card < m₀) * (X.card.choose m₀ : ℝ) := by
  classical
  set n := X.card with hn
  set w : ℕ → ℝ := fun m => p ^ m * (1 - p) ^ (n - m) with hw
  have hwnn : ∀ m, 0 ≤ w m := fun m =>
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  -- termwise bound on each layer
  have key : ∀ m ∈ Finset.range (n + 1),
      (fixedCount X P m : ℝ) * w m * (n.choose m₀ : ℝ)
        ≤ (fixedCount X P m₀ : ℝ) * ((n.choose m : ℝ) * w m)
          + (fixedCount X (fun R => R.card < m₀) m : ℝ) * w m * (n.choose m₀ : ℝ) := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [fixedCount_card_lt]
    by_cases hmm : m < m₀
    · -- below `m₀`: bound the layer by the whole layer
      rw [if_pos hmm]
      have hle : (fixedCount X P m : ℝ) ≤ (n.choose m : ℝ) := by
        have : fixedCount X P m ≤ n.choose m := by
          rw [fixedCount, hn]
          calc ((Finset.powersetCard m X).filter P).card ≤ (Finset.powersetCard m X).card :=
                Finset.card_filter_le _ _
            _ = X.card.choose m := Finset.card_powersetCard m X
        exact_mod_cast this
      have h1 : (fixedCount X P m : ℝ) * w m * (n.choose m₀ : ℝ)
          ≤ (n.choose m : ℝ) * w m * (n.choose m₀ : ℝ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (hwnn m)) ?_
        exact Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (fixedCount X P m₀ : ℝ) * ((n.choose m : ℝ) * w m) := by
        have := hwnn m
        positivity
      linarith
    · -- at or above `m₀`: antitonicity
      rw [if_neg hmm]
      have hmm' : m₀ ≤ m := by omega
      have hanti := fixedCount_antitone_mul hP hmm' (by omega : m ≤ X.card)
      have hcast : (fixedCount X P m : ℝ) * (n.choose m₀ : ℝ)
          ≤ (fixedCount X P m₀ : ℝ) * (n.choose m : ℝ) := by
        rw [hn]; exact_mod_cast hanti
      have h1 : (fixedCount X P m : ℝ) * w m * (n.choose m₀ : ℝ)
          ≤ (fixedCount X P m₀ : ℝ) * ((n.choose m : ℝ) * w m) := by
        calc (fixedCount X P m : ℝ) * w m * (n.choose m₀ : ℝ)
            = ((fixedCount X P m : ℝ) * (n.choose m₀ : ℝ)) * w m := by ring
          _ ≤ ((fixedCount X P m₀ : ℝ) * (n.choose m : ℝ)) * w m :=
              mul_le_mul_of_nonneg_right hcast (hwnn m)
          _ = (fixedCount X P m₀ : ℝ) * ((n.choose m : ℝ) * w m) := by ring
      simp only [Nat.cast_zero, zero_mul]
      linarith
  -- sum the layers
  rw [pBiased_eq_sum_layers X p P, pBiased_eq_sum_layers X p (fun R => R.card < m₀),
    Finset.sum_mul, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : ∑ m ∈ Finset.range (n + 1), ((n.choose m : ℝ) * w m) = 1 := by
    rw [hn, hw]
    exact sum_layer_weights X p
  rw [hsum, mul_one]

/-- **The reverse bridge with the tail discharged by Chebyshev.** For a decreasing event and
`2m₀ ≤ p·n`,

`Pr_p[P]·C(n,m₀) ≤ fixedCount X P m₀ + (4/(p·n))·C(n,m₀)`.

Dividing by `C(n,m₀)`: the `p`-biased probability is at most the fixed-size failure fraction
at `m₀`, plus `4/(p·n)` — which enlarging the ground set makes as small as desired. -/
theorem pBiased_le_fixedCount_add_chebyshev {X : Finset α} {P : Finset α → Prop}
    [DecidablePred P] (hP : Decreasing P) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {m₀ : ℕ}
    (hm₀n : m₀ ≤ X.card) (hm₀ : 2 * (m₀ : ℝ) ≤ p * X.card) (hX : 0 < X.card) :
    pBiased X p P * (X.card.choose m₀ : ℝ)
      ≤ (fixedCount X P m₀ : ℝ) + (4 / (p * (X.card : ℝ))) * (X.card.choose m₀ : ℝ) := by
  have hbridge := pBiased_le_fixedCount_add_tail hP hp0.le hp1 hm₀n
  have htail := mul_le_mul_of_nonneg_right (pBiased_card_lt_le_four_div X hp0 hp1 hm₀ hX)
    (by positivity : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ))
  linarith

end Sunflower

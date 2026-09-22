/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankSequence

/-!
# Log-concavity of the Bernoulli count law

The one anti-concentration input the three-cell route needs:
`p_k · p_{k+2} ≤ p_{k+1}²` for `p = Bernoulli.probCount q`.

The proof is by **convolution**, but not on log-concavity itself, which is
*not* closed under convolution: the sequence `(1,0,0,1)` satisfies every
`a_k a_{k+2} ≤ a_{k+1}²` and its Bernoulli convolution `(1-q, q, 0, 1-q, q)`
does not.  What is closed is the full order-two Pólya-frequency family

`PF2 a : ∀ i ≤ j, a i · a (j+1) ≤ a (i+1) · a j`,

of which log-concavity is the instance `j = i + 1`.  Convolving with
`α + βX` produces the three gaps `α²·(i,j)`, `αβ·(i-1,j+1)`, `β²·(i-1,j-1)`,
and the middle one is the *chain* of `(i-1,j)` and `(i,j-1)` — so the family
closes on itself with no interval-support side condition.

* `PF2`, `SeqNonneg` — the invariant, on plain sequences `ℕ → ℝ`.
* `pf2_convolve` — the closure step, stated through the two recursion
  equations `b 0 = α·a 0` and `b (k+1) = α·a (k+1) + β·a k` so that no
  truncated subtraction appears.
* `coeff_bernoulli_mul_zero` / `_succ` — those equations for the
  coefficients of `(C β · X + C α) · p`.
* `pf2_bernoulli_prod` — the induction over the coordinate set.
* `Bernoulli.probCount_logConcave` — the export, read off the generating
  product through `Bernoulli.probCount_eq_coeff`.
-/

namespace TSPGap

open Polynomial

/-! ### The invariant -/

/-- Nonnegativity of a sequence. -/
def SeqNonneg (a : ℕ → ℝ) : Prop := ∀ k, 0 ≤ a k

/-- The **order-two Pólya-frequency inequalities**: `a i · a (j+1) ≤
a (i+1) · a j` whenever `i ≤ j`.  Unlike bare log-concavity this family is
closed under Bernoulli convolution. -/
def PF2 (a : ℕ → ℝ) : Prop := ∀ i j : ℕ, i ≤ j → a i * a (j + 1) ≤ a (i + 1) * a j

/-- Log-concavity is the diagonal instance `j = i + 1`. -/
theorem PF2.logConcave {a : ℕ → ℝ} (h : PF2 a) (k : ℕ) :
    a k * a (k + 2) ≤ a (k + 1) * a (k + 1) :=
  h k (k + 1) (Nat.le_succ k)

/-! ### Closure under Bernoulli convolution -/

theorem seqNonneg_convolve {a b : ℕ → ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hnn : SeqNonneg a) (hb0 : b 0 = α * a 0)
    (hbs : ∀ k, b (k + 1) = α * a (k + 1) + β * a k) : SeqNonneg b := by
  intro k
  cases k with
  | zero => rw [hb0]; exact mul_nonneg hα (hnn 0)
  | succ k =>
    rw [hbs k]
    exact add_nonneg (mul_nonneg hα (hnn (k + 1))) (mul_nonneg hβ (hnn k))

/-- **The closure step.**  Convolving a nonnegative `PF2` sequence with the
two-point sequence `(α, β)` preserves `PF2`.  The three gaps are the
instances `(i, j)`, `(i-1, j+1)`, `(i-1, j-1)`, and the middle one is the
chain of two others — no interval-support hypothesis is needed. -/
theorem pf2_convolve {a b : ℕ → ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hnn : SeqNonneg a) (hpf : PF2 a) (hb0 : b 0 = α * a 0)
    (hbs : ∀ k, b (k + 1) = α * a (k + 1) + β * a k) : PF2 b := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero =>
      -- `b 0 · b 1 ≤ b 1 · b 0`
      exact le_of_eq (mul_comm _ _)
    | succ j =>
      rw [hb0, hbs (j + 1), hbs 0, hbs j]
      have key := hpf 0 (j + 1) (Nat.zero_le _)
      have t1 : 0 ≤ α * α * (a (0 + 1) * a (j + 1) - a 0 * a (j + 1 + 1)) :=
        mul_nonneg (mul_nonneg hα hα) (by linarith)
      have t2 : 0 ≤ α * β * (a (0 + 1) * a j) :=
        mul_nonneg (mul_nonneg hα hβ) (mul_nonneg (hnn (0 + 1)) (hnn j))
      have t3 : 0 ≤ β * β * (a 0 * a j) :=
        mul_nonneg (mul_nonneg hβ hβ) (mul_nonneg (hnn 0) (hnn j))
      nlinarith [t1, t2, t3]
  | succ i =>
    cases j with
    | zero => omega
    | succ j =>
      rw [hbs i, hbs (j + 1), hbs (i + 1), hbs j]
      have hij' : i ≤ j := by omega
      have f1 := hpf (i + 1) (j + 1) (by omega)
      have f3 := hpf i j hij'
      have f2 : a i * a (j + 1 + 1) ≤ a (i + 1 + 1) * a j := by
        rcases eq_or_lt_of_le hij' with heq | hlt
        · subst heq
          exact le_of_eq (mul_comm _ _)
        · exact le_trans (hpf i (j + 1) (by omega)) (hpf (i + 1) j (by omega))
      have t1 : 0 ≤ α * α * (a (i + 1 + 1) * a (j + 1) - a (i + 1) * a (j + 1 + 1)) :=
        mul_nonneg (mul_nonneg hα hα) (by linarith)
      have t2 : 0 ≤ α * β * (a (i + 1 + 1) * a j - a i * a (j + 1 + 1)) :=
        mul_nonneg (mul_nonneg hα hβ) (by linarith)
      have t3 : 0 ≤ β * β * (a (i + 1) * a j - a i * a (j + 1)) :=
        mul_nonneg (mul_nonneg hβ hβ) (by linarith)
      nlinarith [t1, t2, t3]

/-! ### The coefficient recursion -/

theorem coeff_bernoulli_mul_zero (α β : ℝ) (p : Polynomial ℝ) :
    ((C β * X + C α) * p).coeff 0 = α * p.coeff 0 := by
  rw [add_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
    zero_mul, mul_zero, zero_add]

theorem coeff_bernoulli_mul_succ (α β : ℝ) (p : Polynomial ℝ) (k : ℕ) :
    ((C β * X + C α) * p).coeff (k + 1)
      = α * p.coeff (k + 1) + β * p.coeff k := by
  rw [add_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, add_comm]

/-! ### The Bernoulli generating product -/

/-- The coefficient sequence of `∏ (C qᵢ · X + C (1 - qᵢ))` is nonnegative
and `PF2`, by induction over the coordinate set. -/
theorem pf2_bernoulli_prod {κ : Type*} (q : κ → ℝ) :
    ∀ s : Finset κ, (∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) →
      SeqNonneg (fun k => (∏ i ∈ s, (C (q i) * X + C (1 - q i))).coeff k)
        ∧ PF2 (fun k => (∏ i ∈ s, (C (q i) * X + C (1 - q i))).coeff k) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    constructor
    · intro k
      simp only [Finset.prod_empty, Polynomial.coeff_one]
      split_ifs <;> norm_num
    · intro i j _
      simp [Finset.prod_empty, Polynomial.coeff_one]
  | insert a s ha ih =>
    intro hq
    obtain ⟨hnn, hpf⟩ := ih fun i hi => hq i (Finset.mem_insert_of_mem hi)
    obtain ⟨hq0, hq1⟩ := hq a (Finset.mem_insert_self a s)
    have hb0 : (∏ i ∈ insert a s, (C (q i) * X + C (1 - q i))).coeff 0
        = (1 - q a) * (∏ i ∈ s, (C (q i) * X + C (1 - q i))).coeff 0 := by
      rw [Finset.prod_insert ha]
      exact coeff_bernoulli_mul_zero _ _ _
    have hbs : ∀ k, (∏ i ∈ insert a s, (C (q i) * X + C (1 - q i))).coeff (k + 1)
        = (1 - q a) * (∏ i ∈ s, (C (q i) * X + C (1 - q i))).coeff (k + 1)
          + q a * (∏ i ∈ s, (C (q i) * X + C (1 - q i))).coeff k := by
      intro k
      rw [Finset.prod_insert ha]
      exact coeff_bernoulli_mul_succ _ _ _ _
    exact ⟨seqNonneg_convolve (by linarith) hq0 hnn hb0 hbs,
      pf2_convolve (by linarith) hq0 hnn hpf hb0 hbs⟩

/-! ### The export -/

theorem Bernoulli.pf2_probCount {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : κ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) : PF2 (Bernoulli.probCount q) := by
  have h := (pf2_bernoulli_prod q Finset.univ fun i _ => hq i).2
  intro i j hij
  rw [Bernoulli.probCount_eq_coeff, Bernoulli.probCount_eq_coeff,
    Bernoulli.probCount_eq_coeff, Bernoulli.probCount_eq_coeff]
  exact h i j hij

/-- **The Bernoulli count law is log-concave.** -/
theorem Bernoulli.probCount_logConcave {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : κ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) :
    Bernoulli.probCount q k * Bernoulli.probCount q (k + 2)
      ≤ Bernoulli.probCount q (k + 1) ^ 2 := by
  have h := (Bernoulli.pf2_probCount q hq).logConcave k
  rw [pow_two]
  exact h

end TSPGap

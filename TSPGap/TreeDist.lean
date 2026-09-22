/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic
import Mathlib.Algebra.Order.Star.Real

/-!
# Spanning-tree distributions with prescribed marginals

Everything in the polygon development so far treats the tree as an
arbitrary edge set.  KKO22 Lemma 5.5 is the first statement that needs it
to be *random*: it bounds the probability of a bad event by `4.5η`, via
`P[E→(L)_T = 1] ≥ 1 − 2.5η` (their Corollary 2.12) together with
`P[E∘(L)_T = 0] ≥ 1 − 2η`, which follows from `x(E∘(L)) ≤ 2η` by Markov.

This file provides the minimal interface for that: a finitely-supported
distribution on spanning trees whose edge marginals are `x`, the expected
number of tree edges in a fixed set, and Markov's inequality.  No measure
theory is involved — the sample space is a `Finset`, so expectations are
finite sums.

The key identity `expectedCard_eq_sum` is the one place the marginal
condition is used: exchanging the order of summation turns "expected
number of tree edges in `F`" into "`x`-mass of `F`".
-/

namespace TSPGap

variable {n : ℕ}

open Classical in
/-- A distribution on spanning trees of the complete graph on `Fin n`
whose edge marginals are `x`. -/
structure TreeDist (n : ℕ) (x : Sym2 (Fin n) → ℝ) where
  /-- The probability mass of a given edge set. -/
  prob : Finset (Sym2 (Fin n)) → ℝ
  prob_nonneg : ∀ T, 0 ≤ prob T
  total : ∑ T : Finset (Sym2 (Fin n)), prob T = 1
  support_spanningTree : ∀ T, prob T ≠ 0 → IsSpanningTree n T
  marginals : ∀ e ∈ edgeFinset n,
    (∑ T ∈ Finset.univ.filter (fun T => e ∈ T), prob T) = x e

namespace TreeDist

variable {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)

/-- The expected number of tree edges lying in `F`. -/
noncomputable def expectedCard (F : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ T : Finset (Sym2 (Fin n)), μ.prob T * (F ∩ T).card

open Classical in
/-- The probability of an event, i.e. of a set of trees. -/
noncomputable def probEvent (Q : Finset (Sym2 (Fin n)) → Prop) : ℝ :=
  ∑ T ∈ Finset.univ.filter Q, μ.prob T

/-- **The marginal identity**: the expected number of tree edges in `F`
is the `x`-mass of `F`.  Exchanging the order of summation turns the
expectation into a sum of marginals. -/
theorem expectedCard_eq_sum {F : Finset (Sym2 (Fin n))}
    (hF : F ⊆ edgeFinset n) : μ.expectedCard F = ∑ e ∈ F, x e := by
  classical
  have hcard : ∀ T : Finset (Sym2 (Fin n)),
      ((F ∩ T).card : ℝ) = ∑ e ∈ F, if e ∈ T then (1 : ℝ) else 0 := by
    intro T
    have hfil : F ∩ T = F.filter (fun e => e ∈ T) := by
      ext e
      simp [Finset.mem_inter, Finset.mem_filter]
    rw [hfil, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold expectedCard
  rw [Finset.sum_congr rfl fun T _ => by rw [hcard T, Finset.mul_sum],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← μ.marginals e (hF he), Finset.sum_filter]
  exact Finset.sum_congr rfl fun T _ => by
    by_cases h : e ∈ T <;> simp [h]

open Classical in
/-- Indicator form of `probEvent`. -/
theorem probEvent_eq_sum (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.probEvent Q
      = ∑ T : Finset (Sym2 (Fin n)), if Q T then μ.prob T else 0 := by
  rw [probEvent, Finset.sum_filter]

open Classical in
/-- **Markov's inequality**: the probability that the tree meets `F` is at
most the expected number of tree edges in `F`, hence at most `x(F)`.
This is what turns the proved bound `x(E∘(L)) ≤ 2η` into the second input
of Lemma 5.5. -/
theorem probEvent_meets_le_sum {F : Finset (Sym2 (Fin n))}
    (hF : F ⊆ edgeFinset n) :
    μ.probEvent (fun T => (F ∩ T).Nonempty) ≤ ∑ e ∈ F, x e := by
  rw [← μ.expectedCard_eq_sum hF, probEvent_eq_sum]
  unfold expectedCard
  refine Finset.sum_le_sum fun T _ => ?_
  have hp := μ.prob_nonneg T
  by_cases h : (F ∩ T).Nonempty
  · rw [if_pos h]
    have h1c : (1 : ℝ) ≤ ((F ∩ T).card : ℝ) := by
      have := Finset.card_pos.mpr h
      exact_mod_cast this
    nlinarith
  · rw [if_neg h]
    exact mul_nonneg hp (Nat.cast_nonneg _)

open Classical in
/-- Union bound. -/
theorem probEvent_or_le (Q R : Finset (Sym2 (Fin n)) → Prop) :
    μ.probEvent (fun T => Q T ∨ R T) ≤ μ.probEvent Q + μ.probEvent R := by
  rw [probEvent_eq_sum, probEvent_eq_sum, probEvent_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  have hp := μ.prob_nonneg T
  have hQ : (0:ℝ) ≤ if Q T then μ.prob T else 0 := by
    split_ifs
    · exact hp
    · exact le_rfl
  have hR : (0:ℝ) ≤ if R T then μ.prob T else 0 := by
    split_ifs
    · exact hp
    · exact le_rfl
  by_cases hq : Q T
  · rw [if_pos (Or.inl hq), if_pos hq]
    linarith
  · by_cases hr : R T
    · rw [if_pos (Or.inr hr), if_neg hq, if_pos hr]
      linarith
    · rw [if_neg (by tauto : ¬ (Q T ∨ R T))]
      linarith

/-- **KKO22 Lemma 5.5, the union bound.**  A bad event is the disjunction
"the tree does not meet `E→` exactly once, or it meets `E∘` at all", so
its probability is at most the sum of the two — `2.5η + 2η = 4.5η` with
the inputs the paper supplies. -/
theorem prob_badEvent_le {ER EC : Finset (Sym2 (Fin n))} {η : ℝ}
    (h1 : μ.probEvent (fun T => (ER ∩ T).card ≠ 1) ≤ 2.5 * η)
    (h2 : μ.probEvent (fun T => (EC ∩ T).Nonempty) ≤ 2 * η) :
    μ.probEvent (fun T => (ER ∩ T).card ≠ 1 ∨ (EC ∩ T).Nonempty)
      ≤ 4.5 * η := by
  have h := μ.probEvent_or_le (fun T => (ER ∩ T).card ≠ 1)
    (fun T => (EC ∩ T).Nonempty)
  linarith

open Classical in
/-- Complement rule, from total probability. -/
theorem probEvent_not (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.probEvent (fun T => ¬ Q T) = 1 - μ.probEvent Q := by
  have hsum : μ.probEvent Q + μ.probEvent (fun T => ¬ Q T) = 1 := by
    rw [probEvent_eq_sum, probEvent_eq_sum, ← Finset.sum_add_distrib, ← μ.total]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : Q T <;> simp [h]
  linarith

/-- **KKO22 Lemma 5.5.**  The bad event at a polygon point has
probability at most `4.5η`.

The two inputs are Corollary 2.12 — that the tree meets `E→` exactly once
with probability at least `1 − 2.5η` — and the `x`-mass bound
`x(E∘) ≤ 2η`, which Markov converts into `P[E∘ met] ≤ 2η`. -/
theorem prob_badEvent_le_of_mass {ER EC : Finset (Sym2 (Fin n))} {η : ℝ}
    (hcor : 1 - 2.5 * η ≤ μ.probEvent (fun T => (ER ∩ T).card = 1))
    (hEC : EC ⊆ edgeFinset n) (hmass : ∑ e ∈ EC, x e ≤ 2 * η) :
    μ.probEvent (fun T => (ER ∩ T).card ≠ 1 ∨ (EC ∩ T).Nonempty)
      ≤ 4.5 * η := by
  refine μ.prob_badEvent_le ?_ ?_
  · have h := μ.probEvent_not (fun T => (ER ∩ T).card = 1)
    rw [h]
    linarith
  · exact le_trans (μ.probEvent_meets_le_sum hEC) hmass

/-- The expectation of a real-valued function of the tree. -/
noncomputable def expect (f : Finset (Sym2 (Fin n)) → ℝ) : ℝ :=
  ∑ T : Finset (Sym2 (Fin n)), μ.prob T * f T

open Classical in
/-- The expectation of a scaled indicator is the scaled probability. -/
theorem expect_indicator (Q : Finset (Sym2 (Fin n)) → Prop) (c : ℝ) :
    μ.expect (fun T => if Q T then c else 0) = c * μ.probEvent Q := by
  rw [expect, probEvent_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : Q T <;> simp [h, mul_comm]

open Classical in
/-- **Union bound over a finite family.**  The general form of
`probEvent_or_le`, as used in KKO22's proof of Theorem 5.2 to bound the
probability that *any* of the (at most four) bad events touching a given
edge occurs. -/
theorem probEvent_exists_le {ι : Type*} (s : Finset ι)
    (Q : ι → Finset (Sym2 (Fin n)) → Prop) :
    μ.probEvent (fun T => ∃ b ∈ s, Q b T) ≤ ∑ b ∈ s, μ.probEvent (Q b) := by
  rw [probEvent_eq_sum]
  have hb : ∀ b ∈ s, μ.probEvent (Q b)
      = ∑ T : Finset (Sym2 (Fin n)), if Q b T then μ.prob T else 0 :=
    fun b _ => probEvent_eq_sum μ (Q b)
  rw [Finset.sum_congr rfl hb, Finset.sum_comm]
  refine Finset.sum_le_sum fun T _ => ?_
  have hnn : ∀ i ∈ s, (0 : ℝ) ≤ if Q i T then μ.prob T else 0 := by
    intro i _
    by_cases hi : Q i T
    · rw [if_pos hi]; exact μ.prob_nonneg T
    · rw [if_neg hi]
  by_cases h : ∃ b ∈ s, Q b T
  · obtain ⟨b, hbs, hQ⟩ := h
    rw [if_pos ⟨b, hbs, hQ⟩]
    calc μ.prob T = (if Q b T then μ.prob T else 0) := by rw [if_pos hQ]
      _ ≤ ∑ i ∈ s, if Q i T then μ.prob T else 0 :=
          Finset.single_le_sum hnn hbs
  · rw [if_neg h]
    exact Finset.sum_nonneg hnn

end TreeDist

end TSPGap

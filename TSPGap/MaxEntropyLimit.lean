/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OJoin

/-!
# What passes to the max-entropy limit

`OJoin.IsMaxEntropyLimit` says the distribution the payment argument uses is a
pointwise limit of λ-uniform ones.  It has to be: `OJoin.not_isLambdaUniform`
refutes the exact λ-uniform interface over the restricted marginals, the
distinguished edge having marginal zero while a λ-uniform measure gives every
spanning tree positive probability.

This file makes the limit usable.  `IsMaxEntropyLimit.of_closed` asks for a
property closed under pointwise approximation; the observation here is that
**continuity is enough**, and that everything KKO21 take from the max-entropy
distribution is a non-strict inequality between continuous functions of the
probability vector.

The reason continuity suffices is that the sample space is finite: probability
vectors live in `Finset (Sym2 (Fin n)) → ℝ`, a finite product of copies of `ℝ`,
where pointwise `δ`-approximation *is* convergence.  So `limitClosed_le` is
`le_of_tendsto_of_tendsto'` and nothing more.

## Main results

* `LimitClosed` — the hypothesis of `IsMaxEntropyLimit.of_closed`, named; with
  `LimitClosed.and` and `limitClosed_forall`, so that a family of inequalities
  is limit-closed as soon as each member is.
* `limitClosed_le` — a non-strict inequality between continuous functions of
  the probability vector is limit-closed.
* `IsMaxEntropyLimit.expect_le`, `.le_probEvent`, `.expect_mul_le` — the three
  shapes that occur: a bound on an expectation, a lower bound on the
  probability of an event (Corollary 2.12's shape), and negative association.

## What this does *not* settle

⚠️ The machinery here is generic; two adapters to it still contain real
mathematics, and an earlier draft of this docstring wrongly claimed otherwise.

**Real stability is not a coefficient condition.**  A strongly Rayleigh measure
is defined by *nonvanishing of its generating polynomial on the open upper
half-plane*, which does not unfold into non-strict inequalities among the
coefficients.  Getting it into the shape `limitClosed_le` consumes needs either
the Borcea–Brändén–Liggett criterion — for a multi-affine polynomial, stability
is equivalent to the Rayleigh difference `∂ᵢp ∂ⱼp − p ∂ᵢ∂ⱼp` being nonnegative
on `ℝ^ι` — or a Hurwitz/root-continuity argument.  Both are substantial;
`Stable.lean` sets up the definitions and defers the criterion.

**Fact 2.8 must be passed in cross-multiplied form.**  Conditional probabilities
are not continuous where the conditioning event has probability zero, so the
identity to carry to the limit is
`P(A ∩ B ∩ C) · P(C) = P(A ∩ C) · P(B ∩ C)`, which is polynomial in the
probability vector and so covered here — the conditional form is not.
-/

namespace TSPGap

open Finset

variable {n : ℕ}

/-! ### Limit-closed properties -/

/-- A property of the probability vector is **limit-closed** when it survives
pointwise approximation.  This is exactly the hypothesis of
`IsMaxEntropyLimit.of_closed`. -/
def LimitClosed (P : (Finset (Sym2 (Fin n)) → ℝ) → Prop) : Prop :=
  ∀ f : Finset (Sym2 (Fin n)) → ℝ,
    (∀ δ : ℝ, 0 < δ → ∃ g, P g ∧ ∀ T, |g T - f T| ≤ δ) → P f

/-- `IsMaxEntropyLimit.of_closed`, with the hypothesis named. -/
theorem IsMaxEntropyLimit.holds {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) {P : (Finset (Sym2 (Fin n)) → ℝ) → Prop}
    (hP : LimitClosed P)
    (hlam : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν → P ν.prob) :
    P μ.prob :=
  h.of_closed hP hlam

theorem LimitClosed.and {P Q : (Finset (Sym2 (Fin n)) → ℝ) → Prop}
    (hP : LimitClosed P) (hQ : LimitClosed Q) : LimitClosed fun f => P f ∧ Q f := by
  intro f hf
  refine ⟨hP f fun δ hδ => ?_, hQ f fun δ hδ => ?_⟩
  · obtain ⟨g, hg, hclose⟩ := hf δ hδ
    exact ⟨g, hg.1, hclose⟩
  · obtain ⟨g, hg, hclose⟩ := hf δ hδ
    exact ⟨g, hg.2, hclose⟩

/-- A family of limit-closed properties is limit-closed.  This is what lets a
*definition by a family of inequalities* — real stability, for instance — be
passed to the limit one inequality at a time. -/
theorem limitClosed_forall {ι : Sort*} {P : ι → (Finset (Sym2 (Fin n)) → ℝ) → Prop}
    (h : ∀ i, LimitClosed (P i)) : LimitClosed fun f => ∀ i, P i f := by
  intro f hf i
  refine h i f fun δ hδ => ?_
  obtain ⟨g, hg, hclose⟩ := hf δ hδ
  exact ⟨g, hg i, hclose⟩

/-- An implication whose hypothesis is *not* about the probability vector.  The
hypothesis is fixed data — a combinatorial side condition, say — so it simply
rides along.  This is what lets a limit-closed property carry universally
quantified side conditions without their having to be limit-closed themselves. -/
theorem limitClosed_imp {Q : Prop} {P : (Finset (Sym2 (Fin n)) → ℝ) → Prop}
    (h : LimitClosed P) : LimitClosed fun f => Q → P f := by
  intro f hf hQ
  refine h f fun δ hδ => ?_
  obtain ⟨g, hg, hclose⟩ := hf δ hδ
  exact ⟨g, hg hQ, hclose⟩

/-! ### Continuity is enough

The sample space is finite, so the probability vectors form a finite product of
copies of `ℝ` and pointwise approximation is convergence. -/

/-- **Pointwise `1/(k+1)`-approximants converge.** -/
theorem tendsto_of_approx {f : Finset (Sym2 (Fin n)) → ℝ}
    {g : ℕ → Finset (Sym2 (Fin n)) → ℝ}
    (hg : ∀ k T, |g k T - f T| ≤ 1 / (k + 1)) :
    Filter.Tendsto g Filter.atTop (nhds f) := by
  rw [tendsto_pi_nhds]
  intro T
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hε
  refine ⟨k₀, fun k hk => ?_⟩
  have hmono : (1 : ℝ) / (k + 1) ≤ 1 / (k₀ + 1) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  calc dist (g k T) (f T) = |g k T - f T| := Real.dist_eq _ _
    _ ≤ 1 / (k + 1) := hg k T
    _ ≤ 1 / (k₀ + 1) := hmono
    _ < ε := hk₀

/-- **A non-strict inequality between continuous functions is limit-closed.**
This is the whole content of the limit interface: on a finite sample space
there is no topology to set up, and the statement is
`le_of_tendsto_of_tendsto'`. -/
theorem limitClosed_le {F G : (Finset (Sym2 (Fin n)) → ℝ) → ℝ}
    (hF : Continuous F) (hG : Continuous G) : LimitClosed fun f => F f ≤ G f := by
  intro f hf
  choose g hg hclose using fun k : ℕ => hf (1 / (k + 1)) (by positivity)
  have htend := tendsto_of_approx hclose
  exact le_of_tendsto_of_tendsto' ((hF.tendsto f).comp htend)
    ((hG.tendsto f).comp htend) hg

/-- A linear functional of the probability vector is continuous — an
expectation, in particular. -/
theorem continuous_probSum (c : Finset (Sym2 (Fin n)) → ℝ) :
    Continuous fun f : Finset (Sym2 (Fin n)) → ℝ => ∑ T, f T * c T :=
  continuous_finsetSum _ fun T _ => (continuous_apply T).mul continuous_const

open Classical in
/-- The probability of an event is continuous: it is the sum of the vector over
a fixed set of trees. -/
theorem continuous_probEventSum (Q : Finset (Sym2 (Fin n)) → Prop) :
    Continuous fun f : Finset (Sym2 (Fin n)) → ℝ =>
      ∑ T ∈ Finset.univ.filter Q, f T :=
  continuous_finsetSum _ fun T _ => continuous_apply T

/-- **An identity between continuous functions is limit-closed**, being two
non-strict inequalities.  This is the shape a *cross-multiplied* independence
statement takes, and the reason Fact 2.8 has to be cross-multiplied: the
conditional form divides by a quantity that may vanish in the limit. -/
theorem limitClosed_eq {F G : (Finset (Sym2 (Fin n)) → ℝ) → ℝ}
    (hF : Continuous F) (hG : Continuous G) : LimitClosed fun f => F f = G f := by
  intro f hf
  have h1 : F f ≤ G f := by
    refine limitClosed_le hF hG f fun δ hδ => ?_
    obtain ⟨g, hg, hclose⟩ := hf δ hδ
    exact ⟨g, le_of_eq hg, hclose⟩
  have h2 : G f ≤ F f := by
    refine limitClosed_le hG hF f fun δ hδ => ?_
    obtain ⟨g, hg, hclose⟩ := hf δ hδ
    exact ⟨g, le_of_eq hg.symm, hclose⟩
  linarith

/-! ### The three shapes -/

/-- **A bound on an expectation passes to the limit.**  `μ.expect c` is a
linear functional of the probability vector, so this is `limitClosed_le`
against a constant. -/
theorem IsMaxEntropyLimit.expect_le {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) (c : Finset (Sym2 (Fin n)) → ℝ) (b : ℝ)
    (hlam : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν →
      ν.expect c ≤ b) : μ.expect c ≤ b :=
  h.holds (P := fun f => (∑ T, f T * c T) ≤ b)
    (limitClosed_le (continuous_probSum c) continuous_const) fun ν hν => hlam ν hν

open Classical in
/-- **A lower bound on the probability of an event passes to the limit.**  This
is the shape of KKO22 Corollary 2.12, the one probabilistic input Appendix A
and Theorem 5.2 take from the distribution. -/
theorem IsMaxEntropyLimit.le_probEvent {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) (Q : Finset (Sym2 (Fin n)) → Prop) (b : ℝ)
    (hlam : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν →
      b ≤ ν.probEvent Q) : b ≤ μ.probEvent Q :=
  h.holds (P := fun f => b ≤ ∑ T ∈ Finset.univ.filter Q, f T)
    (limitClosed_le continuous_const (continuous_probEventSum Q)) fun ν hν => hlam ν hν

/-- **Negative association passes to the limit.**  Both sides are polynomial in
the probability vector — the right one a product of two linear functionals — so
`limitClosed_le` applies unchanged.  This is the shape KKO21's strongly-Rayleigh
consequences take. -/
theorem IsMaxEntropyLimit.expect_mul_le {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) (A B : Finset (Sym2 (Fin n)) → ℝ)
    (hlam : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν →
      ν.expect (fun T => A T * B T) ≤ ν.expect A * ν.expect B) :
    μ.expect (fun T => A T * B T) ≤ μ.expect A * μ.expect B :=
  h.holds (P := fun f => (∑ T, f T * (A T * B T)) ≤ (∑ T, f T * A T) * (∑ T, f T * B T))
    (limitClosed_le (continuous_probSum _)
      ((continuous_probSum A).mul (continuous_probSum B))) fun ν hν => hlam ν hν

end TSPGap

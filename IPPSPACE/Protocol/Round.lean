/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Operators
import IPPSPACE.Arithmetization.Univariate
import Mathlib.Algebra.Polynomial.Roots

/-!
# One round of the algebraic verifier

The prover sends a univariate polynomial before the verifier chooses a fresh
challenge. The verifier checks its degree and an operator-specific identity
at zero and one, then updates one coordinate and the claimed value.

An honest slice passes the check and preserves a true claim for every challenge.
From a false claim, an arbitrary reply can pass the check and produce a true
next claim on at most `d` challenges in any finite sampling set. Polynomial
messages here are mathematical objects; their encoding is a later obligation.
-/

namespace IPPSPACE

open MvPolynomial

/-- A claim that a polynomial takes a specified value at a specified point. -/
structure EvaluationClaim (R : Type*) where
  point : ℕ → R
  value : R

/-- The coordinate exposed by an operator's round. -/
def AlgebraicOperator.coordinate : AlgebraicOperator → ℕ
  | .reduce i => i
  | .quantify (.ex i) => i
  | .quantify (.all i) => i

variable {R : Type*} [CommRing R]

/-- Compute the current claim from the reply's two Boolean endpoints. -/
def AlgebraicOperator.combine : AlgebraicOperator → (ℕ → R) → R → R → R
  | .reduce i, x, a, b => (1 - x i) * a + x i * b
  | .quantify (.ex _), _, a, b => 1 - (1 - a) * (1 - b)
  | .quantify (.all _), _, a, b => a * b

noncomputable section

open scoped Classical

def EvaluationClaim.IsTrue (c : EvaluationClaim R) (p : MvPolynomial ℕ R) : Prop :=
  c.value = eval c.point p

/-- Both the degree check and the endpoint identity must hold. -/
def AlgebraicOperator.RoundCheck (op : AlgebraicOperator) (d : ℕ)
    (c : EvaluationClaim R) (reply : Polynomial R) : Prop :=
  reply.natDegree ≤ d ∧ op.combine c.point (reply.eval 0) (reply.eval 1) = c.value

/-- Continue to the next polynomial after drawing the challenge `r`. -/
def AlgebraicOperator.advance (op : AlgebraicOperator) (c : EvaluationClaim R)
    (reply : Polynomial R) (r : R) : EvaluationClaim R :=
  ⟨Function.update c.point op.coordinate r, reply.eval r⟩

/-- The endpoint identity is the exact arithmetic meaning of each operator. -/
theorem AlgebraicOperator.combine_univariateSlice (op : AlgebraicOperator)
    (x : ℕ → R) (p : MvPolynomial ℕ R) :
    op.combine x ((univariateSlice x op.coordinate p).eval 0)
      ((univariateSlice x op.coordinate p).eval 1) = eval x (op.act p) := by
  cases op with
  | reduce i => simp [combine, coordinate, act, eval_univariateSlice, eval_linearize]
  | quantify q =>
    cases q <;> simp [combine, coordinate, act, Quantifier.act, eval_univariateSlice, eval_restrict]

/-- An honest reply passes whenever the current claim is true and the degree bound is valid. -/
theorem AlgebraicOperator.roundCheck_honest [Nontrivial R] (op : AlgebraicOperator)
    (d : ℕ) (c : EvaluationClaim R) (p : MvPolynomial ℕ R)
    (hp : p.degreeOf op.coordinate ≤ d) (hc : c.IsTrue (op.act p)) :
    op.RoundCheck d c (univariateSlice c.point op.coordinate p) := by
  refine ⟨(natDegree_univariateSlice_le _ _ _).trans hp, ?_⟩
  exact (op.combine_univariateSlice c.point p).trans hc.symm

/-- Honest replies preserve truth for every challenge, including non-Boolean ones. -/
theorem AlgebraicOperator.advance_honest (op : AlgebraicOperator) (c : EvaluationClaim R)
    (p : MvPolynomial ℕ R) (r : R) :
    (op.advance c (univariateSlice c.point op.coordinate p) r).IsTrue p :=
  eval_univariateSlice c.point op.coordinate p r

theorem AlgebraicOperator.advance_isTrue_iff (op : AlgebraicOperator) (c : EvaluationClaim R)
    (reply : Polynomial R) (p : MvPolynomial ℕ R) (r : R) :
    (op.advance c reply r).IsTrue p ↔
      reply.eval r = (univariateSlice c.point op.coordinate p).eval r := by
  rw [eval_univariateSlice]
  rfl

/-- Passing a false current claim forces the reply to differ from the honest slice. -/
theorem AlgebraicOperator.reply_ne_slice_of_false (op : AlgebraicOperator) (d : ℕ)
    (c : EvaluationClaim R) (reply : Polynomial R) (p : MvPolynomial ℕ R)
    (hc : ¬ c.IsTrue (op.act p)) (hcheck : op.RoundCheck d c reply) :
    reply ≠ univariateSlice c.point op.coordinate p := by
  intro h
  apply hc
  exact hcheck.2.symm.trans (h ▸ op.combine_univariateSlice c.point p)

/-- Two distinct polynomials of degree at most `d` agree at at most `d` points
of any finite set. The zero polynomial is allowed as either input. -/
theorem polynomial_agreement_card_le [IsDomain R] (g h : Polynomial R) (S : Finset R)
    (d : ℕ) (hne : g ≠ h) (hg : g.natDegree ≤ d) (hh : h.natDegree ≤ d) :
    (S.filter (fun r => g.eval r = h.eval r)).card ≤ d := by
  classical
  apply (Polynomial.card_le_degree_of_subset_roots (p := g - h) ?_).trans
    ((Polynomial.natDegree_sub_le g h).trans (max_le hg hh))
  intro r hr
  apply (Polynomial.mem_roots (sub_ne_zero.mpr hne)).mpr
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero] using
    (Finset.mem_filter.mp hr).2

/-- The complete local error event includes validation: a false current claim
passes the round check and becomes a true next claim on at most `d` challenges.
The reply is arbitrary and fixed before the challenge is sampled. -/
theorem AlgebraicOperator.round_error_card_le [IsDomain R] (op : AlgebraicOperator)
    (d : ℕ) (c : EvaluationClaim R) (reply : Polynomial R) (p : MvPolynomial ℕ R)
    (S : Finset R) (hp : p.degreeOf op.coordinate ≤ d) (hc : ¬ c.IsTrue (op.act p)) :
    (S.filter (fun r => op.RoundCheck d c reply ∧ (op.advance c reply r).IsTrue p)).card ≤ d := by
  classical
  by_cases hcheck : op.RoundCheck d c reply
  · simpa only [hcheck, true_and, op.advance_isTrue_iff] using
      polynomial_agreement_card_le reply (univariateSlice c.point op.coordinate p) S d
        (op.reply_ne_slice_of_false d c reply p hc hcheck) hcheck.1
        ((natDegree_univariateSlice_le _ _ _).trans hp)
  · simp [hcheck]

end

end IPPSPACE

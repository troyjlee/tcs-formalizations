/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.Round
import IPPSPACE.Arithmetization.Matrix

/-!
# Transcript verification and perfect completeness

The verifier consumes exactly one polynomial reply and field challenge per
operator, and finishes by evaluating the quantifier-free matrix. Honest replies
are slices of the next polynomial at the current point. They depend only on the
current state, so they can be sent before the next challenge is known.

The completeness theorem holds for every sequence of challenges. The `Adaptive`
module supplies the probabilistic strategy model and global soundness bound.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial Complexity

variable {R : Type*} [CommRing R]

/-- Verify a complete transcript, rejecting an incorrect number of rounds.
The terminal evaluator is an explicit parameter, independent of polynomial expansion. -/
def VerifyTranscript (d : ℕ) (terminal : (ℕ → R) → R) :
    List AlgebraicOperator → EvaluationClaim R → List (Polynomial R × R) → Prop
  | [], c, [] => c.value = terminal c.point
  | op :: ops, c, (reply, r) :: rest =>
      op.RoundCheck d c reply ∧ VerifyTranscript d terminal ops (op.advance c reply r) rest
  | _, _, _ => False

/-- An accepting transcript contains exactly one message/challenge pair per operator. -/
theorem VerifyTranscript.length_eq (d : ℕ) (terminal : (ℕ → R) → R)
    (ops : List AlgebraicOperator) (c : EvaluationClaim R) (transcript : List (Polynomial R × R))
    (h : VerifyTranscript d terminal ops c transcript) : transcript.length = ops.length := by
  induction ops generalizing c transcript with
  | nil =>
    cases transcript with
    | nil => rfl
    | cons entry rest => exact h.elim
  | cons op ops ih =>
    cases transcript with
    | nil => exact h.elim
    | cons entry rest =>
      obtain ⟨reply, r⟩ := entry
      exact congrArg Nat.succ (ih _ _ h.2)

/-- The honest prover sends the slice of the next polynomial, then uses the
revealed challenge to choose the state for the following round. -/
def honestTranscript (p : MvPolynomial ℕ R) : (ops : List AlgebraicOperator) →
    EvaluationClaim R → (Fin ops.length → R) → List (Polynomial R × R)
  | [], _, _ => []
  | op :: ops, c, rs =>
      let reply := univariateSlice c.point op.coordinate (applyOperators ops p)
      let r := rs 0
      (reply, r) :: honestTranscript p ops (op.advance c reply r) (fun j => rs j.succ)

theorem length_honestTranscript (p : MvPolynomial ℕ R) (ops : List AlgebraicOperator)
    (c : EvaluationClaim R) (rs : Fin ops.length → R) :
    (honestTranscript p ops c rs).length = ops.length := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih => simp [honestTranscript, ih]

/-- Every challenge sequence yields an accepting honest transcript for a true
claim about a chain satisfying the individual-degree bound. -/
theorem verifyTranscript_honest [Nontrivial R] (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) (d : ℕ) (c : EvaluationClaim R) (rs : Fin ops.length → R)
    (hdegree : DegreeBoundedChain ops p d) (hc : c.IsTrue (applyOperators ops p)) :
    VerifyTranscript d (fun x => eval x p) ops c (honestTranscript p ops c rs) := by
  induction ops generalizing c with
  | nil => exact hc
  | cons op ops ih =>
    change op.RoundCheck d c (univariateSlice c.point op.coordinate (applyOperators ops p)) ∧ _
    refine ⟨op.roundCheck_honest d c _ (hdegree.2.degreeOf_output _) hc, ?_⟩
    exact ih _ _ hdegree.2 (op.advance_honest c (applyOperators ops p) (rs 0))

/-- The verifier starts by claiming that the closed formula's constant polynomial is one. -/
def initialClaim : EvaluationClaim R := ⟨fun _ => 0, 1⟩

/-- The initial algebraic claim detects exactly the truth of a closed input. -/
theorem PrenexQBF.initialClaim_isTrue_iff [Nontrivial R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) :
    (initialClaim (R := R)).IsTrue φ.polynomial ↔ φ.toQBF.IsTrue := by
  rw [EvaluationClaim.IsTrue, φ.polynomial_eq_C_of_closed hclosed]
  simp only [initialClaim, eval_C, QBF.IsTrue]
  cases φ.toQBF.eval (fun _ => false) <;> simp

theorem PrenexQBF.initialClaim_isTrue [Nontrivial R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    (initialClaim (R := R)).IsTrue φ.polynomial :=
  (φ.initialClaim_isTrue_iff hclosed).mpr htrue

/-- The concrete algebraic transcript check uses only the direct matrix evaluator at the end. -/
def PrenexQBF.AcceptsTranscript (φ : PrenexQBF) (transcript : List (Polynomial R × R)) : Prop :=
  VerifyTranscript (max 2 (nodeCount φ.matrix))
    (fun x => (matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree).1)
    φ.schedule initialClaim transcript

/-- Perfect completeness for closed true prenex formulas, for every challenge sequence. -/
theorem PrenexQBF.perfect_completeness [Nontrivial R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) (rs : Fin φ.schedule.length → R) :
    φ.AcceptsTranscript (honestTranscript (arithmetize φ.matrix) φ.schedule initialClaim rs) := by
  unfold PrenexQBF.AcceptsTranscript
  simp only [matrixEvalWithCost_value]
  exact verifyTranscript_honest φ.schedule (arithmetize φ.matrix) _ initialClaim rs
    φ.degreeBoundedChain_schedule (φ.initialClaim_isTrue hclosed htrue)

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.Coefficients
import IPPSPACE.Protocol.Transcript

/-!
# Executable verification with finite messages and state

The assignment is a list of updates, with the newest value taking precedence
and zero as the default. Its storage grows by one entry per round, independently
of the largest variable name. The verifier uses bounded coefficient lists and
Horner evaluation. It never constructs a polynomial.

The cost counter counts ring additions, subtractions, and multiplications only.
Separate bounds cover the length check and assignment lookup. These are not
bit-operation or machine-time bounds; field elements are still abstract values.
-/

namespace IPPSPACE

variable {R : Type*} [CommRing R]

/-- Look up the newest update and count inspected list constructors. -/
def assignmentLookupWithCost : List (ℕ × R) → ℕ → R × ℕ
  | [], _ => (0, 1)
  | (i, r) :: rest, j =>
      if j = i then (r, 1)
      else
        let result := assignmentLookupWithCost rest j
        (result.1, result.2 + 1)

theorem assignmentLookupWithCost_cost_le (entries : List (ℕ × R)) (i : ℕ) :
    (assignmentLookupWithCost entries i).2 ≤ entries.length + 1 := by
  induction entries with
  | nil => simp [assignmentLookupWithCost]
  | cons entry entries ih =>
    obtain ⟨j, r⟩ := entry
    by_cases h : i = j <;> simp [assignmentLookupWithCost, h, ih]

/-- All persistent verifier data are finite; no array indexed by variable name is allocated. -/
structure FiniteClaim (R : Type*) where
  entries : List (ℕ × R)
  value : R

def FiniteClaim.point (c : FiniteClaim R) (i : ℕ) : R :=
  (assignmentLookupWithCost c.entries i).1

def FiniteClaim.toClaim (c : FiniteClaim R) : EvaluationClaim R :=
  ⟨c.point, c.value⟩

def finiteInitialClaim : FiniteClaim R := ⟨[], 1⟩

@[simp] theorem finiteInitialClaim_toClaim :
    (finiteInitialClaim (R := R)).toClaim = initialClaim := rfl

/-- Advance the stored claim using one Horner evaluation. -/
def FiniteClaim.advanceWithCost (c : FiniteClaim R) (op : AlgebraicOperator)
    (as : List R) (r : R) : FiniteClaim R × ℕ :=
  let result := coefficientsEvalWithCost r as
  (⟨(op.coordinate, r) :: c.entries, result.1⟩, result.2)

@[simp] theorem FiniteClaim.advanceWithCost_entries_length (c : FiniteClaim R)
    (op : AlgebraicOperator) (as : List R) (r : R) :
    (c.advanceWithCost op as r).1.entries.length = c.entries.length + 1 := rfl

@[simp] theorem FiniteClaim.advanceWithCost_cost (c : FiniteClaim R)
    (op : AlgebraicOperator) (as : List R) (r : R) :
    (c.advanceWithCost op as r).2 = 2 * as.length :=
  coefficientsEvalWithCost_cost r as

/-- Number of ring operations in the endpoint combination. -/
def AlgebraicOperator.combineCost : AlgebraicOperator → ℕ
  | .reduce _ => 4
  | .quantify (.ex _) => 4
  | .quantify (.all _) => 1

theorem AlgebraicOperator.combineCost_le (op : AlgebraicOperator) : op.combineCost ≤ 4 := by
  cases op with
  | reduce _ => rfl
  | quantify q => cases q <;> simp [combineCost]

variable [DecidableEq R]

/-- Reject oversized messages before evaluating them; otherwise check the two endpoints. -/
def checkRoundWithCost (op : AlgebraicOperator) (d : ℕ) (c : FiniteClaim R)
    (as : List R) : Bool × ℕ :=
  if (lengthCheckWithCost (d + 1) as).1 then
    let a := coefficientsEvalWithCost (0 : R) as
    let b := coefficientsEvalWithCost (1 : R) as
    (decide (op.combine c.point a.1 b.1 = c.value), a.2 + b.2 + op.combineCost)
  else (false, 0)

theorem checkRoundWithCost_length (op : AlgebraicOperator) (d : ℕ) (c : FiniteClaim R)
    (as : List R) (h : (checkRoundWithCost op d c as).1 = true) : as.length ≤ d + 1 := by
  by_contra hlen
  simp [checkRoundWithCost, lengthCheckWithCost_value, hlen] at h

theorem checkRoundWithCost_cost_le (op : AlgebraicOperator) (d : ℕ) (c : FiniteClaim R)
    (as : List R) : (checkRoundWithCost op d c as).2 ≤ 4 * (d + 1) + 4 := by
  by_cases h : as.length ≤ d + 1
  · simp only [checkRoundWithCost, lengthCheckWithCost_value, h, decide_true,
      ite_true, coefficientsEvalWithCost_cost]
    have hc := op.combineCost_le
    omega
  · simp [checkRoundWithCost, lengthCheckWithCost_value, h]

/-- Execute a complete transcript, rejecting missing or extra rounds. The
terminal evaluator is a procedure with its own ring-operation counter. -/
def verifyFiniteTranscriptWithCost (d : ℕ) (terminal : (ℕ → R) → R × ℕ) :
    List AlgebraicOperator → FiniteClaim R → List (List R × R) → Bool × ℕ
  | [], c, [] =>
      let result := terminal c.point
      (decide (c.value = result.1), result.2)
  | op :: ops, c, (as, r) :: rest =>
      let check := checkRoundWithCost op d c as
      if check.1 then
        let next := c.advanceWithCost op as r
        let result := verifyFiniteTranscriptWithCost d terminal ops next.1 rest
        (result.1, check.2 + next.2 + result.2)
      else (false, check.2)
  | _, _, _ => (false, 0)

/-- A uniform arithmetic bound, even for adversarially oversized transcripts. -/
theorem verifyFiniteTranscriptWithCost_cost_le (d : ℕ) (terminal : (ℕ → R) → R × ℕ)
    (M : ℕ) (hterminal : ∀ x, (terminal x).2 ≤ M) (ops : List AlgebraicOperator)
    (c : FiniteClaim R) (transcript : List (List R × R)) :
    (verifyFiniteTranscriptWithCost d terminal ops c transcript).2 ≤
      ops.length * (6 * (d + 1) + 4) + M := by
  induction ops generalizing c transcript with
  | nil =>
    cases transcript with
    | nil => simpa [verifyFiniteTranscriptWithCost] using hterminal c.point
    | cons _ _ => simp [verifyFiniteTranscriptWithCost]
  | cons op ops ih =>
    cases transcript with
    | nil => simp [verifyFiniteTranscriptWithCost]
    | cons entry rest =>
      obtain ⟨as, r⟩ := entry
      have hcost := checkRoundWithCost_cost_le op d c as
      by_cases hcheck : (checkRoundWithCost op d c as).1 = true
      · have hlen := checkRoundWithCost_length op d c as hcheck
        have hrest := ih (c.advanceWithCost op as r).1 rest
        simp only [verifyFiniteTranscriptWithCost, hcheck, ite_true,
          FiniteClaim.advanceWithCost_cost, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [verifyFiniteTranscriptWithCost, ite_eq_right hcheck,
          List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

noncomputable section

/-- Interpret a message for the ideal protocol. An oversized list is mapped to
a degree-`d + 1` polynomial, which the ideal verifier always rejects. This is a
proof-only translation, never an operation of the executable verifier. -/
def checkedPolynomial (d : ℕ) (as : List R) : Polynomial R :=
  if as.length ≤ d + 1 then coefficientsPolynomial as else Polynomial.X ^ (d + 1)

omit [DecidableEq R] in
theorem FiniteClaim.advanceWithCost_toClaim (c : FiniteClaim R) (op : AlgebraicOperator)
    (as : List R) (r : R) {d : ℕ} (hlen : as.length ≤ d + 1) :
    (c.advanceWithCost op as r).1.toClaim = op.advance c.toClaim (checkedPolynomial d as) r := by
  unfold advanceWithCost toClaim AlgebraicOperator.advance
  simp only [checkedPolynomial, hlen, ite_true, coefficientsEvalWithCost_value]
  congr 1
  funext j
  by_cases h : j = op.coordinate <;>
    simp [point, assignmentLookupWithCost, h]

/-- The executable endpoint/length check is exactly the ideal check under the
proof-only message translation, including every malformed oversized message. -/
theorem checkRoundWithCost_correct [Nontrivial R] (op : AlgebraicOperator)
    (d : ℕ) (c : FiniteClaim R) (as : List R) :
    (checkRoundWithCost op d c as).1 = true ↔
      op.RoundCheck d c.toClaim (checkedPolynomial d as) := by
  by_cases h : as.length ≤ d + 1
  · have hdegree := coefficientsPolynomial_natDegree_le d as h
    simp [checkRoundWithCost, lengthCheckWithCost_value, checkedPolynomial, h,
      coefficientsEvalWithCost_value, AlgebraicOperator.RoundCheck, hdegree, FiniteClaim.toClaim]
  · simp [checkRoundWithCost, lengthCheckWithCost_value, checkedPolynomial, h,
      AlgebraicOperator.RoundCheck, Polynomial.natDegree_X_pow]

/-- Complete trace refinement to the ideal verifier. -/
theorem verifyFiniteTranscriptWithCost_correct [Nontrivial R] (d : ℕ)
    (terminal : (ℕ → R) → R × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim R) (transcript : List (List R × R)) :
    (verifyFiniteTranscriptWithCost d terminal ops c transcript).1 = true ↔
      VerifyTranscript d (fun x => (terminal x).1) ops c.toClaim
        (transcript.map (fun entry => (checkedPolynomial d entry.1, entry.2))) := by
  induction ops generalizing c transcript with
  | nil =>
    cases transcript <;> simp [verifyFiniteTranscriptWithCost, VerifyTranscript, FiniteClaim.toClaim]
  | cons op ops ih =>
    cases transcript with
    | nil => simp [verifyFiniteTranscriptWithCost, VerifyTranscript]
    | cons entry rest =>
      obtain ⟨as, r⟩ := entry
      by_cases hcheck : (checkRoundWithCost op d c as).1 = true
      · have hlen := checkRoundWithCost_length op d c as hcheck
        have hideal := (checkRoundWithCost_correct op d c as).mp hcheck
        simpa only [verifyFiniteTranscriptWithCost, hcheck, ite_true, List.map_cons,
          VerifyTranscript, hideal, true_and, c.advanceWithCost_toClaim op as r hlen] using
          ih (c.advanceWithCost op as r).1 rest
      · have hideal := (checkRoundWithCost_correct op d c as).not.mp hcheck
        simp [verifyFiniteTranscriptWithCost, hcheck, VerifyTranscript, hideal]

end

end IPPSPACE

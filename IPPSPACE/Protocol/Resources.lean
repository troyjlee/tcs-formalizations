/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.FiniteVerifier

/-!
# Message and arithmetic bounds for the finite verifier

These bounds measure coefficients and ring operations, not encoded bits or
machine steps. The arithmetic bound applies to every transcript, including
malformed ones. The communication bound concerns accepted transcripts: a prover
is free to send a larger message, but the bounded length check rejects it.
-/

namespace IPPSPACE

/-- Total number of field coefficients in a transcript's prover messages. -/
def transcriptCoefficientCount {R : Type*} (transcript : List (List R × R)) : ℕ :=
  (transcript.map (fun entry => entry.1.length)).sum

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Every accepted transcript respects the total coefficient budget. -/
theorem verifyFiniteTranscriptWithCost_coefficientCount_le (d : ℕ)
    (terminal : (ℕ → R) → R × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim R) (transcript : List (List R × R))
    (h : (verifyFiniteTranscriptWithCost d terminal ops c transcript).1 = true) :
    transcriptCoefficientCount transcript ≤ ops.length * (d + 1) := by
  induction ops generalizing c transcript with
  | nil =>
    cases transcript with
    | nil => simp [transcriptCoefficientCount]
    | cons _ _ => simp [verifyFiniteTranscriptWithCost] at h
  | cons op ops ih =>
    cases transcript with
    | nil => simp [verifyFiniteTranscriptWithCost] at h
    | cons entry rest =>
      obtain ⟨as, r⟩ := entry
      by_cases hcheck : (checkRoundWithCost op d c as).1 = true
      · have hlen := checkRoundWithCost_length op d c as hcheck
        have hrest : (verifyFiniteTranscriptWithCost d terminal ops
            (c.advanceWithCost op as r).1 rest).1 = true := by
          simpa only [verifyFiniteTranscriptWithCost, ite_eq_left hcheck] using h
        have hbound := ih _ _ hrest
        change as.length + transcriptCoefficientCount rest ≤ (ops.length + 1) * (d + 1)
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [verifyFiniteTranscriptWithCost, ite_eq_right hcheck, Bool.false_eq_true] at h

/-- The executable verifier for a prenex input and an explicit transcript. -/
def PrenexQBF.verifyWithCost (φ : PrenexQBF) (transcript : List (List R × R)) : Bool × ℕ :=
  verifyFiniteTranscriptWithCost (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    φ.schedule finiteInitialClaim transcript

/-- Every accepting transcript has exactly the scheduled number of challenges. -/
theorem PrenexQBF.verifyWithCost_length [Nontrivial R] (φ : PrenexQBF)
    (transcript : List (List R × R)) (h : (φ.verifyWithCost transcript).1 = true) :
    transcript.length = φ.schedule.length := by
  have hideal := (verifyFiniteTranscriptWithCost_correct _ _ _ _ _).mp h
  simpa only [List.length_map] using VerifyTranscript.length_eq _ _ _ _ _ hideal

theorem PrenexQBF.verifyWithCost_coefficientCount_le (φ : PrenexQBF)
    (transcript : List (List R × R)) (h : (φ.verifyWithCost transcript).1 = true) :
    transcriptCoefficientCount transcript ≤ φ.schedule.length * (max 2 (nodeCount φ.matrix) + 1) :=
  verifyFiniteTranscriptWithCost_coefficientCount_le _ _ _ _ _ h

/-- Communication in field coefficients has a cubic bound in formula-node count. -/
theorem PrenexQBF.verifyWithCost_coefficientCount_le_polynomial (φ : PrenexQBF)
    (transcript : List (List R × R)) (h : (φ.verifyWithCost transcript).1 = true) :
    transcriptCoefficientCount transcript ≤
      (nodeCount φ.toQBF + 1) ^ 3 + (nodeCount φ.toQBF + 1) ^ 2 := by
  apply (φ.verifyWithCost_coefficientCount_le transcript h).trans
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.add_le_add φ.schedule_length_mul_degree_le_cube φ.schedule_length_le_square

/-- Each round uses three Horner evaluations and at most four further ring
operations; the terminal matrix uses at most four per syntax node. -/
theorem PrenexQBF.verifyWithCost_arithmetic_le (φ : PrenexQBF)
    (transcript : List (List R × R)) :
    (φ.verifyWithCost transcript).2 ≤
      φ.schedule.length * (6 * (max 2 (nodeCount φ.matrix) + 1) + 4) + 4 * nodeCount φ.matrix :=
  verifyFiniteTranscriptWithCost_cost_le _ _ _
    (fun x => matrixEvalWithCost_cost_le x φ.matrix φ.matrix_quantifierFree) _ _ _

/-- A cubic arithmetic bound for every transcript, without assuming acceptance
or placing a bound on the lengths of adversarial messages. -/
theorem PrenexQBF.verifyWithCost_arithmetic_le_polynomial (φ : PrenexQBF)
    (transcript : List (List R × R)) :
    (φ.verifyWithCost transcript).2 ≤
      6 * (nodeCount φ.toQBF + 1) ^ 3 + 10 * (nodeCount φ.toQBF + 1) ^ 2 +
        4 * nodeCount φ.toQBF := by
  have hm : nodeCount φ.matrix ≤ nodeCount φ.toQBF := by
    rw [PrenexQBF.toQBF, nodeCount_prefixQBF]
    exact Nat.le_add_right _ _
  calc
    _ ≤ φ.schedule.length * (6 * (max 2 (nodeCount φ.matrix) + 1) + 4) +
        4 * nodeCount φ.matrix := φ.verifyWithCost_arithmetic_le transcript
    _ = 6 * (φ.schedule.length * max 2 (nodeCount φ.matrix)) +
        10 * φ.schedule.length + 4 * nodeCount φ.matrix := by ring
    _ ≤ _ := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left 6 φ.schedule_length_mul_degree_le_cube)
        (Nat.mul_le_mul_left 10 φ.schedule_length_le_square)) (Nat.mul_le_mul_left 4 hm)

end IPPSPACE

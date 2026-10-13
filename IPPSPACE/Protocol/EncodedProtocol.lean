/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.RandomTape
import IPPSPACE.Protocol.TranscriptStrategy
import IPPSPACE.Protocol.ResourcePolynomials

/-!
# Encoded prenex verification with a polynomial-length random tape

This total deterministic verifier consumes a raw encoded input, a global
transcript strategy, and a Boolean tape of an exact polynomial length in the
input bit length. Invalid, non-prenex, and open inputs are rejected. A valid
closed prenex formula uses only the necessary prefix of the tape.

The semantics has perfect completeness with a globally bounded honest prover
and rational counting soundness at most one third. This does not establish
`FP` membership, the full upstream interactive interface, or PSPACE hardness.
-/

namespace IPPSPACE

/-- Successful closed-prenex decoding bounds syntax size by the actual input length. -/
theorem decodeClosedPrenex_nodeCount_le (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ) :
    nodeCount φ.val.toQBF ≤ input.length := by
  rw [← (decodeClosedPrenex_eq_some_iff input φ).mp h]
  exact nodeCount_le_length_encodeQBF φ.val.toQBF

/-- Every decoded input fits the fixed polynomial coin budget. -/
theorem decodeClosedPrenex_coins_le (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ) :
    φ.val.randomBitBudget ≤ coinResourcePolynomial.eval input.length :=
  φ.val.coins_le_resource_eval _ (decodeClosedPrenex_nodeCount_le input φ h)

/-- Total executable verification at the exact encoded-input polynomial coin budget.
The prover receives only the previous challenge through its transcript history. -/
def verifyEncodedProtocol (S : List (List Bool) → List Bool) (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) : Bool :=
  match h : decodeClosedPrenex input with
  | none => false
  | some φ =>
      φ.val.verifyRandomTape (unfoldTranscriptStrategy S φ.val.schedule.length [[]])
        (fun i => tape ⟨i.val, i.isLt.trans_le (decodeClosedPrenex_coins_le input φ h)⟩)

/-- Failed canonical decoding, prenex recognition, or closedness validation rejects. -/
theorem verifyEncodedProtocol_reject (S : List (List Bool) → List Bool) (input : List Bool)
    (h : decodeClosedPrenex input = none)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    verifyEncodedProtocol S input tape = false := by
  unfold verifyEncodedProtocol
  split
  · rfl
  · rename_i φ hφ
    simp [h] at hφ

theorem verifyEncodedProtocol_decoded (S : List (List Bool) → List Bool) (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    verifyEncodedProtocol S input tape =
      φ.val.verifyRandomTape (unfoldTranscriptStrategy S φ.val.schedule.length [[]])
        (fun i => tape (Fin.castLE (decodeClosedPrenex_coins_le input φ h) i)) := by
  unfold verifyEncodedProtocol
  split
  · rename_i hnone
    simp [h] at hnone
  · rename_i ψ hψ
    have heq : ψ = φ := Option.some.inj (hψ.symm.trans h)
    subst ψ
    rfl

/-- The encoded true closed prenex language. No conversion from arbitrary QBF
or PSPACE hardness is built into this definition. -/
def EncodedTruePrenex (input : List Bool) : Prop :=
  ∃ φ : {φ : PrenexQBF // φ.toQBF.Closed},
    decodeClosedPrenex input = some φ ∧ φ.val.toQBF.IsTrue

noncomputable section

open scoped Classical ENNReal

/-- The entire encoded execution has exactly the existing transcript protocol's
output distribution; all surplus input-length-budget coins are ignored. -/
theorem verifyEncodedProtocol_uniform (S : List (List Bool) → List Bool) (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ) :
    (PMF.uniformOfFintype (Fin (coinResourcePolynomial.eval input.length) → Bool)).map
      (verifyEncodedProtocol S input) = φ.val.runTranscriptProtocol S := by
  have hfun : verifyEncodedProtocol S input =
      (φ.val.verifyRandomTape (unfoldTranscriptStrategy S φ.val.schedule.length [[]])) ∘
        (fun tape i => tape (Fin.castLE (decodeClosedPrenex_coins_le input φ h) i)) := by
    funext tape
    exact verifyEncodedProtocol_decoded S input φ h tape
  rw [hfun, ← PMF.map_comp, uniform_bitTape_restrict,
    φ.val.verifyRandomTape_uniform, φ.val.runTranscriptProtocol_eq_runMessageProtocol]

/-- Every global transcript strategy satisfies soundness on a false decoded input. -/
theorem verifyEncodedProtocol_decoded_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (φ : {φ : PrenexQBF // φ.toQBF.Closed})
    (h : decodeClosedPrenex input = some φ) (hfalse : ¬ φ.val.toQBF.IsTrue) :
    ((PMF.uniformOfFintype (Fin (coinResourcePolynomial.eval input.length) → Bool)).map
      (verifyEncodedProtocol S input)) true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [verifyEncodedProtocol_uniform S input φ h]
  exact φ.val.runTranscriptProtocol_soundness_le_third φ.property hfalse S

/-- The rational acceptance-count ratio on a false decoded input is at most one third. -/
theorem verifyEncodedProtocol_decoded_counting_soundness
    (S : List (List Bool) → List Bool) (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ)
    (hfalse : ¬ φ.val.toQBF.IsTrue) :
    ((Finset.univ.filter fun tape => verifyEncodedProtocol S input tape = true).card : ℚ) /
      2 ^ (coinResourcePolynomial.eval input.length) ≤ 1 / 3 :=
  (bitTape_acceptance_le_third_iff _ _).mp
    (verifyEncodedProtocol_decoded_soundness S input φ h hfalse)

/-- Soundness covers all nonmembers, including invalid and open encoded inputs. -/
theorem verifyEncodedProtocol_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTruePrenex input) :
    ((PMF.uniformOfFintype (Fin (coinResourcePolynomial.eval input.length) → Bool)).map
      (verifyEncodedProtocol S input)) true ≤ (1 : ℝ≥0∞) / 3 := by
  cases h : decodeClosedPrenex input with
  | none =>
    have hfun : verifyEncodedProtocol S input = fun _ => false := by
      funext tape
      exact verifyEncodedProtocol_reject S input h tape
    rw [hfun]
    have hp : (PMF.uniformOfFintype (Fin (coinResourcePolynomial.eval input.length) → Bool)).map
        (fun _ => false) = PMF.pure false := PMF.map_const _ _
    rw [hp]
    simp
  | some φ =>
    exact verifyEncodedProtocol_decoded_soundness S input φ h
      (fun ht => hfalse ⟨φ, h, ht⟩)

theorem verifyEncodedProtocol_counting_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTruePrenex input) :
    ((Finset.univ.filter fun tape => verifyEncodedProtocol S input tape = true).card : ℚ) /
      2 ^ (coinResourcePolynomial.eval input.length) ≤ 1 / 3 :=
  (bitTape_acceptance_le_third_iff _ _).mp (verifyEncodedProtocol_soundness S input hfalse)

/-- The honest transcript strategy is bounded on every possible history, not
only histories reached during a successful verification. -/
theorem honestTranscriptStrategy_length_le_input_resource (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ)
    (history : List (List Bool)) :
    (φ.val.honestTranscriptStrategy history).length ≤
      messageResourcePolynomial.eval input.length := by
  apply (φ.val.honestTranscriptStrategy_bounded history).trans
  rw [messageResourcePolynomial_eval]
  have hnode := decodeClosedPrenex_nodeCount_le input φ h
  exact Nat.mul_le_mul (φ.val.coefficientLimit_le_of_nodeCount_le _ hnode)
    (φ.val.wordWidth_le_of_nodeCount_le _ hnode)

/-- Every tape accepts the globally bounded honest prover for a true decoded input. -/
theorem verifyEncodedProtocol_honest (input : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ)
    (htrue : φ.val.toQBF.IsTrue)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    verifyEncodedProtocol φ.val.honestTranscriptStrategy input tape = true := by
  rw [verifyEncodedProtocol_decoded _ input φ h]
  unfold PrenexQBF.honestTranscriptStrategy
  rw [unfoldTranscriptStrategy_asTranscriptStrategy]
  exact φ.val.verifyRandomTape_honest φ.property htrue _

/-- Semantic completeness at exact polynomial coin and global message budgets. -/
theorem verifyEncodedProtocol_complete (input : List Bool) (htrue : EncodedTruePrenex input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤ messageResourcePolynomial.eval input.length) ∧
      ∀ tape, verifyEncodedProtocol S input tape = true := by
  obtain ⟨φ, hdecode, ht⟩ := htrue
  exact ⟨φ.val.honestTranscriptStrategy,
    honestTranscriptStrategy_length_le_input_resource input φ hdecode,
    verifyEncodedProtocol_honest input φ hdecode ht⟩

end

end IPPSPACE

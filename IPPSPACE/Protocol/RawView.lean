/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.PaddedTranscript

/-!
# Total verifier procedures on raw coin strings

The upstream encoded-view interface permits arbitrary coin strings, including
wrong-length strings on unreachable views. These procedures interpret missing
bits as false and ignore bits beyond the fixed budget. Message bounds hold on
every view, and exact-length uniform tapes retain the proved protocol semantics.
The three arguments still need packaging in upstream's encoded-view format and
polynomial-time certificates.
-/

namespace IPPSPACE

/-- Total interpretation of any raw coin string at the input's polynomial budget. -/
def coinTapeFromList (input coins : List Bool) :
    Fin (coinResourcePolynomial.eval input.length) → Bool :=
  fun i => coins[i.val]?.getD false

@[simp] theorem coinTapeFromList_ofFn (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    coinTapeFromList input (List.ofFn tape) = tape := by
  funext i
  simp only [coinTapeFromList, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

/-- Extra coins cannot affect any computation through this tape interface. -/
theorem coinTapeFromList_eq_of_take_eq (input first second : List Bool)
    (h : first.take (coinResourcePolynomial.eval input.length) =
      second.take (coinResourcePolynomial.eval input.length)) :
    coinTapeFromList input first = coinTapeFromList input second := by
  funext i
  have hi := congrArg (fun xs : List Bool => xs[i.val]?.getD false) h
  simpa only [coinTapeFromList, List.getElem?_take, i.isLt, ite_true] using hi

/-- The next verifier message is defined for every input, coin string and history. -/
def rawVerifierMessage (input coins : List Bool) (history : List (List Bool)) : List Bool :=
  encodedVerifierMessage input (coinTapeFromList input coins) history

/-- The final verdict is a total predicate of the same raw view components. -/
def rawTranscriptVerdict (input coins : List Bool) (history : List (List Bool)) : Bool :=
  encodedTranscriptVerdict input (coinTapeFromList input coins) history

/-- This bound has no hypothesis on coin length or history reachability. -/
theorem rawVerifierMessage_length_le (input coins : List Bool) (history : List (List Bool)) :
    (rawVerifierMessage input coins history).length ≤
      messageResourcePolynomial.eval input.length :=
  encodedVerifierMessage_length_le _ _ _

@[simp] theorem rawVerifierMessage_ofFn (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) :
    rawVerifierMessage input (List.ofFn tape) history = encodedVerifierMessage input tape history := by
  rw [rawVerifierMessage, coinTapeFromList_ofFn]

@[simp] theorem rawTranscriptVerdict_ofFn (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) :
    rawTranscriptVerdict input (List.ofFn tape) history = encodedTranscriptVerdict input tape history := by
  rw [rawTranscriptVerdict, coinTapeFromList_ofFn]

theorem rawTranscriptVerdict_invalid (input coins : List Bool) (history : List (List Bool))
    (h : decodeClosedPrenex input = none) : rawTranscriptVerdict input coins history = false :=
  encodedTranscriptVerdict_invalid _ _ _ h

/-- Execute the verifier-first interaction using only the total raw-view procedures. -/
def rawProtocolExecution (S : List (List Bool) → List Bool) (input coins : List Bool) : Bool :=
  rawTranscriptVerdict input coins
    (interactionTranscript S (rawVerifierMessage input coins) (encodedRoundBudget input))

theorem rawProtocolExecution_eq (S : List (List Bool) → List Bool) (input coins : List Bool) :
    rawProtocolExecution S input coins =
      paddedProtocolExecution S input (coinTapeFromList input coins) := rfl

@[simp] theorem rawProtocolExecution_ofFn (S : List (List Bool) → List Bool) (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    rawProtocolExecution S input (List.ofFn tape) = verifyEncodedProtocol S input tape := by
  rw [rawProtocolExecution_eq, coinTapeFromList_ofFn,
    paddedProtocolExecution_eq_verifyEncodedProtocol]

theorem rawProtocolExecution_eq_of_take_eq (S : List (List Bool) → List Bool)
    (input first second : List Bool)
    (h : first.take (coinResourcePolynomial.eval input.length) =
      second.take (coinResourcePolynomial.eval input.length)) :
    rawProtocolExecution S input first = rawProtocolExecution S input second := by
  rw [rawProtocolExecution_eq, rawProtocolExecution_eq,
    coinTapeFromList_eq_of_take_eq input first second h]

noncomputable section

open scoped Classical

/-- Every encoded member has a globally bounded prover accepted on every correctly
sized tape by the raw-view procedures. -/
theorem rawProtocolExecution_complete (input : List Bool) (htrue : EncodedTruePrenex input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤ messageResourcePolynomial.eval input.length) ∧
      ∀ tape : Fin (coinResourcePolynomial.eval input.length) → Bool,
        rawProtocolExecution S input (List.ofFn tape) = true := by
  simpa only [rawProtocolExecution_ofFn] using verifyEncodedProtocol_complete input htrue

/-- The rational soundness guarantee is unchanged by the raw coin-string interface. -/
theorem rawProtocolExecution_counting_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTruePrenex input) :
    ((Finset.univ.filter fun tape : Fin (coinResourcePolynomial.eval input.length) → Bool =>
      rawProtocolExecution S input (List.ofFn tape) = true).card : ℚ) /
      2 ^ (coinResourcePolynomial.eval input.length) ≤ 1 / 3 := by
  simpa only [rawProtocolExecution_ofFn] using
    verifyEncodedProtocol_counting_soundness S input hfalse

end

end IPPSPACE

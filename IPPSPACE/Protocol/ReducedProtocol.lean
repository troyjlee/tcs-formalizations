/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexReduction
import IPPSPACE.Protocol.ViewEncoding

/-!
# Verification after prenex conversion at original-input resource budgets

The total QBF-to-prenex reduction expands an input of length `L` to at most
`L * (4 * L + 8)` bits. Compose the resource polynomials with that bound and
pad the interaction accordingly. Extra rounds and private coins do not affect
acceptance, including for adversarial strategies and malformed source inputs.
These are semantic verifier procedures; machine-time certificates and the
upstream `Protocol` construction remain open.
-/

namespace IPPSPACE

open Polynomial

/-- The proved size bound for the total prenex reduction. -/
def prenexLengthBudget (L : ℕ) : ℕ := L * (4 * L + 8)

noncomputable def prenexLengthPolynomial : Polynomial ℕ := X * (4 * X + 8)
noncomputable def reducedRoundPolynomial : Polynomial ℕ :=
  roundResourcePolynomial.comp prenexLengthPolynomial
noncomputable def reducedCoinPolynomial : Polynomial ℕ :=
  coinResourcePolynomial.comp prenexLengthPolynomial
noncomputable def reducedMessagePolynomial : Polynomial ℕ :=
  messageResourcePolynomial.comp prenexLengthPolynomial

@[simp] theorem prenexLengthPolynomial_eval (L : ℕ) :
    prenexLengthPolynomial.eval L = prenexLengthBudget L := by
  simp [prenexLengthPolynomial, prenexLengthBudget]

@[simp] theorem reducedRoundPolynomial_eval (L : ℕ) :
    reducedRoundPolynomial.eval L = (prenexLengthBudget L + 1) ^ 2 := by
  simp [reducedRoundPolynomial, Polynomial.eval_comp]

@[simp] theorem reducedCoinPolynomial_eval (L : ℕ) :
    reducedCoinPolynomial.eval L =
      (prenexLengthBudget L + 1) ^ 2 * (12 * (prenexLengthBudget L + 1) ^ 3 + 1) := by
  simp [reducedCoinPolynomial, Polynomial.eval_comp]

@[simp] theorem reducedMessagePolynomial_eval (L : ℕ) :
    reducedMessagePolynomial.eval L =
      (prenexLengthBudget L + 3) * (12 * (prenexLengthBudget L + 1) ^ 3 + 1) := by
  simp [reducedMessagePolynomial, Polynomial.eval_comp]

def reducedRoundBudget (input : List Bool) : ℕ := (prenexLengthBudget input.length + 1) ^ 2

@[simp] theorem reducedRoundBudget_eq (input : List Bool) :
    reducedRoundBudget input = reducedRoundPolynomial.eval input.length := by
  simp [reducedRoundBudget]

theorem prenexReduction_rounds_le (input : List Bool) :
    encodedRoundBudget (prenexReduction input) ≤ reducedRoundBudget input := by
  have h := prenexReduction_length_le input
  dsimp [encodedRoundBudget, reducedRoundBudget, prenexLengthBudget]
  gcongr

theorem prenexReduction_coins_le (input : List Bool) :
    coinResourcePolynomial.eval (prenexReduction input).length ≤
      reducedCoinPolynomial.eval input.length := by
  have h : (prenexReduction input).length ≤ prenexLengthBudget input.length :=
    prenexReduction_length_le input
  simp only [coinResourcePolynomial_eval, reducedCoinPolynomial_eval]
  gcongr

theorem prenexReduction_messages_le (input : List Bool) :
    messageResourcePolynomial.eval (prenexReduction input).length ≤
      reducedMessagePolynomial.eval input.length := by
  have h : (prenexReduction input).length ≤ prenexLengthBudget input.length :=
    prenexReduction_length_le input
  simp only [messageResourcePolynomial_eval, reducedMessagePolynomial_eval]
  gcongr

/-- Taking an initial number of rounds gives exactly the shorter interaction,
for every strategy and every message procedure. -/
theorem interactionTranscript_take (S : List (List Bool) → List Bool)
    (vmsg : List (List Bool) → List Bool) (n N : ℕ) (h : n ≤ N) :
    (interactionTranscript S vmsg N).take (2 * n) = interactionTranscript S vmsg n := by
  induction N with
  | zero =>
    have : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases heq : n = N + 1
    · subst n
      exact List.take_of_length_le (by rw [interactionTranscript_length])
    · rw [interactionTranscript,
        List.take_append_of_le_length (by rw [interactionTranscript_length]; omega)]
      exact ih (by omega)

/-- The source verifier sends the target verifier's messages on the same history. -/
def reducedRawVerifierMessage (input coins : List Bool) (history : List (List Bool)) : List Bool :=
  rawVerifierMessage (prenexReduction input) coins history

/-- Check the source round count, then replay only the target's initial rounds. -/
def reducedRawTranscriptVerdict (input coins : List Bool) (history : List (List Bool)) : Bool :=
  if history.length = 2 * reducedRoundBudget input then
    rawTranscriptVerdict (prenexReduction input) coins
      (history.take (2 * encodedRoundBudget (prenexReduction input)))
  else false

theorem reducedRawVerifierMessage_length_le (input coins : List Bool)
    (history : List (List Bool)) :
    (reducedRawVerifierMessage input coins history).length ≤
      reducedMessagePolynomial.eval input.length :=
  (rawVerifierMessage_length_le _ _ _).trans (prenexReduction_messages_le input)

/-- Execute exactly the composed round polynomial in the original input length. -/
def reducedRawProtocolExecution (S : List (List Bool) → List Bool)
    (input coins : List Bool) : Bool :=
  reducedRawTranscriptVerdict input coins
    (interactionTranscript S (reducedRawVerifierMessage input coins) (reducedRoundBudget input))

theorem reducedRawProtocolExecution_eq (S : List (List Bool) → List Bool)
    (input coins : List Bool) :
    reducedRawProtocolExecution S input coins = rawProtocolExecution S (prenexReduction input) coins := by
  simp only [reducedRawProtocolExecution, reducedRawTranscriptVerdict,
    interactionTranscript_length, ite_true]
  rw [interactionTranscript_take _ _ _ _ (prenexReduction_rounds_le input)]
  rfl

/-- Prefix restriction also describes the raw-list tape interpretation exactly. -/
theorem coinTapeFromList_ofFn_restrict (input : List Bool) (T : ℕ)
    (h : coinResourcePolynomial.eval input.length ≤ T) (tape : Fin T → Bool) :
    coinTapeFromList input (List.ofFn tape) = fun i => tape (Fin.castLE h i) := by
  funext i
  simp only [coinTapeFromList, List.getElem?_ofFn, i.isLt.trans_le h,
    dite_true, Option.getD_some, Fin.castLE]

/-- Materialize the tape using an executable numeric length, while retaining the
polynomial-evaluation type of the public fixed-tape interface. -/
def reducedCoinList (input : List Bool)
    (tape : Fin (reducedCoinPolynomial.eval input.length) → Bool) : List Bool :=
  List.ofFn (fun i : Fin ((prenexLengthBudget input.length + 1) ^ 2 *
    (12 * (prenexLengthBudget input.length + 1) ^ 3 + 1)) =>
      tape ⟨i.val, by rw [reducedCoinPolynomial_eval]; exact i.isLt⟩)

@[simp] theorem reducedCoinList_eq (input : List Bool)
    (tape : Fin (reducedCoinPolynomial.eval input.length) → Bool) :
    reducedCoinList input tape = List.ofFn tape :=
  (List.ofFn_congr (reducedCoinPolynomial_eval input.length) tape).symm

/-- Original-input fixed coins feed the target's shorter coin prefix. -/
def verifyReducedProtocol (S : List (List Bool) → List Bool) (input : List Bool)
    (tape : Fin (reducedCoinPolynomial.eval input.length) → Bool) : Bool :=
  reducedRawProtocolExecution S input (reducedCoinList input tape)

theorem verifyReducedProtocol_eq (S : List (List Bool) → List Bool) (input : List Bool)
    (tape : Fin (reducedCoinPolynomial.eval input.length) → Bool) :
    verifyReducedProtocol S input tape = verifyEncodedProtocol S (prenexReduction input)
      (fun i => tape (Fin.castLE (prenexReduction_coins_le input) i)) := by
  rw [verifyReducedProtocol, reducedCoinList_eq, reducedRawProtocolExecution_eq, rawProtocolExecution_eq,
    coinTapeFromList_ofFn_restrict _ _ (prenexReduction_coins_le input),
    paddedProtocolExecution_eq_verifyEncodedProtocol]


/-- Single-string message procedure for arbitrary closed-QBF verification. -/
def reducedViewVerifierMessage : List Bool → List Bool := packViewMessage reducedRawVerifierMessage

/-- Single-string verdict; malformed packed views reject. -/
def reducedViewTranscriptVerdict : List Bool → Bool := packViewVerdict reducedRawTranscriptVerdict

@[simp] theorem reducedViewVerifierMessage_encode (input coins : List Bool)
    (history : List (List Bool)) :
    reducedViewVerifierMessage (encodeProtocolView input coins history) =
      reducedRawVerifierMessage input coins history := packViewMessage_encode _ _ _ _

@[simp] theorem reducedViewTranscriptVerdict_encode (input coins : List Bool)
    (history : List (List Bool)) :
    reducedViewTranscriptVerdict (encodeProtocolView input coins history) =
      reducedRawTranscriptVerdict input coins history := packViewVerdict_encode _ _ _ _

/-- Original-input message bounds hold for every packed raw view. -/
theorem reducedViewVerifierMessage_length_le (input coins : List Bool)
    (history : List (List Bool)) :
    (reducedViewVerifierMessage (encodeProtocolView input coins history)).length ≤
      reducedMessagePolynomial.eval input.length := by
  simpa only [reducedViewVerifierMessage_encode] using
    reducedRawVerifierMessage_length_le input coins history

/-- A total bound on arbitrary strings, including strings that do not decode. -/
theorem reducedViewVerifierMessage_length_le_view_length (bits : List Bool) :
    (reducedViewVerifierMessage bits).length ≤ reducedMessagePolynomial.eval bits.length := by
  apply packViewMessage_length_le_view_length reducedRawVerifierMessage
    (fun n => reducedMessagePolynomial.eval n) _ reducedRawVerifierMessage_length_le bits
  intro a b hab
  simp only [reducedMessagePolynomial_eval, prenexLengthBudget]
  gcongr

/-- Original-input interaction using only the packed message/verdict procedures. -/
def reducedViewProtocolExecution (S : List (List Bool) → List Bool)
    (input coins : List Bool) : Bool :=
  reducedViewTranscriptVerdict (encodeProtocolView input coins
    (interactionTranscript S (fun history =>
      reducedViewVerifierMessage (encodeProtocolView input coins history)) (reducedRoundBudget input)))

theorem reducedViewProtocolExecution_eq (S : List (List Bool) → List Bool)
    (input coins : List Bool) :
    reducedViewProtocolExecution S input coins = reducedRawProtocolExecution S input coins := by
  simp [reducedViewProtocolExecution, reducedRawProtocolExecution]

@[simp] theorem reducedViewProtocolExecution_ofFn (S : List (List Bool) → List Bool)
    (input : List Bool) (tape : Fin (reducedCoinPolynomial.eval input.length) → Bool) :
    reducedViewProtocolExecution S input (List.ofFn tape) = verifyReducedProtocol S input tape := by
  rw [reducedViewProtocolExecution_eq, verifyReducedProtocol, reducedCoinList_eq]

noncomputable section

open scoped Classical ENNReal

/-- All output probabilities are preserved by the additional private coins. -/
theorem verifyReducedProtocol_uniform (S : List (List Bool) → List Bool) (input : List Bool) :
    (PMF.uniformOfFintype (Fin (reducedCoinPolynomial.eval input.length) → Bool)).map
      (verifyReducedProtocol S input) =
    (PMF.uniformOfFintype (Fin (coinResourcePolynomial.eval (prenexReduction input).length) → Bool)).map
      (verifyEncodedProtocol S (prenexReduction input)) := by
  have hfun : verifyReducedProtocol S input = verifyEncodedProtocol S (prenexReduction input) ∘
      (fun tape i => tape (Fin.castLE (prenexReduction_coins_le input) i)) := by
    funext tape
    exact verifyReducedProtocol_eq S input tape
  rw [hfun, ← PMF.map_comp, uniform_bitTape_restrict]

/-- Every true closed QBF has a prover bounded by the composed message polynomial
and accepted for every tape of the composed original-input coin length. -/
theorem verifyReducedProtocol_complete (input : List Bool) (htrue : EncodedTrueQBF input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤ reducedMessagePolynomial.eval input.length) ∧
      ∀ tape, verifyReducedProtocol S input tape = true := by
  obtain ⟨S, hbound, haccept⟩ := verifyEncodedProtocol_complete (prenexReduction input)
    ((encodedTrueQBF_iff_prenexReduction input).mp htrue)
  refine ⟨S, fun history => (hbound history).trans (prenexReduction_messages_le input), ?_⟩
  intro tape
  rw [verifyReducedProtocol_eq]
  exact haccept _

/-- Soundness includes malformed and open source inputs, against every strategy. -/
theorem verifyReducedProtocol_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTrueQBF input) :
    ((PMF.uniformOfFintype (Fin (reducedCoinPolynomial.eval input.length) → Bool)).map
      (verifyReducedProtocol S input)) true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [verifyReducedProtocol_uniform]
  exact verifyEncodedProtocol_soundness S (prenexReduction input)
    (fun h => hfalse ((encodedTrueQBF_iff_prenexReduction input).mpr h))

theorem verifyReducedProtocol_counting_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTrueQBF input) :
    ((Finset.univ.filter fun tape => verifyReducedProtocol S input tape = true).card : ℚ) /
      2 ^ (reducedCoinPolynomial.eval input.length) ≤ 1 / 3 :=
  (bitTape_acceptance_le_third_iff _ _).mp (verifyReducedProtocol_soundness S input hfalse)


/-- Packed procedures retain the globally bounded honest prover. -/
theorem reducedViewProtocolExecution_complete (input : List Bool) (htrue : EncodedTrueQBF input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤ reducedMessagePolynomial.eval input.length) ∧
      ∀ tape : Fin (reducedCoinPolynomial.eval input.length) → Bool,
        reducedViewProtocolExecution S input (List.ofFn tape) = true := by
  simpa only [reducedViewProtocolExecution_ofFn] using verifyReducedProtocol_complete input htrue

/-- Rational counting soundness of the packed arbitrary-QBF verifier. -/
theorem reducedViewProtocolExecution_counting_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTrueQBF input) :
    ((Finset.univ.filter fun tape : Fin (reducedCoinPolynomial.eval input.length) → Bool =>
      reducedViewProtocolExecution S input (List.ofFn tape) = true).card : ℚ) /
      2 ^ (reducedCoinPolynomial.eval input.length) ≤ 1 / 3 := by
  simpa only [reducedViewProtocolExecution_ofFn] using
    verifyReducedProtocol_counting_soundness S input hfalse

end

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.RawView

/-!
# The concrete upstream protocol-view bit encoding

The inspected Complexitylib revision `add0aca8ee0d71e68969f2cb45cf91554a50f787`
defines `protocolView x r τ = pair (pair x r) (DataEncode.bitstringEncode τ)`.
`Encoding/Pairing.lean` doubles the first component's bits, adds `[false,true]`,
then appends the second component. `Encoding/DataEncode.lean` and `Encoding/Data`
encode lists between false/true brackets; Boolean false is `[false,true]` and
Boolean true is `[false,false,true,true]`.

The executable equations below implement that exact concrete representation.
Their proofs establish canonical decoding and the single-string verifier
adapters locally. `UpstreamView.lean` now proves equality to the imported pairing
and data-encoding declarations and certifies polynomial-time packing and field
projections. The full interactive module, including its named `protocolView`,
is not yet imported. This module itself introduces no complexity class or
`FP`/`P` certificate. The encoding conventions originate
in upstream work by Samuel Schlesinger, Christian Reitwiessner, and Bolton Bailey.
-/

namespace IPPSPACE

/-- The upstream doubling-and-separator pairing equation. -/
def viewPair : List Bool → List Bool → List Bool
  | [], right => false :: true :: right
  | b :: left, right => b :: b :: viewPair left right

theorem viewPair_eq_doubled (left right : List Bool) :
    viewPair left right = left.flatMap (fun b => [b, b]) ++ [false, true] ++ right := by
  induction left with
  | nil => rfl
  | cons b left ih => simp [viewPair, ih]

@[simp] theorem length_viewPair (left right : List Bool) :
    (viewPair left right).length = 2 * left.length + 2 + right.length := by
  induction left with
  | nil => simp [viewPair]; omega
  | cons b left ih => simp [viewPair, ih]; omega

/-- Reject malformed doubled prefixes; the separator leaves the second
component untouched. -/
def parseViewPair : List Bool → Option (List Bool × List Bool)
  | false :: true :: rest => some ([], rest)
  | false :: false :: rest => (parseViewPair rest).map (fun result => (false :: result.1, result.2))
  | true :: true :: rest => (parseViewPair rest).map (fun result => (true :: result.1, result.2))
  | _ => none

@[simp] theorem parseViewPair_viewPair (left right : List Bool) :
    parseViewPair (viewPair left right) = some (left, right) := by
  induction left with
  | nil => rfl
  | cons b left ih => cases b <;> simp [viewPair, parseViewPair, ih]

theorem parseViewPair_sound (bits left right : List Bool)
    (h : parseViewPair bits = some (left, right)) : viewPair left right = bits := by
  induction bits using parseViewPair.induct generalizing left right with
  | case1 rest =>
    have heq : ([], rest) = (left, right) := Option.some.inj h
    cases heq
    rfl
  | case2 rest ih =>
    cases hp : parseViewPair rest with
    | none => simp [parseViewPair, hp] at h
    | some result =>
      rcases result with ⟨xs, ys⟩
      have heq : (false :: xs, ys) = (left, right) := by simpa [parseViewPair, hp] using h
      cases heq
      simpa [viewPair] using congrArg (fun bs => false :: false :: bs) (ih xs _ hp)
  | case3 rest ih =>
    cases hp : parseViewPair rest with
    | none => simp [parseViewPair, hp] at h
    | some result =>
      rcases result with ⟨xs, ys⟩
      have heq : (true :: xs, ys) = (left, right) := by simpa [parseViewPair, hp] using h
      cases heq
      simpa [viewPair] using congrArg (fun bs => true :: true :: bs) (ih xs _ hp)
  | case4 bits _ _ _ => simp [parseViewPair] at h

/-- The two concrete `DataEncode Bool` codes after `Data.toBits`. -/
def viewBoolCode (b : Bool) : List Bool :=
  if b then [false, false, true, true] else [false, true]

/-- The concrete upstream encoding of one message (`List Bool`). -/
def encodeViewMessage (bits : List Bool) : List Bool :=
  false :: (bits.flatMap viewBoolCode ++ [true])

/-- The concrete upstream encoding of an alternating transcript. -/
def encodeViewTranscript (history : List (List Bool)) : List Bool :=
  false :: (history.flatMap encodeViewMessage ++ [true])

theorem length_viewBoolCode_ge (b : Bool) : 2 ≤ (viewBoolCode b).length := by
  cases b <;> decide

theorem length_viewBoolCode_le (b : Bool) : (viewBoolCode b).length ≤ 4 := by
  cases b <;> decide

theorem length_encodeViewMessage_ge (bits : List Bool) :
    bits.length + 2 ≤ (encodeViewMessage bits).length := by
  have h : bits.length ≤ (bits.flatMap viewBoolCode).length := by
    induction bits with
    | nil => rfl
    | cons b bits ih =>
      have hb := length_viewBoolCode_ge b
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  simp only [encodeViewMessage, List.length_cons, List.length_append, List.length_nil]
  omega

theorem length_encodeViewMessage_le (bits : List Bool) :
    (encodeViewMessage bits).length ≤ 4 * bits.length + 2 := by
  have h : (bits.flatMap viewBoolCode).length ≤ 4 * bits.length := by
    induction bits with
    | nil => rfl
    | cons b bits ih =>
      have hb := length_viewBoolCode_le b
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
  simp only [encodeViewMessage, List.length_cons, List.length_append, List.length_nil]
  omega

/-- Parse the Boolean contents of one bracketed message after its opening bit.
Fuel bounds recursion even on malformed input. -/
def parseViewMessageBody : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, _ => none
  | _ + 1, true :: rest => some ([], rest)
  | fuel + 1, false :: true :: rest =>
      (parseViewMessageBody fuel rest).map (fun result => (false :: result.1, result.2))
  | fuel + 1, false :: false :: true :: true :: rest =>
      (parseViewMessageBody fuel rest).map (fun result => (true :: result.1, result.2))
  | _ + 1, _ => none

/-- Read one complete message, preserving its following suffix. -/
def parseViewMessage (fuel : ℕ) : List Bool → Option (List Bool × List Bool)
  | false :: rest => parseViewMessageBody fuel rest
  | _ => none

theorem parseViewMessageBody_encode (bits : List Bool) (fuel : ℕ) (rest : List Bool)
    (hfuel : bits.length + 1 ≤ fuel) :
    parseViewMessageBody fuel (bits.flatMap viewBoolCode ++ [true] ++ rest) = some (bits, rest) := by
  induction bits generalizing fuel with
  | nil => cases fuel <;> simp_all [parseViewMessageBody]
  | cons b bits ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hf : bits.length + 1 ≤ fuel := by simpa using Nat.le_of_succ_le_succ hfuel
      cases b <;> simp [viewBoolCode, parseViewMessageBody, List.append_assoc] <;>
        simpa using ih fuel hf

theorem parseViewMessage_encode (bits : List Bool) (fuel : ℕ) (rest : List Bool)
    (hfuel : bits.length + 1 ≤ fuel) :
    parseViewMessage fuel (encodeViewMessage bits ++ rest) = some (bits, rest) := by
  simpa [encodeViewMessage, parseViewMessage, List.append_assoc] using
    parseViewMessageBody_encode bits fuel rest hfuel


theorem parseViewMessageBody_sound (fuel : ℕ) (bits message rest : List Bool)
    (h : parseViewMessageBody fuel bits = some (message, rest)) :
    message.flatMap viewBoolCode ++ [true] ++ rest = bits := by
  induction fuel, bits using parseViewMessageBody.induct generalizing message rest with
  | case1 bits => simp [parseViewMessageBody] at h
  | case2 fuel suffix =>
    have heq : ([], suffix) = (message, rest) := Option.some.inj h
    cases heq
    rfl
  | case3 fuel suffix ih =>
    cases hp : parseViewMessageBody fuel suffix with
    | none => simp [parseViewMessageBody, hp] at h
    | some result =>
      rcases result with ⟨xs, ys⟩
      have heq : (false :: xs, ys) = (message, rest) := by
        simpa [parseViewMessageBody, hp] using h
      cases heq
      simpa [viewBoolCode, List.append_assoc] using
        congrArg (fun bs => false :: true :: bs) (ih xs _ hp)
  | case4 fuel suffix ih =>
    cases hp : parseViewMessageBody fuel suffix with
    | none => simp [parseViewMessageBody, hp] at h
    | some result =>
      rcases result with ⟨xs, ys⟩
      have heq : (true :: xs, ys) = (message, rest) := by
        simpa [parseViewMessageBody, hp] using h
      cases heq
      simpa [viewBoolCode, List.append_assoc] using
        congrArg (fun bs => false :: false :: true :: true :: bs) (ih xs _ hp)
  | case5 fuel bits _ _ _ => simp [parseViewMessageBody] at h

/-- Parse a transcript body after its opening bracket. -/
def parseViewTranscriptBody : ℕ → List Bool → Option (List (List Bool) × List Bool)
  | 0, _ => none
  | _ + 1, true :: rest => some ([], rest)
  | fuel + 1, false :: bits => do
      let first ← parseViewMessageBody fuel bits
      let remaining ← parseViewTranscriptBody fuel first.2
      return (first.1 :: remaining.1, remaining.2)
  | _ + 1, [] => none

/-- Parse one bracketed transcript, preserving an optional following suffix. -/
def parseViewTranscript (fuel : ℕ) : List Bool → Option (List (List Bool) × List Bool)
  | false :: rest => parseViewTranscriptBody fuel rest
  | _ => none

theorem parseViewTranscriptBody_encode (history : List (List Bool)) (fuel : ℕ) (rest : List Bool)
    (hfuel : (encodeViewTranscript history).length ≤ fuel) :
    parseViewTranscriptBody fuel (history.flatMap encodeViewMessage ++ [true] ++ rest) =
      some (history, rest) := by
  induction history generalizing fuel with
  | nil =>
    cases fuel <;> simp_all [encodeViewTranscript, parseViewTranscriptBody]
  | cons message history ih =>
    cases fuel with
    | zero => simp [encodeViewTranscript] at hfuel
    | succ fuel =>
      have hm := length_encodeViewMessage_ge message
      have hf : message.length + 1 ≤ fuel := by
        simp only [encodeViewTranscript, List.flatMap_cons, List.length_cons,
          List.length_append, List.length_nil] at hfuel
        omega
      have ht : (encodeViewTranscript history).length ≤ fuel := by
        simp only [encodeViewTranscript, List.flatMap_cons, List.length_cons,
          List.length_append, List.length_nil] at hfuel ⊢
        omega
      have hfirst := parseViewMessageBody_encode message fuel
        (history.flatMap encodeViewMessage ++ [true] ++ rest) hf
      have htail := ih fuel ht
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hfirst htail
      simp only [List.flatMap_cons, encodeViewMessage, List.cons_append,
        List.append_assoc, List.nil_append, parseViewTranscriptBody]
      rw [hfirst]
      simp [htail]

theorem parseViewTranscript_encode (history : List (List Bool)) (fuel : ℕ) (rest : List Bool)
    (hfuel : (encodeViewTranscript history).length ≤ fuel) :
    parseViewTranscript fuel (encodeViewTranscript history ++ rest) = some (history, rest) := by
  simpa [encodeViewTranscript, parseViewTranscript, List.append_assoc] using
    parseViewTranscriptBody_encode history fuel rest hfuel

theorem parseViewTranscriptBody_sound (fuel : ℕ) (bits : List Bool)
    (history : List (List Bool)) (rest : List Bool)
    (h : parseViewTranscriptBody fuel bits = some (history, rest)) :
    history.flatMap encodeViewMessage ++ [true] ++ rest = bits := by
  induction fuel generalizing bits history rest with
  | zero => simp [parseViewTranscriptBody] at h
  | succ fuel ih =>
    cases bits with
    | nil => simp [parseViewTranscriptBody] at h
    | cons b bits =>
      cases b with
      | true =>
        have heq : ([], bits) = (history, rest) := Option.some.inj h
        cases heq
        rfl
      | false =>
        cases hm : parseViewMessageBody fuel bits with
        | none => simp [parseViewTranscriptBody, hm] at h
        | some message =>
          rcases message with ⟨xs, suffix⟩
          cases ht : parseViewTranscriptBody fuel suffix with
          | none => simp [parseViewTranscriptBody, hm, ht] at h
          | some tail =>
            rcases tail with ⟨messages, ending⟩
            have heq : (xs :: messages, ending) = (history, rest) := by
              simpa [parseViewTranscriptBody, hm, ht] using h
            cases heq
            have hmessage := parseViewMessageBody_sound fuel bits xs suffix hm
            rw [← ih suffix messages _ ht] at hmessage
            simpa [encodeViewMessage, List.append_assoc] using
              congrArg (List.cons false) hmessage

theorem parseViewTranscript_sound (fuel : ℕ) (bits : List Bool)
    (history : List (List Bool)) (rest : List Bool)
    (h : parseViewTranscript fuel bits = some (history, rest)) :
    encodeViewTranscript history ++ rest = bits := by
  cases bits with
  | nil => simp [parseViewTranscript] at h
  | cons b bits =>
    cases b with
    | true => simp [parseViewTranscript] at h
    | false =>
      simpa [encodeViewTranscript, List.append_assoc] using
        congrArg (List.cons false) (parseViewTranscriptBody_sound fuel bits history rest h)

/-- Canonical transcript decoding requires full consumption. -/
def decodeViewTranscript (bits : List Bool) : Option (List (List Bool)) := do
  let result ← parseViewTranscript bits.length bits
  if result.2 = [] then some result.1 else none

@[simp] theorem decodeViewTranscript_encode (history : List (List Bool)) :
    decodeViewTranscript (encodeViewTranscript history) = some history := by
  have h := parseViewTranscript_encode history (encodeViewTranscript history).length [] le_rfl
  simp only [List.append_nil] at h
  simp [decodeViewTranscript, h]

theorem decodeViewTranscript_sound (bits : List Bool) (history : List (List Bool))
    (h : decodeViewTranscript bits = some history) : encodeViewTranscript history = bits := by
  cases hp : parseViewTranscript bits.length bits with
  | none => simp [decodeViewTranscript, hp] at h
  | some result =>
    rcases result with ⟨messages, rest⟩
    by_cases hr : rest = []
    · subst rest
      have heq : messages = history := by simpa [decodeViewTranscript, hp] using h
      subst messages
      simpa using parseViewTranscript_sound bits.length bits history [] hp
    · simp [decodeViewTranscript, hp, hr] at h

/-- The three components supplied to upstream's verifier procedures. -/
structure DecodedProtocolView where
  input : List Bool
  coins : List Bool
  transcript : List (List Bool)
  deriving DecidableEq

/-- Concrete bit-for-bit source equation of upstream `protocolView`. -/
def encodeProtocolView (input coins : List Bool) (history : List (List Bool)) : List Bool :=
  viewPair (viewPair input coins) (encodeViewTranscript history)

/-- Validate both pair delimiters and the complete parenthesized transcript. -/
def decodeProtocolView (bits : List Bool) : Option DecodedProtocolView := do
  let outer ← parseViewPair bits
  let inner ← parseViewPair outer.1
  let history ← decodeViewTranscript outer.2
  return ⟨inner.1, inner.2, history⟩

@[simp] theorem decodeProtocolView_encode (input coins : List Bool) (history : List (List Bool)) :
    decodeProtocolView (encodeProtocolView input coins history) = some ⟨input, coins, history⟩ := by
  simp [decodeProtocolView, encodeProtocolView]

theorem decodeProtocolView_sound (bits : List Bool) (view : DecodedProtocolView)
    (h : decodeProtocolView bits = some view) :
    encodeProtocolView view.input view.coins view.transcript = bits := by
  cases ho : parseViewPair bits with
  | none => simp [decodeProtocolView, ho] at h
  | some outer =>
    rcases outer with ⟨first, transcript⟩
    cases hi : parseViewPair first with
    | none => simp [decodeProtocolView, ho, hi] at h
    | some inner =>
      rcases inner with ⟨input, coins⟩
      cases ht : decodeViewTranscript transcript with
      | none => simp [decodeProtocolView, ho, hi, ht] at h
      | some history =>
        have heq : (⟨input, coins, history⟩ : DecodedProtocolView) = view := by
          simpa [decodeProtocolView, ho, hi, ht] using h
        subst view
        rw [encodeProtocolView, parseViewPair_sound first input coins hi,
          decodeViewTranscript_sound transcript history ht, parseViewPair_sound bits first transcript ho]

theorem decodeProtocolView_eq_some_iff (bits : List Bool) (view : DecodedProtocolView) :
    decodeProtocolView bits = some view ↔
      encodeProtocolView view.input view.coins view.transcript = bits := by
  constructor
  · exact decodeProtocolView_sound bits view
  · rintro rfl
    exact decodeProtocolView_encode _ _ _

@[simp] theorem length_encodeProtocolView (input coins : List Bool)
    (history : List (List Bool)) :
    (encodeProtocolView input coins history).length =
      4 * input.length + 2 * coins.length + 6 + (encodeViewTranscript history).length := by
  simp only [encodeProtocolView, length_viewPair]
  omega

theorem input_length_le_encodeProtocolView (input coins : List Bool)
    (history : List (List Bool)) :
    input.length ≤ (encodeProtocolView input coins history).length := by
  rw [length_encodeProtocolView]
  omega

theorem decodeProtocolView_input_length_le (bits : List Bool) (view : DecodedProtocolView)
    (h : decodeProtocolView bits = some view) : view.input.length ≤ bits.length := by
  rw [← decodeProtocolView_sound bits view h]
  exact input_length_le_encodeProtocolView _ _ _

/-- Turn any total three-argument message procedure into a total procedure on
upstream-compatible views. Malformed views receive the empty message. -/
def packViewMessage
    (message : List Bool → List Bool → List (List Bool) → List Bool)
    (bits : List Bool) : List Bool :=
  match decodeProtocolView bits with
  | none => []
  | some view => message view.input view.coins view.transcript

/-- Turn any total three-argument verdict into a total predicate on views.
Malformed views are rejected. -/
def packViewVerdict
    (verdict : List Bool → List Bool → List (List Bool) → Bool)
    (bits : List Bool) : Bool :=
  match decodeProtocolView bits with
  | none => false
  | some view => verdict view.input view.coins view.transcript

@[simp] theorem packViewMessage_encode
    (message : List Bool → List Bool → List (List Bool) → List Bool)
    (input coins : List Bool) (history : List (List Bool)) :
    packViewMessage message (encodeProtocolView input coins history) =
      message input coins history := by
  simp [packViewMessage]

@[simp] theorem packViewVerdict_encode
    (verdict : List Bool → List Bool → List (List Bool) → Bool)
    (input coins : List Bool) (history : List (List Bool)) :
    packViewVerdict verdict (encodeProtocolView input coins history) =
      verdict input coins history := by
  simp [packViewVerdict]

theorem packViewMessage_invalid
    (message : List Bool → List Bool → List (List Bool) → List Bool)
    (bits : List Bool) (h : decodeProtocolView bits = none) :
    packViewMessage message bits = [] := by
  simp [packViewMessage, h]

theorem packViewVerdict_invalid
    (verdict : List Bool → List Bool → List (List Bool) → Bool)
    (bits : List Bool) (h : decodeProtocolView bits = none) :
    packViewVerdict verdict bits = false := by
  simp [packViewVerdict, h]

/-- The upstream all-view bound is preserved, with no restrictions on coins or
on whether the history can arise in an interaction. -/
theorem packViewMessage_length_le
    (message : List Bool → List Bool → List (List Bool) → List Bool)
    (bound : ℕ → ℕ)
    (hbound : ∀ input coins history, (message input coins history).length ≤ bound input.length)
    (input coins : List Bool) (history : List (List Bool)) :
    (packViewMessage message (encodeProtocolView input coins history)).length ≤
      bound input.length := by
  simpa only [packViewMessage_encode] using hbound input coins history

/-- For arbitrary single strings, a monotone input bound also bounds output in
the size of the entire view, including malformed encodings. -/
theorem packViewMessage_length_le_view_length
    (message : List Bool → List Bool → List (List Bool) → List Bool)
    (bound : ℕ → ℕ) (hmono : Monotone bound)
    (hbound : ∀ input coins history, (message input coins history).length ≤ bound input.length)
    (bits : List Bool) : (packViewMessage message bits).length ≤ bound bits.length := by
  cases h : decodeProtocolView bits with
  | none => simp [packViewMessage, h]
  | some view =>
    simp only [packViewMessage, h]
    exact (hbound _ _ _).trans (hmono (decodeProtocolView_input_length_le bits view h))

/-- Single-bitstring verifier message, in upstream's encoded-view format. -/
def viewVerifierMessage : List Bool → List Bool := packViewMessage rawVerifierMessage

/-- Single-bitstring final verdict, in upstream's encoded-view format. -/
def viewTranscriptVerdict : List Bool → Bool := packViewVerdict rawTranscriptVerdict

@[simp] theorem viewVerifierMessage_encode (input coins : List Bool)
    (history : List (List Bool)) :
    viewVerifierMessage (encodeProtocolView input coins history) =
      rawVerifierMessage input coins history := packViewMessage_encode _ _ _ _

@[simp] theorem viewTranscriptVerdict_encode (input coins : List Bool)
    (history : List (List Bool)) :
    viewTranscriptVerdict (encodeProtocolView input coins history) =
      rawTranscriptVerdict input coins history := packViewVerdict_encode _ _ _ _

/-- This is the all-view message-bound shape required by upstream `Protocol`. -/
theorem viewVerifierMessage_length_le (input coins : List Bool)
    (history : List (List Bool)) :
    (viewVerifierMessage (encodeProtocolView input coins history)).length ≤
      messageResourcePolynomial.eval input.length := by
  simpa only [viewVerifierMessage_encode] using rawVerifierMessage_length_le input coins history

theorem viewVerifierMessage_length_le_view_length (bits : List Bool) :
    (viewVerifierMessage bits).length ≤ messageResourcePolynomial.eval bits.length := by
  apply packViewMessage_length_le_view_length rawVerifierMessage
    (fun n => messageResourcePolynomial.eval n) _ rawVerifierMessage_length_le bits
  intro a b hab
  simp only [messageResourcePolynomial_eval]
  gcongr

/-- Execute using only the single-list message/verdict procedures. The prover
still sees the raw alternating transcript, as in the upstream interface. -/
def viewProtocolExecution (S : List (List Bool) → List Bool) (input coins : List Bool) : Bool :=
  viewTranscriptVerdict (encodeProtocolView input coins
    (interactionTranscript S (fun history =>
      viewVerifierMessage (encodeProtocolView input coins history)) (encodedRoundBudget input)))

theorem viewProtocolExecution_eq_rawProtocolExecution
    (S : List (List Bool) → List Bool) (input coins : List Bool) :
    viewProtocolExecution S input coins = rawProtocolExecution S input coins := by
  simp [viewProtocolExecution, rawProtocolExecution]

@[simp] theorem viewProtocolExecution_ofFn (S : List (List Bool) → List Bool)
    (input : List Bool) (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    viewProtocolExecution S input (List.ofFn tape) = verifyEncodedProtocol S input tape := by
  rw [viewProtocolExecution_eq_rawProtocolExecution, rawProtocolExecution_ofFn]

noncomputable section

open scoped Classical

/-- Perfect completeness of the single-list procedures with a globally bounded
prover and the exact private-coin budget. -/
theorem viewProtocolExecution_complete (input : List Bool) (htrue : EncodedTruePrenex input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤ messageResourcePolynomial.eval input.length) ∧
      ∀ tape : Fin (coinResourcePolynomial.eval input.length) → Bool,
        viewProtocolExecution S input (List.ofFn tape) = true := by
  simpa only [viewProtocolExecution_ofFn] using verifyEncodedProtocol_complete input htrue

/-- Rational soundness for arbitrary adaptive provers is unchanged by the
source-compatible view codec. No polynomial-time certificate is asserted. -/
theorem viewProtocolExecution_counting_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTruePrenex input) :
    ((Finset.univ.filter fun tape : Fin (coinResourcePolynomial.eval input.length) → Bool =>
      viewProtocolExecution S input (List.ofFn tape) = true).card : ℚ) /
      2 ^ (coinResourcePolynomial.eval input.length) ≤ 1 / 3 := by
  simpa only [viewProtocolExecution_ofFn] using
    verifyEncodedProtocol_counting_soundness S input hfalse

end

end IPPSPACE

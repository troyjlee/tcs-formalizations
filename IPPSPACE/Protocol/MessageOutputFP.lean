/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MessageParsingFP
import Complexitylib.Classes.P.DataEncode
import Complexitylib.Classes.P.Range

/-!
# Polynomial-time encoded output of the coefficient parser

Successful coefficient lists are represented by upstream's canonical
`DataEncode` encoding of the list of their fixed-width residue words. Failure
is the empty bitstring, distinct from the encoding of an empty coefficient
list. The construction agrees with the existing `parseMessage` on every input,
including modulus zero, malformed words, and excessive coefficient counts.

The actual upstream `FP` certificate constructs this encoded list; it does not
certify Horner iteration or the complete interactive verifier.
-/

namespace IPPSPACE

open Complexity

/-- Split into complete fixed-width words. A trailing partial word is ignored
here; `parseMessageOutput` first validates the entire input. -/
def messageWords (p : ℕ) (bits : List Bool) : List (List Bool) :=
  (List.range (bits.length / residueWidth p)).map (fun i => messageWordBits p i bits)

@[simp] theorem messageWords_nil (p : ℕ) : messageWords p [] = [] := by
  simp [messageWords]

private theorem messageWordBits_prepend_succ' (p i : ℕ) (word rest : List Bool)
    (hlen : word.length = residueWidth p) :
    messageWordBits p (i + 1) (word ++ rest) = messageWordBits p i rest := by
  simp only [messageWordBits, Nat.add_mul, Nat.one_mul]
  rw [Nat.add_comm (i * residueWidth p), ← hlen, ← List.drop_drop, List.drop_left]

/-- Splitting a canonical coefficient message recovers every encoded word in
order. This syntactic fact does not require a nonzero modulus. -/
theorem messageWords_encodeMessage {p : ℕ} (as : List (ZMod p)) :
    messageWords p (encodeMessage as) = as.map (fun a => wordBits (encodeResidue a)) := by
  have hw : 0 < residueWidth p := by simp [residueWidth]
  have hcount (as : List (ZMod p)) : (encodeMessage as).length / residueWidth p = as.length := by
    rw [length_encodeMessage, Nat.mul_div_cancel _ hw]
  simp only [messageWords, hcount]
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      encodeMessage, List.map_cons]
    have hfirst : messageWordBits p 0 (wordBits (encodeResidue a) ++ encodeMessage as) =
        wordBits (encodeResidue a) := by
      simp only [messageWordBits, Nat.zero_mul, List.drop_zero,
        ← length_wordBits (encodeResidue a), List.take_left]
    rw [hfirst]
    congr 1
    have htail : ((fun i => messageWordBits p i
        (wordBits (encodeResidue a) ++ encodeMessage as)) ∘ Nat.succ) =
        (fun i => messageWordBits p i (encodeMessage as)) := by
      funext i
      exact messageWordBits_prepend_succ' p i _ _ (length_wordBits _)
    rw [htail]
    exact ih

/-- Direct indexed access to the original parser's canonical coefficient
message, useful for bounded arithmetic folds over raw message bits. -/
theorem messageWordBits_encodeMessage_getElem {p : ℕ} (as : List (ZMod p))
    (i : ℕ) (hi : i < as.length) :
    messageWordBits p i (encodeMessage as) = wordBits (encodeResidue as[i]) := by
  have hw : 0 < residueWidth p := by simp [residueWidth]
  have h := congrArg (fun words : List (List Bool) => words[i]?) (messageWords_encodeMessage as)
  simpa [messageWords, length_encodeMessage, Nat.mul_div_cancel _ hw, hi] using h

/-- Canonical upstream data encoding for a list of field coefficients, using
fixed-width word payloads rather than unary coefficient values. -/
def encodeParsedCoefficients {p : ℕ} (as : List (ZMod p)) : List Bool :=
  DataEncode.bitstringEncode (as.map (fun a => wordBits (encodeResidue a)))

theorem encodeParsedCoefficients_ne_nil {p : ℕ} (as : List (ZMod p)) :
    encodeParsedCoefficients as ≠ [] := by
  simp [encodeParsedCoefficients, DataEncode.bitstringEncode_list]

/-- Distinct field coefficient lists have distinct serialized outputs. The
nonzero hypothesis is essential for canonical `ZMod` residue encodings. -/
theorem encodeParsedCoefficients_injective {p : ℕ} [NeZero p] :
    Function.Injective (@encodeParsedCoefficients p) := by
  have hword : Function.Injective (fun a : ZMod p => wordBits (encodeResidue a)) := by
    intro a b h
    apply ZMod.val_injective p
    simpa using congrArg Nat.fromBits h
  intro as bs h
  exact (List.map_injective_iff.mpr hword) (DataEncode.bitstringEncode_injective h)

/-- A total encoded parser output. Invalid inputs yield `[]`; successful empty
messages yield the distinct bracketed encoding of an empty list. -/
def parseMessageOutput (p limit : ℕ) (bits : List Bool) : List Bool :=
  if validateMessageBits p limit bits then DataEncode.bitstringEncode (messageWords p bits) else []

/-- Exact agreement with the existing coefficient parser, for every modulus.
The output represents all decoded coefficients, not only the success flag. -/
theorem parseMessageOutput_eq (p limit : ℕ) (bits : List Bool) :
    parseMessageOutput p limit bits =
      match parseMessage p limit bits with
      | none => []
      | some as => encodeParsedCoefficients as := by
  unfold parseMessageOutput
  rw [validateMessageBits_eq_parseMessage_isSome]
  cases hparse : parseMessage p limit bits with
  | none => rfl
  | some as =>
    simp only [Option.isSome_some, ↓reduceIte]
    by_cases hp : p = 0
    · subst p
      have hnil : bits = [] := (parseMessage_zero_modulus_isSome limit bits).mp (by simp [hparse])
      subst bits
      have has : as = [] := by simpa using hparse.symm
      subst as
      simp [encodeParsedCoefficients]
    · let : NeZero p := ⟨hp⟩
      obtain ⟨hencode, _⟩ := parseMessage_sound limit bits as hparse
      rw [← hencode, messageWords_encodeMessage]
      rfl

@[simp] theorem parseMessageOutput_nil (p limit : ℕ) :
    parseMessageOutput p limit [] = DataEncode.bitstringEncode ([] : List (List Bool)) := by
  simp [parseMessageOutput_eq, encodeParsedCoefficients]

theorem parseMessageOutput_eq_nil_iff (p limit : ℕ) (bits : List Bool) :
    parseMessageOutput p limit bits = [] ↔ parseMessage p limit bits = none := by
  rw [parseMessageOutput_eq]
  cases parseMessage p limit bits with
  | none => simp
  | some as => simp [encodeParsedCoefficients_ne_nil]

/-- A successful encoded result identifies exactly the coefficient list
returned by the existing parser, in both directions. -/
theorem parseMessageOutput_eq_encoded_iff {p : ℕ} [NeZero p] (limit : ℕ)
    (bits : List Bool) (as : List (ZMod p)) :
    parseMessageOutput p limit bits = encodeParsedCoefficients as ↔
      parseMessage p limit bits = some as := by
  rw [parseMessageOutput_eq]
  cases parseMessage p limit bits with
  | none => simp [Ne.symm (encodeParsedCoefficients_ne_nil as)]
  | some bs =>
    simp only [Option.some.injEq]
    exact encodeParsedCoefficients_injective.eq_iff

theorem parseMessageOutput_encode {p : ℕ} [NeZero p] (limit : ℕ)
    (as : List (ZMod p)) (hlimit : as.length ≤ limit) :
    parseMessageOutput p limit (encodeMessage as) = encodeParsedCoefficients as := by
  rw [parseMessageOutput_eq, parseMessage_encode limit as hlimit]

/-- Complete fixed-width chunks can be serialized using the actual upstream
range-loop and data-encoding certificates. -/
theorem messageWords_encoding_mem_FP {p : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hbits : bits ∈ FP) :
    (fun z => DataEncode.bitstringEncode (messageWords (p z) (bits z))) ∈ FP := by
  have hcount := (UnaryFn.length hbits).div (residueWidth_unaryFn hp)
  have hchunk := messageWordBits_mem_FP hp.lift UnaryFn.index
    (mem_FP_comp Cobham.fstBlock_mem_FP hbits)
  have hbody := flatMap_range_mem_FP (encodeList_mem_FP hchunk) hcount.mem_FP
  have h := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody) (constFn_mem_FP [true])
  apply mem_FP_of_eq h
  intro z
  simp [messageWords, DataEncode.bitstringEncode_list, List.flatMap_def, Function.comp_def]

/-- The full serialized result of the existing bounded coefficient parser is
in actual upstream `FP`, uniformly including all zero and malformed cases. -/
theorem parseMessageOutput_mem_FP {p limit : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hlimit : UnaryFn limit) (hbits : bits ∈ FP) :
    (fun z => parseMessageOutput (p z) (limit z) (bits z)) ∈ FP := by
  have htest := (messageBitsValid_fppred hp hlimit hbits).of_iff
    (fun _ => (validateMessageBits_eq_true _ _ _).symm)
  exact htest.ite_mem_FP (messageWords_encoding_mem_FP hp hbits) (constFn_mem_FP [])

/-- The same certificate stated directly for the encoded output of the
original parser rather than its equivalent block-slicing implementation. -/
theorem parseMessage_encodedOutput_mem_FP {p limit : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hlimit : UnaryFn limit) (hbits : bits ∈ FP) :
    (fun z => match parseMessage (p z) (limit z) (bits z) with
      | none => []
      | some as => encodeParsedCoefficients as) ∈ FP := by
  apply mem_FP_of_eq (parseMessageOutput_mem_FP hp hlimit hbits)
  intro z
  rw [parseMessageOutput_eq]
  cases parseMessage (p z) (limit z) (bits z) <;> rfl

end IPPSPACE

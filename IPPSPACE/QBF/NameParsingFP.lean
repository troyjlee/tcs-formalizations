/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.BinaryNamesFP

/-!
# Polynomial-time output of the binary-name prefix parsers

The existing fuel-bounded parsers return a name and the untouched suffix.
Their outputs are encoded by a success bit followed by upstream's `pair` of
the name's binary digits and the suffix; failure is the empty bitstring.
No unary bound on the name's numeric value is assumed.

Bounded search locates an exactly framed prefix. Indexed extraction, framing,
string equality, and suffix slicing then give actual upstream `FP`
certificates. These are prerequisites for QBF parsing, not a certificate
for the complete QBF parser or verifier.
-/

namespace IPPSPACE

open Complexity

/-- Extract the candidate digits at odd positions, keeping little-endian order.
Out-of-range access is total; the complete prefix test rejects such candidates. -/
def namePrefixDigits (count : ℕ) (bits : List Bool) : List Bool :=
  (List.range count).map (fun i => bits[2 * i + 1]?.getD false)

@[simp] theorem length_namePrefixDigits (count : ℕ) (bits : List Bool) :
    (namePrefixDigits count bits).length = count := by
  simp [namePrefixDigits]

private theorem namePrefixDigits_cons_cons (count : ℕ) (tag bit : Bool) (bits : List Bool) :
    namePrefixDigits (count + 1) (tag :: bit :: bits) = bit :: namePrefixDigits count bits := by
  simp [namePrefixDigits, List.range_succ_eq_map, List.map_map, Function.comp_def,
    Nat.mul_add]

/-- Candidate extraction recovers exactly a framed digit list before any suffix. -/
theorem namePrefixDigits_frame (digits suffix : List Bool) :
    namePrefixDigits digits.length (frameNameBits digits ++ suffix) = digits := by
  induction digits with
  | nil => rfl
  | cons bit digits ih =>
    simpa only [List.length_cons, frameNameBits, List.cons_append,
      namePrefixDigits_cons_cons] using congrArg (List.cons bit) ih

/-- The candidate consumes exactly one delimiter after its continuation/digit pairs. -/
def NamePrefixMatches (count : ℕ) (bits : List Bool) : Prop :=
  bits.take (2 * count + 1) = frameNameBits (namePrefixDigits count bits)

instance (count : ℕ) (bits : List Bool) : Decidable (NamePrefixMatches count bits) :=
  inferInstanceAs (Decidable (_ = _))

theorem namePrefixMatches_frame (digits suffix : List Bool) :
    NamePrefixMatches digits.length (frameNameBits digits ++ suffix) := by
  simp only [NamePrefixMatches, namePrefixDigits_frame]
  rw [← length_frameNameBits digits, List.take_left]

/-- Successful parsing uses one unit of fuel for every digit and for the delimiter. -/
theorem parseNameBits_length_lt {fuel : ℕ} {bits digits suffix : List Bool}
    (h : parseNameBits fuel bits = some (digits, suffix)) : digits.length < fuel := by
  induction fuel generalizing bits digits suffix with
  | zero => simp [parseNameBits] at h
  | succ fuel ih =>
    cases bits with
    | nil => simp [parseNameBits] at h
    | cons tag bits =>
      cases tag with
      | false =>
        have heq : ([], bits) = (digits, suffix) := by simpa [parseNameBits] using h
        cases heq
        simp
      | true =>
        cases bits with
        | nil => simp [parseNameBits] at h
        | cons bit bits =>
          cases hr : parseNameBits fuel bits with
          | none => simp [parseNameBits, hr] at h
          | some result =>
            rcases result with ⟨tail, rest⟩
            have heq : (bit :: tail, rest) = (digits, suffix) := by
              simpa [parseNameBits, hr] using h
            cases heq
            simpa using Nat.succ_lt_succ (ih hr)

/-- Exact fuel-sensitive characterization of the existing digit parser. -/
theorem parseNameBits_eq_some_iff (fuel : ℕ) (bits digits suffix : List Bool) :
    parseNameBits fuel bits = some (digits, suffix) ↔
      digits.length < fuel ∧ frameNameBits digits ++ suffix = bits := by
  constructor
  · intro h
    exact ⟨parseNameBits_length_lt h, parseNameBits_sound fuel bits digits suffix h⟩
  · rintro ⟨hfuel, rfl⟩
    exact parseNameBits_frame digits suffix fuel (by omega)

theorem parseNameBits_of_prefixMatches {count fuel : ℕ} {bits : List Bool}
    (hfuel : count < fuel) (hmatch : NamePrefixMatches count bits) :
    parseNameBits fuel bits =
      some (namePrefixDigits count bits, bits.drop (2 * count + 1)) := by
  apply (parseNameBits_eq_some_iff _ _ _ _).mpr
  refine ⟨by simpa using hfuel, ?_⟩
  rw [← hmatch]
  exact List.take_append_drop _ _

/-- Search only candidate digit counts permitted by the parser's fuel. -/
def namePrefixLength (fuel : ℕ) (bits : List Bool) : ℕ :=
  (List.range fuel).findIdx (fun count => decide (NamePrefixMatches count bits))

theorem namePrefixLength_lt_iff (fuel : ℕ) (bits : List Bool) :
    namePrefixLength fuel bits < fuel ↔ ∃ digits suffix, parseNameBits fuel bits = some (digits, suffix) := by
  unfold namePrefixLength
  have hfind : (List.range fuel).findIdx (fun count => decide (NamePrefixMatches count bits)) < fuel ↔
      ∃ count, count < fuel ∧ NamePrefixMatches count bits := by
    simpa only [List.length_range, List.mem_range, decide_eq_true_eq] using
      (List.findIdx_lt_length (xs := List.range fuel)
        (p := fun count => decide (NamePrefixMatches count bits)))
  rw [hfind]
  constructor
  · rintro ⟨count, hcount, hmatch⟩
    exact ⟨_, _, parseNameBits_of_prefixMatches hcount hmatch⟩
  · rintro ⟨digits, suffix, hparse⟩
    refine ⟨digits.length, parseNameBits_length_lt hparse, ?_⟩
    rw [← parseNameBits_sound fuel bits digits suffix hparse]
    exact namePrefixMatches_frame digits suffix

theorem namePrefixMatches_namePrefixLength (fuel : ℕ) (bits : List Bool)
    (h : namePrefixLength fuel bits < fuel) :
    NamePrefixMatches (namePrefixLength fuel bits) bits := by
  have hfind : (List.range fuel).findIdx (fun count => decide (NamePrefixMatches count bits)) <
      (List.range fuel).length := by simpa [namePrefixLength] using h
  have htest := List.findIdx_getElem (w := hfind)
  simpa [namePrefixLength] using htest

/-- The bounded-search implementation returns exactly the original parser's
digits and unconsumed suffix, on successful and malformed inputs alike. -/
theorem parseNameBits_eq_scan (fuel : ℕ) (bits : List Bool) :
    parseNameBits fuel bits =
      if namePrefixLength fuel bits < fuel then
        some (namePrefixDigits (namePrefixLength fuel bits) bits,
          bits.drop (2 * namePrefixLength fuel bits + 1))
      else none := by
  by_cases h : namePrefixLength fuel bits < fuel
  · rw [ite_eq_left h]
    exact parseNameBits_of_prefixMatches h (namePrefixMatches_namePrefixLength fuel bits h)
  · rw [ite_eq_right h]
    cases hparse : parseNameBits fuel bits with
    | none => rfl
    | some result =>
      exact (h ((namePrefixLength_lt_iff fuel bits).mpr ⟨result.1, result.2, hparse⟩)).elim

/-- A successful parse carries both fields; no successful result is empty. -/
def encodeNameParseResult : Option (List Bool × List Bool) → List Bool
  | none => []
  | some (digits, suffix) => true :: pair digits suffix

/-- Recover the two binary fields from the tagged result encoding. -/
def decodeNameParseResult : List Bool → Option (List Bool × List Bool)
  | true :: payload => unpair? payload
  | _ => none

@[simp] theorem decodeNameParseResult_encode (result : Option (List Bool × List Bool)) :
    decodeNameParseResult (encodeNameParseResult result) = result := by
  cases result with
  | none => rfl
  | some result =>
    rcases result with ⟨digits, suffix⟩
    simp [encodeNameParseResult, decodeNameParseResult]

theorem encodeNameParseResult_injective : Function.Injective encodeNameParseResult := by
  intro a b h
  simpa only [decodeNameParseResult_encode] using congrArg decodeNameParseResult h

def parseNameBitsOutput (fuel : ℕ) (bits : List Bool) : List Bool :=
  encodeNameParseResult (parseNameBits fuel bits)

/-- Natural-valued parser output, serialized with canonical binary digits.
The number is never expanded into unary by the runtime certificate. -/
def parseNatNameOutput (fuel : ℕ) (bits : List Bool) : List Bool :=
  match parseNatName fuel bits with
  | none => []
  | some (name, suffix) => true :: pair name.bits suffix

/-- The serialized output retains the entire existing parser result. -/
@[simp] theorem decode_parseNameBitsOutput (fuel : ℕ) (bits : List Bool) :
    decodeNameParseResult (parseNameBitsOutput fuel bits) = parseNameBits fuel bits :=
  decodeNameParseResult_encode _

/-- Natural results are recovered in binary together with the original suffix. -/
@[simp] theorem decode_parseNatNameOutput (fuel : ℕ) (bits : List Bool) :
    decodeNameParseResult (parseNatNameOutput fuel bits) =
      (parseNatName fuel bits).map (fun result => (result.1.bits, result.2)) := by
  cases hparse : parseNatName fuel bits with
  | none => simp [parseNatNameOutput, hparse, decodeNameParseResult]
  | some result =>
    rcases result with ⟨name, suffix⟩
    simp [parseNatNameOutput, hparse, decodeNameParseResult]

theorem parseNameBitsOutput_eq_nil_iff (fuel : ℕ) (bits : List Bool) :
    parseNameBitsOutput fuel bits = [] ↔ parseNameBits fuel bits = none := by
  change encodeNameParseResult (parseNameBits fuel bits) = encodeNameParseResult none ↔ _
  exact encodeNameParseResult_injective.eq_iff

theorem parseNatNameOutput_eq_nil_iff (fuel : ℕ) (bits : List Bool) :
    parseNatNameOutput fuel bits = [] ↔ parseNatName fuel bits = none := by
  cases hparse : parseNatName fuel bits <;> simp [parseNatNameOutput, hparse]

theorem parseNameBitsOutput_frame (digits suffix : List Bool) (fuel : ℕ)
    (hfuel : digits.length + 1 ≤ fuel) :
    parseNameBitsOutput fuel (frameNameBits digits ++ suffix) = true :: pair digits suffix := by
  rw [parseNameBitsOutput, parseNameBits_frame _ _ _ hfuel]
  rfl

theorem parseNatNameOutput_encode (name fuel : ℕ) (suffix : List Bool)
    (hfuel : name.bits.length + 1 ≤ fuel) :
    parseNatNameOutput fuel (encodeNatName name ++ suffix) = true :: pair name.bits suffix := by
  rw [parseNatNameOutput, parseNatName_encode _ _ _ hfuel]

theorem namePrefixDigits_mem_FP {count : List Bool → ℕ} {bits : List Bool → List Bool}
    (hcount : UnaryFn count) (hbits : bits ∈ FP) :
    (fun z => namePrefixDigits (count z) (bits z)) ∈ FP := by
  have hbit := getBit_mem_FP (mem_FP_comp pairFst_mem_FP hbits)
    (((UnaryFn.const 2).mul UnaryFn.index).add (UnaryFn.const 1))
  apply bitwise_mem_FP hcount.mem_FP hbit
  intro z i
  simp

theorem namePrefixMatches_fppred {count : List Bool → ℕ} {bits : List Bool → List Bool}
    (hcount : UnaryFn count) (hbits : bits ∈ FP) :
    FPPred fun z => NamePrefixMatches (count z) (bits z) :=
  bitStrings_eq_fppred
    (take_mem_FP hbits (((UnaryFn.const 2).mul hcount).add (UnaryFn.const 1)))
    (frameNameBits_mem_FP (namePrefixDigits_mem_FP hcount hbits))

theorem namePrefixLength_unaryFn {fuel : List Bool → ℕ} {bits : List Bool → List Bool}
    (hfuel : UnaryFn fuel) (hbits : bits ∈ FP) :
    UnaryFn fun z => namePrefixLength (fuel z) (bits z) := by
  have htest := namePrefixMatches_fppred UnaryFn.index (mem_FP_comp pairFst_mem_FP hbits)
  exact (hfuel.find htest).of_eq (fun z => by simp [namePrefixLength])

/-- The complete digit/suffix result of the existing parser is in upstream FP. -/
theorem parseNameBitsOutput_mem_FP {fuel : List Bool → ℕ} {bits : List Bool → List Bool}
    (hfuel : UnaryFn fuel) (hbits : bits ∈ FP) :
    (fun z => parseNameBitsOutput (fuel z) (bits z)) ∈ FP := by
  have hcount := namePrefixLength_unaryFn hfuel hbits
  have hdigits := namePrefixDigits_mem_FP hcount hbits
  have hsuffix := drop_mem_FP hbits (((UnaryFn.const 2).mul hcount).add (UnaryFn.const 1))
  have hpacked := mem_FP_comp (mem_FP_pair hdigits hsuffix) (Cobham.cons_mem_FP true)
  have h := (FPPred.lt hcount hfuel).ite_mem_FP hpacked (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro z
  rw [parseNameBitsOutput, parseNameBits_eq_scan]
  split <;> rfl

/-- The natural-name parser is polynomial-time when its possibly very large
numeric result is kept in binary, together with the exact remaining suffix. -/
theorem parseNatNameOutput_mem_FP {fuel : List Bool → ℕ} {bits : List Bool → List Bool}
    (hfuel : UnaryFn fuel) (hbits : bits ∈ FP) :
    (fun z => parseNatNameOutput (fuel z) (bits z)) ∈ FP := by
  have hcount := namePrefixLength_unaryFn hfuel hbits
  have hdigits := namePrefixDigits_mem_FP hcount hbits
  have hsuffix := drop_mem_FP hbits (((UnaryFn.const 2).mul hcount).add (UnaryFn.const 1))
  have hpacked := mem_FP_comp (mem_FP_pair hdigits hsuffix) (Cobham.cons_mem_FP true)
  have htest := (FPPred.lt hcount hfuel).and (canonicalNameBits_fppred hdigits)
  have h := htest.ite_mem_FP hpacked (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro z
  unfold parseNatNameOutput parseNatName
  rw [parseNameBits_eq_scan]
  by_cases hfound : namePrefixLength (fuel z) (bits z) < fuel z
  · by_cases hcanonical :
        (nameBitsValue (namePrefixDigits (namePrefixLength (fuel z) (bits z)) (bits z))).bits =
          namePrefixDigits (namePrefixLength (fuel z) (bits z)) (bits z)
    · simp [hfound, hcanonical]
    · simp [hfound, hcanonical]
  · simp [hfound]

end IPPSPACE

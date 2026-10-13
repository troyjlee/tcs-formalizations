/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.NameParsingFP

/-!
# Exact polynomial-time scanning of QBF constructor tokens

A token contains one existing three-bit syntax tag and, where required, its
canonical binary variable name. Child formulas are not consumed. The scanner
returns the complete token and untouched suffix. Its encoded output is in the
actual upstream `FP` class, without a unary bound on variable names.
-/

namespace IPPSPACE

open Complexity

inductive SyntaxToken where
  | var (name : ℕ)
  | tru
  | fls
  | neg
  | conj
  | disj
  | ex (name : ℕ)
  | all (name : ℕ)
  deriving DecidableEq

def SyntaxToken.arity : SyntaxToken → ℕ
  | .var _ | .tru | .fls => 0
  | .neg | .ex _ | .all _ => 1
  | .conj | .disj => 2

def SyntaxToken.encode : SyntaxToken → List Bool
  | .var n => [false, false, false] ++ encodeNatName n
  | .tru => [false, false, true]
  | .fls => [false, true, false]
  | .neg => [false, true, true]
  | .conj => [true, false, false]
  | .disj => [true, false, true]
  | .ex n => [true, true, false] ++ encodeNatName n
  | .all n => [true, true, true] ++ encodeNatName n

theorem SyntaxToken.arity_le (token : SyntaxToken) : token.arity ≤ 2 := by
  cases token <;> simp [SyntaxToken.arity]

theorem SyntaxToken.length_encode_ge (token : SyntaxToken) : 3 ≤ token.encode.length := by
  cases token <;> simp [SyntaxToken.encode]

/-- Read exactly one constructor and its optional canonical binary name. -/
def parseSyntaxToken : List Bool → Option (SyntaxToken × List Bool)
  | false :: false :: false :: bits =>
      (parseNatName bits.length bits).map (fun result => (.var result.1, result.2))
  | false :: false :: true :: bits => some (.tru, bits)
  | false :: true :: false :: bits => some (.fls, bits)
  | false :: true :: true :: bits => some (.neg, bits)
  | true :: false :: false :: bits => some (.conj, bits)
  | true :: false :: true :: bits => some (.disj, bits)
  | true :: true :: false :: bits =>
      (parseNatName bits.length bits).map (fun result => (.ex result.1, result.2))
  | true :: true :: true :: bits =>
      (parseNatName bits.length bits).map (fun result => (.all result.1, result.2))
  | _ => none

@[simp] theorem parseSyntaxToken_encode (token : SyntaxToken) (suffix : List Bool) :
    parseSyntaxToken (token.encode ++ suffix) = some (token, suffix) := by
  have hname (n : ℕ) :
      parseNatName (encodeNatName n ++ suffix).length (encodeNatName n ++ suffix) = some (n, suffix) := by
    apply parseNatName_encode
    simp [encodeNatName, length_frameNameBits]
    omega
  simp only [List.length_append] at hname
  cases token <;> simp [SyntaxToken.encode, parseSyntaxToken, hname]

/-- Every successful scan consumes exactly the canonical encoding of its token. -/
theorem parseSyntaxToken_sound (bits suffix : List Bool) (token : SyntaxToken)
    (h : parseSyntaxToken bits = some (token, suffix)) : token.encode ++ suffix = bits := by
  cases bits with
  | nil => simp [parseSyntaxToken] at h
  | cons a bits =>
    cases bits with
    | nil => simp [parseSyntaxToken] at h
    | cons b bits =>
      cases bits with
      | nil => simp [parseSyntaxToken] at h
      | cons c bits =>
        cases a <;> cases b <;> cases c
        all_goals simp only [parseSyntaxToken] at h
        all_goals first
          | (have heq := Option.some.inj h; cases heq; rfl)
          | (cases hn : parseNatName bits.length bits with
             | none => simp [hn] at h
             | some result =>
               rcases result with ⟨name, rest⟩
               have heq := Option.some.inj (by simpa only [hn, Option.map_some] using h)
               cases heq
               simpa [SyntaxToken.encode] using
                 (parseNatName_sound bits.length bits suffix name hn))

theorem parseSyntaxToken_eq_some_iff (bits suffix : List Bool) (token : SyntaxToken) :
    parseSyntaxToken bits = some (token, suffix) ↔ token.encode ++ suffix = bits := by
  exact ⟨parseSyntaxToken_sound bits suffix token, fun h => h ▸ parseSyntaxToken_encode token suffix⟩

theorem parseSyntaxToken_suffix_length (bits suffix : List Bool) (token : SyntaxToken)
    (h : parseSyntaxToken bits = some (token, suffix)) : suffix.length + 3 ≤ bits.length := by
  have heq := congrArg List.length (parseSyntaxToken_sound bits suffix token h)
  have hlen := token.length_encode_ge
  simp only [List.length_append] at heq
  omega

def encodeSyntaxTokenResult : Option (SyntaxToken × List Bool) → List Bool
  | none => []
  | some (token, suffix) => true :: pair token.encode suffix

def parseSyntaxTokenOutput (bits : List Bool) : List Bool :=
  encodeSyntaxTokenResult (parseSyntaxToken bits)

private def namedSyntaxOutput (tag bits : List Bool) : List Bool :=
  match parseNatName bits.length bits with
  | none => []
  | some (name, suffix) => true :: pair (tag ++ encodeNatName name) suffix

private theorem namedSyntaxOutput_mem_FP (tag : List Bool) {bits : List Bool → List Bool}
    (hbits : bits ∈ FP) : (fun z => namedSyntaxOutput tag (bits z)) ∈ FP := by
  have hout := parseNatNameOutput_mem_FP (UnaryFn.length hbits) hbits
  have htail := drop_mem_FP hout (UnaryFn.const 1)
  have hdigits := mem_FP_comp htail pairFst_mem_FP
  have hsuffix := mem_FP_comp htail pairSnd_mem_FP
  have hheader := Cobham.appendFn_mem_FP (constFn_mem_FP tag) (frameNameBits_mem_FP hdigits)
  have hpacked := mem_FP_comp (mem_FP_pair hheader hsuffix) (Cobham.cons_mem_FP true)
  have htest := (FPPred.eq (UnaryFn.length hout) (UnaryFn.const 0)).not
  apply mem_FP_of_eq (htest.ite_mem_FP hpacked (constFn_mem_FP []))
  intro z
  cases hp : parseNatName (bits z).length (bits z) with
  | none => simp [namedSyntaxOutput, parseNatNameOutput, hp]
  | some result =>
    rcases result with ⟨name, suffix⟩
    simp [namedSyntaxOutput, parseNatNameOutput, hp, encodeNatName]

private theorem parseSyntaxTokenOutput_eq (bits : List Bool) :
    parseSyntaxTokenOutput bits =
      if bits.take 3 = [false, false, false] then namedSyntaxOutput [false, false, false] (bits.drop 3)
      else if bits.take 3 = [false, false, true] then true :: pair [false, false, true] (bits.drop 3)
      else if bits.take 3 = [false, true, false] then true :: pair [false, true, false] (bits.drop 3)
      else if bits.take 3 = [false, true, true] then true :: pair [false, true, true] (bits.drop 3)
      else if bits.take 3 = [true, false, false] then true :: pair [true, false, false] (bits.drop 3)
      else if bits.take 3 = [true, false, true] then true :: pair [true, false, true] (bits.drop 3)
      else if bits.take 3 = [true, true, false] then namedSyntaxOutput [true, true, false] (bits.drop 3)
      else if bits.take 3 = [true, true, true] then namedSyntaxOutput [true, true, true] (bits.drop 3)
      else [] := by
  cases bits with
  | nil => rfl
  | cons a bits =>
    cases bits with
    | nil => cases a <;> rfl
    | cons b bits =>
      cases bits with
      | nil => cases a <;> cases b <;> rfl
      | cons c bits =>
        cases a <;> cases b <;> cases c <;>
          simp [parseSyntaxTokenOutput, parseSyntaxToken, encodeSyntaxTokenResult, namedSyntaxOutput]
        all_goals cases parseNatName bits.length bits <;> rfl

/-- Actual FP for the complete constructor/name/suffix output on every input. -/
theorem parseSyntaxTokenOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => parseSyntaxTokenOutput (bits z)) ∈ FP := by
  have hprefix := take_mem_FP hbits (UnaryFn.const 3)
  have hsuffix := drop_mem_FP hbits (UnaryFn.const 3)
  have htag (tag : List Bool) := bitStrings_eq_fppred hprefix (constFn_mem_FP tag)
  have hplain (tag : List Bool) :=
    mem_FP_comp (mem_FP_pair (constFn_mem_FP tag) hsuffix) (Cobham.cons_mem_FP true)
  have h := (htag [false, false, false]).ite_mem_FP (namedSyntaxOutput_mem_FP [false, false, false] hsuffix)
    ((htag [false, false, true]).ite_mem_FP (hplain [false, false, true])
    ((htag [false, true, false]).ite_mem_FP (hplain [false, true, false])
    ((htag [false, true, true]).ite_mem_FP (hplain [false, true, true])
    ((htag [true, false, false]).ite_mem_FP (hplain [true, false, false])
    ((htag [true, false, true]).ite_mem_FP (hplain [true, false, true])
    ((htag [true, true, false]).ite_mem_FP (namedSyntaxOutput_mem_FP [true, true, false] hsuffix)
    ((htag [true, true, true]).ite_mem_FP (namedSyntaxOutput_mem_FP [true, true, true] hsuffix)
      (constFn_mem_FP []))))))))
  exact mem_FP_of_eq h (fun z => (parseSyntaxTokenOutput_eq (bits z)).symm)

/-- Child count from the three constructor bits. Malformed short inputs use a
total default; token success is checked separately. -/
def syntaxTokenArity (bits : List Bool) : ℕ :=
  if bits[0]?.getD false then (if bits[1]?.getD false then 1 else 2)
  else if bits[1]?.getD false && bits[2]?.getD false then 1 else 0

theorem syntaxTokenArity_encode (token : SyntaxToken) (suffix : List Bool) :
    syntaxTokenArity (token.encode ++ suffix) = token.arity := by
  cases token <;> simp [syntaxTokenArity, SyntaxToken.encode, SyntaxToken.arity]

theorem syntaxTokenArity_eq (bits suffix : List Bool) (token : SyntaxToken)
    (h : parseSyntaxToken bits = some (token, suffix)) : syntaxTokenArity bits = token.arity := by
  rw [← parseSyntaxToken_sound bits suffix token h, syntaxTokenArity_encode]

theorem syntaxTokenArity_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => syntaxTokenArity (bits z) := by
  have hbit (i : ℕ) := FPPred.getBit hbits (UnaryFn.const i)
  have h := UnaryFn.ite (hbit 0)
    (UnaryFn.ite (hbit 1) (UnaryFn.const 1) (UnaryFn.const 2))
    (UnaryFn.ite ((hbit 1).and (hbit 2)) (UnaryFn.const 1) (UnaryFn.const 0))
  exact h.of_eq (fun z => by simp [syntaxTokenArity])

/-- The token's unconsumed suffix, with an empty fallback on failure. -/
def syntaxTokenSuffix (bits : List Bool) : List Bool := pairSnd ((parseSyntaxTokenOutput bits).drop 1)

theorem syntaxTokenSuffix_eq (bits suffix : List Bool) (token : SyntaxToken)
    (h : parseSyntaxToken bits = some (token, suffix)) : syntaxTokenSuffix bits = suffix := by
  simp [syntaxTokenSuffix, parseSyntaxTokenOutput, encodeSyntaxTokenResult, h]

theorem syntaxTokenSuffix_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxTokenSuffix (bits z)) ∈ FP :=
  mem_FP_comp (drop_mem_FP (parseSyntaxTokenOutput_mem_FP hbits) (UnaryFn.const 1)) pairSnd_mem_FP

theorem parseSyntaxToken_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (parseSyntaxToken (bits z)).isSome = true := by
  refine ((FPPred.eq (UnaryFn.length (parseSyntaxTokenOutput_mem_FP hbits)) (UnaryFn.const 0)).not).of_iff
    (fun z => ?_)
  cases hp : parseSyntaxToken (bits z) <;> simp [parseSyntaxTokenOutput, encodeSyntaxTokenResult, hp]

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.SyntaxTraversalFP

/-!
# Polynomial-time extraction of immediate syntax children

The pending-slot scanner splits the first complete formula from an arbitrary
suffix. Its result agrees with the existing prefix parser. Immediate-child
extraction additionally validates the whole parent encoding, so malformed and
trailing parent inputs return the empty fallback. Variable names remain binary.
-/

namespace IPPSPACE

open Complexity

/-- The length-fuel scanner stops at the end of one formula, preserving every
bit of the suffix. -/
theorem scanSyntax_prefix_encode (formula : QBF) (suffix : List Bool) :
    scanSyntax (encodeQBF formula ++ suffix).length 1 (encodeQBF formula ++ suffix) =
      some (nodeCount formula, suffix) := by
  have hlen : nodeCount formula ≤ (encodeQBF formula ++ suffix).length :=
    (nodeCount_le_length_encodeQBF formula).trans (by simp)
  have h := scanSyntax_encode formula
    ((encodeQBF formula ++ suffix).length - nodeCount formula) 0 suffix
  rw [Nat.add_sub_of_le hlen] at h
  simpa only [Nat.zero_add, scanSyntax_zero_pending, Option.map_some] using h

/-- Exact prefix-parser agreement, without imposing full input consumption. -/
theorem scanSyntax_prefix_eq_parseQBF (bits : List Bool) :
    scanSyntax bits.length 1 bits =
      (parseQBF bits.length bits).map (fun result => (nodeCount result.1, result.2)) := by
  cases hp : parseQBF bits.length bits with
  | none =>
    cases hs : scanSyntax bits.length 1 bits with
    | none => rfl
    | some result =>
      rcases result with ⟨count, suffix⟩
      obtain ⟨formulas, hlen, hbytes, _⟩ := scanSyntax_sound bits.length 1 bits suffix count hs
      cases formulas with
      | nil => simp at hlen
      | cons formula rest =>
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst rest
        have hbytes' : encodeQBF formula ++ suffix = bits := by simpa using hbytes
        have hparse := parseQBF_encode formula bits.length suffix
          (by rw [← hbytes']; simp)
        rw [hbytes', hp] at hparse
        contradiction
  | some result =>
    rcases result with ⟨formula, suffix⟩
    have hbytes := parseQBF_sound bits.length bits suffix formula hp
    rw [← hbytes, scanSyntax_prefix_encode]
    rfl

/-- Successful scanner completion permits an untouched trailing suffix. -/
def SyntaxStatePrefixComplete (bits : List Bool) : Prop :=
  bits ≠ [] ∧ syntaxStatePending bits = 0

instance (bits : List Bool) : Decidable (SyntaxStatePrefixComplete bits) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem syntaxStatePrefixComplete_nil : ¬ SyntaxStatePrefixComplete [] := by
  simp [SyntaxStatePrefixComplete]

@[simp] theorem syntaxStatePrefixComplete_encode (state : SyntaxScanState) :
    SyntaxStatePrefixComplete (encodeSyntaxScanState (some state)) ↔ state.pending = 0 := by
  unfold SyntaxStatePrefixComplete
  rw [syntaxStatePending_encode]
  simp [encodeSyntaxScanState]

theorem syntaxStatePrefixComplete_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => SyntaxStatePrefixComplete (bits z) :=
  ((FPPred.eq (UnaryFn.length hbits) (UnaryFn.const 0)).not).and
    (FPPred.eq (syntaxStatePending_unaryFn hbits) (UnaryFn.const 0)) |>.of_iff (fun _ => by
      simp only [SyntaxStatePrefixComplete, List.length_eq_zero_iff])

theorem scanSyntax_prefix_eq_state (bits : List Bool) :
    scanSyntax bits.length 1 bits =
      if SyntaxStatePrefixComplete (syntaxScanStateRun bits.length 1 bits) then
        some (syntaxStateCount (syntaxScanStateRun bits.length 1 bits),
          syntaxStateRemaining (syntaxScanStateRun bits.length 1 bits)) else none := by
  have hscan := syntaxScannerResult_iterate bits.length 1 0 bits
  have hscan' : syntaxScannerResult
      (syntaxScannerStep^[bits.length] (some ⟨1, 0, bits⟩)) =
      scanSyntax bits.length 1 bits := by
    rw [hscan]
    cases scanSyntax bits.length 1 bits with
    | none => rfl
    | some result => cases result; simp only [Option.map_some, Nat.zero_add]
  rw [← hscan']
  unfold syntaxScanStateRun
  cases syntaxScannerStep^[bits.length] (some ⟨1, 0, bits⟩) with
  | none => simp [syntaxScannerResult, encodeSyntaxScanState]
  | some state =>
    simp only [syntaxScannerResult, syntaxStatePrefixComplete_encode,
      syntaxStateCount_encode, syntaxStateRemaining_encode]

/-- Tagged serialization of the original prefix parser: failure is `[]`, and
success is `true :: pair encodedFormula untouchedSuffix`. -/
def parseQBFPrefixOutput (bits : List Bool) : List Bool :=
  match parseQBF bits.length bits with
  | none => []
  | some (formula, suffix) => true :: pair (encodeQBF formula) suffix

theorem parseQBFPrefixOutput_eq_state (bits : List Bool) :
    parseQBFPrefixOutput bits =
      if SyntaxStatePrefixComplete (syntaxScanStateRun bits.length 1 bits) then
        true :: pair
          (bits.take (bits.length - (syntaxStateRemaining
            (syntaxScanStateRun bits.length 1 bits)).length))
          (syntaxStateRemaining (syntaxScanStateRun bits.length 1 bits)) else [] := by
  have hscan := scanSyntax_prefix_eq_parseQBF bits
  rw [scanSyntax_prefix_eq_state] at hscan
  cases hp : parseQBF bits.length bits with
  | none =>
    rw [hp] at hscan
    simp only [Option.map_none] at hscan
    have hnot : ¬ SyntaxStatePrefixComplete (syntaxScanStateRun bits.length 1 bits) := by
      intro h
      simp [h] at hscan
    simp [parseQBFPrefixOutput, hp, hnot]
  | some result =>
    rcases result with ⟨formula, suffix⟩
    rw [hp] at hscan
    simp only [Option.map_some] at hscan
    have hyes : SyntaxStatePrefixComplete (syntaxScanStateRun bits.length 1 bits) := by
      by_contra h
      simp [h] at hscan
    rw [ite_eq_left hyes] at hscan
    have hremaining : syntaxStateRemaining (syntaxScanStateRun bits.length 1 bits) = suffix :=
      congrArg Prod.snd (Option.some.inj hscan)
    have hbytes := parseQBF_sound bits.length bits suffix formula hp
    simp only [parseQBFPrefixOutput, hp, ite_eq_left hyes, hremaining]
    rw [← hbytes]
    simp

theorem parseQBFPrefixOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => parseQBFPrefixOutput (bits z)) ∈ FP := by
  have hrun := syntaxScanStateRun_mem_FP (UnaryFn.length hbits) (UnaryFn.const 1) hbits
  have hremaining := syntaxStateRemaining_mem_FP hrun
  have hprefix := take_mem_FP hbits ((UnaryFn.length hbits).sub (UnaryFn.length hremaining))
  have h := (syntaxStatePrefixComplete_fppred hrun).ite_mem_FP
    (mem_FP_comp (mem_FP_pair hprefix hremaining) (Cobham.cons_mem_FP true)) (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun z => (parseQBFPrefixOutput_eq_state (bits z)).symm)

@[simp] theorem parseQBFPrefixOutput_encode (formula : QBF) (suffix : List Bool) :
    parseQBFPrefixOutput (encodeQBF formula ++ suffix) =
      true :: pair (encodeQBF formula) suffix := by
  unfold parseQBFPrefixOutput
  rw [parseQBF_encode formula _ suffix (by simp)]

@[simp] theorem parseQBFPrefixOutput_nil : parseQBFPrefixOutput [] = [] := rfl

theorem parseQBFPrefixOutput_eq_nil_iff (bits : List Bool) :
    parseQBFPrefixOutput bits = [] ↔ parseQBF bits.length bits = none := by
  cases hp : parseQBF bits.length bits with
  | none => simp [parseQBFPrefixOutput, hp]
  | some result => cases result; simp [parseQBFPrefixOutput, hp]

/-- Encoded first complete formula, or `[]` if there is no complete prefix. -/
def syntaxPrefixBits (bits : List Bool) : List Bool :=
  pairFst ((parseQBFPrefixOutput bits).drop 1)

/-- Untouched suffix after the first complete formula, or `[]` on failure. -/
def syntaxPrefixSuffix (bits : List Bool) : List Bool :=
  pairSnd ((parseQBFPrefixOutput bits).drop 1)

theorem syntaxPrefixBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxPrefixBits (bits z)) ∈ FP :=
  mem_FP_comp (drop_mem_FP (parseQBFPrefixOutput_mem_FP hbits) (UnaryFn.const 1)) pairFst_mem_FP

theorem syntaxPrefixSuffix_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxPrefixSuffix (bits z)) ∈ FP :=
  mem_FP_comp (drop_mem_FP (parseQBFPrefixOutput_mem_FP hbits) (UnaryFn.const 1)) pairSnd_mem_FP

@[simp] theorem syntaxPrefixBits_encode (formula : QBF) (suffix : List Bool) :
    syntaxPrefixBits (encodeQBF formula ++ suffix) = encodeQBF formula := by
  simp [syntaxPrefixBits]

@[simp] theorem syntaxPrefixSuffix_encode (formula : QBF) (suffix : List Bool) :
    syntaxPrefixSuffix (encodeQBF formula ++ suffix) = suffix := by
  simp [syntaxPrefixSuffix]

@[simp] theorem syntaxPrefixBits_nil : syntaxPrefixBits [] = [] := by
  simp [syntaxPrefixBits, pairFst]

@[simp] theorem syntaxPrefixSuffix_nil : syntaxPrefixSuffix [] = [] := by
  simp [syntaxPrefixSuffix, pairSnd, unpair?]

/-- The first immediate child; full-parent decoding rejects malformed inputs. -/
def syntaxFirstChildBits (bits : List Bool) : List Bool :=
  if (decodeQBF bits).isSome then syntaxPrefixBits (syntaxTokenSuffix bits) else []

/-- The second immediate child, present only for binary constructors. -/
def syntaxSecondChildBits (bits : List Bool) : List Bool :=
  if (decodeQBF bits).isSome then
    syntaxPrefixBits (syntaxPrefixSuffix (syntaxTokenSuffix bits)) else []

theorem syntaxFirstChildBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxFirstChildBits (bits z)) ∈ FP :=
  (decodeQBF_success_fppred hbits).ite_mem_FP
    (syntaxPrefixBits_mem_FP (syntaxTokenSuffix_mem_FP hbits)) (constFn_mem_FP [])

theorem syntaxSecondChildBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxSecondChildBits (bits z)) ∈ FP :=
  (decodeQBF_success_fppred hbits).ite_mem_FP
    (syntaxPrefixBits_mem_FP (syntaxPrefixSuffix_mem_FP (syntaxTokenSuffix_mem_FP hbits)))
    (constFn_mem_FP [])

theorem syntaxFirstChildBits_decode_none (bits : List Bool) (h : decodeQBF bits = none) :
    syntaxFirstChildBits bits = [] := by simp [syntaxFirstChildBits, h]

theorem syntaxSecondChildBits_decode_none (bits : List Bool) (h : decodeQBF bits = none) :
    syntaxSecondChildBits bits = [] := by simp [syntaxSecondChildBits, h]

@[simp] theorem syntaxPrefixBits_encodeQBF (formula : QBF) :
    syntaxPrefixBits (encodeQBF formula) = encodeQBF formula := by
  simpa using syntaxPrefixBits_encode formula []

@[simp] theorem syntaxPrefixSuffix_encodeQBF (formula : QBF) :
    syntaxPrefixSuffix (encodeQBF formula) = [] := by
  simpa using syntaxPrefixSuffix_encode formula []

/-- Immediate children in their original left-to-right order. -/
def qbfChildren : QBF → List QBF
  | .var _ | .tru | .fls => []
  | .neg child | .ex _ child | .all _ child => [child]
  | .conj left right | .disj left right => [left, right]

theorem syntaxTokenSuffix_encodeQBF (formula : QBF) :
    syntaxTokenSuffix (encodeQBF formula) = encodeQBFList (qbfChildren formula) := by
  cases formula with
  | var name =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode (.var name) [])
  | tru =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode .tru [])
  | fls =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode .fls [])
  | neg child =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode .neg (encodeQBF child))
  | ex name child =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren, List.append_assoc] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode (.ex name) (encodeQBF child))
  | all name child =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren, List.append_assoc] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode (.all name) (encodeQBF child))
  | conj left right =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren, List.append_assoc] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode .conj (encodeQBF left ++ encodeQBF right))
  | disj left right =>
    simpa [encodeQBF, SyntaxToken.encode, qbfChildren, List.append_assoc] using
      syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode .disj (encodeQBF left ++ encodeQBF right))

/-- Exact child extraction, including the absence of children at leaves. -/
@[simp] theorem syntaxFirstChildBits_encodeQBF (formula : QBF) :
    syntaxFirstChildBits (encodeQBF formula) =
      (((qbfChildren formula)[0]?).map encodeQBF).getD [] := by
  simp only [syntaxFirstChildBits, decodeQBF_encodeQBF, Option.isSome_some,
    ↓reduceIte, syntaxTokenSuffix_encodeQBF]
  cases formula <;> simp [qbfChildren]

/-- Unary constructors have no second child; binary constructors retain the
original right child, with no renaming or reconstruction. -/
@[simp] theorem syntaxSecondChildBits_encodeQBF (formula : QBF) :
    syntaxSecondChildBits (encodeQBF formula) =
      (((qbfChildren formula)[1]?).map encodeQBF).getD [] := by
  simp only [syntaxSecondChildBits, decodeQBF_encodeQBF, Option.isSome_some,
    ↓reduceIte, syntaxTokenSuffix_encodeQBF]
  cases formula <;> simp [qbfChildren]

@[simp] theorem syntaxFirstChildBits_encode_conj (left right : QBF) :
    syntaxFirstChildBits (encodeQBF (.conj left right)) = encodeQBF left := by
  simp [qbfChildren]

@[simp] theorem syntaxFirstChildBits_encode_disj (left right : QBF) :
    syntaxFirstChildBits (encodeQBF (.disj left right)) = encodeQBF left := by
  simp [qbfChildren]

@[simp] theorem syntaxSecondChildBits_encode_conj (left right : QBF) :
    syntaxSecondChildBits (encodeQBF (.conj left right)) = encodeQBF right := by
  simp [qbfChildren]

@[simp] theorem syntaxSecondChildBits_encode_disj (left right : QBF) :
    syntaxSecondChildBits (encodeQBF (.disj left right)) = encodeQBF right := by
  simp [qbfChildren]

@[simp] theorem syntaxFirstChildBits_encode_neg (child : QBF) :
    syntaxFirstChildBits (encodeQBF (.neg child)) = encodeQBF child := by
  simp [qbfChildren]

@[simp] theorem syntaxFirstChildBits_encode_ex (name : ℕ) (child : QBF) :
    syntaxFirstChildBits (encodeQBF (.ex name child)) = encodeQBF child := by
  simp [qbfChildren]

@[simp] theorem syntaxFirstChildBits_encode_all (name : ℕ) (child : QBF) :
    syntaxFirstChildBits (encodeQBF (.all name child)) = encodeQBF child := by
  simp [qbfChildren]

/-- All-input refinement to the original decoder followed by list indexing. -/
theorem syntaxFirstChildBits_eq_decodeQBF (bits : List Bool) :
    syntaxFirstChildBits bits =
      (((decodeQBF bits).bind (fun formula => (qbfChildren formula)[0]?)).map encodeQBF).getD [] := by
  cases hd : decodeQBF bits with
  | none => simp [syntaxFirstChildBits_decode_none bits hd]
  | some formula =>
    have hbytes := (decodeQBF_eq_some_iff bits formula).mp hd
    rw [← hbytes, syntaxFirstChildBits_encodeQBF]
    simp

theorem syntaxSecondChildBits_eq_decodeQBF (bits : List Bool) :
    syntaxSecondChildBits bits =
      (((decodeQBF bits).bind (fun formula => (qbfChildren formula)[1]?)).map encodeQBF).getD [] := by
  cases hd : decodeQBF bits with
  | none => simp [syntaxSecondChildBits_decode_none bits hd]
  | some formula =>
    have hbytes := (decodeQBF_eq_some_iff bits formula).mp hd
    rw [← hbytes, syntaxSecondChildBits_encodeQBF]
    simp

/-- Child extraction never increases the length, including invalid parents. -/
theorem syntaxFirstChildBits_length_le (bits : List Bool) :
    (syntaxFirstChildBits bits).length ≤ bits.length := by
  cases hd : decodeQBF bits with
  | none => simp [syntaxFirstChildBits_decode_none bits hd]
  | some formula =>
    have hbytes := (decodeQBF_eq_some_iff bits formula).mp hd
    rw [← hbytes, syntaxFirstChildBits_encodeQBF]
    cases formula <;> simp [qbfChildren, encodeQBF] <;> omega

theorem syntaxSecondChildBits_length_le (bits : List Bool) :
    (syntaxSecondChildBits bits).length ≤ bits.length := by
  cases hd : decodeQBF bits with
  | none => simp [syntaxSecondChildBits_decode_none bits hd]
  | some formula =>
    have hbytes := (decodeQBF_eq_some_iff bits formula).mp hd
    rw [← hbytes, syntaxSecondChildBits_encodeQBF]
    cases formula <;> simp [qbfChildren, encodeQBF] <;> omega

end IPPSPACE

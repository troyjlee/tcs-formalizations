/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.SyntaxParsingFP

/-!
# Polynomial-time traversal of binary syntax tokens

Only token positions are unary. Names and untouched syntax suffixes remain
binary strings, including on arbitrary malformed inputs.
-/

namespace IPPSPACE

open Complexity

def qbfTokens : QBF → List SyntaxToken
  | .var i => [.var i]
  | .tru => [.tru]
  | .fls => [.fls]
  | .neg φ => .neg :: qbfTokens φ
  | .conj φ ψ => .conj :: (qbfTokens φ ++ qbfTokens ψ)
  | .disj φ ψ => .disj :: (qbfTokens φ ++ qbfTokens ψ)
  | .ex i φ => .ex i :: qbfTokens φ
  | .all i φ => .all i :: qbfTokens φ

def encodeSyntaxTokens (tokens : List SyntaxToken) : List Bool :=
  tokens.flatMap SyntaxToken.encode

@[simp] theorem encodeSyntaxTokens_nil : encodeSyntaxTokens [] = [] := rfl

@[simp] theorem encodeSyntaxTokens_cons (token : SyntaxToken) (tokens : List SyntaxToken) :
    encodeSyntaxTokens (token :: tokens) = token.encode ++ encodeSyntaxTokens tokens := rfl

@[simp] theorem encodeSyntaxTokens_append (left right : List SyntaxToken) :
    encodeSyntaxTokens (left ++ right) = encodeSyntaxTokens left ++ encodeSyntaxTokens right := by
  simp [encodeSyntaxTokens]

@[simp] theorem encodeSyntaxTokens_qbfTokens (φ : QBF) :
    encodeSyntaxTokens (qbfTokens φ) = encodeQBF φ := by
  induction φ <;> simp_all [qbfTokens, SyntaxToken.encode, encodeQBF]

@[simp] theorem length_qbfTokens (φ : QBF) : (qbfTokens φ).length = nodeCount φ := by
  induction φ <;> simp_all [qbfTokens, nodeCount]

theorem syntaxTokenSuffix_none (bits : List Bool) (h : parseSyntaxToken bits = none) :
    syntaxTokenSuffix bits = [] := by
  simp [syntaxTokenSuffix, parseSyntaxTokenOutput, encodeSyntaxTokenResult, h, pairSnd, unpair?]

@[simp] theorem syntaxTokenSuffix_nil : syntaxTokenSuffix [] = [] :=
  syntaxTokenSuffix_none [] rfl

theorem syntaxTokenSuffix_length_le (bits : List Bool) :
    (syntaxTokenSuffix bits).length ≤ bits.length := by
  cases hp : parseSyntaxToken bits with
  | none => rw [syntaxTokenSuffix_none bits hp]; exact Nat.zero_le _
  | some result =>
    rw [syntaxTokenSuffix_eq bits result.2 result.1 hp]
    have h := parseSyntaxToken_suffix_length bits result.2 result.1 hp
    omega

def syntaxSuffixAt (index : ℕ) (bits : List Bool) : List Bool :=
  syntaxTokenSuffix^[index] bits

@[simp] theorem syntaxSuffixAt_zero (bits : List Bool) : syntaxSuffixAt 0 bits = bits := rfl

@[simp] theorem syntaxSuffixAt_succ (index : ℕ) (bits : List Bool) :
    syntaxSuffixAt (index + 1) bits = syntaxSuffixAt index (syntaxTokenSuffix bits) :=
  Function.iterate_succ_apply _ _ _

@[simp] theorem syntaxSuffixAt_nil (index : ℕ) : syntaxSuffixAt index [] = [] := by
  induction index <;> simp_all

theorem syntaxSuffixAt_encodeSyntaxTokens (index : ℕ) (tokens : List SyntaxToken) :
    syntaxSuffixAt index (encodeSyntaxTokens tokens) = encodeSyntaxTokens (tokens.drop index) := by
  induction index generalizing tokens with
  | zero => simp
  | succ index ih =>
    cases tokens with
    | nil => simp
    | cons token tokens =>
      rw [syntaxSuffixAt_succ, encodeSyntaxTokens_cons,
        syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode token _), ih]
      rfl

theorem syntaxSuffixAt_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => syntaxSuffixAt (index z) (bits z)) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have h := iterate_mem_FP_of_step_le (syntaxTokenSuffix_mem_FP hid)
    hbits hindex.mem_FP 0 (fun _ _ _ => by
      rw [Function.iterate_succ_apply']
      simpa using syntaxTokenSuffix_length_le _)
  exact mem_FP_of_eq h (fun z => by simp only [List.length_replicate, syntaxSuffixAt, id_eq])

/-- The canonical current token bytes; failure has the empty fallback. -/
def syntaxTokenBits (bits : List Bool) : List Bool :=
  pairFst ((parseSyntaxTokenOutput bits).drop 1)

@[simp] theorem syntaxTokenBits_encode (token : SyntaxToken) (suffix : List Bool) :
    syntaxTokenBits (token.encode ++ suffix) = token.encode := by
  simp [syntaxTokenBits, parseSyntaxTokenOutput, encodeSyntaxTokenResult]

@[simp] theorem syntaxTokenBits_nil : syntaxTokenBits [] = [] := by
  simp [syntaxTokenBits, parseSyntaxTokenOutput, encodeSyntaxTokenResult, parseSyntaxToken, pairFst]

theorem syntaxTokenBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxTokenBits (bits z)) ∈ FP :=
  mem_FP_comp (drop_mem_FP (parseSyntaxTokenOutput_mem_FP hbits) (UnaryFn.const 1)) pairFst_mem_FP

def syntaxTokenBitsAt (index : ℕ) (bits : List Bool) : List Bool :=
  syntaxTokenBits (syntaxSuffixAt index bits)

theorem syntaxTokenBitsAt_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => syntaxTokenBitsAt (index z) (bits z)) ∈ FP :=
  syntaxTokenBits_mem_FP (syntaxSuffixAt_mem_FP hindex hbits)

theorem syntaxTokenBitsAt_encodeSyntaxTokens (index : ℕ) (tokens : List SyntaxToken) :
    syntaxTokenBitsAt index (encodeSyntaxTokens tokens) =
      ((tokens[index]?).map SyntaxToken.encode).getD [] := by
  unfold syntaxTokenBitsAt
  rw [syntaxSuffixAt_encodeSyntaxTokens]
  induction index generalizing tokens with
  | zero => cases tokens <;> simp
  | succ index ih => cases tokens with
    | nil => simp
    | cons token tokens => simpa using ih tokens

theorem syntaxTokenBitsAt_encodeQBF (index : ℕ) (φ : QBF) :
    syntaxTokenBitsAt index (encodeQBF φ) =
      (((qbfTokens φ)[index]?).map SyntaxToken.encode).getD [] := by
  rw [← encodeSyntaxTokens_qbfTokens φ, syntaxTokenBitsAt_encodeSyntaxTokens]

end IPPSPACE

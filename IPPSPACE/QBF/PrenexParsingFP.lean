/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.SyntaxTraversalFP
import IPPSPACE.QBF.EncodedPrenex
import IPPSPACE.QBF.PrenexConversion

/-!
# Polynomial-time recognition and extraction of prenex syntax

The outer quantifier prefix is removed directly from canonical binary tokens.
Names remain binary; numeric counters measure syntax positions only.
-/

namespace IPPSPACE

open Complexity

def SyntaxToken.IsQuantifier : SyntaxToken → Prop
  | .ex _ | .all _ => True
  | _ => False

instance (token : SyntaxToken) : Decidable token.IsQuantifier := by
  cases token <;> simp only [SyntaxToken.IsQuantifier] <;> infer_instance

def QuantifierTokenBits (bits : List Bool) : Prop := bits.take 2 = [true, true]

instance (bits : List Bool) : Decidable (QuantifierTokenBits bits) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem quantifierTokenBits_nil : ¬ QuantifierTokenBits [] := by
  simp [QuantifierTokenBits]

@[simp] theorem quantifierTokenBits_encode (token : SyntaxToken) (suffix : List Bool) :
    QuantifierTokenBits (token.encode ++ suffix) ↔ token.IsQuantifier := by
  cases token <;> simp [QuantifierTokenBits, SyntaxToken.encode, SyntaxToken.IsQuantifier]

theorem quantifierTokenBits_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => QuantifierTokenBits (bits z) :=
  bitStrings_eq_fppred (take_mem_FP hbits (UnaryFn.const 2)) (constFn_mem_FP [true, true])

@[simp] theorem quantifierTokenBits_encode_only (token : SyntaxToken) :
    QuantifierTokenBits token.encode ↔ token.IsQuantifier := by
  simpa only [List.append_nil] using quantifierTokenBits_encode token []

theorem quantifierFree_iff_tokens (φ : QBF) :
    φ.QuantifierFree ↔ ∀ token ∈ qbfTokens φ, ¬ token.IsQuantifier := by
  induction φ <;>
    simp_all [qbfTokens, SyntaxToken.IsQuantifier, QBF.QuantifierFree, QBF.quantDepth,
      or_imp, forall_and]

def NoQuantifierBits (bits : List Bool) : Prop :=
  ∀ i < bits.length, ¬ QuantifierTokenBits (syntaxTokenBitsAt i bits)

instance (bits : List Bool) : Decidable (NoQuantifierBits bits) :=
  inferInstanceAs (Decidable (∀ i < bits.length, _))

private theorem tokens_quantifier_test (tokens : List SyntaxToken) (bound : ℕ)
    (hbound : tokens.length ≤ bound) :
    (∀ i < bound, ¬ QuantifierTokenBits (((tokens[i]?).map SyntaxToken.encode).getD [])) ↔
      ∀ token ∈ tokens, ¬ token.IsQuantifier := by
  constructor
  · intro h token ht
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ht
    have hh := h i (lt_of_lt_of_le hi hbound)
    simpa only [List.getElem?_eq_getElem hi, heq, Option.map_some, Option.getD_some,
      quantifierTokenBits_encode_only] using hh
  · intro h i _
    by_cases hi : i < tokens.length
    · simpa only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
        quantifierTokenBits_encode_only] using
        h tokens[i] (List.getElem_mem hi)
    · simp [List.getElem?_eq_none (by omega : tokens.length ≤ i)]

theorem noQuantifierBits_encodeQBF (φ : QBF) :
    NoQuantifierBits (encodeQBF φ) ↔ φ.QuantifierFree := by
  unfold NoQuantifierBits
  simp only [syntaxTokenBitsAt_encodeQBF]
  rw [tokens_quantifier_test _ _ (by simpa using nodeCount_le_length_encodeQBF φ)]
  exact (quantifierFree_iff_tokens φ).symm

theorem noQuantifierBits_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => NoQuantifierBits (bits z) := by
  have hp := (quantifierTokenBits_fppred
    (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hbits))).not
  exact (FPPred.forall_lt (UnaryFn.length hbits) hp).of_iff (fun z => by
    simp only [NoQuantifierBits, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.length_replicate])

def stripQuantifierStep (bits : List Bool) : List Bool :=
  if QuantifierTokenBits bits then syntaxTokenSuffix bits else bits

def prenexMatrixBits (bits : List Bool) : List Bool := stripQuantifierStep^[bits.length] bits

theorem stripQuantifierStep_mem_FP : stripQuantifierStep ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  exact (quantifierTokenBits_fppred hid).ite_mem_FP (syntaxTokenSuffix_mem_FP hid) hid

theorem stripQuantifierStep_length_le (bits : List Bool) :
    (stripQuantifierStep bits).length ≤ bits.length := by
  unfold stripQuantifierStep
  split
  · exact syntaxTokenSuffix_length_le bits
  · exact le_rfl

theorem prenexMatrixBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => prenexMatrixBits (bits z)) ∈ FP := by
  have h := iterate_mem_FP_of_step_le stripQuantifierStep_mem_FP hbits hbits 0
    (fun _ _ _ => by
      rw [Function.iterate_succ_apply']
      simpa using stripQuantifierStep_length_le _)
  exact h

def Quantifier.token : Quantifier → SyntaxToken
  | .ex i => .ex i
  | .all i => .all i

@[simp] theorem quantifier_token_isQuantifier (q : Quantifier) : q.token.IsQuantifier := by
  cases q <;> trivial

theorem encodeQBF_prefixQBF_tokens (qs : List Quantifier) (φ : QBF) :
    encodeQBF (prefixQBF qs φ) = encodeSyntaxTokens (qs.map Quantifier.token) ++ encodeQBF φ := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    cases q <;> simp [prefixQBF, Quantifier.bind, encodeQBF, Quantifier.token,
      SyntaxToken.encode, ih, List.append_assoc]

theorem stripQuantifierStep_encode_quantifier (q : Quantifier) (bits : List Bool) :
    stripQuantifierStep (q.token.encode ++ bits) = bits := by
  simp only [stripQuantifierStep, quantifierTokenBits_encode, quantifier_token_isQuantifier,
    ↓reduceIte]
  exact syntaxTokenSuffix_eq _ _ _ (parseSyntaxToken_encode _ _)

theorem stripQuantifierStep_iterate_prefix (qs : List Quantifier) (bits : List Bool) (fuel : ℕ) :
    stripQuantifierStep^[qs.length + fuel] (encodeSyntaxTokens (qs.map Quantifier.token) ++ bits) =
      stripQuantifierStep^[fuel] bits := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.length_cons, List.map_cons, encodeSyntaxTokens_cons, List.append_assoc]
    rw [show qs.length + 1 + fuel = (qs.length + fuel) + 1 by omega,
      Function.iterate_succ_apply, stripQuantifierStep_encode_quantifier, ih]

theorem splitQBFPrefix_not_quantifier (φ : QBF) :
    ¬ QuantifierTokenBits (encodeQBF (splitQBFPrefix φ).2) := by
  induction φ <;> simp_all [splitQBFPrefix, encodeQBF, QuantifierTokenBits]

theorem splitQBFPrefix_length_le (φ : QBF) :
    (splitQBFPrefix φ).1.length ≤ nodeCount φ := by
  induction φ <;> simp_all [splitQBFPrefix, nodeCount]

theorem prenexMatrixBits_encodeQBF (φ : QBF) :
    prenexMatrixBits (encodeQBF φ) = encodeQBF (splitQBFPrefix φ).2 := by
  have hp := prefixQBF_splitQBFPrefix φ
  have hlen : (splitQBFPrefix φ).1.length ≤ (encodeQBF φ).length :=
    (splitQBFPrefix_length_le φ).trans (nodeCount_le_length_encodeQBF φ)
  have h := stripQuantifierStep_iterate_prefix (splitQBFPrefix φ).1
    (encodeQBF (splitQBFPrefix φ).2) ((encodeQBF φ).length - (splitQBFPrefix φ).1.length)
  rw [Nat.add_sub_of_le hlen, ← encodeQBF_prefixQBF_tokens, hp] at h
  unfold prenexMatrixBits
  rw [h]
  apply Function.iterate_fixed
  simp [stripQuantifierStep, splitQBFPrefix_not_quantifier]

theorem decodePrenex_success_iff (bits : List Bool) :
    (decodePrenex bits).isSome = true ↔
      (decodeQBF bits).isSome = true ∧ NoQuantifierBits (prenexMatrixBits bits) := by
  cases hd : decodeQBF bits with
  | none => simp [decodePrenex, hd]
  | some φ =>
    have he := (decodeQBF_eq_some_iff bits φ).mp hd
    rw [← he, prenexMatrixBits_encodeQBF, noQuantifierBits_encodeQBF]
    simp only [decodePrenex, decodeQBF_encodeQBF, Option.bind_some, recognizePrenex]
    split <;> simp_all [QBF.QuantifierFree]

theorem decodePrenex_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (decodePrenex (bits z)).isSome = true :=
  ((decodeQBF_success_fppred hbits).and
    (noQuantifierBits_fppred (prenexMatrixBits_mem_FP hbits))).of_iff
      (fun z => (decodePrenex_success_iff (bits z)).symm)

def prenexPrefixBits (bits : List Bool) : List Bool :=
  bits.take (bits.length - (prenexMatrixBits bits).length)

def prenexPrefixCount (bits : List Bool) : ℕ :=
  ((decodeQBF bits).map nodeCount).getD 0 -
    ((decodeQBF (prenexMatrixBits bits)).map nodeCount).getD 0

theorem prenexPrefixBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => prenexPrefixBits (bits z)) ∈ FP :=
  take_mem_FP hbits ((UnaryFn.length hbits).sub
    (UnaryFn.length (prenexMatrixBits_mem_FP hbits)))

theorem prenexPrefixCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => prenexPrefixCount (bits z) :=
  (decodeQBF_nodeCount_unaryFn hbits).sub
    (decodeQBF_nodeCount_unaryFn (prenexMatrixBits_mem_FP hbits))

@[simp] theorem prenexMatrixBits_encode_prenex (φ : PrenexQBF) :
    prenexMatrixBits (encodeQBF φ.toQBF) = encodeQBF φ.matrix := by
  rw [prenexMatrixBits_encodeQBF, PrenexQBF.toQBF,
    splitQBFPrefix_prefixQBF _ _ φ.matrix_quantifierFree]

@[simp] theorem prenexPrefixBits_encode_prenex (φ : PrenexQBF) :
    prenexPrefixBits (encodeQBF φ.toQBF) =
      encodeSyntaxTokens (φ.quantifiers.map Quantifier.token) := by
  unfold prenexPrefixBits
  rw [prenexMatrixBits_encode_prenex]
  rw [PrenexQBF.toQBF, encodeQBF_prefixQBF_tokens]
  simp

@[simp] theorem prenexPrefixCount_encode_prenex (φ : PrenexQBF) :
    prenexPrefixCount (encodeQBF φ.toQBF) = φ.quantifiers.length := by
  simp only [prenexPrefixCount, prenexMatrixBits_encode_prenex, decodeQBF_encodeQBF,
    Option.map_some, Option.getD_some]
  simp [PrenexQBF.toQBF, nodeCount_prefixQBF]

/-- Failure is empty; success contains the exact original prefix and matrix. -/
def decodePrenexOutput (bits : List Bool) : List Bool :=
  match decodePrenex bits with
  | none => []
  | some φ => true :: pair (encodeSyntaxTokens (φ.quantifiers.map Quantifier.token))
      (encodeQBF φ.matrix)

theorem decodePrenexOutput_eq (bits : List Bool) :
    decodePrenexOutput bits =
      if (decodePrenex bits).isSome then
        true :: pair (prenexPrefixBits bits) (prenexMatrixBits bits) else [] := by
  cases hd : decodePrenex bits with
  | none => simp [decodePrenexOutput, hd]
  | some φ =>
    have he := (decodePrenex_eq_some_iff bits φ).mp hd
    simp [decodePrenexOutput, ← he]

theorem decodePrenexOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodePrenexOutput (bits z)) ∈ FP := by
  have h := (decodePrenex_success_fppred hbits).ite_mem_FP
    (mem_FP_comp (mem_FP_pair (prenexPrefixBits_mem_FP hbits) (prenexMatrixBits_mem_FP hbits))
      (Cobham.cons_mem_FP true)) (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun z => (decodePrenexOutput_eq (bits z)).symm)

theorem mem_var_qbfTokens_iff (φ : QBF) (hφ : φ.QuantifierFree) (i : ℕ) :
    SyntaxToken.var i ∈ qbfTokens φ ↔ i ∈ φ.freeVars := by
  induction φ <;> simp_all [qbfTokens, QBF.freeVars, QBF.QuantifierFree, QBF.quantDepth]

theorem prenex_closed_iff_tokens (φ : PrenexQBF) :
    φ.toQBF.Closed ↔
      ∀ i, SyntaxToken.var i ∈ qbfTokens φ.matrix →
        ∃ q ∈ φ.quantifiers, q.index = i := by
  simp only [mem_var_qbfTokens_iff _ φ.matrix_quantifierFree]
  unfold QBF.Closed PrenexQBF.toQBF
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_freeVars_prefixQBF]
  constructor
  · intro h i hi
    by_contra hn
    apply h i
    refine ⟨hi, ?_⟩
    simpa only [not_exists, not_and, ne_eq, eq_comm] using hn
  · rintro h i ⟨hi, hn⟩
    obtain ⟨q, hq, he⟩ := h i hi
    exact hn q hq he.symm

def VariableTokenBits (bits : List Bool) : Prop := bits.take 3 = [false, false, false]

instance (bits : List Bool) : Decidable (VariableTokenBits bits) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem variableTokenBits_nil : ¬ VariableTokenBits [] := by simp [VariableTokenBits]

theorem variableTokenBits_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => VariableTokenBits (bits z) :=
  bitStrings_eq_fppred (take_mem_FP hbits (UnaryFn.const 3))
    (constFn_mem_FP [false, false, false])

def PrefixCoversToken (count : ℕ) (prefixBits token : List Bool) : Prop :=
  VariableTokenBits token →
    ∃ j < count, (syntaxTokenBitsAt j prefixBits).drop 3 = token.drop 3

instance (count : ℕ) (prefixBits token : List Bool) : Decidable (PrefixCoversToken count prefixBits token) :=
  inferInstanceAs (Decidable (_ → ∃ j < count, _))

@[simp] theorem prefixCoversToken_nil (count : ℕ) (prefixBits : List Bool) :
    PrefixCoversToken count prefixBits [] := by simp [PrefixCoversToken]

private theorem encodeNatName_injective_local : Function.Injective encodeNatName := by
  intro i j h
  have he : QBF.var i = QBF.var j := encodeQBF_injective (by simp [encodeQBF, h])
  exact QBF.var.inj he

@[simp] theorem quantifier_token_drop (q : Quantifier) :
    q.token.encode.drop 3 = encodeNatName q.index := by
  cases q <;> simp [Quantifier.token, SyntaxToken.encode, Quantifier.index]

theorem prefixCoversToken_encode (qs : List Quantifier) (token : SyntaxToken) :
    PrefixCoversToken qs.length (encodeSyntaxTokens (qs.map Quantifier.token)) token.encode ↔
      ∀ i, token = .var i → ∃ q ∈ qs, q.index = i := by
  cases token <;> simp [PrefixCoversToken, VariableTokenBits, SyntaxToken.encode]
  case var i =>
    constructor
    · rintro h
      obtain ⟨j, hj, he⟩ := h
      rw [syntaxTokenBitsAt_encodeSyntaxTokens] at he
      simp only [List.getElem?_eq_getElem (by simpa using hj : j < (qs.map Quantifier.token).length),
        List.getElem_map, Option.map_some, Option.getD_some, quantifier_token_drop] at he
      exact ⟨qs[j], List.getElem_mem hj, encodeNatName_injective_local he⟩
    · rintro ⟨q, hq, he⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      refine ⟨j, hj, ?_⟩
      rw [syntaxTokenBitsAt_encodeSyntaxTokens]
      simp only [List.getElem?_eq_getElem (by simpa using hj : j < (qs.map Quantifier.token).length),
        List.getElem_map, Option.map_some, Option.getD_some, quantifier_token_drop, he]

theorem prefixCoversToken_fppred {count : List Bool → ℕ} {prefixBits token : List Bool → List Bool}
    (hc : UnaryFn count) (hp : prefixBits ∈ FP) (ht : token ∈ FP) :
    FPPred fun z => PrefixCoversToken (count z) (prefixBits z) (token z) := by
  have heq := bitStrings_eq_fppred
    (drop_mem_FP (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hp))
      (UnaryFn.const 3))
    (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.const 3))
  have hex := FPPred.exists_lt hc heq
  exact ((variableTokenBits_fppred ht).not.or hex).of_iff (fun z => by
    simp only [PrefixCoversToken, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.length_replicate]
    exact imp_iff_not_or.symm)

def PrefixCoversMatrix (count : ℕ) (prefixBits matrix : List Bool) : Prop :=
  ∀ i < matrix.length, PrefixCoversToken count prefixBits (syntaxTokenBitsAt i matrix)

instance (count : ℕ) (prefixBits matrix : List Bool) :
    Decidable (PrefixCoversMatrix count prefixBits matrix) :=
  inferInstanceAs (Decidable (∀ i < matrix.length, _))

theorem prefixCoversMatrix_fppred {count : List Bool → ℕ} {prefixBits matrix : List Bool → List Bool}
    (hc : UnaryFn count) (hp : prefixBits ∈ FP) (hm : matrix ∈ FP) :
    FPPred fun z => PrefixCoversMatrix (count z) (prefixBits z) (matrix z) := by
  have h := prefixCoversToken_fppred (hc.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hp)
    (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hm))
  exact (FPPred.forall_lt (UnaryFn.length hm) h).of_iff (fun z => by
    simp only [PrefixCoversMatrix, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.length_replicate])

theorem prefixCoversMatrix_encode_prenex (φ : PrenexQBF) :
    PrefixCoversMatrix φ.quantifiers.length
      (encodeSyntaxTokens (φ.quantifiers.map Quantifier.token)) (encodeQBF φ.matrix) ↔
      φ.toQBF.Closed := by
  rw [prenex_closed_iff_tokens]
  unfold PrefixCoversMatrix
  simp only [syntaxTokenBitsAt_encodeQBF]
  constructor
  · intro h i hi
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hi
    have hh := h j (lt_of_lt_of_le hj (by simpa using nodeCount_le_length_encodeQBF φ.matrix))
    rw [List.getElem?_eq_getElem hj, he] at hh
    exact (prefixCoversToken_encode _ _).mp hh i rfl
  · intro h j _
    by_cases hj : j < (qbfTokens φ.matrix).length
    · simp only [List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
      apply (prefixCoversToken_encode _ _).mpr
      intro i he
      apply h i
      rw [← he]
      exact List.getElem_mem hj
    · simp [List.getElem?_eq_none (by omega : (qbfTokens φ.matrix).length ≤ j)]

theorem decodeClosedPrenex_success_iff (bits : List Bool) :
    (decodeClosedPrenex bits).isSome = true ↔
      (decodePrenex bits).isSome = true ∧
        PrefixCoversMatrix (prenexPrefixCount bits) (prenexPrefixBits bits) (prenexMatrixBits bits) := by
  cases hd : decodePrenex bits with
  | none => simp [decodeClosedPrenex, hd]
  | some φ =>
    have he := (decodePrenex_eq_some_iff bits φ).mp hd
    rw [← he, prenexPrefixCount_encode_prenex, prenexPrefixBits_encode_prenex,
      prenexMatrixBits_encode_prenex, prefixCoversMatrix_encode_prenex]
    simp only [decodeClosedPrenex, decodePrenex_encode, Option.bind_eq_bind, Option.bind_some]
    split <;> simp_all [QBF.Closed]

theorem decodeClosedPrenex_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (decodeClosedPrenex (bits z)).isSome = true :=
  ((decodePrenex_success_fppred hbits).and
    (prefixCoversMatrix_fppred (prenexPrefixCount_unaryFn hbits) (prenexPrefixBits_mem_FP hbits)
      (prenexMatrixBits_mem_FP hbits))).of_iff
        (fun z => (decodeClosedPrenex_success_iff (bits z)).symm)

/-- The exact decoder's prefix length, with zero on every failed recognition. -/
theorem decodePrenex_quantifierCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => ((decodePrenex (bits z)).map (fun φ => φ.quantifiers.length)).getD 0 := by
  apply (UnaryFn.ite (decodePrenex_success_fppred hbits)
    (prenexPrefixCount_unaryFn hbits) (UnaryFn.const 0)).of_eq
  intro z
  cases hd : decodePrenex (bits z) with
  | none => simp
  | some φ =>
    have he := (decodePrenex_eq_some_iff (bits z) φ).mp hd
    simp [← he]

/-- The exact decoder's matrix size, with zero on every failed recognition. -/
theorem decodePrenex_matrixNodeCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => ((decodePrenex (bits z)).map (fun φ => nodeCount φ.matrix)).getD 0 := by
  apply (UnaryFn.ite (decodePrenex_success_fppred hbits)
    (decodeQBF_nodeCount_unaryFn (prenexMatrixBits_mem_FP hbits)) (UnaryFn.const 0)).of_eq
  intro z
  cases hd : decodePrenex (bits z) with
  | none => simp
  | some φ =>
    have he := (decodePrenex_eq_some_iff (bits z) φ).mp hd
    simp [← he]

/-- The same prefix/matrix serialization with the existing closedness guard. -/
def decodeClosedPrenexOutput (bits : List Bool) : List Bool :=
  match decodeClosedPrenex bits with
  | none => []
  | some φ => true :: pair (encodeSyntaxTokens (φ.val.quantifiers.map Quantifier.token))
      (encodeQBF φ.val.matrix)

theorem decodeClosedPrenexOutput_eq (bits : List Bool) :
    decodeClosedPrenexOutput bits =
      if (decodeClosedPrenex bits).isSome then
        true :: pair (prenexPrefixBits bits) (prenexMatrixBits bits) else [] := by
  cases hd : decodeClosedPrenex bits with
  | none => simp [decodeClosedPrenexOutput, hd]
  | some φ =>
    have he := (decodeClosedPrenex_eq_some_iff bits φ).mp hd
    simp [decodeClosedPrenexOutput, ← he, φ.property]

theorem decodeClosedPrenexOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodeClosedPrenexOutput (bits z)) ∈ FP := by
  have h := (decodeClosedPrenex_success_fppred hbits).ite_mem_FP
    (mem_FP_comp (mem_FP_pair (prenexPrefixBits_mem_FP hbits) (prenexMatrixBits_mem_FP hbits))
      (Cobham.cons_mem_FP true)) (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun z => (decodeClosedPrenexOutput_eq (bits z)).symm)

@[simp] theorem decodePrenexOutput_encode (φ : PrenexQBF) :
    decodePrenexOutput (encodeQBF φ.toQBF) =
      true :: pair (encodeSyntaxTokens (φ.quantifiers.map Quantifier.token))
        (encodeQBF φ.matrix) := by simp [decodePrenexOutput]

@[simp] theorem decodeClosedPrenexOutput_encode (φ : PrenexQBF) (hφ : φ.toQBF.Closed) :
    decodeClosedPrenexOutput (encodeQBF φ.toQBF) =
      true :: pair (encodeSyntaxTokens (φ.quantifiers.map Quantifier.token))
        (encodeQBF φ.matrix) := by simp [decodeClosedPrenexOutput, hφ]

theorem decodePrenexOutput_eq_nil_iff (bits : List Bool) :
    decodePrenexOutput bits = [] ↔ decodePrenex bits = none := by
  cases hd : decodePrenex bits <;> simp [decodePrenexOutput, hd]

theorem decodeClosedPrenexOutput_eq_nil_iff (bits : List Bool) :
    decodeClosedPrenexOutput bits = [] ↔ decodeClosedPrenex bits = none := by
  cases hd : decodeClosedPrenex bits <;> simp [decodeClosedPrenexOutput, hd]

end IPPSPACE

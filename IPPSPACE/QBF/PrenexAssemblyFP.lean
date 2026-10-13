/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ScopedRenamingFP
import IPPSPACE.QBF.PrenexParsingFP

/-!
# Polynomial-time assembly of the prenex converter's local results

These certificates act on the exact computational payload of `prenexAux`:
quantifier prefix, matrix syntax, and binary next-name counter. Negation dualizes
the prefix, binary nodes concatenate prefixes, and binders prepend their fresh
name. They are local runtime results; bounded traversal with saved scopes remains
a separate obligation for the complete converter.
-/

namespace IPPSPACE

open Complexity

/-- Change only a recognized quantifier tag. Callers supply canonical tokens. -/
def dualQuantifierTokenBytes (bits : List Bool) : List Bool :=
  if bits.take 3 = [true, true, false] then [true, true, true] ++ bits.drop 3
  else if bits.take 3 = [true, true, true] then [true, true, false] ++ bits.drop 3
  else bits

@[simp] theorem dualQuantifierTokenBytes_nil : dualQuantifierTokenBytes [] = [] := by
  simp [dualQuantifierTokenBytes]

@[simp] theorem dualQuantifierTokenBytes_encode (q : Quantifier) :
    dualQuantifierTokenBytes q.token.encode = q.dual.token.encode := by
  cases q <;> simp [dualQuantifierTokenBytes, Quantifier.token, Quantifier.dual, SyntaxToken.encode]

theorem dualQuantifierTokenBytes_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => dualQuantifierTokenBytes (bits z)) ∈ FP := by
  have htag := take_mem_FP hbits (UnaryFn.const 3)
  have htail := drop_mem_FP hbits (UnaryFn.const 3)
  exact (bitStrings_eq_fppred htag (constFn_mem_FP [true, true, false])).ite_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, true]) htail)
    ((bitStrings_eq_fppred htag (constFn_mem_FP [true, true, true])).ite_mem_FP
      (Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false]) htail) hbits)

def dualQuantifierPrefixBits (bits : List Bool) : List Bool :=
  (List.range bits.length).flatMap (fun i => dualQuantifierTokenBytes (syntaxTokenBitsAt i bits))

theorem dualQuantifierPrefixBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => dualQuantifierPrefixBits (bits z)) ∈ FP := by
  have hbody := dualQuantifierTokenBytes_mem_FP
    (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hbits))
  apply mem_FP_of_eq (flatMap_range_mem_FP hbody (UnaryFn.length hbits).mem_FP)
  intro z
  simp only [dualQuantifierPrefixBits, Function.comp_apply, pairFst_pair,
    pairSnd_pair, List.length_replicate]

private theorem assembly_flatMap_range_getD {α β : Type} (entries : List α) (f : α → List β)
    (fuel : ℕ) (hfuel : entries.length ≤ fuel) :
    (List.range fuel).flatMap (fun i => ((entries[i]?).map f).getD []) = entries.flatMap f := by
  induction entries generalizing fuel with
  | nil => simp
  | cons head tail ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have htail : tail.length ≤ fuel := by simpa using hfuel
      simp only [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, List.getElem?_cons_succ]
      rw [ih fuel htail]

theorem quantifierPrefix_length_ge (qs : List Quantifier) :
    qs.length ≤ (encodeSyntaxTokens (qs.map Quantifier.token)).length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have h := q.token.length_encode_ge
    simp only [List.map_cons, encodeSyntaxTokens_cons, List.length_append, List.length_cons]
    omega

theorem dualQuantifierPrefixBits_encode (qs : List Quantifier) :
    dualQuantifierPrefixBits (encodeSyntaxTokens (qs.map Quantifier.token)) =
      encodeSyntaxTokens ((qs.map Quantifier.dual).map Quantifier.token) := by
  have hbody (i : ℕ) :
      dualQuantifierTokenBytes (syntaxTokenBitsAt i (encodeSyntaxTokens (qs.map Quantifier.token))) =
        ((qs[i]?).map (fun q => q.dual.token.encode)).getD [] := by
    rw [syntaxTokenBitsAt_encodeSyntaxTokens, List.getElem?_map]
    cases qs[i]? <;> simp
  simp only [dualQuantifierPrefixBits, hbody]
  rw [assembly_flatMap_range_getD _ _ _ (quantifierPrefix_length_ge qs)]
  simp [encodeSyntaxTokens, List.flatMap_map, Function.comp_def]

/-- Each payload field is stored once. The binary counter is never expanded. -/
def encodeScopedPrenexData (result : ScopedPrenexData) : List Bool :=
  pair (encodeSyntaxTokens (result.prefix.map Quantifier.token))
    (pair (encodeQBF result.matrix) result.next.bits)

theorem encodeScopedPrenexData_length (result : ScopedPrenexData) :
    (encodeScopedPrenexData result).length =
      2 * (encodeQBF (prefixQBF result.prefix result.matrix)).length + result.next.bits.length + 4 := by
  simp only [encodeScopedPrenexData, pair_length, encodeQBF_prefixQBF_tokens, List.length_append]
  omega

theorem encodeScopedPrenexData_mem_FP {result : List Bool → ScopedPrenexData}
    (hp : (fun z => encodeSyntaxTokens ((result z).prefix.map Quantifier.token)) ∈ FP)
    (hm : (fun z => encodeQBF (result z).matrix) ∈ FP)
    (hn : (fun z => (result z).next.bits) ∈ FP) :
    (fun z => encodeScopedPrenexData (result z)) ∈ FP :=
  mem_FP_pair hp (mem_FP_pair hm hn)

theorem scopedPrenexPrefix_mem_FP {result : List Bool → ScopedPrenexData}
    (h : (fun z => encodeScopedPrenexData (result z)) ∈ FP) :
    (fun z => encodeSyntaxTokens ((result z).prefix.map Quantifier.token)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp h pairFst_mem_FP) (fun z => by simp [encodeScopedPrenexData])

theorem scopedPrenexMatrix_mem_FP {result : List Bool → ScopedPrenexData}
    (h : (fun z => encodeScopedPrenexData (result z)) ∈ FP) :
    (fun z => encodeQBF (result z).matrix) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_comp h pairSnd_mem_FP) pairFst_mem_FP)
    (fun z => by simp [encodeScopedPrenexData])

theorem scopedPrenexNext_bits_mem_FP {result : List Bool → ScopedPrenexData}
    (h : (fun z => encodeScopedPrenexData (result z)) ∈ FP) :
    (fun z => (result z).next.bits) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_comp h pairSnd_mem_FP) pairSnd_mem_FP)
    (fun z => by simp [encodeScopedPrenexData])

theorem scopedPrenexAux_var_mem_FP {entries : List Bool → List (ℕ × ℕ)}
    {name start : List Bool → ℕ}
    (he : (fun z => encodeNameEnvironment (entries z)) ∈ FP)
    (hn : (fun z => (name z).bits) ∈ FP) (hs : (fun z => (start z).bits) ∈ FP) :
    (fun z => encodeScopedPrenexData (scopedPrenexAux (.var (name z)) (entries z) (start z))) ∈ FP := by
  apply encodeScopedPrenexData_mem_FP
  · exact constFn_mem_FP []
  · exact Cobham.appendFn_mem_FP (constFn_mem_FP _)
      (frameNameBits_mem_FP (scopedNameLookup_bits_mem_FP he hn))
  · exact hs

theorem scopedPrenexAux_tru_mem_FP (entries : List Bool → List (ℕ × ℕ))
    {start : List Bool → ℕ} (hs : (fun z => (start z).bits) ∈ FP) :
    (fun z => encodeScopedPrenexData (scopedPrenexAux .tru (entries z) (start z))) ∈ FP :=
  encodeScopedPrenexData_mem_FP (constFn_mem_FP []) encodeQBF_tru_mem_FP hs

theorem scopedPrenexAux_fls_mem_FP (entries : List Bool → List (ℕ × ℕ))
    {start : List Bool → ℕ} (hs : (fun z => (start z).bits) ∈ FP) :
    (fun z => encodeScopedPrenexData (scopedPrenexAux .fls (entries z) (start z))) ∈ FP :=
  encodeScopedPrenexData_mem_FP (constFn_mem_FP []) encodeQBF_fls_mem_FP hs

theorem encodeScopedPrenexData_neg_mem_FP {result : List Bool → ScopedPrenexData}
    (h : (fun z => encodeScopedPrenexData (result z)) ∈ FP) :
    (fun z => encodeScopedPrenexData (result z).neg) ∈ FP := by
  apply encodeScopedPrenexData_mem_FP
  · exact mem_FP_of_eq (dualQuantifierPrefixBits_mem_FP (scopedPrenexPrefix_mem_FP h))
      (fun z => dualQuantifierPrefixBits_encode (result z).prefix)
  · exact encodeQBF_neg_mem_FP (scopedPrenexMatrix_mem_FP h)
  · exact scopedPrenexNext_bits_mem_FP (result := result) h

theorem encodeScopedPrenexData_binary_mem_FP (op : QBFConnective)
    {left right : List Bool → ScopedPrenexData}
    (hl : (fun z => encodeScopedPrenexData (left z)) ∈ FP)
    (hr : (fun z => encodeScopedPrenexData (right z)) ∈ FP) :
    (fun z => encodeScopedPrenexData ((left z).binary op (right z))) ∈ FP := by
  apply encodeScopedPrenexData_mem_FP
  · apply mem_FP_of_eq (Cobham.appendFn_mem_FP (scopedPrenexPrefix_mem_FP hl)
      (scopedPrenexPrefix_mem_FP hr))
    intro z
    simp [ScopedPrenexData.binary]
  · cases op
    · exact encodeQBF_conj_mem_FP (scopedPrenexMatrix_mem_FP hl) (scopedPrenexMatrix_mem_FP hr)
    · exact encodeQBF_disj_mem_FP (scopedPrenexMatrix_mem_FP hl) (scopedPrenexMatrix_mem_FP hr)
  · exact scopedPrenexNext_bits_mem_FP (result := right) hr

theorem encodeScopedPrenexData_quantify_mem_FP (q : Quantifier)
    {start : List Bool → ℕ} {child : List Bool → ScopedPrenexData}
    (hs : (fun z => (start z).bits) ∈ FP)
    (hc : (fun z => encodeScopedPrenexData (child z)) ∈ FP) :
    (fun z => encodeScopedPrenexData ((child z).quantify q (start z))) ∈ FP := by
  apply encodeScopedPrenexData_mem_FP
  · have htoken : (fun z => (q.withIndex (start z)).token.encode) ∈ FP := by
      cases q <;> exact Cobham.appendFn_mem_FP (constFn_mem_FP _) (frameNameBits_mem_FP hs)
    exact Cobham.appendFn_mem_FP htoken (scopedPrenexPrefix_mem_FP hc)
  · exact scopedPrenexMatrix_mem_FP (result := child) hc
  · exact scopedPrenexNext_bits_mem_FP (result := child) hc

/-- Once the complete payload is computed, writing its prenex formula is FP. -/
theorem scopedPrenexFormula_mem_FP {result : List Bool → ScopedPrenexData}
    (h : (fun z => encodeScopedPrenexData (result z)) ∈ FP) :
    (fun z => encodeQBF (prefixQBF (result z).prefix (result z).matrix)) ∈ FP :=
  mem_FP_of_eq (Cobham.appendFn_mem_FP (scopedPrenexPrefix_mem_FP h) (scopedPrenexMatrix_mem_FP h))
    (fun z => (encodeQBF_prefixQBF_tokens (result z).prefix (result z).matrix).symm)

end IPPSPACE

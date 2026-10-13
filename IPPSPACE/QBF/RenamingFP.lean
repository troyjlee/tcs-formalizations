/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.SyntaxTraversalFP
import IPPSPACE.QBF.Renaming

/-!
# Polynomial-time renaming of encoded QBF syntax

Uniform renaming changes every variable occurrence and binder without changing
the constructor tree. Traversal keeps names binary, and a local name-map runtime
certificate composes with the complete parser and exact token stream. This is a
runtime theorem for the existing `renameQBF`, not for scoped binder freshening or
the full prenex converter.
-/

namespace IPPSPACE

open Complexity

def SyntaxToken.mapNames (f : ℕ → ℕ) : SyntaxToken → SyntaxToken
  | .var i => .var (f i)
  | .tru => .tru
  | .fls => .fls
  | .neg => .neg
  | .conj => .conj
  | .disj => .disj
  | .ex i => .ex (f i)
  | .all i => .all (f i)

theorem qbfTokens_renameQBF (f : ℕ → ℕ) (formula : QBF) :
    qbfTokens (renameQBF f formula) = (qbfTokens formula).map (SyntaxToken.mapNames f) := by
  induction formula <;> simp_all [renameQBF, qbfTokens, SyntaxToken.mapNames]

/-- The three exact syntax tags that carry a variable name. -/
def SyntaxNameTag (bits : List Bool) : Prop :=
  bits.take 3 = [false, false, false] ∨ bits.take 3 = [true, true, false] ∨
    bits.take 3 = [true, true, true]

instance (bits : List Bool) : Decidable (SyntaxNameTag bits) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- A canonical binary name from one named token. Other strings have a total
fallback inherited from the exact name parser and pair projection. -/
def syntaxTokenNameDigits (bits : List Bool) : List Bool :=
  pairFst ((parseNatNameOutput (bits.drop 3).length (bits.drop 3)).drop 1)

theorem syntaxTokenNameDigits_named (tag : List Bool) (htag : tag.length = 3)
    (name : ℕ) (suffix : List Bool) :
    syntaxTokenNameDigits (tag ++ encodeNatName name ++ suffix) = name.bits := by
  have hdrop : (tag ++ encodeNatName name ++ suffix).drop 3 = encodeNatName name ++ suffix := by
    rw [List.append_assoc, ← htag, List.drop_left]
  have hfuel : name.bits.length + 1 ≤ (encodeNatName name ++ suffix).length := by
    simp only [List.length_append, encodeNatName, length_frameNameBits]
    omega
  simp only [syntaxTokenNameDigits, hdrop, parseNatNameOutput_encode name _ suffix hfuel,
    List.drop_succ_cons, List.drop_zero, pairFst_pair]

theorem syntaxNameTag_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => SyntaxNameTag (bits z) :=
  (bitStrings_eq_fppred (take_mem_FP hbits (UnaryFn.const 3)) (constFn_mem_FP _)).or
    ((bitStrings_eq_fppred (take_mem_FP hbits (UnaryFn.const 3)) (constFn_mem_FP _)).or
      (bitStrings_eq_fppred (take_mem_FP hbits (UnaryFn.const 3)) (constFn_mem_FP _)))

theorem syntaxTokenNameDigits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxTokenNameDigits (bits z)) ∈ FP := by
  have htail := drop_mem_FP hbits (UnaryFn.const 3)
  exact mem_FP_comp
    (drop_mem_FP (parseNatNameOutput_mem_FP (UnaryFn.length htail) htail) (UnaryFn.const 1))
    pairFst_mem_FP

/-- Rename the name of one token, retaining its exact constructor tag. The
empty token stays empty, which permits padding a token scan by unused iterations. -/
def renameTokenBytes (f : ℕ → ℕ) (bits : List Bool) : List Bool :=
  if SyntaxNameTag bits then
    bits.take 3 ++ encodeNatName (f (nameBitsValue (syntaxTokenNameDigits bits)))
  else bits

@[simp] theorem renameTokenBytes_nil (f : ℕ → ℕ) : renameTokenBytes f [] = [] := by
  simp [renameTokenBytes, SyntaxNameTag]

@[simp] theorem renameTokenBytes_encode (f : ℕ → ℕ) (token : SyntaxToken) :
    renameTokenBytes f token.encode = (token.mapNames f).encode := by
  have hname (a b c : Bool) (name : ℕ) :
      syntaxTokenNameDigits (a :: b :: c :: encodeNatName name) = name.bits := by
    simpa only [List.append_nil, List.cons_append, List.nil_append] using
      syntaxTokenNameDigits_named [a, b, c] rfl name []
  cases token <;> simp [renameTokenBytes, SyntaxNameTag, SyntaxToken.encode,
    SyntaxToken.mapNames, hname, nameBitsValue_bits]

/-- A binary local name map composes with exact token parsing. Its input is the
original task input paired with arbitrary binary name digits; its output remains
binary, with no polynomial bound on the numerical name value. -/
theorem renameTokenBytes_mem_FP {rename : List Bool → ℕ → ℕ} {bits : List Bool → List Bool}
    (hbits : bits ∈ FP)
    (hrename : (fun w => (rename (pairFst w) (nameBitsValue (pairSnd w))).bits) ∈ FP) :
    (fun z => renameTokenBytes (rename z) (bits z)) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hargs := mem_FP_pair hid (syntaxTokenNameDigits_mem_FP hbits)
  have hname := mem_FP_comp hargs hrename
  have hbody := Cobham.appendFn_mem_FP (take_mem_FP hbits (UnaryFn.const 3))
    (frameNameBits_mem_FP hname)
  apply mem_FP_of_eq ((syntaxNameTag_fppred hbits).ite_mem_FP hbody hbits)
  intro z
  simp only [renameTokenBytes, encodeNatName, Function.comp_apply, pairFst_pair, pairSnd_pair, id_eq]

private theorem flatMap_range_getD {α β : Type} (entries : List α) (f : α → List β)
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
        List.getElem?_cons_zero, Option.map_some, Option.getD_some,
        List.getElem?_cons_succ]
      rw [ih fuel htail]

/-- Apply one binary name transformation per constructor token. The outer loop
uses input bit length; iterations beyond the actual token list emit nothing. -/
def renameTokenStream (f : ℕ → ℕ) (bits : List Bool) : List Bool :=
  (List.range bits.length).flatMap (fun i => renameTokenBytes f (syntaxTokenBitsAt i bits))

theorem renameTokenStream_encodeQBF (f : ℕ → ℕ) (formula : QBF) :
    renameTokenStream f (encodeQBF formula) = encodeQBF (renameQBF f formula) := by
  have hbody (i : ℕ) :
      renameTokenBytes f ((((qbfTokens formula)[i]?).map SyntaxToken.encode).getD []) =
        (((qbfTokens formula)[i]?).map (fun token => (token.mapNames f).encode)).getD [] := by
    cases (qbfTokens formula)[i]? <;> simp
  unfold renameTokenStream
  simp only [syntaxTokenBitsAt_encodeQBF, hbody]
  rw [flatMap_range_getD _ _ _ (by simpa using nodeCount_le_length_encodeQBF formula)]
  rw [← encodeSyntaxTokens_qbfTokens, qbfTokens_renameQBF]
  simp only [encodeSyntaxTokens, List.flatMap_map]

theorem renameTokenStream_mem_FP {rename : List Bool → ℕ → ℕ} {bits : List Bool → List Bool}
    (hbits : bits ∈ FP)
    (hrename : (fun w => (rename (pairFst w) (nameBitsValue (pairSnd w))).bits) ∈ FP) :
    (fun z => renameTokenStream (rename z) (bits z)) ∈ FP := by
  have hmap : (fun v =>
      (rename (pairFst (pairFst v)) (nameBitsValue (pairSnd v))).bits) ∈ FP := by
    apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) hrename)
    intro v
    simp
  have hbody := renameTokenBytes_mem_FP (rename := fun w => rename (pairFst w))
    (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hbits)) hmap
  apply mem_FP_of_eq (flatMap_range_mem_FP hbody (UnaryFn.length hbits).mem_FP)
  intro z
  simp only [renameTokenStream, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate]

/-- Total encoded output of the existing structural renaming operation. Invalid
complete syntax is rejected with the empty string. -/
def renameQBFOutput (f : ℕ → ℕ) (bits : List Bool) : List Bool :=
  match decodeQBF bits with
  | none => []
  | some formula => encodeQBF (renameQBF f formula)

@[simp] theorem renameQBFOutput_encodeQBF (f : ℕ → ℕ) (formula : QBF) :
    renameQBFOutput f (encodeQBF formula) = encodeQBF (renameQBF f formula) := by
  simp [renameQBFOutput]

/-- Exact complete-syntax renaming is in actual `FP` whenever its local binary
name transformation is. No unary bound on source or target name values is used. -/
theorem renameQBFOutput_mem_FP {rename : List Bool → ℕ → ℕ} {bits : List Bool → List Bool}
    (hbits : bits ∈ FP)
    (hrename : (fun w => (rename (pairFst w) (nameBitsValue (pairSnd w))).bits) ∈ FP) :
    (fun z => renameQBFOutput (rename z) (bits z)) ∈ FP := by
  have h := (decodeQBF_success_fppred hbits).ite_mem_FP
    (renameTokenStream_mem_FP hbits hrename) (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro z
  cases hd : decodeQBF (bits z) with
  | none => simp [renameQBFOutput, hd]
  | some formula =>
    have hbytes := (decodeQBF_eq_some_iff (bits z) formula).mp hd
    simp only [hd, Option.isSome_some, ↓reduceIte, renameQBFOutput]
    rw [← hbytes, renameTokenStream_encodeQBF]

theorem encode_renameQBF_mem_FP {rename : List Bool → ℕ → ℕ} {formula : List Bool → QBF}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP)
    (hrename : (fun w => (rename (pairFst w) (nameBitsValue (pairSnd w))).bits) ∈ FP) :
    (fun z => encodeQBF (renameQBF (rename z) (formula z))) ∈ FP :=
  mem_FP_of_eq (renameQBFOutput_mem_FP hformula hrename)
    (fun z => renameQBFOutput_encodeQBF (rename z) (formula z))

/-- One environment update on arbitrary binary names has an actual runtime
certificate. This changes all matching binders and occurrences uniformly; scoped
freshening must separately manage which environment applies to each subtree. -/
theorem updateName_bits_mem_FP {source target : List Bool → ℕ}
    (hsource : (fun z => (source z).bits) ∈ FP)
    (htarget : (fun z => (target z).bits) ∈ FP) :
    (fun w => (Function.update id (source (pairFst w)) (target (pairFst w))
      (nameBitsValue (pairSnd w))).bits) ∈ FP := by
  have htest := nameBitsValue_eq_fppred pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hsource)
  have h := htest.ite_mem_FP (mem_FP_comp pairFst_mem_FP htarget)
    (nameBitsValue_bits_mem_FP pairSnd_mem_FP)
  apply mem_FP_of_eq h
  intro w
  simp only [Function.comp_apply, nameBitsValue_bits, Function.update_apply, id_eq]
  split <;> rfl

theorem encode_renameQBF_update_mem_FP {source target : List Bool → ℕ}
    {formula : List Bool → QBF} (hformula : (fun z => encodeQBF (formula z)) ∈ FP)
    (hsource : (fun z => (source z).bits) ∈ FP)
    (htarget : (fun z => (target z).bits) ∈ FP) :
    (fun z => encodeQBF (renameQBF (Function.update id (source z) (target z)) (formula z))) ∈ FP :=
  encode_renameQBF_mem_FP hformula (updateName_bits_mem_FP hsource htarget)

end IPPSPACE

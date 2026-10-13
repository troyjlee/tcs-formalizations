/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.AssignmentFP
import IPPSPACE.QBF.SyntaxTraversalFP
import IPPSPACE.Arithmetization.Matrix

/-!
# Polynomial-time direct matrix evaluation

A stack machine evaluates the existing prefix syntax from right to left. Its
values are fixed-width residue words and its variable names remain binary.
Quantifier tokens and malformed complete syntax are rejected.
-/

namespace IPPSPACE

open Complexity

/-- Total arithmetic evaluation, with explicit rejection of quantified syntax. -/
def matrixValue? {R : Type*} [CommRing R] (point : ℕ → R) : QBF → Option R
  | .var name => some (point name)
  | .tru => some 1
  | .fls => some 0
  | .neg body => (matrixValue? point body).map (1 - ·)
  | .conj left right => do
      let a ← matrixValue? point left
      let b ← matrixValue? point right
      some (a * b)
  | .disj left right => do
      let a ← matrixValue? point left
      let b ← matrixValue? point right
      some (1 - (1 - a) * (1 - b))
  | .ex _ _ | .all _ _ => none

theorem matrixValue?_eq {R : Type*} [CommRing R] (point : ℕ → R)
    (formula : QBF) (h : formula.QuantifierFree) :
    matrixValue? point formula = some (matrixEvalWithCost point formula h).1 := by
  induction formula with
  | var name => rfl
  | tru => rfl
  | fls => rfl
  | neg body ih => simp [matrixValue?, matrixEvalWithCost, ih h]
  | conj left right ihleft ihright =>
    simp [matrixValue?, matrixEvalWithCost, ihleft (QBF.quantifierFree_conj.mp h).1,
      ihright (QBF.quantifierFree_conj.mp h).2]
  | disj left right ihleft ihright =>
    have hs : left.QuantifierFree ∧ right.QuantifierFree := by
      simpa [QBF.QuantifierFree, QBF.quantDepth] using h
    simp [matrixValue?, matrixEvalWithCost, ihleft hs.1, ihright hs.2]
  | ex name body _ => exact (Nat.succ_ne_zero body.quantDepth h).elim
  | all name body _ => exact (Nat.succ_ne_zero body.quantDepth h).elim

theorem matrixValue?_isSome {R : Type*} [CommRing R] (point : ℕ → R) (formula : QBF) :
    (matrixValue? point formula).isSome = true ↔ formula.QuantifierFree := by
  induction formula with
  | var name => simp [matrixValue?, QBF.QuantifierFree, QBF.quantDepth]
  | tru => simp [matrixValue?, QBF.QuantifierFree, QBF.quantDepth]
  | fls => simp [matrixValue?, QBF.QuantifierFree, QBF.quantDepth]
  | neg body ih => simpa [matrixValue?, QBF.QuantifierFree, QBF.quantDepth] using ih
  | conj left right ihleft ihright | disj left right ihleft ihright =>
    cases hl : matrixValue? point left <;> cases hr : matrixValue? point right <;>
      simp_all [matrixValue?, QBF.QuantifierFree, QBF.quantDepth]
  | ex name body _ => simp [matrixValue?, QBF.QuantifierFree, QBF.quantDepth]
  | all name body _ => simp [matrixValue?, QBF.QuantifierFree, QBF.quantDepth]

/-- One token acts on the value stack. Reversing prefix order puts the left
child at the top and the right child immediately below it. -/
def matrixTokenStack {R : Type*} [CommRing R] (point : ℕ → R) :
    SyntaxToken → List R → Option (List R)
  | .var name, stack => some (point name :: stack)
  | .tru, stack => some (1 :: stack)
  | .fls, stack => some (0 :: stack)
  | .neg, a :: stack => some ((1 - a) :: stack)
  | .conj, a :: b :: stack => some ((a * b) :: stack)
  | .disj, a :: b :: stack => some ((1 - (1 - a) * (1 - b)) :: stack)
  | _, _ => none

/-- Evaluate a token list from its last token to its first. -/
def matrixTokensStack {R : Type*} [CommRing R] (point : ℕ → R) :
    List SyntaxToken → List R → Option (List R)
  | [], stack => some stack
  | token :: tokens, stack => (matrixTokensStack point tokens stack).bind (matrixTokenStack point token)

theorem matrixTokensStack_append {R : Type*} [CommRing R] (point : ℕ → R)
    (left right : List SyntaxToken) (stack : List R) :
    matrixTokensStack point (left ++ right) stack =
      (matrixTokensStack point right stack).bind (matrixTokensStack point left) := by
  induction left with
  | nil => simp [matrixTokensStack]
  | cons token left ih => simp [matrixTokensStack, ih, Option.bind_assoc]

/-- Exact stack semantics for the entire original syntax, including rejection
of every formula containing a quantifier. -/
theorem matrixTokensStack_qbfTokens {R : Type*} [CommRing R] (point : ℕ → R)
    (formula : QBF) (stack : List R) :
    matrixTokensStack point (qbfTokens formula) stack =
      (matrixValue? point formula).map (· :: stack) := by
  induction formula generalizing stack with
  | var name => rfl
  | tru => rfl
  | fls => rfl
  | neg body ih =>
    simp only [qbfTokens, matrixTokensStack, ih, matrixValue?]
    cases matrixValue? point body <;> rfl
  | conj left right ihleft ihright | disj left right ihleft ihright =>
    simp only [qbfTokens, matrixTokensStack, matrixTokensStack_append, ihright]
    cases hl : matrixValue? point left <;> cases hr : matrixValue? point right <;>
      simp [ihleft, hl, matrixTokenStack, matrixValue?, hr]
  | ex name body ih | all name body ih =>
    simp only [qbfTokens, matrixTokensStack, ih, matrixValue?]
    cases matrixValue? point body <;> rfl

/-- Failed stacks are empty; successful stacks have a tag even when no value
has been pushed yet. Their payload is the existing fixed-width message codec. -/
def encodeMatrixStack {p : ℕ} : Option (List (ZMod p)) → List Bool
  | none => []
  | some stack => true :: encodeMessage stack

/-- Replace the first `removed` values by one canonical word. -/
def matrixStackReplace (p removed : ℕ) (value state : List Bool) : List Bool :=
  if state ≠ [] ∧ CanonicalResidueBits p value then
    true :: (value ++ (state.drop 1).drop (removed * residueWidth p))
  else []

def matrixStackFirst (p : ℕ) (state : List Bool) : List Bool :=
  (state.drop 1).take (residueWidth p)

def matrixStackSecond (p : ℕ) (state : List Bool) : List Bool :=
  ((state.drop 1).drop (residueWidth p)).take (residueWidth p)

/-- A variable token's canonical binary name, retained in binary. -/
def matrixTokenNameBits (token : List Bool) : List Bool :=
  pairFst ((parseNatNameOutput (token.drop 3).length (token.drop 3)).drop 1)

/-- The encoded stack update is total on every token, state, and assignment
string. Its semantic theorem below uses canonical internal assignments. -/
def matrixTokenBitsStep (p : ℕ) (assignments token state : List Bool) : List Bool :=
  let one := roundConstantBits p 1
  let a := matrixStackFirst p state
  let b := matrixStackSecond p state
  if token.take 3 = [false, false, false] then
    matrixStackReplace p 0 (assignmentLookupBits p (matrixTokenNameBits token) assignments) state
  else if token.take 3 = [false, false, true] then matrixStackReplace p 0 one state
  else if token.take 3 = [false, true, false] then matrixStackReplace p 0 (roundConstantBits p 0) state
  else if token.take 3 = [false, true, true] then
    matrixStackReplace p 1 (checkedResidueBitsBinary p (fun x y => x + p - y) one a) state
  else if token.take 3 = [true, false, false] then
    matrixStackReplace p 2 (checkedResidueBitsBinary p (· * ·) a b) state
  else if token.take 3 = [true, false, true] then
    matrixStackReplace p 2 (combineRoundBits p 1 [] a b) state
  else []

theorem matrixStackReplace_mem_FP {p removed : List Bool → ℕ}
    {value state : List Bool → List Bool} (hp : UnaryFn p) (hr : UnaryFn removed)
    (hv : value ∈ FP) (hs : state ∈ FP) :
    (fun z => matrixStackReplace (p z) (removed z) (value z) (state z)) ∈ FP :=
  ((bitStrings_eq_fppred hs (constFn_mem_FP [])).not.and
    (canonicalResidueBits_fppred hp hv)).ite_mem_FP
      (mem_FP_comp (Cobham.appendFn_mem_FP hv
        (drop_mem_FP (drop_mem_FP hs (UnaryFn.const 1)) (hr.mul (residueWidth_unaryFn hp))))
        (Cobham.cons_mem_FP true)) (constFn_mem_FP [])

theorem matrixStackFirst_mem_FP {p : List Bool → ℕ} {state : List Bool → List Bool}
    (hp : UnaryFn p) (hs : state ∈ FP) :
    (fun z => matrixStackFirst (p z) (state z)) ∈ FP :=
  take_mem_FP (drop_mem_FP hs (UnaryFn.const 1)) (residueWidth_unaryFn hp)

theorem matrixStackSecond_mem_FP {p : List Bool → ℕ} {state : List Bool → List Bool}
    (hp : UnaryFn p) (hs : state ∈ FP) :
    (fun z => matrixStackSecond (p z) (state z)) ∈ FP :=
  take_mem_FP (drop_mem_FP (drop_mem_FP hs (UnaryFn.const 1)) (residueWidth_unaryFn hp))
    (residueWidth_unaryFn hp)

theorem matrixTokenNameBits_mem_FP {token : List Bool → List Bool} (ht : token ∈ FP) :
    (fun z => matrixTokenNameBits (token z)) ∈ FP := by
  have hd := drop_mem_FP ht (UnaryFn.const 3)
  exact mem_FP_comp (drop_mem_FP (parseNatNameOutput_mem_FP (UnaryFn.length hd) hd)
    (UnaryFn.const 1)) pairFst_mem_FP

theorem matrixTokenBitsStep_mem_FP {p : List Bool → ℕ}
    {assignments token state : List Bool → List Bool} (hp : UnaryFn p)
    (hassign : assignments ∈ FP) (ht : token ∈ FP) (hs : state ∈ FP) :
    (fun z => matrixTokenBitsStep (p z) (assignments z) (token z) (state z)) ∈ FP := by
  have htag (tag : List Bool) :=
    bitStrings_eq_fppred (take_mem_FP ht (UnaryFn.const 3)) (constFn_mem_FP tag)
  have hone := reduceResidueWord_bits_mem_FP hp (UnaryFn.const 1)
  have ha := matrixStackFirst_mem_FP hp hs
  have hb := matrixStackSecond_mem_FP hp hs
  exact (htag [false, false, false]).ite_mem_FP
    (matrixStackReplace_mem_FP hp (UnaryFn.const 0)
      (assignmentLookupBits_mem_FP hp (matrixTokenNameBits_mem_FP ht) hassign) hs)
    ((htag [false, false, true]).ite_mem_FP
      (matrixStackReplace_mem_FP hp (UnaryFn.const 0) hone hs)
      ((htag [false, true, false]).ite_mem_FP
        (matrixStackReplace_mem_FP hp (UnaryFn.const 0)
          (reduceResidueWord_bits_mem_FP hp (UnaryFn.const 0)) hs)
        ((htag [false, true, true]).ite_mem_FP
          (matrixStackReplace_mem_FP hp (UnaryFn.const 1) (residueBitsSub_mem_FP hp hone ha) hs)
          ((htag [true, false, false]).ite_mem_FP
            (matrixStackReplace_mem_FP hp (UnaryFn.const 2) (residueBitsMul_mem_FP hp ha hb) hs)
            ((htag [true, false, true]).ite_mem_FP
              (matrixStackReplace_mem_FP hp (UnaryFn.const 2)
                (combineRoundBits_mem_FP hp (UnaryFn.const 1) (constFn_mem_FP []) ha hb) hs)
              (constFn_mem_FP []))))))

/-- Every update adds at most one fixed-width value, even on malformed data. -/
theorem matrixStackReplace_length_le (p removed : ℕ) (value state : List Bool) :
    (matrixStackReplace p removed value state).length ≤ state.length + residueWidth p := by
  unfold matrixStackReplace
  split
  · rename_i h
    have hs : 0 < state.length := List.length_pos_iff.mpr h.1
    simp only [List.length_cons, List.length_append, List.length_drop, h.2.1]
    omega
  · simp

theorem matrixTokenBitsStep_length_le (p : ℕ) (assignments token state : List Bool) :
    (matrixTokenBitsStep p assignments token state).length ≤ state.length + residueWidth p := by
  unfold matrixTokenBitsStep
  split <;> (try exact matrixStackReplace_length_le ..)
  split <;> (try exact matrixStackReplace_length_le ..)
  split <;> (try exact matrixStackReplace_length_le ..)
  split <;> (try exact matrixStackReplace_length_le ..)
  split <;> (try exact matrixStackReplace_length_le ..)
  split <;> (try exact matrixStackReplace_length_le ..)
  simp

/-- Bounded reverse traversal of prefix tokens, with an initially empty stack. -/
def matrixStackLoop (p : ℕ) (assignments bits : List Bool) (count : ℕ) : ℕ → List Bool
  | 0 => [true]
  | n + 1 => matrixTokenBitsStep p assignments (syntaxTokenBitsAt (count - (n + 1)) bits)
      (matrixStackLoop p assignments bits count n)

theorem matrixStackLoop_length_le (p : ℕ) (assignments bits : List Bool) (count n : ℕ) :
    (matrixStackLoop p assignments bits count n).length ≤ 1 + n * residueWidth p := by
  induction n with
  | zero => simp [matrixStackLoop]
  | succ n ih =>
    have h := matrixTokenBitsStep_length_le p assignments
      (syntaxTokenBitsAt (count - (n + 1)) bits) (matrixStackLoop p assignments bits count n)
    simp only [matrixStackLoop, Nat.add_mul, Nat.one_mul]
    omega

/-- Actual upstream machine-time certificate. Both the iteration count and
residue width are polynomially bounded, and the full stack has linear growth. -/
theorem matrixStackLoop_mem_FP {p count : List Bool → ℕ}
    {assignments bits : List Bool → List Bool} (hp : UnaryFn p) (hc : UnaryFn count)
    (hassign : assignments ∈ FP) (hbits : bits ∈ FP) :
    (fun z => matrixStackLoop (p z) (assignments z) (bits z) (count z) (count z)) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  let original : List Bool → List Bool := fun z => pairFst (pairFst z)
  let state : List Bool → List Bool := fun z => pairSnd (pairFst z)
  have ho : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs : state ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hn : UnaryFn fun z => (pairSnd z).length + 1 :=
    (UnaryFn.length pairSnd_mem_FP).add (UnaryFn.const 1)
  have hi := (hc.comp ho).sub hn
  have hstep := matrixTokenBitsStep_mem_FP (hp.comp ho) (mem_FP_comp ho hassign)
    (syntaxTokenBitsAt_mem_FP hi (mem_FP_comp ho hbits)) hs
  obtain ⟨pc, hpc⟩ := Cobham.output_length_poly_of_mem_FP hc.mem_FP
  obtain ⟨pw, hpw⟩ := Cobham.output_length_poly_of_mem_FP (residueWidth_unaryFn hp).mem_FP
  have h := recFold_mem_FP_of_bound
    (g := fun z t => matrixStackLoop (p z) (assignments z) (bits z) (count z) t.length)
    (w := id) (E := fun _ => [true]) hstep hstep (constFn_mem_FP [true]) hid hc.mem_FP
    (by intro z; rfl)
    (by intro z t; simp [original, state, matrixStackLoop])
    (by intro z t; simp [original, state, matrixStackLoop])
    ((PolyBound.const 1).add ((PolyBound.eval pc).mul (PolyBound.eval pw)))
    (by
      intro z t ht
      have htc : t.length ≤ count z := by simpa using ht.length_le
      have hc' : count z ≤ pc.eval z.length := by simpa using hpc z
      have hw' : residueWidth (p z) ≤ pw.eval z.length := by simpa using hpw z
      exact (matrixStackLoop_length_le _ _ _ _ _).trans
        (Nat.add_le_add_left (Nat.mul_le_mul (htc.trans hc') hw') 1))
  exact mem_FP_of_eq h (fun z => by simp)

private theorem drop_encodeMessage {p : ℕ} (stack : List (ZMod p)) (n : ℕ) :
    (encodeMessage stack).drop (n * residueWidth p) = encodeMessage (stack.drop n) := by
  induction n generalizing stack with
  | zero => simp
  | succ n ih =>
    cases stack with
    | nil => simp [encodeMessage]
    | cons a stack =>
      simp only [encodeMessage, Nat.add_mul, Nat.one_mul]
      rw [Nat.add_comm, ← List.drop_drop]
      simpa using ih stack

@[simp] theorem matrixStackReplace_nil (p removed : ℕ) (value : List Bool) :
    matrixStackReplace p removed value [] = [] := by simp [matrixStackReplace]

@[simp] theorem canonicalResidueBits_nil (p : ℕ) : ¬ CanonicalResidueBits p [] := by
  simp [CanonicalResidueBits, residueWidth]

@[simp] theorem matrixStackReplace_value_nil (p removed : ℕ) (state : List Bool) :
    matrixStackReplace p removed [] state = [] := by simp [matrixStackReplace]

@[simp] theorem matrixStackReplace_encode {p : ℕ} [NeZero p] (removed : ℕ)
    (value : ZMod p) (stack : List (ZMod p)) :
    matrixStackReplace p removed (wordBits (encodeResidue value)) (encodeMatrixStack (some stack)) =
      encodeMatrixStack (some (value :: stack.drop removed)) := by
  simp [matrixStackReplace, encodeMatrixStack, drop_encodeMessage, encodeMessage, value.val_lt]

@[simp] theorem matrixStackFirst_encode_nil (p : ℕ) :
    matrixStackFirst p (encodeMatrixStack (some ([] : List (ZMod p)))) = [] := by
  simp [matrixStackFirst, encodeMatrixStack, encodeMessage]

@[simp] theorem matrixStackFirst_encode_cons {p : ℕ} (a : ZMod p) (stack : List (ZMod p)) :
    matrixStackFirst p (encodeMatrixStack (some (a :: stack))) = wordBits (encodeResidue a) := by
  simp [matrixStackFirst, encodeMatrixStack, encodeMessage]

@[simp] theorem matrixStackSecond_encode_nil (p : ℕ) :
    matrixStackSecond p (encodeMatrixStack (some ([] : List (ZMod p)))) = [] := by
  simp [matrixStackSecond, encodeMatrixStack, encodeMessage]

@[simp] theorem matrixStackSecond_encode_single {p : ℕ} (a : ZMod p) :
    matrixStackSecond p (encodeMatrixStack (some [a])) = [] := by
  simp [matrixStackSecond, encodeMatrixStack, encodeMessage]

@[simp] theorem matrixStackSecond_encode_cons {p : ℕ} (a b : ZMod p) (stack : List (ZMod p)) :
    matrixStackSecond p (encodeMatrixStack (some (a :: b :: stack))) = wordBits (encodeResidue b) := by
  simp [matrixStackSecond, encodeMatrixStack, encodeMessage]

@[simp] theorem matrixTokenNameBits_encode (name : ℕ) :
    matrixTokenNameBits (SyntaxToken.var name).encode = name.bits := by
  have h := parseNatNameOutput_encode name (encodeNatName name).length [] (by
    rw [length_encodeNatName, Nat.size_eq_bits_len]; omega)
  simp only [List.append_nil] at h
  simp [matrixTokenNameBits, SyntaxToken.encode, h]

private theorem matrixSubBits_encode {p : ℕ} [NeZero p] (a b : ZMod p) :
    checkedResidueBitsBinary p (fun x y => x + p - y) (wordBits (encodeResidue a))
      (wordBits (encodeResidue b)) = wordBits (encodeResidue (a - b)) := by
  rw [checkedResidueBitsBinary_wordBits, ← wordSub, wordSub_encodeResidue]
  rfl

private theorem matrixMulBits_encode {p : ℕ} [NeZero p] (a b : ZMod p) :
    checkedResidueBitsBinary p (· * ·) (wordBits (encodeResidue a))
      (wordBits (encodeResidue b)) = wordBits (encodeResidue (a * b)) := by
  rw [checkedResidueBitsBinary_wordBits, ← wordMul, wordMul_encodeResidue]
  rfl

@[simp] theorem checkedResidueBitsBinary_nil_left (p : ℕ) (f : ℕ → ℕ → ℕ) (b : List Bool) :
    checkedResidueBitsBinary p f [] b = [] := by simp [checkedResidueBitsBinary]

@[simp] theorem checkedResidueBitsBinary_nil_right (p : ℕ) (f : ℕ → ℕ → ℕ) (a : List Bool) :
    checkedResidueBitsBinary p f a [] = [] := by simp [checkedResidueBitsBinary]

private theorem matrixDisjBits_encode {p : ℕ} [NeZero p] (a b : ZMod p) :
    combineRoundBits p 1 [] (wordBits (encodeResidue a)) (wordBits (encodeResidue b)) =
      wordBits (encodeResidue (1 - (1 - a) * (1 - b))) := by
  dsimp [combineRoundBits]
  rw [roundConstantBits_eq]
  simp only [Nat.cast_one, matrixSubBits_encode, matrixMulBits_encode]

@[simp] theorem encodeMatrixStack_none (p : ℕ) :
    encodeMatrixStack (p := p) none = [] := rfl

/-- The raw update implements exactly one semantic stack instruction on
canonical values and assignments, including underflow and quantifier rejection. -/
theorem matrixTokenBitsStep_encode {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (token : SyntaxToken) (stack : Option (List (ZMod p))) :
    matrixTokenBitsStep p (encodeAssignmentEntries entries) token.encode (encodeMatrixStack stack) =
      encodeMatrixStack (stack.bind (matrixTokenStack (fun i => (assignmentLookupWithCost entries i).1) token)) := by
  cases stack with
  | none => cases token <;> simp [matrixTokenBitsStep, SyntaxToken.encode]
  | some stack =>
    cases token with
    | var name =>
      have hn := matrixTokenNameBits_encode name
      change matrixTokenNameBits (false :: false :: false :: encodeNatName name) = name.bits at hn
      simp [matrixTokenBitsStep, SyntaxToken.encode, hn, matrixTokenStack]
    | tru => simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack]
    | fls => simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack]
    | neg =>
      cases stack <;> simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack,
        matrixSubBits_encode, -checkedResidueBitsBinary_wordBits]
    | conj =>
      cases stack with
      | nil => simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack]
      | cons a stack => cases stack <;>
          simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack, matrixMulBits_encode,
            -checkedResidueBitsBinary_wordBits]
    | disj =>
      cases stack with
      | nil => simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack, combineRoundBits]
      | cons a stack => cases stack <;>
          simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack,
            combineRoundBits, matrixMulBits_encode, matrixSubBits_encode,
            -checkedResidueBitsBinary_wordBits]
    | ex name => simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack]
    | all name => simp [matrixTokenBitsStep, SyntaxToken.encode, matrixTokenStack]

/-- The bounded loop evaluates exactly the last `n` tokens. This invariant
connects the actual string machine to the syntax-level stack semantics. -/
theorem matrixStackLoop_encode {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (tokens : List SyntaxToken) (n : ℕ)
    (hn : n ≤ tokens.length) :
    matrixStackLoop p (encodeAssignmentEntries entries) (encodeSyntaxTokens tokens) tokens.length n =
      encodeMatrixStack (matrixTokensStack (fun i => (assignmentLookupWithCost entries i).1)
        (tokens.drop (tokens.length - n)) []) := by
  induction n with
  | zero => simp [matrixStackLoop, matrixTokensStack, encodeMatrixStack, encodeMessage]
  | succ n ih =>
    have hi : tokens.length - (n + 1) < tokens.length := by omega
    have he : tokens.length - (n + 1) + 1 = tokens.length - n := by omega
    rw [matrixStackLoop, ih (by omega), syntaxTokenBitsAt_encodeSyntaxTokens,
      List.getElem?_eq_getElem hi]
    simp only [Option.map_some, Option.getD_some]
    rw [matrixTokenBitsStep_encode, List.drop_eq_getElem_cons hi, he, matrixTokensStack]

theorem matrixStackLoop_encodeQBF {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (formula : QBF) :
    matrixStackLoop p (encodeAssignmentEntries entries) (encodeQBF formula)
      (nodeCount formula) (nodeCount formula) =
      encodeMatrixStack ((matrixValue? (fun i => (assignmentLookupWithCost entries i).1) formula).map
        (fun value => [value])) := by
  have h := matrixStackLoop_encode entries (qbfTokens formula) (qbfTokens formula).length le_rfl
  simpa only [encodeSyntaxTokens_qbfTokens, length_qbfTokens, Nat.sub_self, List.drop_zero,
    matrixTokensStack_qbfTokens] using h

/-- Decode exactly one complete formula, evaluate its matrix by the bounded
stack machine, and return a single residue word. The empty result means failure. -/
def evaluateMatrixBits (p : ℕ) (assignments bits : List Bool) : List Bool :=
  let count := ((decodeQBF bits).map nodeCount).getD 0
  let state := matrixStackLoop p assignments bits count count
  if (decodeQBF bits).isSome ∧ state ≠ [] ∧ (state.drop 1).length = residueWidth p then
    state.drop 1
  else []

theorem evaluateMatrixBits_mem_FP {p : List Bool → ℕ}
    {assignments bits : List Bool → List Bool} (hp : UnaryFn p)
    (hassign : assignments ∈ FP) (hbits : bits ∈ FP) :
    (fun z => evaluateMatrixBits (p z) (assignments z) (bits z)) ∈ FP := by
  have hstate := matrixStackLoop_mem_FP hp (decodeQBF_nodeCount_unaryFn hbits) hassign hbits
  have hvalue := drop_mem_FP hstate (UnaryFn.const 1)
  exact ((decodeQBF_success_fppred hbits).and
    ((bitStrings_eq_fppred hstate (constFn_mem_FP [])).not.and
      (FPPred.eq (UnaryFn.length hvalue) (residueWidth_unaryFn hp)))).ite_mem_FP
    hvalue (constFn_mem_FP [])

/-- Raw malformed input and trailing material are rejected, using the original
full-consumption decoder, independently of the assignment representation. -/
theorem evaluateMatrixBits_decode_failure (p : ℕ) (assignments bits : List Bool)
    (h : decodeQBF bits = none) : evaluateMatrixBits p assignments bits = [] := by
  simp [evaluateMatrixBits, h]

/-- Exact semantic refinement on canonical assignments, for arbitrary syntax.
Every quantified formula is rejected by the total matrix evaluator. -/
@[simp] theorem evaluateMatrixBits_encodeQBF {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (formula : QBF) :
    evaluateMatrixBits p (encodeAssignmentEntries entries) (encodeQBF formula) =
      ((matrixValue? (fun i => (assignmentLookupWithCost entries i).1) formula).map
        (fun value => wordBits (encodeResidue value))).getD [] := by
  simp only [evaluateMatrixBits, decodeQBF_encodeQBF, Option.map_some, Option.getD_some,
    matrixStackLoop_encodeQBF]
  cases matrixValue? (fun i => (assignmentLookupWithCost entries i).1) formula <;>
    simp [encodeMatrixStack, encodeMessage]

/-- Full raw-string parser/evaluator agreement, including malformed and
trailing inputs. Assignment entries retain newest-match/default-zero semantics. -/
theorem evaluateMatrixBits_eq {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (bits : List Bool) :
    evaluateMatrixBits p (encodeAssignmentEntries entries) bits =
      (((decodeQBF bits).bind
        (matrixValue? (fun i => (assignmentLookupWithCost entries i).1))).map
          (fun value => wordBits (encodeResidue value))).getD [] := by
  cases h : decodeQBF bits with
  | none => simp [evaluateMatrixBits_decode_failure _ _ _ h]
  | some formula =>
    have he := (decodeQBF_eq_some_iff bits formula).mp h
    rw [← he, evaluateMatrixBits_encodeQBF]
    rfl

/-- The exact existing direct matrix value has an actual upstream FP witness.
Variable names can be arbitrarily large binary names; no numeric name bound is
assumed. The finite assignment itself is supplied through its canonical codec. -/
theorem matrixEvalWithCost_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (formula : List Bool → QBF) (hformula : ∀ z, (formula z).QuantifierFree)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z)))
    (hsyntax : (fun z => encodeQBF (formula z)) ∈ FP)
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP) :
    (fun z => wordBits (encodeResidue
      (matrixEvalWithCost (c z).point (formula z) (hformula z)).1)) ∈ FP := by
  have hentries : (fun z => encodeAssignmentEntries (c z).entries) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hc pairFst_mem_FP) (fun z => pairFst_encodeFiniteClaim (c z))
  apply mem_FP_of_eq (evaluateMatrixBits_mem_FP hp hentries hsyntax)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  rw [evaluateMatrixBits_encodeQBF]
  change ((matrixValue? (c z).point (formula z)).map _).getD [] = _
  rw [matrixValue?_eq _ _ (hformula z)]
  rfl

/-- The polynomial's value is computed by direct syntax traversal; the FP
witness does not expand the multivariate polynomial. -/
theorem arithmetize_matrix_eval_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (formula : List Bool → QBF) (hformula : ∀ z, (formula z).QuantifierFree)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z)))
    (hsyntax : (fun z => encodeQBF (formula z)) ∈ FP)
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP) :
    (fun z => wordBits (encodeResidue
      (MvPolynomial.eval (c z).point (arithmetize (formula z))))) ∈ FP :=
  mem_FP_of_eq (matrixEvalWithCost_bits_mem_FP hp hnz formula hformula c hsyntax hc)
    (fun z => by rw [matrixEvalWithCost_value])

/-- Every raw result is either failure or exactly one residue-width word. -/
theorem evaluateMatrixBits_length_le (p : ℕ) (assignments bits : List Bool) :
    (evaluateMatrixBits p assignments bits).length ≤ residueWidth p := by
  dsimp only [evaluateMatrixBits]
  split
  · rename_i h
    exact Nat.le_of_eq h.2.2
  · simp

/-- On canonical assignments, failure is exactly invalid full syntax or a
formula containing a quantifier. -/
theorem evaluateMatrixBits_eq_nil_iff {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (bits : List Bool) :
    evaluateMatrixBits p (encodeAssignmentEntries entries) bits = [] ↔
      ¬ ∃ formula, decodeQBF bits = some formula ∧ formula.QuantifierFree := by
  rw [evaluateMatrixBits_eq]
  cases hd : decodeQBF bits with
  | none => simp
  | some formula =>
    simp only [Option.bind_some, Option.some.injEq]
    have hs := matrixValue?_isSome (fun i => (assignmentLookupWithCost entries i).1) formula
    cases hv : matrixValue? (fun i => (assignmentLookupWithCost entries i).1) formula with
    | none => simpa [hv] using hs.not
    | some value =>
      have hnonempty : wordBits (encodeResidue value) ≠ [] := List.cons_ne_nil _ _
      simp only [Option.map_some, Option.getD_some, hnonempty, false_iff, not_not]
      exact ⟨formula, rfl, hs.mp (by simp [hv])⟩

/-- The exact parser and direct arithmetic evaluator composed on canonical
finite assignments form an actual FP string function. -/
theorem parseQBF_matrixValue_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (entries : (z : List Bool) → List (ℕ × ZMod (p z)))
    {bits : List Bool → List Bool}
    (hentries : (fun z => encodeAssignmentEntries (entries z)) ∈ FP) (hbits : bits ∈ FP) :
    (fun z => (((decodeQBF (bits z)).bind
        (matrixValue? (fun i => (assignmentLookupWithCost (entries z) i).1))).map
          (fun value => wordBits (encodeResidue value))).getD []) ∈ FP := by
  apply mem_FP_of_eq (evaluateMatrixBits_mem_FP hp hentries hbits)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  exact evaluateMatrixBits_eq (entries z) (bits z)

/-- The finite verifier's final comparison is polynomial-time, including all
assignment lookups and fixed-width field arithmetic. -/
theorem matrixTerminalCheck_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (formula : List Bool → QBF) (hformula : ∀ z, (formula z).QuantifierFree)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z)))
    (hsyntax : (fun z => encodeQBF (formula z)) ∈ FP)
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP) :
    (fun z => [decide ((matrixEvalWithCost (c z).point (formula z) (hformula z)).1 =
      (c z).value)]) ∈ FP := by
  have heval := matrixEvalWithCost_bits_mem_FP hp hnz formula hformula c hsyntax hc
  have hvalue : (fun z => wordBits (encodeResidue (c z).value)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hc pairSnd_mem_FP) (fun z => pairSnd_encodeFiniteClaim (c z))
  have htest := (bitStrings_eq_fppred heval hvalue).of_iff (fun z => by
    let : NeZero (p z) := ⟨hnz z⟩
    constructor
    · intro h
      have hv := congrArg Nat.fromBits h
      simp only [fromBits_wordBits, encodeResidue_toNat] at hv
      exact ZMod.val_injective (p z) hv
    · intro h
      rw [h])
  exact htest.flag_mem_FP

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexParsingFP
import IPPSPACE.QBF.RenamingFP
import IPPSPACE.Arithmetization.Schedule
import IPPSPACE.Protocol.RoundFP

/-!
# Polynomial-time construction of the existing verifier schedule

Operator coordinates stay binary. Reduction uses the existing variable token;
quantification uses its existing existential/universal token. Concatenation is
unambiguous because the token codec is self-delimiting. Matrix variables retain
their original occurrence order and repetitions.
-/

namespace IPPSPACE

open Complexity

def AlgebraicOperator.syntaxToken : AlgebraicOperator → SyntaxToken
  | .reduce i => .var i
  | .quantify q => q.token

def encodeOperatorSchedule (ops : List AlgebraicOperator) : List Bool :=
  encodeSyntaxTokens (ops.map AlgebraicOperator.syntaxToken)

@[simp] theorem encodeOperatorSchedule_nil : encodeOperatorSchedule [] = [] := rfl

@[simp] theorem encodeOperatorSchedule_cons (op : AlgebraicOperator) (ops : List AlgebraicOperator) :
    encodeOperatorSchedule (op :: ops) = op.syntaxToken.encode ++ encodeOperatorSchedule ops := rfl

@[simp] theorem encodeOperatorSchedule_append (ops more : List AlgebraicOperator) :
    encodeOperatorSchedule (ops ++ more) = encodeOperatorSchedule ops ++ encodeOperatorSchedule more := by
  simp [encodeOperatorSchedule]

def variableTokenBytes (bits : List Bool) : List Bool := if VariableTokenBits bits then bits else []

@[simp] theorem variableTokenBytes_nil : variableTokenBytes [] = [] := by simp [variableTokenBytes]

theorem variableTokenBytes_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => variableTokenBytes (bits z)) ∈ FP :=
  (variableTokenBits_fppred hbits).ite_mem_FP hbits (constFn_mem_FP [])

private theorem schedule_flatMap_range_getD {α β : Type} (entries : List α) (f : α → List β)
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

theorem variableTokenBytes_qbfTokens (φ : QBF) (hφ : φ.QuantifierFree) :
    (qbfTokens φ).flatMap (fun token => variableTokenBytes token.encode) =
      encodeSyntaxTokens ((freeVarList φ).map SyntaxToken.var) := by
  induction φ <;> simp_all [qbfTokens, freeVarList, encodeSyntaxTokens, variableTokenBytes,
    VariableTokenBits, SyntaxToken.encode, QBF.QuantifierFree, QBF.quantDepth]

/-- Extract the variable occurrence stream, with one canonical token per occurrence. -/
def matrixVariableBits (bits : List Bool) : List Bool :=
  (List.range bits.length).flatMap (fun i => variableTokenBytes (syntaxTokenBitsAt i bits))

theorem matrixVariableBits_encodeQBF (φ : QBF) (hφ : φ.QuantifierFree) :
    matrixVariableBits (encodeQBF φ) = encodeSyntaxTokens ((freeVarList φ).map SyntaxToken.var) := by
  have hbody (i : ℕ) :
      variableTokenBytes ((((qbfTokens φ)[i]?).map SyntaxToken.encode).getD []) =
        (((qbfTokens φ)[i]?).map (fun token => variableTokenBytes token.encode)).getD [] := by
    cases (qbfTokens φ)[i]? <;> simp
  unfold matrixVariableBits
  simp only [syntaxTokenBitsAt_encodeQBF, hbody]
  rw [schedule_flatMap_range_getD _ _ _ (by simpa using nodeCount_le_length_encodeQBF φ)]
  exact variableTokenBytes_qbfTokens φ hφ

theorem matrixVariableBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => matrixVariableBits (bits z)) ∈ FP := by
  have hbody := variableTokenBytes_mem_FP
    (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hbits))
  apply mem_FP_of_eq (flatMap_range_mem_FP hbody (UnaryFn.length hbits).mem_FP)
  intro z
  simp only [matrixVariableBits, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate]

theorem encode_reductionSchedule (is : List ℕ) (qs : List Quantifier) :
    encodeOperatorSchedule (reductionSchedule is qs) =
      qs.flatMap (fun q => encodeSyntaxTokens (is.map SyntaxToken.var) ++ q.token.encode) ++
        encodeSyntaxTokens (is.map SyntaxToken.var) := by
  have hreduce : encodeOperatorSchedule (is.map AlgebraicOperator.reduce) =
      encodeSyntaxTokens (is.map SyntaxToken.var) := by
    simp [encodeOperatorSchedule, List.map_map, Function.comp_def, AlgebraicOperator.syntaxToken]
  induction qs with
  | nil => simpa [reductionSchedule] using hreduce
  | cons q qs ih =>
    simp [reductionSchedule, ih, hreduce, AlgebraicOperator.syntaxToken, List.append_assoc]

def rawPrenexScheduleBits (bits : List Bool) : List Bool :=
  let varBits := matrixVariableBits (prenexMatrixBits bits)
  (List.range (prenexPrefixCount bits)).flatMap
      (fun i => varBits ++ syntaxTokenBitsAt i (prenexPrefixBits bits)) ++ varBits

theorem rawPrenexScheduleBits_encode (φ : PrenexQBF) :
    rawPrenexScheduleBits (encodeQBF φ.toQBF) = encodeOperatorSchedule φ.schedule := by
  have hbody (i : ℕ) (hi : i < φ.quantifiers.length) :
      syntaxTokenBitsAt i (encodeSyntaxTokens (φ.quantifiers.map Quantifier.token)) =
        φ.quantifiers[i].token.encode := by
    rw [syntaxTokenBitsAt_encodeSyntaxTokens]
    simp only [List.getElem?_eq_getElem (by simpa using hi : i < (φ.quantifiers.map Quantifier.token).length),
      List.getElem_map, Option.map_some, Option.getD_some]
  simp only [rawPrenexScheduleBits, prenexMatrixBits_encode_prenex,
    matrixVariableBits_encodeQBF _ φ.matrix_quantifierFree, prenexPrefixCount_encode_prenex,
    prenexPrefixBits_encode_prenex, PrenexQBF.schedule, encode_reductionSchedule]
  congr 1
  calc
    _ = (List.range φ.quantifiers.length).flatMap (fun i =>
        ((φ.quantifiers[i]?).map (fun q =>
          encodeSyntaxTokens ((freeVarList φ.matrix).map SyntaxToken.var) ++ q.token.encode)).getD []) := by
      apply List.flatMap_congr
      intro i hi
      have hlt := List.mem_range.mp hi
      rw [hbody i hlt, List.getElem?_eq_getElem hlt]
      rfl
    _ = _ := schedule_flatMap_range_getD _ _ _ le_rfl

theorem rawPrenexScheduleBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => rawPrenexScheduleBits (bits z)) ∈ FP := by
  have hv := matrixVariableBits_mem_FP (prenexMatrixBits_mem_FP hbits)
  have hentry := Cobham.appendFn_mem_FP (mem_FP_comp pairFst_mem_FP hv)
    (syntaxTokenBitsAt_mem_FP UnaryFn.index
      (mem_FP_comp pairFst_mem_FP (prenexPrefixBits_mem_FP hbits)))
  have h := Cobham.appendFn_mem_FP
    (flatMap_range_mem_FP hentry (prenexPrefixCount_unaryFn hbits).mem_FP) hv
  apply mem_FP_of_eq h
  intro z
  simp only [rawPrenexScheduleBits, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate]

/-- The success tag distinguishes a valid empty schedule from decoding failure. -/
def decodePrenexScheduleOutput (bits : List Bool) : List Bool :=
  match decodePrenex bits with
  | none => []
  | some φ => true :: encodeOperatorSchedule φ.schedule

theorem decodePrenexScheduleOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodePrenexScheduleOutput (bits z)) ∈ FP := by
  have h := (decodePrenex_success_fppred hbits).ite_mem_FP
    (mem_FP_comp (rawPrenexScheduleBits_mem_FP hbits) (Cobham.cons_mem_FP true)) (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro z
  cases hd : decodePrenex (bits z) with
  | none => simp [decodePrenexScheduleOutput, hd]
  | some φ =>
    have he := (decodePrenex_eq_some_iff (bits z) φ).mp hd
    simp [decodePrenexScheduleOutput, ← he, rawPrenexScheduleBits_encode]

@[simp] theorem decodePrenexScheduleOutput_encode (φ : PrenexQBF) :
    decodePrenexScheduleOutput (encodeQBF φ.toQBF) = true :: encodeOperatorSchedule φ.schedule := by
  simp [decodePrenexScheduleOutput]

theorem decodePrenexScheduleOutput_eq_nil_iff (bits : List Bool) :
    decodePrenexScheduleOutput bits = [] ↔ decodePrenex bits = none := by
  cases hd : decodePrenex bits <;> simp [decodePrenexScheduleOutput, hd]

theorem length_encodeSyntaxTokens_ge (tokens : List SyntaxToken) :
    tokens.length ≤ (encodeSyntaxTokens tokens).length := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
    have h := token.length_encode_ge
    simp only [List.length_cons, encodeSyntaxTokens_cons, List.length_append]
    omega

theorem syntaxTokenBitsAt_encode_ne_nil_iff (index : ℕ) (tokens : List SyntaxToken) :
    syntaxTokenBitsAt index (encodeSyntaxTokens tokens) ≠ [] ↔ index < tokens.length := by
  rw [syntaxTokenBitsAt_encodeSyntaxTokens]
  by_cases hi : index < tokens.length
  · simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, hi, iff_true]
    intro h
    have hn := tokens[index].length_encode_ge
    simp [h] at hn
  · simp [hi]

/-- Count tokens by bounded position tests; malformed streams remain total. -/
def syntaxTokenCount (bits : List Bool) : ℕ :=
  ((Finset.range bits.length).filter (fun i => syntaxTokenBitsAt i bits ≠ [])).card

theorem syntaxTokenCount_mem_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => syntaxTokenCount (bits z) := by
  have hp := (bitStrings_eq_fppred
    (syntaxTokenBitsAt_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hbits))
    (constFn_mem_FP [])).not
  apply ((UnaryFn.length hbits).count hp).of_eq
  intro z
  simp only [syntaxTokenCount, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate]

@[simp] theorem syntaxTokenCount_encodeSyntaxTokens (tokens : List SyntaxToken) :
    syntaxTokenCount (encodeSyntaxTokens tokens) = tokens.length := by
  have he : (Finset.range (encodeSyntaxTokens tokens).length).filter
      (fun i => syntaxTokenBitsAt i (encodeSyntaxTokens tokens) ≠ []) = Finset.range tokens.length := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, syntaxTokenBitsAt_encode_ne_nil_iff]
    exact ⟨And.right, fun hi => ⟨hi.trans_le (length_encodeSyntaxTokens_ge tokens), hi⟩⟩
  rw [syntaxTokenCount, he, Finset.card_range]

@[simp] theorem syntaxTokenCount_nil : syntaxTokenCount [] = 0 := rfl

/-- The exact existing schedule length; every decoder failure returns zero. -/
theorem decodePrenex_scheduleLength_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => ((decodePrenex (bits z)).map (fun φ => φ.schedule.length)).getD 0 := by
  have h := syntaxTokenCount_mem_unaryFn
    (drop_mem_FP (decodePrenexScheduleOutput_mem_FP hbits) (UnaryFn.const 1))
  apply h.of_eq
  intro z
  cases hd : decodePrenex (bits z) with
  | none => simp [decodePrenexScheduleOutput, hd]
  | some φ => simp [decodePrenexScheduleOutput, hd, encodeOperatorSchedule]

def decodedScheduleTokenAt (index : ℕ) (bits : List Bool) : List Bool :=
  syntaxTokenBitsAt index ((decodePrenexScheduleOutput bits).drop 1)

theorem decodedScheduleTokenAt_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => decodedScheduleTokenAt (index z) (bits z)) ∈ FP :=
  syntaxTokenBitsAt_mem_FP hindex
    (drop_mem_FP (decodePrenexScheduleOutput_mem_FP hbits) (UnaryFn.const 1))

theorem decodedScheduleTokenAt_eq (index : ℕ) (bits : List Bool) :
    decodedScheduleTokenAt index bits =
      (((decodePrenex bits).bind (fun φ => φ.schedule[index]?)).map
        (fun op => op.syntaxToken.encode)).getD [] := by
  cases hd : decodePrenex bits with
  | none => simp [decodedScheduleTokenAt, decodePrenexScheduleOutput, hd, syntaxTokenBitsAt]
  | some φ =>
    simp only [decodedScheduleTokenAt, decodePrenexScheduleOutput, hd, List.drop_succ_cons,
      List.drop_zero, encodeOperatorSchedule, syntaxTokenBitsAt_encodeSyntaxTokens,
      List.getElem?_map, Option.bind_some, Option.map_map]
    rfl

@[simp] theorem decodedScheduleTokenAt_encode (index : ℕ) (φ : PrenexQBF) :
    decodedScheduleTokenAt index (encodeQBF φ.toQBF) =
      ((φ.schedule[index]?).map (fun op => op.syntaxToken.encode)).getD [] := by
  simp [decodedScheduleTokenAt_eq]

/-- Unrecognized three-bit tags and absent tokens use kind three, rejected by
the round checker. Decoded schedule access supplies canonical tokens or empty. -/
def scheduleTokenKind (bits : List Bool) : ℕ :=
  if bits.take 3 = [false, false, false] then 0
  else if bits.take 3 = [true, true, false] then 1
  else if bits.take 3 = [true, true, true] then 2 else 3

theorem scheduleTokenKind_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => scheduleTokenKind (bits z) := by
  have htag (tag : List Bool) :=
    bitStrings_eq_fppred (take_mem_FP hbits (UnaryFn.const 3)) (constFn_mem_FP tag)
  exact UnaryFn.ite (htag [false, false, false]) (UnaryFn.const 0)
    (UnaryFn.ite (htag [true, true, false]) (UnaryFn.const 1)
      (UnaryFn.ite (htag [true, true, true]) (UnaryFn.const 2) (UnaryFn.const 3)))

@[simp] theorem scheduleTokenKind_encode (op : AlgebraicOperator) :
    scheduleTokenKind op.syntaxToken.encode = op.roundKind := by
  cases op with
  | reduce i => simp [scheduleTokenKind, AlgebraicOperator.syntaxToken, SyntaxToken.encode,
      AlgebraicOperator.roundKind]
  | quantify q => cases q <;> simp [scheduleTokenKind, AlgebraicOperator.syntaxToken,
      Quantifier.token, SyntaxToken.encode, AlgebraicOperator.roundKind]

theorem scheduleTokenNameDigits_encode (op : AlgebraicOperator) :
    syntaxTokenNameDigits op.syntaxToken.encode = op.coordinate.bits := by
  cases op with
  | reduce i =>
    simpa only [AlgebraicOperator.syntaxToken, SyntaxToken.encode,
      AlgebraicOperator.coordinate, List.append_nil] using
      syntaxTokenNameDigits_named [false, false, false] rfl i []
  | quantify q =>
    cases q with
    | ex i =>
      simpa only [AlgebraicOperator.syntaxToken, Quantifier.token, SyntaxToken.encode,
        AlgebraicOperator.coordinate, List.append_nil] using
        syntaxTokenNameDigits_named [true, true, false] rfl i []
    | all i =>
      simpa only [AlgebraicOperator.syntaxToken, Quantifier.token, SyntaxToken.encode,
        AlgebraicOperator.coordinate, List.append_nil] using
        syntaxTokenNameDigits_named [true, true, true] rfl i []

theorem decodedScheduleKind_unaryFn {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    UnaryFn fun z => scheduleTokenKind (decodedScheduleTokenAt (index z) (bits z)) :=
  scheduleTokenKind_unaryFn (decodedScheduleTokenAt_mem_FP hindex hbits)

theorem decodedScheduleCoordinate_bits_mem_FP {index : List Bool → ℕ}
    {bits : List Bool → List Bool} (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => syntaxTokenNameDigits (decodedScheduleTokenAt (index z) (bits z))) ∈ FP :=
  syntaxTokenNameDigits_mem_FP (decodedScheduleTokenAt_mem_FP hindex hbits)

theorem decodedScheduleKind_eq (index : ℕ) (bits : List Bool) (φ : PrenexQBF)
    (hφ : decodePrenex bits = some φ) (op : AlgebraicOperator) (hop : φ.schedule[index]? = some op) :
    scheduleTokenKind (decodedScheduleTokenAt index bits) = op.roundKind := by
  simp [decodedScheduleTokenAt_eq, hφ, hop]

theorem decodedScheduleCoordinate_eq (index : ℕ) (bits : List Bool) (φ : PrenexQBF)
    (hφ : decodePrenex bits = some φ) (op : AlgebraicOperator) (hop : φ.schedule[index]? = some op) :
    syntaxTokenNameDigits (decodedScheduleTokenAt index bits) = op.coordinate.bits := by
  simp only [decodedScheduleTokenAt_eq, hφ, Option.bind_some, hop, Option.map_some,
    Option.getD_some, scheduleTokenNameDigits_encode]

theorem decodedScheduleKind_eq_getD (index : ℕ) (bits : List Bool) :
    scheduleTokenKind (decodedScheduleTokenAt index bits) =
      (((decodePrenex bits).bind (fun φ => φ.schedule[index]?)).map
        AlgebraicOperator.roundKind).getD 3 := by
  rw [decodedScheduleTokenAt_eq]
  cases (decodePrenex bits).bind (fun φ => φ.schedule[index]?) with
  | none => rfl
  | some op => exact scheduleTokenKind_encode op

theorem decodedScheduleCoordinate_eq_getD (index : ℕ) (bits : List Bool) :
    syntaxTokenNameDigits (decodedScheduleTokenAt index bits) =
      (((decodePrenex bits).bind (fun φ => φ.schedule[index]?)).map
        (fun op => op.coordinate.bits)).getD [] := by
  rw [decodedScheduleTokenAt_eq]
  cases (decodePrenex bits).bind (fun φ => φ.schedule[index]?) with
  | none => rfl
  | some op => exact scheduleTokenNameDigits_encode op

theorem encodePrenexSchedule_mem_FP {formula : List Bool → PrenexQBF}
    (hformula : (fun z => encodeQBF (formula z).toQBF) ∈ FP) :
    (fun z => encodeOperatorSchedule (formula z).schedule) ∈ FP :=
  mem_FP_of_eq (rawPrenexScheduleBits_mem_FP hformula)
    (fun z => rawPrenexScheduleBits_encode (formula z))

theorem prenexSchedule_length_unaryFn {formula : List Bool → PrenexQBF}
    (hformula : (fun z => encodeQBF (formula z).toQBF) ∈ FP) :
    UnaryFn fun z => (formula z).schedule.length :=
  (decodePrenex_scheduleLength_unaryFn hformula).of_eq (fun z => by simp)

end IPPSPACE

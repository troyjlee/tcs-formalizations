/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.RenamingFP
import IPPSPACE.QBF.BinaryArithmeticFP
import IPPSPACE.QBF.PrenexConversion

/-!
# Runtime components of the exact prenex converter

The converter starts its fresh-name counter above the largest source name.
Computing that number in unary would impose an invalid restriction on binary
QBF inputs. Instead, a bounded search over token positions identifies a maximal
binary name. These certificates produce the exact existing maximum, initial
fresh counter, and polynomially indexed later counter values. Scoped environment
management and prefix/matrix assembly remain separate runtime obligations.
-/

namespace IPPSPACE

open Complexity

/-- Positions, not the magnitudes of the values, are searched in unary. -/
def binaryMaximumIndex (length : ℕ) (name : ℕ → ℕ) : ℕ :=
  (List.range length).findIdx (fun j => decide (∀ i < length, name i ≤ name j))

theorem binaryMaximumIndex_spec (length : ℕ) (name : ℕ → ℕ) (hpos : 0 < length) :
    binaryMaximumIndex length name < length ∧
      name (binaryMaximumIndex length name) = (Finset.range length).sup name := by
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range length)
    ⟨0, Finset.mem_range.mpr hpos⟩ name
  have hex : ∃ j ∈ List.range length, decide (∀ i < length, name i ≤ name j) = true := by
    refine ⟨j, List.mem_range.mpr (Finset.mem_range.mp hj), ?_⟩
    simp only [decide_eq_true_eq]
    intro i hi
    rw [← hsup]
    exact Finset.le_sup (f := name) (Finset.mem_range.mpr hi)
  have hindex : binaryMaximumIndex length name < length := by
    simpa only [binaryMaximumIndex, List.length_range] using List.findIdx_lt_length_of_exists hex
  have hmax : ∀ i < length, name i ≤ name (binaryMaximumIndex length name) := by
    have h := @List.findIdx_getElem ℕ (fun j => decide (∀ i < length, name i ≤ name j))
      (List.range length) (by simpa only [binaryMaximumIndex, List.length_range] using hindex)
    simpa only [binaryMaximumIndex, List.getElem_range, decide_eq_true_eq] using h
  exact ⟨hindex, le_antisymm (Finset.le_sup (f := name) (Finset.mem_range.mpr hindex))
    (Finset.sup_le (fun i hi => hmax i (Finset.mem_range.mp hi)))⟩

/-- The maximum of polynomially many binary-computable numbers is binary FP,
even if its value is exponentially larger than the original input length. -/
theorem binaryName_rangeSup_mem_FP {length : List Bool → ℕ}
    {name : List Bool → ℕ → ℕ} (hlength : UnaryFn length)
    (hname : (fun w => (name (pairFst w) (pairSnd w).length).bits) ∈ FP) :
    (fun z => ((Finset.range (length z)).sup (name z)).bits) ∈ FP := by
  have hleft : (fun v => (name (pairFst (pairFst v)) (pairSnd v).length).bits) ∈ FP := by
    apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) hname)
    intro v
    simp
  have hright := mem_FP_comp pairFst_mem_FP hname
  have hmax : FPPred fun w => ∀ i < length (pairFst w),
      name (pairFst w) i ≤ name (pairFst w) (pairSnd w).length := by
    refine (FPPred.forall_lt hlength.lift (binaryName_le_fppred hleft hright)).of_iff (fun w => ?_)
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  have hindex : UnaryFn fun z => binaryMaximumIndex (length z) (name z) := by
    apply (hlength.find hmax).of_eq
    intro z
    simp only [binaryMaximumIndex, pairFst_pair, pairSnd_pair, List.length_replicate]
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hchosen := mem_FP_comp (mem_FP_pair hid hindex.mem_FP) hname
  have h := (FPPred.eq hlength (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP []) hchosen
  apply mem_FP_of_eq h
  intro z
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, id_eq]
  by_cases hz : length z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    rw [(binaryMaximumIndex_spec (length z) (name z) (Nat.pos_of_ne_zero hz)).2]

/-- Constructor tags with no name contribute zero to the maximum. -/
def SyntaxToken.nameValue : SyntaxToken → ℕ
  | .var i | .ex i | .all i => i
  | .tru | .fls | .neg | .conj | .disj => 0

@[simp] theorem syntaxTokenNameDigits_encode (token : SyntaxToken) :
    syntaxTokenNameDigits token.encode = token.nameValue.bits := by
  cases token with
  | var name =>
    simpa only [SyntaxToken.encode, SyntaxToken.nameValue, List.append_nil] using
      syntaxTokenNameDigits_named [false, false, false] rfl name []
  | ex name =>
    simpa only [SyntaxToken.encode, SyntaxToken.nameValue, List.append_nil] using
      syntaxTokenNameDigits_named [true, true, false] rfl name []
  | all name =>
    simpa only [SyntaxToken.encode, SyntaxToken.nameValue, List.append_nil] using
      syntaxTokenNameDigits_named [true, true, true] rfl name []
  | tru | fls | neg | conj | disj => rfl

@[simp] theorem syntaxTokenNameDigits_nil : syntaxTokenNameDigits [] = [] := by
  simp [syntaxTokenNameDigits, parseNatNameOutput, parseNatName, parseNameBits, pairFst]

/-- The total binary name at a token position; absent or nameless tokens mean zero. -/
def syntaxNameAt (index : ℕ) (bits : List Bool) : ℕ :=
  nameBitsValue (syntaxTokenNameDigits (syntaxTokenBitsAt index bits))

theorem syntaxNameAt_bits_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => (syntaxNameAt (index z) (bits z)).bits) ∈ FP :=
  nameBitsValue_bits_mem_FP (syntaxTokenNameDigits_mem_FP (syntaxTokenBitsAt_mem_FP hindex hbits))

theorem syntaxNameAt_encodeQBF (index : ℕ) (formula : QBF) :
    syntaxNameAt index (encodeQBF formula) =
      (((qbfTokens formula)[index]?).map SyntaxToken.nameValue).getD 0 := by
  rw [syntaxNameAt, syntaxTokenBitsAt_encodeQBF]
  cases (qbfTokens formula)[index]? with
  | none => rfl
  | some token => simp only [Option.map_some, Option.getD_some,
      syntaxTokenNameDigits_encode, nameBitsValue_bits]

theorem qbfMaxVar_eq_token_sup (formula : QBF) :
    qbfMaxVar formula = (qbfTokens formula).toFinset.sup SyntaxToken.nameValue := by
  induction formula <;> simp_all [qbfMaxVar, qbfTokens, SyntaxToken.nameValue, Finset.sup_union]

private theorem sup_range_getD {α : Type} [DecidableEq α] (entries : List α)
    (name : α → ℕ) (length : ℕ) (hlen : entries.length ≤ length) :
    (Finset.range length).sup (fun i => ((entries[i]?).map name).getD 0) =
      entries.toFinset.sup name := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    cases hg : entries[i]? with
    | none => simp
    | some entry =>
      simp only [Option.map_some, Option.getD_some]
      exact Finset.le_sup (f := name) (List.mem_toFinset.mpr (List.mem_of_getElem? hg))
  · apply Finset.sup_le
    intro entry hentry
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hentry)
    have hget : entries[i]? = some entry := by rw [List.getElem?_eq_getElem hi, heq]
    have h := Finset.le_sup (f := fun j => ((entries[j]?).map name).getD 0)
      (Finset.mem_range.mpr (hi.trans_le hlen))
    simpa only [hget, Option.map_some, Option.getD_some] using h

theorem qbfMaxVar_eq_syntaxNameAt_sup (formula : QBF) :
    qbfMaxVar formula = (Finset.range (encodeQBF formula).length).sup
      (fun index => syntaxNameAt index (encodeQBF formula)) := by
  simp only [syntaxNameAt_encodeQBF]
  rw [sup_range_getD _ _ _ (by simpa using nodeCount_le_length_encodeQBF formula)]
  exact qbfMaxVar_eq_token_sup formula

/-- The exact maximum of all source variable names and binder names is binary
polynomial-time. Only the serialized formula needs an FP certificate. -/
theorem qbfMaxVar_bits_mem_FP {formula : List Bool → QBF}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) :
    (fun z => (qbfMaxVar (formula z)).bits) ∈ FP := by
  have h := binaryName_rangeSup_mem_FP (name := fun z index => syntaxNameAt index (encodeQBF (formula z)))
    (UnaryFn.length hformula)
    (syntaxNameAt_bits_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hformula))
  exact mem_FP_of_eq h (fun z => congrArg Nat.bits (qbfMaxVar_eq_syntaxNameAt_sup (formula z)).symm)

/-- This is exactly the initial counter supplied to the existing `prenexAux`. -/
theorem prenexStart_bits_mem_FP {formula : List Bool → QBF}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) :
    (fun z => (qbfMaxVar (formula z) + 1).bits) ∈ FP :=
  binaryName_succ_mem_FP (qbfMaxVar_bits_mem_FP hformula)

/-- Every later fresh counter with a unary-computable binder offset remains FP
in binary; the potentially large source maximum is never expanded into unary. -/
theorem prenexFresh_bits_mem_FP {formula : List Bool → QBF} {offset : List Bool → ℕ}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) (hoffset : UnaryFn offset) :
    (fun z => (qbfMaxVar (formula z) + 1 + offset z).bits) ∈ FP :=
  binaryName_add_unary_mem_FP (prenexStart_bits_mem_FP hformula) hoffset

/-- A fixed fallback turns the actual partial decoder into an FP-produced QBF
family, while preserving the original canonical bytes on every success. -/
theorem encode_decodeQBF_getD_mem_FP (fallback : QBF) {bits : List Bool → List Bool}
    (hbits : bits ∈ FP) :
    (fun z => encodeQBF ((decodeQBF (bits z)).getD fallback)) ∈ FP := by
  have h := (decodeQBF_success_fppred hbits).ite_mem_FP hbits (constFn_mem_FP (encodeQBF fallback))
  apply mem_FP_of_eq h
  intro z
  cases hd : decodeQBF (bits z) with
  | none => simp
  | some formula =>
    simpa only [hd, Option.isSome_some, ↓reduceIte, Option.getD_some] using
      ((decodeQBF_eq_some_iff (bits z) formula).mp hd).symm

/-- Exact binary maximum of a decoded formula, with zero on every malformed
or trailing input, using the original full-consumption decoder. -/
theorem decodeQBF_maxVar_bits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => (((decodeQBF (bits z)).map qbfMaxVar).getD 0).bits) ∈ FP := by
  apply mem_FP_of_eq (qbfMaxVar_bits_mem_FP (encode_decodeQBF_getD_mem_FP .tru hbits))
  intro z
  cases decodeQBF (bits z) <;> rfl

/-- The decoder's exact fresh-name start, with harmless value one on failure.
The eventual complete converter still has to retain its separate syntax guard. -/
theorem decodeQBF_prenexStart_bits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => (((decodeQBF (bits z)).map qbfMaxVar).getD 0 + 1).bits) ∈ FP :=
  binaryName_succ_mem_FP (decodeQBF_maxVar_bits_mem_FP hbits)

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.TapeTransitionFP
import IPPSPACE.QBF.MachineRead
import IPPSPACE.QBF.MachineTransitionCases
import Complexitylib.Classes.P.StringAccess

/-!
# Polynomial-time construction of actual machine read guards

These certificates construct the exact existing state, work/output read, fixed
input read, and input-head movement formulas. Dynamic input strings remain in
binary; only positions, space bounds, and variable offsets use unary arithmetic.
The transition table is fixed. The guards do not replace configuration validity.
-/

namespace IPPSPACE

open Complexity

private theorem ofFn_val_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_get
  · simp
  · intro i hleft hright
    simp

private theorem blockValues_two (names : Fin 2 → ℕ) (values : Fin 2 → Bool) :
    blockValues names values =
      .conj (bitValue (names 0) (values 0)) (.conj (bitValue (names 1) (values 1)) .tru) := rfl

/-- A packed tape read as an exact natural-index range enumeration. -/
def tapeReadRange (symbol : Fin 2 → Bool) (width headStart cellsStart : ℕ) : QBF :=
  qbfAny ((List.range width).map (fun head =>
    .conj (.var (headStart + head))
      (blockValues (blockNames (cellsStart + 2 * head) 2) symbol)))

theorem tapeReadSymbolFormula_contiguous_eq (symbol : Fin 2 → Bool)
    (width headStart cellsStart : ℕ) :
    tapeReadSymbolFormula symbol (blockNames headStart width)
      (fun i bit => cellsStart + 2 * i.val + bit.val) =
      tapeReadRange symbol width headStart cellsStart := by
  unfold tapeReadSymbolFormula qbfAnyFin tapeReadRange
  exact congrArg qbfAny (ofFn_val_eq_range width
    (fun head => QBF.conj (.var (headStart + head))
      (blockValues (blockNames (cellsStart + 2 * head) 2) symbol)))

theorem encode_tapeReadRange_mem_FP (symbol : Fin 2 → Bool)
    {width headStart cellsStart : List Bool → ℕ}
    (hw : UnaryFn width) (hh : UnaryFn headStart) (hc : UnaryFn cellsStart) :
    (fun z => encodeQBF (tapeReadRange symbol (width z) (headStart z) (cellsStart z))) ∈ FP := by
  have hname := hc.lift.add ((UnaryFn.const 2).mul UnaryFn.index)
  have hcell := encodeQBF_conj_mem_FP
    (encodeQBF_bitValue_mem_FP hname (FPPred.const (symbol 0 = true)))
    (encodeQBF_conj_mem_FP
      (encodeQBF_bitValue_mem_FP (hname.add (UnaryFn.const 1)) (FPPred.const (symbol 1 = true)))
      encodeQBF_tru_mem_FP)
  have hbody : (fun w => encodeQBF (.conj
      (.var (headStart (pairFst w) + (pairSnd w).length))
      (blockValues (blockNames (cellsStart (pairFst w) + 2 * (pairSnd w).length) 2) symbol))) ∈ FP := by
    simpa only [blockValues_two, blockNames, Fin.val_zero, Fin.val_one, Nat.add_zero] using
      encodeQBF_conj_mem_FP (encodeQBF_var_mem_FP (hh.lift.add UnaryFn.index)) hcell
  exact encodeQBF_qbfAny_range_mem_FP hw hbody

theorem encode_machineStateFormula_contiguous_mem_FP {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (tapes : ℕ) (state : Q)
    {inputLength space start : List Bool → ℕ} (hstart : UnaryFn start) :
    (fun z => encodeQBF (machineStateFormula stateNumber tapes (inputLength z) (space z) state
      (blockNames (start z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  exact encodeQBF_var_mem_FP (hstart.add (UnaryFn.const (stateNumber state).val))

/-- Work tape fields are exactly contiguous one-hot heads followed by two bits
per stored cell in the full configuration block. -/
theorem machineWorkReadFormula_contiguous_eq (states tapes inputLength space start : ℕ)
    (symbol : Γ) (tape : Fin tapes) :
    machineWorkReadFormula symbol tape
      (blockNames start (configurationWidth states tapes inputLength space)) =
      tapeReadRange (machineSymbolBits symbol) (space + 1)
        (start + states + (inputLength + space + 2) + 3 * (space + 1) * tape.val)
        (start + states + (inputLength + space + 2) + 3 * (space + 1) * tape.val + (space + 1)) := by
  rw [← tapeReadSymbolFormula_contiguous_eq]
  unfold machineWorkReadFormula machineTapeReadFormula
  congr 1
  · funext i
    simp [blockNames]
    omega
  · funext i bit
    simp [blockNames]
    omega

theorem machineOutputReadFormula_contiguous_eq (states tapes inputLength space start : ℕ)
    (symbol : Γ) :
    machineOutputReadFormula symbol
      (blockNames start (configurationWidth states tapes inputLength space)) =
      tapeReadRange (machineSymbolBits symbol) (space + 2)
        (start + states + (inputLength + space + 2) + 3 * tapes * (space + 1))
        (start + states + (inputLength + space + 2) + 3 * tapes * (space + 1) + (space + 2)) := by
  rw [← tapeReadSymbolFormula_contiguous_eq]
  unfold machineOutputReadFormula machineTapeReadFormula
  congr 1
  · funext i
    simp [blockNames]
    omega
  · funext i bit
    simp [blockNames]
    omega

theorem encode_machineWorkReadFormula_contiguous_mem_FP (states : ℕ) {tapes : ℕ}
    (symbol : Γ) (tape : Fin tapes) {inputLength space start : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space) (hb : UnaryFn start) :
    (fun z => encodeQBF (machineWorkReadFormula symbol tape
      (blockNames (start z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have hwidth := hs.add (UnaryFn.const 1)
  have hhead := ((hb.add (UnaryFn.const states)).add ((hn.add hs).add (UnaryFn.const 2))).add
    (((UnaryFn.const 3).mul hwidth).mul (UnaryFn.const tape.val))
  simpa only [machineWorkReadFormula_contiguous_eq] using
    encode_tapeReadRange_mem_FP (machineSymbolBits symbol) hwidth hhead (hhead.add hwidth)

theorem encode_machineOutputReadFormula_contiguous_mem_FP (states tapes : ℕ)
    (symbol : Γ) {inputLength space start : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space) (hb : UnaryFn start) :
    (fun z => encodeQBF (machineOutputReadFormula symbol
      (blockNames (start z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have hwidth := hs.add (UnaryFn.const 2)
  have hhead := ((hb.add (UnaryFn.const states)).add ((hn.add hs).add (UnaryFn.const 2))).add
    ((UnaryFn.const (3 * tapes)).mul (hs.add (UnaryFn.const 1)))
  simpa only [machineOutputReadFormula_contiguous_eq] using
    encode_tapeReadRange_mem_FP (machineSymbolBits symbol) hwidth hhead (hhead.add hwidth)

/-- Exact access to the actual initialized input tape. The symbol test uses a
bit lookup, never the numeric value of the input word. -/
theorem initializedInputCell_eq_iff (input : List Bool) (index : ℕ) (symbol : Γ) :
    (Tape.init (input.map Γ.ofBool)).cells index = symbol ↔
      match symbol with
      | .start => index = 0
      | .blank => input.length < index
      | .zero => 0 < index ∧ index ≤ input.length ∧ input[index - 1]?.getD false = false
      | .one => 0 < index ∧ index ≤ input.length ∧ input[index - 1]?.getD false = true := by
  cases index with
  | zero => cases symbol <;> simp
  | succ index =>
    by_cases hi : index < input.length
    · rw [Tape.init_ofBool_cells_lt input index hi]
      cases symbol <;> cases hb : input[index] <;>
        simp [Γ.ofBool, hi, hb]
    · rw [Tape.init_ofBool_cells_ge input index (Nat.le_of_not_gt hi)]
      cases symbol <;> simp [hi, Nat.le_of_not_gt hi]

theorem initializedInputCell_fppred (symbol : Γ)
    {input : List Bool → List Bool} {index : List Bool → ℕ}
    (hinput : input ∈ FP) (hindex : UnaryFn index) :
    FPPred fun z => (Tape.init ((input z).map Γ.ofBool)).cells (index z) = symbol := by
  have hpositive := FPPred.lt (UnaryFn.const 0) hindex
  have hinrange := FPPred.le hindex (UnaryFn.length hinput)
  have hbit := FPPred.getBit hinput (hindex.sub (UnaryFn.const 1))
  cases symbol with
  | start =>
    exact (FPPred.eq hindex (UnaryFn.const 0)).of_iff
      (fun z => (initializedInputCell_eq_iff (input z) (index z) Γ.start).symm)
  | blank =>
    exact (FPPred.lt (UnaryFn.length hinput) hindex).of_iff
      (fun z => (initializedInputCell_eq_iff (input z) (index z) Γ.blank).symm)
  | zero =>
    refine (hpositive.and (hinrange.and hbit.not)).of_iff (fun z => ?_)
    rw [initializedInputCell_eq_iff]
    simp
  | one =>
    exact (hpositive.and (hinrange.and hbit)).of_iff
      (fun z => (initializedInputCell_eq_iff (input z) (index z) Γ.one).symm)

theorem fixedInputReadFormula_contiguous_eq (input : List Bool) (symbol : Γ)
    (width start : ℕ) :
    fixedInputReadFormula input symbol (blockNames start width) =
      qbfAny ((List.range width).map (fun head =>
        if (Tape.init (input.map Γ.ofBool)).cells head = symbol then QBF.var (start + head) else QBF.fls)) := by
  unfold fixedInputReadFormula qbfAnyFin
  exact congrArg qbfAny (ofFn_val_eq_range width
    (fun head => if (Tape.init (input.map Γ.ofBool)).cells head = symbol
      then QBF.var (start + head) else QBF.fls))

theorem encode_fixedInputReadFormula_contiguous_mem_FP (symbol : Γ)
    {input : List Bool → List Bool} {width start : List Bool → ℕ}
    (hinput : input ∈ FP) (hw : UnaryFn width) (hs : UnaryFn start) :
    (fun z => encodeQBF (fixedInputReadFormula (input z) symbol (blockNames (start z) (width z)))) ∈ FP := by
  have htest := initializedInputCell_fppred symbol
    (mem_FP_comp Cobham.fstBlock_mem_FP hinput) UnaryFn.index
  have hbody := htest.ite_mem_FP (encodeQBF_var_mem_FP (hs.lift.add UnaryFn.index)) encodeQBF_fls_mem_FP
  have h := encodeQBF_qbfAny_range_mem_FP
    (body := fun z head => if (Tape.init ((input z).map Γ.ofBool)).cells head = symbol
      then .var (start z + head) else .fls) hw
    (mem_FP_of_eq hbody (fun w => by
      simp only [Function.comp_apply]
      split <;> simp_all))
  simpa only [fixedInputReadFormula_contiguous_eq] using h

theorem encode_machineInputReadFormula_contiguous_mem_FP (states tapes : ℕ) (symbol : Γ)
    {input : List Bool → List Bool} {space start : List Bool → ℕ}
    (hinput : input ∈ FP) (hs : UnaryFn space) (hb : UnaryFn start) :
    (fun z => encodeQBF (machineInputReadFormula (input z) (space z) symbol
      (blockNames (start z) (configurationWidth states tapes (input z).length (space z))))) ∈ FP := by
  have h := encode_fixedInputReadFormula_contiguous_mem_FP symbol hinput
    (((UnaryFn.length hinput).add hs).add (UnaryFn.const 2)) (hb.add (UnaryFn.const states))
  apply mem_FP_of_eq h
  intro z
  congr 1
  unfold machineInputReadFormula
  congr 1
  funext i
  simp [blockNames]
  omega

/-- Natural-index view of one input-head movement branch. -/
def inputHeadRangeBranch (direction : Dir3) (width head beforeStart afterStart : ℕ) : QBF :=
  if machineMovedHead direction head < width then
    .conj (blockValues (blockNames beforeStart width) (fun i => decide (head = i.val)))
      (blockValues (blockNames afterStart width)
        (fun i => decide (machineMovedHead direction head = i.val)))
  else .fls

theorem inputHeadMoveFormula_contiguous_eq (direction : Dir3) (width beforeStart afterStart : ℕ) :
    inputHeadMoveFormula direction (blockNames beforeStart width) (blockNames afterStart width) =
      qbfAny ((List.range width).map (fun head =>
        inputHeadRangeBranch direction width head beforeStart afterStart)) := by
  unfold inputHeadMoveFormula qbfAnyFin
  apply congrArg qbfAny
  rw [← ofFn_val_eq_range width (fun head =>
    inputHeadRangeBranch direction width head beforeStart afterStart)]
  apply congrArg List.ofFn
  funext head
  have hencode (i : Fin width) : FixedWidthCodec.encodeFin i =
      (fun j : Fin width => decide (i.val = j.val)) := by
    funext j
    simp [FixedWidthCodec.encodeFin, Fin.ext_iff]
  have hleft : head.val - 1 < width := (Nat.sub_le _ _).trans_lt head.isLt
  cases direction with
  | left =>
    simp [boundedMachineHead, boundedHeadLeft, inputHeadRangeBranch,
      machineMovedHead, hleft, hencode]
    rfl
  | right =>
    by_cases hright : head.val + 1 < width <;>
      simp [boundedMachineHead, boundedHeadRight, inputHeadRangeBranch,
        machineMovedHead, hright, hencode]
    rfl
  | stay =>
    simp [boundedMachineHead, boundedHeadStay, inputHeadRangeBranch,
      machineMovedHead, head.isLt, hencode]
    rfl

theorem encode_inputHeadRangeBranch_mem_FP (direction : Dir3)
    {width head beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hh : UnaryFn head)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (inputHeadRangeBranch direction (width z) (head z)
      (beforeStart z) (afterStart z))) ∈ FP := by
  have hnext := machineMovedHead_unaryFn direction hh
  have hvalue : FPPred fun w => decide (head (pairFst w) = (pairSnd w).length) = true :=
    (FPPred.eq hh.lift UnaryFn.index).of_iff (fun _ => by simp)
  have hnextvalue : FPPred fun w =>
      decide (machineMovedHead direction (head (pairFst w)) = (pairSnd w).length) = true :=
    (FPPred.eq hnext.lift UnaryFn.index).of_iff (fun _ => by simp)
  have hbody := encodeQBF_conj_mem_FP
    (encodeQBF_blockValues_contiguous_mem_FP (values := fun z i => decide (head z = i)) hb hw hvalue)
    (encodeQBF_blockValues_contiguous_mem_FP
      (values := fun z i => decide (machineMovedHead direction (head z) = i)) ha hw hnextvalue)
  have h := (FPPred.lt hnext hw).ite_mem_FP hbody encodeQBF_fls_mem_FP
  refine mem_FP_of_eq h (fun z => ?_)
  by_cases hnext : machineMovedHead direction (head z) < width z <;>
    simp [inputHeadRangeBranch, hnext]

theorem encode_inputHeadMoveFormula_contiguous_mem_FP (direction : Dir3)
    {width beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (inputHeadMoveFormula direction
      (blockNames (beforeStart z) (width z)) (blockNames (afterStart z) (width z)))) ∈ FP := by
  have hbody := encode_inputHeadRangeBranch_mem_FP direction hw.lift UnaryFn.index hb.lift ha.lift
  have h := encodeQBF_qbfAny_range_mem_FP
    (body := fun z head => inputHeadRangeBranch direction (width z) head (beforeStart z) (afterStart z))
    hw hbody
  simpa only [inputHeadMoveFormula_contiguous_eq] using h

/-- The actual full-layout input-head formula, including its two complete
one-hot tests and rejecting finite-window boundary case, is constructible in FP. -/
theorem encode_machineInputHeadMoveFormula_contiguous_mem_FP (states tapes : ℕ) (direction : Dir3)
    {inputLength space beforeStart afterStart : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineInputHeadMoveFormula direction
      (blockNames (beforeStart z) (configurationWidth states tapes (inputLength z) (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have h := encode_inputHeadMoveFormula_contiguous_mem_FP direction
    ((hn.add hs).add (UnaryFn.const 2)) (hb.add (UnaryFn.const states)) (ha.add (UnaryFn.const states))
  apply mem_FP_of_eq h
  intro z
  congr 1
  unfold machineInputHeadMoveFormula
  congr 1 <;> funext i <;> simp [blockNames] <;> omega

end IPPSPACE

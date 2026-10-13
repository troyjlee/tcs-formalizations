/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.OneHotFP
import IPPSPACE.QBF.MachineTapeTransition

/-!
# Polynomial-time construction of bounded tape transitions

The exact existing packed tape-update formula, for a fixed write symbol and
movement direction, can be constructed in upstream's actual `FP` class when
the window width and the two packed block starts are unary polynomial-time
functions. The construction enumerates possible heads and stored cell indices;
it never enumerates the exponentially many tape contents. All syntax identities
preserve the existing one-hot tests, immutable cell zero, and boundary rejection.
-/

namespace IPPSPACE

open Complexity

private theorem ofFn_val_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_get
  · simp
  · intro i hleft hright
    simp

/-- A natural-index view of one cell bit in the actual packed layout. -/
def tapeRangeCellBit (write : Option (Fin 2 → Bool)) (width head cell : ℕ)
    (bit : Fin 2) (beforeStart afterStart : ℕ) : QBF :=
  let before := beforeStart + width + (bit.val + 2 * cell)
  let after := afterStart + width + (bit.val + 2 * cell)
  match write with
  | none => bitEquality after before
  | some symbol =>
    if head ≠ 0 ∧ cell = head then bitValue after (symbol bit)
    else bitEquality after before

/-- Natural-index enumeration with exactly the same cell and bit order. -/
def tapeRangeCells (write : Option (Fin 2 → Bool)) (width head beforeStart afterStart : ℕ) : QBF :=
  qbfAll ((List.range width).map (fun cell => qbfAllFin 2
    (fun bit => tapeRangeCellBit write width head cell bit beforeStart afterStart)))

/-- One branch has its original complete before/after one-hot tests and cells. -/
def tapeRangeBranch (write : Option (Fin 2 → Bool)) (direction : Dir3)
    (width head beforeStart afterStart : ℕ) : QBF :=
  if machineMovedHead direction head < width then
    .conj (blockValues (blockNames beforeStart width) (fun i => decide (head = i.val)))
      (.conj (blockValues (blockNames afterStart width)
        (fun i => decide (machineMovedHead direction head = i.val)))
        (tapeRangeCells write width head beforeStart afterStart))
  else .fls

private theorem tapeCellNames_blockNames (start n : ℕ) (cell : Fin n) (bit : Fin 2) :
    tapeCellNames (blockNames start (n + n * 2)) cell bit =
      start + n + (bit.val + 2 * cell.val) := by
  simp [tapeCellNames, blockNames, finProdFinEquiv, Nat.add_assoc]

private theorem tapeHeadNames_blockNames (start n : ℕ) :
    tapeHeadNames (blockNames start (n + n * 2)) = blockNames start n := by
  rfl

private theorem tapeCellBitFormula_eq_range {n : ℕ} (write : Option (Fin 2 → Bool))
    (head cell : Fin n) (bit : Fin 2) (beforeStart afterStart : ℕ) :
    tapeCellBitFormula write head cell bit
      (tapeCellNames (blockNames beforeStart (n + n * 2)))
      (tapeCellNames (blockNames afterStart (n + n * 2))) =
      tapeRangeCellBit write n head.val cell.val bit beforeStart afterStart := by
  cases write <;>
    simp [tapeCellBitFormula, tapeRangeCellBit, tapeCellNames_blockNames, Fin.ext_iff]

private theorem tapeCellsFormula_eq_range {n : ℕ} (write : Option (Fin 2 → Bool))
    (head : Fin n) (beforeStart afterStart : ℕ) :
    tapeCellsFormula write head
      (tapeCellNames (blockNames beforeStart (n + n * 2)))
      (tapeCellNames (blockNames afterStart (n + n * 2))) =
      tapeRangeCells write n head.val beforeStart afterStart := by
  simp only [tapeCellsFormula, tapeCellBitFormula_eq_range, tapeRangeCells, qbfAllFin]
  exact congrArg qbfAll (ofFn_val_eq_range n (fun cell => qbfAll
    (List.ofFn (fun bit => tapeRangeCellBit write n head.val cell bit beforeStart afterStart))))

private theorem encodeFin_val {n : ℕ} (head : Fin n) :
    FixedWidthCodec.encodeFin head = (fun i : Fin n => decide (head.val = i.val)) := by
  funext i
  simp [FixedWidthCodec.encodeFin, Fin.ext_iff]

private theorem tapeHeadBranch_eq_range {n : ℕ} (write : Option (Fin 2 → Bool))
    (direction : Dir3) (head : Fin n) (beforeStart afterStart : ℕ) :
    tapeHeadBranch (boundedMachineHead direction) write
      (tapeHeadNames (blockNames beforeStart (n + n * 2)))
      (tapeHeadNames (blockNames afterStart (n + n * 2)))
      (tapeCellNames (blockNames beforeStart (n + n * 2)))
      (tapeCellNames (blockNames afterStart (n + n * 2))) head =
      tapeRangeBranch write direction n head.val beforeStart afterStart := by
  have hleft : head.val - 1 < n := (Nat.sub_le _ _).trans_lt head.isLt
  cases direction with
  | left =>
    simp [tapeHeadBranch, boundedMachineHead, boundedHeadLeft, tapeRangeBranch,
      machineMovedHead, hleft, tapeHeadNames_blockNames, encodeFin_val,
      tapeCellsFormula_eq_range]
    rfl
  | right =>
    by_cases hright : head.val + 1 < n <;>
      simp [tapeHeadBranch, boundedMachineHead, boundedHeadRight, tapeRangeBranch,
        machineMovedHead, hright, tapeHeadNames_blockNames, encodeFin_val,
        tapeCellsFormula_eq_range]
    rfl
  | stay =>
    simp [tapeHeadBranch, boundedMachineHead, boundedHeadStay, tapeRangeBranch,
      machineMovedHead, head.isLt, tapeHeadNames_blockNames, encodeFin_val,
      tapeCellsFormula_eq_range]
    rfl

/-- Exact syntax equality, including width zero and the rejecting last right
move. This is stronger than a mere evaluation equivalence. -/
theorem packedTapeTransitionFormula_eq_range (write : Option (Fin 2 → Bool)) (direction : Dir3)
    (width beforeStart afterStart : ℕ) :
    packedTapeTransitionFormula (boundedMachineHead direction) write
      (blockNames beforeStart (width + width * 2)) (blockNames afterStart (width + width * 2)) =
      qbfAny ((List.range width).map (fun head =>
        tapeRangeBranch write direction width head beforeStart afterStart)) := by
  simp only [packedTapeTransitionFormula, tapeTransitionFormula, qbfAnyFin]
  apply congrArg qbfAny
  calc
    _ = List.ofFn (fun head : Fin width =>
        tapeRangeBranch write direction width head.val beforeStart afterStart) :=
      congrArg List.ofFn (funext (fun head =>
        tapeHeadBranch_eq_range write direction head beforeStart afterStart))
    _ = _ := ofFn_val_eq_range width
      (fun head => tapeRangeBranch write direction width head beforeStart afterStart)

/-- Movement arithmetic is polynomial-time for each fixed machine direction. -/
theorem machineMovedHead_unaryFn (direction : Dir3) {head : List Bool → ℕ}
    (hhead : UnaryFn head) : UnaryFn fun z => machineMovedHead direction (head z) := by
  cases direction with
  | left => exact hhead.sub (UnaryFn.const 1)
  | right => exact hhead.add (UnaryFn.const 1)
  | stay => exact hhead

theorem encode_tapeRangeCellBit_mem_FP (write : Option (Fin 2 → Bool)) (bit : Fin 2)
    {width head cell beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hh : UnaryFn head) (hc : UnaryFn cell)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (tapeRangeCellBit write (width z) (head z) (cell z) bit
      (beforeStart z) (afterStart z))) ∈ FP := by
  have hbefore := (hb.add hw).add ((UnaryFn.const bit.val).add ((UnaryFn.const 2).mul hc))
  have hafter := (ha.add hw).add ((UnaryFn.const bit.val).add ((UnaryFn.const 2).mul hc))
  cases write with
  | none => exact encodeQBF_bitEquality_mem_FP hafter hbefore
  | some symbol =>
    have hwrite : FPPred fun z => head z ≠ 0 ∧ cell z = head z :=
      ((FPPred.eq hh (UnaryFn.const 0)).not).and (FPPred.eq hc hh)
    have h := hwrite.ite_mem_FP
      (encodeQBF_bitValue_mem_FP hafter (FPPred.const (symbol bit = true)))
      (encodeQBF_bitEquality_mem_FP hafter hbefore)
    refine mem_FP_of_eq h (fun z => ?_)
    by_cases ht : head z ≠ 0 ∧ cell z = head z <;> simp [tapeRangeCellBit, ht]

private theorem qbfAllFin_two (body : Fin 2 → QBF) :
    qbfAllFin 2 body = .conj (body 0) (.conj (body 1) .tru) := by
  simp [qbfAllFin, List.ofFn_succ, qbfAll]

theorem encode_tapeRangeCells_mem_FP (write : Option (Fin 2 → Bool))
    {width head beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hh : UnaryFn head)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (tapeRangeCells write (width z) (head z)
      (beforeStart z) (afterStart z))) ∈ FP := by
  have hbit (bit : Fin 2) := encode_tapeRangeCellBit_mem_FP write bit hw.lift hh.lift
    UnaryFn.index hb.lift ha.lift
  have hcell : (fun w => encodeQBF (qbfAllFin 2 (fun bit =>
      tapeRangeCellBit write (width (pairFst w)) (head (pairFst w)) (pairSnd w).length bit
        (beforeStart (pairFst w)) (afterStart (pairFst w))))) ∈ FP := by
    simpa only [qbfAllFin_two] using
      encodeQBF_conj_mem_FP (hbit 0) (encodeQBF_conj_mem_FP (hbit 1) encodeQBF_tru_mem_FP)
  exact encodeQBF_qbfAll_range_mem_FP hw hcell

theorem encode_tapeRangeBranch_mem_FP (write : Option (Fin 2 → Bool)) (direction : Dir3)
    {width head beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hh : UnaryFn head)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (tapeRangeBranch write direction (width z) (head z)
      (beforeStart z) (afterStart z))) ∈ FP := by
  have hnext := machineMovedHead_unaryFn direction hh
  have hvalue : FPPred fun w => decide (head (pairFst w) = (pairSnd w).length) = true :=
    (FPPred.eq hh.lift UnaryFn.index).of_iff (fun _ => by simp)
  have hnextvalue : FPPred fun w =>
      decide (machineMovedHead direction (head (pairFst w)) = (pairSnd w).length) = true :=
    (FPPred.eq hnext.lift UnaryFn.index).of_iff (fun _ => by simp)
  have hbody := encodeQBF_conj_mem_FP
    (encodeQBF_blockValues_contiguous_mem_FP (values := fun z i => decide (head z = i)) hb hw hvalue)
    (encodeQBF_conj_mem_FP (encodeQBF_blockValues_contiguous_mem_FP
      (values := fun z i => decide (machineMovedHead direction (head z) = i)) ha hw hnextvalue)
      (encode_tapeRangeCells_mem_FP write hw hh hb ha))
  have h := (FPPred.lt hnext hw).ite_mem_FP hbody encodeQBF_fls_mem_FP
  refine mem_FP_of_eq h (fun z => ?_)
  by_cases hnext : machineMovedHead direction (head z) < width z <;>
    simp [tapeRangeBranch, hnext]

/-- Actual `FP` construction of the exact packed tape formula with optional
fixed write and fixed direction. Dynamic width zero retains the false formula. -/
theorem encode_packedTapeTransitionFormula_contiguous_mem_FP
    (write : Option (Fin 2 → Bool)) (direction : Dir3)
    {width beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (packedTapeTransitionFormula (boundedMachineHead direction) write
      (blockNames (beforeStart z) (width z + width z * 2))
      (blockNames (afterStart z) (width z + width z * 2)))) ∈ FP := by
  have hbranch := encode_tapeRangeBranch_mem_FP write direction hw.lift UnaryFn.index hb.lift ha.lift
  have h := encodeQBF_qbfAny_range_mem_FP
    (body := fun z head => tapeRangeBranch write direction (width z) head (beforeStart z) (afterStart z))
    hw hbranch
  simpa only [← packedTapeTransitionFormula_eq_range] using h

/-- The exact existing formula for an actual machine-symbol write and movement
has a machine-time certificate, for dynamic polynomial-time packed windows. -/
theorem encode_machineTapeTransitionFormula_contiguous_mem_FP (symbol : Γ) (direction : Dir3)
    {width beforeStart afterStart : List Bool → ℕ}
    (hw : UnaryFn width) (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineTapeTransitionFormula symbol direction
      (blockNames (beforeStart z) (width z + width z * 2))
      (blockNames (afterStart z) (width z + width z * 2)))) ∈ FP :=
  encode_packedTapeTransitionFormula_contiguous_mem_FP (some (machineSymbolBits symbol)) direction hw hb ha

end IPPSPACE

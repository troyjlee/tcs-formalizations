/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.EncodingFP

/-!
# Machine-based polynomial-time construction of variable blocks

The recursive block formulas already used by the reachability construction
are exactly finite conjunctions or flat encoded quantifier prefixes. These
identities transfer the actual upstream `FP` certificates to their canonical
binary encodings. Dynamic widths and numeric names are required to be unary
polynomial-time values; arbitrary numerically large binary names are not covered
by that assumption. No complete machine reduction is certified here.
-/

namespace IPPSPACE

open Complexity

/-- The existing recursive block-equality syntax is exactly the range-indexed
conjunction, with the same order and terminal `tru`. -/
theorem blockEquality_eq_qbfAll_range (width : ℕ) (left right : ℕ → ℕ) :
    blockEquality (fun i : Fin width => left i.val) (fun i => right i.val) =
      qbfAll ((List.range width).map (fun i => bitEquality (left i) (right i))) := by
  induction width generalizing left right with
  | zero => rfl
  | succ width ih =>
    simp only [blockEquality, List.range_succ_eq_map, List.map_cons, List.map_map, qbfAll]
    convert congrArg (QBF.conj (bitEquality (left 0) (right 0)))
      (ih (fun i => left (i + 1)) (fun i => right (i + 1))) using 1
    all_goals rfl

/-- The fixed-value block keeps the same literal order as its range conjunction. -/
theorem blockValues_eq_qbfAll_range (width : ℕ) (names : ℕ → ℕ) (values : ℕ → Bool) :
    blockValues (fun i : Fin width => names i.val) (fun i => values i.val) =
      qbfAll ((List.range width).map (fun i => bitValue (names i) (values i))) := by
  induction width generalizing names values with
  | zero => rfl
  | succ width ih =>
    simp only [blockValues, List.range_succ_eq_map, List.map_cons, List.map_map, qbfAll]
    convert congrArg (QBF.conj (bitValue (names 0) (values 0)))
      (ih (fun i => names (i + 1)) (fun i => values (i + 1))) using 1
    all_goals rfl

/-- Generate an equality block from two polynomial-time numeric index rules.
Each rule receives the original input paired with a unary coordinate. -/
theorem encodeQBF_blockEquality_mem_FP {width : List Bool → ℕ}
    {left right : List Bool → ℕ → ℕ} (hwidth : UnaryFn width)
    (hleft : UnaryFn fun w => left (pairFst w) (pairSnd w).length)
    (hright : UnaryFn fun w => right (pairFst w) (pairSnd w).length) :
    (fun z => encodeQBF (blockEquality (fun i : Fin (width z) => left z i.val)
      (fun i => right z i.val))) ∈ FP := by
  have h := encodeQBF_qbfAll_range_mem_FP (body := fun z i => bitEquality (left z i) (right z i))
    hwidth (encodeQBF_bitEquality_mem_FP hleft hright)
  simpa only [← blockEquality_eq_qbfAll_range] using h

/-- Generate a block of prescribed values from a polynomial-time index rule
and a polynomial-time bit predicate on the same paired input and index. -/
theorem encodeQBF_blockValues_mem_FP {width : List Bool → ℕ}
    {names : List Bool → ℕ → ℕ} {values : List Bool → ℕ → Bool} (hwidth : UnaryFn width)
    (hnames : UnaryFn fun w => names (pairFst w) (pairSnd w).length)
    (hvalues : FPPred fun w => values (pairFst w) (pairSnd w).length = true) :
    (fun z => encodeQBF (blockValues (fun i : Fin (width z) => names z i.val)
      (fun i => values z i.val))) ∈ FP := by
  have h := encodeQBF_qbfAll_range_mem_FP (body := fun z i => bitValue (names z i) (values z i))
    hwidth (encodeQBF_bitValue_mem_FP hnames hvalues)
  simpa only [← blockValues_eq_qbfAll_range] using h

/-- In particular, equality of two contiguous variable blocks is polynomial-time
when their starts and common width are polynomial-time numeric values. -/
theorem encodeQBF_blockEquality_contiguous_mem_FP {left right width : List Bool → ℕ}
    (hleft : UnaryFn left) (hright : UnaryFn right) (hwidth : UnaryFn width) :
    (fun z => encodeQBF (blockEquality (blockNames (left z) (width z))
      (blockNames (right z) (width z)))) ∈ FP :=
  encodeQBF_blockEquality_mem_FP hwidth (hleft.lift.add UnaryFn.index) (hright.lift.add UnaryFn.index)

theorem encodeQBF_blockValues_contiguous_mem_FP {start width : List Bool → ℕ}
    {values : List Bool → ℕ → Bool} (hstart : UnaryFn start) (hwidth : UnaryFn width)
    (hvalues : FPPred fun w => values (pairFst w) (pairSnd w).length = true) :
    (fun z => encodeQBF (blockValues (blockNames (start z) (width z))
      (fun i => values z i.val))) ∈ FP :=
  encodeQBF_blockValues_mem_FP hwidth (hstart.lift.add UnaryFn.index) hvalues

/-- Existential blocks prepend one correctly tagged binary name per coordinate.
The original formula's encoding occurs exactly once at the end. -/
theorem encodeQBF_existsBlock (start width : ℕ) (body : QBF) :
    encodeQBF (existsBlock start width body) =
      (List.range width).flatMap (fun i => [true, true, false] ++ encodeNatName (start + i)) ++
        encodeQBF body := by
  induction width generalizing start with
  | zero => rfl
  | succ width ih =>
    simp [existsBlock, encodeQBF, ih, List.range_succ_eq_map, List.flatMap_map,
      List.append_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The analogous flat prefix identity for universal blocks. -/
theorem encodeQBF_forallBlock (start width : ℕ) (body : QBF) :
    encodeQBF (forallBlock start width body) =
      (List.range width).flatMap (fun i => [true, true, true] ++ encodeNatName (start + i)) ++
        encodeQBF body := by
  induction width generalizing start with
  | zero => rfl
  | succ width ih =>
    simp [forallBlock, encodeQBF, ih, List.range_succ_eq_map, List.flatMap_map,
      List.append_assoc, Nat.add_left_comm, Nat.add_comm]

/-- A dynamically sized existential block has a genuine upstream `FP`
certificate when the start, width, and already encoded body do. -/
theorem encodeQBF_existsBlock_mem_FP {start width : List Bool → ℕ} {body : List Bool → QBF}
    (hstart : UnaryFn start) (hwidth : UnaryFn width)
    (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (existsBlock (start z) (width z) (body z))) ∈ FP := by
  have hentry := Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false])
    (encodeNatName_mem_FP (hstart.lift.add UnaryFn.index))
  have h := Cobham.appendFn_mem_FP (flatMap_range_mem_FP hentry hwidth.mem_FP) hbody
  apply mem_FP_of_eq h
  intro z
  simp [encodeQBF_existsBlock]

/-- A dynamically sized universal block, preserving the exact `forallBlock`
syntax and order of binders. -/
theorem encodeQBF_forallBlock_mem_FP {start width : List Bool → ℕ} {body : List Bool → QBF}
    (hstart : UnaryFn start) (hwidth : UnaryFn width)
    (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (forallBlock (start z) (width z) (body z))) ∈ FP := by
  have hentry := Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, true])
    (encodeNatName_mem_FP (hstart.lift.add UnaryFn.index))
  have h := Cobham.appendFn_mem_FP (flatMap_range_mem_FP hentry hwidth.mem_FP) hbody
  apply mem_FP_of_eq h
  intro z
  simp [encodeQBF_forallBlock]

end IPPSPACE

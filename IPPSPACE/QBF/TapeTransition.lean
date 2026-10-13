/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.BooleanGadgets
import IPPSPACE.QBF.ConfigurationEncoding

/-!
# Explicit formulas for a bounded tape component update

A component stores a one-hot head position and two bits per cell, exactly as in
`configurationCodec`. Writing at cell zero is ignored; writing elsewhere changes
only the old head cell, before the head moves. These are the equations of the
pinned upstream `Tape.write` and `Tape.writeAndMove`. Movement is supplied as a
partial next-index function, so leaving the finite window rejects the update.

The formula enumerates head positions, not tape contents. Every branch compares
two head blocks and all cell bits, giving a quadratic node bound. It is an
explicit formula for one finite component operation, not an imported machine
transition or a machine-time certificate. All four cell bit patterns are allowed;
alphabet restrictions and start-marker invariants belong to the full machine.
-/

namespace IPPSPACE

open Complexity

/-- The finite tape factor used by the configuration codec, in symbol bits. -/
abbrev TapeComponent (n : ℕ) := Fin n × (Fin n → Fin 2 → Bool)

/-- The tape's existing one-hot-head / row-major two-bit-cell representation. -/
def tapeComponentCodec (n : ℕ) : FixedWidthCodec (TapeComponent n) (n + n * 2) :=
  (FixedWidthCodec.fin n).prod ((FixedWidthCodec.word 2).vector n)

/-- An optional write at the old head; the left-end cell is immutable. -/
def writeTapeCells {n : ℕ} (write : Option (Fin 2 → Bool)) (head : Fin n)
    (cells : Fin n → Fin 2 → Bool) (i : Fin n) (bit : Fin 2) : Bool :=
  match write with
  | none => cells i bit
  | some symbol => if head.val ≠ 0 ∧ i = head then symbol bit else cells i bit

@[simp] theorem writeTapeCells_none {n : ℕ} (head : Fin n)
    (cells : Fin n → Fin 2 → Bool) : writeTapeCells none head cells = cells := rfl

/-- Exact finite-tuple form of the upstream `Tape.write` equation. -/
theorem writeTapeCells_some {n : ℕ} (symbol : Fin 2 → Bool) (head : Fin n)
    (cells : Fin n → Fin 2 → Bool) :
    writeTapeCells (some symbol) head cells =
      if head.val = 0 then cells else Function.update cells head symbol := by
  funext i bit
  by_cases hz : head.val = 0
  · simp [writeTapeCells, hz]
  · by_cases hi : i = head <;> simp [writeTapeCells, hz, hi]

theorem writeTapeCells_head_zero {n : ℕ} (write : Option (Fin 2 → Bool)) (head : Fin n)
    (cells : Fin n → Fin 2 → Bool) (h : head.val = 0) :
    writeTapeCells write head cells = cells := by
  cases write <;> simp [writeTapeCells_some, h]

theorem writeTapeCells_other {n : ℕ} (write : Option (Fin 2 → Bool)) (head i : Fin n)
    (cells : Fin n → Fin 2 → Bool) (h : i ≠ head) :
    writeTapeCells write head cells i = cells i := by
  funext bit
  cases write <;> simp [writeTapeCells, h]

/-- Write first, then move; reject a move outside the available index set. -/
def stepTapeComponent {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (tape : TapeComponent n) : Option (TapeComponent n) :=
  (next tape.1).map (fun head => (head, writeTapeCells write tape.1 tape.2))

theorem stepTapeComponent_eq_some_iff {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (before after : TapeComponent n) :
    stepTapeComponent next write before = some after ↔
      next before.1 = some after.1 ∧ after.2 = writeTapeCells write before.1 before.2 := by
  cases hnext : next before.1 with
  | none => simp [stepTapeComponent, hnext]
  | some head => simp [stepTapeComponent, hnext, Prod.ext_iff, eq_comm]

@[simp] theorem stepTapeComponent_eq_none_iff {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (before : TapeComponent n) :
    stepTapeComponent next write before = none ↔ next before.1 = none := by
  simp [stepTapeComponent]

/-- Left motion saturates at zero, as in the upstream natural head index. -/
def boundedHeadLeft {n : ℕ} (head : Fin n) : Option (Fin n) :=
  some ⟨head.val - 1, (Nat.sub_le _ _).trans_lt head.isLt⟩

/-- A right move beyond the finite window is rejected. -/
def boundedHeadRight {n : ℕ} (head : Fin n) : Option (Fin n) :=
  if h : head.val + 1 < n then some ⟨head.val + 1, h⟩ else none

def boundedHeadStay {n : ℕ} (head : Fin n) : Option (Fin n) := some head

theorem boundedHeadRight_eq_none_iff {n : ℕ} (head : Fin n) :
    boundedHeadRight head = none ↔ head.val + 1 = n := by
  simp [boundedHeadRight]
  omega

/-- Compare one target cell bit with either the new symbol or its old value. -/
def tapeCellBitFormula {n : ℕ} (write : Option (Fin 2 → Bool)) (head i : Fin n)
    (bit : Fin 2) (beforeCells afterCells : Fin n → Fin 2 → ℕ) : QBF :=
  match write with
  | none => bitEquality (afterCells i bit) (beforeCells i bit)
  | some symbol =>
      if head.val ≠ 0 ∧ i = head then bitValue (afterCells i bit) (symbol bit)
      else bitEquality (afterCells i bit) (beforeCells i bit)

theorem eval_tapeCellBitFormula {n : ℕ} (write : Option (Fin 2 → Bool)) (head i : Fin n)
    (bit : Fin 2) (beforeCells afterCells : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool) :
    (tapeCellBitFormula write head i bit beforeCells afterCells).eval assignment = true ↔
      assignment (afterCells i bit) =
        writeTapeCells write head (fun j k => assignment (beforeCells j k)) i bit := by
  cases write with
  | none => simp [tapeCellBitFormula, writeTapeCells]
  | some symbol =>
    by_cases h : head.val ≠ 0 ∧ i = head <;> simp [tapeCellBitFormula, writeTapeCells, h,
      eval_bitValue]

def tapeCellsFormula {n : ℕ} (write : Option (Fin 2 → Bool)) (head : Fin n)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) : QBF :=
  qbfAllFin n (fun i => qbfAllFin 2 (fun bit =>
    tapeCellBitFormula write head i bit beforeCells afterCells))

theorem eval_tapeCellsFormula {n : ℕ} (write : Option (Fin 2 → Bool)) (head : Fin n)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool) :
    (tapeCellsFormula write head beforeCells afterCells).eval assignment = true ↔
      (fun i bit => assignment (afterCells i bit)) =
        writeTapeCells write head (fun i bit => assignment (beforeCells i bit)) := by
  simp only [tapeCellsFormula, eval_qbfAllFin, eval_tapeCellBitFormula]
  exact ⟨fun h => funext (fun i => funext (h i)), fun h i bit => congrFun (congrFun h i) bit⟩

/-- One branch fixes the complete old and new head blocks, then checks every cell. -/
def tapeHeadBranch {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (head : Fin n) : QBF :=
  match next head with
  | none => .fls
  | some newHead =>
      .conj (blockValues beforeHead (FixedWidthCodec.encodeFin head))
        (.conj (blockValues afterHead (FixedWidthCodec.encodeFin newHead))
          (tapeCellsFormula write head beforeCells afterCells))

/-- An explicit quadratic-size formula, enumerating heads rather than tape states. -/
def tapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) : QBF :=
  qbfAnyFin n (tapeHeadBranch next write beforeHead afterHead beforeCells afterCells)

/-- Exact semantics on arbitrary bit assignments. Both one-hot head codes are
validated by the formula; no well-formedness hypothesis on the bits is required. -/
theorem eval_tapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool) :
    (tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells).eval
        assignment = true ↔
      ∃ head newHead, next head = some newHead ∧
        assignment ∘ beforeHead = FixedWidthCodec.encodeFin head ∧
        assignment ∘ afterHead = FixedWidthCodec.encodeFin newHead ∧
        (fun i bit => assignment (afterCells i bit)) =
          writeTapeCells write head (fun i bit => assignment (beforeCells i bit)) := by
  simp only [tapeTransitionFormula, eval_qbfAnyFin]
  apply exists_congr
  intro head
  cases hnext : next head with
  | none => simp [tapeHeadBranch, hnext]
  | some newHead =>
    simp [tapeHeadBranch, hnext, eval_blockValues, eval_tapeCellsFormula]

theorem quantifierFree_tapeCellBitFormula {n : ℕ} (write : Option (Fin 2 → Bool))
    (head i : Fin n) (bit : Fin 2) (beforeCells afterCells : Fin n → Fin 2 → ℕ) :
    (tapeCellBitFormula write head i bit beforeCells afterCells).QuantifierFree := by
  cases write with
  | none => exact quantifierFree_bitEquality _ _
  | some symbol =>
    simp only [tapeCellBitFormula]
    split <;> simp

theorem quantifierFree_tapeCellsFormula {n : ℕ} (write : Option (Fin 2 → Bool))
    (head : Fin n) (beforeCells afterCells : Fin n → Fin 2 → ℕ) :
    (tapeCellsFormula write head beforeCells afterCells).QuantifierFree :=
  quantifierFree_qbfAllFin _ _ (fun i => quantifierFree_qbfAllFin _ _ (fun bit =>
    quantifierFree_tapeCellBitFormula write head i bit beforeCells afterCells))

theorem quantifierFree_tapeHeadBranch {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (head : Fin n) :
    (tapeHeadBranch next write beforeHead afterHead beforeCells afterCells head).QuantifierFree := by
  cases hnext : next head with
  | none => simp [tapeHeadBranch, hnext, QBF.QuantifierFree, QBF.quantDepth]
  | some newHead =>
    simp only [tapeHeadBranch, hnext]
    exact QBF.quantifierFree_conj.mpr ⟨quantifierFree_blockValues _ _,
      QBF.quantifierFree_conj.mpr ⟨quantifierFree_blockValues _ _,
        quantifierFree_tapeCellsFormula _ _ _ _⟩⟩

theorem quantifierFree_tapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) :
    (tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells).QuantifierFree :=
  quantifierFree_qbfAnyFin _ _ (quantifierFree_tapeHeadBranch _ _ _ _ _ _)

theorem nodeCount_tapeCellBitFormula_le {n : ℕ} (write : Option (Fin 2 → Bool))
    (head i : Fin n) (bit : Fin 2) (beforeCells afterCells : Fin n → Fin 2 → ℕ) :
    nodeCount (tapeCellBitFormula write head i bit beforeCells afterCells) ≤ 9 := by
  cases write with
  | none => exact le_rfl
  | some symbol =>
    simp only [tapeCellBitFormula]
    split
    · exact (nodeCount_bitValue_le _ _).trans (by decide)
    · exact le_rfl

theorem nodeCount_tapeCellsFormula_le {n : ℕ} (write : Option (Fin 2 → Bool))
    (head : Fin n) (beforeCells afterCells : Fin n → Fin 2 → ℕ) :
    nodeCount (tapeCellsFormula write head beforeCells afterCells) ≤ 22 * n + 1 := by
  apply nodeCount_qbfAllFin_le n _ 21
  intro i
  exact nodeCount_qbfAllFin_le 2 _ 9 (fun bit =>
    nodeCount_tapeCellBitFormula_le write head i bit beforeCells afterCells)

theorem nodeCount_tapeHeadBranch_le {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (head : Fin n) :
    nodeCount (tapeHeadBranch next write beforeHead afterHead beforeCells afterCells head) ≤
      28 * n + 5 := by
  cases hnext : next head with
  | none => simp [tapeHeadBranch, hnext, nodeCount]
  | some newHead =>
    have hbefore := nodeCount_blockValues_le beforeHead (FixedWidthCodec.encodeFin head)
    have hafter := nodeCount_blockValues_le afterHead (FixedWidthCodec.encodeFin newHead)
    have hcells := nodeCount_tapeCellsFormula_le write head beforeCells afterCells
    simp only [tapeHeadBranch, hnext, nodeCount]
    omega

/-- A syntax-node bound, not a machine-time certificate. -/
theorem nodeCount_tapeTransitionFormula_le {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) :
    nodeCount (tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells) ≤
      (28 * n + 6) * n + 1 :=
  nodeCount_qbfAnyFin_le n _ (28 * n + 5) (nodeCount_tapeHeadBranch_le _ _ _ _ _ _)

private theorem mem_bitValue_names {name i : ℕ} (value : Bool)
    (h : i ∈ qbfNames (bitValue name value)) : i = name := by
  cases value <;> simpa [bitValue, qbfNames] using h

private theorem mem_blockValues_names {n : ℕ} (names : Fin n → ℕ)
    (values : Fin n → Bool) {i : ℕ} (h : i ∈ qbfNames (blockValues names values)) :
    ∃ j, names j = i := by
  induction n with
  | zero => simp [blockValues, qbfNames] at h
  | succ n ih =>
    rcases Finset.mem_union.mp h with h | h
    · exact ⟨0, (mem_bitValue_names (values 0) h).symm⟩
    · obtain ⟨j, hj⟩ := ih (Fin.tail names) (Fin.tail values) h
      exact ⟨j.succ, hj⟩

theorem mem_qbfNames_tapeCellBitFormula {n : ℕ} (write : Option (Fin 2 → Bool))
    (head j : Fin n) (bit : Fin 2) (beforeCells afterCells : Fin n → Fin 2 → ℕ)
    {i : ℕ} (h : i ∈ qbfNames (tapeCellBitFormula write head j bit beforeCells afterCells)) :
    beforeCells j bit = i ∨ afterCells j bit = i := by
  cases write with
  | none => simpa [tapeCellBitFormula, bitEquality, qbfNames, eq_comm, or_comm] using h
  | some symbol =>
    simp only [tapeCellBitFormula] at h
    split at h
    · exact Or.inr (mem_bitValue_names _ h).symm
    · simpa [bitEquality, qbfNames, eq_comm, or_comm] using h

/-- Every name in the formula is a supplied head or cell coordinate. -/
theorem mem_qbfNames_tapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) {i : ℕ}
    (h : i ∈ qbfNames
      (tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells)) :
    (∃ j, beforeHead j = i) ∨ (∃ j, afterHead j = i) ∨
      (∃ j bit, beforeCells j bit = i) ∨ (∃ j bit, afterCells j bit = i) := by
  obtain ⟨head, h⟩ := (mem_qbfNames_qbfAnyFin _ _ _).mp h
  cases hnext : next head with
  | none => simp [tapeHeadBranch, hnext, qbfNames] at h
  | some newHead =>
    simp only [tapeHeadBranch, hnext, qbfNames, Finset.mem_union] at h
    rcases h with h | h | h
    · exact Or.inl (mem_blockValues_names _ _ h)
    · exact Or.inr (Or.inl (mem_blockValues_names _ _ h))
    · obtain ⟨j, h⟩ := (mem_qbfNames_qbfAllFin _ _ _).mp h
      obtain ⟨bit, h⟩ := (mem_qbfNames_qbfAllFin _ _ _).mp h
      rcases mem_qbfNames_tapeCellBitFormula write head j bit beforeCells afterCells h with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨j, bit, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨j, bit, h⟩))

theorem qbfNames_tapeTransitionFormula_lt {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (B : ℕ)
    (hbh : ∀ j, beforeHead j < B) (hah : ∀ j, afterHead j < B)
    (hbc : ∀ j bit, beforeCells j bit < B) (hac : ∀ j bit, afterCells j bit < B) :
    ∀ i ∈ qbfNames
      (tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells), i < B := by
  intro i hi
  rcases mem_qbfNames_tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells hi
      with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, bit, rfl⟩ | ⟨j, bit, rfl⟩
  · exact hbh j
  · exact hah j
  · exact hbc j bit
  · exact hac j bit

/-- On encoded components, the explicit formula is exactly the partial update. -/
theorem eval_tapeTransitionFormula_components {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeHead afterHead : Fin n → ℕ)
    (beforeCells afterCells : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool)
    (before after : TapeComponent n)
    (hbh : assignment ∘ beforeHead = FixedWidthCodec.encodeFin before.1)
    (hah : assignment ∘ afterHead = FixedWidthCodec.encodeFin after.1)
    (hbc : (fun i bit => assignment (beforeCells i bit)) = before.2)
    (hac : (fun i bit => assignment (afterCells i bit)) = after.2) :
    (tapeTransitionFormula next write beforeHead afterHead beforeCells afterCells).eval
        assignment = true ↔ stepTapeComponent next write before = some after := by
  rw [eval_tapeTransitionFormula, hbh, hah, hbc, hac, stepTapeComponent_eq_some_iff]
  have hinj : Function.Injective (@FixedWidthCodec.encodeFin n) :=
    (FixedWidthCodec.fin n).encode_injective
  simp only [hinj.eq_iff]
  constructor
  · rintro ⟨head, newHead, hnext, rfl, rfl, hcells⟩
    exact ⟨hnext, hcells⟩
  · rintro ⟨hnext, hcells⟩
    exact ⟨before.1, after.1, hnext, rfl, rfl, hcells⟩

/-- Head coordinates in the component codec's packed layout. -/
def tapeHeadNames {n : ℕ} (names : Fin (n + n * 2) → ℕ) (head : Fin n) : ℕ :=
  names (Fin.castAdd (n * 2) head)

/-- Row-major cell coordinates in the component codec's packed layout. -/
def tapeCellNames {n : ℕ} (names : Fin (n + n * 2) → ℕ) (cell : Fin n) (bit : Fin 2) : ℕ :=
  names (Fin.natAdd n (finProdFinEquiv (cell, bit)))

def packedTapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (before after : Fin (n + n * 2) → ℕ) : QBF :=
  tapeTransitionFormula next write (tapeHeadNames before) (tapeHeadNames after)
    (tapeCellNames before) (tapeCellNames after)

@[simp] theorem tapeComponentCodec_encode_head {n : ℕ} (tape : TapeComponent n) (i : Fin n) :
    (tapeComponentCodec n).encode tape (Fin.castAdd (n * 2) i) =
      FixedWidthCodec.encodeFin tape.1 i := by
  simp [tapeComponentCodec, FixedWidthCodec.prod, FixedWidthCodec.fin]

@[simp] theorem tapeComponentCodec_encode_cell {n : ℕ} (tape : TapeComponent n)
    (i : Fin n) (bit : Fin 2) :
    (tapeComponentCodec n).encode tape (Fin.natAdd n (finProdFinEquiv (i, bit))) =
      tape.2 i bit := by
  change (Fin.append (FixedWidthCodec.encodeFin tape.1)
    (fun k => tape.2 (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) _ = _
  rw [Fin.append_right, Equiv.symm_apply_apply]

theorem eval_packedTapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (beforeNames afterNames : Fin (n + n * 2) → ℕ)
    (assignment : ℕ → Bool) (before after : TapeComponent n)
    (hbefore : assignment ∘ beforeNames = (tapeComponentCodec n).encode before)
    (hafter : assignment ∘ afterNames = (tapeComponentCodec n).encode after) :
    (packedTapeTransitionFormula next write beforeNames afterNames).eval assignment = true ↔
      stepTapeComponent next write before = some after := by
  apply eval_tapeTransitionFormula_components
  · funext i
    exact (congrFun hbefore _).trans (tapeComponentCodec_encode_head before i)
  · funext i
    exact (congrFun hafter _).trans (tapeComponentCodec_encode_head after i)
  · funext i bit
    exact (congrFun hbefore _).trans (tapeComponentCodec_encode_cell before i bit)
  · funext i bit
    exact (congrFun hafter _).trans (tapeComponentCodec_encode_cell after i bit)

theorem quantifierFree_packedTapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (before after : Fin (n + n * 2) → ℕ) :
    (packedTapeTransitionFormula next write before after).QuantifierFree :=
  quantifierFree_tapeTransitionFormula _ _ _ _ _ _

theorem nodeCount_packedTapeTransitionFormula_le {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (before after : Fin (n + n * 2) → ℕ) :
    nodeCount (packedTapeTransitionFormula next write before after) ≤ (28 * n + 6) * n + 1 :=
  nodeCount_tapeTransitionFormula_le _ _ _ _ _ _

theorem mem_qbfNames_packedTapeTransitionFormula {n : ℕ} (next : Fin n → Option (Fin n))
    (write : Option (Fin 2 → Bool)) (before after : Fin (n + n * 2) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (packedTapeTransitionFormula next write before after)) :
    (∃ j, before j = i) ∨ (∃ j, after j = i) := by
  rcases mem_qbfNames_tapeTransitionFormula next write _ _ _ _ h with
    ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, bit, hj⟩ | ⟨j, bit, hj⟩
  · exact Or.inl ⟨_, hj⟩
  · exact Or.inr ⟨_, hj⟩
  · exact Or.inl ⟨_, hj⟩
  · exact Or.inr ⟨_, hj⟩

end IPPSPACE

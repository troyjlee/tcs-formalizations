/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineTapeTransition
import IPPSPACE.QBF.ConfigurationLayout

/-!
# Reading symbols and moving the input head

These executable quantifier-free formulas select a tape cell through its one-hot
head, test the fixed input tape directly, and update the bounded input head.
Read tests assume a canonical head in their codec-image theorems; they do not
replace configuration validity. The movement formula checks both complete head
blocks and rejects a right move that exits the stored window. Node and variable
support bounds describe the formula syntax, not machine running time.
-/

namespace IPPSPACE

open Complexity

private theorem blockValues_names_mem_read {n : ℕ} (names : Fin n → ℕ)
    (values : Fin n → Bool) {i : ℕ} (h : i ∈ qbfNames (blockValues names values)) :
    ∃ j, names j = i := by
  induction n with
  | zero => simp [blockValues, qbfNames] at h
  | succ n ih =>
    rcases Finset.mem_union.mp h with h | h
    · refine ⟨0, ?_⟩
      cases hv : values 0 <;> simpa [bitValue, hv, qbfNames, eq_comm] using h
    · obtain ⟨j, hj⟩ := ih (Fin.tail names) (Fin.tail values) h
      exact ⟨j.succ, hj⟩

/-- A selected head bit together with the two bits of the requested symbol.
Only positions, not tape contents, are enumerated. -/
def tapeReadSymbolFormula {n : ℕ} (symbol : Fin 2 → Bool)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) : QBF :=
  qbfAnyFin n (fun head => .conj (.var (headNames head)) (blockValues (cellNames head) symbol))

/-- On arbitrary assignments the test chooses any set head bit carrying the
requested symbol. Canonicality is supplied separately by the validity formula. -/
theorem eval_tapeReadSymbolFormula_iff {n : ℕ} (symbol : Fin 2 → Bool)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool) :
    (tapeReadSymbolFormula symbol headNames cellNames).eval assignment = true ↔
      ∃ head, assignment (headNames head) = true ∧ assignment ∘ cellNames head = symbol := by
  simp [tapeReadSymbolFormula, eval_blockValues]

/-- Exact read semantics on a canonical one-hot head and encoded cell vector. -/
theorem eval_tapeReadSymbolFormula {n : ℕ} (symbol : Fin 2 → Bool)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool)
    (head : Fin n) (cells : Fin n → Fin 2 → Bool)
    (hhead : assignment ∘ headNames = FixedWidthCodec.encodeFin head)
    (hcells : ∀ i bit, assignment (cellNames i bit) = cells i bit) :
    (tapeReadSymbolFormula symbol headNames cellNames).eval assignment = true ↔
      cells head = symbol := by
  rw [eval_tapeReadSymbolFormula_iff]
  have hh (i : Fin n) : assignment (headNames i) = decide (head = i) := congrFun hhead i
  simp only [hh, decide_eq_true_eq]
  constructor
  · rintro ⟨i, rfl, hi⟩
    simpa only [Function.comp_def, hcells] using hi
  · intro h
    refine ⟨head, rfl, ?_⟩
    simpa only [Function.comp_def, hcells] using h

theorem quantifierFree_tapeReadSymbolFormula {n : ℕ} (symbol : Fin 2 → Bool)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) :
    (tapeReadSymbolFormula symbol headNames cellNames).QuantifierFree :=
  quantifierFree_qbfAnyFin _ _ (fun _ =>
    QBF.quantifierFree_conj.mpr ⟨rfl, quantifierFree_blockValues _ _⟩)

theorem nodeCount_tapeReadSymbolFormula_le {n : ℕ} (symbol : Fin 2 → Bool)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) :
    nodeCount (tapeReadSymbolFormula symbol headNames cellNames) ≤ 10 * n + 1 := by
  apply nodeCount_qbfAnyFin_le _ _ 9
  intro head
  have h := nodeCount_blockValues_le (cellNames head) symbol
  simp only [nodeCount]
  omega

theorem mem_qbfNames_tapeReadSymbolFormula {n : ℕ} (symbol : Fin 2 → Bool)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (tapeReadSymbolFormula symbol headNames cellNames)) :
    (∃ j, headNames j = i) ∨ (∃ j bit, cellNames j bit = i) := by
  obtain ⟨head, h⟩ := (mem_qbfNames_qbfAnyFin _ _ _).mp h
  rcases Finset.mem_union.mp h with h | h
  · exact Or.inl ⟨head, (Finset.mem_singleton.mp h).symm⟩
  · obtain ⟨bit, hbit⟩ := blockValues_names_mem_read (cellNames head) symbol h
    exact Or.inr ⟨head, bit, hbit⟩

/-- Read a concrete symbol of the actual imported machine alphabet. -/
def machineTapeReadFormula {n : ℕ} (symbol : Γ)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) : QBF :=
  tapeReadSymbolFormula (machineSymbolBits symbol) headNames cellNames

theorem eval_machineTapeReadFormula {n : ℕ} (symbol : Γ)
    (headNames : Fin n → ℕ) (cellNames : Fin n → Fin 2 → ℕ) (assignment : ℕ → Bool)
    (head : Fin n) (cells : Fin n → Γ)
    (hhead : assignment ∘ headNames = FixedWidthCodec.encodeFin head)
    (hcells : ∀ i bit, assignment (cellNames i bit) = machineSymbolBits (cells i) bit) :
    (machineTapeReadFormula symbol headNames cellNames).eval assignment = true ↔
      cells head = symbol := by
  rw [machineTapeReadFormula,
    eval_tapeReadSymbolFormula _ _ _ _ head (fun i => machineSymbolBits (cells i)) hhead hcells]
  exact machineSymbolBits.injective.eq_iff

/-- The input cells are fixed by the input string, so reading requires only
head bits. The upstream initial tape supplies start, data, and trailing blanks. -/
def fixedInputReadFormula {n : ℕ} (input : List Bool) (symbol : Γ)
    (headNames : Fin n → ℕ) : QBF :=
  qbfAnyFin n (fun head =>
    if (Tape.init (input.map Γ.ofBool)).cells head.val = symbol then .var (headNames head) else .fls)

theorem eval_fixedInputReadFormula_iff {n : ℕ} (input : List Bool) (symbol : Γ)
    (headNames : Fin n → ℕ) (assignment : ℕ → Bool) :
    (fixedInputReadFormula input symbol headNames).eval assignment = true ↔
      ∃ head, (Tape.init (input.map Γ.ofBool)).cells head.val = symbol ∧
        assignment (headNames head) = true := by
  rw [fixedInputReadFormula, eval_qbfAnyFin]
  apply exists_congr
  intro head
  split <;> simp_all

theorem eval_fixedInputReadFormula {n : ℕ} (input : List Bool) (symbol : Γ)
    (headNames : Fin n → ℕ) (assignment : ℕ → Bool) (head : Fin n)
    (hhead : assignment ∘ headNames = FixedWidthCodec.encodeFin head) :
    (fixedInputReadFormula input symbol headNames).eval assignment = true ↔
      (Tape.init (input.map Γ.ofBool)).cells head.val = symbol := by
  rw [eval_fixedInputReadFormula_iff]
  have hh (i : Fin n) : assignment (headNames i) = decide (head = i) := congrFun hhead i
  simp only [hh, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro h
    exact ⟨head, h, rfl⟩

theorem quantifierFree_fixedInputReadFormula {n : ℕ} (input : List Bool) (symbol : Γ)
    (headNames : Fin n → ℕ) : (fixedInputReadFormula input symbol headNames).QuantifierFree := by
  apply quantifierFree_qbfAnyFin
  intro head
  split <;> rfl

theorem nodeCount_fixedInputReadFormula_le {n : ℕ} (input : List Bool) (symbol : Γ)
    (headNames : Fin n → ℕ) : nodeCount (fixedInputReadFormula input symbol headNames) ≤ 2 * n + 1 := by
  apply nodeCount_qbfAnyFin_le _ _ 1
  intro head
  split <;> exact le_rfl

theorem mem_qbfNames_fixedInputReadFormula {n : ℕ} (input : List Bool) (symbol : Γ)
    (headNames : Fin n → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (fixedInputReadFormula input symbol headNames)) :
    ∃ j, headNames j = i := by
  obtain ⟨head, h⟩ := (mem_qbfNames_qbfAnyFin _ _ _).mp h
  split at h
  · exact ⟨head, (Finset.mem_singleton.mp h).symm⟩
  · simp [qbfNames] at h

/-- A bounded input-head move compares both complete one-hot blocks. There is
no input-cell update because the input tape is read-only. -/
def inputHeadMoveFormula {n : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin n → ℕ) : QBF :=
  qbfAnyFin n (fun head =>
    match boundedMachineHead direction head with
    | none => .fls
    | some target => .conj (blockValues beforeNames (FixedWidthCodec.encodeFin head))
        (blockValues afterNames (FixedWidthCodec.encodeFin target)))

theorem eval_inputHeadMoveFormula_iff {n : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin n → ℕ) (assignment : ℕ → Bool) :
    (inputHeadMoveFormula direction beforeNames afterNames).eval assignment = true ↔
      ∃ head target, boundedMachineHead direction head = some target ∧
        assignment ∘ beforeNames = FixedWidthCodec.encodeFin head ∧
        assignment ∘ afterNames = FixedWidthCodec.encodeFin target := by
  rw [inputHeadMoveFormula, eval_qbfAnyFin]
  apply exists_congr
  intro head
  cases hh : boundedMachineHead direction head with
  | none => simp
  | some target => simp [eval_blockValues]

/-- On canonical head codes, acceptance is exactly successful bounded movement. -/
theorem eval_inputHeadMoveFormula {n : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin n → ℕ) (assignment : ℕ → Bool) (before after : Fin n)
    (hbefore : assignment ∘ beforeNames = FixedWidthCodec.encodeFin before)
    (hafter : assignment ∘ afterNames = FixedWidthCodec.encodeFin after) :
    (inputHeadMoveFormula direction beforeNames afterNames).eval assignment = true ↔
      boundedMachineHead direction before = some after := by
  rw [eval_inputHeadMoveFormula_iff, hbefore, hafter]
  have hinj : Function.Injective (@FixedWidthCodec.encodeFin n) :=
    (FixedWidthCodec.fin n).encode_injective
  simp only [hinj.eq_iff]
  constructor
  · rintro ⟨head, target, hmove, rfl, rfl⟩
    exact hmove
  · intro h
    exact ⟨before, after, h, rfl, rfl⟩

theorem quantifierFree_inputHeadMoveFormula {n : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin n → ℕ) :
    (inputHeadMoveFormula direction beforeNames afterNames).QuantifierFree := by
  apply quantifierFree_qbfAnyFin
  intro head
  cases hh : boundedMachineHead direction head with
  | none => rfl
  | some target =>
    exact QBF.quantifierFree_conj.mpr
      ⟨quantifierFree_blockValues _ _, quantifierFree_blockValues _ _⟩

theorem nodeCount_inputHeadMoveFormula_le {n : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin n → ℕ) :
    nodeCount (inputHeadMoveFormula direction beforeNames afterNames) ≤ (6 * n + 4) * n + 1 := by
  apply nodeCount_qbfAnyFin_le _ _ (6 * n + 3)
  intro head
  cases hh : boundedMachineHead direction head with
  | none => simp [nodeCount]
  | some target =>
    have hb := nodeCount_blockValues_le beforeNames (FixedWidthCodec.encodeFin head)
    have ha := nodeCount_blockValues_le afterNames (FixedWidthCodec.encodeFin target)
    simp only [nodeCount]
    omega

theorem mem_qbfNames_inputHeadMoveFormula {n : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin n → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (inputHeadMoveFormula direction beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  obtain ⟨head, h⟩ := (mem_qbfNames_qbfAnyFin _ _ _).mp h
  cases hh : boundedMachineHead direction head with
  | none => simp [hh, qbfNames] at h
  | some target =>
    rw [hh] at h
    rcases Finset.mem_union.mp h with h | h
    · exact Or.inl (blockValues_names_mem_read _ _ h)
    · exact Or.inr (blockValues_names_mem_read _ _ h)

/-- Read the fixed input in a complete configuration's variable layout. -/
def machineInputReadFormula {states tapes : ℕ} (input : List Bool) (space : ℕ) (symbol : Γ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ) : QBF :=
  fixedInputReadFormula input symbol (names ∘ configurationInputHeadIndex states tapes input.length space)

/-- Read one work tape in a complete configuration's variable layout. -/
def machineWorkReadFormula {states tapes inputLength space : ℕ} (symbol : Γ) (tape : Fin tapes)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  machineTapeReadFormula symbol (names ∘ configurationWorkHeadIndex states tapes inputLength space tape)
    (fun i bit => names (configurationWorkCellIndex states tapes inputLength space tape i bit))

/-- Read the output tape in a complete configuration's variable layout. -/
def machineOutputReadFormula {states tapes inputLength space : ℕ} (symbol : Γ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  machineTapeReadFormula symbol (names ∘ configurationOutputHeadIndex states tapes inputLength space)
    (fun i bit => names (configurationOutputCellIndex states tapes inputLength space i bit))

/-- Move the read-only input head inside a complete configuration layout. -/
def machineInputHeadMoveFormula {states tapes inputLength space : ℕ} (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  inputHeadMoveFormula direction
    (beforeNames ∘ configurationInputHeadIndex states tapes inputLength space)
    (afterNames ∘ configurationInputHeadIndex states tapes inputLength space)

theorem eval_machineInputReadFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ) (symbol : Γ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (code : Code Q tapes input.length space)
    (hcode : assignment ∘ names = (machineConfigurationCodec stateNumber tapes input.length space).encode code) :
    (machineInputReadFormula input space symbol names).eval assignment = true ↔
      (machineConfigurationOfCode input space code).input.read = symbol := by
  apply eval_fixedInputReadFormula _ _ _ _ code.2.1
  funext i
  exact (congrFun hcode _).trans
    (configurationCodec_encode_inputHead stateNumber machineSymbolBits tapes input.length space code i)

theorem eval_machineWorkReadFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ) (symbol : Γ) (tape : Fin tapes)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (code : Code Q tapes input.length space)
    (hcode : assignment ∘ names = (machineConfigurationCodec stateNumber tapes input.length space).encode code) :
    (machineWorkReadFormula symbol tape names).eval assignment = true ↔
      ((machineConfigurationOfCode input space code).work tape).read = symbol := by
  have hhead : assignment ∘ (names ∘ configurationWorkHeadIndex states tapes input.length space tape) =
      FixedWidthCodec.encodeFin (code.2.2.1 tape).1 := by
    funext i
    exact (congrFun hcode _).trans
      (configurationCodec_encode_workHead stateNumber machineSymbolBits tapes input.length space code tape i)
  have hcells (i : Fin (space + 1)) (bit : Fin 2) :
      assignment (names (configurationWorkCellIndex states tapes input.length space tape i bit)) =
        machineSymbolBits ((code.2.2.1 tape).2 i) bit :=
    (congrFun hcode _).trans
      (configurationCodec_encode_workCell stateNumber machineSymbolBits tapes input.length space code tape i bit)
  have h := eval_machineTapeReadFormula symbol _ _ assignment (code.2.2.1 tape).1
    (code.2.2.1 tape).2 hhead hcells
  simpa only [machineWorkReadFormula, machineConfigurationOfCode, Tape.read,
    machineTapeOfCode_head, machineTapeOfCode_cells] using h

theorem eval_machineOutputReadFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ) (symbol : Γ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (code : Code Q tapes input.length space)
    (hcode : assignment ∘ names = (machineConfigurationCodec stateNumber tapes input.length space).encode code) :
    (machineOutputReadFormula symbol names).eval assignment = true ↔
      (machineConfigurationOfCode input space code).output.read = symbol := by
  have hhead : assignment ∘ (names ∘ configurationOutputHeadIndex states tapes input.length space) =
      FixedWidthCodec.encodeFin code.2.2.2.1 := by
    funext i
    exact (congrFun hcode _).trans
      (configurationCodec_encode_outputHead stateNumber machineSymbolBits tapes input.length space code i)
  have hcells (i : Fin (space + 2)) (bit : Fin 2) :
      assignment (names (configurationOutputCellIndex states tapes input.length space i bit)) =
        machineSymbolBits (code.2.2.2.2 i) bit :=
    (congrFun hcode _).trans
      (configurationCodec_encode_outputCell stateNumber machineSymbolBits tapes input.length space code i bit)
  have h := eval_machineTapeReadFormula symbol _ _ assignment code.2.2.2.1 code.2.2.2.2 hhead hcells
  simpa only [machineOutputReadFormula, machineConfigurationOfCode, Tape.read,
    machineTapeOfCode_head, machineTapeOfCode_cells] using h

theorem eval_machineInputHeadMoveFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ) (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (before after : Code Q tapes input.length space)
    (hbefore : assignment ∘ beforeNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode before)
    (hafter : assignment ∘ afterNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode after) :
    (machineInputHeadMoveFormula direction beforeNames afterNames).eval assignment = true ↔
      (machineConfigurationOfCode input space after).input =
        (machineConfigurationOfCode input space before).input.move direction := by
  have hb : assignment ∘ (beforeNames ∘ configurationInputHeadIndex states tapes input.length space) =
      FixedWidthCodec.encodeFin before.2.1 := by
    funext i
    exact (congrFun hbefore _).trans
      (configurationCodec_encode_inputHead stateNumber machineSymbolBits tapes input.length space before i)
  have ha : assignment ∘ (afterNames ∘ configurationInputHeadIndex states tapes input.length space) =
      FixedWidthCodec.encodeFin after.2.1 := by
    funext i
    exact (congrFun hafter _).trans
      (configurationCodec_encode_inputHead stateNumber machineSymbolBits tapes input.length space after i)
  rw [machineInputHeadMoveFormula, eval_inputHeadMoveFormula _ _ _ _ before.2.1 after.2.1 hb ha,
    boundedMachineHead_eq_some_iff]
  constructor
  · intro h
    apply Tape.ext
    · rw [machineMovedHead_eq]
      exact h.symm
    · rw [Tape.move_cells]
      rfl
  · intro h
    have hh := congrArg Tape.head h
    rw [machineMovedHead_eq] at hh
    exact hh.symm

theorem quantifierFree_machineInputReadFormula {states tapes : ℕ}
    (input : List Bool) (space : ℕ) (symbol : Γ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ) :
    (machineInputReadFormula input space symbol names).QuantifierFree :=
  quantifierFree_fixedInputReadFormula _ _ _

theorem quantifierFree_machineWorkReadFormula {states tapes inputLength space : ℕ}
    (symbol : Γ) (tape : Fin tapes)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    (machineWorkReadFormula symbol tape names).QuantifierFree :=
  quantifierFree_tapeReadSymbolFormula _ _ _

theorem quantifierFree_machineOutputReadFormula {states tapes inputLength space : ℕ}
    (symbol : Γ) (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    (machineOutputReadFormula symbol names).QuantifierFree := quantifierFree_tapeReadSymbolFormula _ _ _

theorem quantifierFree_machineInputHeadMoveFormula {states tapes inputLength space : ℕ}
    (direction : Dir3) (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    (machineInputHeadMoveFormula direction beforeNames afterNames).QuantifierFree :=
  quantifierFree_inputHeadMoveFormula _ _ _

theorem nodeCount_machineInputReadFormula_le {states tapes : ℕ}
    (input : List Bool) (space : ℕ) (symbol : Γ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ) :
    nodeCount (machineInputReadFormula input space symbol names) ≤ 2 * (input.length + space + 2) + 1 :=
  nodeCount_fixedInputReadFormula_le _ _ _

theorem nodeCount_machineWorkReadFormula_le {states tapes inputLength space : ℕ}
    (symbol : Γ) (tape : Fin tapes)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    nodeCount (machineWorkReadFormula symbol tape names) ≤ 10 * (space + 1) + 1 :=
  nodeCount_tapeReadSymbolFormula_le _ _ _

theorem nodeCount_machineOutputReadFormula_le {states tapes inputLength space : ℕ}
    (symbol : Γ) (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    nodeCount (machineOutputReadFormula symbol names) ≤ 10 * (space + 2) + 1 :=
  nodeCount_tapeReadSymbolFormula_le _ _ _

theorem nodeCount_machineInputHeadMoveFormula_le {states tapes inputLength space : ℕ}
    (direction : Dir3) (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    nodeCount (machineInputHeadMoveFormula direction beforeNames afterNames) ≤
      (6 * (inputLength + space + 2) + 4) * (inputLength + space + 2) + 1 :=
  nodeCount_inputHeadMoveFormula_le _ _ _

theorem mem_qbfNames_machineInputReadFormula {states tapes : ℕ}
    (input : List Bool) (space : ℕ) (symbol : Γ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineInputReadFormula input space symbol names)) : ∃ j, names j = i := by
  obtain ⟨j, hj⟩ := mem_qbfNames_fixedInputReadFormula input symbol _ h
  exact ⟨_, hj⟩

theorem mem_qbfNames_machineWorkReadFormula {states tapes inputLength space : ℕ}
    (symbol : Γ) (tape : Fin tapes)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineWorkReadFormula symbol tape names)) : ∃ j, names j = i := by
  rcases mem_qbfNames_tapeReadSymbolFormula _ _ _ h with ⟨j, hj⟩ | ⟨j, bit, hj⟩
  · exact ⟨_, hj⟩
  · exact ⟨_, hj⟩

theorem mem_qbfNames_machineOutputReadFormula {states tapes inputLength space : ℕ}
    (symbol : Γ) (names : Fin (configurationWidth states tapes inputLength space) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineOutputReadFormula symbol names)) : ∃ j, names j = i := by
  rcases mem_qbfNames_tapeReadSymbolFormula _ _ _ h with ⟨j, hj⟩ | ⟨j, bit, hj⟩
  · exact ⟨_, hj⟩
  · exact ⟨_, hj⟩

theorem mem_qbfNames_machineInputHeadMoveFormula {states tapes inputLength space : ℕ}
    (direction : Dir3) (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ)
    {i : ℕ} (h : i ∈ qbfNames (machineInputHeadMoveFormula direction beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  rcases mem_qbfNames_inputHeadMoveFormula _ _ _ h with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl ⟨_, hj⟩
  · exact Or.inr ⟨_, hj⟩

end IPPSPACE

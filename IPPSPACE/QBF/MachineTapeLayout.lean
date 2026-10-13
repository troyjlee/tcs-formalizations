/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationLayout
import IPPSPACE.QBF.MachineTapeTransition

/-!
# Packed tape blocks inside actual machine configuration codes

The embeddings below reuse the exact configuration-code layout. Restricting
an encoded configuration to a tape block gives its existing tape-component
encoding. Blank tails of reconstructed tapes then upgrade the finite-cell
semantics of the tape formula to equality of the actual infinite tapes.
-/

namespace IPPSPACE

open Complexity

/-- The complete head/cell block of one work tape. -/
def machineWorkTapeIndex (q k n s : ℕ) (t : Fin k) :
    Fin ((s + 1) + (s + 1) * 2) → Fin (configurationWidth q k n s) :=
  fun i => configurationWorkIndex q k n s (finProdFinEquiv (t, i))

/-- The complete head/cell block of the output tape. -/
def machineOutputTapeIndex (q k n s : ℕ) :
    Fin ((s + 2) + (s + 2) * 2) → Fin (configurationWidth q k n s) :=
  configurationOutputIndex q k n s

def machineWorkTapeNames (q k n s : ℕ) (t : Fin k)
    (names : Fin (configurationWidth q k n s) → ℕ) : Fin ((s + 1) + (s + 1) * 2) → ℕ :=
  names ∘ machineWorkTapeIndex q k n s t

def machineOutputTapeNames (q k n s : ℕ)
    (names : Fin (configurationWidth q k n s) → ℕ) : Fin ((s + 2) + (s + 2) * 2) → ℕ :=
  names ∘ machineOutputTapeIndex q k n s

/-- Keep the exact finite head while replacing actual symbols by their two bits. -/
def machineTapeComponentOfCode {n : ℕ} (code : Fin n × (Fin n → Γ)) : TapeComponent n :=
  (code.1, fun i => machineSymbolBits (code.2 i))

theorem machineConfigurationCodec_encode_workTape {Q : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (k n s : ℕ) (code : Code Q k n s) (t : Fin k) :
    (machineConfigurationCodec stateNumber k n s).encode code ∘ machineWorkTapeIndex q k n s t =
      (tapeComponentCodec (s + 1)).encode (machineTapeComponentOfCode (code.2.2.1 t)) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · change (configurationCodec stateNumber machineSymbolBits k n s).encode code
      (configurationWorkHeadIndex q k n s t i) = _
    simp [tapeComponentCodec, FixedWidthCodec.prod, FixedWidthCodec.fin,
      FixedWidthCodec.encodeFin, machineTapeComponentOfCode]
  · obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective j
    change (configurationCodec stateNumber machineSymbolBits k n s).encode code
      (configurationWorkCellIndex q k n s t i b) = _
    simp [tapeComponentCodec, FixedWidthCodec.prod, FixedWidthCodec.word, machineTapeComponentOfCode]

theorem machineConfigurationCodec_encode_outputTape {Q : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (k n s : ℕ) (code : Code Q k n s) :
    (machineConfigurationCodec stateNumber k n s).encode code ∘ machineOutputTapeIndex q k n s =
      (tapeComponentCodec (s + 2)).encode (machineTapeComponentOfCode code.2.2.2) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · change (configurationCodec stateNumber machineSymbolBits k n s).encode code
      (configurationOutputHeadIndex q k n s i) = _
    simp [tapeComponentCodec, FixedWidthCodec.prod, FixedWidthCodec.fin,
      FixedWidthCodec.encodeFin, machineTapeComponentOfCode]
  · obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective j
    change (configurationCodec stateNumber machineSymbolBits k n s).encode code
      (configurationOutputCellIndex q k n s i b) = _
    simp [tapeComponentCodec, FixedWidthCodec.prod, FixedWidthCodec.word, machineTapeComponentOfCode]

@[simp] theorem restrictMachineTape_machineTapeOfCode {n : ℕ}
    (code : Fin n × (Fin n → Γ)) :
    restrictMachineTape (machineTapeOfCode code) code.1.isLt = machineTapeComponentOfCode code := by
  apply Prod.ext
  · rfl
  · funext i
    simp [restrictMachineTape, machineTapeComponentOfCode]

/-- Pull a whole-configuration encoding equality back to one work-tape block. -/
theorem machineWorkTapeNames_encode {Q : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (k n s : ℕ) (code : Code Q k n s) (t : Fin k)
    (names : Fin (configurationWidth q k n s) → ℕ) (assignment : ℕ → Bool)
    (h : assignment ∘ names = (machineConfigurationCodec stateNumber k n s).encode code) :
    assignment ∘ machineWorkTapeNames q k n s t names =
      (tapeComponentCodec (s + 1)).encode
        (restrictMachineTape (machineTapeOfCode (code.2.2.1 t)) (code.2.2.1 t).1.isLt) := by
  rw [restrictMachineTape_machineTapeOfCode, machineWorkTapeNames, ← Function.comp_assoc,
    h, machineConfigurationCodec_encode_workTape]

/-- Pull the encoding equality back to the output block, including its free verdict cell. -/
theorem machineOutputTapeNames_encode {Q : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (k n s : ℕ) (code : Code Q k n s)
    (names : Fin (configurationWidth q k n s) → ℕ) (assignment : ℕ → Bool)
    (h : assignment ∘ names = (machineConfigurationCodec stateNumber k n s).encode code) :
    assignment ∘ machineOutputTapeNames q k n s names =
      (tapeComponentCodec (s + 2)).encode
        (restrictMachineTape (machineTapeOfCode code.2.2.2) code.2.2.2.1.isLt) := by
  rw [restrictMachineTape_machineTapeOfCode, machineOutputTapeNames, ← Function.comp_assoc,
    h, machineConfigurationCodec_encode_outputTape]

/-- Blank tails and a bounded old head make agreement inside the window enough
for full tape equality after write-and-move, including a move leaving the window. -/
theorem machineTape_eq_writeAndMove_iff {n : ℕ} (before after : Tape)
    (symbol : Γ) (direction : Dir3) (headBound : before.head < n)
    (beforeBlank : ∀ p, n ≤ p → before.cells p = Γ.blank)
    (afterBlank : ∀ p, n ≤ p → after.cells p = Γ.blank) :
    after = before.writeAndMove symbol direction ↔
      after.head = (before.writeAndMove symbol direction).head ∧
        ∀ i : Fin n, after.cells i.val = (before.writeAndMove symbol direction).cells i.val := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨hhead, hcells⟩
    apply Tape.ext hhead
    funext p
    by_cases hp : p < n
    · exact hcells ⟨p, hp⟩
    · have hpn : n ≤ p := Nat.le_of_not_gt hp
      rw [cells_writeAndMove_of_ne before symbol direction (by omega),
        beforeBlank p hpn, afterBlank p hpn]

/-- Reconstruction supplies exactly the two blank-tail hypotheses. -/
theorem machineTapeOfCode_eq_writeAndMove_iff {n : ℕ}
    (before after : Fin n × (Fin n → Γ)) (symbol : Γ) (direction : Dir3) :
    machineTapeOfCode after = (machineTapeOfCode before).writeAndMove symbol direction ↔
      (machineTapeOfCode after).head = ((machineTapeOfCode before).writeAndMove symbol direction).head ∧
        ∀ i : Fin n, (machineTapeOfCode after).cells i.val =
          ((machineTapeOfCode before).writeAndMove symbol direction).cells i.val := by
  apply machineTape_eq_writeAndMove_iff _ _ _ _ before.1.isLt <;>
    intro p hp <;> simp [machineTapeOfCode, show ¬ p < n by omega]

/-- The actual tape formula placed in the configuration's selected work block. -/
def machineWorkTapeTransitionFormula {q k n s : ℕ} (symbol : Γ) (direction : Dir3)
    (t : Fin k) (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) : QBF :=
  machineTapeTransitionFormula symbol direction
    (machineWorkTapeNames q k n s t beforeNames) (machineWorkTapeNames q k n s t afterNames)

/-- The same formula placed in the output block. -/
def machineOutputTapeTransitionFormula {q k n s : ℕ} (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) : QBF :=
  machineTapeTransitionFormula symbol direction
    (machineOutputTapeNames q k n s beforeNames) (machineOutputTapeNames q k n s afterNames)

theorem eval_machineWorkTapeTransitionFormula {Q : Type} {q k : ℕ}
    (stateNumber : Q ≃ Fin q) (input : List Bool) (space : ℕ) (symbol : Γ) (direction : Dir3)
    (t : Fin k) (beforeNames afterNames : Fin (configurationWidth q k input.length space) → ℕ)
    (assignment : ℕ → Bool) (before after : Code Q k input.length space)
    (ebefore : assignment ∘ beforeNames =
      (machineConfigurationCodec stateNumber k input.length space).encode before)
    (eafter : assignment ∘ afterNames =
      (machineConfigurationCodec stateNumber k input.length space).encode after) :
    (machineWorkTapeTransitionFormula symbol direction t beforeNames afterNames).eval assignment = true ↔
      (machineConfigurationOfCode input space after).work t =
        ((machineConfigurationOfCode input space before).work t).writeAndMove symbol direction := by
  rw [machineWorkTapeTransitionFormula, eval_machineTapeTransitionFormula symbol direction
    _ _ assignment (machineTapeOfCode (before.2.2.1 t)) (machineTapeOfCode (after.2.2.1 t))
    (before.2.2.1 t).1.isLt (after.2.2.1 t).1.isLt
    (machineWorkTapeNames_encode stateNumber k input.length space before t _ _ ebefore)
    (machineWorkTapeNames_encode stateNumber k input.length space after t _ _ eafter)]
  exact (machineTapeOfCode_eq_writeAndMove_iff (before.2.2.1 t) (after.2.2.1 t) symbol direction).symm

theorem eval_machineOutputTapeTransitionFormula {Q : Type} {q k : ℕ}
    (stateNumber : Q ≃ Fin q) (input : List Bool) (space : ℕ) (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth q k input.length space) → ℕ)
    (assignment : ℕ → Bool) (before after : Code Q k input.length space)
    (ebefore : assignment ∘ beforeNames =
      (machineConfigurationCodec stateNumber k input.length space).encode before)
    (eafter : assignment ∘ afterNames =
      (machineConfigurationCodec stateNumber k input.length space).encode after) :
    (machineOutputTapeTransitionFormula symbol direction beforeNames afterNames).eval assignment = true ↔
      (machineConfigurationOfCode input space after).output =
        (machineConfigurationOfCode input space before).output.writeAndMove symbol direction := by
  rw [machineOutputTapeTransitionFormula, eval_machineTapeTransitionFormula symbol direction
    _ _ assignment (machineTapeOfCode before.2.2.2) (machineTapeOfCode after.2.2.2)
    before.2.2.2.1.isLt after.2.2.2.1.isLt
    (machineOutputTapeNames_encode stateNumber k input.length space before _ _ ebefore)
    (machineOutputTapeNames_encode stateNumber k input.length space after _ _ eafter)]
  exact (machineTapeOfCode_eq_writeAndMove_iff before.2.2.2 after.2.2.2 symbol direction).symm

theorem quantifierFree_machineWorkTapeTransitionFormula {q k n s : ℕ}
    (symbol : Γ) (direction : Dir3) (t : Fin k)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) :
    (machineWorkTapeTransitionFormula symbol direction t beforeNames afterNames).QuantifierFree :=
  quantifierFree_machineTapeTransitionFormula _ _ _ _

theorem quantifierFree_machineOutputTapeTransitionFormula {q k n s : ℕ}
    (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) :
    (machineOutputTapeTransitionFormula symbol direction beforeNames afterNames).QuantifierFree :=
  quantifierFree_machineTapeTransitionFormula _ _ _ _

theorem nodeCount_machineWorkTapeTransitionFormula_le {q k n s : ℕ}
    (symbol : Γ) (direction : Dir3) (t : Fin k)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) :
    nodeCount (machineWorkTapeTransitionFormula symbol direction t beforeNames afterNames) ≤
      (28 * (s + 1) + 6) * (s + 1) + 1 :=
  nodeCount_machineTapeTransitionFormula_le _ _ _ _

theorem nodeCount_machineOutputTapeTransitionFormula_le {q k n s : ℕ}
    (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) :
    nodeCount (machineOutputTapeTransitionFormula symbol direction beforeNames afterNames) ≤
      (28 * (s + 2) + 6) * (s + 2) + 1 :=
  nodeCount_machineTapeTransitionFormula_le _ _ _ _

theorem mem_qbfNames_machineWorkTapeTransitionFormula {q k n s : ℕ}
    (symbol : Γ) (direction : Dir3) (t : Fin k)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineWorkTapeTransitionFormula symbol direction t beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  rcases mem_qbfNames_machineTapeTransitionFormula symbol direction
    (machineWorkTapeNames q k n s t beforeNames) (machineWorkTapeNames q k n s t afterNames) h with
    ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl ⟨machineWorkTapeIndex q k n s t j, hj⟩
  · exact Or.inr ⟨machineWorkTapeIndex q k n s t j, hj⟩

theorem mem_qbfNames_machineOutputTapeTransitionFormula {q k n s : ℕ}
    (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (configurationWidth q k n s) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineOutputTapeTransitionFormula symbol direction beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  rcases mem_qbfNames_machineTapeTransitionFormula symbol direction
    (machineOutputTapeNames q k n s beforeNames) (machineOutputTapeNames q k n s afterNames) h with
    ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl ⟨machineOutputTapeIndex q k n s j, hj⟩
  · exact Or.inr ⟨machineOutputTapeIndex q k n s j, hj⟩

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.TapeTransition
import IPPSPACE.QBF.MachineConfiguration

/-!
# Tape formulas refine the imported machine's tape operations

The bounded component update is the restriction of the actual upstream
`Complexity.Tape.writeAndMove`: the old head must lie in the stored window,
and a successful move must stay in that window. Writing at zero is ignored,
and a left move at zero stays there. Right moves out of the window reject.

These are component equations for the imported infinite tape, rather than a
complete machine transition construction or a running-time theorem. A bounded
restriction does not identify the cells outside its window.
-/

namespace IPPSPACE

open Complexity

/-- The exact natural head arithmetic in upstream `Tape.move`. -/
def machineMovedHead (direction : Dir3) (head : ℕ) : ℕ :=
  match direction with
  | .left => head - 1
  | .right => head + 1
  | .stay => head

@[simp] theorem machineMovedHead_eq (tape : Tape) (direction : Dir3) :
    (tape.move direction).head = machineMovedHead direction tape.head := by
  cases direction <;> rfl

@[simp] theorem machineMovedHead_write (tape : Tape) (symbol : Γ) (direction : Dir3) :
    (tape.writeAndMove symbol direction).head = machineMovedHead direction tape.head := by
  simp [Tape.writeAndMove, Tape.write_head]

/-- The actual direction operation, made partial at the finite right boundary. -/
def boundedMachineHead {n : ℕ} (direction : Dir3) : Fin n → Option (Fin n) :=
  match direction with
  | .left => boundedHeadLeft
  | .right => boundedHeadRight
  | .stay => boundedHeadStay

theorem boundedMachineHead_eq_some_iff {n : ℕ} (direction : Dir3) (head target : Fin n) :
    boundedMachineHead direction head = some target ↔
      machineMovedHead direction head.val = target.val := by
  cases direction with
  | left => simp [boundedMachineHead, boundedHeadLeft, machineMovedHead, Fin.ext_iff]
  | right =>
    by_cases h : head.val + 1 < n
    · simp [boundedMachineHead, boundedHeadRight, machineMovedHead, h, Fin.ext_iff]
    · simp [boundedMachineHead, boundedHeadRight, machineMovedHead, h]
      omega
  | stay => simp [boundedMachineHead, boundedHeadStay, machineMovedHead, Fin.ext_iff]

theorem boundedMachineHead_eq_none_iff {n : ℕ} (direction : Dir3) (head : Fin n) :
    boundedMachineHead direction head = none ↔ n ≤ machineMovedHead direction head.val := by
  cases direction with
  | left =>
    simp [boundedMachineHead, boundedHeadLeft, machineMovedHead]
    omega
  | right => simp [boundedMachineHead, boundedHeadRight, machineMovedHead]
  | stay => simp [boundedMachineHead, boundedHeadStay, machineMovedHead, head.isLt]

/-- Store precisely the finite window of an actual tape whose head is in it. -/
def restrictMachineTape {n : ℕ} (tape : Tape) (headBound : tape.head < n) : TapeComponent n :=
  (⟨tape.head, headBound⟩, fun i => machineSymbolBits (tape.cells i.val))

theorem restrictMachineTape_write_cells {n : ℕ} (tape : Tape) (symbol : Γ)
    (headBound : tape.head < n) :
    (restrictMachineTape (tape.write symbol) (by simpa [Tape.write_head] using headBound)).2 =
      writeTapeCells (some (machineSymbolBits symbol)) ⟨tape.head, headBound⟩
        (restrictMachineTape tape headBound).2 := by
  funext i bit
  by_cases hz : tape.head = 0
  · simp [restrictMachineTape, Tape.write, writeTapeCells, hz]
  · by_cases hi : i.val = tape.head
    · simp [restrictMachineTape, Tape.write, writeTapeCells, hz, Fin.ext_iff, hi]
    · simp [restrictMachineTape, Tape.write, writeTapeCells, hz, Fin.ext_iff, hi]

/-- The executable component update equals restriction of upstream write-and-move. -/
theorem stepTapeComponent_restrictMachineTape {n : ℕ} (tape : Tape) (symbol : Γ)
    (direction : Dir3) (headBound : tape.head < n)
    (nextBound : (tape.writeAndMove symbol direction).head < n) :
    stepTapeComponent (boundedMachineHead direction) (some (machineSymbolBits symbol))
        (restrictMachineTape tape headBound) =
      some (restrictMachineTape (tape.writeAndMove symbol direction) nextBound) := by
  rw [stepTapeComponent_eq_some_iff]
  constructor
  · apply (boundedMachineHead_eq_some_iff _ _ _).mpr
    exact (machineMovedHead_write tape symbol direction).symm
  · change (fun i : Fin n => machineSymbolBits ((tape.writeAndMove symbol direction).cells i.val)) = _
    rw [Tape.move_cells]
    exact restrictMachineTape_write_cells tape symbol headBound

/-- The bounded executable operation rejects exactly when the actual moved head
leaves the window. There is no wraparound or clamping. -/
theorem stepTapeComponent_restrictMachineTape_eq_none_iff {n : ℕ} (tape : Tape) (symbol : Γ)
    (direction : Dir3) (headBound : tape.head < n) :
    stepTapeComponent (boundedMachineHead direction) (some (machineSymbolBits symbol))
        (restrictMachineTape tape headBound) = none ↔
      n ≤ (tape.writeAndMove symbol direction).head := by
  rw [stepTapeComponent_eq_none_iff, boundedMachineHead_eq_none_iff, machineMovedHead_write]
  rfl

/-- Equality is asserted on the stored window. The infinite tails are not encoded. -/
theorem stepTapeComponent_restrictMachineTape_eq_some_iff {n : ℕ} (before after : Tape)
    (symbol : Γ) (direction : Dir3) (hbefore : before.head < n) (hafter : after.head < n) :
    stepTapeComponent (boundedMachineHead direction) (some (machineSymbolBits symbol))
        (restrictMachineTape before hbefore) = some (restrictMachineTape after hafter) ↔
      after.head = (before.writeAndMove symbol direction).head ∧
        ∀ i : Fin n, after.cells i.val = (before.writeAndMove symbol direction).cells i.val := by
  rw [stepTapeComponent_eq_some_iff, boundedMachineHead_eq_some_iff]
  have hwrite : (fun i : Fin n =>
      machineSymbolBits ((before.writeAndMove symbol direction).cells i.val)) =
      writeTapeCells (some (machineSymbolBits symbol)) ⟨before.head, hbefore⟩
        (restrictMachineTape before hbefore).2 := by
    rw [Tape.move_cells]
    exact restrictMachineTape_write_cells before symbol hbefore
  dsimp only [restrictMachineTape] at hwrite ⊢
  rw [← hwrite, machineMovedHead_write]
  constructor
  · rintro ⟨hhead, hcells⟩
    exact ⟨hhead.symm, fun i => machineSymbolBits.injective (congrFun hcells i)⟩
  · rintro ⟨hhead, hcells⟩
    exact ⟨hhead.symm, funext (fun i => congrArg machineSymbolBits (hcells i))⟩

/-- Explicit syntax for a fixed actual-machine write symbol and direction. -/
def machineTapeTransitionFormula {n : ℕ} (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (n + n * 2) → ℕ) : QBF :=
  packedTapeTransitionFormula (boundedMachineHead direction) (some (machineSymbolBits symbol))
    beforeNames afterNames

/-- On canonical restrictions, the formula recognizes exactly the upstream tape
operation's head and stored cells. This includes rejection of escaping right moves. -/
theorem eval_machineTapeTransitionFormula {n : ℕ} (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (n + n * 2) → ℕ) (assignment : ℕ → Bool)
    (before after : Tape) (hbefore : before.head < n) (hafter : after.head < n)
    (ebefore : assignment ∘ beforeNames =
      (tapeComponentCodec n).encode (restrictMachineTape before hbefore))
    (eafter : assignment ∘ afterNames =
      (tapeComponentCodec n).encode (restrictMachineTape after hafter)) :
    (machineTapeTransitionFormula symbol direction beforeNames afterNames).eval assignment = true ↔
      after.head = (before.writeAndMove symbol direction).head ∧
        ∀ i : Fin n, after.cells i.val = (before.writeAndMove symbol direction).cells i.val := by
  rw [machineTapeTransitionFormula,
    eval_packedTapeTransitionFormula _ _ _ _ _ _ _ ebefore eafter]
  exact stepTapeComponent_restrictMachineTape_eq_some_iff before after symbol direction hbefore hafter

theorem quantifierFree_machineTapeTransitionFormula {n : ℕ} (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (n + n * 2) → ℕ) :
    (machineTapeTransitionFormula symbol direction beforeNames afterNames).QuantifierFree :=
  quantifierFree_packedTapeTransitionFormula _ _ _ _

theorem nodeCount_machineTapeTransitionFormula_le {n : ℕ} (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (n + n * 2) → ℕ) :
    nodeCount (machineTapeTransitionFormula symbol direction beforeNames afterNames) ≤
      (28 * n + 6) * n + 1 :=
  nodeCount_packedTapeTransitionFormula_le _ _ _ _

theorem mem_qbfNames_machineTapeTransitionFormula {n : ℕ} (symbol : Γ) (direction : Dir3)
    (beforeNames afterNames : Fin (n + n * 2) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineTapeTransitionFormula symbol direction beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) :=
  mem_qbfNames_packedTapeTransitionFormula _ _ _ _ h

end IPPSPACE

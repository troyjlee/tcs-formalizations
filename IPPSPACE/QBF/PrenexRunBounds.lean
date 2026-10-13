/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexStepBounds

/-!
# Bounds for every intermediate prenex-machine state

At a fixed iteration horizon, lexical environments and binary counters have
linear per-step bounds. Summing the additive transition cost gives a cubic
bound in the original encoding length for the complete conversion.
-/

namespace IPPSPACE

open Complexity

theorem prenexMachineRun_bounds (state : PrenexMachineState) (L E B limit : ℕ)
    (h : state.ControlBound L E B) (steps : ℕ) (hsteps : steps ≤ limit) :
    let C := 4 * L + 2 * (B + 2 * limit) + 6
    let A := 128 * (L + (E + limit * C) + (B + 2 * limit) + 1)
    (prenexMachineRun steps state).ControlBound L (E + steps * C) (B + 2 * steps) ∧
      (encodePrenexMachineState (prenexMachineRun steps state)).length ≤
        (encodePrenexMachineState state).length + steps * A := by
  let C := 4 * L + 2 * (B + 2 * limit) + 6
  let A := 128 * (L + (E + limit * C) + (B + 2 * limit) + 1)
  change (prenexMachineRun steps state).ControlBound L (E + steps * C) (B + 2 * steps) ∧
    (encodePrenexMachineState (prenexMachineRun steps state)).length ≤
      (encodePrenexMachineState state).length + steps * A
  induction steps with
  | zero => simpa using And.intro h (Nat.le_refl (encodePrenexMachineState state).length)
  | succ steps ih =>
    obtain ⟨hc, hl⟩ := ih (by omega)
    rw [prenexMachineRun_succ_last]
    refine ⟨(prenexMachineStep_controlBound hc).mono ?_ (by omega), ?_⟩
    · dsimp [C]
      nlinarith
    · have hs := prenexMachineStep_length_le hc
      have hm : steps * C ≤ limit * C := Nat.mul_le_mul_right C (by omega)
      have ha : 128 * (L + (E + steps * C) + (B + 2 * steps) + 1) ≤ A := by
        dsimp [A]
        omega
      calc
        _ ≤ (encodePrenexMachineState (prenexMachineRun steps state)).length +
            128 * (L + (E + steps * C) + (B + 2 * steps) + 1) := hs
        _ ≤ (encodePrenexMachineState state).length + steps * A + A := Nat.add_le_add hl ha
        _ = _ := by ring

theorem prenexMachineInitial_controlBound (formula : QBF) :
    (prenexMachineInitial formula).ControlBound (encodeQBF formula).length 0
      ((encodeQBF formula).length + 1) := by
  have hn := successor_bits_length_le (qbfMaxVar formula)
  have hm := qbfMaxVar_size_le_encoding formula
  simp only [Nat.size_eq_bits_len] at hn
  constructor
  · change (qbfMaxVar formula + 1).bits.length ≤ (encodeQBF formula).length + 1
    simp only [Nat.size_eq_bits_len]
    omega
  · simp [prenexMachineInitial, PrenexTask.ControlBound]

theorem prenexMachineInitial_length_le (formula : QBF) :
    (encodePrenexMachineState (prenexMachineInitial formula)).length ≤
      10 * (encodeQBF formula).length + 30 := by
  have hn : (qbfMaxVar formula + 1).bits.length ≤ (encodeQBF formula).length + 1 :=
    (prenexMachineInitial_controlBound formula).1
  simp [prenexMachineInitial, length_encodePrenexMachineState]
  omega

/-- Every intermediate encoded state fits in a cubic polynomial of input size.
The numerical values of variable names are unrestricted. -/
theorem prenexMachineRun_initial_length_le (formula : QBF) (steps : ℕ)
    (hsteps : steps ≤ 2 * (encodeQBF formula).length) :
    (encodePrenexMachineState (prenexMachineRun steps (prenexMachineInitial formula))).length ≤
      8192 * ((encodeQBF formula).length + 1) ^ 3 := by
  let L := (encodeQBF formula).length
  have h := (prenexMachineRun_bounds (prenexMachineInitial formula) L 0 (L + 1) (2 * L)
    (prenexMachineInitial_controlBound formula) steps hsteps).2
  have hi := prenexMachineInitial_length_le formula
  change (encodePrenexMachineState (prenexMachineRun steps (prenexMachineInitial formula))).length ≤
    8192 * (L + 1) ^ 3
  have hmul := Nat.mul_le_mul_right
    (128 * (L + (0 + 2 * L * (4 * L + 2 * (L + 1 + 2 * (2 * L)) + 6)) +
      (L + 1 + 2 * (2 * L)) + 1)) hsteps
  change (encodePrenexMachineState (prenexMachineInitial formula)).length ≤ 10 * L + 30 at hi
  nlinarith

end IPPSPACE

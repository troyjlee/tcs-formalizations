/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineTransition

/-!
# Polynomial size of the complete transition table formula

Only control states and symbols under the heads are enumerated. Their number is
a constant for a fixed machine. The stored head positions and tape contents
contribute a quadratic node budget in input length and space.
-/

namespace IPPSPACE

open Complexity

def machineCommandNodeBound (tapes inputLength space : ℕ) : ℕ :=
  ((6 * (inputLength + space + 2) + 4) * (inputLength + space + 2) + 1) +
    (((28 * (space + 1) + 6) * (space + 1) + 2) * tapes + 1) +
    ((28 * (space + 2) + 6) * (space + 2) + 1) + 6

def machineBranchNodeBound (tapes inputLength space : ℕ) : ℕ :=
  (2 * (inputLength + space + 2) + 1) + ((10 * (space + 1) + 2) * tapes + 1) +
    (10 * (space + 2) + 1) + machineCommandNodeBound tapes inputLength space + 7

def machineTransitionNodeBound (states tapes inputLength space : ℕ) : ℕ :=
  ((machineBranchNodeBound tapes inputLength space + 1) * 4 ^ (tapes + 2) + 2) * states + 1

theorem nodeCount_machineCommandFormula_le {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ)
    (command : MachineCommand Q tapes)
    (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    nodeCount (machineCommandFormula stateNumber inputLength space command beforeNames afterNames) ≤
      machineCommandNodeBound tapes inputLength space := by
  have hi := nodeCount_machineInputHeadMoveFormula_le command.2.2.2.1 beforeNames afterNames
  have hw := nodeCount_qbfAllFin_le tapes
    (fun i => machineWorkTapeTransitionFormula (command.2.1 i) (command.2.2.2.2.1 i)
      i beforeNames afterNames) ((28 * (space + 1) + 6) * (space + 1) + 1)
    (fun i => nodeCount_machineWorkTapeTransitionFormula_le _ _ i beforeNames afterNames)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hw
  have ho := nodeCount_machineOutputTapeTransitionFormula_le command.2.2.1 command.2.2.2.2.2
    beforeNames afterNames
  simp only [machineCommandFormula, qbfAll, machineStateFormula, nodeCount,
    machineCommandNodeBound]
  omega

theorem nodeCount_machineTransitionBranch_le {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (state : Fin states) (read : MachineReadCase tapes) :
    nodeCount (machineTransitionBranch tm stateNumber input space beforeNames afterNames state read) ≤
      machineBranchNodeBound tapes input.length space := by
  unfold machineTransitionBranch
  split
  · simp only [nodeCount, machineBranchNodeBound]
    omega
  · have hi := nodeCount_machineInputReadFormula_le input space read.1 beforeNames
    have hw := nodeCount_qbfAllFin_le tapes
      (fun i => machineWorkReadFormula (read.2.1 i) i beforeNames) (10 * (space + 1) + 1)
      (fun i => nodeCount_machineWorkReadFormula_le _ i beforeNames)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hw
    have ho := nodeCount_machineOutputReadFormula_le read.2.2 beforeNames
    have hc := nodeCount_machineCommandFormula_le stateNumber input.length space
      (tm.δ (stateNumber.symm state) read.1 read.2.1 read.2.2) beforeNames afterNames
    simp only [qbfAll, machineStateFormula, nodeCount, machineBranchNodeBound]
    omega

theorem nodeCount_machineTransitionFormula_le {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ) :
    nodeCount (machineTransitionFormula tm stateNumber input space beforeNames afterNames) ≤
      machineTransitionNodeBound states tapes input.length space := by
  apply nodeCount_qbfAnyFin_le states _
    ((machineBranchNodeBound tapes input.length space + 1) * 4 ^ (tapes + 2) + 1)
  intro state
  have h := nodeCount_qbfAny_le
    ((machineReadCases tapes).map
      (machineTransitionBranch tm stateNumber input space beforeNames afterNames state))
    (machineBranchNodeBound tapes input.length space) (by
      intro formula hformula
      obtain ⟨read, _, rfl⟩ := List.mem_map.mp hformula
      exact nodeCount_machineTransitionBranch_le _ _ _ _ _ _ _ _)
  simpa only [List.length_map, length_machineReadCases] using h

noncomputable def machineCommandNodePolynomial (tapes : ℕ) (space : Polynomial ℕ) : Polynomial ℕ :=
  ((6 * (Polynomial.X + space + 2) + 4) * (Polynomial.X + space + 2) + 1) +
    (((28 * (space + 1) + 6) * (space + 1) + 2) * Polynomial.C tapes + 1) +
    ((28 * (space + 2) + 6) * (space + 2) + 1) + 6

noncomputable def machineBranchNodePolynomial (tapes : ℕ) (space : Polynomial ℕ) : Polynomial ℕ :=
  (2 * (Polynomial.X + space + 2) + 1) +
    ((10 * (space + 1) + 2) * Polynomial.C tapes + 1) +
    (10 * (space + 2) + 1) + machineCommandNodePolynomial tapes space + 7

noncomputable def machineTransitionNodePolynomial
    (states tapes : ℕ) (space : Polynomial ℕ) : Polynomial ℕ :=
  ((machineBranchNodePolynomial tapes space + 1) * Polynomial.C (4 ^ (tapes + 2)) + 2) *
    Polynomial.C states + 1

@[simp] theorem machineCommandNodePolynomial_eval (tapes : ℕ) (space : Polynomial ℕ) (n : ℕ) :
    (machineCommandNodePolynomial tapes space).eval n =
      machineCommandNodeBound tapes n (space.eval n) := by
  simp [machineCommandNodePolynomial, machineCommandNodeBound]

@[simp] theorem machineBranchNodePolynomial_eval (tapes : ℕ) (space : Polynomial ℕ) (n : ℕ) :
    (machineBranchNodePolynomial tapes space).eval n =
      machineBranchNodeBound tapes n (space.eval n) := by
  simp [machineBranchNodePolynomial, machineBranchNodeBound]

@[simp] theorem machineTransitionNodePolynomial_eval
    (states tapes : ℕ) (space : Polynomial ℕ) (n : ℕ) :
    (machineTransitionNodePolynomial states tapes space).eval n =
      machineTransitionNodeBound states tapes n (space.eval n) := by
  simp [machineTransitionNodePolynomial, machineTransitionNodeBound]

end IPPSPACE

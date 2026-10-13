/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineTransitionCases
import IPPSPACE.QBF.MachineRead
import IPPSPACE.QBF.MachineTapeLayout

/-!
# The full deterministic machine transition as an explicit QBF

The formula enumerates finite control states and head-read symbol tuples, then
uses the imported machine's actual transition table. It checks the new state,
read-only input-head movement, and every work/output write-and-move operation.
Halting states and moves escaping the stored windows are rejected.

Correctness is on canonical finite codes, whose reconstruction fixes the input
contents and fills omitted cells with blanks. A separate validity guard handles
arbitrary bit assignments. The number of table cases depends on the fixed
machine, while each branch has polynomial syntax size in the stored windows.
No machine-time certificate is asserted here.
-/

namespace IPPSPACE

open Complexity

def machineCommandFormula {Q : Type} {states tapes : ℕ} (stateNumber : Q ≃ Fin states)
    (inputLength space : ℕ) (command : MachineCommand Q tapes)
    (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  qbfAll [
    machineStateFormula stateNumber tapes inputLength space command.1 afterNames,
    machineInputHeadMoveFormula command.2.2.2.1 beforeNames afterNames,
    qbfAllFin tapes (fun i => machineWorkTapeTransitionFormula (command.2.1 i)
      (command.2.2.2.2.1 i) i beforeNames afterNames),
    machineOutputTapeTransitionFormula command.2.2.1 command.2.2.2.2.2 beforeNames afterNames]

def machineTransitionBranch {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (state : Fin states) (read : MachineReadCase tapes) : QBF :=
  if stateNumber.symm state = tm.qhalt then .fls else
    qbfAll [
      machineStateFormula stateNumber tapes input.length space (stateNumber.symm state) beforeNames,
      machineInputReadFormula input space read.1 beforeNames,
      qbfAllFin tapes (fun i => machineWorkReadFormula (read.2.1 i) i beforeNames),
      machineOutputReadFormula read.2.2 beforeNames,
      machineCommandFormula stateNumber input.length space
        (tm.δ (stateNumber.symm state) read.1 read.2.1 read.2.2) beforeNames afterNames]

/-- Enumerate only the fixed control/read table, never complete tape contents. -/
def machineTransitionFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ) : QBF :=
  qbfAnyFin states (fun state => qbfAny ((machineReadCases tapes).map
    (machineTransitionBranch tm stateNumber input space beforeNames afterNames state)))

theorem eval_machineCommandFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (command : MachineCommand Q tapes)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (before after : Code Q tapes input.length space)
    (ebefore : assignment ∘ beforeNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode before)
    (eafter : assignment ∘ afterNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode after) :
    (machineCommandFormula stateNumber input.length space command beforeNames afterNames).eval
        assignment = true ↔
      machineConfigurationOfCode input space after =
        executeMachineCommand (machineConfigurationOfCode input space before) command := by
  simp only [machineCommandFormula, qbfAll, QBF.eval_conj, QBF.eval_tru,
    Bool.and_eq_true, and_true, eval_qbfAllFin,
    eval_machineStateFormula stateNumber input.length space command.1 afterNames assignment after eafter,
    eval_machineInputHeadMoveFormula stateNumber input space command.2.2.2.1
      beforeNames afterNames assignment before after ebefore eafter,
    eval_machineWorkTapeTransitionFormula stateNumber input space _ _ _
      beforeNames afterNames assignment before after ebefore eafter,
    eval_machineOutputTapeTransitionFormula stateNumber input space _ _
      beforeNames afterNames assignment before after ebefore eafter]
  constructor
  · rintro ⟨hstate, hinput, hwork, houtput⟩
    exact Cfg.ext hstate hinput (funext hwork) houtput
  · intro h
    exact ⟨congrArg Cfg.state h, congrArg Cfg.input h,
      fun i => congrFun (congrArg Cfg.work h) i, congrArg Cfg.output h⟩

theorem eval_machineTransitionBranch {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (before after : Code tm.Q tapes input.length space)
    (ebefore : assignment ∘ beforeNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode before)
    (eafter : assignment ∘ afterNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode after)
    (state : Fin states) (read : MachineReadCase tapes) :
    (machineTransitionBranch tm stateNumber input space beforeNames afterNames state read).eval
        assignment = true ↔
      stateNumber.symm state ≠ tm.qhalt ∧
      (machineConfigurationOfCode input space before).state = stateNumber.symm state ∧
      (machineConfigurationOfCode input space before).input.read = read.1 ∧
      (∀ i, ((machineConfigurationOfCode input space before).work i).read = read.2.1 i) ∧
      (machineConfigurationOfCode input space before).output.read = read.2.2 ∧
      machineConfigurationOfCode input space after =
        executeMachineCommand (machineConfigurationOfCode input space before)
          (tm.δ (stateNumber.symm state) read.1 read.2.1 read.2.2) := by
  by_cases hhalt : stateNumber.symm state = tm.qhalt
  · simp [machineTransitionBranch, hhalt]
  · simp only [machineTransitionBranch, hhalt, ↓reduceIte,
      qbfAll, QBF.eval_conj, QBF.eval_tru, Bool.and_eq_true, and_true, eval_qbfAllFin,
      eval_machineStateFormula stateNumber input.length space _ beforeNames assignment before ebefore,
      eval_machineInputReadFormula stateNumber input space _ beforeNames assignment before ebefore,
      eval_machineWorkReadFormula stateNumber input space _ _ beforeNames assignment before ebefore,
      eval_machineOutputReadFormula stateNumber input space _ beforeNames assignment before ebefore,
      eval_machineCommandFormula stateNumber input space _ beforeNames afterNames assignment before after
        ebefore eafter]
    exact ⟨fun h => ⟨hhalt, h⟩, fun h => h.2⟩

/-- Exact full-step semantics for any pair of canonical bounded configuration codes. -/
theorem eval_machineTransitionFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) (before after : Code tm.Q tapes input.length space)
    (ebefore : assignment ∘ beforeNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode before)
    (eafter : assignment ∘ afterNames =
      (machineConfigurationCodec stateNumber tapes input.length space).encode after) :
    (machineTransitionFormula tm stateNumber input space beforeNames afterNames).eval
        assignment = true ↔
      tm.step (machineConfigurationOfCode input space before) =
        some (machineConfigurationOfCode input space after) := by
  rw [step_eq_some_iff_machineReadCase tm stateNumber]
  rw [machineTransitionFormula, eval_qbfAnyFin]
  apply exists_congr
  intro state
  rw [eval_qbfAny]
  constructor
  · rintro ⟨φ, hφ, heval⟩
    obtain ⟨read, _, rfl⟩ := List.mem_map.mp hφ
    exact ⟨read, (eval_machineTransitionBranch tm stateNumber input space beforeNames afterNames
      assignment before after ebefore eafter state read).mp heval⟩
  · rintro ⟨read, hread⟩
    exact ⟨_, List.mem_map.mpr ⟨read, mem_machineReadCases _, rfl⟩,
      (eval_machineTransitionBranch tm stateNumber input space beforeNames afterNames
        assignment before after ebefore eafter state read).mpr hread⟩

theorem quantifierFree_machineCommandFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (command : MachineCommand Q tapes)
    (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    (machineCommandFormula stateNumber inputLength space command beforeNames afterNames).QuantifierFree := by
  apply quantifierFree_qbfAll
  intro φ hφ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl
  · rfl
  · exact quantifierFree_machineInputHeadMoveFormula _ _ _
  · exact quantifierFree_qbfAllFin _ _ (fun _ =>
      quantifierFree_machineWorkTapeTransitionFormula _ _ _ _ _)
  · exact quantifierFree_machineOutputTapeTransitionFormula _ _ _ _

theorem quantifierFree_machineTransitionBranch {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (state : Fin states) (read : MachineReadCase tapes) :
    (machineTransitionBranch tm stateNumber input space beforeNames afterNames state read).QuantifierFree := by
  unfold machineTransitionBranch
  split
  · rfl
  · apply quantifierFree_qbfAll
    intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact quantifierFree_machineInputReadFormula _ _ _ _
    · exact quantifierFree_qbfAllFin _ _ (fun _ => quantifierFree_machineWorkReadFormula _ _ _)
    · exact quantifierFree_machineOutputReadFormula _ _
    · exact quantifierFree_machineCommandFormula _ _ _ _ _ _

theorem quantifierFree_machineTransitionFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ) :
    (machineTransitionFormula tm stateNumber input space beforeNames afterNames).QuantifierFree := by
  apply quantifierFree_qbfAnyFin
  intro state
  apply quantifierFree_qbfAny
  intro φ hφ
  obtain ⟨read, _, rfl⟩ := List.mem_map.mp hφ
  exact quantifierFree_machineTransitionBranch _ _ _ _ _ _ _ _

theorem mem_qbfNames_machineCommandFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (command : MachineCommand Q tapes)
    (beforeNames afterNames : Fin (configurationWidth states tapes inputLength space) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineCommandFormula stateNumber inputLength space command beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  obtain ⟨φ, hφ, hi⟩ := (mem_qbfNames_qbfAll _ _).mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl
  · exact Or.inr ⟨_, (Finset.mem_singleton.mp hi).symm⟩
  · exact mem_qbfNames_machineInputHeadMoveFormula _ _ _ hi
  · obtain ⟨t, ht⟩ := (mem_qbfNames_qbfAllFin _ _ _).mp hi
    exact mem_qbfNames_machineWorkTapeTransitionFormula _ _ t _ _ ht
  · exact mem_qbfNames_machineOutputTapeTransitionFormula _ _ _ _ hi

theorem mem_qbfNames_machineTransitionBranch {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ)
    (state : Fin states) (read : MachineReadCase tapes) {i : ℕ}
    (h : i ∈ qbfNames (machineTransitionBranch tm stateNumber input space beforeNames afterNames state read)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  unfold machineTransitionBranch at h
  split at h
  · simp [qbfNames] at h
  · obtain ⟨φ, hφ, hi⟩ := (mem_qbfNames_qbfAll _ _).mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, (Finset.mem_singleton.mp hi).symm⟩
    · exact Or.inl (mem_qbfNames_machineInputReadFormula _ _ _ _ hi)
    · obtain ⟨t, ht⟩ := (mem_qbfNames_qbfAllFin _ _ _).mp hi
      exact Or.inl (mem_qbfNames_machineWorkReadFormula _ t _ ht)
    · exact Or.inl (mem_qbfNames_machineOutputReadFormula _ _ hi)
    · exact mem_qbfNames_machineCommandFormula _ _ _ _ _ _ hi

/-- The transition introduces no names beyond its two configuration blocks. -/
theorem mem_qbfNames_machineTransitionFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (beforeNames afterNames : Fin (configurationWidth states tapes input.length space) → ℕ) {i : ℕ}
    (h : i ∈ qbfNames (machineTransitionFormula tm stateNumber input space beforeNames afterNames)) :
    (∃ j, beforeNames j = i) ∨ (∃ j, afterNames j = i) := by
  obtain ⟨state, h⟩ := (mem_qbfNames_qbfAnyFin _ _ _).mp h
  obtain ⟨φ, hφ, hi⟩ := (mem_qbfNames_qbfAny _ _).mp h
  obtain ⟨read, _, rfl⟩ := List.mem_map.mp hφ
  exact mem_qbfNames_machineTransitionBranch _ _ _ _ _ _ state read hi

end IPPSPACE

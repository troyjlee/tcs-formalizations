/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineReadFP
import IPPSPACE.QBF.TapeTransitionFP
import IPPSPACE.QBF.ConfigurationValidityFP
import IPPSPACE.QBF.ConfigurationAcceptanceFP
import IPPSPACE.QBF.MachineReduction

/-!
# Polynomial-time construction of machine transition templates

Certificates for the exact finite transition table and its validity guards use
upstream's actual machine-based `FP`. The machine is fixed: only input strings,
space bounds, and offsets vary. This does not yet certify the recursive
reachability construction or prenex conversion.
-/

namespace IPPSPACE

open Complexity

/-- A fixed finite list of uniformly FP formula constructors can be conjoined. -/
theorem encodeQBF_qbfAll_fixed_mem_FP {α : Type} (entries : List α)
    {body : α → List Bool → QBF}
    (hbody : ∀ a, (fun z => encodeQBF (body a z)) ∈ FP) :
    (fun z => encodeQBF (qbfAll (entries.map (fun a => body a z)))) ∈ FP := by
  induction entries with
  | nil => exact encodeQBF_tru_mem_FP
  | cons a entries ih => exact encodeQBF_conj_mem_FP (hbody a) ih

theorem encodeQBF_qbfAny_fixed_mem_FP {α : Type} (entries : List α)
    {body : α → List Bool → QBF}
    (hbody : ∀ a, (fun z => encodeQBF (body a z)) ∈ FP) :
    (fun z => encodeQBF (qbfAny (entries.map (fun a => body a z)))) ∈ FP := by
  induction entries with
  | nil => exact encodeQBF_fls_mem_FP
  | cons a entries ih => exact encodeQBF_disj_mem_FP (hbody a) ih

theorem encodeQBF_qbfAllFin_fixed_mem_FP (count : ℕ) {body : Fin count → List Bool → QBF}
    (hbody : ∀ i, (fun z => encodeQBF (body i z)) ∈ FP) :
    (fun z => encodeQBF (qbfAllFin count (fun i => body i z))) ∈ FP := by
  simpa only [qbfAllFin, List.map_ofFn, Function.comp_def] using
    encodeQBF_qbfAll_fixed_mem_FP (List.ofFn (fun i : Fin count => i)) hbody

theorem encodeQBF_qbfAnyFin_fixed_mem_FP (count : ℕ) {body : Fin count → List Bool → QBF}
    (hbody : ∀ i, (fun z => encodeQBF (body i z)) ∈ FP) :
    (fun z => encodeQBF (qbfAnyFin count (fun i => body i z))) ∈ FP := by
  simpa only [qbfAnyFin, List.map_ofFn, Function.comp_def] using
    encodeQBF_qbfAny_fixed_mem_FP (List.ofFn (fun i : Fin count => i)) hbody

/-- The packed work-tape subblock has a polynomial arithmetic offset. -/
theorem machineWorkTapeNames_blockNames (states tapes inputLength space start : ℕ)
    (tape : Fin tapes) :
    machineWorkTapeNames states tapes inputLength space tape
      (blockNames start (configurationWidth states tapes inputLength space)) =
      blockNames (start + states + (inputLength + space + 2) +
        (space + 1 + (space + 1) * 2) * tape.val) (space + 1 + (space + 1) * 2) := by
  funext i
  change start + (configurationWorkIndex states tapes inputLength space
    (finProdFinEquiv (tape, i))).val = _
  change start + (states + (inputLength + space + 2 +
    (i.val + configurationTapeWidth (space + 1) * tape.val))) = _
  dsimp [configurationTapeWidth, blockNames]
  ring

theorem machineOutputTapeNames_blockNames (states tapes inputLength space start : ℕ) :
    machineOutputTapeNames states tapes inputLength space
      (blockNames start (configurationWidth states tapes inputLength space)) =
      blockNames (start + states + (inputLength + space + 2) +
        tapes * (space + 1 + (space + 1) * 2)) (space + 2 + (space + 2) * 2) := by
  funext i
  change start + (configurationOutputIndex states tapes inputLength space i).val = _
  change start + (states + (inputLength + space + 2 +
    (tapes * configurationTapeWidth (space + 1) + i.val))) = _
  dsimp [configurationTapeWidth, blockNames]
  ring

theorem encode_machineWorkTapeTransitionFormula_mem_FP (states tapes : ℕ)
    (symbol : Γ) (direction : Dir3) (tape : Fin tapes)
    {inputLength space beforeStart afterStart : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineWorkTapeTransitionFormula symbol direction tape
      (blockNames (beforeStart z) (configurationWidth states tapes (inputLength z) (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have hw := hs.add (UnaryFn.const 1)
  have hoff := ((UnaryFn.const states).add ((hn.add hs).add (UnaryFn.const 2))).add
    ((hw.add (hw.mul (UnaryFn.const 2))).mul (UnaryFn.const tape.val))
  have h := encode_machineTapeTransitionFormula_contiguous_mem_FP symbol direction hw
    (hb.add hoff) (ha.add hoff)
  simpa only [machineWorkTapeTransitionFormula, machineWorkTapeNames_blockNames, Nat.add_assoc] using h

theorem encode_machineOutputTapeTransitionFormula_mem_FP (states tapes : ℕ)
    (symbol : Γ) (direction : Dir3)
    {inputLength space beforeStart afterStart : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineOutputTapeTransitionFormula symbol direction
      (blockNames (beforeStart z) (configurationWidth states tapes (inputLength z) (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have hw := hs.add (UnaryFn.const 1)
  have hoff := ((UnaryFn.const states).add ((hn.add hs).add (UnaryFn.const 2))).add
    ((UnaryFn.const tapes).mul (hw.add (hw.mul (UnaryFn.const 2))))
  have h := encode_machineTapeTransitionFormula_contiguous_mem_FP symbol direction
    (hs.add (UnaryFn.const 2)) (hb.add hoff) (ha.add hoff)
  simpa only [machineOutputTapeTransitionFormula, machineOutputTapeNames_blockNames, Nat.add_assoc] using h

/-- The width arithmetic of a fixed machine configuration is polynomial-time. -/
theorem configurationWidth_unaryFn (states tapes : ℕ)
    {inputLength space : List Bool → ℕ} (hn : UnaryFn inputLength) (hs : UnaryFn space) :
    UnaryFn fun z => configurationWidth states tapes (inputLength z) (space z) :=
  ((((UnaryFn.const (3 * tapes + 4)).mul hs).add hn).add
    (UnaryFn.const (states + 3 * tapes + 8))).of_eq fun _ =>
      (configurationWidth_eq _ _ _ _).symm

/-- The complete accepting-state template includes its exact-image validity guard. -/
theorem encode_machineGuardedAcceptance_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {inputLength space : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space) :
    (fun z => encodeQBF (machineGuardedAcceptance tm stateNumber (inputLength z) (space z))) ∈ FP := by
  have hv := encode_configurationValidityFormula_mem_FP stateNumber machineSymbolBits tapes
    hn hs (UnaryFn.const 0)
  have ha := encode_machineAcceptanceFormula_mem_FP stateNumber tm.qhalt tapes
    hn hs (UnaryFn.const 0)
  have hzero (width : ℕ) : blockNames 0 width = Fin.val := by
    funext i
    exact Nat.zero_add i.val
  simpa only [machineGuardedAcceptance, guardedAcceptance, configurationValidityFormula,
    hzero, Nat.zero_add] using encodeQBF_conj_mem_FP hv ha

/-- Every command of a fixed machine emits an FP transition formula. -/
theorem encode_machineCommandFormula_mem_FP {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (command : MachineCommand Q tapes)
    {inputLength space beforeStart afterStart : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineCommandFormula stateNumber (inputLength z) (space z) command
      (blockNames (beforeStart z) (configurationWidth states tapes (inputLength z) (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have hstate := encode_machineStateFormula_contiguous_mem_FP stateNumber tapes command.1
    (inputLength := inputLength) (space := space) ha
  have hinput := encode_machineInputHeadMoveFormula_contiguous_mem_FP states tapes
    command.2.2.2.1 hn hs hb ha
  have hwork := encodeQBF_qbfAllFin_fixed_mem_FP tapes (fun t =>
    encode_machineWorkTapeTransitionFormula_mem_FP states tapes (command.2.1 t)
      (command.2.2.2.2.1 t) t hn hs hb ha)
  have hout := encode_machineOutputTapeTransitionFormula_mem_FP states tapes
    command.2.2.1 command.2.2.2.2.2 hn hs hb ha
  exact encodeQBF_conj_mem_FP hstate (encodeQBF_conj_mem_FP hinput
    (encodeQBF_conj_mem_FP hwork (encodeQBF_conj_mem_FP hout encodeQBF_tru_mem_FP)))

/-- A fixed state/read-table branch, with the actual machine's halt rejection. -/
theorem encode_machineTransitionBranch_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (state : Fin states) (read : MachineReadCase tapes)
    {input : List Bool → List Bool} {space beforeStart afterStart : List Bool → ℕ}
    (hinput : input ∈ FP) (hs : UnaryFn space)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineTransitionBranch tm stateNumber (input z) (space z)
      (blockNames (beforeStart z) (configurationWidth states tapes (input z).length (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (input z).length (space z)))
      state read)) ∈ FP := by
  by_cases hhalt : stateNumber.symm state = tm.qhalt
  · simpa only [machineTransitionBranch, hhalt, ite_true] using encodeQBF_fls_mem_FP
  · have hn := UnaryFn.length hinput
    have hstate := encode_machineStateFormula_contiguous_mem_FP stateNumber tapes
      (stateNumber.symm state) (inputLength := fun z => (input z).length) (space := space) hb
    have hin := encode_machineInputReadFormula_contiguous_mem_FP states tapes read.1 hinput hs hb
    have hwork := encodeQBF_qbfAllFin_fixed_mem_FP tapes (fun t =>
      encode_machineWorkReadFormula_contiguous_mem_FP states (read.2.1 t) t hn hs hb)
    have hout := encode_machineOutputReadFormula_contiguous_mem_FP states tapes read.2.2 hn hs hb
    have hcmd := encode_machineCommandFormula_mem_FP stateNumber
      (tm.δ (stateNumber.symm state) read.1 read.2.1 read.2.2) hn hs hb ha
    simpa only [machineTransitionBranch, hhalt, ite_false, qbfAll] using
      encodeQBF_conj_mem_FP hstate (encodeQBF_conj_mem_FP hin
        (encodeQBF_conj_mem_FP hwork (encodeQBF_conj_mem_FP hout
          (encodeQBF_conj_mem_FP hcmd encodeQBF_tru_mem_FP))))

/-- The entire fixed control/read table is constructible in actual upstream FP.
Neither tape contents nor complete configurations are enumerated. -/
theorem encode_machineTransitionFormula_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states)
    {input : List Bool → List Bool} {space beforeStart afterStart : List Bool → ℕ}
    (hinput : input ∈ FP) (hs : UnaryFn space)
    (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineTransitionFormula tm stateNumber (input z) (space z)
      (blockNames (beforeStart z) (configurationWidth states tapes (input z).length (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (input z).length (space z))))) ∈ FP :=
  encodeQBF_qbfAnyFin_fixed_mem_FP states fun state =>
    encodeQBF_qbfAny_fixed_mem_FP (machineReadCases tapes) fun read =>
      encode_machineTransitionBranch_mem_FP tm stateNumber state read hinput hs hb ha

/-- The complete encoded guarded edge used by `encodeMachineAcceptance` is
polynomial-time, uniformly in the actual input and any unary FP space budget. -/
theorem encode_machineGuardedEdge_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {input : List Bool → List Bool} {space : List Bool → ℕ}
    (hinput : input ∈ FP) (hs : UnaryFn space) :
    (fun z => encodeQBF (machineGuardedEdge tm stateNumber (input z) (space z))) ∈ FP := by
  have hn := UnaryFn.length hinput
  have hw := configurationWidth_unaryFn states tapes hn hs
  have hbefore := encode_configurationValidityFormula_mem_FP stateNumber machineSymbolBits tapes
    hn hs (UnaryFn.const 0)
  have hafter := encode_configurationValidityFormula_mem_FP stateNumber machineSymbolBits tapes hn hs hw
  have htable := encode_machineTransitionFormula_mem_FP tm stateNumber hinput hs (UnaryFn.const 0) hw
  have hzero (width : ℕ) : blockNames 0 width = Fin.val := by
    funext i
    exact Nat.zero_add i.val
  apply mem_FP_of_eq (encodeQBF_conj_mem_FP hbefore (encodeQBF_conj_mem_FP hafter htable))
  intro z
  simp only [machineGuardedEdge, guardedEdge, machineEdgeTemplate, configurationValidityFormula,
    hzero]
  rfl

end IPPSPACE

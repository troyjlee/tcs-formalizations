/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.EncodingFP
import IPPSPACE.QBF.MachineAcceptance

/-!
# Polynomial-time construction of the actual acceptance test

The exact halt-state and output-cell test uses polynomial-time numeric offsets
within a configuration block. The resulting certificate is in upstream `FP`,
including the binary names and syntax tags. Endpoint validity and the complete
transition/reachability construction need their own certificates.
-/

namespace IPPSPACE

open Complexity

theorem encode_machineAcceptanceFormula_mem_FP {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (halt : Q) (tapes : ℕ)
    {inputLength space start : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space) (hstart : UnaryFn start) :
    (fun z => encodeQBF (machineAcceptanceFormula stateNumber halt tapes (inputLength z) (space z)
      (fun i => start z + i.val))) ∈ FP := by
  have hstate : UnaryFn fun z => start z +
      (configurationStateIndex states tapes (inputLength z) (space z) (stateNumber halt)).val :=
    hstart.add (UnaryFn.const (stateNumber halt).val)
  have hcell (b : Fin 2) : UnaryFn fun z => start z +
      (configurationOutputCellIndex states tapes (inputLength z) (space z)
        (configurationVerdictCell (space z)) b).val := by
    have h := hstart.add ((((((UnaryFn.const states).add
      ((hn.add hs).add (UnaryFn.const 2))).add
      ((UnaryFn.const (3 * tapes)).mul (hs.add (UnaryFn.const 1)))).add
      (hs.add (UnaryFn.const 2))).add (UnaryFn.const 2)).add (UnaryFn.const b.val))
    exact h.of_eq (fun z => by simp [configurationVerdictCell])
  exact encodeQBF_conj_mem_FP (encodeQBF_var_mem_FP hstate)
    (encodeQBF_conj_mem_FP
      (encodeQBF_bitValue_mem_FP (hcell 0) (FPPred.const (machineSymbolBits Γ.one 0 = true)))
      (encodeQBF_bitValue_mem_FP (hcell 1) (FPPred.const (machineSymbolBits Γ.one 1 = true))))

/-- The actual machine acceptance template is uniformly constructible from a
polynomial-time space budget and the original input's length. -/
theorem encode_machineAcceptanceTemplate_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {space : List Bool → ℕ} (hs : UnaryFn space) :
    (fun input => encodeQBF
      (machineAcceptanceFormula stateNumber tm.qhalt tapes input.length (space input) Fin.val)) ∈ FP := by
  simpa only [Nat.zero_add] using encode_machineAcceptanceFormula_mem_FP
    stateNumber tm.qhalt tapes unaryLength_mem_FP hs (UnaryFn.const 0)

end IPPSPACE

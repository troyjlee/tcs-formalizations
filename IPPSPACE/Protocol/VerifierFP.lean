/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.VerifierMessageFP
import IPPSPACE.Protocol.ReplayFP
import Complexitylib.Classes.P.Preimage
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Complete runtime certificates for the encoded prenex verifier

The existing packed message computation belongs to actual upstream FP, and the
existing packed verdict language belongs to actual upstream P. All malformed
view encodings retain their original rejection behavior. This certifies the
verifier on closed prenex inputs; arbitrary QBF prenex-conversion runtime and
construction of the named upstream interactive protocol remain separate.
-/

namespace IPPSPACE

open Complexity

theorem viewTranscriptVerdict_mem_FP : (fun bits => [viewTranscriptVerdict bits]) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hraw := decodedTranscriptVerdict_mem_FP upstreamViewInput_mem_FP
    upstreamViewCoins_mem_FP upstreamViewTranscriptBits_mem_FP
  apply mem_FP_of_eq ((decodeProtocolView_success_fppred hid).ite_mem_FP hraw (constFn_mem_FP [false]))
  intro bits
  cases hd : decodeProtocolView bits with
  | none => simp [viewTranscriptVerdict, packViewVerdict, hd]
  | some view =>
    have hi := upstreamViewInput_of_decode bits view hd
    have hc := upstreamViewCoins_of_decode bits view hd
    have ht := upstreamViewTranscriptBits_of_decode bits view hd
    simp only [id_eq, hd, Option.isSome_some, ↓reduceIte, hi, hc, ht,
      decodedTranscriptVerdict, decodeViewTranscript_bitstringEncode,
      viewTranscriptVerdict, packViewVerdict]

/-- A one-bit FP verdict yields an actual P decider. The imported finite-state
scanner reads the final output bit in linear time, and upstream preprocessing
closure composes it with the given FP machine. -/
theorem booleanVerdict_mem_P {verdict : List Bool → Bool}
    (h : (fun bits => [verdict bits]) ∈ FP) : {bits | verdict bits = true} ∈ P := by
  let lastTrue : Language := {bits | bits.foldl (fun _ bit => bit) false = true}
  have hlast : lastTrue ∈ P := by
    apply mem_P_iff_decidesInTime_polynomial.mpr
    refine ⟨0, TM.scannerTM false (fun _ bit => bit) (fun bit => if bit then Γw.one else Γw.zero),
      Polynomial.X + Polynomial.C 2, ?_⟩
    have hscan := TM.scannerTM_decidesInTime (S := Bool) false (fun _ bit => bit) id
      (L := lastTrue) (fun bits => Iff.rfl)
    simpa using hscan
  have hpre := mem_P_preimage h hlast
  have heq : (fun bits => [verdict bits]) ⁻¹' lastTrue = {bits | verdict bits = true} := by
    ext bits
    simp [lastTrue]
  rw [heq] at hpre
  exact hpre

/-- The exact packed final verdict meets the upstream polynomial-time language
interface, with no hypothesis about the input or transcript. -/
theorem viewTranscriptVerdict_mem_P : {bits | viewTranscriptVerdict bits = true} ∈ P :=
  booleanVerdict_mem_P viewTranscriptVerdict_mem_FP

theorem prenexVerifier_runtime :
    viewVerifierMessage ∈ FP ∧ {bits | viewTranscriptVerdict bits = true} ∈ P :=
  ⟨viewVerifierMessage_mem_FP, viewTranscriptVerdict_mem_P⟩

end IPPSPACE

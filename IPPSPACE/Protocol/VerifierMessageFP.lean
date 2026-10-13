/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.CoinAccessFP
import IPPSPACE.Protocol.TranscriptParsingFP

/-!
# The complete encoded outgoing verifier message is polynomial-time

This theorem certifies the existing `viewVerifierMessage` on every encoded view,
including malformed views, wrong-length private tapes, and unreachable histories.
It composes full view validation, exact transcript counting, closed-prenex syntax
validation, operator counts, and private challenge sampling. The outgoing message
continues to reveal only the preceding real-round challenge.
-/

namespace IPPSPACE

open Complexity

theorem viewVerifierMessage_mem_FP : viewVerifierMessage ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hcount := decodeViewTranscript_length_unaryFn upstreamViewTranscriptBits_mem_FP
  have hmessage := verifierMessageAtCount_mem_FP upstreamViewInput_mem_FP
    upstreamViewCoins_mem_FP hcount
  apply mem_FP_of_eq ((decodeProtocolView_success_fppred hid).ite_mem_FP hmessage (constFn_mem_FP []))
  intro bits
  cases hd : decodeProtocolView bits with
  | none => simp [viewVerifierMessage, packViewMessage, hd]
  | some view =>
    have hi := upstreamViewInput_of_decode bits view hd
    have hc := upstreamViewCoins_of_decode bits view hd
    have ht := upstreamViewTranscriptBits_of_decode bits view hd
    simpa only [id_eq, hd, Option.isSome_some, ↓reduceIte, hi, hc, ht,
      decodeViewTranscript_bitstringEncode, Option.map_some, Option.getD_some,
      viewVerifierMessage, packViewMessage] using
      verifierMessageAtCount_eq view.input view.coins view.transcript

/-- Composition with any already polynomial-time producer of a packed view. -/
theorem viewVerifierMessage_comp_mem_FP {view : List Bool → List Bool} (hview : view ∈ FP) :
    (fun z => viewVerifierMessage (view z)) ∈ FP :=
  mem_FP_comp hview viewVerifierMessage_mem_FP

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexReductionFP
import IPPSPACE.Protocol.VerifierFP

/-!
# Runtime certificates for the original closed-QBF verifier

The existing reduction is composed with the existing packed prenex verifier.
The original source-history length guard is retained, and only the prescribed
target-history prefix is passed to the final verdict. Malformed packed views
retain their original empty-message and false-verdict behavior.
-/

namespace IPPSPACE

open Complexity

private theorem prefix_flatMap_range (count : ℕ) (history : List (List Bool)) :
    (List.range (min count history.length)).flatMap
        (fun i => encodeViewMessage (history[i]?.getD [])) =
      (history.take count).flatMap encodeViewMessage := by
  induction history generalizing count with
  | nil => simp
  | cons message history ih =>
    cases count with
    | zero => simp
    | succ count =>
      have hm : min (count + 1) (history.length + 1) = min count history.length + 1 := by omega
      rw [List.length_cons, hm]
      simp only [List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map, List.getElem?_cons_zero, Option.getD_some,
        List.getElem?_cons_succ, List.take_succ_cons]
      rw [ih]

/-- Reconstruct a prefix from validated indexed access. A malformed transcript
has count zero and produces the canonical empty transcript; callers that need
rejection retain the full-decoder guard. -/
def viewTranscriptPrefixBits (count : ℕ) (bits : List Bool) : List Bool :=
  false :: ((List.range (min count (viewTranscriptCount bits))).flatMap
    (fun i => encodeViewMessage (viewTranscriptMessage i bits)) ++ [true])

@[simp] theorem viewTranscriptPrefixBits_encode (count : ℕ) (history : List (List Bool)) :
    viewTranscriptPrefixBits count (encodeViewTranscript history) =
      encodeViewTranscript (history.take count) := by
  unfold viewTranscriptPrefixBits
  rw [viewTranscriptCount_encode]
  simp only [viewTranscriptMessage_encode]
  rw [prefix_flatMap_range]
  rfl

theorem viewTranscriptPrefixBits_mem_FP {count : List Bool → ℕ} {bits : List Bool → List Bool}
    (hc : UnaryFn count) (hb : bits ∈ FP) :
    (fun z => viewTranscriptPrefixBits (count z) (bits z)) ∈ FP := by
  have hentry := mem_FP_comp
    (viewTranscriptMessage_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hb))
    encodeViewMessage_mem_FP
  have hlist := flatMap_range_mem_FP hentry (hc.min (viewTranscriptCount_unaryFn hb)).mem_FP
  have h := mem_FP_comp (Cobham.appendFn_mem_FP hlist (constFn_mem_FP [true]))
    (Cobham.cons_mem_FP false)
  apply mem_FP_of_eq h
  intro z
  simp only [viewTranscriptPrefixBits, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate]

@[simp] theorem packEncodedView_encodeViewTranscript (input coins : List Bool)
    (history : List (List Bool)) :
    packEncodedView input coins (encodeViewTranscript history) = encodeProtocolView input coins history := rfl

/-- The original arbitrary-QBF outgoing message has an actual upstream FP
certificate on every packed string, with its full malformed-view guard. -/
theorem reducedViewVerifierMessage_mem_FP : reducedViewVerifierMessage ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hinput := prenexReduction_comp_mem_FP upstreamViewInput_mem_FP
  have hview := packEncodedView_mem_FP hinput upstreamViewCoins_mem_FP upstreamViewTranscriptBits_mem_FP
  have hmessage := mem_FP_comp hview viewVerifierMessage_mem_FP
  apply mem_FP_of_eq ((decodeProtocolView_success_fppred hid).ite_mem_FP hmessage (constFn_mem_FP []))
  intro bits
  cases hd : decodeProtocolView bits with
  | none => simp [reducedViewVerifierMessage, packViewMessage, hd]
  | some view =>
    have hi := upstreamViewInput_of_decode bits view hd
    have hc := upstreamViewCoins_of_decode bits view hd
    have ht : upstreamViewTranscriptBits bits = encodeViewTranscript view.transcript := by
      simpa only [encodeViewTranscript_eq_bitstringEncode] using upstreamViewTranscriptBits_of_decode bits view hd
    simp only [id_eq, hd, Option.isSome_some, ↓reduceIte, Function.comp_apply, hi, hc, ht,
      packEncodedView_encodeViewTranscript, viewVerifierMessage_encode,
      reducedViewVerifierMessage, packViewMessage, reducedRawVerifierMessage]

/-- The exact original verdict, including source-round padding, target-prefix
replay, and rejection of every malformed packed view, is an FP Boolean function. -/
theorem reducedViewTranscriptVerdict_mem_FP :
    (fun bits => [reducedViewTranscriptVerdict bits]) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hinput := prenexReduction_comp_mem_FP upstreamViewInput_mem_FP
  have htargetCount := (UnaryFn.const 2).mul (encodedRoundBudget_unaryFn.comp hinput)
  have hprefix := viewTranscriptPrefixBits_mem_FP htargetCount upstreamViewTranscriptBits_mem_FP
  have hview := packEncodedView_mem_FP hinput upstreamViewCoins_mem_FP hprefix
  have hverdict := mem_FP_comp hview viewTranscriptVerdict_mem_FP
  have hsourceCount := (UnaryFn.const 2).mul (reducedRoundBudget_unaryFn.comp upstreamViewInput_mem_FP)
  have hguard := (decodeProtocolView_success_fppred hid).and
    (FPPred.eq (viewTranscriptCount_unaryFn upstreamViewTranscriptBits_mem_FP) hsourceCount)
  apply mem_FP_of_eq (hguard.ite_mem_FP hverdict (constFn_mem_FP [false]))
  intro bits
  cases hd : decodeProtocolView bits with
  | none => simp [reducedViewTranscriptVerdict, packViewVerdict, hd]
  | some view =>
    have hi := upstreamViewInput_of_decode bits view hd
    have hc := upstreamViewCoins_of_decode bits view hd
    have ht : upstreamViewTranscriptBits bits = encodeViewTranscript view.transcript := by
      simpa only [encodeViewTranscript_eq_bitstringEncode] using upstreamViewTranscriptBits_of_decode bits view hd
    simp only [id_eq, hd, Option.isSome_some, true_and, Function.comp_apply, hi, hc, ht,
      viewTranscriptCount_encode, viewTranscriptPrefixBits_encode,
      packEncodedView_encodeViewTranscript, viewTranscriptVerdict_encode,
      reducedViewTranscriptVerdict, packViewVerdict, reducedRawTranscriptVerdict]
    split <;> rfl

/-- The actual upstream polynomial-time language interface for the complete
closed-QBF verdict, without restrictions on input or transcript strings. -/
theorem reducedViewTranscriptVerdict_mem_P : {bits | reducedViewTranscriptVerdict bits = true} ∈ P :=
  booleanVerdict_mem_P reducedViewTranscriptVerdict_mem_FP

theorem closedQBFVerifier_runtime :
    reducedViewVerifierMessage ∈ FP ∧ {bits | reducedViewTranscriptVerdict bits = true} ∈ P :=
  ⟨reducedViewVerifierMessage_mem_FP, reducedViewTranscriptVerdict_mem_P⟩

end IPPSPACE

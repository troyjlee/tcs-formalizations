/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Fin.Tuple.Take
import Complexitylib.Classes.Interactive
import Complexitylib.Classes.Containments
import IPPSPACE.Protocol.ReducedVerifierFP
import IPPSPACE.Protocol.EventPadding

/-!
# Interactive proofs are closed under polynomial-time preimages

Resource polynomials are composed with a polynomial bound on the reduction's
output length. Extra rounds and coins are ignored. The final verdict checks the
target message bound on its replay prefix: this is necessary because the padded
source message budget can exceed the target budget. An accepted transcript then
agrees with a globally clipped strategy, to which upstream soundness applies.
-/

namespace IPPSPACE

open Complexity

/-- Every message in a finite transcript satisfies the specified bound. -/
def TranscriptBounded (bound : ℕ) (history : Transcript) : Prop :=
  ∀ message ∈ history, message.length ≤ bound

theorem transcriptBounded_take_iff (bound count : ℕ) (history : Transcript) :
    TranscriptBounded bound (history.take count) ↔
      ∀ i < count, (history[i]?.getD []).length ≤ bound := by
  induction history generalizing count with
  | nil => simp [TranscriptBounded]
  | cons message history ih =>
    cases count with
    | zero => simp [TranscriptBounded]
    | succ count =>
      rw [Nat.forall_lt_succ_left]
      simpa [TranscriptBounded, List.getElem?_cons_succ] using
        and_congr Iff.rfl (ih count)

/-- Check all messages in a bounded transcript prefix using the exact parser. -/
def transcriptPrefixBounded (bound count : ℕ) (bits : List Bool) : Prop :=
  ∀ i < count, (viewTranscriptMessage i bits).length ≤ bound

theorem transcriptPrefixBounded_fppred {bound count : List Bool → ℕ}
    {bits : List Bool → List Bool} (hb : UnaryFn bound) (hc : UnaryFn count) (hs : bits ∈ FP) :
    FPPred fun z => transcriptPrefixBounded (bound z) (count z) (bits z) := by
  have he := viewTranscriptMessage_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hs)
  exact (FPPred.forall_lt hc (FPPred.le (UnaryFn.length he) hb.lift)).of_iff
    (fun z => by simp only [transcriptPrefixBounded, pairFst_pair, pairSnd_pair,
      List.length_replicate, Function.comp_apply, pairFst_pair])

@[simp] theorem transcriptPrefixBounded_encode (bound count : ℕ) (history : Transcript) :
    transcriptPrefixBounded bound count (encodeViewTranscript history) ↔
      TranscriptBounded bound (history.take count) := by
  simp only [transcriptPrefixBounded, viewTranscriptMessage_encode]
  exact (transcriptBounded_take_iff bound count history).symm

/-- Clipping yields a globally bounded strategy even from an arbitrary prover. -/
def clipProver (bound : ℕ) (strategy : Complexity.ProverStrategy) : Complexity.ProverStrategy :=
  fun history => (strategy history).take bound

theorem clipProver_bounded (bound : ℕ) (strategy : Complexity.ProverStrategy) :
    (clipProver bound strategy).Bounded bound := by
  intro history
  exact List.length_take_le _ _

theorem protocol_transcript_eq_interaction (prot : Protocol) (strategy : Complexity.ProverStrategy)
    (input coins : List Bool) (rounds : ℕ) :
    prot.transcript strategy input coins rounds =
      interactionTranscript strategy (fun history => prot.vmsg (protocolView input coins history)) rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp only [Protocol.transcript, interactionTranscript, ih, Protocol.view]

theorem protocol_transcript_take (prot : Protocol) (strategy : Complexity.ProverStrategy)
    (input coins : List Bool) (rounds total : ℕ) (h : rounds ≤ total) :
    (prot.transcript strategy input coins total).take (2 * rounds) =
      prot.transcript strategy input coins rounds := by
  simp only [protocol_transcript_eq_interaction]
  exact interactionTranscript_take _ _ _ _ h

theorem protocol_transcript_bounded (prot : Protocol) (strategy : Complexity.ProverStrategy)
    (input coins : List Bool) (hstrategy : strategy.Bounded (prot.msgLen input.length))
    (rounds : ℕ) :
    TranscriptBounded (prot.msgLen input.length) (prot.transcript strategy input coins rounds) := by
  induction rounds with
  | zero => simp [Protocol.transcript, TranscriptBounded]
  | succ rounds ih =>
    intro message hmessage
    simp only [Protocol.transcript, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hmessage
    rcases hmessage with hmessage | rfl | rfl
    · exact ih message hmessage
    · exact prot.vmsg_len input coins _
    · exact hstrategy _

/-- On a transcript whose actual messages fit the target budget, clipping the
strategy changes no message in that transcript. -/
theorem protocol_transcript_clip (prot : Protocol) (strategy : Complexity.ProverStrategy)
    (input coins : List Bool) (bound rounds : ℕ)
    (h : TranscriptBounded bound (prot.transcript strategy input coins rounds)) :
    prot.transcript (clipProver bound strategy) input coins rounds =
      prot.transcript strategy input coins rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    have hprev : TranscriptBounded bound (prot.transcript strategy input coins rounds) := by
      intro message hm
      exact h message (List.mem_append_left _ hm)
    rw [Protocol.transcript, ih hprev]
    have hreply := h (strategy (prot.transcript strategy input coins rounds ++
      [prot.vmsg (Protocol.view input coins (prot.transcript strategy input coins rounds))]))
      (by simp [Protocol.transcript])
    simp only [clipProver, List.take_of_length_le hreply]
    rfl

/-- Total view transformation for the next message. Only the target's coin
prefix is visible to its verifier; all names and input bits remain unchanged. -/
def reductionMessageView (f : List Bool → List Bool) (cp : Polynomial ℕ)
    (bits : List Bool) : List Bool :=
  let input := f (upstreamViewInput bits)
  packEncodedView input ((upstreamViewCoins bits).take (cp.eval input.length))
    (upstreamViewTranscriptBits bits)

/-- Total view transformation for the final verdict: discard padded rounds. -/
def reductionVerdictView (f : List Bool → List Bool) (rp cp : Polynomial ℕ)
    (bits : List Bool) : List Bool :=
  let input := f (upstreamViewInput bits)
  packEncodedView input ((upstreamViewCoins bits).take (cp.eval input.length))
    (viewTranscriptPrefixBits (2 * rp.eval input.length) (upstreamViewTranscriptBits bits))

def reductionMessageGuard (f : List Bool → List Bool) (rp mp : Polynomial ℕ)
    (bits : List Bool) : Prop :=
  let input := f (upstreamViewInput bits)
  transcriptPrefixBounded (mp.eval input.length) (2 * rp.eval input.length)
    (upstreamViewTranscriptBits bits)

theorem reductionMessageView_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP)
    (cp : Polynomial ℕ) : reductionMessageView f cp ∈ FP := by
  have hi := mem_FP_comp upstreamViewInput_mem_FP hf
  exact packEncodedView_mem_FP hi
    (take_mem_FP upstreamViewCoins_mem_FP (polynomial_eval_unaryFn cp (UnaryFn.length hi)))
    upstreamViewTranscriptBits_mem_FP

theorem reductionVerdictView_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP)
    (rp cp : Polynomial ℕ) : reductionVerdictView f rp cp ∈ FP := by
  have hi := mem_FP_comp upstreamViewInput_mem_FP hf
  exact packEncodedView_mem_FP hi
    (take_mem_FP upstreamViewCoins_mem_FP (polynomial_eval_unaryFn cp (UnaryFn.length hi)))
    (viewTranscriptPrefixBits_mem_FP
      ((UnaryFn.const 2).mul (polynomial_eval_unaryFn rp (UnaryFn.length hi)))
      upstreamViewTranscriptBits_mem_FP)

theorem reductionMessageGuard_fppred {f : List Bool → List Bool} (hf : f ∈ FP)
    (rp mp : Polynomial ℕ) : FPPred (reductionMessageGuard f rp mp) := by
  have hi := mem_FP_comp upstreamViewInput_mem_FP hf
  exact transcriptPrefixBounded_fppred (polynomial_eval_unaryFn mp (UnaryFn.length hi))
    ((UnaryFn.const 2).mul (polynomial_eval_unaryFn rp (UnaryFn.length hi)))
    upstreamViewTranscriptBits_mem_FP

private theorem fppred_language_mem_P {predicate : List Bool → Prop} (hp : FPPred predicate) :
    {bits | predicate bits} ∈ P := by
  classical
  have h := booleanVerdict_mem_P hp.flag_mem_FP
  simpa only [decide_eq_true_eq] using h

private theorem protocolView_eq_local (input coins : List Bool) (history : Transcript) :
    protocolView input coins history = encodeProtocolView input coins history :=
  (encodeProtocolView_eq_upstream_encoding input coins history).symm

@[simp] theorem reductionMessageView_protocolView (f : List Bool → List Bool)
    (cp : Polynomial ℕ) (input coins : List Bool) (history : Transcript) :
    reductionMessageView f cp (protocolView input coins history) =
      protocolView (f input) (coins.take (cp.eval (f input).length)) history := by
  simp only [protocolView_eq_local]
  simp only [reductionMessageView, upstreamViewInput_encodeProtocolView,
    upstreamViewCoins_encodeProtocolView, upstreamViewTranscriptBits_encodeProtocolView,
    packEncodedView_bitstringEncode]

@[simp] theorem reductionVerdictView_protocolView (f : List Bool → List Bool)
    (rp cp : Polynomial ℕ) (input coins : List Bool) (history : Transcript) :
    reductionVerdictView f rp cp (protocolView input coins history) =
      protocolView (f input) (coins.take (cp.eval (f input).length))
        (history.take (2 * rp.eval (f input).length)) := by
  simp only [protocolView_eq_local]
  simp only [reductionVerdictView, upstreamViewInput_encodeProtocolView,
    upstreamViewCoins_encodeProtocolView, upstreamViewTranscriptBits_encodeProtocolView,
    ← encodeViewTranscript_eq_bitstringEncode, viewTranscriptPrefixBits_encode,
    packEncodedView_encodeViewTranscript]

@[simp] theorem reductionMessageGuard_protocolView (f : List Bool → List Bool)
    (rp mp : Polynomial ℕ) (input coins : List Bool) (history : Transcript) :
    reductionMessageGuard f rp mp (protocolView input coins history) ↔
      TranscriptBounded (mp.eval (f input).length) (history.take (2 * rp.eval (f input).length)) := by
  simp only [protocolView_eq_local]
  simp only [reductionMessageGuard, upstreamViewInput_encodeProtocolView,
    upstreamViewTranscriptBits_encodeProtocolView, ← encodeViewTranscript_eq_bitstringEncode,
    transcriptPrefixBounded_encode]

/-- The padded source protocol, with an explicit target-bound guard. -/
noncomputable def reductionProtocol (prot : Protocol) (rp cp mp P : Polynomial ℕ)
    (hm : ∀ n, prot.msgLen n = mp.eval n) (f : List Bool → List Bool) (hf : f ∈ FP)
    (hP : ∀ input, (f input).length ≤ P.eval input.length) : Protocol where
  rounds := (rp.comp P).eval
  coins := (cp.comp P).eval
  msgLen := (mp.comp P).eval
  vmsg := prot.vmsg ∘ reductionMessageView f cp
  vmsg_mem := mem_FP_comp (reductionMessageView_mem_FP hf cp) prot.vmsg_mem
  vmsg_len := by
    intro input coins history
    simp only [Function.comp_apply, reductionMessageView_protocolView, Polynomial.eval_comp]
    exact (prot.vmsg_len (f input) _ _).trans (by rw [hm]; exact polynomial_eval_mono_nat mp (hP input))
  verdict := (reductionVerdictView f rp cp) ⁻¹' prot.verdict ∩
    {bits | reductionMessageGuard f rp mp bits}
  verdict_mem := P_inter (mem_P_preimage (reductionVerdictView_mem_FP hf rp cp) prot.verdict_mem)
    (fppred_language_mem_P (reductionMessageGuard_fppred hf rp mp))


namespace ReductionProtocol

variable (prot : Protocol) (rp cp mp P : Polynomial ℕ)
  (hr : ∀ n, prot.rounds n = rp.eval n)
  (hc : ∀ n, prot.coins n = cp.eval n)
  (hm : ∀ n, prot.msgLen n = mp.eval n)
  (f : List Bool → List Bool) (hf : f ∈ FP)
  (hP : ∀ input, (f input).length ≤ P.eval input.length)

local notation "source" => reductionProtocol prot rp cp mp P hm f hf hP

theorem transcript_eq (strategy : Complexity.ProverStrategy) (input coins : List Bool) (rounds : ℕ) :
    (source).transcript strategy input coins rounds =
      prot.transcript strategy (f input) (coins.take (cp.eval (f input).length)) rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    simp only [Protocol.transcript]
    rw [ih]
    simp only [reductionProtocol, Function.comp_apply, Protocol.view, reductionMessageView_protocolView]

include hr in
theorem rounds_le (input : List Bool) : prot.rounds (f input).length ≤ (source).rounds input.length := by
  change prot.rounds (f input).length ≤ (rp.comp P).eval input.length
  rw [hr, Polynomial.eval_comp]
  exact polynomial_eval_mono_nat rp (hP input)

include hc in
theorem coins_le (input : List Bool) : prot.coins (f input).length ≤ (source).coins input.length := by
  change prot.coins (f input).length ≤ (cp.comp P).eval input.length
  rw [hc, Polynomial.eval_comp]
  exact polynomial_eval_mono_nat cp (hP input)

theorem messages_le (input : List Bool) : prot.msgLen (f input).length ≤ (source).msgLen input.length := by
  change prot.msgLen (f input).length ≤ (mp.comp P).eval input.length
  rw [hm, Polynomial.eval_comp]
  exact polynomial_eval_mono_nat mp (hP input)

include hr

theorem accepts_iff (strategy : Complexity.ProverStrategy) (input coins : List Bool) :
    (source).Accepts strategy input coins ↔
      prot.Accepts strategy (f input) (coins.take (cp.eval (f input).length)) ∧
      TranscriptBounded (prot.msgLen (f input).length)
        (prot.transcript strategy (f input) (coins.take (cp.eval (f input).length))
          (prot.rounds (f input).length)) := by
  change (reductionVerdictView f rp cp (protocolView input coins
    ((source).transcript strategy input coins ((source).rounds input.length))) ∈ prot.verdict ∧
    reductionMessageGuard f rp mp (protocolView input coins
      ((source).transcript strategy input coins ((source).rounds input.length)))) ↔ _
  rw [reductionVerdictView_protocolView, reductionMessageGuard_protocolView,
    transcript_eq, ← hr, protocol_transcript_take _ _ _ _ _ _
      (rounds_le prot rp cp mp P hr hm f hf hP input), ← hm]
  rfl

theorem accepts_of_target (strategy : Complexity.ProverStrategy) (input coins : List Bool)
    (hs : strategy.Bounded (prot.msgLen (f input).length)) :
    (source).Accepts strategy input coins ↔
      prot.Accepts strategy (f input) (coins.take (cp.eval (f input).length)) := by
  rw [accepts_iff prot rp cp mp P hr hm f hf hP]
  exact and_iff_left (protocol_transcript_bounded prot strategy _ _ hs _)

theorem accepts_implies_clipped (strategy : Complexity.ProverStrategy) (input coins : List Bool) :
    (source).Accepts strategy input coins →
      prot.Accepts (clipProver (prot.msgLen (f input).length) strategy) (f input)
        (coins.take (cp.eval (f input).length)) := by
  rw [accepts_iff prot rp cp mp P hr hm f hf hP]
  rintro ⟨ha, hb⟩
  unfold Protocol.Accepts at ha ⊢
  rw [protocol_transcript_clip _ _ _ _ _ _ hb]
  exact ha

end ReductionProtocol

private theorem bitString_take {n N : ℕ} (h : n ≤ N) (tape : Fin N → Bool) :
    (BitString.toList tape).take n = BitString.toList (fun i => tape (Fin.castLE h i)) := by
  exact (Fin.ofFn_take_eq_take_ofFn h tape).symm

/-- Actual upstream interactive proofs are closed under an arbitrary actual
upstream polynomial-time preimage. No bound on the reduction's numeric contents
is needed, only the output-length polynomial provided by FP itself. -/
theorem mem_IP_preimage {f : List Bool → List Bool} {language : Language}
    (hf : f ∈ FP) (hlanguage : language ∈ IP) : f ⁻¹' language ∈ IP := by
  classical
  obtain ⟨prot, rp, cp, mp, hr, hc, hm, hcomplete, hsound⟩ := hlanguage
  obtain ⟨P, hP⟩ := Cobham.output_length_poly_of_mem_FP hf
  let source := reductionProtocol prot rp cp mp P hm f hf hP
  refine ⟨source, rp.comp P, cp.comp P, mp.comp P,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro input hinput
    obtain ⟨strategy, hbounded, haccept⟩ := hcomplete (f input) hinput
    refine ⟨strategy, fun history => (hbounded history).trans
      (ReductionProtocol.messages_le prot rp cp mp P hm f hf hP input), ?_⟩
    have hcoins := ReductionProtocol.coins_le prot rp cp mp P hc hm f hf hP input
    have hevent : eventProb ((source).acceptEvent strategy input) =
        eventProb (prot.acceptEvent strategy (f input)) := by
      unfold Protocol.acceptEvent
      apply eventProb_bitTape_factor hcoins
      intro tape
      rw [ReductionProtocol.accepts_of_target prot rp cp mp P hr hm f hf hP strategy input _ hbounded]
      rw [← hc, bitString_take hcoins]
    rw [hevent]
    exact haccept
  · intro input hinput strategy _
    let clipped := clipProver (prot.msgLen (f input).length) strategy
    have hs := hsound (f input) hinput clipped (clipProver_bounded _ _)
    have hcoins := ReductionProtocol.coins_le prot rp cp mp P hc hm f hf hP input
    have hsub : (source).acceptEvent strategy input ⊆
        Finset.univ.filter (fun tape : Fin ((source).coins input.length) → Bool =>
          prot.Accepts clipped (f input)
            (BitString.toList (fun i => tape (Fin.castLE hcoins i)))) := by
      intro tape htape
      simp only [Protocol.acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and] at htape ⊢
      have ha := ReductionProtocol.accepts_implies_clipped prot rp cp mp P hr hm f hf hP
        strategy input (BitString.toList tape) htape
      rw [← hc, bitString_take hcoins] at ha
      exact ha
    calc
      eventProb ((source).acceptEvent strategy input) ≤ _ := eventProb_mono hsub
      _ = eventProb (prot.acceptEvent clipped (f input)) :=
        eventProb_bitTape_restrict hcoins (fun tape => prot.Accepts clipped (f input) (BitString.toList tape))
      _ ≤ 1 / 3 := hs

/-- Many-one reduction form of closure, using the actual FP and IP classes. -/
theorem mem_IP_of_FP_reduction {source target : Language} {f : List Bool → List Bool}
    (hf : f ∈ FP) (hreduce : ∀ input, input ∈ source ↔ f input ∈ target)
    (htarget : target ∈ IP) : source ∈ IP := by
  have heq : source = f ⁻¹' target := by ext input; exact hreduce input
  rw [heq]
  exact mem_IP_preimage hf htarget

end IPPSPACE

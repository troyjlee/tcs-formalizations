/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.EncodedProtocol

/-!
# Prover-free message and verdict functions with padded rounds

The verifier-message function sees only the input, private tape, and previous
alternating transcript. It sends an initial empty request, then the preceding
canonical residue, and empty requests after the real schedule. The verdict
replays the recorded prover replies using its own private tape. Neither verifier
function calls a prover oracle. The execution harness alone takes a strategy.

This is a semantic interface with explicit polynomial rounds and coins. It does
not assert `FP`/`P` membership or construct a substitute for upstream `Protocol`.
-/

namespace IPPSPACE

/-- Standard verifier-first interaction, for an arbitrary message procedure. -/
def interactionTranscript (S : List (List Bool) → List Bool)
    (vmsg : List (List Bool) → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | n + 1 =>
      let history := interactionTranscript S vmsg n
      let message := vmsg history
      history ++ [message, S (history ++ [message])]

theorem interactionTranscript_length (S : List (List Bool) → List Bool)
    (vmsg : List (List Bool) → List Bool) (n : ℕ) :
    (interactionTranscript S vmsg n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [interactionTranscript, ih, Nat.mul_add]

theorem interactionTranscript_eq_transcriptFromMessages
    (S : List (List Bool) → List Bool) (vmsg : List (List Bool) → List Bool)
    (messages : ℕ → List Bool)
    (hv : ∀ history, vmsg history = messages (history.length / 2)) (n : ℕ) :
    interactionTranscript S vmsg n = transcriptFromMessages S messages n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [interactionTranscript, ih, hv, transcriptFromMessages_length, transcriptFromMessages]

/-- Replay only the prover's odd-indexed entries; the supplied budget bounds
which transcript positions are inspected. -/
def transcriptReplies (n : ℕ) (history : List (List Bool)) : List (List Bool) :=
  (List.range n).map (fun j => history[2 * j + 1]?.getD [])

theorem transcriptFromMessages_reply (S : List (List Bool) → List Bool)
    (messages : ℕ → List Bool) (N j : ℕ) (hj : j < N) :
    (transcriptFromMessages S messages N)[2 * j + 1]? =
      some (S (transcriptFromMessages S messages j ++ [messages j])) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [transcriptFromMessages]
    by_cases hlt : j < N
    · rw [List.getElem?_append_left (by rw [transcriptFromMessages_length]; omega)]
      exact ih hlt
    · have heq : j = N := by omega
      subst j
      rw [List.getElem?_append_right (by rw [transcriptFromMessages_length]; omega),
        transcriptFromMessages_length]
      simp

theorem transcriptFromMessages_congr (S : List (List Bool) → List Bool)
    (left right : ℕ → List Bool) (n : ℕ) (h : ∀ i < n, left i = right i) :
    transcriptFromMessages S left n = transcriptFromMessages S right n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [transcriptFromMessages, transcriptFromMessages,
      ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Front decomposition of the already-visible challenge prefix. -/
theorem challengePrefix_succ_front (challenges : ℕ → List Bool) (n : ℕ) :
    challengePrefix challenges (n + 1) =
      challenges 0 :: challengePrefix (fun i => challenges (i + 1)) n := by
  simp [challengePrefix, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- The replies along one predetermined private-word path. This is used only
to connect a transcript to the existing adaptive strategy-tree semantics. -/
def strategyReplies (p : ℕ) :
    {n : ℕ} → MessageStrategy n → (ℕ → BitVec (residueWidth p)) → List (List Bool)
  | 0, _, _ => []
  | _ + 1, strategy, words =>
      strategy.1 :: strategyReplies p
        (strategy.2 (encodeMessage [sampleResidue p (words 0)])) (fun i => words (i + 1))

/-- Deterministically replay a finite list of replies with private tape words.
Missing replies reject; the schedule determines exactly how many are used. -/
def verifyReplyList (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ) :
    List AlgebraicOperator → FiniteClaim (ZMod p) → List (List Bool) →
      (ℕ → BitVec (residueWidth p)) → Bool
  | [], c, _, _ => decide (c.value = (terminal c.point).1)
  | _ :: _, _, [], _ => false
  | op :: ops, c, reply :: replies, words =>
      match parseMessage p (d + 1) reply with
      | none => false
      | some as =>
        if (checkRoundWithCost op d c as).1 then
          let r := sampleResidue p (words 0)
          verifyReplyList p d terminal ops (c.advanceWithCost op as r).1 replies
            (fun i => words (i + 1))
        else false

theorem verifyReplyList_strategyReplies (p d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) (strategy : MessageStrategy ops.length)
    (words : ℕ → BitVec (residueWidth p)) :
    verifyReplyList p d terminal ops c (strategyReplies p strategy words) words =
      verifyWordTape p d terminal ops c strategy (fun i => words i.val) := by
  induction ops generalizing c words with
  | nil => rfl
  | cons op ops ih =>
    simp only [strategyReplies, verifyReplyList, verifyWordTape, List.length_cons,
      verifyWordTapeCore]
    cases hparse : parseMessage p (d + 1) strategy.1 with
    | none => rfl
    | some as =>
      simp only
      by_cases hcheck : (checkRoundWithCost op d c as).1 = true
      · rw [ite_eq_left hcheck, ite_eq_left hcheck]
        exact ih _ _ _
      · rw [ite_eq_right hcheck, ite_eq_right hcheck]

theorem strategyReplies_unfoldTranscriptStrategy (p : ℕ)
    (S : List (List Bool) → List Bool) (n : ℕ) (history : List (List Bool))
    (words : ℕ → BitVec (residueWidth p)) :
    strategyReplies p (unfoldTranscriptStrategy S n history) words =
      (List.range n).map (fun j => S (pendingTranscript S history
        (challengePrefix (fun i => encodeMessage [sampleResidue p (words i)]) j))) := by
  induction n generalizing history words with
  | zero => rfl
  | succ n ih =>
    simp only [unfoldTranscriptStrategy, strategyReplies, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro j _
    rw [challengePrefix_succ_front]
    rfl

/-- The last private challenge is used only in the verdict; dummy rounds reveal
nothing further. -/
def paddedVerifierMessage (p n : ℕ) (words : ℕ → BitVec (residueWidth p))
    (round : ℕ) : List Bool :=
  if round < n then
    delayedVerifierMessage (fun i => encodeMessage [sampleResidue p (words i)]) round
  else []

@[simp] theorem paddedVerifierMessage_zero (p n : ℕ)
    (words : ℕ → BitVec (residueWidth p)) : paddedVerifierMessage p n words 0 = [] := by
  simp [paddedVerifierMessage, delayedVerifierMessage]

theorem paddedVerifierMessage_after (p n : ℕ) (words : ℕ → BitVec (residueWidth p))
    (round : ℕ) (h : n ≤ round) : paddedVerifierMessage p n words round = [] := by
  simp [paddedVerifierMessage, Nat.not_lt.mpr h]

/-- The current message depends only on earlier private words. -/
theorem paddedVerifierMessage_prefix_eq (p n round : ℕ)
    (left right : ℕ → BitVec (residueWidth p)) (h : ∀ i < round, left i = right i) :
    paddedVerifierMessage p n left round = paddedVerifierMessage p n right round := by
  by_cases hr : round < n
  · cases round with
    | zero => simp
    | succ round => simp [paddedVerifierMessage, hr, delayedVerifierMessage, h round (by omega)]
  · simp [paddedVerifierMessage, hr]

/-- The real-round replies in a longer padded transcript are exactly the
adaptive replies on the private challenge path. Dummy replies are excluded. -/
theorem transcriptReplies_padded (p n N : ℕ) (hN : n ≤ N)
    (S : List (List Bool) → List Bool) (words : ℕ → BitVec (residueWidth p)) :
    transcriptReplies n (transcriptFromMessages S (paddedVerifierMessage p n words) N) =
      strategyReplies p (unfoldTranscriptStrategy S n [[]]) words := by
  rw [strategyReplies_unfoldTranscriptStrategy, transcriptReplies]
  apply List.map_congr_left
  intro j hj
  have hjn := List.mem_range.mp hj
  rw [transcriptFromMessages_reply S _ N j (by omega), Option.getD_some,
    pendingTranscript_eq_transcriptFromMessages]
  have hmessages (i : ℕ) (hi : i < n) :
      paddedVerifierMessage p n words i =
        delayedVerifierMessage (fun i => encodeMessage [sampleResidue p (words i)]) i := by
    simp [paddedVerifierMessage, hi]
  rw [hmessages j hjn, transcriptFromMessages_congr S _ _ j
    (fun i hi => hmessages i (by omega))]


/-- Executable evaluation of the fixed round polynomial. -/
def encodedRoundBudget (input : List Bool) : ℕ := (input.length + 1) ^ 2

theorem encodedRoundBudget_eq (input : List Bool) :
    encodedRoundBudget input = roundResourcePolynomial.eval input.length := by
  simp [encodedRoundBudget]

/-- Extend the real private-word blocks by zero words for convenient indexing.
Only blocks within the actual schedule are ever used by replay or messages. -/
def decodedTapeWords (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ)
    (j : ℕ) : BitVec (residueWidth (protocolPrime (nodeCount φ.val.toQBF))) :=
  if hj : j < φ.val.schedule.length then
    randomTapeEquiv φ.val.schedule.length (residueWidth (protocolPrime (nodeCount φ.val.toQBF)))
      (fun i => tape ⟨i.val, i.isLt.trans_le (decodeClosedPrenex_coins_le input φ h)⟩) ⟨j, hj⟩
  else 0

/-- Prover-free verifier messages on all alternating transcript views, including
unreachable and malformed ones. Only the number of completed pairs matters. -/
def encodedVerifierMessage (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) : List Bool :=
  match h : decodeClosedPrenex input with
  | none => []
  | some φ => paddedVerifierMessage (protocolPrime (nodeCount φ.val.toQBF)) φ.val.schedule.length
      (decodedTapeWords input tape φ h) (history.length / 2)

/-- Prover-free final verdict. It checks the full padded transcript's shape,
then replays only the real-round prover replies with the private challenges. -/
def encodedTranscriptVerdict (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) : Bool :=
  match h : decodeClosedPrenex input with
  | none => false
  | some φ =>
      if history.length = 2 * encodedRoundBudget input then
        verifyReplyList (protocolPrime (nodeCount φ.val.toQBF)) (max 2 (nodeCount φ.val.matrix))
          (fun x => matrixEvalWithCost x φ.val.matrix φ.val.matrix_quantifierFree)
          φ.val.schedule finiteInitialClaim (transcriptReplies φ.val.schedule.length history)
          (decodedTapeWords input tape φ h)
      else false

theorem encodedVerifierMessage_decoded (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) (φ : {φ : PrenexQBF // φ.toQBF.Closed})
    (h : decodeClosedPrenex input = some φ) :
    encodedVerifierMessage input tape history =
      paddedVerifierMessage (protocolPrime (nodeCount φ.val.toQBF)) φ.val.schedule.length
        (decodedTapeWords input tape φ h) (history.length / 2) := by
  unfold encodedVerifierMessage
  split
  · rename_i hn
    simp [h] at hn
  · rename_i ψ hψ
    have heq : ψ = φ := Option.some.inj (hψ.symm.trans h)
    subst ψ
    rfl

theorem encodedTranscriptVerdict_decoded (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) (φ : {φ : PrenexQBF // φ.toQBF.Closed})
    (h : decodeClosedPrenex input = some φ) :
    encodedTranscriptVerdict input tape history =
      if history.length = 2 * encodedRoundBudget input then
        verifyReplyList (protocolPrime (nodeCount φ.val.toQBF)) (max 2 (nodeCount φ.val.matrix))
          (fun x => matrixEvalWithCost x φ.val.matrix φ.val.matrix_quantifierFree)
          φ.val.schedule finiteInitialClaim (transcriptReplies φ.val.schedule.length history)
          (decodedTapeWords input tape φ h)
      else false := by
  unfold encodedTranscriptVerdict
  split
  · rename_i hn
    simp [h] at hn
  · rename_i ψ hψ
    have heq : ψ = φ := Option.some.inj (hψ.symm.trans h)
    subst ψ
    rfl

theorem encodedTranscriptVerdict_invalid (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) (h : decodeClosedPrenex input = none) :
    encodedTranscriptVerdict input tape history = false := by
  unfold encodedTranscriptVerdict
  split
  · rfl
  · rename_i φ hφ
    simp [h] at hφ

/-- Every malformed transcript length rejects, including truncation and excess pairs. -/
theorem encodedTranscriptVerdict_wrong_length (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) (h : history.length ≠ 2 * encodedRoundBudget input) :
    encodedTranscriptVerdict input tape history = false := by
  unfold encodedTranscriptVerdict
  split
  · rfl
  · simp only [ite_eq_right h]

/-- Message lengths are bounded on every view, without assuming reachability,
valid message contents, or even an even transcript length. -/
theorem encodedVerifierMessage_length_le (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) :
    (encodedVerifierMessage input tape history).length ≤
      messageResourcePolynomial.eval input.length := by
  unfold encodedVerifierMessage
  split
  · simp
  · rename_i φ hφ
    unfold paddedVerifierMessage
    split
    · cases hr : history.length / 2 with
      | zero => simp [delayedVerifierMessage]
      | succ j =>
        exact φ.val.challenge_length_le_resource_eval input.length
          (decodeClosedPrenex_nodeCount_le input φ hφ) _
    · simp

theorem encodedVerifierMessage_initial (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    encodedVerifierMessage input tape [] = [] := by
  unfold encodedVerifierMessage
  split
  · rfl
  · exact paddedVerifierMessage_zero _ _ _

/-- No private challenge is revealed in dummy rounds, including the final
real-round challenge used only by the verdict. -/
theorem encodedVerifierMessage_dummy (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) (φ : {φ : PrenexQBF // φ.toQBF.Closed})
    (h : decodeClosedPrenex input = some φ) (hdummy : φ.val.schedule.length ≤ history.length / 2) :
    encodedVerifierMessage input tape history = [] := by
  rw [encodedVerifierMessage_decoded input tape history φ h]
  exact paddedVerifierMessage_after _ _ _ _ hdummy

/-- Equality of earlier private blocks suffices for the current outgoing message. -/
theorem encodedVerifierMessage_private_prefix (input : List Bool)
    (left right : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (history : List (List Bool)) (φ : {φ : PrenexQBF // φ.toQBF.Closed})
    (h : decodeClosedPrenex input = some φ)
    (hprefix : ∀ i < history.length / 2,
      decodedTapeWords input left φ h i = decodedTapeWords input right φ h i) :
    encodedVerifierMessage input left history = encodedVerifierMessage input right history := by
  rw [encodedVerifierMessage_decoded input left history φ h,
    encodedVerifierMessage_decoded input right history φ h]
  exact paddedVerifierMessage_prefix_eq _ _ _ _ _ hprefix

/-- Changing dummy replies or verifier-message entries cannot alter the final
verdict when the real prover replies and full transcript length are fixed. -/
theorem encodedTranscriptVerdict_congr_replies (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool)
    (left right : List (List Bool)) (φ : {φ : PrenexQBF // φ.toQBF.Closed})
    (h : decodeClosedPrenex input = some φ) (hlen : left.length = right.length)
    (hreplies : ∀ j < φ.val.schedule.length, left[2 * j + 1]? = right[2 * j + 1]?) :
    encodedTranscriptVerdict input tape left = encodedTranscriptVerdict input tape right := by
  have hr : transcriptReplies φ.val.schedule.length left =
      transcriptReplies φ.val.schedule.length right := by
    apply List.map_congr_left
    intro j hj
    rw [hreplies j (List.mem_range.mp hj)]
  rw [encodedTranscriptVerdict_decoded input tape left φ h,
    encodedTranscriptVerdict_decoded input tape right φ h, hlen, hr]

/-- Execute the two prover-free verifier procedures for exactly the fixed round budget. -/
def paddedProtocolExecution (S : List (List Bool) → List Bool) (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) : Bool :=
  encodedTranscriptVerdict input tape
    (interactionTranscript S (encodedVerifierMessage input tape) (encodedRoundBudget input))

theorem paddedProtocolExecution_transcript_length (S : List (List Bool) → List Bool)
    (input : List Bool) (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    (interactionTranscript S (encodedVerifierMessage input tape) (encodedRoundBudget input)).length =
      2 * roundResourcePolynomial.eval input.length := by
  rw [interactionTranscript_length, encodedRoundBudget_eq]

/-- Oracle-free replay and the previously analyzed oracle execution agree on
all strategies and all tapes, including invalid replies and early rejection. -/
theorem paddedProtocolExecution_eq_verifyEncodedProtocol
    (S : List (List Bool) → List Bool) (input : List Bool)
    (tape : Fin (coinResourcePolynomial.eval input.length) → Bool) :
    paddedProtocolExecution S input tape = verifyEncodedProtocol S input tape := by
  unfold paddedProtocolExecution
  cases h : decodeClosedPrenex input with
  | none =>
    rw [encodedTranscriptVerdict_invalid input tape _ h,
      verifyEncodedProtocol_reject S input h tape]
  | some φ =>
    have hrounds : φ.val.schedule.length ≤ encodedRoundBudget input := by
      rw [encodedRoundBudget_eq]
      exact φ.val.rounds_le_resource_eval input.length (decodeClosedPrenex_nodeCount_le input φ h)
    have htrace := interactionTranscript_eq_transcriptFromMessages S
      (encodedVerifierMessage input tape)
      (paddedVerifierMessage (protocolPrime (nodeCount φ.val.toQBF)) φ.val.schedule.length
        (decodedTapeWords input tape φ h))
      (fun history => encodedVerifierMessage_decoded input tape history φ h)
      (encodedRoundBudget input)
    rw [encodedTranscriptVerdict_decoded input tape _ φ h,
      ite_eq_left (interactionTranscript_length S _ _), htrace,
      transcriptReplies_padded _ _ _ hrounds,
      verifyReplyList_strategyReplies, verifyEncodedProtocol_decoded S input φ h tape]
    unfold PrenexQBF.verifyRandomTape IPPSPACE.verifyRandomTape
    congr 1
    funext i
    simp only [decodedTapeWords, dite_eq_left i.isLt, Fin.castLE]
    rfl

noncomputable section

open scoped Classical ENNReal

/-- Perfect completeness with a globally bounded prover, now for the actual
padded interaction of prover-free message and verdict procedures. -/
theorem paddedProtocolExecution_complete (input : List Bool) (htrue : EncodedTruePrenex input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤ messageResourcePolynomial.eval input.length) ∧
      ∀ tape, paddedProtocolExecution S input tape = true := by
  obtain ⟨S, hbound, haccept⟩ := verifyEncodedProtocol_complete input htrue
  exact ⟨S, hbound, fun tape =>
    (paddedProtocolExecution_eq_verifyEncodedProtocol S input tape).trans (haccept tape)⟩

/-- The rational accepting-tape fraction is at most one third for every global
strategy and every input outside the encoded true closed prenex language. -/
theorem paddedProtocolExecution_counting_soundness (S : List (List Bool) → List Bool)
    (input : List Bool) (hfalse : ¬ EncodedTruePrenex input) :
    ((Finset.univ.filter fun tape => paddedProtocolExecution S input tape = true).card : ℚ) /
      2 ^ (coinResourcePolynomial.eval input.length) ≤ 1 / 3 := by
  simp only [paddedProtocolExecution_eq_verifyEncodedProtocol]
  exact verifyEncodedProtocol_counting_soundness S input hfalse

end

end IPPSPACE

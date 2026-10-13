/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MessageProtocol

/-!
# Strategies that see an alternating binary transcript

The strategy argument in this module has the exact underlying function type of
Complexitylib's prover strategy: `List (List Bool) → List Bool`. An initial empty
verifier message requests the first reply; later verifier messages reveal the
previous round's canonical field challenge. Unfolding the strategy retains the
entire raw transcript, including the prover's own previous replies.

The deterministic replay lemmas show that each reply depends only on earlier
challenges. The probabilistic refinement connects this history-based execution
to the established raw-message protocol, including malformed-message rejection.
These are semantic adapters, not a new complexity class or an `FP` certificate.
-/

namespace IPPSPACE

/-- Unfold a global transcript strategy from a history ending in the verifier's
message. A fresh challenge is appended only after the current prover reply. -/
def unfoldTranscriptStrategy (S : List (List Bool) → List Bool) :
    (n : ℕ) → List (List Bool) → MessageStrategy n
  | 0, _ => PUnit.unit
  | n + 1, history =>
      (S history, fun challenge =>
        unfoldTranscriptStrategy S n (history ++ [S history, challenge]))

/-- The next reply after following a finite challenge history, or `none` if
the strategy has no round left at that point. -/
def MessageStrategy.replyAfter :
    {n : ℕ} → MessageStrategy n → List (List Bool) → Option (List Bool)
  | 0, _, _ => none
  | _ + 1, strategy, [] => some strategy.1
  | _ + 1, strategy, challenge :: challenges =>
      replyAfter (strategy.2 challenge) challenges

/-- Extend a history ending in a verifier message by the requested reply and
each successive challenge. The result again ends in a verifier message. -/
def pendingTranscript (S : List (List Bool) → List Bool) :
    List (List Bool) → List (List Bool) → List (List Bool)
  | history, [] => history
  | history, challenge :: challenges =>
      pendingTranscript S (history ++ [S history, challenge]) challenges

/-- Tree execution and transcript execution request exactly the same raw reply. -/
theorem replyAfter_unfoldTranscriptStrategy (S : List (List Bool) → List Bool)
    (n : ℕ) (history challenges : List (List Bool)) (h : challenges.length < n) :
    (unfoldTranscriptStrategy S n history).replyAfter challenges =
      some (S (pendingTranscript S history challenges)) := by
  induction challenges generalizing n history with
  | nil =>
    cases n with
    | zero => simp at h
    | succ n => rfl
  | cons challenge challenges ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      exact ih n (history ++ [S history, challenge]) (by simpa using h)

theorem pendingTranscript_append (S : List (List Bool) → List Bool)
    (history first rest : List (List Bool)) :
    pendingTranscript S history (first ++ rest) =
      pendingTranscript S (pendingTranscript S history first) rest := by
  induction first generalizing history with
  | nil => rfl
  | cons challenge first ih =>
    exact ih (history ++ [S history, challenge])

theorem pendingTranscript_length (S : List (List Bool) → List Bool)
    (history challenges : List (List Bool)) :
    (pendingTranscript S history challenges).length =
      history.length + 2 * challenges.length := by
  induction challenges generalizing history with
  | nil => simp [pendingTranscript]
  | cons challenge challenges ih =>
    rw [pendingTranscript, ih]
    simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]

/-- A strategy tree respects a bound on every reply, including replies after
unreachable challenge strings. -/
def MessageStrategy.RepliesBounded (m : ℕ) : {n : ℕ} → MessageStrategy n → Prop
  | 0, _ => True
  | _ + 1, strategy =>
      strategy.1.length ≤ m ∧ ∀ challenge, RepliesBounded m (strategy.2 challenge)

theorem unfoldTranscriptStrategy_repliesBounded (S : List (List Bool) → List Bool)
    (m : ℕ) (hS : ∀ history, (S history).length ≤ m) (n : ℕ)
    (history : List (List Bool)) :
    (unfoldTranscriptStrategy S n history).RepliesBounded m := by
  induction n generalizing history with
  | zero => trivial
  | succ n ih => exact ⟨hS history, fun _ => ih _⟩

theorem MessageStrategy.RepliesBounded.replyAfter {m n : ℕ}
    {strategy : MessageStrategy n} (h : strategy.RepliesBounded m)
    (challenges : List (List Bool)) (reply : List Bool)
    (hreply : strategy.replyAfter challenges = some reply) : reply.length ≤ m := by
  induction n generalizing challenges with
  | zero => simp [MessageStrategy.replyAfter] at hreply
  | succ n ih =>
    cases challenges with
    | nil =>
      have heq : strategy.1 = reply := Option.some.inj hreply
      rw [← heq]
      exact h.1
    | cons challenge challenges =>
      exact ih (h.2 challenge) challenges hreply

/-- An unexhausted tree has a reply along every challenge history. -/
theorem MessageStrategy.replyAfter_ne_none {n : ℕ} (strategy : MessageStrategy n)
    (challenges : List (List Bool)) (h : challenges.length < n) :
    strategy.replyAfter challenges ≠ none := by
  induction n generalizing challenges with
  | zero => omega
  | succ n ih =>
    cases challenges with
    | nil => simp [MessageStrategy.replyAfter]
    | cons challenge challenges =>
      exact ih (strategy.2 challenge) challenges (by simpa using h)

/-- A finite strategy tree is determined by its replies on all challenge paths. -/
theorem MessageStrategy.ext_replyAfter {n : ℕ} (left right : MessageStrategy n)
    (h : ∀ challenges, challenges.length < n →
      left.replyAfter challenges = right.replyAfter challenges) : left = right := by
  induction n with
  | zero => cases left; cases right; rfl
  | succ n ih =>
    apply Prod.ext
    · exact Option.some.inj (h [] (by simp))
    · funext challenge
      apply ih
      intro challenges hlen
      exact h (challenge :: challenges) (by simpa using hlen)

/-- Read the verifier challenges from consecutive prover/verifier pairs. -/
def challengesFromPairs : List (List Bool) → List (List Bool)
  | [] => []
  | [_] => []
  | _ :: challenge :: rest => challenge :: challengesFromPairs rest

theorem challengesFromPairs_append (first rest : List (List Bool))
    (h : first.length % 2 = 0) :
    challengesFromPairs (first ++ rest) =
      challengesFromPairs first ++ challengesFromPairs rest := by
  induction first using List.twoStepInduction with
  | nil => rfl
  | singleton message => simp at h
  | cons_cons reply challenge first ih _ =>
    simp only [List.cons_append, challengesFromPairs, List.cons.injEq, true_and]
    apply ih
    simp only [List.length_cons] at h
    omega

/-- Removing the initial verifier message from a pending history exposes
exactly the challenges that have already been revealed. -/
theorem challengesFromPairs_pendingTranscript (S : List (List Bool) → List Bool)
    (initial : List Bool) (rest challenges : List (List Bool))
    (h : rest.length % 2 = 0) :
    challengesFromPairs (pendingTranscript S (initial :: rest) challenges).tail =
      challengesFromPairs rest ++ challenges := by
  induction challenges generalizing rest with
  | nil => simp [pendingTranscript]
  | cons challenge challenges ih =>
    change challengesFromPairs
      (pendingTranscript S (initial :: (rest ++ [S (initial :: rest), challenge])) challenges).tail = _
    rw [ih (rest ++ [S (initial :: rest), challenge]) (by simpa using h),
      challengesFromPairs_append rest _ h]
    simp [challengesFromPairs, List.append_assoc]

/-- Realize a finite tree as a total transcript strategy. Replies outside its
round budget are empty; arbitrary forged prover messages are simply ignored. -/
def MessageStrategy.asTranscriptStrategy {n : ℕ} (strategy : MessageStrategy n)
    (history : List (List Bool)) : List Bool :=
  (strategy.replyAfter (challengesFromPairs history.tail)).getD []

theorem MessageStrategy.asTranscriptStrategy_bounded {n m : ℕ}
    (strategy : MessageStrategy n) (h : strategy.RepliesBounded m)
    (history : List (List Bool)) : (strategy.asTranscriptStrategy history).length ≤ m := by
  unfold asTranscriptStrategy
  cases hr : strategy.replyAfter (challengesFromPairs history.tail) with
  | none => simp
  | some reply => exact h.replyAfter _ reply hr

/-- Replaying the global strategy recovers its original tree, at every raw
challenge history, not merely the canonical histories used by the verifier. -/
theorem unfoldTranscriptStrategy_asTranscriptStrategy {n : ℕ} (strategy : MessageStrategy n) :
    unfoldTranscriptStrategy strategy.asTranscriptStrategy n [[]] = strategy := by
  apply MessageStrategy.ext_replyAfter
  intro challenges hlen
  rw [replyAfter_unfoldTranscriptStrategy _ _ _ _ hlen]
  simp only [MessageStrategy.asTranscriptStrategy]
  rw [challengesFromPairs_pendingTranscript _ [] [] challenges (by simp)]
  simp only [challengesFromPairs, List.nil_append]
  cases hr : strategy.replyAfter challenges with
  | none => exact (strategy.replyAfter_ne_none challenges hlen hr).elim
  | some reply => rfl

/-- Replay externally supplied verifier messages in the verifier-first order
used upstream: append the verifier message and then the strategy's reply. -/
def transcriptFromMessages (S : List (List Bool) → List Bool)
    (messages : ℕ → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | n + 1 =>
      let history := transcriptFromMessages S messages n
      history ++ [messages n, S (history ++ [messages n])]

/-- Request the first reply with an empty message, then reveal one previous
challenge per further request. No new challenge is revealed before its reply. -/
def delayedVerifierMessage (challenges : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => challenges n

/-- The first `n` challenges visible by the time reply `n` is requested. -/
def challengePrefix (challenges : ℕ → List Bool) (n : ℕ) : List (List Bool) :=
  (List.range n).map challenges

theorem challengePrefix_succ (challenges : ℕ → List Bool) (n : ℕ) :
    challengePrefix challenges (n + 1) = challengePrefix challenges n ++ [challenges n] := by
  simp [challengePrefix, List.range_succ]

/-- The tree's pending history is the complete upstream-shaped transcript
followed by the verifier's next (delayed) message. -/
theorem pendingTranscript_eq_transcriptFromMessages
    (S : List (List Bool) → List Bool) (challenges : ℕ → List Bool) (n : ℕ) :
    pendingTranscript S [[]] (challengePrefix challenges n) =
      transcriptFromMessages S (delayedVerifierMessage challenges) n ++
        [delayedVerifierMessage challenges n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [challengePrefix_succ, pendingTranscript_append, ih]
    simp [pendingTranscript, transcriptFromMessages, delayedVerifierMessage, List.append_assoc]

/-- Every requested reply agrees with verifier-first replay along that prefix. -/
theorem replyAfter_eq_transcriptFromMessages (S : List (List Bool) → List Bool)
    (challenges : ℕ → List Bool) (rounds n : ℕ) (h : n < rounds) :
    (unfoldTranscriptStrategy S rounds [[]]).replyAfter (challengePrefix challenges n) =
      some (S (transcriptFromMessages S (delayedVerifierMessage challenges) n ++
        [delayedVerifierMessage challenges n])) := by
  rw [replyAfter_unfoldTranscriptStrategy S rounds [[]] _
    (by simpa [challengePrefix] using h), pendingTranscript_eq_transcriptFromMessages]

/-- Equal earlier challenges give equal pending transcripts. Thus the current
reply cannot depend on the current challenge or any future challenge. -/
theorem pendingTranscript_prefix_eq (S : List (List Bool) → List Bool)
    (left right : ℕ → List Bool) (n : ℕ) (h : ∀ i < n, left i = right i) :
    pendingTranscript S [[]] (challengePrefix left n) =
      pendingTranscript S [[]] (challengePrefix right n) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem transcriptFromMessages_length (S : List (List Bool) → List Bool)
    (messages : ℕ → List Bool) (n : ℕ) :
    (transcriptFromMessages S messages n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [transcriptFromMessages, ih, Nat.mul_add]

/-- Uniform bounds on both parties bound every message in
the completed transcript, regardless of which messages the prover chooses. -/
theorem transcriptFromMessages_messages_bounded
    (S : List (List Bool) → List Bool) (messages : ℕ → List Bool) (m n : ℕ)
    (hS : ∀ history, (S history).length ≤ m)
    (hv : ∀ i < n, (messages i).length ≤ m)
    (message : List Bool) (hmem : message ∈ transcriptFromMessages S messages n) :
    message.length ≤ m := by
  induction n with
  | zero => simp [transcriptFromMessages] at hmem
  | succ n ih =>
    simp only [transcriptFromMessages, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | rfl | rfl
    · exact ih (fun i hi => hv i (Nat.lt_trans hi (Nat.lt_succ_self n))) hmem
    · exact hv n (Nat.lt_succ_self n)
    · exact hS _

/-- Completed transcripts contain at most two bounded messages per round.
This counts payload bits and excludes the outer transcript encoding. -/
theorem transcriptFromMessages_total_bits_le
    (S : List (List Bool) → List Bool) (messages : ℕ → List Bool) (m n : ℕ)
    (hS : ∀ history, (S history).length ≤ m)
    (hv : ∀ i < n, (messages i).length ≤ m) :
    ((transcriptFromMessages S messages n).map List.length).sum ≤ 2 * n * m := by
  induction n with
  | zero => simp [transcriptFromMessages]
  | succ n ih =>
    have hprior := ih (fun i hi => hv i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hreply := hS (transcriptFromMessages S messages n ++ [messages n])
    have hmessage := hv n (Nat.lt_succ_self n)
    simp only [transcriptFromMessages, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega

noncomputable section

open MvPolynomial
open scoped Classical ENNReal

/-- Canonical polynomial encodings have the same fixed message-length bound
at every node, even after an arbitrary noncanonical challenge string. -/
theorem encodePolynomialStrategy_repliesBounded (p d : ℕ) {n : ℕ}
    (strategy : ProverStrategy (ZMod p) n) :
    (encodeCoefficientStrategy p (encodePolynomialStrategy d strategy)).RepliesBounded
      ((d + 1) * residueWidth p) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · simp [encodeCoefficientStrategy, encodePolynomialStrategy]
    · intro challenge
      exact ih _

/-- Execute directly against a global transcript strategy, starting with a
history ending in the verifier's message. Fresh words are sampled only after
the requested reply is fixed and passes both parsing and the algebraic check. -/
def runTranscriptVerifier (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (S : List (List Bool) → List Bool) :
    List AlgebraicOperator → FiniteClaim (ZMod p) → List (List Bool) → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = (terminal c.point).1))
  | op :: ops, c, history =>
      match parseMessage p (d + 1) (S history) with
      | none => PMF.pure false
      | some as =>
        if (checkRoundWithCost op d c as).1 then
          (fairWord (residueWidth p)).bind (fun word =>
            let r := sampleResidue p word
            runTranscriptVerifier p d terminal S ops (c.advanceWithCost op as r).1
              (history ++ [S history, encodeMessage [r]]))
        else PMF.pure false

/-- History-based execution exactly refines the analyzed raw strategy tree,
including all malformed replies and early rejections. -/
theorem runTranscriptVerifier_eq_runMessageVerifier (p d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (S : List (List Bool) → List Bool)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (history : List (List Bool)) :
    runTranscriptVerifier p d terminal S ops c history =
      runMessageVerifier p d terminal ops c (unfoldTranscriptStrategy S ops.length history) := by
  induction ops generalizing c history with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.length_cons, runTranscriptVerifier, unfoldTranscriptStrategy,
      runMessageVerifier]
    cases hp : parseMessage p (d + 1) (S history) with
    | none => rfl
    | some as =>
      simp only
      by_cases hc : (checkRoundWithCost op d c as).1 = true
      · rw [ite_eq_left hc, ite_eq_left hc]
        congr 1
        funext word
        exact ih _ _
      · rw [ite_eq_right hc, ite_eq_right hc]

/-- The concrete-field protocol with the upstream strategy's underlying type
and the verifier-first initial dummy message. -/
def PrenexQBF.runTranscriptProtocol (φ : PrenexQBF)
    (S : List (List Bool) → List Bool) : PMF Bool :=
  runTranscriptVerifier (protocolPrime (nodeCount φ.toQBF)) (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    S φ.schedule finiteInitialClaim [[]]

theorem PrenexQBF.runTranscriptProtocol_eq_runMessageProtocol (φ : PrenexQBF)
    (S : List (List Bool) → List Bool) :
    φ.runTranscriptProtocol S =
      φ.runMessageProtocol (unfoldTranscriptStrategy S φ.schedule.length [[]]) :=
  runTranscriptVerifier_eq_runMessageVerifier _ _ _ _ _ _ _

/-- A total globally bounded honest prover in the upstream strategy's
underlying type; no promise is made about the transcript it is handed. -/
def PrenexQBF.honestTranscriptStrategy (φ : PrenexQBF) : List (List Bool) → List Bool :=
  (encodeCoefficientStrategy (protocolPrime (nodeCount φ.toQBF))
    (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
      (honestStrategy (arithmetize (R := ProtocolField (nodeCount φ.toQBF)) φ.matrix)
        φ.schedule initialClaim))).asTranscriptStrategy

theorem PrenexQBF.honestTranscriptStrategy_bounded (φ : PrenexQBF)
    (history : List (List Bool)) :
    (φ.honestTranscriptStrategy history).length ≤
      (max 2 (nodeCount φ.matrix) + 1) * residueWidth (protocolPrime (nodeCount φ.toQBF)) :=
  MessageStrategy.asTranscriptStrategy_bounded _
    (encodePolynomialStrategy_repliesBounded _ _ _) history

/-- Verifier-first transcript strategies preserve perfect completeness. -/
theorem PrenexQBF.runTranscriptProtocol_honest (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    φ.runTranscriptProtocol φ.honestTranscriptStrategy = PMF.pure true := by
  rw [φ.runTranscriptProtocol_eq_runMessageProtocol]
  unfold honestTranscriptStrategy
  rw [unfoldTranscriptStrategy_asTranscriptStrategy]
  exact φ.runMessageProtocol_honest hclosed htrue

/-- Every global transcript strategy satisfies soundness. No bound or
well-formedness condition on its replies is needed for this semantic result. -/
theorem PrenexQBF.runTranscriptProtocol_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (S : List (List Bool) → List Bool) :
    φ.runTranscriptProtocol S true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [φ.runTranscriptProtocol_eq_runMessageProtocol]
  exact φ.runMessageProtocol_soundness_le_third hclosed hfalse _

end

end IPPSPACE

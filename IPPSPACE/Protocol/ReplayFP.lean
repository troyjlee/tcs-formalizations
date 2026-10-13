/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MatrixFP
import IPPSPACE.Protocol.ScheduleFP
import IPPSPACE.Protocol.CoinAccessFP
import IPPSPACE.Protocol.TranscriptParsingFP

/-!
# Polynomial-time bounded finite-claim replay

The raw loop keeps a tagged finite assignment and one residue value. Each round
checks the bounded coefficient message and appends one binary-name assignment.
Failure is absorbing. The exact semantic refinement below uses canonical initial
claims and challenges; the runtime and size bounds cover every raw input.
-/

namespace IPPSPACE

open Complexity

/-- Empty means failure; a successful finite claim is tagged. -/
def encodeReplayClaim {p : ℕ} : Option (FiniteClaim (ZMod p)) → List Bool
  | none => []
  | some c => true :: encodeFiniteClaim c

/-- One replay round, total on arbitrary strings. -/
def replayClaimBitsStep (p degree kind : ℕ) (key reply challenge state : List Bool) : List Bool :=
  let claim := state.drop 1
  let entries := pairFst claim
  let value := pairSnd claim
  let point := assignmentLookupBits p key entries
  if state ≠ [] ∧ CanonicalResidueBits p challenge ∧
      checkRoundBits p kind degree point value reply = true then
    true :: pair (pair (pair key challenge) entries)
      (evaluateMessageBits p (degree + 1) challenge reply)
  else []

theorem replayClaimBitsStep_mem_FP {p degree kind : List Bool → ℕ}
    {key reply challenge state : List Bool → List Bool}
    (hp : UnaryFn p) (hd : UnaryFn degree) (hk : UnaryFn kind)
    (hkey : key ∈ FP) (hreply : reply ∈ FP) (hr : challenge ∈ FP) (hs : state ∈ FP) :
    (fun z => replayClaimBitsStep (p z) (degree z) (kind z)
      (key z) (reply z) (challenge z) (state z)) ∈ FP := by
  have he := mem_FP_comp (drop_mem_FP hs (UnaryFn.const 1)) pairFst_mem_FP
  have hv := mem_FP_comp (drop_mem_FP hs (UnaryFn.const 1)) pairSnd_mem_FP
  have hcheck := checkRoundBits_mem_FP hp hk hd (assignmentLookupBits_mem_FP hp hkey he) hv hreply
  have hpred : FPPred fun z => checkRoundBits (p z) (kind z) (degree z)
      (assignmentLookupBits (p z) (key z) (pairFst ((state z).drop 1)))
      (pairSnd ((state z).drop 1)) (reply z) = true :=
    (FPPred.getBit hcheck (UnaryFn.const 0)).of_iff (fun _ => by simp)
  exact ((bitStrings_eq_fppred hs (constFn_mem_FP [])).not.and
    ((canonicalResidueBits_fppred hp hr).and hpred)).ite_mem_FP
    (mem_FP_comp (mem_FP_pair (mem_FP_pair (mem_FP_pair hkey hr) he)
      (evaluateMessageBits_mem_FP hp (hd.add (UnaryFn.const 1)) hr hreply))
      (Cobham.cons_mem_FP true)) (constFn_mem_FP [])

private theorem twice_pairFst_length_le (bits : List Bool) :
    2 * (pairFst bits).length ≤ bits.length := by
  induction bits using pairFst.induct <;> simp [pairFst] <;> omega

/-- Re-encoding a claim does not double its stored assignment chain. The
pair decoder consumes two input bits per returned first-component bit. -/
theorem replayClaimBitsStep_length_le (p degree kind : ℕ)
    (key reply challenge state : List Bool) :
    (replayClaimBitsStep p degree kind key reply challenge state).length ≤
      state.length + 8 * key.length + 5 * residueWidth p + 15 := by
  dsimp only [replayClaimBitsStep]
  split
  · rename_i h
    have he := twice_pairFst_length_le (state.drop 1)
    have hv := evaluateMessageBits_length_le p (degree + 1) challenge reply
    simp only [List.length_cons, pair_length, h.2.1.1]
    simp only [List.length_drop] at he
    omega
  · simp

@[simp] theorem replayClaimBitsStep_nil (p degree kind : ℕ) (key reply challenge : List Bool) :
    replayClaimBitsStep p degree kind key reply challenge [] = [] := by
  simp [replayClaimBitsStep]

/-- Semantic state transition corresponding to the original reply-list verifier. -/
def replayClaimStep (p degree : ℕ) (op : AlgebraicOperator) (reply : List Bool)
    (challenge : ZMod p) (c : FiniteClaim (ZMod p)) : Option (FiniteClaim (ZMod p)) := do
  let as ← parseMessage p (degree + 1) reply
  if (checkRoundWithCost op degree c as).1 then some (c.advanceWithCost op as challenge).1 else none

/-- One machine update equals the exact parser, check, and finite-claim advance. -/
theorem replayClaimBitsStep_encode {p : ℕ} [NeZero p] (degree : ℕ)
    (op : AlgebraicOperator) (reply : List Bool) (challenge : ZMod p)
    (c : Option (FiniteClaim (ZMod p))) :
    replayClaimBitsStep p degree op.roundKind op.coordinate.bits reply
      (wordBits (encodeResidue challenge)) (encodeReplayClaim c) =
      encodeReplayClaim (c.bind (replayClaimStep p degree op reply challenge)) := by
  cases c with
  | none => simp [encodeReplayClaim]
  | some c =>
    simp only [replayClaimBitsStep, encodeReplayClaim, List.drop_succ_cons, List.drop_zero,
      pairFst_encodeFiniteClaim, pairSnd_encodeFiniteClaim, assignmentLookupBits_encode,
      show (assignmentLookupWithCost c.entries op.coordinate).1 = c.point op.coordinate from rfl,
      checkRoundBits_eq, canonicalResidueBits_wordBits, encodeResidue_toNat,
      challenge.val_lt, true_and, Option.bind_some]
    cases hparse : parseMessage p (degree + 1) reply with
    | none => simp [replayClaimStep, hparse]
    | some as =>
      obtain ⟨hbits, hlen⟩ := parseMessage_sound (degree + 1) reply as hparse
      by_cases hcheck : (checkRoundWithCost op degree c as).1 = true
      · rw [← hbits, evaluateMessageBits_encodeMessage _ _ _ hlen]
        simp [replayClaimStep, parseMessage_encode _ _ hlen, hcheck,
          encodeFiniteClaim, FiniteClaim.advanceWithCost, encodeAssignmentEntries]
      · simp [hcheck, replayClaimStep, hparse]

/-- Forward replay with separately indexed round data. -/
def replayClaimBitsLoop (p degree : ℕ) (kind : ℕ → ℕ)
    (key reply challenge : ℕ → List Bool) (initial : List Bool) : ℕ → List Bool
  | 0 => initial
  | n + 1 => replayClaimBitsStep p degree (kind n) (key n) (reply n) (challenge n)
      (replayClaimBitsLoop p degree kind key reply challenge initial n)

theorem replayClaimBitsLoop_length_le (p degree bound : ℕ) (kind : ℕ → ℕ)
    (key reply challenge : ℕ → List Bool) (initial : List Bool) (n : ℕ)
    (hkey : ∀ i < n, (key i).length ≤ bound) :
    (replayClaimBitsLoop p degree kind key reply challenge initial n).length ≤
      initial.length + n * (8 * bound + 5 * residueWidth p + 15) := by
  induction n with
  | zero => simp [replayClaimBitsLoop]
  | succ n ih =>
    have hi := ih (fun i hi => hkey i (by omega))
    have hs := replayClaimBitsStep_length_le p degree (kind n) (key n) (reply n) (challenge n)
      (replayClaimBitsLoop p degree kind key reply challenge initial n)
    have hk := hkey n (by omega)
    simp only [replayClaimBitsLoop, Nat.add_mul, Nat.one_mul]
    omega

/-- Genuine upstream FP certificate for bounded replay. Indexed inputs use the
standard pair of the original input with a unary index; keys remain binary. -/
theorem replayClaimBitsLoop_mem_FP {p degree count : List Bool → ℕ}
    {kind : List Bool → ℕ → ℕ} {key reply challenge : List Bool → ℕ → List Bool}
    {initial : List Bool → List Bool}
    (hp : UnaryFn p) (hd : UnaryFn degree) (hc : UnaryFn count)
    (hk : UnaryFn fun w => kind (pairFst w) (pairSnd w).length)
    (hkey : (fun w => key (pairFst w) (pairSnd w).length) ∈ FP)
    (hreply : (fun w => reply (pairFst w) (pairSnd w).length) ∈ FP)
    (hr : (fun w => challenge (pairFst w) (pairSnd w).length) ∈ FP)
    (hinit : initial ∈ FP) :
    (fun z => replayClaimBitsLoop (p z) (degree z) (kind z) (key z) (reply z)
      (challenge z) (initial z) (count z)) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  let original : List Bool → List Bool := fun z => pairFst (pairFst z)
  have ho : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hindex : (fun z => pair (original z) (pairSnd z)) ∈ FP := mem_FP_pair ho pairSnd_mem_FP
  have hstep := replayClaimBitsStep_mem_FP (hp.comp ho) (hd.comp ho) (hk.comp hindex)
    (mem_FP_comp hindex hkey) (mem_FP_comp hindex hreply) (mem_FP_comp hindex hr)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  obtain ⟨pc, hpc⟩ := Cobham.output_length_poly_of_mem_FP hc.mem_FP
  obtain ⟨pk, hpk⟩ := Cobham.output_length_poly_of_mem_FP hkey
  obtain ⟨pw, hpw⟩ := Cobham.output_length_poly_of_mem_FP (residueWidth_unaryFn hp).mem_FP
  obtain ⟨pi, hpi⟩ := Cobham.output_length_poly_of_mem_FP hinit
  let keyBound := fun n => pk.eval (2 * n + 2 + pc.eval n)
  have hkb : PolyBound keyBound :=
    (PolyBound.eval (pk.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 2 + pc))).mono
      (fun n => by simp [keyBound, Polynomial.eval_comp])
  have h := recFold_mem_FP_of_bound
    (g := fun z t => replayClaimBitsLoop (p z) (degree z) (kind z) (key z) (reply z)
      (challenge z) (initial z) t.length)
    (w := id) (E := initial) hstep hstep hinit hid hc.mem_FP
    (by intro z; rfl)
    (by intro z t; simp [original, replayClaimBitsLoop])
    (by intro z t; simp [original, replayClaimBitsLoop])
    ((PolyBound.eval pi).add ((PolyBound.eval pc).mul
      ((((PolyBound.const 8).mul hkb).add ((PolyBound.const 5).mul (PolyBound.eval pw))).add
        (PolyBound.const 15))))
    (by
      intro z t ht
      have htc : t.length ≤ count z := by simpa using ht.length_le
      have hc' : count z ≤ pc.eval z.length := by simpa using hpc z
      have hw' : residueWidth (p z) ≤ pw.eval z.length := by simpa using hpw z
      have hkeys : ∀ i < t.length, (key z i).length ≤ keyBound z.length := by
        intro i hi
        have h := hpk (pair z (List.replicate i true))
        simp only [pairFst_pair, pairSnd_pair, List.length_replicate, pair_length] at h
        exact h.trans (polynomial_eval_mono_nat pk (by omega))
      refine (replayClaimBitsLoop_length_le _ _ _ _ _ _ _ _ _ hkeys).trans ?_
      exact Nat.add_le_add (hpi z) (Nat.mul_le_mul (htc.trans hc') (by omega)))
  exact mem_FP_of_eq h (fun z => by simp)

/-- Semantic forward replay of exactly `count` indexed rounds. -/
def replayClaimRun (p degree : ℕ) (ops : ℕ → AlgebraicOperator) (replies : ℕ → List Bool)
    (challenges : ℕ → ZMod p) : ℕ → FiniteClaim (ZMod p) → Option (FiniteClaim (ZMod p))
  | 0, c => some c
  | n + 1, c => (replayClaimStep p degree (ops 0) (replies 0) (challenges 0) c).bind
      (replayClaimRun p degree (fun i => ops (i + 1)) (fun i => replies (i + 1))
        (fun i => challenges (i + 1)) n)

/-- The same forward computation may be extended by its final round. -/
theorem replayClaimRun_succ_last (p degree : ℕ) (ops : ℕ → AlgebraicOperator)
    (replies : ℕ → List Bool) (challenges : ℕ → ZMod p) (n : ℕ) (c : FiniteClaim (ZMod p)) :
    replayClaimRun p degree ops replies challenges (n + 1) c =
      (replayClaimRun p degree ops replies challenges n c).bind
        (replayClaimStep p degree (ops n) (replies n) (challenges n)) := by
  induction n generalizing ops replies challenges c with
  | zero => simp [replayClaimRun]
  | succ n ih =>
    change (replayClaimStep p degree (ops 0) (replies 0) (challenges 0) c).bind
        (fun c' => replayClaimRun p degree (fun i => ops (i + 1))
          (fun i => replies (i + 1)) (fun i => challenges (i + 1)) (n + 1) c') =
      ((replayClaimStep p degree (ops 0) (replies 0) (challenges 0) c).bind
        (replayClaimRun p degree (fun i => ops (i + 1))
          (fun i => replies (i + 1)) (fun i => challenges (i + 1)) n)).bind _
    rw [Option.bind_assoc]
    congr 1
    funext next
    exact ih _ _ _ next

/-- Canonical-state invariant for the actual bounded loop, including failure. -/
theorem replayClaimBitsLoop_encode {p : ℕ} [NeZero p] (degree : ℕ)
    (ops : ℕ → AlgebraicOperator) (replies : ℕ → List Bool) (challenges : ℕ → ZMod p)
    (initial : FiniteClaim (ZMod p)) (n : ℕ) :
    replayClaimBitsLoop p degree (fun i => (ops i).roundKind)
      (fun i => (ops i).coordinate.bits) replies
      (fun i => wordBits (encodeResidue (challenges i))) (encodeReplayClaim (some initial)) n =
      encodeReplayClaim (replayClaimRun p degree ops replies challenges n initial) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replayClaimBitsLoop, ih, replayClaimBitsStep_encode, replayClaimRun_succ_last]

/-- The bounded semantic replay has the original reply-list verifier's exact
behavior whenever the reply list contains every scheduled round. Extra replies
are ignored by both definitions. -/
theorem verifyReplyList_eq_replayClaimRun (p degree : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (initial : FiniteClaim (ZMod p)) (replies : List (List Bool))
    (words : ℕ → BitVec (residueWidth p)) (hlen : ops.length ≤ replies.length) :
    verifyReplyList p degree terminal ops initial replies words =
      ((replayClaimRun p degree (fun i => ops[i]?.getD (.reduce 0))
        (fun i => replies[i]?.getD []) (fun i => sampleResidue p (words i))
        ops.length initial).map (fun c => decide (c.value = (terminal c.point).1))).getD false := by
  induction ops generalizing initial replies words with
  | nil => rfl
  | cons op ops ih =>
    cases replies with
    | nil => simp at hlen
    | cons reply replies =>
      have ht : ops.length ≤ replies.length := by simpa using hlen
      simp only [List.length_cons, replayClaimRun, List.getElem?_cons_zero, Option.getD_some,
        List.getElem?_cons_succ]
      cases hp : parseMessage p (degree + 1) reply with
      | none => simp [verifyReplyList, replayClaimStep, hp]
      | some as =>
        by_cases hc : (checkRoundWithCost op degree initial as).1 = true
        · simpa [verifyReplyList, replayClaimStep, hp, hc] using
            ih (initial.advanceWithCost op as (sampleResidue p (words 0))).1 replies
              (fun i => words (i + 1)) ht
        · simp [verifyReplyList, replayClaimStep, hp, hc]

/-- Check a completed tagged claim by directly evaluating the terminal matrix. -/
def replayVerdictBits (p : ℕ) (matrix state : List Bool) : Bool :=
  if state ≠ [] then
    decide (pairSnd (state.drop 1) = evaluateMatrixBits p (pairFst (state.drop 1)) matrix)
  else false

theorem replayVerdictBits_mem_FP {p : List Bool → ℕ} {matrix state : List Bool → List Bool}
    (hp : UnaryFn p) (hm : matrix ∈ FP) (hs : state ∈ FP) :
    (fun z => [replayVerdictBits (p z) (matrix z) (state z)]) ∈ FP := by
  have hclaim := drop_mem_FP hs (UnaryFn.const 1)
  have heq := bitStrings_eq_fppred (mem_FP_comp hclaim pairSnd_mem_FP)
    (evaluateMatrixBits_mem_FP hp (mem_FP_comp hclaim pairFst_mem_FP) hm)
  apply mem_FP_of_eq (((bitStrings_eq_fppred hs (constFn_mem_FP [])).not).ite_mem_FP
    heq.flag_mem_FP (constFn_mem_FP [false]))
  intro z
  unfold replayVerdictBits
  split <;> rfl

theorem replayVerdictBits_encode {p : ℕ} [NeZero p]
    (matrix : QBF) (hm : matrix.QuantifierFree) (c : Option (FiniteClaim (ZMod p))) :
    replayVerdictBits p (encodeQBF matrix) (encodeReplayClaim c) =
      (c.map (fun c => decide (c.value = (matrixEvalWithCost c.point matrix hm).1))).getD false := by
  cases c with
  | none => simp [replayVerdictBits, encodeReplayClaim]
  | some c =>
    have hinj : Function.Injective (fun a : ZMod p => wordBits (encodeResidue a)) := by
      intro a b h
      have hv := congrArg Nat.fromBits h
      simp only [fromBits_wordBits, encodeResidue_toNat] at hv
      exact ZMod.val_injective p hv
    simp only [replayVerdictBits, encodeReplayClaim, List.drop_succ_cons, List.drop_zero,
      pairFst_encodeFiniteClaim, pairSnd_encodeFiniteClaim, evaluateMatrixBits_encodeQBF,
      show (fun i => (assignmentLookupWithCost c.entries i).1) = c.point from rfl,
      matrixValue?_eq _ _ hm, Option.map_some, Option.getD_some]
    simp [hinj.eq_iff]

/-- Machine certificate for the exact semantic bounded replay and final matrix
comparison, from polynomial-time indexed round data and canonical initial state. -/
theorem replayClaimRun_verdict_mem_FP {p degree count : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0) (hd : UnaryFn degree) (hc : UnaryFn count)
    (ops : List Bool → ℕ → AlgebraicOperator) (replies : List Bool → ℕ → List Bool)
    (challenges : (z : List Bool) → ℕ → ZMod (p z))
    (initial : (z : List Bool) → FiniteClaim (ZMod (p z)))
    (matrix : List Bool → QBF) (hqm : ∀ z, (matrix z).QuantifierFree)
    (hk : UnaryFn fun w => (ops (pairFst w) (pairSnd w).length).roundKind)
    (hi : (fun w => (ops (pairFst w) (pairSnd w).length).coordinate.bits) ∈ FP)
    (hreply : (fun w => replies (pairFst w) (pairSnd w).length) ∈ FP)
    (hr : (fun w => wordBits (encodeResidue (challenges (pairFst w) (pairSnd w).length))) ∈ FP)
    (hinit : (fun z => encodeFiniteClaim (initial z)) ∈ FP)
    (hm : (fun z => encodeQBF (matrix z)) ∈ FP) :
    (fun z => [((replayClaimRun (p z) (degree z) (ops z) (replies z) (challenges z)
      (count z) (initial z)).map
        (fun c => decide (c.value = (matrixEvalWithCost c.point (matrix z) (hqm z)).1))).getD false]) ∈ FP := by
  have hloop := replayClaimBitsLoop_mem_FP
    (kind := fun z i => (ops z i).roundKind)
    (key := fun z i => (ops z i).coordinate.bits)
    (challenge := fun z i => wordBits (encodeResidue (challenges z i))) hp hd hc hk hi hreply hr
    (mem_FP_comp hinit (Cobham.cons_mem_FP true))
  apply mem_FP_of_eq (replayVerdictBits_mem_FP hp hm hloop)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  dsimp only [Function.comp_apply]
  rw [show true :: encodeFiniteClaim (initial z) = encodeReplayClaim (some (initial z)) from rfl,
    replayClaimBitsLoop_encode, replayVerdictBits_encode]

/-- A bounded replay only depends on the round data below its iteration count. -/
theorem replayClaimBitsLoop_congr (p degree : ℕ)
    (kind kind' : ℕ → ℕ) (key key' reply reply' challenge challenge' : ℕ → List Bool)
    (initial : List Bool) (n : ℕ)
    (hk : ∀ i < n, kind i = kind' i) (hi : ∀ i < n, key i = key' i)
    (hr : ∀ i < n, reply i = reply' i) (hc : ∀ i < n, challenge i = challenge' i) :
    replayClaimBitsLoop p degree kind key reply challenge initial n =
      replayClaimBitsLoop p degree kind' key' reply' challenge' initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replayClaimBitsLoop, replayClaimBitsLoop,
      ih (fun i hi => hk i (by omega)) (fun i hi' => hi i (by omega))
        (fun i hi => hr i (by omega)) (fun i hi => hc i (by omega)),
      hk n (by omega), hi n (by omega), hr n (by omega), hc n (by omega)]

/-- Total verifier replay given the history's size and indexed prover replies.
The decoder and full padded-history length guard are the existing ones. -/
def replayTranscriptAtAccess (input coins : List Bool) (messageCount : ℕ)
    (replies : ℕ → List Bool) : Bool :=
  let p := protocolPrime (((decodeQBF input).map nodeCount).getD 0)
  let degree := max 2 (((decodePrenex input).map (fun φ => nodeCount φ.matrix)).getD 0)
  let count := ((decodePrenex input).map (fun φ => φ.schedule.length)).getD 0
  if (decodeClosedPrenex input).isSome ∧ messageCount = 2 * encodedRoundBudget input then
    replayVerdictBits p (prenexMatrixBits input)
      (replayClaimBitsLoop p degree
        (fun i => scheduleTokenKind (decodedScheduleTokenAt i input))
        (fun i => syntaxTokenNameDigits (decodedScheduleTokenAt i input)) replies
        (fun i => rawCoinChallengeBits p i coins)
        (true :: pair [] (roundConstantBits p 1)) count)
  else false

theorem replayTranscriptAtAccess_mem_FP {input coins : List Bool → List Bool}
    {messageCount : List Bool → ℕ} {replies : List Bool → ℕ → List Bool}
    (hinput : input ∈ FP) (hcoins : coins ∈ FP) (hcount : UnaryFn messageCount)
    (hreplies : (fun w => replies (pairFst w) (pairSnd w).length) ∈ FP) :
    (fun z => [replayTranscriptAtAccess (input z) (coins z) (messageCount z) (replies z)]) ∈ FP := by
  have hp := decodedProtocolPrime_unaryFn hinput
  have hnz : ∀ z, protocolPrime (((decodeQBF (input z)).map nodeCount).getD 0) ≠ 0 :=
    fun _ => (protocolPrime_spec _).1.ne_zero
  have hd := (UnaryFn.const 2).max (decodePrenex_matrixNodeCount_unaryFn hinput)
  have hc := decodePrenex_scheduleLength_unaryFn hinput
  have hk := decodedScheduleKind_unaryFn UnaryFn.index (mem_FP_comp pairFst_mem_FP hinput)
  have hi := decodedScheduleCoordinate_bits_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hinput)
  have hr := rawCoinChallengeBits_mem_FP hp.lift (fun z => hnz (pairFst z)) UnaryFn.index
    (mem_FP_comp pairFst_mem_FP hcoins)
  have hinit := mem_FP_comp (mem_FP_pair (constFn_mem_FP [])
    (reduceResidueWord_bits_mem_FP hp (UnaryFn.const 1))) (Cobham.cons_mem_FP true)
  have hloop := replayClaimBitsLoop_mem_FP
    (kind := fun z i => scheduleTokenKind (decodedScheduleTokenAt i (input z)))
    (key := fun z i => syntaxTokenNameDigits (decodedScheduleTokenAt i (input z)))
    (challenge := fun z i => rawCoinChallengeBits
      (protocolPrime (((decodeQBF (input z)).map nodeCount).getD 0)) i (coins z))
    hp hd hc hk hi hreplies hr hinit
  have hv := replayVerdictBits_mem_FP hp (prenexMatrixBits_mem_FP hinput) hloop
  have hlen := (UnaryFn.length hinput).add (UnaryFn.const 1)
  have hbudget : UnaryFn fun z => ((input z).length + 1) ^ 2 :=
    (hlen.mul hlen).of_eq (fun _ => by rw [pow_two])
  have hguard := (decodeClosedPrenex_success_fppred hinput).and
    (FPPred.eq hcount ((UnaryFn.const 2).mul hbudget))
  apply mem_FP_of_eq (hguard.ite_mem_FP hv (constFn_mem_FP [false]))
  intro z
  dsimp only [replayTranscriptAtAccess, encodedRoundBudget, Function.comp_apply]
  split <;> rename_i h <;> simp only [h, ite_false]
  rfl

/-- Instantiate every indexed accessor by the existing input schedule, odd
transcript messages, and private tape. No reachability assumption is required. -/
theorem replayTranscriptAtAccess_eq (input coins : List Bool) (history : List (List Bool)) :
    replayTranscriptAtAccess input coins history.length
      (fun i => history[2 * i + 1]?.getD []) = rawTranscriptVerdict input coins history := by
  cases hd : decodeClosedPrenex input with
  | none =>
    simp only [replayTranscriptAtAccess, hd, Option.isSome_none, Bool.false_eq_true,
      false_and, ↓reduceIte]
    exact (rawTranscriptVerdict_invalid input coins history hd).symm
  | some φ =>
    have he := (decodeClosedPrenex_eq_some_iff input φ).mp hd
    have hq : decodeQBF input = some φ.val.toQBF := by rw [← he]; simp
    have hp : decodePrenex input = some φ.val := by rw [← he]; simp
    have hm : prenexMatrixBits input = encodeQBF φ.val.matrix := by rw [← he]; simp
    let prime := protocolPrime (nodeCount φ.val.toQBF)
    let : NeZero prime := ⟨(protocolPrime_spec _).1.ne_zero⟩
    rw [rawTranscriptVerdict, encodedTranscriptVerdict_decoded input _ history φ hd]
    dsimp only [replayTranscriptAtAccess]
    simp only [hd, hq, hp, Option.isSome_some, Option.map_some, Option.getD_some, true_and, hm]
    by_cases hshape : history.length = 2 * encodedRoundBudget input
    · rw [ite_eq_left hshape, ite_eq_left hshape]
      let ops : ℕ → AlgebraicOperator := fun i => φ.val.schedule[i]?.getD (.reduce 0)
      let replies := transcriptReplies φ.val.schedule.length history
      let words := decodedTapeWords input (coinTapeFromList input coins) φ hd
      have hk (i : ℕ) (hi : i < φ.val.schedule.length) :
          scheduleTokenKind (decodedScheduleTokenAt i input) = (ops i).roundKind := by
        simpa only [ops, List.getElem?_eq_getElem hi, Option.getD_some] using
          decodedScheduleKind_eq i input φ.val hp φ.val.schedule[i]
            (List.getElem?_eq_getElem hi)
      have hi (i : ℕ) (hlt : i < φ.val.schedule.length) :
          syntaxTokenNameDigits (decodedScheduleTokenAt i input) = (ops i).coordinate.bits := by
        simpa only [ops, List.getElem?_eq_getElem hlt, Option.getD_some] using
          decodedScheduleCoordinate_eq i input φ.val hp φ.val.schedule[i]
            (List.getElem?_eq_getElem hlt)
      have hr (i : ℕ) (hi : i < φ.val.schedule.length) :
          history[2 * i + 1]?.getD [] = replies[i]?.getD [] := by
        simp [replies, transcriptReplies, List.getElem?_map, List.getElem?_range hi]
      have hc (i : ℕ) (hi : i < φ.val.schedule.length) :
          rawCoinChallengeBits prime i coins = wordBits (encodeResidue (sampleResidue prime (words i))) := by
        rw [show words i = rawCoinWord prime i coins from decodedTapeWords_raw_eq input coins φ hd i hi]
        rfl
      have hinit : true :: pair [] (roundConstantBits prime 1) =
          encodeReplayClaim (some (finiteInitialClaim (R := ZMod prime))) := by
        simp [encodeReplayClaim, encodeFiniteClaim, finiteInitialClaim, encodeAssignmentEntries]
      change replayVerdictBits prime (encodeQBF φ.val.matrix) _ = _
      rw [replayClaimBitsLoop_congr prime _ _ _ _ _ _ _ _ _ _ _ hk hi hr hc, hinit,
        replayClaimBitsLoop_encode, replayVerdictBits_encode _ φ.val.matrix_quantifierFree]
      exact (verifyReplyList_eq_replayClaimRun prime (max 2 (nodeCount φ.val.matrix))
        (fun x => matrixEvalWithCost x φ.val.matrix φ.val.matrix_quantifierFree)
        φ.val.schedule finiteInitialClaim replies words
        (by simp [replies, transcriptReplies])).symm
    · simp [hshape]

/-- Actual FP runtime of the original raw final-verdict function, from
polynomial-time history count and indexed odd-message access. -/
theorem rawTranscriptVerdict_mem_FP_of_access {input coins : List Bool → List Bool}
    (history : List Bool → List (List Bool)) (hinput : input ∈ FP) (hcoins : coins ∈ FP)
    (hcount : UnaryFn fun z => (history z).length)
    (hreplies : (fun w => (history (pairFst w))[2 * (pairSnd w).length + 1]?.getD []) ∈ FP) :
    (fun z => [rawTranscriptVerdict (input z) (coins z) (history z)]) ∈ FP :=
  mem_FP_of_eq (replayTranscriptAtAccess_mem_FP hinput hcoins hcount hreplies)
    (fun z => congrArg (fun b => [b]) (replayTranscriptAtAccess_eq (input z) (coins z) (history z)))

/-- The exact existing raw verdict is polynomial-time from the canonical
upstream transcript encoding, without a premise about history reachability. -/
theorem rawTranscriptVerdict_mem_FP {input coins : List Bool → List Bool}
    (history : List Bool → List (List Bool)) (hinput : input ∈ FP) (hcoins : coins ∈ FP)
    (hhistory : (fun z => encodeViewTranscript (history z)) ∈ FP) :
    (fun z => [rawTranscriptVerdict (input z) (coins z) (history z)]) ∈ FP := by
  have hcount : UnaryFn fun z => (history z).length :=
    (viewTranscriptCount_unaryFn hhistory).of_eq (fun z => viewTranscriptCount_encode (history z))
  have hreply := viewTranscriptMessage_mem_FP
    (((UnaryFn.const 2).mul UnaryFn.index).add (UnaryFn.const 1))
    (mem_FP_comp pairFst_mem_FP hhistory)
  apply rawTranscriptVerdict_mem_FP_of_access history hinput hcoins hcount
  exact mem_FP_of_eq hreply (fun w => viewTranscriptMessage_encode _ (history (pairFst w)))

/-- Complete transcript decoding followed by the original raw verdict. This
single-string transcript interface rejects malformed or trailing encodings. -/
def decodedTranscriptVerdict (input coins historyBits : List Bool) : Bool :=
  match decodeViewTranscript historyBits with
  | none => false
  | some history => rawTranscriptVerdict input coins history

theorem decodedTranscriptVerdict_mem_FP {input coins historyBits : List Bool → List Bool}
    (hinput : input ∈ FP) (hcoins : coins ∈ FP) (hhistory : historyBits ∈ FP) :
    (fun z => [decodedTranscriptVerdict (input z) (coins z) (historyBits z)]) ∈ FP := by
  have hreplies := viewTranscriptMessage_mem_FP
    (((UnaryFn.const 2).mul UnaryFn.index).add (UnaryFn.const 1))
    (mem_FP_comp pairFst_mem_FP hhistory)
  have hv := replayTranscriptAtAccess_mem_FP
    (replies := fun z i => viewTranscriptMessage (2 * i + 1) (historyBits z)) hinput hcoins
    (viewTranscriptCount_unaryFn hhistory) hreplies
  apply mem_FP_of_eq ((decodeViewTranscript_success_fppred hhistory).ite_mem_FP hv
    (constFn_mem_FP [false]))
  intro z
  cases hd : decodeViewTranscript (historyBits z) with
  | none => simp [decodedTranscriptVerdict, hd]
  | some history =>
    have he := decodeViewTranscript_sound (historyBits z) history hd
    simp only [hd, Option.isSome_some, ↓reduceIte, decodedTranscriptVerdict]
    rw [← he]
    simp only [viewTranscriptCount_encode, viewTranscriptMessage_encode]
    rw [replayTranscriptAtAccess_eq]

@[simp] theorem decodedTranscriptVerdict_encode (input coins : List Bool)
    (history : List (List Bool)) :
    decodedTranscriptVerdict input coins (encodeViewTranscript history) =
      rawTranscriptVerdict input coins history := by simp [decodedTranscriptVerdict]

end IPPSPACE

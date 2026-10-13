/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.SyntaxTokenFP

/-!
# Scanning complete QBF syntax and counting nodes

The scanner tracks the number of pending child formulas while consuming exact
constructor tokens. Full consumption is checked separately. Binary names stay
encoded throughout the machine-time construction.
-/

namespace IPPSPACE

open Complexity

def encodeQBFList (formulas : List QBF) : List Bool := formulas.flatMap encodeQBF

def qbfListNodes (formulas : List QBF) : ℕ := (formulas.map nodeCount).sum

@[simp] theorem encodeQBFList_nil : encodeQBFList [] = [] := rfl
@[simp] theorem encodeQBFList_cons (formula : QBF) (formulas : List QBF) :
    encodeQBFList (formula :: formulas) = encodeQBF formula ++ encodeQBFList formulas := rfl
@[simp] theorem qbfListNodes_nil : qbfListNodes [] = 0 := rfl
@[simp] theorem qbfListNodes_cons (formula : QBF) (formulas : List QBF) :
    qbfListNodes (formula :: formulas) = nodeCount formula + qbfListNodes formulas := rfl

/-- Satisfy `pending` formula obligations, consuming at most `fuel` tokens.
The returned number counts exactly the consumed syntax nodes. -/
def scanSyntax : ℕ → ℕ → List Bool → Option (ℕ × List Bool)
  | _, 0, bits => some (0, bits)
  | 0, _ + 1, _ => none
  | fuel + 1, pending + 1, bits => do
      let token ← parseSyntaxToken bits
      let rest ← scanSyntax fuel (pending + token.1.arity) token.2
      some (rest.1 + 1, rest.2)

@[simp] theorem scanSyntax_zero_pending (fuel : ℕ) (bits : List Bool) :
    scanSyntax fuel 0 bits = some (0, bits) := by cases fuel <;> rfl

theorem scanSyntax_token (token : SyntaxToken) (fuel pending : ℕ) (bits : List Bool) :
    scanSyntax (fuel + 1) (pending + 1) (token.encode ++ bits) =
      (scanSyntax fuel (pending + token.arity) bits).map (fun rest => (rest.1 + 1, rest.2)) := by
  simp only [scanSyntax, parseSyntaxToken_encode, Option.bind_eq_bind, Option.bind_some]
  cases scanSyntax fuel (pending + token.arity) bits <;> rfl

private theorem prepend_token_forest (token : SyntaxToken) (pending : ℕ) (tail : List QBF)
    (hlen : tail.length = pending + token.arity) :
    ∃ formulas : List QBF, formulas.length = pending + 1 ∧
      encodeQBFList formulas = token.encode ++ encodeQBFList tail ∧
      qbfListNodes formulas = qbfListNodes tail + 1 := by
  cases token with
  | var n => exact ⟨.var n :: tail, by simpa [SyntaxToken.arity] using hlen,
      rfl, by simp [nodeCount, Nat.add_comm]⟩
  | tru => exact ⟨.tru :: tail, by simpa [SyntaxToken.arity] using hlen,
      rfl, by simp [nodeCount, Nat.add_comm]⟩
  | fls => exact ⟨.fls :: tail, by simpa [SyntaxToken.arity] using hlen,
      rfl, by simp [nodeCount, Nat.add_comm]⟩
  | neg =>
    cases tail with
    | nil => simp [SyntaxToken.arity] at hlen
    | cons child tail =>
      refine ⟨.neg child :: tail, hlen, ?_, ?_⟩
      · rfl
      · simp only [qbfListNodes_cons, nodeCount]; omega
  | ex n =>
    cases tail with
    | nil => simp [SyntaxToken.arity] at hlen
    | cons child tail =>
      refine ⟨.ex n child :: tail, hlen, ?_, ?_⟩
      · simp [SyntaxToken.encode, encodeQBF, List.append_assoc]
      · simp only [qbfListNodes_cons, nodeCount]; omega
  | all n =>
    cases tail with
    | nil => simp [SyntaxToken.arity] at hlen
    | cons child tail =>
      refine ⟨.all n child :: tail, hlen, ?_, ?_⟩
      · simp [SyntaxToken.encode, encodeQBF, List.append_assoc]
      · simp only [qbfListNodes_cons, nodeCount]; omega
  | conj =>
    cases tail with
    | nil => simp [SyntaxToken.arity] at hlen
    | cons left tail =>
      cases tail with
      | nil => simp [SyntaxToken.arity] at hlen
      | cons right tail =>
        refine ⟨.conj left right :: tail, ?_, ?_, ?_⟩
        · simp only [List.length_cons, SyntaxToken.arity] at hlen ⊢; omega
        · simp [SyntaxToken.encode, encodeQBF, List.append_assoc]
        · simp only [qbfListNodes_cons, nodeCount]; omega
  | disj =>
    cases tail with
    | nil => simp [SyntaxToken.arity] at hlen
    | cons left tail =>
      cases tail with
      | nil => simp [SyntaxToken.arity] at hlen
      | cons right tail =>
        refine ⟨.disj left right :: tail, ?_, ?_, ?_⟩
        · simp only [List.length_cons, SyntaxToken.arity] at hlen ⊢; omega
        · simp [SyntaxToken.encode, encodeQBF, List.append_assoc]
        · simp only [qbfListNodes_cons, nodeCount]; omega

/-- Success reconstructs an actual forest of upstream QBFs, with exact bytes
and exact node count. No mere balance condition is substituted for syntax. -/
theorem scanSyntax_sound (fuel pending : ℕ) (bits suffix : List Bool) (count : ℕ)
    (h : scanSyntax fuel pending bits = some (count, suffix)) :
    ∃ formulas : List QBF, formulas.length = pending ∧
      encodeQBFList formulas ++ suffix = bits ∧ qbfListNodes formulas = count := by
  induction fuel generalizing pending bits suffix count with
  | zero =>
    cases pending with
    | zero =>
      have heq : (0, bits) = (count, suffix) := Option.some.inj h
      cases heq
      exact ⟨[], rfl, rfl, rfl⟩
    | succ pending => simp [scanSyntax] at h
  | succ fuel ih =>
    cases pending with
    | zero =>
      have heq : (0, bits) = (count, suffix) := Option.some.inj h
      cases heq
      exact ⟨[], rfl, rfl, rfl⟩
    | succ pending =>
      cases ht : parseSyntaxToken bits with
      | none => simp [scanSyntax, ht] at h
      | some token =>
        rcases token with ⟨token, rest⟩
        cases hs : scanSyntax fuel (pending + token.arity) rest with
        | none => simp [scanSyntax, ht, hs] at h
        | some result =>
          rcases result with ⟨nodes, suffix'⟩
          have heq : (nodes + 1, suffix') = (count, suffix) := by simpa [scanSyntax, ht, hs] using h
          cases heq
          obtain ⟨tail, hlen, hbytes, hnodes⟩ := ih _ _ _ _ hs
          obtain ⟨formulas, hlen', hbytes', hnodes'⟩ := prepend_token_forest token pending tail hlen
          refine ⟨formulas, hlen', ?_, hnodes'.trans (congrArg (· + 1) hnodes)⟩
          rw [hbytes', List.append_assoc, hbytes]
          exact parseSyntaxToken_sound bits rest token ht

/-- A complete formula consumes exactly its syntax-node count, leaving the
remaining obligations and suffix to the same scanner. -/
theorem scanSyntax_encode (formula : QBF) (fuel pending : ℕ) (bits : List Bool) :
    scanSyntax (nodeCount formula + fuel) (pending + 1) (encodeQBF formula ++ bits) =
      (scanSyntax fuel pending bits).map (fun result => (result.1 + nodeCount formula, result.2)) := by
  induction formula generalizing fuel pending bits with
  | var n =>
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, SyntaxToken.arity, Nat.add_comm] using
      scanSyntax_token (.var n) fuel pending bits
  | tru =>
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, SyntaxToken.arity, Nat.add_comm] using
      scanSyntax_token .tru fuel pending bits
  | fls =>
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, SyntaxToken.arity, Nat.add_comm] using
      scanSyntax_token .fls fuel pending bits
  | neg formula ih =>
    have h := scanSyntax_token .neg (nodeCount formula + fuel) pending (encodeQBF formula ++ bits)
    simp only [SyntaxToken.arity] at h
    rw [ih] at h
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, Option.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | ex name formula ih =>
    have h := scanSyntax_token (.ex name) (nodeCount formula + fuel) pending (encodeQBF formula ++ bits)
    simp only [SyntaxToken.arity] at h
    rw [ih] at h
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, List.append_assoc, Option.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | all name formula ih =>
    have h := scanSyntax_token (.all name) (nodeCount formula + fuel) pending (encodeQBF formula ++ bits)
    simp only [SyntaxToken.arity] at h
    rw [ih] at h
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, List.append_assoc, Option.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | conj left right ihleft ihright =>
    have h := scanSyntax_token .conj (nodeCount left + (nodeCount right + fuel)) pending
      (encodeQBF left ++ (encodeQBF right ++ bits))
    simp only [SyntaxToken.arity] at h
    rw [show pending + 2 = (pending + 1) + 1 by omega, ihleft, ihright] at h
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, List.append_assoc, Option.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | disj left right ihleft ihright =>
    have h := scanSyntax_token .disj (nodeCount left + (nodeCount right + fuel)) pending
      (encodeQBF left ++ (encodeQBF right ++ bits))
    simp only [SyntaxToken.arity] at h
    rw [show pending + 2 = (pending + 1) + 1 by omega, ihleft, ihright] at h
    simpa [nodeCount, SyntaxToken.encode, encodeQBF, List.append_assoc, Option.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Validate exactly one complete formula and return its syntax-node count. -/
def syntaxNodeCount (bits : List Bool) : Option ℕ := do
  let result ← scanSyntax bits.length 1 bits
  if result.2 = [] then some result.1 else none

theorem syntaxNodeCount_encode (formula : QBF) :
    syntaxNodeCount (encodeQBF formula) = some (nodeCount formula) := by
  have h := scanSyntax_encode formula ((encodeQBF formula).length - nodeCount formula) 0 []
  rw [Nat.add_sub_of_le (nodeCount_le_length_encodeQBF formula)] at h
  simp only [Nat.zero_add, List.append_nil, scanSyntax_zero_pending, Option.map_some,
    Nat.zero_add] at h
  simp [syntaxNodeCount, h]

theorem syntaxNodeCount_sound (bits : List Bool) (count : ℕ)
    (h : syntaxNodeCount bits = some count) :
    ∃ formula : QBF, encodeQBF formula = bits ∧ nodeCount formula = count := by
  cases hs : scanSyntax bits.length 1 bits with
  | none => simp [syntaxNodeCount, hs] at h
  | some result =>
    rcases result with ⟨nodes, suffix⟩
    by_cases hempty : suffix = []
    · subst suffix
      have hcount : nodes = count := by simpa [syntaxNodeCount, hs] using h
      obtain ⟨formulas, hlen, hbytes, hnodes⟩ := scanSyntax_sound bits.length 1 bits [] nodes hs
      cases formulas with
      | nil => simp at hlen
      | cons formula rest =>
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst rest
        exact ⟨formula, by simpa using hbytes, by simpa using hnodes.trans hcount⟩
    · simp [syntaxNodeCount, hs, hempty] at h

/-- Exact agreement with the existing full-consumption QBF decoder. -/
theorem syntaxNodeCount_eq_decodeQBF (bits : List Bool) :
    syntaxNodeCount bits = (decodeQBF bits).map nodeCount := by
  cases hdecode : decodeQBF bits with
  | none =>
    cases hcount : syntaxNodeCount bits with
    | none => rfl
    | some count =>
      obtain ⟨formula, hbytes, _⟩ := syntaxNodeCount_sound bits count hcount
      rw [← hbytes, decodeQBF_encodeQBF] at hdecode
      contradiction
  | some formula =>
    have hbytes := (decodeQBF_eq_some_iff bits formula).mp hdecode
    rw [← hbytes, syntaxNodeCount_encode]
    rfl

structure SyntaxScanState where
  pending : ℕ
  count : ℕ
  remaining : List Bool

/-- One constructor step; completion and failure are absorbing states. -/
def syntaxScannerStep : Option SyntaxScanState → Option SyntaxScanState
  | none => none
  | some state =>
      if state.pending = 0 then some state
      else (parseSyntaxToken state.remaining).map (fun token =>
        ⟨state.pending - 1 + token.1.arity, state.count + 1, token.2⟩)

def syntaxScannerResult : Option SyntaxScanState → Option (ℕ × List Bool)
  | none => none
  | some state => if state.pending = 0 then some (state.count, state.remaining) else none

@[simp] theorem syntaxScannerStep_iterate_none (fuel : ℕ) :
    syntaxScannerStep^[fuel] none = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem syntaxScannerResult_iterate (fuel pending count : ℕ) (bits : List Bool) :
    syntaxScannerResult (syntaxScannerStep^[fuel] (some ⟨pending, count, bits⟩)) =
      (scanSyntax fuel pending bits).map (fun result => (count + result.1, result.2)) := by
  induction fuel generalizing pending count bits with
  | zero => cases pending <;> simp [syntaxScannerResult, scanSyntax]
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    cases pending with
    | zero => simp [syntaxScannerStep, ih, scanSyntax]
    | succ pending =>
      cases ht : parseSyntaxToken bits with
      | none => simp [syntaxScannerStep, ht, syntaxScannerResult, scanSyntax]
      | some token =>
        rcases token with ⟨token, suffix⟩
        simp only [syntaxScannerStep, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          ↓reduceIte, ht, Option.map_some, Nat.add_sub_cancel]
        rw [ih]
        cases hs : scanSyntax fuel (pending + token.arity) suffix <;>
          simp [scanSyntax, ht, hs, Nat.add_comm, Nat.add_left_comm]

/-- Unary counters and the remaining input have a linear-size tagged encoding. -/
def encodeSyntaxScanState : Option SyntaxScanState → List Bool
  | none => []
  | some state => true :: pair (List.replicate state.pending true)
      (pair (List.replicate state.count true) state.remaining)

@[simp] theorem length_encodeSyntaxScanState (state : SyntaxScanState) :
    (encodeSyntaxScanState (some state)).length =
      2 * state.pending + 2 * state.count + state.remaining.length + 5 := by
  simp [encodeSyntaxScanState]
  omega

def syntaxStatePending (bits : List Bool) : ℕ := (pairFst (bits.drop 1)).length
def syntaxStateCount (bits : List Bool) : ℕ := (pairFst (pairSnd (bits.drop 1))).length
def syntaxStateRemaining (bits : List Bool) : List Bool := pairSnd (pairSnd (bits.drop 1))

@[simp] theorem syntaxStatePending_encode (state : SyntaxScanState) :
    syntaxStatePending (encodeSyntaxScanState (some state)) = state.pending := by
  simp [syntaxStatePending, encodeSyntaxScanState]

@[simp] theorem syntaxStateCount_encode (state : SyntaxScanState) :
    syntaxStateCount (encodeSyntaxScanState (some state)) = state.count := by
  simp [syntaxStateCount, encodeSyntaxScanState]

@[simp] theorem syntaxStateRemaining_encode (state : SyntaxScanState) :
    syntaxStateRemaining (encodeSyntaxScanState (some state)) = state.remaining := by
  simp [syntaxStateRemaining, encodeSyntaxScanState]

def syntaxScannerBitsStep (bits : List Bool) : List Bool :=
  if bits = [] then []
  else if syntaxStatePending bits = 0 then bits
  else if (parseSyntaxToken (syntaxStateRemaining bits)).isSome then
    encodeSyntaxScanState (some
      ⟨syntaxStatePending bits - 1 + syntaxTokenArity (syntaxStateRemaining bits),
        syntaxStateCount bits + 1, syntaxTokenSuffix (syntaxStateRemaining bits)⟩)
  else []

theorem syntaxScannerBitsStep_encode (state : Option SyntaxScanState) :
    syntaxScannerBitsStep (encodeSyntaxScanState state) = encodeSyntaxScanState (syntaxScannerStep state) := by
  cases state with
  | none => simp [encodeSyntaxScanState, syntaxScannerBitsStep, syntaxScannerStep]
  | some state =>
    have hne : encodeSyntaxScanState (some state) ≠ [] := by simp [encodeSyntaxScanState]
    simp only [syntaxScannerBitsStep, hne, ↓reduceIte, syntaxStatePending_encode,
      syntaxStateCount_encode, syntaxStateRemaining_encode]
    by_cases hp : state.pending = 0
    · simp [syntaxScannerStep, hp]
    · cases ht : parseSyntaxToken state.remaining with
      | none => simp [syntaxScannerStep, hp, ht, encodeSyntaxScanState]
      | some token =>
        rcases token with ⟨token, suffix⟩
        have hs := syntaxTokenSuffix_eq state.remaining suffix token ht
        have ha := syntaxTokenArity_eq state.remaining suffix token ht
        simp [syntaxScannerStep, hp, ht, hs, ha]

theorem syntaxScannerStep_length_le (state : Option SyntaxScanState) :
    (encodeSyntaxScanState (syntaxScannerStep state)).length ≤ (encodeSyntaxScanState state).length + 4 := by
  cases state with
  | none => simp [syntaxScannerStep, encodeSyntaxScanState]
  | some state =>
    by_cases hp : state.pending = 0
    · simp [syntaxScannerStep, hp]
    · cases ht : parseSyntaxToken state.remaining with
      | none => simp [syntaxScannerStep, hp, ht, encodeSyntaxScanState]
      | some token =>
        rcases token with ⟨token, suffix⟩
        have hlen := parseSyntaxToken_suffix_length state.remaining suffix token ht
        have ha := token.arity_le
        simp only [syntaxScannerStep, hp, ↓reduceIte, ht, Option.map_some, length_encodeSyntaxScanState]
        omega

theorem syntaxStatePending_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => syntaxStatePending (bits z) :=
  UnaryFn.length (mem_FP_comp (drop_mem_FP hbits (UnaryFn.const 1)) pairFst_mem_FP)

theorem syntaxStateCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => syntaxStateCount (bits z) :=
  UnaryFn.length (mem_FP_comp
    (mem_FP_comp (drop_mem_FP hbits (UnaryFn.const 1)) pairSnd_mem_FP) pairFst_mem_FP)

theorem syntaxStateRemaining_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => syntaxStateRemaining (bits z)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (drop_mem_FP hbits (UnaryFn.const 1)) pairSnd_mem_FP) pairSnd_mem_FP

theorem syntaxScannerBitsStep_mem_FP : syntaxScannerBitsStep ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hremaining := syntaxStateRemaining_mem_FP hid
  have hpending := syntaxStatePending_unaryFn hid
  have hcount := syntaxStateCount_unaryFn hid
  have hnextPending := (hpending.sub (UnaryFn.const 1)).add (syntaxTokenArity_unaryFn hremaining)
  have hnextCount := hcount.add (UnaryFn.const 1)
  have hnext := mem_FP_comp
    (mem_FP_pair hnextPending.mem_FP
      (mem_FP_pair hnextCount.mem_FP (syntaxTokenSuffix_mem_FP hremaining)))
    (Cobham.cons_mem_FP true)
  have h := (FPPred.eq (UnaryFn.length hid) (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP [])
    ((FPPred.eq hpending (UnaryFn.const 0)).ite_mem_FP hid
      ((parseSyntaxToken_success_fppred hremaining).ite_mem_FP hnext (constFn_mem_FP [])))
  apply mem_FP_of_eq h
  intro bits
  simp only [id_eq, Function.comp_apply, List.length_eq_zero_iff,
    syntaxScannerBitsStep, encodeSyntaxScanState]

def syntaxScanStateRun (fuel pending : ℕ) (bits : List Bool) : List Bool :=
  encodeSyntaxScanState (syntaxScannerStep^[fuel] (some ⟨pending, 0, bits⟩))

/-- The complete bounded scanner is an actual polynomial-time string function.
The state grows by at most four bits per constructor step. -/
theorem syntaxScanStateRun_mem_FP {fuel pending : List Bool → ℕ} {bits : List Bool → List Bool}
    (hfuel : UnaryFn fuel) (hpending : UnaryFn pending) (hbits : bits ∈ FP) :
    (fun z => syntaxScanStateRun (fuel z) (pending z) (bits z)) ∈ FP := by
  have hinit : (fun z => encodeSyntaxScanState (some ⟨pending z, 0, bits z⟩)) ∈ FP :=
    mem_FP_comp (mem_FP_pair hpending.mem_FP (mem_FP_pair (constFn_mem_FP []) hbits))
      (Cobham.cons_mem_FP true)
  have hsemi : Function.Semiconj encodeSyntaxScanState syntaxScannerStep syntaxScannerBitsStep :=
    fun state => (syntaxScannerBitsStep_encode state).symm
  have h := iterate_mem_FP_of_step_le syntaxScannerBitsStep_mem_FP hinit hfuel.mem_FP 4
    (fun z n _ => by
      rw [← hsemi.iterate_right (n + 1), ← hsemi.iterate_right n, Function.iterate_succ_apply']
      exact syntaxScannerStep_length_le _)
  apply mem_FP_of_eq h
  intro z
  simpa only [List.length_replicate, syntaxScanStateRun] using
    (hsemi.iterate_right (fuel z) (some ⟨pending z, 0, bits z⟩)).symm

/-- A complete successful state has no pending children and no trailing bits. -/
def SyntaxStateComplete (bits : List Bool) : Prop :=
  bits ≠ [] ∧ syntaxStatePending bits = 0 ∧ syntaxStateRemaining bits = []

instance (bits : List Bool) : Decidable (SyntaxStateComplete bits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[simp] theorem syntaxStateComplete_nil : ¬ SyntaxStateComplete [] := by
  simp [SyntaxStateComplete]

@[simp] theorem syntaxStateComplete_encode (state : SyntaxScanState) :
    SyntaxStateComplete (encodeSyntaxScanState (some state)) ↔
      state.pending = 0 ∧ state.remaining = [] := by
  unfold SyntaxStateComplete
  rw [syntaxStatePending_encode, syntaxStateRemaining_encode]
  simp [encodeSyntaxScanState]

private theorem syntaxScannerResult_finish (state : Option SyntaxScanState) :
    ((syntaxScannerResult state).bind (fun result =>
      if result.2 = [] then some result.1 else none)) =
      if SyntaxStateComplete (encodeSyntaxScanState state) then
        some (syntaxStateCount (encodeSyntaxScanState state)) else none := by
  cases state with
  | none => simp [syntaxScannerResult, encodeSyntaxScanState]
  | some state =>
    simp only [syntaxScannerResult, syntaxStateComplete_encode, syntaxStateCount_encode]
    by_cases hp : state.pending = 0 <;> by_cases hr : state.remaining = [] <;> simp [hp, hr]

theorem syntaxNodeCount_eq_state (bits : List Bool) :
    syntaxNodeCount bits =
      if SyntaxStateComplete (syntaxScanStateRun bits.length 1 bits) then
        some (syntaxStateCount (syntaxScanStateRun bits.length 1 bits)) else none := by
  have hscan := syntaxScannerResult_iterate bits.length 1 0 bits
  have hscan' : syntaxScannerResult
      (syntaxScannerStep^[bits.length] (some ⟨1, 0, bits⟩)) =
      scanSyntax bits.length 1 bits := by
    rw [hscan]
    cases scanSyntax bits.length 1 bits with
    | none => rfl
    | some result => cases result; simp only [Option.map_some, Nat.zero_add]
  unfold syntaxNodeCount
  rw [← hscan']
  exact syntaxScannerResult_finish _

theorem syntaxStateComplete_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => SyntaxStateComplete (bits z) :=
  ((FPPred.eq (UnaryFn.length hbits) (UnaryFn.const 0)).not).and
    ((FPPred.eq (syntaxStatePending_unaryFn hbits) (UnaryFn.const 0)).and
      ((FPPred.eq (UnaryFn.length (syntaxStateRemaining_mem_FP hbits)) (UnaryFn.const 0)).of_iff
        (fun _ => List.length_eq_zero_iff))) |>.of_iff (fun z => by
          simp only [SyntaxStateComplete, List.length_eq_zero_iff])

/-- Actual polynomial-time validation of the existing complete QBF decoder,
including arbitrary binary names and every malformed or trailing input. -/
theorem decodeQBF_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (decodeQBF (bits z)).isSome = true := by
  have hrun := syntaxScanStateRun_mem_FP (UnaryFn.length hbits) (UnaryFn.const 1) hbits
  refine (syntaxStateComplete_fppred hrun).of_iff (fun z => ?_)
  have heq : (decodeQBF (bits z)).isSome =
      (syntaxNodeCount (bits z)).isSome := by rw [syntaxNodeCount_eq_decodeQBF]; simp
  rw [heq, syntaxNodeCount_eq_state]
  split <;> simp_all

/-- The exact decoded formula's node count is unary polynomial-time; invalid
inputs return zero. Numeric variable-name values need no unary bound. -/
theorem decodeQBF_nodeCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => ((decodeQBF (bits z)).map nodeCount).getD 0 := by
  have hrun := syntaxScanStateRun_mem_FP (UnaryFn.length hbits) (UnaryFn.const 1) hbits
  have h := UnaryFn.ite (syntaxStateComplete_fppred hrun)
    (syntaxStateCount_unaryFn hrun) (UnaryFn.const 0)
  apply h.of_eq
  intro z
  rw [← syntaxNodeCount_eq_decodeQBF, syntaxNodeCount_eq_state]
  split <;> rfl

/-- Canonically serialized full decoder output, distinguished from failure. -/
def decodeQBFOutput (bits : List Bool) : List Bool :=
  match decodeQBF bits with
  | none => []
  | some formula => true :: encodeQBF formula

theorem decodeQBFOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodeQBFOutput (bits z)) ∈ FP := by
  have h := (decodeQBF_success_fppred hbits).ite_mem_FP
    (mem_FP_comp hbits (Cobham.cons_mem_FP true)) (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro z
  cases hd : decodeQBF (bits z) with
  | none => simp [decodeQBFOutput, hd]
  | some formula =>
    have heq := (decodeQBF_eq_some_iff (bits z) formula).mp hd
    simp [decodeQBFOutput, hd, heq]

@[simp] theorem decodeQBFOutput_encodeQBF (formula : QBF) :
    decodeQBFOutput (encodeQBF formula) = true :: encodeQBF formula := by
  simp [decodeQBFOutput]

theorem decodeQBFOutput_eq_nil_iff (bits : List Bool) :
    decodeQBFOutput bits = [] ↔ decodeQBF bits = none := by
  cases hd : decodeQBF bits <;> simp [decodeQBFOutput, hd]

end IPPSPACE

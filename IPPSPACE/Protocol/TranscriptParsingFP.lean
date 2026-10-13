/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.ViewParsingFP

/-!
# Polynomial-time transcript message extraction

A forward transducer reuses the exact fixed-depth transcript automaton. It
counts message openings and emits the requested message's decoded bits. The
public wrappers retain the original full-consumption validating decoder, so
malformed histories cannot be mistaken for valid prefixes.
-/

namespace IPPSPACE

open Complexity

structure TranscriptReadState where
  scanner : ViewScanState
  count : ℕ
  output : List Bool
  deriving DecidableEq

def transcriptReadStep (index : ℕ) (state : TranscriptReadState) (bit : Bool) : TranscriptReadState :=
  ⟨viewScanStep state.scanner bit,
    if state.scanner = .between ∧ bit = false then state.count + 1 else state.count,
    if state.count = index + 1 ∧ bit = true then
      if state.scanner = .bit then state.output ++ [false]
      else if state.scanner = .trueLast then state.output ++ [true] else state.output
    else state.output⟩

def transcriptReadFold (index : ℕ) (bits : List Bool) (state : TranscriptReadState) :
    TranscriptReadState := bits.foldl (transcriptReadStep index) state

@[simp] theorem transcriptReadFold_nil (index : ℕ) (state : TranscriptReadState) :
    transcriptReadFold index [] state = state := rfl

@[simp] theorem transcriptReadFold_append (index : ℕ) (left right : List Bool)
    (state : TranscriptReadState) :
    transcriptReadFold index (left ++ right) state =
      transcriptReadFold index right (transcriptReadFold index left state) := by
  exact List.foldl_append

theorem transcriptReadFold_boolCode (index count : ℕ) (output : List Bool) (bit : Bool) :
    transcriptReadFold index (viewBoolCode bit) ⟨.message, count, output⟩ =
      ⟨.message, count, output ++ if count = index + 1 then [bit] else []⟩ := by
  cases bit <;> by_cases h : count = index + 1 <;>
    simp [transcriptReadFold, transcriptReadStep, viewScanStep, viewBoolCode, h]

theorem transcriptReadFold_messageBody (index count : ℕ) (output message : List Bool) :
    transcriptReadFold index (message.flatMap viewBoolCode) ⟨.message, count, output⟩ =
      ⟨.message, count, output ++ if count = index + 1 then message else []⟩ := by
  induction message generalizing output with
  | nil => simp
  | cons bit message ih =>
    rw [List.flatMap_cons, transcriptReadFold_append, transcriptReadFold_boolCode, ih]
    by_cases h : count = index + 1 <;> simp [h, List.append_assoc]

theorem transcriptReadFold_message (index count : ℕ) (output message : List Bool) :
    transcriptReadFold index (encodeViewMessage message) ⟨.between, count, output⟩ =
      ⟨.between, count + 1, output ++ if count = index then message else []⟩ := by
  unfold encodeViewMessage
  change transcriptReadFold index (message.flatMap viewBoolCode ++ [true])
    (transcriptReadStep index ⟨.between, count, output⟩ false) = _
  simp only [transcriptReadStep, Bool.false_eq_true, and_false, ↓reduceIte,
    viewScanStep, and_self]
  rw [transcriptReadFold_append, transcriptReadFold_messageBody]
  simp [transcriptReadFold, transcriptReadStep, viewScanStep]

def selectedTranscriptBytes (index : ℕ) : ℕ → List (List Bool) → List Bool
  | _, [] => []
  | offset, message :: history =>
      (if offset = index then message else []) ++ selectedTranscriptBytes index (offset + 1) history

theorem selectedTranscriptBytes_below (index offset : ℕ) (history : List (List Bool))
    (h : index < offset) : selectedTranscriptBytes index offset history = [] := by
  induction history generalizing offset with
  | nil => rfl
  | cons message history ih =>
    have ht := ih (offset + 1) (by omega)
    simp [selectedTranscriptBytes, show offset ≠ index by omega, ht]

theorem selectedTranscriptBytes_eq_getElem (offset index : ℕ) (history : List (List Bool)) :
    selectedTranscriptBytes (offset + index) offset history = history[index]?.getD [] := by
  induction history generalizing offset index with
  | nil => simp [selectedTranscriptBytes]
  | cons message history ih =>
    cases index with
    | zero =>
      have ht := selectedTranscriptBytes_below offset (offset + 1) history (by omega)
      simp [selectedTranscriptBytes, ht]
    | succ index =>
      have h : offset + (index + 1) = (offset + 1) + index := by omega
      simp only [selectedTranscriptBytes, List.getElem?_cons_succ, h]
      rw [ite_eq_right (show offset ≠ offset + 1 + index by omega), List.nil_append]
      exact ih (offset + 1) index

theorem transcriptReadFold_history (index count : ℕ) (output : List Bool)
    (history : List (List Bool)) :
    transcriptReadFold index (history.flatMap encodeViewMessage) ⟨.between, count, output⟩ =
      ⟨.between, count + history.length, output ++ selectedTranscriptBytes index count history⟩ := by
  induction history generalizing count output with
  | nil => simp [selectedTranscriptBytes]
  | cons message history ih =>
    rw [List.flatMap_cons, transcriptReadFold_append, transcriptReadFold_message, ih]
    simp only [selectedTranscriptBytes, List.append_assoc, List.length_cons]
    congr 1
    omega

def readTranscript (index : ℕ) (bits : List Bool) : TranscriptReadState :=
  transcriptReadFold index bits ⟨.start, 0, []⟩

@[simp] theorem readTranscript_encode (index : ℕ) (history : List (List Bool)) :
    readTranscript index (encodeViewTranscript history) =
      ⟨.done, history.length, history[index]?.getD []⟩ := by
  unfold readTranscript encodeViewTranscript
  change transcriptReadFold index (history.flatMap encodeViewMessage ++ [true])
    (transcriptReadStep index ⟨.start, 0, []⟩ false) = _
  simp only [transcriptReadStep, viewScanStep, Bool.false_eq_true, and_false,
    ↓reduceIte, reduceCtorEq, false_and]
  rw [transcriptReadFold_append, transcriptReadFold_history]
  have hs := selectedTranscriptBytes_eq_getElem 0 index history
  simp only [Nat.zero_add] at hs
  simp [transcriptReadFold, transcriptReadStep, viewScanStep, hs]

def ViewScanState.code : ViewScanState → ℕ
  | .start => 0 | .between => 1 | .message => 2 | .bit => 3
  | .trueFirst => 4 | .trueLast => 5 | .done => 6 | .error => 7

theorem viewScanState_code_le (state : ViewScanState) : state.code ≤ 7 := by
  cases state <;> decide

def encodeTranscriptReadState (state : TranscriptReadState) : List Bool :=
  pair (List.replicate state.scanner.code true) (pair (List.replicate state.count true) state.output)

@[simp] theorem length_encodeTranscriptReadState (state : TranscriptReadState) :
    (encodeTranscriptReadState state).length =
      2 * state.scanner.code + 2 * state.count + state.output.length + 4 := by
  simp [encodeTranscriptReadState, pair_length]
  omega

theorem transcriptReadStep_length_le (index : ℕ) (state : TranscriptReadState) (bit : Bool) :
    (encodeTranscriptReadState (transcriptReadStep index state bit)).length ≤
      (encodeTranscriptReadState state).length + 17 := by
  rw [length_encodeTranscriptReadState, length_encodeTranscriptReadState]
  have hcode := viewScanState_code_le (viewScanStep state.scanner bit)
  unfold transcriptReadStep
  dsimp only
  split <;> split <;> (try split) <;> (try split) <;>
    (try simp only [List.length_append, List.length_cons, List.length_nil]) <;> omega

def transcriptStateCode (bits : List Bool) : ℕ := (pairFst bits).length
def transcriptStateCount (bits : List Bool) : ℕ := (pairFst (pairSnd bits)).length
def transcriptStateOutput (bits : List Bool) : List Bool := pairSnd (pairSnd bits)

@[simp] theorem transcriptStateCode_encode (state : TranscriptReadState) :
    transcriptStateCode (encodeTranscriptReadState state) = state.scanner.code := by
  simp [transcriptStateCode, encodeTranscriptReadState]

@[simp] theorem transcriptStateCount_encode (state : TranscriptReadState) :
    transcriptStateCount (encodeTranscriptReadState state) = state.count := by
  simp [transcriptStateCount, encodeTranscriptReadState]

@[simp] theorem transcriptStateOutput_encode (state : TranscriptReadState) :
    transcriptStateOutput (encodeTranscriptReadState state) = state.output := by
  simp [transcriptStateOutput, encodeTranscriptReadState]

def viewNextCode (bit : Bool) (code : ℕ) : ℕ :=
  if code = 0 then (viewScanStep .start bit).code
  else if code = 1 then (viewScanStep .between bit).code
  else if code = 2 then (viewScanStep .message bit).code
  else if code = 3 then (viewScanStep .bit bit).code
  else if code = 4 then (viewScanStep .trueFirst bit).code
  else if code = 5 then (viewScanStep .trueLast bit).code
  else 7

@[simp] theorem viewNextCode_encode (bit : Bool) (state : ViewScanState) :
    viewNextCode bit state.code = (viewScanStep state bit).code := by
  cases state <;> cases bit <;> rfl

theorem viewNextCode_unaryFn (bit : Bool) {code : List Bool → ℕ} (hcode : UnaryFn code) :
    UnaryFn fun z => viewNextCode bit (code z) :=
  UnaryFn.ite (FPPred.eq hcode (UnaryFn.const 0)) (UnaryFn.const _)
    (UnaryFn.ite (FPPred.eq hcode (UnaryFn.const 1)) (UnaryFn.const _)
      (UnaryFn.ite (FPPred.eq hcode (UnaryFn.const 2)) (UnaryFn.const _)
        (UnaryFn.ite (FPPred.eq hcode (UnaryFn.const 3)) (UnaryFn.const _)
          (UnaryFn.ite (FPPred.eq hcode (UnaryFn.const 4)) (UnaryFn.const _)
            (UnaryFn.ite (FPPred.eq hcode (UnaryFn.const 5)) (UnaryFn.const _) (UnaryFn.const 7))))))

def transcriptReadBitsStep (index : ℕ) (bit : Bool) (bits : List Bool) : List Bool :=
  let code := transcriptStateCode bits
  let count := transcriptStateCount bits
  let output := transcriptStateOutput bits
  pair (List.replicate (viewNextCode bit code) true)
    (pair (List.replicate (if code = 1 ∧ bit = false then count + 1 else count) true)
      (if count = index + 1 ∧ bit = true then
        if code = 3 then output ++ [false]
        else if code = 5 then output ++ [true] else output
      else output))

theorem transcriptReadBitsStep_encode (index : ℕ) (bit : Bool) (state : TranscriptReadState) :
    transcriptReadBitsStep index bit (encodeTranscriptReadState state) =
      encodeTranscriptReadState (transcriptReadStep index state bit) := by
  simp only [transcriptReadBitsStep, transcriptStateCode_encode, transcriptStateCount_encode,
    transcriptStateOutput_encode, viewNextCode_encode]
  rcases state with ⟨scanner, count, output⟩
  cases scanner <;> cases bit <;>
    simp [ViewScanState.code, encodeTranscriptReadState, transcriptReadStep]

theorem transcriptStateCode_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => transcriptStateCode (bits z) :=
  UnaryFn.length (mem_FP_comp hbits pairFst_mem_FP)

theorem transcriptStateCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => transcriptStateCount (bits z) :=
  UnaryFn.length (mem_FP_comp (mem_FP_comp hbits pairSnd_mem_FP) pairFst_mem_FP)

theorem transcriptStateOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => transcriptStateOutput (bits z)) ∈ FP :=
  mem_FP_comp (mem_FP_comp hbits pairSnd_mem_FP) pairSnd_mem_FP

theorem transcriptReadBitsStep_mem_FP (bit : Bool) {index : List Bool → ℕ}
    {bits : List Bool → List Bool} (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => transcriptReadBitsStep (index z) bit (bits z)) ∈ FP := by
  have hcode := transcriptStateCode_unaryFn hbits
  have hcount := transcriptStateCount_unaryFn hbits
  have hout := transcriptStateOutput_mem_FP hbits
  have hfalse := FPPred.const (bit = false)
  have htrue := FPPred.const (bit = true)
  have hnextCount := UnaryFn.ite ((FPPred.eq hcode (UnaryFn.const 1)).and hfalse)
    (hcount.add (UnaryFn.const 1)) hcount
  have hnextOut := ((FPPred.eq hcount (hindex.add (UnaryFn.const 1))).and htrue).ite_mem_FP
    ((FPPred.eq hcode (UnaryFn.const 3)).ite_mem_FP
      (Cobham.appendFn_mem_FP hout (constFn_mem_FP [false]))
      ((FPPred.eq hcode (UnaryFn.const 5)).ite_mem_FP
        (Cobham.appendFn_mem_FP hout (constFn_mem_FP [true])) hout)) hout
  exact mem_FP_pair (viewNextCode_unaryFn bit hcode).mem_FP (mem_FP_pair hnextCount.mem_FP hnextOut)

theorem transcriptReadFold_length_le (index : ℕ) (bits : List Bool) (state : TranscriptReadState) :
    (encodeTranscriptReadState (transcriptReadFold index bits state)).length ≤
      (encodeTranscriptReadState state).length + 17 * bits.length := by
  induction bits generalizing state with
  | nil => simp
  | cons bit bits ih =>
    have h := ih (transcriptReadStep index state bit)
    have hs := transcriptReadStep_length_le index state bit
    change (encodeTranscriptReadState (transcriptReadFold index bits
      (transcriptReadStep index state bit))).length ≤ _
    simp only [List.length_cons]
    omega

/-- Actual machine-time certificate for the forward transducer. Reversing the
recursion ruler turns the upstream right fold into a left-to-right bit scan. -/
theorem readTranscript_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => encodeTranscriptReadState (readTranscript (index z) (bits z))) ∈ FP := by
  let original : List Bool → List Bool := fun z => pairFst (pairFst z)
  have ho : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs : (fun z => pairSnd (pairFst z)) ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hstep (bit : Bool) := transcriptReadBitsStep_mem_FP bit (hindex.comp ho) hs
  have hrev := mem_FP_comp hbits reverse_mem_FP
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  obtain ⟨P, hP⟩ := Cobham.output_length_poly_of_mem_FP hbits
  have h := recFold_mem_FP_of_bound
    (g := fun z t => encodeTranscriptReadState
      (transcriptReadFold (index z) t.reverse ⟨.start, 0, []⟩))
    (w := id) (E := fun _ => encodeTranscriptReadState ⟨.start, 0, []⟩)
    (hstep false) (hstep true) (constFn_mem_FP _) hid hrev
    (by intro z; rfl)
    (by
      intro z t
      simp only [original, id_eq, pairFst_pair, pairSnd_pair,
        transcriptReadBitsStep_encode, List.reverse_cons, transcriptReadFold_append]
      rfl)
    (by
      intro z t
      simp only [original, id_eq, pairFst_pair, pairSnd_pair,
        transcriptReadBitsStep_encode, List.reverse_cons, transcriptReadFold_append]
      rfl)
    ((PolyBound.const 4).add ((PolyBound.const 17).mul (PolyBound.eval P)))
    (by
      intro z t ht
      have hlen : t.length ≤ (bits z).length := by simpa using ht.length_le
      have hg := transcriptReadFold_length_le (index z) t.reverse ⟨.start, 0, []⟩
      change (encodeTranscriptReadState
        (transcriptReadFold (index z) t.reverse ⟨.start, 0, []⟩)).length ≤
          4 + 17 * t.reverse.length at hg
      simp only [List.length_reverse] at hg
      have hp := hP z
      change _ ≤ 4 + 17 * P.eval z.length
      omega)
  apply mem_FP_of_eq h
  intro z
  simp only [Function.comp_apply, List.reverse_reverse, readTranscript]

/-- Exact existing decoder count, with zero on malformed input. -/
def viewTranscriptCount (bits : List Bool) : ℕ :=
  ((decodeViewTranscript bits).map List.length).getD 0

theorem viewTranscriptCount_eq (bits : List Bool) :
    viewTranscriptCount bits = if (decodeViewTranscript bits).isSome then
      transcriptStateCount (encodeTranscriptReadState (readTranscript 0 bits)) else 0 := by
  cases hd : decodeViewTranscript bits with
  | none => simp [viewTranscriptCount, hd]
  | some history =>
    have he := decodeViewTranscript_sound bits history hd
    simp [viewTranscriptCount, ← he]

theorem decodeViewTranscript_length_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => ((decodeViewTranscript (bits z)).map List.length).getD 0 := by
  have h := UnaryFn.ite (decodeViewTranscript_success_fppred hbits)
    (transcriptStateCount_unaryFn (readTranscript_mem_FP (UnaryFn.const 0) hbits)) (UnaryFn.const 0)
  exact h.of_eq (fun z => (viewTranscriptCount_eq (bits z)).symm)

theorem viewTranscriptCount_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => viewTranscriptCount (bits z) := decodeViewTranscript_length_unaryFn hbits

def viewTranscriptMessage? (index : ℕ) (bits : List Bool) : Option (List Bool) :=
  (decodeViewTranscript bits).bind (fun history => history[index]?)

/-- An empty actual message yields `[true]`; failure and absent indices yield `[]`. -/
def viewTranscriptMessageOutput (index : ℕ) (bits : List Bool) : List Bool :=
  ((viewTranscriptMessage? index bits).map (List.cons true)).getD []

/-- Raw bytes with an empty fallback; use the count or success-tagged result
when the distinction between empty and missing messages matters. -/
def viewTranscriptMessage (index : ℕ) (bits : List Bool) : List Bool :=
  (viewTranscriptMessage? index bits).getD []

theorem viewTranscriptMessageOutput_eq (index : ℕ) (bits : List Bool) :
    viewTranscriptMessageOutput index bits =
      if index < viewTranscriptCount bits then
        true :: transcriptStateOutput (encodeTranscriptReadState (readTranscript index bits)) else [] := by
  cases hd : decodeViewTranscript bits with
  | none => simp [viewTranscriptMessageOutput, viewTranscriptMessage?, viewTranscriptCount, hd]
  | some history =>
    have he := decodeViewTranscript_sound bits history hd
    rw [← he]
    simp only [viewTranscriptMessageOutput, viewTranscriptMessage?, decodeViewTranscript_encode,
      Option.bind_some, viewTranscriptCount, Option.map_some, Option.getD_some,
      readTranscript_encode, transcriptStateOutput_encode]
    by_cases hi : index < history.length
    · simp [hi]
    · simp [hi]

theorem viewTranscriptMessageOutput_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => viewTranscriptMessageOutput (index z) (bits z)) ∈ FP := by
  have hout := transcriptStateOutput_mem_FP (readTranscript_mem_FP hindex hbits)
  have h := (FPPred.lt hindex (viewTranscriptCount_unaryFn hbits)).ite_mem_FP
    (mem_FP_comp hout (Cobham.cons_mem_FP true)) (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun z => (viewTranscriptMessageOutput_eq (index z) (bits z)).symm)

theorem viewTranscriptMessage_eq_drop (index : ℕ) (bits : List Bool) :
    viewTranscriptMessage index bits = (viewTranscriptMessageOutput index bits).drop 1 := by
  unfold viewTranscriptMessage viewTranscriptMessageOutput
  cases viewTranscriptMessage? index bits <;> rfl

theorem viewTranscriptMessage_mem_FP {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => viewTranscriptMessage (index z) (bits z)) ∈ FP :=
  mem_FP_of_eq (drop_mem_FP (viewTranscriptMessageOutput_mem_FP hindex hbits) (UnaryFn.const 1))
    (fun z => (viewTranscriptMessage_eq_drop (index z) (bits z)).symm)

@[simp] theorem viewTranscriptCount_encode (history : List (List Bool)) :
    viewTranscriptCount (encodeViewTranscript history) = history.length := by simp [viewTranscriptCount]

@[simp] theorem viewTranscriptMessage?_encode (index : ℕ) (history : List (List Bool)) :
    viewTranscriptMessage? index (encodeViewTranscript history) = history[index]? := by
  simp [viewTranscriptMessage?]

@[simp] theorem viewTranscriptMessage_encode (index : ℕ) (history : List (List Bool)) :
    viewTranscriptMessage index (encodeViewTranscript history) = history[index]?.getD [] := by
  simp [viewTranscriptMessage]

@[simp] theorem viewTranscriptMessageOutput_encode (index : ℕ) (history : List (List Bool)) :
    viewTranscriptMessageOutput index (encodeViewTranscript history) =
      (history[index]?.map (List.cons true)).getD [] := by simp [viewTranscriptMessageOutput]

theorem viewTranscriptMessageOutput_eq_nil_iff (index : ℕ) (bits : List Bool) :
    viewTranscriptMessageOutput index bits = [] ↔ viewTranscriptMessage? index bits = none := by
  unfold viewTranscriptMessageOutput
  cases viewTranscriptMessage? index bits <;> simp

theorem viewTranscriptMessageOutput_success_iff (index : ℕ) (bits message : List Bool) :
    viewTranscriptMessageOutput index bits = true :: message ↔
      (decodeViewTranscript bits).bind (fun history => history[index]?) = some message := by
  change viewTranscriptMessageOutput index bits = true :: message ↔
    viewTranscriptMessage? index bits = some message
  unfold viewTranscriptMessageOutput
  cases viewTranscriptMessage? index bits <;> simp

theorem viewTranscriptMessage_success_fppred {index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hindex : UnaryFn index) (hbits : bits ∈ FP) :
    FPPred fun z => (viewTranscriptMessage? (index z) (bits z)).isSome = true := by
  refine ((bitStrings_eq_fppred (viewTranscriptMessageOutput_mem_FP hindex hbits)
    (constFn_mem_FP [])).not).of_iff (fun z => ?_)
  rw [viewTranscriptMessageOutput_eq_nil_iff]
  cases viewTranscriptMessage? (index z) (bits z) <;> simp

end IPPSPACE

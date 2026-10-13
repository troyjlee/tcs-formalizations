/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.UpstreamView
import IPPSPACE.QBF.BinaryNamesFP

/-!
# Polynomial-time validation of protocol views

The transcript codec has fixed nesting depth, so a finite-state scan recognizes
exactly its canonical encodings. This module connects that scan to the existing
validating decoder, including malformed pair prefixes and trailing transcript
bytes. It certifies validation and encoded output, not transcript replay.
-/

namespace IPPSPACE

open Complexity

private def TranscriptTail (bits : List Bool) : Prop :=
  ∃ history : List (List Bool), history.flatMap encodeViewMessage ++ [true] = bits

private def MessageTail (bits : List Bool) : Prop :=
  ∃ message : List Bool, ∃ history : List (List Bool),
    message.flatMap viewBoolCode ++ [true] ++ history.flatMap encodeViewMessage ++ [true] = bits

private def BoolTail (bits : List Bool) : Prop :=
  (∃ rest, bits = true :: rest ∧ MessageTail rest) ∨
    (∃ rest, bits = false :: true :: true :: rest ∧ MessageTail rest)

private theorem transcriptTail_true (bits : List Bool) :
    TranscriptTail (true :: bits) ↔ bits = [] := by
  constructor
  · rintro ⟨history, h⟩
    cases history with
    | nil => simpa using h.symm
    | cons m ms => simp [encodeViewMessage] at h
  · rintro rfl
    exact ⟨[], rfl⟩

private theorem transcriptTail_false (bits : List Bool) :
    TranscriptTail (false :: bits) ↔ MessageTail bits := by
  constructor
  · rintro ⟨history, h⟩
    cases history with
    | nil => simp at h
    | cons m ms =>
      refine ⟨m, ms, ?_⟩
      simpa [encodeViewMessage, List.append_assoc] using h
  · rintro ⟨m, ms, h⟩
    refine ⟨m :: ms, ?_⟩
    simpa [encodeViewMessage, List.append_assoc] using congrArg (List.cons false) h

private theorem messageTail_true (bits : List Bool) :
    MessageTail (true :: bits) ↔ TranscriptTail bits := by
  constructor
  · rintro ⟨m, ms, h⟩
    cases m with
    | nil => exact ⟨ms, by simpa using h⟩
    | cons b m => cases b <;> simp [viewBoolCode] at h
  · rintro ⟨ms, h⟩
    exact ⟨[], ms, by simpa using congrArg (List.cons true) h⟩

private theorem messageTail_false (bits : List Bool) :
    MessageTail (false :: bits) ↔ BoolTail bits := by
  constructor
  · rintro ⟨m, ms, h⟩
    cases m with
    | nil => simp at h
    | cons b m =>
      let rest := m.flatMap viewBoolCode ++ [true] ++ ms.flatMap encodeViewMessage ++ [true]
      have hr : MessageTail rest := ⟨m, ms, rfl⟩
      cases b with
      | false =>
        exact Or.inl ⟨rest, by simpa [viewBoolCode, rest, List.append_assoc] using h.symm, hr⟩
      | true =>
        exact Or.inr ⟨rest, by simpa [viewBoolCode, rest, List.append_assoc] using h.symm, hr⟩
  · rintro (⟨rest, rfl, m, ms, h⟩ | ⟨rest, rfl, m, ms, h⟩)
    · refine ⟨false :: m, ms, ?_⟩
      simpa [viewBoolCode, List.append_assoc] using congrArg (fun xs => false :: true :: xs) h
    · refine ⟨true :: m, ms, ?_⟩
      simpa [viewBoolCode, List.append_assoc] using
        congrArg (fun xs => false :: false :: true :: true :: xs) h

/-- Eight states suffice for the fixed-depth upstream transcript code. -/
inductive ViewScanState where
  | start | between | message | bit | trueFirst | trueLast | done | error
  deriving DecidableEq

def viewScanStep : ViewScanState → Bool → ViewScanState
  | .start, false => .between
  | .between, false => .message
  | .between, true => .done
  | .message, false => .bit
  | .message, true => .between
  | .bit, false => .trueFirst
  | .bit, true => .message
  | .trueFirst, true => .trueLast
  | .trueLast, true => .message
  | _, _ => .error

private def ViewStateLanguage : ViewScanState → List Bool → Prop
  | .start, bits => ∃ rest, bits = false :: rest ∧ TranscriptTail rest
  | .between, bits => TranscriptTail bits
  | .message, bits => MessageTail bits
  | .bit, bits => BoolTail bits
  | .trueFirst, bits => ∃ rest, bits = true :: true :: rest ∧ MessageTail rest
  | .trueLast, bits => ∃ rest, bits = true :: rest ∧ MessageTail rest
  | .done, bits => bits = []
  | .error, _ => False

private theorem viewStateLanguage_nil (state : ViewScanState) :
    ViewStateLanguage state [] ↔ state = .done := by
  cases state <;> simp [ViewStateLanguage, TranscriptTail, MessageTail, BoolTail]

private theorem viewStateLanguage_cons (state : ViewScanState) (b : Bool) (bits : List Bool) :
    ViewStateLanguage state (b :: bits) ↔ ViewStateLanguage (viewScanStep state b) bits := by
  cases state <;> cases b <;>
    simp [ViewStateLanguage, viewScanStep, BoolTail, transcriptTail_true,
      transcriptTail_false, messageTail_true, messageTail_false]

/-- Scan every input bit; reaching the final state early rejects later bytes. -/
def viewScanAccept : List Bool → ViewScanState → Bool
  | [], state => decide (state = .done)
  | b :: bits, state => viewScanAccept bits (viewScanStep state b)

private theorem viewScanAccept_iff (bits : List Bool) (state : ViewScanState) :
    viewScanAccept bits state = true ↔ ViewStateLanguage state bits := by
  induction bits generalizing state with
  | nil => simp [viewScanAccept, viewStateLanguage_nil]
  | cons b bits ih => rw [viewScanAccept, ih, viewStateLanguage_cons]

/-- Full transcript validation recognizes exactly canonical upstream encodings. -/
theorem viewScanAccept_start_iff (bits : List Bool) :
    viewScanAccept bits .start = true ↔ ∃ history, encodeViewTranscript history = bits := by
  rw [viewScanAccept_iff]
  constructor
  · rintro ⟨rest, rfl, history, h⟩
    exact ⟨history, by rw [encodeViewTranscript, h]⟩
  · rintro ⟨history, rfl⟩
    exact ⟨_, rfl, history, rfl⟩

theorem viewScanAccept_eq_decodeViewTranscript (bits : List Bool) :
    viewScanAccept bits .start = (decodeViewTranscript bits).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [viewScanAccept_start_iff]
  constructor
  · rintro ⟨history, rfl⟩
    simp
  · intro h
    cases hd : decodeViewTranscript bits with
    | none => simp [hd] at h
    | some history => exact ⟨history, decodeViewTranscript_sound bits history hd⟩

/-- A truth table stores the acceptance of every possible starting state. -/
def viewScanVector (bits : List Bool) : List Bool :=
  [viewScanAccept bits .start, viewScanAccept bits .between, viewScanAccept bits .message,
    viewScanAccept bits .bit, viewScanAccept bits .trueFirst, viewScanAccept bits .trueLast,
    viewScanAccept bits .done, viewScanAccept bits .error]

def viewScanVectorStep (b : Bool) (state : List Bool) : List Bool :=
  (if b then [7, 6, 1, 2, 5, 2, 7, 7] else [1, 2, 3, 4, 7, 7, 7, 7]).map
    (fun i => state[i]?.getD false)

theorem viewScanVector_cons (b : Bool) (bits : List Bool) :
    viewScanVector (b :: bits) = viewScanVectorStep b (viewScanVector bits) := by
  cases b <;> rfl

private theorem fixedBitSelection_mem_FP (indices : List ℕ) {bits : List Bool → List Bool}
    (hbits : bits ∈ FP) :
    (fun z => indices.map (fun i => (bits z)[i]?.getD false)) ∈ FP := by
  induction indices with
  | nil => exact constFn_mem_FP []
  | cons i indices ih => exact Cobham.appendFn_mem_FP (getBit_mem_FP hbits (UnaryFn.const i)) ih

theorem viewScanVector_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => viewScanVector (bits z)) ∈ FP := by
  have hstate := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hstep (b : Bool) : (fun z => viewScanVectorStep b (pairSnd (pairFst z))) ∈ FP :=
    fixedBitSelection_mem_FP _ hstate
  apply recFold_mem_FP_of_bound (g := fun _ t => viewScanVector t)
    (w := fun _ => []) (E := fun _ => viewScanVector []) (hstep false) (hstep true)
    (constFn_mem_FP _) (constFn_mem_FP _) hbits
  · intro z; rfl
  · intro z t; simp only [pairFst_pair, pairSnd_pair, viewScanVector_cons]
  · intro z t; simp only [pairFst_pair, pairSnd_pair, viewScanVector_cons]
  · exact PolyBound.const 8
  · intro z t ht; rfl

theorem decodeViewTranscript_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (decodeViewTranscript (bits z)).isSome = true := by
  have h := FPPred.getBit (viewScanVector_mem_FP hbits) (UnaryFn.const 0)
  refine h.of_iff (fun z => ?_)
  simp only [viewScanVector, List.getElem?_cons_zero, Option.getD_some,
    viewScanAccept_eq_decodeViewTranscript]

/-- Exact canonicality test for upstream's total pair projections. -/
theorem parseViewPair_success_iff_repack (bits : List Bool) :
    (parseViewPair bits).isSome = true ↔ pair (pairFst bits) (pairSnd bits) = bits := by
  rw [parseViewPair_eq_unpair]
  constructor
  · intro h
    cases hp : unpair? bits with
    | none => simp [hp] at h
    | some result =>
      rw [eq_pair_of_unpair?_eq_some hp]
      simp
  · intro h
    rw [← h, unpair?_pair]
    rfl

theorem parseViewPair_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (parseViewPair (bits z)).isSome = true :=
  (bitStrings_eq_fppred
    (mem_FP_pair (mem_FP_comp hbits pairFst_mem_FP) (mem_FP_comp hbits pairSnd_mem_FP))
    hbits).of_iff (fun z => (parseViewPair_success_iff_repack (bits z)).symm)

/-- Both nested pair delimiters and the complete transcript must be valid. -/
theorem decodeProtocolView_success_iff (bits : List Bool) :
    (decodeProtocolView bits).isSome = true ↔
      (parseViewPair bits).isSome = true ∧
      (parseViewPair (pairFst bits)).isSome = true ∧
      (decodeViewTranscript (pairSnd bits)).isSome = true := by
  cases ho : parseViewPair bits with
  | none => simp [decodeProtocolView, ho]
  | some outer =>
    have hf : pairFst bits = outer.1 := by
      rw [← parseViewPair_sound bits outer.1 outer.2 ho, viewPair_eq_pair]
      simp
    have hs : pairSnd bits = outer.2 := by
      rw [← parseViewPair_sound bits outer.1 outer.2 ho, viewPair_eq_pair]
      simp
    cases hi : parseViewPair outer.1 <;> cases ht : decodeViewTranscript outer.2 <;>
      simp [decodeProtocolView, ho, hi, ht, hf, hs]

/-- The original complete view decoder has an actual polynomial-time success
test, including malformed nested pairs and malformed transcript contents. -/
theorem decodeProtocolView_success_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (decodeProtocolView (bits z)).isSome = true :=
  ((parseViewPair_success_fppred hbits).and
    ((parseViewPair_success_fppred (mem_FP_comp hbits pairFst_mem_FP)).and
      (decodeViewTranscript_success_fppred (mem_FP_comp hbits pairSnd_mem_FP)))).of_iff
    (fun z => (decodeProtocolView_success_iff (bits z)).symm)

/-- Preserve the full canonical transcript after validation, with a distinct
failure encoding. This does not extract individual transcript messages. -/
def decodeViewTranscriptOutput (bits : List Bool) : List Bool :=
  match decodeViewTranscript bits with
  | none => []
  | some history => true :: encodeViewTranscript history

theorem decodeViewTranscriptOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodeViewTranscriptOutput (bits z)) ∈ FP := by
  apply mem_FP_of_eq ((decodeViewTranscript_success_fppred hbits).ite_mem_FP
    (mem_FP_comp hbits (Cobham.cons_mem_FP true)) (constFn_mem_FP []))
  intro z
  cases hd : decodeViewTranscript (bits z) with
  | none => simp [decodeViewTranscriptOutput, hd]
  | some history =>
    simp [decodeViewTranscriptOutput, hd, decodeViewTranscript_sound (bits z) history hd]

def decodeProtocolViewOutput (bits : List Bool) : List Bool :=
  match decodeProtocolView bits with
  | none => []
  | some view => true :: encodeProtocolView view.input view.coins view.transcript

theorem decodeProtocolViewOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodeProtocolViewOutput (bits z)) ∈ FP := by
  apply mem_FP_of_eq ((decodeProtocolView_success_fppred hbits).ite_mem_FP
    (mem_FP_comp hbits (Cobham.cons_mem_FP true)) (constFn_mem_FP []))
  intro z
  cases hd : decodeProtocolView (bits z) with
  | none => simp [decodeProtocolViewOutput, hd]
  | some view => simp [decodeProtocolViewOutput, hd, decodeProtocolView_sound (bits z) view hd]

@[simp] theorem decodeProtocolViewOutput_encode (input coins : List Bool) (history : List (List Bool)) :
    decodeProtocolViewOutput (encodeProtocolView input coins history) =
      true :: encodeProtocolView input coins history := by simp [decodeProtocolViewOutput]

theorem decodeProtocolViewOutput_eq_nil_iff (bits : List Bool) :
    decodeProtocolViewOutput bits = [] ↔ decodeProtocolView bits = none := by
  cases hd : decodeProtocolView bits <;> simp [decodeProtocolViewOutput, hd]

/-- Validating field projection: malformed full views produce no field bytes. -/
def decodedViewField (field : DecodedProtocolView → List Bool) (bits : List Bool) : List Bool :=
  match decodeProtocolView bits with
  | none => []
  | some view => field view

private theorem decodedViewField_mem_FP (field : DecodedProtocolView → List Bool)
    (raw : List Bool → List Bool) (hraw : raw ∈ FP)
    (hrefine : ∀ bits view, decodeProtocolView bits = some view → raw bits = field view)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodedViewField field (bits z)) ∈ FP := by
  apply mem_FP_of_eq ((decodeProtocolView_success_fppred hbits).ite_mem_FP
    (mem_FP_comp hbits hraw) (constFn_mem_FP []))
  intro z
  cases hd : decodeProtocolView (bits z) with
  | none => simp [decodedViewField, hd]
  | some view =>
    simpa only [decodedViewField, hd, Option.isSome_some, ↓reduceIte, Function.comp_apply] using
      hrefine (bits z) view hd

theorem decodedViewInput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodedViewField DecodedProtocolView.input (bits z)) ∈ FP :=
  decodedViewField_mem_FP _ upstreamViewInput upstreamViewInput_mem_FP upstreamViewInput_of_decode hbits

theorem decodedViewCoins_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodedViewField DecodedProtocolView.coins (bits z)) ∈ FP :=
  decodedViewField_mem_FP _ upstreamViewCoins upstreamViewCoins_mem_FP upstreamViewCoins_of_decode hbits

theorem decodedViewTranscriptBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodedViewField (fun view => DataEncode.bitstringEncode view.transcript) (bits z)) ∈ FP :=
  decodedViewField_mem_FP _ upstreamViewTranscriptBits upstreamViewTranscriptBits_mem_FP
    upstreamViewTranscriptBits_of_decode hbits

end IPPSPACE

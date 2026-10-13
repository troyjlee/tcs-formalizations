/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Encoding.Pairing
import Complexitylib.Encoding.DataEncode
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.DataEncode
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Composition
import IPPSPACE.Protocol.ViewEncoding

/-!
# Exact correspondence with upstream view encoding

The local executable pair and transcript codecs are equal to the actual imported
upstream `pair`, `unpair?`, and `DataEncode.bitstringEncode` declarations. Thus
the complete view equals the nested upstream encoding expression. The total
upstream field projections are correct on canonical views; on malformed inputs
the validating decoder remains distinct from prefix-tolerant `pairFst`.

The polynomial-time results use upstream's actual machine-based `FP` class:
field projections, packing already encoded fields, repacking, and encoding an
individual message. They do not certify the validating transcript parser or the
complete interactive verifier.
-/

namespace IPPSPACE

open Complexity

theorem viewPair_eq_pair (left right : List Bool) : viewPair left right = pair left right := by
  rw [viewPair_eq_doubled]
  rfl

/-- The validating pair parser agrees with upstream on every string, including
malformed doubled prefixes and missing separators. -/
theorem parseViewPair_eq_unpair (bits : List Bool) : parseViewPair bits = unpair? bits := by
  cases hp : parseViewPair bits with
  | none =>
    cases hu : unpair? bits with
    | none => rfl
    | some result =>
      rcases result with ⟨left, right⟩
      have heq := eq_pair_of_unpair?_eq_some hu
      rw [heq, ← viewPair_eq_pair, parseViewPair_viewPair] at hp
      contradiction
  | some result =>
    rcases result with ⟨left, right⟩
    rw [← parseViewPair_sound bits left right hp, viewPair_eq_pair, unpair?_pair]

theorem viewBoolCode_eq_bitstringEncode (bit : Bool) :
    viewBoolCode bit = DataEncode.bitstringEncode bit := by
  cases bit <;> simp [viewBoolCode, DataEncode.bitstringEncode_def, DataEncode.encode, Data.toBits_l]

theorem encodeViewMessage_eq_bitstringEncode (bits : List Bool) :
    encodeViewMessage bits = DataEncode.bitstringEncode bits := by
  rw [encodeViewMessage, DataEncode.bitstringEncode_list,
    show viewBoolCode = DataEncode.bitstringEncode from funext viewBoolCode_eq_bitstringEncode]
  rfl

theorem encodeViewTranscript_eq_bitstringEncode (history : List (List Bool)) :
    encodeViewTranscript history = DataEncode.bitstringEncode history := by
  rw [encodeViewTranscript, DataEncode.bitstringEncode_list,
    show encodeViewMessage = DataEncode.bitstringEncode from funext encodeViewMessage_eq_bitstringEncode]
  rfl

/-- Equality to the actual imported encoding operations, not merely a comparison
of their source equations. -/
theorem encodeProtocolView_eq_upstream_encoding (input coins : List Bool)
    (history : List (List Bool)) :
    encodeProtocolView input coins history =
      pair (pair input coins) (DataEncode.bitstringEncode history) := by
  simp only [encodeProtocolView, viewPair_eq_pair, encodeViewTranscript_eq_bitstringEncode]

@[simp] theorem decodeViewTranscript_bitstringEncode (history : List (List Bool)) :
    decodeViewTranscript (DataEncode.bitstringEncode history) = some history := by
  rw [← encodeViewTranscript_eq_bitstringEncode, decodeViewTranscript_encode]

@[simp] theorem decodeProtocolView_upstream_encoding (input coins : List Bool)
    (history : List (List Bool)) :
    decodeProtocolView (pair (pair input coins) (DataEncode.bitstringEncode history)) =
      some ⟨input, coins, history⟩ := by
  rw [← encodeProtocolView_eq_upstream_encoding, decodeProtocolView_encode]

theorem decodeProtocolView_eq_some_iff_upstream (bits : List Bool) (view : DecodedProtocolView) :
    decodeProtocolView bits = some view ↔
      pair (pair view.input view.coins) (DataEncode.bitstringEncode view.transcript) = bits := by
  rw [decodeProtocolView_eq_some_iff, encodeProtocolView_eq_upstream_encoding]

/-- Upstream's total input projection. It may return a decoded prefix on a
malformed view, so it is not identified with the validating decoder there. -/
def upstreamViewInput (bits : List Bool) : List Bool := pairFst (pairFst bits)

/-- Upstream's total projection to the private coin string. -/
def upstreamViewCoins (bits : List Bool) : List Bool := pairSnd (pairFst bits)

/-- Project the serialized transcript without decoding its bracketed contents. -/
def upstreamViewTranscriptBits (bits : List Bool) : List Bool := pairSnd bits

@[simp] theorem upstreamViewInput_encodeProtocolView (input coins : List Bool)
    (history : List (List Bool)) :
    upstreamViewInput (encodeProtocolView input coins history) = input := by
  simp [upstreamViewInput, encodeProtocolView_eq_upstream_encoding]

@[simp] theorem upstreamViewCoins_encodeProtocolView (input coins : List Bool)
    (history : List (List Bool)) :
    upstreamViewCoins (encodeProtocolView input coins history) = coins := by
  simp [upstreamViewCoins, encodeProtocolView_eq_upstream_encoding]

@[simp] theorem upstreamViewTranscriptBits_encodeProtocolView (input coins : List Bool)
    (history : List (List Bool)) :
    upstreamViewTranscriptBits (encodeProtocolView input coins history) =
      DataEncode.bitstringEncode history := by
  simp [upstreamViewTranscriptBits, encodeProtocolView_eq_upstream_encoding]

theorem upstreamViewInput_of_decode (bits : List Bool) (view : DecodedProtocolView)
    (h : decodeProtocolView bits = some view) : upstreamViewInput bits = view.input := by
  rw [← decodeProtocolView_sound bits view h, upstreamViewInput_encodeProtocolView]

theorem upstreamViewCoins_of_decode (bits : List Bool) (view : DecodedProtocolView)
    (h : decodeProtocolView bits = some view) : upstreamViewCoins bits = view.coins := by
  rw [← decodeProtocolView_sound bits view h, upstreamViewCoins_encodeProtocolView]

theorem upstreamViewTranscriptBits_of_decode (bits : List Bool) (view : DecodedProtocolView)
    (h : decodeProtocolView bits = some view) :
    upstreamViewTranscriptBits bits = DataEncode.bitstringEncode view.transcript := by
  rw [← decodeProtocolView_sound bits view h, upstreamViewTranscriptBits_encodeProtocolView]

/-- Pack three raw fields when the transcript has already been serialized. -/
def packEncodedView (input coins transcriptBits : List Bool) : List Bool :=
  viewPair (viewPair input coins) transcriptBits

theorem packEncodedView_bitstringEncode (input coins : List Bool) (history : List (List Bool)) :
    packEncodedView input coins (DataEncode.bitstringEncode history) =
      encodeProtocolView input coins history := by
  simp only [packEncodedView, encodeProtocolView, encodeViewTranscript_eq_bitstringEncode]

/-- Reassemble the three total upstream projections. Canonical views are fixed;
malformed inputs follow the projections' total fallback behavior. -/
def repackEncodedView (bits : List Bool) : List Bool :=
  packEncodedView (upstreamViewInput bits) (upstreamViewCoins bits) (upstreamViewTranscriptBits bits)

@[simp] theorem repackEncodedView_encodeProtocolView (input coins : List Bool)
    (history : List (List Bool)) :
    repackEncodedView (encodeProtocolView input coins history) = encodeProtocolView input coins history := by
  simp only [repackEncodedView, upstreamViewInput_encodeProtocolView,
    upstreamViewCoins_encodeProtocolView, upstreamViewTranscriptBits_encodeProtocolView,
    packEncodedView_bitstringEncode]

/-- Genuine polynomial-time input projection, including its total behavior on
malformed strings. No validating-decoder claim is made. -/
theorem upstreamViewInput_mem_FP : upstreamViewInput ∈ FP :=
  mem_FP_comp pairFst_mem_FP pairFst_mem_FP

theorem upstreamViewCoins_mem_FP : upstreamViewCoins ∈ FP :=
  mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem upstreamViewTranscriptBits_mem_FP : upstreamViewTranscriptBits ∈ FP := pairSnd_mem_FP

/-- The local doubling codec inherits upstream's actual polynomial-time pairing
closure through the proved function equality. -/
theorem viewPair_mem_FP {left right : List Bool → List Bool} (hleft : left ∈ FP) (hright : right ∈ FP) :
    (fun bits => viewPair (left bits) (right bits)) ∈ FP := by
  simpa only [viewPair_eq_pair] using mem_FP_pair hleft hright

/-- Nested packing of three already encoded polynomial-time fields. -/
theorem packEncodedView_mem_FP {input coins transcriptBits : List Bool → List Bool}
    (hinput : input ∈ FP) (hcoins : coins ∈ FP) (htranscript : transcriptBits ∈ FP) :
    (fun bits => packEncodedView (input bits) (coins bits) (transcriptBits bits)) ∈ FP :=
  viewPair_mem_FP (viewPair_mem_FP hinput hcoins) htranscript

theorem repackEncodedView_mem_FP : repackEncodedView ∈ FP :=
  packEncodedView_mem_FP upstreamViewInput_mem_FP upstreamViewCoins_mem_FP upstreamViewTranscriptBits_mem_FP

/-- The executable codec for one raw message has a genuine upstream `FP`
certificate. This does not encode or decode an arbitrary nested transcript. -/
theorem encodeViewMessage_mem_FP : encodeViewMessage ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have h := encodeList_mem_FP hid
  simpa only [id_eq, ← encodeViewMessage_eq_bitstringEncode] using h

@[simp] theorem packViewMessage_upstream_encoding
    (message : List Bool → List Bool → List (List Bool) → List Bool)
    (input coins : List Bool) (history : List (List Bool)) :
    packViewMessage message (pair (pair input coins) (DataEncode.bitstringEncode history)) =
      message input coins history := by
  rw [← encodeProtocolView_eq_upstream_encoding, packViewMessage_encode]

@[simp] theorem packViewVerdict_upstream_encoding
    (verdict : List Bool → List Bool → List (List Bool) → Bool)
    (input coins : List Bool) (history : List (List Bool)) :
    packViewVerdict verdict (pair (pair input coins) (DataEncode.bitstringEncode history)) =
      verdict input coins history := by
  rw [← encodeProtocolView_eq_upstream_encoding, packViewVerdict_encode]

end IPPSPACE

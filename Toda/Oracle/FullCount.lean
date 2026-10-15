import Toda.Oracle.BatchAccess
import Toda.Oracle.CountVerdict
import Toda.Counting.BoundedProduct
import Toda.Counting.Constants

/-!
# Three full binary answers for the randomized parity count

The third answer supplies the required decoding width, as the binary length
of a power of two. It comes from the same canonical #P function as the two
counts. Every deterministic query and answer transformation below is FP.
-/

namespace Toda.Oracle

open Complexity Counting

/-- Add a metadata branch to the existing counting oracle. -/
def fullCountFunction (F : List Bool → ℕ) (width : List Bool → ℕ) : List Bool → ℕ :=
  taggedCounting F (fun x => 2 ^ (width x + 1))

theorem fullCountFunction_mem_sharpP {F : List Bool → ℕ} {width : List Bool → ℕ}
    (hF : F ∈ SharpP) (hwidth : UnaryFn width) : fullCountFunction F width ∈ SharpP :=
  taggedCounting_mem_sharpP hF
    (sharpP_pow_unaryFn (sharpP_const 2) (hwidth.add (UnaryFn.const 1)))

/-- Positive count, negative count, and the decoding-width marker. -/
def fullCountQueries (input : List Bool) : List (List Bool) :=
  [taggedInput false (taggedInput false input),
   taggedInput false (taggedInput true input), taggedInput true input]

theorem encoded_fullCountQueries_mem_FP :
    (fun input => Batch.encode (fullCountQueries input)) ∈ FP := by
  have hfirst := encodeQuery_mem_FP
    (mem_FP_comp (taggedInput_mem_FP false) (taggedInput_mem_FP false))
  have hsecond := encodeQuery_mem_FP
    (mem_FP_comp (taggedInput_mem_FP true) (taggedInput_mem_FP false))
  have hthird := encodeQuery_mem_FP (taggedInput_mem_FP true)
  refine mem_FP_of_eq (Cobham.appendFn_mem_FP hfirst
    (Cobham.appendFn_mem_FP hsecond hthird)) fun input => ?_
  simp [Batch.encode, fullCountQueries]

/-- Fixed-width binary truncation/padding is actual FP. -/
theorem fixedWidthBits_mem_FP {bits : List Bool → List Bool} {width : List Bool → ℕ}
    (hbits : bits ∈ FP) (hwidth : UnaryFn width) :
    (fun input => fixedWidthBits (bits input) (width input)) ∈ FP := by
  refine mem_FP_of_eq (Cobham.appendFn_mem_FP (take_mem_FP hbits hwidth)
    ((hwidth.sub (UnaryFn.length hbits)).replicate_mem_FP false)) fun input => ?_
  exact (fixedWidthBits_eq_take_append_replicate _ _).symm

/-- Decode the width from the third answer, never from its numerical value. -/
def fullAnswerWidth (answers : List Bool) : ℕ :=
  (Batch.first (Batch.rest (Batch.rest answers))).length - 1

def fullAnswerPrefixes (answers : List Bool) : List Bool :=
  fixedWidthBits (Batch.first answers) (fullAnswerWidth answers) ++
    fixedWidthBits (Batch.first (Batch.rest answers)) (fullAnswerWidth answers)

/-- The total binary verdict after three full oracle answers. -/
def fullCountVerdict (answers : List Bool) : List Bool :=
  countVerdict (fullAnswerPrefixes answers)

theorem fullAnswerWidth_unary : UnaryFn fullAnswerWidth :=
  (UnaryFn.length (mem_FP_comp
    (mem_FP_comp Batch.rest_mem_FP Batch.rest_mem_FP) Batch.first_mem_FP)).sub (UnaryFn.const 1)

theorem fullAnswerPrefixes_mem_FP : fullAnswerPrefixes ∈ FP :=
  Cobham.appendFn_mem_FP (fixedWidthBits_mem_FP Batch.first_mem_FP fullAnswerWidth_unary)
    (fixedWidthBits_mem_FP (mem_FP_comp Batch.rest_mem_FP Batch.first_mem_FP)
      fullAnswerWidth_unary)

theorem fullCountVerdict_mem_FP : fullCountVerdict ∈ FP :=
  mem_FP_comp fullAnswerPrefixes_mem_FP countVerdict_mem_FP

theorem fullCountVerdict_boolean (answers : List Bool) :
    fullCountVerdict answers = [true] ∨ fullCountVerdict answers = [false] := by
  simp only [fullCountVerdict, countVerdict]
  cases decide (true ∈ thresholdBits (fullAnswerPrefixes answers)) <;> simp

theorem fullCountQueries_answers (F : List Bool → ℕ) (width : List Bool → ℕ)
    (input : List Bool) :
    (fullCountQueries input).map (fun query => (fullCountFunction F width query).bits) =
      [(F (taggedInput false input)).bits, (F (taggedInput true input)).bits,
       (2 ^ (width input + 1)).bits] := by
  simp [fullCountQueries, fullCountFunction]

theorem fullAnswerPrefixes_answers (F : List Bool → ℕ) (width : List Bool → ℕ)
    (input : List Bool) :
    fullAnswerPrefixes (Batch.encode
      ((fullCountQueries input).map (fun query => (fullCountFunction F width query).bits))) =
      (countQueries input (width input + 1)).map (bitOracle F) := by
  rw [fullCountQueries_answers, countQueries_answers]
  simp only [Batch.encode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    fullAnswerPrefixes, fullAnswerWidth, Batch.first_encodeQuery, Batch.rest_encodeQuery,
    Batch.first_encodeQuery_single]
  simp only [Nat.size_eq_bits_len, Nat.size_pow, Nat.add_sub_cancel]
  rw [fixedWidthBits_eq_toBitsLE, fixedWidthBits_eq_toBitsLE,
    Nat.fromBitsLE_bits, Nat.fromBitsLE_bits, answerBits_eq_toBitsLE, answerBits_eq_toBitsLE]

/-- Full answers agree exactly with the previous bit-prefix verdict. -/
theorem fullCountVerdict_answers (F : List Bool → ℕ) (width : List Bool → ℕ)
    (input : List Bool) :
    fullCountVerdict (Batch.encode
      ((fullCountQueries input).map (fun query => (fullCountFunction F width query).bits))) =
      countVerdict ((countQueries input (width input + 1)).map (bitOracle F)) := by
  exact congrArg countVerdict (fullAnswerPrefixes_answers F width input)

end Toda.Oracle

namespace Toda.Randomized

open Complexity Toda.Oracle

/-- A fixed three-query algorithm decides every bounded-error parity language.
The oracle is canonical #P and both ordinary string transformations are FP;
their execution on a full-answer oracle TM is supplied by the machine compiler. -/
theorem bpParityP_exists_fullCountVerdict {language : Language}
    (hlanguage : language ∈ BPParityP) :
    ∃ F : List Bool → ℕ, F ∈ SharpP ∧ ∀ input,
      input ∈ language ↔ fullCountVerdict (Batch.encode
        ((fullCountQueries input).map (fun query => (F query).bits))) = [true] := by
  obtain ⟨F, width, hF, hwidth, hdecide⟩ := bpParityP_exists_countVerdict hlanguage
  refine ⟨fullCountFunction F width, fullCountFunction_mem_sharpP hF hwidth, fun input => ?_⟩
  rw [fullCountVerdict_answers]
  exact hdecide input

end Toda.Randomized

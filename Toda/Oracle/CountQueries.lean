import Toda.Oracle.CountRecovery
import Toda.Oracle.Batch.Codec
import Complexitylib.Classes.P.Range

/-! Polynomial-time preparation of the nonadaptive bit queries for count recovery. -/

namespace Toda.Oracle

open Complexity Counting

private theorem list_eq_map_range (bits : List Bool) :
    bits = (List.range bits.length).map fun i => bits[i]?.getD false := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [hi]

/-- Encode a polynomial-time query for the streaming batch machine. -/
theorem encodeQuery_mem_FP {query : List Bool → List Bool} (hquery : query ∈ FP) :
    (fun x => Batch.encodeQuery (query x)) ∈ FP := by
  have hbit := getBit_mem_FP (mem_FP_comp pairFst_mem_FP hquery) UnaryFn.index
  have hentry := Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hbit
  have hbody := flatMap_range_mem_FP hentry (UnaryFn.length hquery).mem_FP
  refine mem_FP_of_eq (Cobham.appendFn_mem_FP hbody (constFn_mem_FP [false])) fun x => ?_
  simp only [List.length_replicate, Function.comp_apply, pairFst_pair, pairSnd_pair]
  change (List.range (query x).length).flatMap (fun i =>
    [true, (query x)[i]?.getD false]) ++ [false] = Batch.encodeQuery (query x)
  unfold Batch.encodeQuery
  conv_rhs => rw [list_eq_map_range (query x)]
  simp only [List.flatMap_map]

/-- Requests for one tagged answer, from low to high bits. -/
def taggedQueries (tag : Bool) (input : List Bool) (width : ℕ) : List (List Bool) :=
  (List.range width).map fun i => bitQuery (taggedInput tag input) i

/-- Both tagged answer prefixes, with the positive answer first. -/
def countQueries (input : List Bool) (width : ℕ) : List (List Bool) :=
  taggedQueries false input width ++ taggedQueries true input width

@[simp] theorem countQueries_length (input : List Bool) (width : ℕ) :
    (countQueries input width).length = 2 * width := by
  simp [countQueries, taggedQueries]
  omega

theorem taggedQueries_answers (F : List Bool → ℕ) (tag : Bool)
    (input : List Bool) (width : ℕ) :
    (taggedQueries tag input width).map (bitOracle F) =
      answerBits F (taggedInput tag input) width := by
  apply List.ext_getElem
  · simp [taggedQueries]
  · intro i hi hj
    simp [taggedQueries, answerBits]

theorem countQueries_answers (F : List Bool → ℕ) (input : List Bool) (width : ℕ) :
    (countQueries input width).map (bitOracle F) =
      answerBits F (taggedInput false input) width ++
        answerBits F (taggedInput true input) width := by
  simp [countQueries, taggedQueries_answers]

/-- Preparing all requests for one tagged value has a uniform FP machine. -/
theorem encoded_taggedQueries_mem_FP (tag : Bool) {width : List Bool → ℕ}
    (hwidth : UnaryFn width) :
    (fun input => Batch.encode (taggedQueries tag input (width input))) ∈ FP := by
  have htag : (fun z => taggedInput tag (pairFst z)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP (taggedInput_mem_FP tag)
  have hquery := bitQuery_mem_FP htag UnaryFn.index
  have hentry := encodeQuery_mem_FP hquery
  refine mem_FP_of_eq (flatMap_range_mem_FP hentry hwidth.mem_FP) fun input => ?_
  simp only [List.length_replicate, pairFst_pair, pairSnd_pair,
    Batch.encode, taggedQueries, List.flatMap_map]

/-- Preparing the complete nonadaptive request stream is polynomial time. -/
theorem encoded_countQueries_mem_FP {width : List Bool → ℕ} (hwidth : UnaryFn width) :
    (fun input => Batch.encode (countQueries input (width input))) ∈ FP := by
  refine mem_FP_of_eq (Cobham.appendFn_mem_FP
    (encoded_taggedQueries_mem_FP false hwidth)
    (encoded_taggedQueries_mem_FP true hwidth)) fun input => ?_
  simp [Batch.encode, countQueries]

end Toda.Oracle

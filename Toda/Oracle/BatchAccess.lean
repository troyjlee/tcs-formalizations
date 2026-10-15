import Toda.Oracle.CountQueries
import Complexitylib.Classes.P.StringAccess

/-!
# Polynomial-time access to a self-delimiting batch

The first false tag delimits a block. Its position is found by scanning the
even positions, with every index and loop bounded by the input length.
These total accessors also operate on malformed streams.
-/

namespace Toda.Oracle.Batch

open Complexity

def tags (bits : List Bool) (count : ℕ) : List Bool :=
  (List.range count).map fun i => bits[2 * i]?.getD false

theorem tags_cons_cons (a b : Bool) (bits : List Bool) (count : ℕ) :
    tags (a :: b :: bits) (count + 1) = a :: tags bits count := by
  simp only [tags, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

theorem tags_false (bits : List Bool) (count : ℕ) :
    ((tags (false :: bits) (count + 1)).takeWhile id).length = 0 := by
  simp [tags, List.range_succ_eq_map]

theorem leading_tags_encodeQuery (query rest : List Bool) (count : ℕ)
    (hcount : query.length < count) :
    ((tags (encodeQuery query ++ rest) count).takeWhile id).length = query.length := by
  induction query generalizing count with
  | nil =>
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
      simpa [encodeQuery] using tags_false rest count
  | cons bit query ih =>
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
      have h := ih count (by simpa using hcount)
      simpa [encodeQuery, tags_cons_cons] using congrArg Nat.succ h

def firstWidth (bits : List Bool) : ℕ := ((tags bits bits.length).takeWhile id).length

def first (bits : List Bool) : List Bool :=
  (List.range (firstWidth bits)).map fun i => bits[2 * i + 1]?.getD false

def rest (bits : List Bool) : List Bool := bits.drop (2 * firstWidth bits + 1)

@[simp] theorem firstWidth_encodeQuery (query suffix : List Bool) :
    firstWidth (encodeQuery query ++ suffix) = query.length := by
  apply leading_tags_encodeQuery
  simp only [List.length_append, encodeQuery_length]
  omega

theorem get_encodeQuery_odd (query suffix : List Bool) (index : ℕ)
    (hindex : index < query.length) :
    (encodeQuery query ++ suffix)[2 * index + 1]?.getD false = query[index]?.getD false := by
  induction query generalizing index with
  | nil => simp at hindex
  | cons bit query ih =>
      cases index with
      | zero => simp [encodeQuery]
      | succ index =>
          have h := ih index (by simpa using hindex)
          simpa [encodeQuery, Nat.mul_add, Nat.add_assoc] using h

@[simp] theorem first_encodeQuery (query suffix : List Bool) :
    first (encodeQuery query ++ suffix) = query := by
  simp only [first, firstWidth_encodeQuery]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa [hj] using get_encodeQuery_odd query suffix i hj

@[simp] theorem rest_encodeQuery (query suffix : List Bool) :
    rest (encodeQuery query ++ suffix) = suffix := by
  simp only [rest, firstWidth_encodeQuery, ← encodeQuery_length query]
  simp

@[simp] theorem first_encodeQuery_single (query : List Bool) :
    first (encodeQuery query) = query := by
  simpa using first_encodeQuery query []

@[simp] theorem rest_encodeQuery_single (query : List Bool) :
    rest (encodeQuery query) = [] := by
  simpa using rest_encodeQuery query []

theorem firstWidth_unary : UnaryFn firstWidth := by
  have hentry := getBit_mem_FP pairFst_mem_FP ((UnaryFn.const 2).mul UnaryFn.index)
  have htags : (fun bits => tags bits bits.length) ∈ FP := by
    refine mem_FP_of_eq (flatMap_range_mem_FP hentry id_mem_FP) fun bits => ?_
    simp [tags, ← List.map_eq_flatMap]
  exact UnaryFn.leadingTrueLength htags

theorem first_mem_FP : first ∈ FP := by
  have hentry := getBit_mem_FP pairFst_mem_FP
    (((UnaryFn.const 2).mul UnaryFn.index).add (UnaryFn.const 1))
  refine mem_FP_of_eq (flatMap_range_mem_FP hentry firstWidth_unary.mem_FP) fun bits => ?_
  simp [first, ← List.map_eq_flatMap]

theorem rest_mem_FP : rest ∈ FP :=
  drop_mem_FP id_mem_FP (((UnaryFn.const 2).mul firstWidth_unary).add (UnaryFn.const 1))

end Toda.Oracle.Batch

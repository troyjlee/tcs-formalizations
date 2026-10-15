import Toda.Oracle.Machine

/-! # A self-delimiting stream of Boolean-oracle requests -/

namespace Toda.Oracle.Batch

open Complexity

/-- Data bits carry a true prefix; a false tag ends the query. -/
def encodeQuery (query : List Bool) : List Bool :=
  query.flatMap (fun bit => [true, bit]) ++ [false]

def encode (queries : List (List Bool)) : List Bool := queries.flatMap encodeQuery

/-- An unfinished trailing query is discarded, so decoding is total on all
binary streams. `pending` contains the already consumed current query. -/
def decodeFrom (pending : List Bool) : List Bool → List (List Bool)
  | [] => []
  | false :: rest => pending :: decodeFrom [] rest
  | true :: [] => []
  | true :: bit :: rest => decodeFrom (pending ++ [bit]) rest

def decode (stream : List Bool) : List (List Bool) := decodeFrom [] stream

/-- Exact runtime from the tag-reading state, including an eventual halt. -/
def costFrom (pending : List Bool) : List Bool → ℕ
  | [] => 1
  | false :: rest => pending.length + 5 + costFrom [] rest
  | true :: [] => 2
  | true :: bit :: rest => 2 + costFrom (pending ++ [bit]) rest

theorem decodeFrom_encodeQuery (pending query rest : List Bool) :
    decodeFrom pending (encodeQuery query ++ rest) =
      (pending ++ query) :: decodeFrom [] rest := by
  induction query generalizing pending with
  | nil => simp [encodeQuery, decodeFrom]
  | cons bit query ih =>
    simpa [encodeQuery, decodeFrom, List.append_assoc] using ih (pending ++ [bit])

@[simp] theorem decode_encode (queries : List (List Bool)) :
    decode (encode queries) = queries := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
    change decodeFrom [] (encodeQuery query ++ encode queries) = _
    rw [decodeFrom_encodeQuery]
    simpa [decode] using congrArg (List.cons query) ih

@[simp] theorem encodeQuery_length (query : List Bool) :
    (encodeQuery query).length = 2 * query.length + 1 := by
  induction query with
  | nil => simp [encodeQuery]
  | cons bit query ih =>
    simp only [encodeQuery, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢
    omega

theorem costFrom_le (stream : List Bool) : ∀ pending,
    costFrom pending stream ≤ 5 * stream.length + pending.length + 1 := by
  induction stream using List.twoStepInduction with
  | nil => intro pending; simp [costFrom]
  | singleton bit =>
    intro pending
    cases bit <;> simp [costFrom] <;> omega
  | cons_cons tag bit rest ih1 ih2 =>
    intro pending
    cases tag with
    | false =>
      have h := ih2 bit ([] : List Bool)
      simp only [costFrom, List.length_cons, List.length_nil] at h ⊢
      omega
    | true =>
      have h := ih1 (pending ++ [bit])
      simp only [costFrom, List.length_cons, List.length_append,
        List.length_nil] at h ⊢
      omega

theorem costFrom_encodeQuery (pending query rest : List Bool) :
    costFrom pending (encodeQuery query ++ rest) =
      pending.length + 3 * query.length + 5 + costFrom [] rest := by
  induction query generalizing pending with
  | nil => simp [encodeQuery, costFrom]
  | cons bit query ih =>
    have h := ih (pending ++ [bit])
    simp only [encodeQuery, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc, costFrom, List.length_append, List.length_singleton] at h ⊢
    simp only [List.length_cons]
    omega

theorem costFrom_encode (queries : List (List Bool)) :
    costFrom [] (encode queries) =
      1 + (queries.map (fun query => 3 * query.length + 5)).sum := by
  induction queries with
  | nil => simp [encode, costFrom]
  | cons query queries ih =>
    change costFrom [] (encodeQuery query ++ encode queries) = _
    rw [costFrom_encodeQuery, ih]
    simp
    omega

end Toda.Oracle.Batch

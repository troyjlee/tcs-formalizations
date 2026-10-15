import Toda.Oracle.FunctionBatch.Defs
import Toda.Counting.PolynomialClock

/-! # Polynomial bounds for streaming full binary answers -/

namespace Toda.Oracle.FunctionBatch

open Complexity

/-- Query construction and all encoded answer writes are charged. The cap
bounds the current prefix together with all unconsumed stream positions. -/
theorem costFrom_le (oracle : FunctionOracle) (stream : List Bool)
    (cap answerBound : ℕ)
    (hanswer : ∀ query : List Bool, query.length ≤ cap →
      (oracle query).bits.length ≤ answerBound) :
    ∀ pending, pending.length + stream.length ≤ cap →
      costFrom oracle pending stream ≤
        (2 * answerBound + 6) * stream.length + pending.length + 1 := by
  induction stream using List.twoStepInduction with
  | nil => intro pending _; simp [costFrom]
  | singleton bit =>
      intro pending hcap
      have ha := hanswer pending (by
        simp only [List.length_singleton] at hcap
        omega)
      cases bit <;> simp [costFrom] <;> omega
  | cons_cons tag bit rest ih1 ih2 =>
      intro pending hcap
      cases tag with
      | false =>
          have ha := hanswer pending (by
            simp only [List.length_cons] at hcap
            omega)
          have h := ih2 bit [] (by simp only [List.length_nil, List.length_cons] at *; omega)
          simp only [costFrom, List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one] at h ⊢
          omega
      | true =>
          have h := ih1 (pending ++ [bit]) (by
            simp only [List.length_append, List.length_cons, List.length_nil] at *
            omega)
          simp only [costFrom, List.length_cons, List.length_append, List.length_nil,
            Nat.mul_add, Nat.mul_one] at h ⊢
          omega

theorem encoded_answers_length_le_costFrom (oracle : FunctionOracle)
    (stream : List Bool) : ∀ pending,
    (Batch.encode ((Batch.decodeFrom pending stream).map fun query => (oracle query).bits)).length ≤
      costFrom oracle pending stream := by
  induction stream using List.twoStepInduction with
  | nil => intro pending; simp [Batch.decodeFrom, Batch.encode, costFrom]
  | singleton bit =>
      intro pending
      cases bit <;> simp [Batch.decodeFrom, Batch.encode, costFrom]
      omega
  | cons_cons tag bit rest ih1 ih2 =>
      intro pending
      cases tag with
      | false =>
          have h := ih2 bit []
          simp only [Batch.decodeFrom, List.map_cons, Batch.encode, List.flatMap_cons,
            List.length_append, Batch.encodeQuery_length, costFrom] at h ⊢
          omega
      | true =>
          have h := ih1 (pending ++ [bit])
          simp only [Batch.decodeFrom, costFrom]
          omega

theorem answers_length_le_costFrom (oracle : FunctionOracle) (stream : List Bool) :
    (answers oracle stream).length ≤ costFrom oracle [] stream :=
  encoded_answers_length_le_costFrom oracle stream []

/-- A clock for a complete batch, including the initial boot step. -/
def batchClock (coefficient exponent length : ℕ) : ℕ :=
  (2 * (Counting.polynomialClock coefficient exponent length + 1) + 6) * length + 2

theorem batchClock_polyBound (coefficient exponent : ℕ) :
    PolyBound (batchClock coefficient exponent) :=
  ((((PolyBound.const 2).mul
    ((Counting.polynomialClock_polyBound coefficient exponent).add (PolyBound.const 1))).add
      (PolyBound.const 6)).mul PolyBound.id).add (PolyBound.const 2)

theorem batchClock_mono (coefficient exponent : ℕ) :
    Monotone (batchClock coefficient exponent) := by
  intro first second h
  unfold batchClock
  exact Nat.add_le_add_right (Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (Counting.polynomialClock_mono coefficient exponent h) 1)) 6) h) 2

/-- One polynomial bound covers every input stream, including malformed ones.
Only the binary length of a #P answer enters this runtime bound. -/
theorem exists_polynomial_cost_bound {oracle : FunctionOracle} (horacle : oracle ∈ SharpP) :
    ∃ coefficient exponent, ∀ stream,
      costFrom oracle [] stream + 1 ≤ batchClock coefficient exponent stream.length := by
  obtain ⟨coefficient, exponent, hanswer⟩ := Counting.sharpP_exists_value_size_bound horacle
  refine ⟨coefficient, exponent, fun stream => ?_⟩
  have hbound := costFrom_le oracle stream stream.length
    (Counting.polynomialClock coefficient exponent stream.length + 1)
    (fun query hquery => ?_) [] (by simp)
  · simpa [batchClock] using Nat.add_le_add_right hbound 1
  · rw [Nat.size_eq_bits_len]
    exact (hanswer query).2.trans
      (Nat.add_le_add_right (Counting.polynomialClock_mono coefficient exponent hquery) 1)

end Toda.Oracle.FunctionBatch

import Toda.Counting.UniformAmplification
import Toda.Counting.BoundedSum
import Toda.Arithmetic.ParityCounting

/-!
# A GapP encoding of an exact parity count

Uniform amplification and uniform summation realize the arithmetic parity-count
identity inside the canonical counting classes. One GapP value, reduced modulo
`2^(q(x)+1)`, equals the number of width-`q(x)` strings whose paired-input count
is odd. Equivalently, the value is a difference of two actual #P counts.

This is an exact counting-class encoding. An oracle-machine implementation of
the subtraction and modular reduction, with query/answer costs, is separate.
-/

namespace Toda.Counting

open Complexity Arithmetic

/-- Sum the uniformly amplified values over all strings of the requested width. -/
def amplifiedSum (f : List Bool → ℤ) (q : List Bool → ℕ) (x : List Bool) : ℤ :=
  ∑ y : Fin (q x) → Bool,
    amplifyIterate (amplificationRounds (q x)) (f (pair x (List.ofFn y)))

/-- The amplified sum is a single canonical GapP function, with a round count
depending on the original input and shared by all summands. -/
theorem gapP_amplifiedSum {f : List Bool → ℤ} {q : List Bool → ℕ}
    (hf : f ∈ GapP) (hq : UnaryFn q) : amplifiedSum f q ∈ GapP := by
  have ha := gapP_amplifyRounds hf (hq.comp pairFst_mem_FP)
  change (fun x => amplifiedSum f q x) ∈ GapP
  simpa only [pairFst_pair, amplifiedSum] using gapP_sum_bits ha hq

/-- Reducing the amplified sum recovers the exact odd-value count, including
negative source values and width zero. -/
theorem amplifiedSum_emod_eq_odd_count (f : List Bool → ℤ) (q : List Bool → ℕ)
    (x : List Bool) :
    amplifiedSum f q x % (2 ^ (q x + 1)) =
      ((Finset.univ.filter fun y : Fin (q x) → Bool =>
        f (pair x (List.ofFn y)) % 2 = 1).card : ℤ) :=
  amplified_binary_sum_emod_eq_odd_count (q x)
    (fun y => f (pair x (List.ofFn y)))

/-- Exact parity counting has a uniform encoding as a difference of two
machine-based #P functions followed by one integer remainder. -/
theorem exists_sharpP_difference_odd_count_encoding
    {f : List Bool → ℤ} {q : List Bool → ℕ} (hf : f ∈ GapP) (hq : UnaryFn q) :
    ∃ a b : List Bool → ℕ, a ∈ SharpP ∧ b ∈ SharpP ∧ ∀ x,
      ((a x : ℤ) - (b x : ℤ)) % (2 ^ (q x + 1)) =
        ((Finset.univ.filter fun y : Fin (q x) → Bool =>
          f (pair x (List.ofFn y)) % 2 = 1).card : ℤ) := by
  obtain ⟨a, b, ha, hb, hcount⟩ := gapP_amplifiedSum hf hq
  refine ⟨a, b, ha, hb, fun x => ?_⟩
  rw [← hcount x]
  exact amplifiedSum_emod_eq_odd_count f q x

end Toda.Counting

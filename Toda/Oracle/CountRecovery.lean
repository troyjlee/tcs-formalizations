import Toda.Counting.OracleBundle
import Toda.Oracle.BitOracle
import Toda.Oracle.BinaryDifference

/-!
# Recovering the odd-value count from a single #P bit oracle

The first `q(x)+1` bits of each of two tagged answers suffice. An actual FP
postprocessor performs the signed subtraction and remainder on those binary
strings. The remaining execution bridge must collect these answers and compose
that postprocessor on an oracle machine; the value theorem here does not
assert that bridge or a complexity-class inclusion.
-/

namespace Toda.Oracle

open Complexity Counting BinaryDifference

/-- The fixed binary postprocessor applied to the two tagged answer prefixes. -/
def recoveredCountBits (F : List Bool → ℕ) (input : List Bool) (width : ℕ) :
    List Bool :=
  differenceBits (answerBits F (taggedInput false input) width)
    (answerBits F (taggedInput true input) width) width

@[simp] theorem recoveredCountBits_length (F : List Bool → ℕ)
    (input : List Bool) (width : ℕ) :
    (recoveredCountBits F input width).length = width := by
  simp [recoveredCountBits]

/-- High bits of either answer cannot affect the signed remainder. -/
theorem recoveredCountBits_correct (F : List Bool → ℕ) (input : List Bool)
    (width : ℕ) :
    (Nat.fromBitsLE (recoveredCountBits F input width) : ℤ) =
      ((F (taggedInput false input) : ℤ) - F (taggedInput true input)) %
        (2 ^ width) := by
  simp only [recoveredCountBits, answerBits_eq_toBitsLE]
  exact differenceBits_toBitsLE_correct _ _ _

/-- Each tagged bit request has linear source-input overhead. -/
@[simp] theorem tagged_bitQuery_length (bit : Bool) (input : List Bool)
    (index : ℕ) :
    (bitQuery (taggedInput bit input) index).length =
      4 * input.length + 8 + index.size := by
  simp only [bitQuery_length, taggedInput_length]
  omega

/-- Preparing a tagged request uses an actual FP computation at every
unary polynomial-time index. -/
theorem tagged_bitQuery_mem_FP (bit : Bool) {index : List Bool → ℕ}
    (hindex : UnaryFn index) :
    (fun x => bitQuery (taggedInput bit x) (index x)) ∈ FP :=
  bitQuery_mem_FP (taggedInput_mem_FP bit) hindex

/-- There is one #P function whose two low-bit prefixes, followed by the
proved binary postprocessor, give the exact odd-value count. In total these
prefixes contain `2 * (q(x)+1)` Boolean answers. -/
theorem exists_single_sharpP_bit_count_recovery
    {f : List Bool → ℤ} {q : List Bool → ℕ} (hf : f ∈ GapP) (hq : UnaryFn q) :
    ∃ F : List Bool → ℕ, F ∈ SharpP ∧ ∀ x,
      Nat.fromBitsLE (recoveredCountBits F x (q x + 1)) =
        (Finset.univ.filter fun y : Fin (q x) → Bool =>
          f (pair x (List.ofFn y)) % 2 = 1).card := by
  obtain ⟨F, hF, hcount⟩ := exists_single_sharpP_odd_count_encoding hf hq
  refine ⟨F, hF, fun x => ?_⟩
  exact_mod_cast (recoveredCountBits_correct F x (q x + 1)).trans (hcount x)

/-- The implementation used after answer collection is the unconditional FP
function on an ordinary paired input, with the width supplied in unary. -/
theorem recoveredCountBits_eq_encodedDifference (F : List Bool → ℕ)
    (input : List Bool) (width : ℕ) :
    recoveredCountBits F input width = encodedDifference
      (pair (pair (answerBits F (taggedInput false input) width)
        (answerBits F (taggedInput true input) width)) (List.replicate width true)) := by
  simp [recoveredCountBits]

end Toda.Oracle

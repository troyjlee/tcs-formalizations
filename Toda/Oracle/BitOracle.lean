import Toda.Counting.PolynomialClock
import Toda.Oracle.BinaryBits
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.P.Pairing
import Complexitylib.Models.TuringMachine.Oracle

/-!
# A precise bit interface for natural-valued oracles

Queries pair the ordinary input with a canonical little-endian binary index.
Malformed pairs and noncanonical index strings receive false. Preparing a
query at a unary polynomial-time index is an actual FP computation.

The answer-reconstruction results describe the values of finitely many oracle
queries. Full-answer execution and the complete machine reduction are supplied
separately by `FunctionBatch` and `Reduction`.
-/

namespace Toda.Oracle

open Complexity

/-- Canonical query for bit `index` of the value at `input`. -/
def bitQuery (input : List Bool) (index : ℕ) : List Bool :=
  pair input index.bits

/-- A query is valid precisely when pairing and the binary index are canonical. -/
def ValidBitQuery (query : List Bool) : Prop :=
  query = pair (pairFst query) (pairSnd query) ∧
    pairSnd query = (Nat.fromBitsLE (pairSnd query)).bits

instance (query : List Bool) : Decidable (ValidBitQuery query) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The Boolean bit oracle of a natural-valued function. Evaluating the
function is the oracle operation, not an assumed polynomial-time algorithm. -/
def bitOracle (F : List Bool → ℕ) : BooleanOracle := fun query =>
  if ValidBitQuery query then
    decide (F (pairFst query) / 2 ^ Nat.fromBitsLE (pairSnd query) % 2 = 1)
  else false

@[simp] theorem validBitQuery_bitQuery (input : List Bool) (index : ℕ) :
    ValidBitQuery (bitQuery input index) := by
  simp [ValidBitQuery, bitQuery, Nat.fromBitsLE_bits]

/-- There are no other valid representations. -/
theorem validBitQuery_iff (query : List Bool) :
    ValidBitQuery query ↔ ∃ input index, query = bitQuery input index := by
  constructor
  · rintro ⟨hpair, hindex⟩
    exact ⟨pairFst query, Nat.fromBitsLE (pairSnd query),
      hpair.trans (congrArg (pair (pairFst query)) hindex)⟩
  · rintro ⟨input, index, rfl⟩
    exact validBitQuery_bitQuery input index

@[simp] theorem bitOracle_bitQuery (F : List Bool → ℕ) (input : List Bool)
    (index : ℕ) :
    bitOracle F (bitQuery input index) = decide (F input / 2 ^ index % 2 = 1) := by
  simp [bitOracle, bitQuery, ValidBitQuery, Nat.fromBitsLE_bits]

theorem bitOracle_invalid (F : List Bool → ℕ) {query : List Bool}
    (hquery : ¬ ValidBitQuery query) : bitOracle F query = false := by
  simp [bitOracle, hquery]

@[simp] theorem bitQuery_length (input : List Bool) (index : ℕ) :
    (bitQuery input index).length = 2 * input.length + 2 + index.size := by
  simp [bitQuery, Nat.size_eq_bits_len]

/-- Query preparation is polynomial time when its input and index are. The
index is unary-bounded; the oracle value itself has no such restriction. -/
theorem bitQuery_mem_FP {input : List Bool → List Bool} {index : List Bool → ℕ}
    (hinput : input ∈ FP) (hindex : UnaryFn index) :
    (fun x => bitQuery (input x) (index x)) ∈ FP :=
  mem_FP_pair hinput (bits_mem_FP hindex)

/-- Semantic list of the first `width` oracle answers, in little-endian order. -/
def answerBits (F : List Bool → ℕ) (input : List Bool) (width : ℕ) : List Bool :=
  List.ofFn fun index : Fin width => bitOracle F (bitQuery input index.val)

@[simp] theorem answerBits_length (F : List Bool → ℕ) (input : List Bool)
    (width : ℕ) : (answerBits F input width).length = width := by
  simp [answerBits]

/-- Query answers agree exactly with the fixed-width binary codec. -/
theorem answerBits_eq_toBitsLE (F : List Bool → ℕ) (input : List Bool)
    (width : ℕ) : answerBits F input width = Nat.toBitsLE width (F input) := by
  rw [toBitsLE_eq_map_range]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [answerBits]

/-- A finite prefix of the bit oracle determines the corresponding remainder. -/
theorem fromBitsLE_answerBits (F : List Bool → ℕ) (input : List Bool)
    (width : ℕ) :
    Nat.fromBitsLE (answerBits F input width) = F input % 2 ^ width := by
  rw [answerBits_eq_toBitsLE, Nat.fromBitsLE_toBitsLE_mod]

/-- A sufficiently long prefix determines the whole natural-valued answer. -/
theorem fromBitsLE_answerBits_of_lt (F : List Bool → ℕ) (input : List Bool)
    {width : ℕ} (hvalue : F input < 2 ^ width) :
    Nat.fromBitsLE (answerBits F input width) = F input := by
  rw [fromBitsLE_answerBits, Nat.mod_eq_of_lt hvalue]

/-- Every #P function has a fixed polynomial bound on the number of bit queries
needed to recover its complete answer. This is an exact value identity. -/
theorem sharpP_exists_answer_width {F : List Bool → ℕ} (hF : F ∈ SharpP) :
    ∃ A B : ℕ, ∀ input,
      Nat.fromBitsLE (answerBits F input
        (Counting.polynomialClock A B input.length + 1)) = F input := by
  obtain ⟨A, B, hbound⟩ := Counting.sharpP_exists_value_size_bound hF
  refine ⟨A, B, fun input => fromBitsLE_answerBits_of_lt F input ?_⟩
  exact (hbound input).1.trans_lt (by
    have hpos : 0 < 2 ^ Counting.polynomialClock A B input.length := by positivity
    rw [pow_succ]
    omega)

/-- Queries beyond the represented value's binary length return false. -/
theorem bitOracle_bitQuery_of_lt (F : List Bool → ℕ) (input : List Bool)
    {index : ℕ} (hvalue : F input < 2 ^ index) :
    bitOracle F (bitQuery input index) = false := by
  simp [bitOracle_bitQuery, Nat.div_eq_of_lt hvalue]

end Toda.Oracle

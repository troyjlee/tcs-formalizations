import Toda.Oracle.CountQueries
import Toda.Randomized.Class
import Toda.Parity.Class.Repetition
import Complexitylib.Languages.Contains

/-!
# A polynomial-time verdict from the two binary count answers

The answer string is split in half, then the proved binary subtraction
computes the recovered count modulo its width. Looking for a true bit in the
highest two positions tests the half-sample threshold without converting the
count, which may be exponentially large, to unary.
-/

namespace Toda.Oracle

open Complexity

/-- Decoding an arbitrary binary string is positive exactly when it contains
at least one true bit. -/
theorem fromBitsLE_pos_iff_mem_true (bits : List Bool) :
    0 < Nat.fromBitsLE bits ↔ true ∈ bits := by
  induction bits with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons bit rest ih =>
    cases bit <;> simp [Nat.fromBitsLE_cons, ih]

/-- Discarding low little-endian bits divides the value by the corresponding
power of two, including shifts beyond the represented width. -/
theorem fromBitsLE_drop (bits : List Bool) (shift : ℕ) :
    Nat.fromBitsLE (bits.drop shift) = Nat.fromBitsLE bits / 2 ^ shift := by
  by_cases hs : shift ≤ bits.length
  · have hsplit := fromBitsLE_append (bits.take shift) (bits.drop shift)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left hs] at hsplit
    have hlt := Nat.fromBitsLE_lt_pow_length (bits.take shift)
    rw [List.length_take, Nat.min_eq_left hs] at hlt
    rw [hsplit, Nat.mul_comm (2 ^ shift),
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos shift), Nat.div_eq_of_lt hlt, zero_add]
  · have hs' : bits.length ≤ shift := by omega
    have hlt : Nat.fromBitsLE bits < 2 ^ shift :=
      (Nat.fromBitsLE_lt_pow_length bits).trans_le (Nat.pow_le_pow_right (by decide) hs')
    rw [List.drop_eq_nil_of_le hs', Nat.div_eq_of_lt hlt]
    rfl

/-- A true bit at or above `shift` is an exact binary threshold test. -/
theorem mem_true_drop_iff (bits : List Bool) (shift : ℕ) :
    true ∈ bits.drop shift ↔ 2 ^ shift ≤ Nat.fromBitsLE bits := by
  rw [← fromBitsLE_pos_iff_mem_true, fromBitsLE_drop]
  rw [Nat.div_pos_iff]
  simp

/-- Recover a fixed-width modular difference from two concatenated equal-width
answer prefixes. For malformed or odd-length inputs the splitting is total. -/
def answerDifference (answers : List Bool) : List Bool :=
  BinaryDifference.differenceBits (answers.take (answers.length / 2))
    (answers.drop (answers.length / 2)) (answers.length / 2)

/-- Retain the highest two result bits (or all bits at widths below two). -/
def thresholdBits (answers : List Bool) : List Bool :=
  (answerDifference answers).drop (answers.length / 2 - 2)

/-- The ordinary binary output verdict, always exactly one bit. -/
def countVerdict (answers : List Bool) : List Bool :=
  [decide (true ∈ thresholdBits answers)]

theorem answerDifference_mem_FP : answerDifference ∈ FP := by
  have hw := (UnaryFn.length id_mem_FP).div (UnaryFn.const 2)
  exact BinaryDifference.differenceBits_mem_FP
    (take_mem_FP id_mem_FP hw) (drop_mem_FP id_mem_FP hw) hw

theorem thresholdBits_mem_FP : thresholdBits ∈ FP :=
  drop_mem_FP answerDifference_mem_FP
    (((UnaryFn.length id_mem_FP).div (UnaryFn.const 2)).sub (UnaryFn.const 2))

/-- The complete threshold verdict is an actual machine-based FP function. -/
theorem countVerdict_mem_FP : countVerdict ∈ FP := by
  have hp : FPPred fun bits : List Bool => bits ∈ Language.containsOne :=
    mem_P_iff_exists_decisionFn.mp containsOne_mem_P
  have hcontains : FPPred fun bits : List Bool => true ∈ bits :=
    hp.of_iff fun bits => by simp [Language.containsOne]
  exact (hcontains.comp thresholdBits_mem_FP).flag_mem_FP

theorem countVerdict_eq_true_iff (answers : List Bool) :
    countVerdict answers = [true] ↔
      2 ^ (answers.length / 2 - 2) ≤ Nat.fromBitsLE (answerDifference answers) := by
  simp only [countVerdict, List.cons.injEq, and_true, decide_eq_true_eq,
    thresholdBits, mem_true_drop_iff]

theorem answerDifference_append (a b : List Bool) (hlen : b.length = a.length) :
    answerDifference (a ++ b) = BinaryDifference.differenceBits a b a.length := by
  have hhalf : (a.length + a.length) / 2 = a.length := by omega
  simp [answerDifference, hlen, hhalf]

/-- The streaming query answer list produces exactly the already proved
recovered-count bit string. -/
theorem answerDifference_countQueries (F : List Bool → ℕ) (input : List Bool)
    (width : ℕ) :
    answerDifference ((countQueries input width).map (bitOracle F)) =
      recoveredCountBits F input width := by
  rw [countQueries_answers, answerDifference_append _ _ (by simp)]
  simp [recoveredCountBits]

/-- Width `q+1` tests threshold `2^(q-1)`. At `q=0` this is threshold one,
so the sole seed is accepted exactly when its parity predicate accepts. -/
theorem countVerdict_countQueries_iff (F : List Bool → ℕ) (input : List Bool)
    (q : ℕ) :
    countVerdict ((countQueries input (q+1)).map (bitOracle F)) = [true] ↔
      2 ^ (q - 1) ≤ Nat.fromBitsLE (recoveredCountBits F input (q+1)) := by
  rw [countVerdict_eq_true_iff, answerDifference_countQueries]
  simp only [List.length_map, countQueries_length]
  have heq : 2 * (q + 1) / 2 - 2 = q - 1 := by omega
  rw [heq]

end Toda.Oracle

namespace Toda.Randomized

open Complexity Toda.Parity

private theorem large_count_threshold (n good bad : ℕ)
    (htotal : good + bad = 2 ^ n) (hbad : 16 * bad ≤ 2 ^ n) :
    2 ^ (n - 1) ≤ good := by
  cases n with
  | zero => simp only [pow_zero, Nat.zero_sub] at htotal hbad ⊢; omega
  | succ n =>
    have hpos : 0 < 2 ^ n := by positivity
    simp only [Nat.succ_sub_one, pow_succ] at htotal hbad ⊢
    omega

private theorem small_count_threshold (n good : ℕ) (hgood : 16 * good ≤ 2 ^ n) :
    good < 2 ^ (n - 1) := by
  cases n with
  | zero => simp only [pow_zero, Nat.zero_sub] at hgood ⊢; omega
  | succ n =>
    have hpos : 0 < 2 ^ n := by positivity
    simp only [Nat.succ_sub_one, pow_succ] at hgood ⊢
    omega

/-- The error promise separates the true and false instances by the half-seed
threshold. The natural subtraction in the exponent also handles zero seed
bits, where the threshold is one. -/
theorem mem_iff_seedEvent_card_threshold (language predicate : Language)
    (width : List Bool → ℕ) (input : List Bool)
    (herror : 16 * (errorSeeds language predicate width input).card ≤ 2 ^ width input) :
    input ∈ language ↔
      2 ^ (width input - 1) ≤ (seedEvent predicate input (width input)).card := by
  classical
  by_cases hin : input ∈ language
  · have herr : errorSeeds language predicate width input =
        (seedEvent predicate input (width input))ᶜ := by
      ext seed
      simp [errorSeeds, seedEvent, hin]
    have htotal := Finset.card_add_card_compl (seedEvent predicate input (width input))
    rw [← herr] at htotal
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htotal
    simp only [hin, true_iff]
    exact large_count_threshold (width input) _ _ htotal herror
  · have herr : errorSeeds language predicate width input =
        seedEvent predicate input (width input) := by
      ext seed
      simp [errorSeeds, seedEvent, hin]
    rw [herr] at herror
    simp only [hin, false_iff, not_le]
    exact small_count_threshold (width input) _ herror

/-- The same threshold expressed through any GapP representative of the
canonical parity predicate. -/
theorem mem_iff_odd_count_threshold (language predicate : Language)
    (width : List Bool → ℕ) (f : List Bool → ℤ)
    (hpredicate : ∀ z, z ∈ predicate ↔ f z % 2 = 1) (input : List Bool)
    (herror : 16 * (errorSeeds language predicate width input).card ≤ 2 ^ width input) :
    input ∈ language ↔
      2 ^ (width input - 1) ≤
        (Finset.univ.filter fun seed : Fin (width input) → Bool =>
          f (pair input (List.ofFn seed)) % 2 = 1).card := by
  have heq : seedEvent predicate input (width input) =
      Finset.univ.filter (fun seed : Fin (width input) → Bool =>
        f (pair input (List.ofFn seed)) % 2 = 1) := by
    ext seed
    simp [seedEvent, hpredicate]
  rw [← heq]
  exact mem_iff_seedEvent_card_threshold language predicate width input herror

/-- Every bounded-error parity witness has one #P oracle and a uniform query
width whose collected answers are classified by the fixed FP verdict.
This statement specifies the query/postprocessing computation; executing its
batch on an oracle machine is a separate theorem. -/
theorem bpParityP_exists_countVerdict {language : Language}
    (hlanguage : language ∈ BPParityP) :
    ∃ (F : List Bool → ℕ) (width : List Bool → ℕ),
      F ∈ SharpP ∧ UnaryFn width ∧ ∀ input,
        input ∈ language ↔
          Toda.Oracle.countVerdict
            ((Toda.Oracle.countQueries input (width input + 1)).map
              (Toda.Oracle.bitOracle F)) = [true] := by
  obtain ⟨predicate, width, hpredicate, hwidth, herror⟩ := hlanguage
  obtain ⟨f, hf, hparity⟩ := mem_parityP_iff_gapP.mp hpredicate
  obtain ⟨F, hF, hcount⟩ := Toda.Oracle.exists_single_sharpP_bit_count_recovery hf hwidth
  refine ⟨F, width, hF, hwidth, fun input => ?_⟩
  rw [Toda.Oracle.countVerdict_countQueries_iff, hcount]
  exact mem_iff_odd_count_threshold language predicate width f hparity input (herror input)

end Toda.Randomized

import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.Pairing
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Polynomial-time subtraction of binary oracle answers

A ripple-borrow cursor has unary size linear in the bit position. Neither
operand is ever converted to unary. The result has exactly the prescribed
width and represents signed subtraction modulo the corresponding power of two.
-/

namespace Toda.Oracle.BinaryDifference

open Complexity

def bitValue (bits : List Bool) (i : ℕ) : ℕ :=
  if bits[i]?.getD false then 1 else 0

theorem bitValue_le (bits : List Bool) (i : ℕ) : bitValue bits i ≤ 1 := by
  unfold bitValue
  split <;> omega

def nextBorrow (a b c : ℕ) : ℕ := if a < b + c then 1 else 0

def borrow (a b : List Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => nextBorrow (bitValue a i) (bitValue b i) (borrow a b i)

theorem borrow_le (a b : List Bool) (i : ℕ) : borrow a b i ≤ 1 := by
  cases i with
  | zero => simp [borrow]
  | succ i => simp only [borrow, nextBorrow]; split <;> omega

def digit (a b : List Bool) (i : ℕ) : ℕ :=
  (bitValue a i + 2 - bitValue b i - borrow a b i) % 2

theorem digit_le (a b : List Bool) (i : ℕ) : digit a b i ≤ 1 := by
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

def differenceBits (a b : List Bool) (width : ℕ) : List Bool :=
  (List.range width).map fun i => decide (digit a b i = 1)

@[simp] theorem length_differenceBits (a b : List Bool) (width : ℕ) :
    (differenceBits a b width).length = width := by
  simp [differenceBits]

theorem digit_step (a b : List Bool) (i : ℕ) :
    (digit a b i : ℤ) = (bitValue a i : ℤ) - bitValue b i - borrow a b i +
      2 * borrow a b (i + 1) := by
  have ha := bitValue_le a i
  have hb := bitValue_le b i
  have hc := borrow_le a b i
  simp only [digit, borrow, nextBorrow]
  split <;> omega

theorem fromBitsLE_append (a b : List Bool) :
    Nat.fromBitsLE (a ++ b) = Nat.fromBitsLE a + 2 ^ a.length * Nat.fromBitsLE b := by
  induction a with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons x xs ih =>
      simp only [List.cons_append, Nat.fromBitsLE_cons, ih, List.length_cons, pow_succ]
      ring

theorem fromBitsLE_take_succ (a : List Bool) (i : ℕ) :
    Nat.fromBitsLE (a.take (i+1)) =
      Nat.fromBitsLE (a.take i) + 2 ^ i * bitValue a i := by
  by_cases hi : i < a.length
  · rw [List.take_succ_eq_append_getElem hi, fromBitsLE_append]
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi),
      bitValue, List.getElem?_eq_getElem hi,
      Nat.fromBitsLE, Nat.fromBits]
  · have hi' : a.length ≤ i := by omega
    simp [(List.take_eq_self_iff a).mpr hi',
      (List.take_eq_self_iff a).mpr (by omega : a.length ≤ i + 1),
      bitValue, List.getElem?_eq_none hi']

theorem differenceBits_value (a b : List Bool) (width : ℕ) :
    (Nat.fromBitsLE (differenceBits a b width) : ℤ) =
      (Nat.fromBitsLE (a.take width) : ℤ) - Nat.fromBitsLE (b.take width) +
        2 ^ width * borrow a b width := by
  induction width with
  | zero => simp [differenceBits, borrow, Nat.fromBitsLE, Nat.fromBits]
  | succ width ih =>
      have hd : (if decide (digit a b width = 1) then 1 else 0 : ℕ) = digit a b width := by
        have hl := digit_le a b width
        split <;> simp_all
        omega
      have hs := digit_step a b width
      have hw : differenceBits a b (width + 1) =
          differenceBits a b width ++ [decide (digit a b width = 1)] := by
        simp [differenceBits, List.range_succ]
      rw [hw, fromBitsLE_append, length_differenceBits]
      have hempty : Nat.fromBitsLE [] = 0 := rfl
      simp only [Nat.fromBitsLE_cons, hempty, mul_zero, add_zero, hd,
        Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [ih, fromBitsLE_take_succ, fromBitsLE_take_succ]
      push_cast
      rw [hs, pow_succ]
      ring

theorem fromBitsLE_take_modEq (a : List Bool) (width : ℕ) :
    (Nat.fromBitsLE a : ℤ) ≡ Nat.fromBitsLE (a.take width) [ZMOD (2 ^ width)] := by
  by_cases hw : width ≤ a.length
  · have heq := fromBitsLE_append (a.take width) (a.drop width)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left hw] at heq
    rw [heq]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact Int.modEq_iff_dvd.mpr ⟨-(Nat.fromBitsLE (a.drop width) : ℤ), by ring⟩
  · rw [(List.take_eq_self_iff a).mpr (by omega)]

/-- Decoding the result gives the Euclidean remainder of the signed difference,
including negative differences and width zero. -/
theorem differenceBits_correct (a b : List Bool) (width : ℕ) :
    (Nat.fromBitsLE (differenceBits a b width) : ℤ) =
      ((Nat.fromBitsLE a : ℤ) - Nat.fromBitsLE b) % (2 ^ width) := by
  have hcong := (fromBitsLE_take_modEq a width).sub (fromBitsLE_take_modEq b width)
  have hout : (Nat.fromBitsLE (differenceBits a b width) : ℤ) ≡
      (Nat.fromBitsLE (a.take width) : ℤ) - Nat.fromBitsLE (b.take width)
        [ZMOD (2 ^ width)] := by
    rw [differenceBits_value]
    exact Int.modEq_iff_dvd.mpr ⟨-(borrow a b width : ℤ), by ring⟩
  have hlt : (Nat.fromBitsLE (differenceBits a b width) : ℤ) < 2 ^ width := by
    exact_mod_cast (by simpa using Nat.fromBitsLE_lt_pow_length (differenceBits a b width))
  have h := (hout.trans hcong.symm)
  change _ % _ = _ % _ at h
  rwa [Int.emod_eq_of_lt (by positivity) hlt] at h

/-- Only the low `width` bits of each operand are needed. High bits may be
omitted before the polynomial-time subtraction, with no effect on its value. -/
theorem differenceBits_toBitsLE_correct (a b width : ℕ) :
    (Nat.fromBitsLE (differenceBits (Nat.toBitsLE width a)
      (Nat.toBitsLE width b) width) : ℤ) = ((a : ℤ) - b) % (2 ^ width) := by
  rw [differenceBits_correct, Nat.fromBitsLE_toBitsLE_mod, Nat.fromBitsLE_toBitsLE_mod]
  simp only [Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]
  exact (Int.sub_emod _ _ _).symm

/-- Canonical variable-width binary answers decode to the intended signed
natural-number difference. -/
theorem differenceBits_natBits_correct (a b width : ℕ) :
    Nat.fromBitsLE (differenceBits a.bits b.bits width) =
      (((a : ℤ) - b) % (2 ^ width)).toNat := by
  have h := congrArg Int.toNat (differenceBits_correct a.bits b.bits width)
  simpa only [Int.toNat_natCast, Nat.fromBitsLE_bits] using h

/-- Cursor state `2*i+c` stores a position and one borrow bit. -/
def cursorStep (a b : List Bool) (state : ℕ) : ℕ :=
  2 * (state / 2 + 1) +
    nextBorrow (bitValue a (state / 2)) (bitValue b (state / 2)) (state % 2)

theorem cursor_iterate (a b : List Bool) (i : ℕ) :
    (cursorStep a b)^[i] 0 = 2 * i + borrow a b i := by
  induction i with
  | zero => simp [borrow]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      have hb := borrow_le a b i
      have hdiv : (2 * i + borrow a b i) / 2 = i := by omega
      have hmod : (2 * i + borrow a b i) % 2 = borrow a b i := by omega
      simp only [cursorStep, hdiv, hmod, borrow]

/-- A selected binary digit is unary-computable because its value is at most
one; this does not convert the full operand value to unary. -/
theorem bitValue_unary {bits : List Bool → List Bool} {i : List Bool → ℕ}
    (hbits : bits ∈ FP) (hi : UnaryFn i) :
    UnaryFn fun z => bitValue (bits z) (i z) :=
  UnaryFn.ite (FPPred.getBit hbits hi) (UnaryFn.const 1) (UnaryFn.const 0)

theorem cursorStep_unary {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    UnaryFn fun w => cursorStep (a (pairFst w)) (b (pairFst w)) (pairSnd w).length := by
  have hi := UnaryFn.index.div (UnaryFn.const 2)
  have hrem := UnaryFn.index.mod (UnaryFn.const 2)
  have hba := bitValue_unary (mem_FP_comp pairFst_mem_FP ha) hi
  have hbb := bitValue_unary (mem_FP_comp pairFst_mem_FP hb) hi
  exact ((UnaryFn.const 2).mul (hi.add (UnaryFn.const 1))).add
    (UnaryFn.ite (FPPred.lt hba (hbb.add hrem)) (UnaryFn.const 1) (UnaryFn.const 0))

theorem borrow_unary {a b : List Bool → List Bool} {i : List Bool → ℕ}
    (ha : a ∈ FP) (hb : b ∈ FP) (hi : UnaryFn i) :
    UnaryFn fun z => borrow (a z) (b z) (i z) := by
  have hrun := UnaryFn.iterate (s := fun z => cursorStep (a z) (b z))
    (cursorStep_unary ha hb) (UnaryFn.const 0) hi
    (((UnaryFn.const 2).mul hi).add (UnaryFn.const 1)) (by
      intro z j hj
      rw [cursor_iterate]
      have hc := borrow_le (a z) (b z) j
      omega)
  apply (hrun.mod (UnaryFn.const 2)).of_eq
  intro z
  rw [cursor_iterate]
  have hc := borrow_le (a z) (b z) (i z)
  omega

theorem digit_unary {a b : List Bool → List Bool} {i : List Bool → ℕ}
    (ha : a ∈ FP) (hb : b ∈ FP) (hi : UnaryFn i) :
    UnaryFn fun z => digit (a z) (b z) (i z) :=
  ((((bitValue_unary ha hi).add (UnaryFn.const 2)).sub
    (bitValue_unary hb hi)).sub (borrow_unary ha hb hi)).mod (UnaryFn.const 2)

/-- Binary subtraction modulo a unary-computable power-of-two width is a
canonical machine-based `FP` function, even for exponentially large values. -/
theorem differenceBits_mem_FP {a b : List Bool → List Bool} {width : List Bool → ℕ}
    (ha : a ∈ FP) (hb : b ∈ FP) (hw : UnaryFn width) :
    (fun z => differenceBits (a z) (b z) (width z)) ∈ FP := by
  have hd := digit_unary (mem_FP_comp pairFst_mem_FP ha)
    (mem_FP_comp pairFst_mem_FP hb) UnaryFn.index
  apply bitwise_mem_FP hw (FPPred.eq hd (UnaryFn.const 1)).flag_mem_FP
  intro z i
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]

/-- The ordinary string input contains two binary operands and a unary width.
Malformed pairs still have total projections and therefore a total result. -/
def encodedDifference (z : List Bool) : List Bool :=
  differenceBits (pairFst (pairFst z)) (pairSnd (pairFst z)) (pairSnd z).length

theorem encodedDifference_mem_FP : encodedDifference ∈ FP :=
  differenceBits_mem_FP (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) UnaryFn.index

@[simp] theorem encodedDifference_pair (a b : List Bool) (width : ℕ) :
    encodedDifference (pair (pair a b) (List.replicate width true)) =
      differenceBits a b width := by
  simp [encodedDifference]

end Toda.Oracle.BinaryDifference

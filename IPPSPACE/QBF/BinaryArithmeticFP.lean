/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.BinaryNamesFP
import Mathlib.Data.Nat.Bitwise

/-!
# Arithmetic on arbitrarily large binary names

Successor, comparison, and maximum operate on little-endian digits. Their actual
upstream `FP` certificates depend on the length of those digits; the numeric
name values are never required to be unary polynomial-time.
-/

namespace IPPSPACE

open Complexity

/-- Carry through the low true bits, retaining any redundant high zeroes. -/
def incrementNameBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: incrementNameBits bits

@[simp] theorem nameBitsValue_increment (bits : List Bool) :
    nameBitsValue (incrementNameBits bits) = nameBitsValue bits + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b <;> simp only [incrementNameBits, nameBitsValue, List.foldr_cons,
      Nat.bit_false, Nat.bit_true] at ih ⊢; omega

theorem incrementNameBits_length_le (bits : List Bool) :
    (incrementNameBits bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [incrementNameBits]
  | cons b bits ih => cases b <;> simp [incrementNameBits]; omega

theorem incrementNameBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => incrementNameBits (bits z)) ∈ FP := by
  obtain ⟨P, hP⟩ := Cobham.output_length_poly_of_mem_FP hbits
  have hfalse := mem_FP_comp pairSnd_mem_FP (Cobham.cons_mem_FP true)
  have htrue := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (Cobham.cons_mem_FP false)
  apply recFold_mem_FP_of_bound (g := fun _ bits => incrementNameBits bits)
    (w := fun _ => []) (E := fun _ => [true]) hfalse htrue
    (constFn_mem_FP _) (constFn_mem_FP _) hbits
  · intro z; rfl
  · intro z bits; simp [incrementNameBits]
  · intro z bits; simp [incrementNameBits]
  · exact PolyBound.eval (P + 1)
  · intro z bits hbits
    have hlen := (incrementNameBits_length_le bits).trans
      (Nat.add_le_add_right (hbits.length_le.trans (hP z)) 1)
    simpa using hlen

/-- Canonical binary successor, including zero and inputs with high zero padding. -/
theorem nameBitsValue_succ_bits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => (nameBitsValue (bits z) + 1).bits) ∈ FP := by
  apply mem_FP_of_eq (normalizeNameBits_mem_FP (incrementNameBits_mem_FP hbits))
  intro z
  rw [normalizeNameBits_eq_bits, nameBitsValue_increment]

theorem binaryName_succ_mem_FP {name : List Bool → ℕ}
    (hname : (fun z => (name z).bits) ∈ FP) :
    (fun z => (name z + 1).bits) ∈ FP := by
  simpa only [nameBitsValue_bits] using nameBitsValue_succ_bits_mem_FP hname

@[simp] theorem nameBitsValue_testBit (bits : List Bool) (i : ℕ) :
    (nameBitsValue bits).testBit i = bits[i]?.getD false := by
  induction bits generalizing i with
  | nil => simp [nameBitsValue]
  | cons b bits ih =>
    cases i with
    | zero => simp [nameBitsValue]
    | succ i => simpa only [nameBitsValue, List.foldr_cons, Nat.testBit_bit_succ,
        List.getElem?_cons_succ] using ih i

theorem nameBitsValue_drop_testBit (bits : List Bool) (k j : ℕ) :
    (nameBitsValue (bits.drop k)).testBit j = (nameBitsValue bits).testBit (k + j) := by
  simp only [nameBitsValue_testBit, List.getElem?_drop]

private theorem nat_lt_iff_mostBit (n m : ℕ) :
    n < m ↔ ∃ i, n.testBit i = false ∧ m.testBit i = true ∧
      ∀ j, i < j → n.testBit j = m.testBit j := by
  have hbool (a b : Bool) : (a ^^ b) = false ↔ a = b := by cases a <;> cases b <;> decide
  constructor
  · intro hlt
    have hxor : n ^^^ m ≠ 0 := by
      intro hz
      have heq : n = m := Nat.eq_of_testBit_eq (fun i => by
        have h := congrArg (fun v : ℕ => v.testBit i) hz
        exact (hbool _ _).mp (by simpa only [Nat.testBit_xor, Nat.zero_testBit] using h))
      omega
    obtain ⟨i, hi, hhigher⟩ := Nat.exists_most_significant_bit hxor
    have heq (j : ℕ) (hj : i < j) : n.testBit j = m.testBit j := by
      have h := hhigher j hj
      exact (hbool _ _).mp (by simpa only [Nat.testBit_xor] using h)
    cases hn : n.testBit i <;> cases hm : m.testBit i
    · simp [Nat.testBit_xor, hn, hm] at hi
    · exact ⟨i, hn, hm, heq⟩
    · have hgt := Nat.lt_of_testBit i hm hn (fun j hj => (heq j hj).symm)
      omega
    · simp [Nat.testBit_xor, hn, hm] at hi
  · rintro ⟨i, hn, hm, heq⟩
    exact Nat.lt_of_testBit i hn hm heq

/-- Compare at the most significant differing bit; equal high tails are tested
as binary names, including arbitrary redundant high zeroes. -/
theorem nameBitsValue_lt_iff (left right : List Bool) :
    nameBitsValue left < nameBitsValue right ↔
      ∃ i < right.length, left[i]?.getD false = false ∧ right[i]?.getD false = true ∧
        nameBitsValue (left.drop (i + 1)) = nameBitsValue (right.drop (i + 1)) := by
  rw [nat_lt_iff_mostBit]
  constructor
  · rintro ⟨i, hl, hr, hhigher⟩
    have hi : i < right.length := by
      by_contra h
      simp [nameBitsValue_testBit, List.getElem?_eq_none (Nat.le_of_not_lt h)] at hr
    refine ⟨i, hi, by simpa using hl, by simpa using hr, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro j
    rw [nameBitsValue_drop_testBit, nameBitsValue_drop_testBit]
    exact hhigher _ (by omega)
  · rintro ⟨i, _, hl, hr, htail⟩
    refine ⟨i, by simpa using hl, by simpa using hr, ?_⟩
    intro j hj
    have h := congrArg (fun n : ℕ => n.testBit (j - (i + 1))) htail
    rw [nameBitsValue_drop_testBit, nameBitsValue_drop_testBit] at h
    simpa only [Nat.add_sub_of_le (show i + 1 ≤ j by omega)] using h

/-- Numeric ordering is polynomial-time in the input digit lengths. -/
theorem nameBitsValue_lt_fppred {left right : List Bool → List Bool}
    (hl : left ∈ FP) (hr : right ∈ FP) :
    FPPred fun z => nameBitsValue (left z) < nameBitsValue (right z) := by
  have hleft := mem_FP_comp pairFst_mem_FP hl
  have hright := mem_FP_comp pairFst_mem_FP hr
  have hfalse : FPPred fun z => (left (pairFst z))[(pairSnd z).length]?.getD false = false :=
    (FPPred.getBit hleft UnaryFn.index).not.of_iff (fun z => by
      simp)
  have htrue := FPPred.getBit hright UnaryFn.index
  have htail := nameBitsValue_eq_fppred
    (drop_mem_FP hleft (UnaryFn.index.add (UnaryFn.const 1)))
    (drop_mem_FP hright (UnaryFn.index.add (UnaryFn.const 1)))
  have h := FPPred.exists_lt (UnaryFn.length hr) (hfalse.and (htrue.and htail))
  refine h.of_iff (fun z => ?_)
  simpa only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate] using
    (nameBitsValue_lt_iff (left z) (right z)).symm

theorem nameBitsValue_le_fppred {left right : List Bool → List Bool}
    (hl : left ∈ FP) (hr : right ∈ FP) :
    FPPred fun z => nameBitsValue (left z) ≤ nameBitsValue (right z) :=
  (nameBitsValue_lt_fppred hr hl).not.of_iff (fun _ => Nat.not_lt)

/-- Binary maximum preserves canonical output without a unary magnitude bound. -/
theorem nameBitsValue_max_bits_mem_FP {left right : List Bool → List Bool}
    (hl : left ∈ FP) (hr : right ∈ FP) :
    (fun z => (max (nameBitsValue (left z)) (nameBitsValue (right z))).bits) ∈ FP := by
  have h := (nameBitsValue_le_fppred hl hr).ite_mem_FP
    (nameBitsValue_bits_mem_FP hr) (nameBitsValue_bits_mem_FP hl)
  apply mem_FP_of_eq h
  intro z
  split
  · rename_i hle; rw [max_eq_right hle]
  · rename_i hle; rw [max_eq_left (Nat.le_of_not_le hle)]

theorem binaryName_lt_fppred {left right : List Bool → ℕ}
    (hl : (fun z => (left z).bits) ∈ FP) (hr : (fun z => (right z).bits) ∈ FP) :
    FPPred fun z => left z < right z := by
  simpa only [nameBitsValue_bits] using nameBitsValue_lt_fppred hl hr

theorem binaryName_le_fppred {left right : List Bool → ℕ}
    (hl : (fun z => (left z).bits) ∈ FP) (hr : (fun z => (right z).bits) ∈ FP) :
    FPPred fun z => left z ≤ right z := by
  simpa only [nameBitsValue_bits] using nameBitsValue_le_fppred hl hr

theorem binaryName_max_mem_FP {left right : List Bool → ℕ}
    (hl : (fun z => (left z).bits) ∈ FP) (hr : (fun z => (right z).bits) ∈ FP) :
    (fun z => (max (left z) (right z)).bits) ∈ FP := by
  simpa only [nameBitsValue_bits] using nameBitsValue_max_bits_mem_FP hl hr

theorem nameBitsValue_iterate_increment (count : ℕ) (bits : List Bool) :
    nameBitsValue (incrementNameBits^[count] bits) = nameBitsValue bits + count := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply', nameBitsValue_increment, ih]
    omega

/-- Add a polynomially bounded fresh-name offset to an arbitrarily large name.
Every carry step grows the binary state by at most one bit. -/
theorem nameBitsValue_add_unary_bits_mem_FP {bits : List Bool → List Bool} {offset : List Bool → ℕ}
    (hb : bits ∈ FP) (hk : UnaryFn offset) :
    (fun z => (nameBitsValue (bits z) + offset z).bits) ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hiter := iterate_mem_FP_of_step_le (incrementNameBits_mem_FP hid) hb hk.mem_FP 1
    (fun z n _ => by
      rw [Function.iterate_succ_apply']
      exact incrementNameBits_length_le _)
  apply mem_FP_of_eq (normalizeNameBits_mem_FP hiter)
  intro z
  simp only [id_eq]
  rw [normalizeNameBits_eq_bits, nameBitsValue_iterate_increment, List.length_replicate]

theorem binaryName_add_unary_mem_FP {name offset : List Bool → ℕ}
    (hn : (fun z => (name z).bits) ∈ FP) (hk : UnaryFn offset) :
    (fun z => (name z + offset z).bits) ∈ FP := by
  simpa only [nameBitsValue_bits] using nameBitsValue_add_unary_bits_mem_FP hn hk

end IPPSPACE

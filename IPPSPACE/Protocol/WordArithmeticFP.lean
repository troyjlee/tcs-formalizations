/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.PrimeFieldFP
import IPPSPACE.Protocol.WordArithmetic
import IPPSPACE.Protocol.MessageEncoding

/-!
# Machine-based polynomial-time certificates for residue-word arithmetic

These certificates use actual upstream `FP` and unary-number closure theorems.
The protocol's big-endian words are identified with the upstream binary codec.
Their numeric values, even when noncanonical residues, fit a polynomial bound
when the modulus has a unary polynomial-time certificate. Checked operations
retain rejection and encode failure as the empty string. Successful residue
words have positive width. Message parsing and Horner iteration remain separate.
-/

namespace IPPSPACE

open Complexity

/-- The upstream binary writer and the protocol writer use opposite bit orders. -/
theorem toBits_mem_FP {width value : List Bool → ℕ}
    (hw : UnaryFn width) (hv : UnaryFn value) :
    (fun z => Nat.toBits (width z) (value z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (toBitsLE_mem_FP hw hv) reverse_mem_FP)
    (fun z => by simp [Nat.toBitsLE])

theorem wordBits_ofNat_eq_toBits (width value : ℕ) :
    wordBits (BitVec.ofNat width value) = Nat.toBits width value := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [wordBits, Nat.toBits,
      BitVec.setWidth_ofNat_of_le (Nat.le_succ width), ih, List.cons.injEq, and_true]
    simp only [BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel,
      BitVec.getLsbD_ofNat, Nat.lt_succ_self, decide_true, Bool.true_and]
    simp only [Nat.testBit_eq_decide_div_mod_eq, beq_eq_decide]

theorem wordBits_eq_toBits {width : ℕ} (word : BitVec width) :
    wordBits word = Nat.toBits width word.toNat := by
  simpa using wordBits_ofNat_eq_toBits width word.toNat

@[simp] theorem fromBits_wordBits {width : ℕ} (word : BitVec width) :
    Nat.fromBits (wordBits word) = word.toNat := by
  rw [wordBits_eq_toBits, Nat.fromBits_toBits word.isLt]

theorem wordBits_ofNat_mem_FP {width value : List Bool → ℕ}
    (hw : UnaryFn width) (hv : UnaryFn value) :
    (fun z => wordBits (BitVec.ofNat (width z) (value z))) ∈ FP :=
  mem_FP_of_eq (toBits_mem_FP hw hv) (fun _ => (wordBits_ofNat_eq_toBits _ _).symm)

theorem reduceResidueWord_bits_mem_FP {p value : List Bool → ℕ}
    (hp : UnaryFn p) (hv : UnaryFn value) :
    (fun z => wordBits (reduceResidueWord (p z) (value z))) ∈ FP :=
  wordBits_ofNat_mem_FP (residueWidth_unaryFn hp) (hv.mod hp)

/-- Reading an arbitrary big-endian string up to a unary-computable cap is
polynomial-time. The cap is essential: arbitrary binary values need not have
polynomially long unary representations. -/
theorem fromBits_min_unaryFn {bits : List Bool → List Bool} {cap : List Bool → ℕ}
    (hbits : bits ∈ FP) (hcap : UnaryFn cap) :
    UnaryFn fun z => min (Nat.fromBits (bits z)) (cap z) := by
  exact (UnaryFn.fromBitsLE_min (mem_FP_comp hbits reverse_mem_FP) hcap).of_eq
    (fun _ => by simp [Nat.fromBitsLE])

/-- Exact bounded big-endian decoding inherits the same machine certificate. -/
theorem fromBits_unaryFn_of_le {bits : List Bool → List Bool} {cap : List Bool → ℕ}
    (hbits : bits ∈ FP) (hcap : UnaryFn cap)
    (hbound : ∀ z, Nat.fromBits (bits z) ≤ cap z) :
    UnaryFn fun z => Nat.fromBits (bits z) :=
  (fromBits_min_unaryFn hbits hcap).of_eq (fun z => min_eq_left (hbound z))

/-- Canonical raw residue words have exactly the prescribed width and denote
a value below the modulus. This test covers arbitrary malformed input strings. -/
def CanonicalResidueBits (p : ℕ) (bits : List Bool) : Prop :=
  bits.length = residueWidth p ∧ Nat.fromBits bits < p

instance (p : ℕ) (bits : List Bool) : Decidable (CanonicalResidueBits p bits) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem canonicalResidueBits_fppred {p : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hbits : bits ∈ FP) :
    FPPred fun z => CanonicalResidueBits (p z) (bits z) := by
  refine ((FPPred.eq (UnaryFn.length hbits) (residueWidth_unaryFn hp)).and
    (FPPred.lt (fromBits_min_unaryFn hbits hp) hp)).of_iff (fun z => ?_)
  simp only [CanonicalResidueBits, min_lt_iff, lt_self_iff_false, or_false]

@[simp] theorem canonicalResidueBits_wordBits {p : ℕ}
    (word : BitVec (residueWidth p)) :
    CanonicalResidueBits p (wordBits word) ↔ word.toNat < p := by
  simp [CanonicalResidueBits]

private theorem two_pow_residueWidth_le_all (p : ℕ) : 2 ^ residueWidth p ≤ 2 * p + 2 := by
  by_cases hp : p = 0
  · simp [hp, residueWidth]
  · exact (two_pow_residueWidth_le p hp).trans (by omega)

/-- Even malformed words of the specified width have polynomially bounded
numeric values. Thus reading an FP-produced word back to unary is in FP. -/
theorem residueWordValue_unaryFn {p : List Bool → ℕ} (hp : UnaryFn p)
    (words : (z : List Bool) → BitVec (residueWidth (p z)))
    (hwords : (fun z => wordBits (words z)) ∈ FP) : UnaryFn fun z => (words z).toNat := by
  have hbound : UnaryFn fun z => 2 * p z + 2 :=
    ((UnaryFn.const 2).mul hp).add (UnaryFn.const 2)
  have hread := UnaryFn.fromBitsLE_of_le (mem_FP_comp hwords reverse_mem_FP) hbound
    (fun z => show Nat.fromBitsLE ((wordBits (words z)).reverse) ≤ 2 * p z + 2 from by
      simp only [Nat.fromBitsLE, List.reverse_reverse, fromBits_wordBits]
      exact (Nat.le_of_lt (words z).isLt).trans (two_pow_residueWidth_le_all _))
  exact hread.of_eq (fun z => by simp [Nat.fromBitsLE])

/-- Encode a failed word operation by the empty list. Successful words have
positive residue width, so the two outcomes remain distinguishable. -/
def wordResultBits {width : ℕ} (result : Option (BitVec width)) : List Bool :=
  (result.map wordBits).getD []

theorem checkedWordBinary_bits_mem_FP {p : List Bool → ℕ} (hp : UnaryFn p)
    (f : List Bool → ℕ → ℕ → ℕ)
    (a b : (z : List Bool) → BitVec (residueWidth (p z)))
    (ha : UnaryFn fun z => (a z).toNat) (hb : UnaryFn fun z => (b z).toNat)
    (hf : UnaryFn fun z => f z (a z).toNat (b z).toNat) :
    (fun z => wordResultBits (checkedWordBinary (p z) (f z) (a z) (b z))) ∈ FP := by
  refine mem_FP_of_eq
    (((FPPred.lt ha hp).and (FPPred.lt hb hp)).ite_mem_FP
      (reduceResidueWord_bits_mem_FP hp hf) (constFn_mem_FP [])) (fun z => ?_)
  by_cases h : (a z).toNat < p z ∧ (b z).toNat < p z <;>
    simp [checkedWordBinary, wordResultBits, h]

theorem wordAdd_bits_mem_FP {p : List Bool → ℕ} (hp : UnaryFn p)
    (a b : (z : List Bool) → BitVec (residueWidth (p z)))
    (ha : (fun z => wordBits (a z)) ∈ FP) (hb : (fun z => wordBits (b z)) ∈ FP) :
    (fun z => wordResultBits (wordAdd (p z) (a z) (b z))) ∈ FP := by
  have hav := residueWordValue_unaryFn hp a ha
  have hbv := residueWordValue_unaryFn hp b hb
  exact checkedWordBinary_bits_mem_FP hp (fun _ => (· + ·)) a b hav hbv (hav.add hbv)

theorem wordMul_bits_mem_FP {p : List Bool → ℕ} (hp : UnaryFn p)
    (a b : (z : List Bool) → BitVec (residueWidth (p z)))
    (ha : (fun z => wordBits (a z)) ∈ FP) (hb : (fun z => wordBits (b z)) ∈ FP) :
    (fun z => wordResultBits (wordMul (p z) (a z) (b z))) ∈ FP := by
  have hav := residueWordValue_unaryFn hp a ha
  have hbv := residueWordValue_unaryFn hp b hb
  exact checkedWordBinary_bits_mem_FP hp (fun _ => (· * ·)) a b hav hbv (hav.mul hbv)

theorem wordSub_bits_mem_FP {p : List Bool → ℕ} (hp : UnaryFn p)
    (a b : (z : List Bool) → BitVec (residueWidth (p z)))
    (ha : (fun z => wordBits (a z)) ∈ FP) (hb : (fun z => wordBits (b z)) ∈ FP) :
    (fun z => wordResultBits (wordSub (p z) (a z) (b z))) ∈ FP := by
  have hav := residueWordValue_unaryFn hp a ha
  have hbv := residueWordValue_unaryFn hp b hb
  exact checkedWordBinary_bits_mem_FP hp (fun z x y => x + p z - y) a b hav hbv ((hav.add hp).sub hbv)

theorem wordNeg_bits_mem_FP {p : List Bool → ℕ} (hp : UnaryFn p)
    (a : (z : List Bool) → BitVec (residueWidth (p z)))
    (ha : (fun z => wordBits (a z)) ∈ FP) :
    (fun z => wordResultBits (wordNeg (p z) (a z))) ∈ FP := by
  have hav := residueWordValue_unaryFn hp a ha
  refine mem_FP_of_eq ((FPPred.lt hav hp).ite_mem_FP
    (reduceResidueWord_bits_mem_FP hp (hp.sub hav)) (constFn_mem_FP [])) (fun z => ?_)
  by_cases h : (a z).toNat < p z <;> simp [wordNeg, wordResultBits, h]

/-- A total raw-string binary operation: reject noncanonical widths or residues
with the empty string, otherwise return the actual checked operation's word. -/
def checkedResidueBitsBinary (p : ℕ) (f : ℕ → ℕ → ℕ)
    (a b : List Bool) : List Bool :=
  if CanonicalResidueBits p a ∧ CanonicalResidueBits p b then
    wordBits (reduceResidueWord p (f (Nat.fromBits a) (Nat.fromBits b)))
  else []

@[simp] theorem checkedResidueBitsBinary_wordBits (p : ℕ) (f : ℕ → ℕ → ℕ)
    (a b : BitVec (residueWidth p)) :
    checkedResidueBitsBinary p f (wordBits a) (wordBits b) =
      wordResultBits (checkedWordBinary p f a b) := by
  simp only [checkedResidueBitsBinary, canonicalResidueBits_wordBits, fromBits_wordBits,
    checkedWordBinary]
  split <;> rfl

theorem checkedResidueBitsBinary_eq_nil_iff (p : ℕ) (f : ℕ → ℕ → ℕ)
    (a b : List Bool) :
    checkedResidueBitsBinary p f a b = [] ↔
      ¬ (CanonicalResidueBits p a ∧ CanonicalResidueBits p b) := by
  unfold checkedResidueBitsBinary
  split
  · rename_i h
    have hnot : wordBits (reduceResidueWord p (f (Nat.fromBits a) (Nat.fromBits b))) ≠ [] := by
      exact List.cons_ne_nil _ _
    simp [h, hnot]
  · simp_all

/-- The binary operator only needs an FP certificate on capped operands.
Canonical operands are unchanged by the cap, and other strings are rejected. -/
theorem checkedResidueBitsBinary_mem_FP {p : List Bool → ℕ}
    {a b : List Bool → List Bool} (hp : UnaryFn p) (ha : a ∈ FP) (hb : b ∈ FP)
    (f : List Bool → ℕ → ℕ → ℕ)
    (hf : UnaryFn fun z => f z (min (Nat.fromBits (a z)) (p z))
      (min (Nat.fromBits (b z)) (p z))) :
    (fun z => checkedResidueBitsBinary (p z) (f z) (a z) (b z)) ∈ FP := by
  refine mem_FP_of_eq
    (((canonicalResidueBits_fppred hp ha).and
      (canonicalResidueBits_fppred hp hb)).ite_mem_FP
        (reduceResidueWord_bits_mem_FP hp hf) (constFn_mem_FP [])) (fun z => ?_)
  by_cases h : CanonicalResidueBits (p z) (a z) ∧ CanonicalResidueBits (p z) (b z)
  · simp only [checkedResidueBitsBinary, h,
      min_eq_left (Nat.le_of_lt h.1.2), min_eq_left (Nat.le_of_lt h.2.2)]
  · simp [checkedResidueBitsBinary, h]

theorem residueBitsAdd_mem_FP {p : List Bool → ℕ} {a b : List Bool → List Bool}
    (hp : UnaryFn p) (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => checkedResidueBitsBinary (p z) (· + ·) (a z) (b z)) ∈ FP :=
  checkedResidueBitsBinary_mem_FP hp ha hb (fun _ => (· + ·))
    ((fromBits_min_unaryFn ha hp).add (fromBits_min_unaryFn hb hp))

theorem residueBitsMul_mem_FP {p : List Bool → ℕ} {a b : List Bool → List Bool}
    (hp : UnaryFn p) (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => checkedResidueBitsBinary (p z) (· * ·) (a z) (b z)) ∈ FP :=
  checkedResidueBitsBinary_mem_FP hp ha hb (fun _ => (· * ·))
    ((fromBits_min_unaryFn ha hp).mul (fromBits_min_unaryFn hb hp))

theorem residueBitsSub_mem_FP {p : List Bool → ℕ} {a b : List Bool → List Bool}
    (hp : UnaryFn p) (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => checkedResidueBitsBinary (p z) (fun x y => x + p z - y) (a z) (b z)) ∈ FP :=
  checkedResidueBitsBinary_mem_FP hp ha hb (fun z x y => x + p z - y)
    (((fromBits_min_unaryFn ha hp).add hp).sub (fromBits_min_unaryFn hb hp))

/-- Total raw-string negation with the same width/range rejection policy. -/
def residueBitsNeg (p : ℕ) (a : List Bool) : List Bool :=
  if CanonicalResidueBits p a then
    wordBits (reduceResidueWord p (p - Nat.fromBits a))
  else []

@[simp] theorem residueBitsNeg_wordBits (p : ℕ) (a : BitVec (residueWidth p)) :
    residueBitsNeg p (wordBits a) = wordResultBits (wordNeg p a) := by
  simp only [residueBitsNeg, canonicalResidueBits_wordBits, fromBits_wordBits, wordNeg]
  split <;> rfl

theorem residueBitsNeg_mem_FP {p : List Bool → ℕ} {a : List Bool → List Bool}
    (hp : UnaryFn p) (ha : a ∈ FP) :
    (fun z => residueBitsNeg (p z) (a z)) ∈ FP := by
  refine mem_FP_of_eq ((canonicalResidueBits_fppred hp ha).ite_mem_FP
    (reduceResidueWord_bits_mem_FP hp (hp.sub (fromBits_min_unaryFn ha hp)))
      (constFn_mem_FP [])) (fun z => ?_)
  by_cases h : CanonicalResidueBits (p z) (a z)
  · simp only [residueBitsNeg, h, ite_true, min_eq_left (Nat.le_of_lt h.2)]
  · simp [residueBitsNeg, h]

end IPPSPACE

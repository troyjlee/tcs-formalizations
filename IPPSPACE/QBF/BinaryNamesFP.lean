/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.EncodingFP
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.BoundedQuant

/-!
# Polynomial-time operations on arbitrary binary variable names

A variable name's numeric value need not be polynomially bounded by its binary
encoding. These results normalize, compare, and frame its bits without expanding
that value into unary. They use the actual upstream machine-based `FP` class.
-/

namespace IPPSPACE

open Complexity

/-- Remove redundant most-significant zeroes from little-endian digits. -/
def normalizeNameBits : List Bool → List Bool
  | [] => []
  | b :: bits =>
      let tail := normalizeNameBits bits
      if tail = [] then (if b then [true] else []) else b :: tail

theorem normalizeNameBits_eq_bits (bits : List Bool) :
    normalizeNameBits bits = (nameBitsValue bits).bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    by_cases hn : nameBitsValue bits = 0
    · cases b <;> simp [normalizeNameBits, ih, nameBitsValue,
        show bits.foldr Nat.bit 0 = 0 from hn, Nat.bit]
    · have hne : (nameBitsValue bits).bits ≠ [] := by
        intro heq
        have h := nameBitsValue_bits (nameBitsValue bits)
        rw [heq] at h
        exact hn h.symm
      simp only [normalizeNameBits, ih, ite_eq_right hne]
      exact (Nat.bits_append_bit _ b (fun h => (hn h).elim)).symm

theorem length_normalizeNameBits_le (bits : List Bool) :
    (normalizeNameBits bits).length ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [normalizeNameBits, List.length_cons]
    split
    · cases b <;> simp
    · simp only [List.length_cons]
      omega

@[simp] theorem normalizeNameBits_bits (n : ℕ) : normalizeNameBits n.bits = n.bits := by
  rw [normalizeNameBits_eq_bits, nameBitsValue_bits]

theorem normalizeNameBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => normalizeNameBits (bits z)) ∈ FP := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hbits
  let state : List Bool → List Bool := fun z => pairSnd (pairFst z)
  have hstate : state ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hempty : FPPred fun z => state z = [] :=
    (FPPred.eq (UnaryFn.length hstate) (UnaryFn.const 0)).of_iff fun _ => List.length_eq_zero_iff
  have hstep (b : Bool) :
      (fun z => if state z = [] then (if b then [true] else []) else b :: state z) ∈ FP :=
    hempty.ite_mem_FP (constFn_mem_FP _) (mem_FP_comp hstate (Cobham.cons_mem_FP b))
  apply recFold_mem_FP_of_bound (g := fun _ t => normalizeNameBits t)
    (w := fun _ => []) (E := fun _ => []) (hstep false) (hstep true)
    (constFn_mem_FP _) (constFn_mem_FP _) hbits
  · intro z
    rfl
  · intro z t
    simp [normalizeNameBits, state]
  · intro z t
    simp [normalizeNameBits, state]
  · exact PolyBound.eval p
  · intro z t ht
    exact (length_normalizeNameBits_le t).trans (ht.length_le.trans (hp z))

/-- Canonical digits of an arbitrarily large binary name are computed in FP. -/
theorem nameBitsValue_bits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => (nameBitsValue (bits z)).bits) ∈ FP :=
  mem_FP_of_eq (normalizeNameBits_mem_FP hbits) fun z => normalizeNameBits_eq_bits (bits z)

/-- Equality of two FP bit strings, including strings of different lengths. -/
theorem bitStrings_eq_fppred {left right : List Bool → List Bool}
    (hleft : left ∈ FP) (hright : right ∈ FP) : FPPred fun z => left z = right z := by
  let lbit := fun w => (left (pairFst w))[(pairSnd w).length]?.getD false
  let rbit := fun w => (right (pairFst w))[(pairSnd w).length]?.getD false
  have hl : FPPred fun w => lbit w = true :=
    FPPred.getBit (mem_FP_comp pairFst_mem_FP hleft) UnaryFn.index
  have hr : FPPred fun w => rbit w = true :=
    FPPred.getBit (mem_FP_comp pairFst_mem_FP hright) UnaryFn.index
  have heq : FPPred fun w => lbit w = rbit w :=
    ((hl.and hr).or (hl.not.and hr.not)).of_iff fun w => by
      cases lbit w <;> cases rbit w <;> simp
  have hall := FPPred.forall_lt (UnaryFn.length hleft) heq
  apply ((FPPred.eq (UnaryFn.length hleft) (UnaryFn.length hright)).and hall).of_iff
  intro z
  simp only [lbit, rbit, pairFst_pair, pairSnd_pair, List.length_replicate]
  constructor
  · rintro ⟨hlen, hbits⟩
    apply List.ext_getElem hlen
    intro i hi hj
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
      using hbits i hi
  · intro h
    simp [h]

/-- Numeric equality of binary names is polynomial-time even when their values
are exponentially larger than their encodings. -/
theorem nameBitsValue_eq_fppred {left right : List Bool → List Bool}
    (hleft : left ∈ FP) (hright : right ∈ FP) :
    FPPred fun z => nameBitsValue (left z) = nameBitsValue (right z) :=
  (bitStrings_eq_fppred (nameBitsValue_bits_mem_FP hleft)
    (nameBitsValue_bits_mem_FP hright)).of_iff fun z => by
      constructor
      · intro h
        have := congrArg nameBitsValue h
        simpa only [nameBitsValue_bits] using this
      · exact congrArg Nat.bits

/-- The existing name parser's canonical-digit test has an FP certificate. -/
theorem canonicalNameBits_fppred {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    FPPred fun z => (nameBitsValue (bits z)).bits = bits z :=
  bitStrings_eq_fppred (nameBitsValue_bits_mem_FP hbits) hbits

/-- Re-encode an arbitrary binary name with the exact existing framing. -/
theorem encodeNatName_binary_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => encodeNatName (nameBitsValue (bits z))) ∈ FP :=
  frameNameBits_mem_FP (nameBitsValue_bits_mem_FP hbits)

/-- Constructors can preserve arbitrary binary names without a unary bound. -/
theorem encodeQBF_var_binary_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => encodeQBF (.var (nameBitsValue (bits z)))) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP _) (encodeNatName_binary_mem_FP hbits)

theorem encodeQBF_ex_binary_mem_FP {bits : List Bool → List Bool} {body : List Bool → QBF}
    (hbits : bits ∈ FP) (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (.ex (nameBitsValue (bits z)) (body z))) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP _) (encodeNatName_binary_mem_FP hbits)) hbody

theorem encodeQBF_all_binary_mem_FP {bits : List Bool → List Bool} {body : List Bool → QBF}
    (hbits : bits ∈ FP) (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (.all (nameBitsValue (bits z)) (body z))) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP _) (encodeNatName_binary_mem_FP hbits)) hbody

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Encoding
import IPPSPACE.QBF.BooleanGadgets
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Iterate

/-!
# Machine-based polynomial-time certificates for QBF construction

These certificates use the actual upstream `FP` class and its proved machine
closure rules. They cover the canonical binary name framing, syntax
constructors, and conjunction/disjunction builders over polynomial-time ranges.
They do not certify arbitrary syntax recursion, parsing, or prenex conversion.
-/

namespace IPPSPACE

open Complexity

/-- The canonical continuation-bit name framing is an actual FP computation. -/
theorem frameNameBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => frameNameBits (bits z)) ∈ FP := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hbits
  let state : List Bool → List Bool := fun z => pairSnd (pairFst z)
  have hstate : state ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hstep (b : Bool) : (fun z => true :: b :: state z) ∈ FP :=
    mem_FP_comp (mem_FP_comp hstate (Cobham.cons_mem_FP b)) (Cobham.cons_mem_FP true)
  apply recFold_mem_FP_of_bound (g := fun _ t => frameNameBits t)
    (w := fun _ => []) (E := fun _ => [false]) (hstep false) (hstep true)
    (constFn_mem_FP _) (constFn_mem_FP _) hbits
  · intro z
    rfl
  · intro z t
    simp [frameNameBits, state]
  · intro z t
    simp [frameNameBits, state]
  · exact ((PolyBound.const 2).mul (PolyBound.eval p)).add (PolyBound.const 1)
  · intro z t ht
    rw [length_frameNameBits]
    have := ht.length_le
    have := hp z
    change _ ≤ 2 * p.eval z.length + 1
    omega

/-- Write a canonical binary variable name from a polynomial-time numeric value. -/
theorem encodeNatName_mem_FP {name : List Bool → ℕ} (hname : UnaryFn name) :
    (fun z => encodeNatName (name z)) ∈ FP :=
  frameNameBits_mem_FP (bits_mem_FP hname)

theorem encodeQBF_var_mem_FP {name : List Bool → ℕ} (hname : UnaryFn name) :
    (fun z => encodeQBF (.var (name z))) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP _) (encodeNatName_mem_FP hname)

theorem encodeQBF_tru_mem_FP : (fun _ : List Bool => encodeQBF .tru) ∈ FP :=
  constFn_mem_FP _

theorem encodeQBF_fls_mem_FP : (fun _ : List Bool => encodeQBF .fls) ∈ FP :=
  constFn_mem_FP _

theorem encodeQBF_neg_mem_FP {body : List Bool → QBF}
    (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (.neg (body z))) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP _) hbody

theorem encodeQBF_conj_mem_FP {left right : List Bool → QBF}
    (hleft : (fun z => encodeQBF (left z)) ∈ FP)
    (hright : (fun z => encodeQBF (right z)) ∈ FP) :
    (fun z => encodeQBF (.conj (left z) (right z))) ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP (constFn_mem_FP _) hleft) hright

theorem encodeQBF_disj_mem_FP {left right : List Bool → QBF}
    (hleft : (fun z => encodeQBF (left z)) ∈ FP)
    (hright : (fun z => encodeQBF (right z)) ∈ FP) :
    (fun z => encodeQBF (.disj (left z) (right z))) ∈ FP :=
  Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP (constFn_mem_FP _) hleft) hright

theorem encodeQBF_ex_mem_FP {name : List Bool → ℕ} {body : List Bool → QBF}
    (hname : UnaryFn name) (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (.ex (name z) (body z))) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP _) (encodeNatName_mem_FP hname)) hbody

theorem encodeQBF_all_mem_FP {name : List Bool → ℕ} {body : List Bool → QBF}
    (hname : UnaryFn name) (hbody : (fun z => encodeQBF (body z)) ∈ FP) :
    (fun z => encodeQBF (.all (name z) (body z))) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP _) (encodeNatName_mem_FP hname)) hbody

theorem encodeQBF_bitValue_mem_FP {name : List Bool → ℕ} {value : List Bool → Bool}
    (hname : UnaryFn name) (hvalue : FPPred fun z => value z = true) :
    (fun z => encodeQBF (bitValue (name z) (value z))) ∈ FP := by
  have h := hvalue.ite_mem_FP (encodeQBF_var_mem_FP hname)
    (encodeQBF_neg_mem_FP (encodeQBF_var_mem_FP hname))
  apply mem_FP_of_eq h
  intro z
  cases value z <;> simp [bitValue]

theorem encodeQBF_bitEquality_mem_FP {left right : List Bool → ℕ}
    (hleft : UnaryFn left) (hright : UnaryFn right) :
    (fun z => encodeQBF (bitEquality (left z) (right z))) ∈ FP :=
  encodeQBF_disj_mem_FP
    (encodeQBF_conj_mem_FP (encodeQBF_var_mem_FP hleft) (encodeQBF_var_mem_FP hright))
    (encodeQBF_conj_mem_FP (encodeQBF_neg_mem_FP (encodeQBF_var_mem_FP hleft))
      (encodeQBF_neg_mem_FP (encodeQBF_var_mem_FP hright)))

/-- Conjunction encoding is a single flat concatenation of tagged entries. -/
theorem encodeQBF_qbfAll (formulas : List QBF) :
    encodeQBF (qbfAll formulas) =
      formulas.flatMap (fun formula => [true, false, false] ++ encodeQBF formula) ++ encodeQBF .tru := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih => simp [qbfAll, encodeQBF, ih, List.append_assoc]

theorem encodeQBF_qbfAny (formulas : List QBF) :
    encodeQBF (qbfAny formulas) =
      formulas.flatMap (fun formula => [true, false, true] ++ encodeQBF formula) ++ encodeQBF .fls := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih => simp [qbfAny, encodeQBF, ih, List.append_assoc]

/-- Generate a conjunction over an input-dependent polynomial-time range. Each
body computation receives the original input paired with a unary index. -/
theorem encodeQBF_qbfAll_range_mem_FP {count : List Bool → ℕ}
    {body : List Bool → ℕ → QBF} (hcount : UnaryFn count)
    (hbody : (fun w => encodeQBF (body (pairFst w) (pairSnd w).length)) ∈ FP) :
    (fun z => encodeQBF (qbfAll ((List.range (count z)).map (body z)))) ∈ FP := by
  have hentry := Cobham.appendFn_mem_FP (constFn_mem_FP [true, false, false]) hbody
  have h := Cobham.appendFn_mem_FP (flatMap_range_mem_FP hentry hcount.mem_FP)
    (constFn_mem_FP (encodeQBF .tru))
  apply mem_FP_of_eq h
  intro z
  simp [encodeQBF_qbfAll, List.flatMap_map]

theorem encodeQBF_qbfAny_range_mem_FP {count : List Bool → ℕ}
    {body : List Bool → ℕ → QBF} (hcount : UnaryFn count)
    (hbody : (fun w => encodeQBF (body (pairFst w) (pairSnd w).length)) ∈ FP) :
    (fun z => encodeQBF (qbfAny ((List.range (count z)).map (body z)))) ∈ FP := by
  have hentry := Cobham.appendFn_mem_FP (constFn_mem_FP [true, false, true]) hbody
  have h := Cobham.appendFn_mem_FP (flatMap_range_mem_FP hentry hcount.mem_FP)
    (constFn_mem_FP (encodeQBF .fls))
  apply mem_FP_of_eq h
  intro z
  simp [encodeQBF_qbfAny, List.flatMap_map]

end IPPSPACE

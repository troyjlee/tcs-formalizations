/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.BlocksFP
import IPPSPACE.QBF.AcceptingReachability

/-!
# Polynomial-time construction of succinct reachability formulas

The exact recursive reachability encoding is a flat concatenation of one prefix
per squaring level followed by one copy of the base-edge encoding. Upstream's
actual range-loop certificate makes this construction polynomial-time. The
base-edge constructor remains an explicit compositional premise; these results
do not certify arbitrary template renaming, closure, or prenex conversion.
-/

namespace IPPSPACE

open Complexity

/-- Binary prefix for a contiguous quantifier block. -/
def reachQuantifierPrefix (universal : Bool) (start width : ℕ) : List Bool :=
  (List.range width).flatMap (fun i => [true, true, universal] ++ encodeNatName (start + i))

/-- One level contributes three quantifier blocks and the selected-pair premise.
The recursive conclusion is the sole missing tail. -/
def reachLevelPrefix (width fresh left right : ℕ) : List Bool :=
  reachQuantifierPrefix false fresh width ++
  reachQuantifierPrefix true (fresh + width) width ++
  reachQuantifierPrefix true (fresh + 2 * width) width ++
  [true, false, true] ++ [false, true, true] ++
  encodeQBF (selectedPair (blockNames left width) (blockNames fresh width)
    (blockNames right width) (blockNames (fresh + width) width)
    (blockNames (fresh + 2 * width) width))

/-- Start of an endpoint block after the given number of recursive levels.
The offsets 1 and 2 select the universally quantified left and right blocks. -/
def reachEndpointStart (width fresh start offset : ℕ) : ℕ → ℕ
  | 0 => start
  | level + 1 => fresh + 3 * width * level + offset * width

@[simp] theorem reachEndpointStart_zero (width fresh start offset : ℕ) :
    reachEndpointStart width fresh start offset 0 = start := rfl

@[simp] theorem reachEndpointStart_shift (width fresh start offset level : ℕ) :
    reachEndpointStart width (fresh + 3 * width) (fresh + offset * width) offset level =
      reachEndpointStart width fresh start offset (level + 1) := by
  cases level <;> simp [reachEndpointStart]
  ring

/-- Exact one-level encoding, with no duplicated recursive subformula. -/
theorem encodeQBF_reachFormula_succ (width : ℕ)
    (edge : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (depth fresh left right : ℕ) :
    encodeQBF (reachFormula width edge (depth + 1) fresh
      (blockNames left width) (blockNames right width)) =
      reachLevelPrefix width fresh left right ++
        encodeQBF (reachFormula width edge depth (fresh + 3 * width)
          (blockNames (fresh + width) width) (blockNames (fresh + 2 * width) width)) := by
  simp [reachFormula, encodeQBF_existsBlock, encodeQBF_forallBlock,
    reachLevelPrefix, reachQuantifierPrefix, encodeQBF, List.append_assoc]

/-- Flattening the actual recursive syntax exposes polynomially many independent
prefix computations and exactly one final base-edge computation. -/
theorem encodeQBF_reachFormula_flat (width : ℕ)
    (edge : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (depth fresh left right : ℕ) :
    encodeQBF (reachFormula width edge depth fresh
      (blockNames left width) (blockNames right width)) =
      (List.range depth).flatMap (fun level => reachLevelPrefix width
        (fresh + 3 * width * level)
        (reachEndpointStart width fresh left 1 level)
        (reachEndpointStart width fresh right 2 level)) ++
      encodeQBF (edge
        (blockNames (reachEndpointStart width fresh left 1 depth) width)
        (blockNames (reachEndpointStart width fresh right 2 depth) width)) := by
  induction depth generalizing fresh left right with
  | zero => simp [reachFormula, reachEndpointStart]
  | succ depth ih =>
    have hleft (level : ℕ) :
        reachEndpointStart width (fresh + 3 * width) (fresh + width) 1 level =
          reachEndpointStart width fresh left 1 (level + 1) := by
      simpa using reachEndpointStart_shift width fresh left 1 level
    have hright (level : ℕ) :
        reachEndpointStart width (fresh + 3 * width) (fresh + 2 * width) 2 level =
          reachEndpointStart width fresh right 2 (level + 1) :=
      reachEndpointStart_shift width fresh right 2 level
    rw [encodeQBF_reachFormula_succ, ih, hleft, hright]
    simp only [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      Nat.mul_zero, Nat.add_zero, reachEndpointStart_zero, List.append_assoc]
    congr 2
    apply congrArg (fun f : ℕ → List Bool => (List.range depth).flatMap f)
    funext level
    rw [hleft, hright]
    congr 1
    simp only [Nat.succ_eq_add_one]
    ring

/-- Quantifier prefixes are produced with the upstream finite-range machine. -/
theorem reachQuantifierPrefix_mem_FP (universal : Bool)
    {start width : List Bool → ℕ} (hs : UnaryFn start) (hw : UnaryFn width) :
    (fun z => reachQuantifierPrefix universal (start z) (width z)) ∈ FP := by
  have hentry := Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, universal])
    (encodeNatName_mem_FP (hs.lift.add UnaryFn.index))
  apply mem_FP_of_eq (flatMap_range_mem_FP hentry hw.mem_FP)
  intro z
  simp [reachQuantifierPrefix]

/-- The actual pair-selection gadget on five contiguous blocks is constructible. -/
theorem encode_selectedPair_contiguous_mem_FP
    {width left middle right u v : List Bool → ℕ}
    (hw : UnaryFn width) (hl : UnaryFn left) (hm : UnaryFn middle)
    (hr : UnaryFn right) (hu : UnaryFn u) (hv : UnaryFn v) :
    (fun z => encodeQBF (selectedPair (blockNames (left z) (width z))
      (blockNames (middle z) (width z)) (blockNames (right z) (width z))
      (blockNames (u z) (width z)) (blockNames (v z) (width z)))) ∈ FP :=
  encodeQBF_disj_mem_FP
    (encodeQBF_conj_mem_FP (encodeQBF_blockEquality_contiguous_mem_FP hu hl hw)
      (encodeQBF_blockEquality_contiguous_mem_FP hv hm hw))
    (encodeQBF_conj_mem_FP (encodeQBF_blockEquality_contiguous_mem_FP hu hm hw)
      (encodeQBF_blockEquality_contiguous_mem_FP hv hr hw))

theorem reachLevelPrefix_mem_FP {width fresh left right : List Bool → ℕ}
    (hw : UnaryFn width) (hf : UnaryFn fresh) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun z => reachLevelPrefix (width z) (fresh z) (left z) (right z)) ∈ FP := by
  have hu := hf.add hw
  have hv := hf.add ((UnaryFn.const 2).mul hw)
  exact Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP
        (Cobham.appendFn_mem_FP
          (Cobham.appendFn_mem_FP (reachQuantifierPrefix_mem_FP false hf hw)
            (reachQuantifierPrefix_mem_FP true hu hw))
          (reachQuantifierPrefix_mem_FP true hv hw))
        (constFn_mem_FP [true, false, true]))
      (constFn_mem_FP [false, true, true]))
    (encode_selectedPair_contiguous_mem_FP hw hl hf hr hu hv)

theorem reachEndpointStart_unaryFn (offset : ℕ)
    {width fresh start level : List Bool → ℕ}
    (hw : UnaryFn width) (hf : UnaryFn fresh) (hs : UnaryFn start) (hi : UnaryFn level) :
    UnaryFn fun z => reachEndpointStart (width z) (fresh z) (start z) offset (level z) := by
  have h := UnaryFn.ite (FPPred.eq hi (UnaryFn.const 0)) hs
    ((hf.add (((UnaryFn.const 3).mul hw).mul (hi.sub (UnaryFn.const 1)))).add
      ((UnaryFn.const offset).mul hw))
  refine h.of_eq (fun z => ?_)
  cases level z <;> simp [reachEndpointStart]

/-- Genuine `FP` construction of the exact recursive reachability formula.
The sole constructor premise is the base edge at its final endpoint blocks. -/
theorem encode_reachFormula_mem_FP {width depth fresh left right : List Bool → ℕ}
    (edge : (z : List Bool) → (Fin (width z) → ℕ) → (Fin (width z) → ℕ) → QBF)
    (hw : UnaryFn width) (hd : UnaryFn depth) (hf : UnaryFn fresh)
    (hl : UnaryFn left) (hr : UnaryFn right)
    (hbase : (fun z => encodeQBF (edge z
      (blockNames (reachEndpointStart (width z) (fresh z) (left z) 1 (depth z)) (width z))
      (blockNames (reachEndpointStart (width z) (fresh z) (right z) 2 (depth z)) (width z)))) ∈ FP) :
    (fun z => encodeQBF (reachFormula (width z) (edge z) (depth z) (fresh z)
      (blockNames (left z) (width z)) (blockNames (right z) (width z)))) ∈ FP := by
  have hlevel := reachLevelPrefix_mem_FP hw.lift
    (hf.lift.add (((UnaryFn.const 3).mul hw.lift).mul UnaryFn.index))
    (reachEndpointStart_unaryFn 1 hw.lift hf.lift hl.lift UnaryFn.index)
    (reachEndpointStart_unaryFn 2 hw.lift hf.lift hr.lift UnaryFn.index)
  have h := Cobham.appendFn_mem_FP (flatMap_range_mem_FP hlevel hd.mem_FP) hbase
  apply mem_FP_of_eq h
  intro z
  simp only [List.length_replicate, pairFst_pair, pairSnd_pair, ← encodeQBF_reachFormula_flat]

/-- A uniform base constructor receives the original input paired with the two
endpoint starts in unary. This conventional interface implies the tail premise
of `encode_reachFormula_mem_FP`. -/
theorem encode_reachFormula_of_builder_mem_FP {width depth fresh left right : List Bool → ℕ}
    (edge : (z : List Bool) → (Fin (width z) → ℕ) → (Fin (width z) → ℕ) → QBF)
    (hw : UnaryFn width) (hd : UnaryFn depth) (hf : UnaryFn fresh)
    (hl : UnaryFn left) (hr : UnaryFn right)
    (hbuilder : (fun v => encodeQBF (edge (pairFst v)
      (blockNames (pairFst (pairSnd v)).length (width (pairFst v)))
      (blockNames (pairSnd (pairSnd v)).length (width (pairFst v))))) ∈ FP) :
    (fun z => encodeQBF (reachFormula (width z) (edge z) (depth z) (fresh z)
      (blockNames (left z) (width z)) (blockNames (right z) (width z)))) ∈ FP := by
  have hleft := reachEndpointStart_unaryFn 1 hw hf hl hd
  have hright := reachEndpointStart_unaryFn 2 hw hf hr hd
  have hid : (fun z : List Bool => z) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (mem_FP_pairWithInput (constFn_mem_FP [])) pairSnd_mem_FP)
      (fun z => by simp)
  have hargs := Cobham.pairFn_mem_FP hid (Cobham.pairFn_mem_FP hleft.mem_FP hright.mem_FP)
  apply encode_reachFormula_mem_FP edge hw hd hf hl hr
  apply mem_FP_of_eq (mem_FP_comp hargs hbuilder)
  intro z
  simp
  rw [pairFst_pair]

/-- Adding equality as the stuttering branch preserves the same actual runtime
certificate, including the single occurrence of the original edge formula. -/
theorem encode_reachFormula_stutter_mem_FP {width depth fresh left right : List Bool → ℕ}
    (edge : (z : List Bool) → (Fin (width z) → ℕ) → (Fin (width z) → ℕ) → QBF)
    (hw : UnaryFn width) (hd : UnaryFn depth) (hf : UnaryFn fresh)
    (hl : UnaryFn left) (hr : UnaryFn right)
    (hbase : (fun z => encodeQBF (edge z
      (blockNames (reachEndpointStart (width z) (fresh z) (left z) 1 (depth z)) (width z))
      (blockNames (reachEndpointStart (width z) (fresh z) (right z) 2 (depth z)) (width z)))) ∈ FP) :
    (fun z => encodeQBF (reachFormula (width z) (stutterFormula (width z) (edge z))
      (depth z) (fresh z) (blockNames (left z) (width z))
      (blockNames (right z) (width z)))) ∈ FP :=
  encode_reachFormula_mem_FP (fun z => stutterFormula (width z) (edge z)) hw hd hf hl hr
    (encodeQBF_disj_mem_FP (encodeQBF_blockEquality_contiguous_mem_FP
      (reachEndpointStart_unaryFn 1 hw hf hl hd)
      (reachEndpointStart_unaryFn 2 hw hf hr hd) hw) hbase)

@[simp] theorem reachEndpointStart_accepting_left (width : ℕ) :
    reachEndpointStart width (2 * width) 0 1 width = 3 * width ^ 2 := by
  cases width with
  | zero => rfl
  | succ width => dsimp [reachEndpointStart]; ring

@[simp] theorem reachEndpointStart_accepting_right (width : ℕ) :
    reachEndpointStart width (2 * width) width 2 width = 3 * width ^ 2 + width := by
  cases width with
  | zero => rfl
  | succ width => dsimp [reachEndpointStart]; ring

/-- Actual `FP` construction of the exact accepting-reachability formula from
its three local ingredients: the source block, acceptance test, and final edge.
No reachability or complexity-class conclusion is assumed in these premises. -/
theorem encode_acceptingReachFormula_mem_FP {width : List Bool → ℕ}
    (edge : (z : List Bool) → (Fin (width z) → ℕ) → (Fin (width z) → ℕ) → QBF)
    (accept : (z : List Bool) → (Fin (width z) → ℕ) → QBF)
    (source : (z : List Bool) → Fin (width z) → Bool)
    (hw : UnaryFn width)
    (hsource : (fun z => encodeQBF (blockValues (blockNames 0 (width z)) (source z))) ∈ FP)
    (haccept : (fun z => encodeQBF (accept z (blockNames (width z) (width z)))) ∈ FP)
    (hedge : (fun z => encodeQBF (edge z
      (blockNames (3 * width z ^ 2) (width z))
      (blockNames (3 * width z ^ 2 + width z) (width z)))) ∈ FP) :
    (fun z => encodeQBF (acceptingReachFormula (width z) (edge z) (accept z) (source z))) ∈ FP := by
  have hreach := encode_reachFormula_stutter_mem_FP edge hw hw
    ((UnaryFn.const 2).mul hw) (UnaryFn.const 0) hw (by simpa using hedge)
  exact encodeQBF_existsBlock_mem_FP (UnaryFn.const 0) hw
    (encodeQBF_existsBlock_mem_FP hw hw
      (encodeQBF_conj_mem_FP hsource (encodeQBF_conj_mem_FP haccept hreach)))

/-- The fixed-target construction has the same runtime certificate with a
second encoded value block in place of the acceptance test. -/
theorem encode_fixedEndpointReachFormula_mem_FP {width : List Bool → ℕ}
    (edge : (z : List Bool) → (Fin (width z) → ℕ) → (Fin (width z) → ℕ) → QBF)
    (source target : (z : List Bool) → Fin (width z) → Bool)
    (hw : UnaryFn width)
    (hsource : (fun z => encodeQBF (blockValues (blockNames 0 (width z)) (source z))) ∈ FP)
    (htarget : (fun z => encodeQBF (blockValues (blockNames (width z) (width z)) (target z))) ∈ FP)
    (hedge : (fun z => encodeQBF (edge z
      (blockNames (3 * width z ^ 2) (width z))
      (blockNames (3 * width z ^ 2 + width z) (width z)))) ∈ FP) :
    (fun z => encodeQBF (fixedEndpointReachFormula (width z) (edge z) (source z) (target z))) ∈ FP := by
  have h := encode_acceptingReachFormula_mem_FP edge
    (fun z names => blockValues names (target z)) source hw hsource htarget hedge
  exact h

end IPPSPACE

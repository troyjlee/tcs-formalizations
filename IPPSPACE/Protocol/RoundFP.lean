/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.HornerFP
import IPPSPACE.Protocol.FiniteVerifier
import IPPSPACE.QBF.BinaryNamesFP

/-!
# Polynomial-time encoded round checks

The total bit-string procedures compose bounded message parsing, Horner
execution at zero and one, and checked modular operations. The operator kind
has a constant-size numeric tag; its coordinate is represented separately by
the current assignment value. Exact refinement connects the result to the
existing finite verifier. Assignment lookup and transcript replay remain
separate obligations.
-/

namespace IPPSPACE

open Complexity

/-- Only the arithmetic kind is needed once the current coordinate is looked up. -/
def AlgebraicOperator.roundKind : AlgebraicOperator → ℕ
  | .reduce _ => 0
  | .quantify (.ex _) => 1
  | .quantify (.all _) => 2

/-- Modular zero and one, also defined at modulus zero. -/
def roundConstantBits (p value : ℕ) : List Bool := wordBits (reduceResidueWord p value)

@[simp] theorem roundConstantBits_eq {p : ℕ} [NeZero p] (value : ℕ) :
    roundConstantBits p value = wordBits (encodeResidue (value : ZMod p)) := by
  rw [roundConstantBits, reduceResidueWord_eq_encodeResidue]

private theorem addBits_encode {p : ℕ} [NeZero p] (a b : ZMod p) :
    checkedResidueBitsBinary p (· + ·) (wordBits (encodeResidue a))
      (wordBits (encodeResidue b)) = wordBits (encodeResidue (a + b)) := by
  simpa only [wordAdd, wordResultBits, Option.map_some, Option.getD_some] using
    (checkedResidueBitsBinary_wordBits p (· + ·) (encodeResidue a) (encodeResidue b)).trans
      (by rw [← wordAdd, wordAdd_encodeResidue]; rfl)

private theorem mulBits_encode {p : ℕ} [NeZero p] (a b : ZMod p) :
    checkedResidueBitsBinary p (· * ·) (wordBits (encodeResidue a))
      (wordBits (encodeResidue b)) = wordBits (encodeResidue (a * b)) := by
  rw [checkedResidueBitsBinary_wordBits, ← wordMul, wordMul_encodeResidue]
  rfl

private theorem subBits_encode {p : ℕ} [NeZero p] (a b : ZMod p) :
    checkedResidueBitsBinary p (fun x y => x + p - y) (wordBits (encodeResidue a))
      (wordBits (encodeResidue b)) = wordBits (encodeResidue (a - b)) := by
  rw [checkedResidueBitsBinary_wordBits, ← wordSub, wordSub_encodeResidue]
  rfl

/-- Three endpoint identities, using only validated modular string operations.
Unrecognized operator tags return the empty failure string. -/
def combineRoundBits (p kind : ℕ) (point a b : List Bool) : List Bool :=
  let one := roundConstantBits p 1
  let add := checkedResidueBitsBinary p (· + ·)
  let mul := checkedResidueBitsBinary p (· * ·)
  let sub := checkedResidueBitsBinary p (fun x y => x + p - y)
  if kind = 0 then add (mul (sub one point) a) (mul point b)
  else if kind = 1 then sub one (mul (sub one a) (sub one b))
  else if kind = 2 then mul a b
  else []

theorem combineRoundBits_encode {p : ℕ} [NeZero p] (op : AlgebraicOperator)
    (point : ℕ → ZMod p) (a b : ZMod p) :
    combineRoundBits p op.roundKind (wordBits (encodeResidue (point op.coordinate)))
      (wordBits (encodeResidue a)) (wordBits (encodeResidue b)) =
      wordBits (encodeResidue (op.combine point a b)) := by
  cases op with
  | reduce i =>
    dsimp [combineRoundBits, AlgebraicOperator.roundKind, AlgebraicOperator.coordinate,
      AlgebraicOperator.combine]
    simp only [roundConstantBits_eq, Nat.cast_one, subBits_encode, mulBits_encode, addBits_encode]
  | quantify q => cases q <;>
      dsimp [combineRoundBits, AlgebraicOperator.roundKind, AlgebraicOperator.combine] <;>
      simp only [roundConstantBits_eq, Nat.cast_one, subBits_encode, mulBits_encode]

theorem combineRoundBits_mem_FP {p kind : List Bool → ℕ} {point a b : List Bool → List Bool}
    (hp : UnaryFn p) (hk : UnaryFn kind) (hx : point ∈ FP) (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => combineRoundBits (p z) (kind z) (point z) (a z) (b z)) ∈ FP := by
  have hone := reduceResidueWord_bits_mem_FP hp (UnaryFn.const 1)
  exact (FPPred.eq hk (UnaryFn.const 0)).ite_mem_FP
    (residueBitsAdd_mem_FP hp
      (residueBitsMul_mem_FP hp (residueBitsSub_mem_FP hp hone hx) ha)
      (residueBitsMul_mem_FP hp hx hb))
    ((FPPred.eq hk (UnaryFn.const 1)).ite_mem_FP
      (residueBitsSub_mem_FP hp hone
        (residueBitsMul_mem_FP hp (residueBitsSub_mem_FP hp hone ha)
          (residueBitsSub_mem_FP hp hone hb)))
      ((FPPred.eq hk (UnaryFn.const 2)).ite_mem_FP
        (residueBitsMul_mem_FP hp ha hb) (constFn_mem_FP [])))

/-- A complete endpoint/degree-list check on raw strings. Malformed state words
and coefficient messages are rejected before comparison. -/
def checkRoundBits (p kind degree : ℕ) (point claim message : List Bool) : Bool :=
  if CanonicalResidueBits p point ∧ CanonicalResidueBits p claim ∧
      validateMessageBits p (degree + 1) message = true then
    decide (combineRoundBits p kind point
      (evaluateMessageBits p (degree + 1) (roundConstantBits p 0) message)
      (evaluateMessageBits p (degree + 1) (roundConstantBits p 1) message) = claim)
  else false

theorem checkRoundBits_mem_FP {p kind degree : List Bool → ℕ}
    {point claim message : List Bool → List Bool}
    (hp : UnaryFn p) (hk : UnaryFn kind) (hd : UnaryFn degree)
    (hx : point ∈ FP) (hc : claim ∈ FP) (hm : message ∈ FP) :
    (fun z => [checkRoundBits (p z) (kind z) (degree z) (point z) (claim z) (message z)]) ∈ FP := by
  have hlimit := hd.add (UnaryFn.const 1)
  have heval (v : ℕ) := evaluateMessageBits_mem_FP hp hlimit
    (reduceResidueWord_bits_mem_FP hp (UnaryFn.const v)) hm
  have hcombine := combineRoundBits_mem_FP hp hk hx (heval 0) (heval 1)
  have hvalid := (canonicalResidueBits_fppred hp hx).and
    ((canonicalResidueBits_fppred hp hc).and
      ((messageBitsValid_fppred hp hlimit hm).of_iff fun _ =>
        (validateMessageBits_eq_true _ _ _).symm))
  have heq := bitStrings_eq_fppred hcombine hc
  apply mem_FP_of_eq (hvalid.ite_mem_FP heq.flag_mem_FP (constFn_mem_FP [false]))
  intro z
  unfold checkRoundBits
  split <;> rfl

private theorem residueBits_injective {p : ℕ} [NeZero p] :
    Function.Injective (fun a : ZMod p => wordBits (encodeResidue a)) := by
  intro a b h
  have hval := congrArg Nat.fromBits h
  simp only [fromBits_wordBits, encodeResidue_toNat] at hval
  exact ZMod.val_injective p hval

/-- On canonical state words, the raw checker refines the exact existing parser
and finite-verifier check, for all messages including malformed ones. -/
theorem checkRoundBits_eq {p : ℕ} [NeZero p] (op : AlgebraicOperator) (degree : ℕ)
    (c : FiniteClaim (ZMod p)) (message : List Bool) :
    checkRoundBits p op.roundKind degree (wordBits (encodeResidue (c.point op.coordinate)))
      (wordBits (encodeResidue c.value)) message =
      match parseMessage p (degree + 1) message with
      | none => false
      | some as => (checkRoundWithCost op degree c as).1 := by
  cases hparse : parseMessage p (degree + 1) message with
  | none =>
    have hv : validateMessageBits p (degree + 1) message = false := by
      rw [validateMessageBits_eq_parseMessage_isSome, hparse]
      rfl
    simp [checkRoundBits, hv]
  | some as =>
    obtain ⟨hmessage, hlen⟩ := parseMessage_sound (degree + 1) message as hparse
    have hv : validateMessageBits p (degree + 1) message = true := by
      rw [validateMessageBits_eq_parseMessage_isSome, hparse]
      rfl
    simp only [checkRoundBits, canonicalResidueBits_wordBits, encodeResidue_toNat,
      ZMod.val_lt, hv, and_self, ite_true]
    rw [← hmessage]
    simp only [roundConstantBits_eq, Nat.cast_zero, Nat.cast_one,
      evaluateMessageBits_encodeMessage _ _ _ hlen, combineRoundBits_encode]
    simp only [residueBits_injective.eq_iff]
    simp [checkRoundWithCost, lengthCheckWithCost_value, hlen]

/-- Canonically encoded coefficient lists refine the existing finite round
check exactly, including oversized lists rejected by both implementations. -/
@[simp] theorem checkRoundBits_encodeMessage {p : ℕ} [NeZero p]
    (op : AlgebraicOperator) (degree : ℕ) (c : FiniteClaim (ZMod p))
    (as : List (ZMod p)) :
    checkRoundBits p op.roundKind degree (wordBits (encodeResidue (c.point op.coordinate)))
      (wordBits (encodeResidue c.value)) (encodeMessage as) =
      (checkRoundWithCost op degree c as).1 := by
  rw [checkRoundBits_eq]
  by_cases hlen : as.length ≤ degree + 1
  · rw [parseMessage_encode _ _ hlen]
  · have hw : 0 < residueWidth p := by simp [residueWidth]
    have hover : (degree + 1) * residueWidth p < (encodeMessage as).length := by
      rw [length_encodeMessage]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hlen) hw
    rw [parseMessage_reject_overlong _ _ hover]
    simp [checkRoundWithCost, lengthCheckWithCost_value, hlen]

/-- State-word rejection is unconditional, including modulus zero. -/
theorem checkRoundBits_invalid (p kind degree : ℕ) (point claim message : List Bool)
    (h : ¬ (CanonicalResidueBits p point ∧ CanonicalResidueBits p claim ∧
      validateMessageBits p (degree + 1) message = true)) :
    checkRoundBits p kind degree point claim message = false := by
  simp only [checkRoundBits, ite_eq_right h]

end IPPSPACE

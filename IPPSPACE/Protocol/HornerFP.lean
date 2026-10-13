/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MessageOutputFP

/-!
# Machine-based polynomial-time Horner evaluation

A unary loop state packs a coefficient index and a reduced accumulator. Capped
binary decoding makes each transition polynomial-time even on malformed inputs;
the accumulator bound gives a polynomial bound on every intermediate state.
The total raw evaluator agrees exactly with the existing bounded parser followed
by field-list evaluation. The checked word-level and polynomial specifications
inherit genuine upstream `FP` certificates through the proved refinement.
-/

namespace IPPSPACE

open Complexity

/-- Number of complete coefficient-width blocks in a raw message. -/
def hornerBlockCount (p : ℕ) (bits : List Bool) : ℕ :=
  bits.length / residueWidth p

/-- Read coefficients from highest to lowest degree. The cap is immaterial on
canonical words and prevents arbitrary malformed bytes from producing huge unary values. -/
def hornerCoefficient (p : ℕ) (bits : List Bool) (index : ℕ) : ℕ :=
  min (Nat.fromBits (messageWordBits p (hornerBlockCount p bits - (index + 1)) bits)) p

/-- One reduced Horner update, total also when the modulus is zero. -/
def hornerUpdate (p x coefficient accumulator : ℕ) : ℕ :=
  min ((coefficient + x * accumulator) % p) p

/-- The numeric accumulator after the given number of reverse-order blocks. -/
def hornerAccumulator (p x : ℕ) (bits : List Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => hornerUpdate p x (hornerCoefficient p bits n)
      (hornerAccumulator p x bits n)

/-- Pack the index and accumulator in base `p+1`. -/
def hornerLoopStep (p x : ℕ) (bits : List Bool) (state : ℕ) : ℕ :=
  (state / (p + 1) + 1) * (p + 1) +
    hornerUpdate p x (hornerCoefficient p bits (state / (p + 1))) (state % (p + 1))

theorem hornerAccumulator_le (p x : ℕ) (bits : List Bool) (n : ℕ) :
    hornerAccumulator p x bits n ≤ p := by
  cases n with
  | zero => simp [hornerAccumulator]
  | succ n => exact min_le_right _ _

theorem hornerLoopStep_iterate (p x : ℕ) (bits : List Bool) (n : ℕ) :
    (hornerLoopStep p x bits)^[n] 0 =
      n * (p + 1) + hornerAccumulator p x bits n := by
  induction n with
  | zero => simp [hornerAccumulator]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have ha : hornerAccumulator p x bits n < p + 1 := by
      have := hornerAccumulator_le p x bits n
      omega
    simp [hornerLoopStep, Nat.add_div, Nat.div_eq_of_lt ha,
      Nat.add_mod, Nat.mod_eq_of_lt ha, hornerAccumulator,
      show ¬ p < hornerAccumulator p x bits n by omega]

/-- Every state, including the index, has an explicit polynomial numeric bound. -/
theorem hornerLoopStep_iterate_le (p x : ℕ) (bits : List Bool) (n : ℕ) :
    (hornerLoopStep p x bits)^[n] 0 ≤ (n + 1) * (p + 1) := by
  rw [hornerLoopStep_iterate, Nat.add_mul, Nat.one_mul]
  have := hornerAccumulator_le p x bits n
  omega

theorem hornerBlockCount_unaryFn {p : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hbits : bits ∈ FP) :
    UnaryFn fun z => hornerBlockCount (p z) (bits z) :=
  (UnaryFn.length hbits).div (residueWidth_unaryFn hp)

theorem hornerCoefficient_unaryFn {p index : List Bool → ℕ}
    {bits : List Bool → List Bool} (hp : UnaryFn p) (hi : UnaryFn index) (hbits : bits ∈ FP) :
    UnaryFn fun z => hornerCoefficient (p z) (bits z) (index z) :=
  fromBits_min_unaryFn
    (messageWordBits_mem_FP hp
      ((hornerBlockCount_unaryFn hp hbits).sub (hi.add (UnaryFn.const 1))) hbits) hp

theorem hornerUpdate_unaryFn {p x coefficient accumulator : List Bool → ℕ}
    (hp : UnaryFn p) (hx : UnaryFn x) (hc : UnaryFn coefficient) (ha : UnaryFn accumulator) :
    UnaryFn fun z => hornerUpdate (p z) (x z) (coefficient z) (accumulator z) :=
  ((hc.add (hx.mul ha)).mod hp).min hp

theorem hornerLoopStep_unaryFn {p x state : List Bool → ℕ}
    {bits : List Bool → List Bool} (hp : UnaryFn p) (hx : UnaryFn x)
    (hs : UnaryFn state) (hbits : bits ∈ FP) :
    UnaryFn fun z => hornerLoopStep (p z) (x z) (bits z) (state z) := by
  have hb := hp.add (UnaryFn.const 1)
  have hi := hs.div hb
  exact ((hi.add (UnaryFn.const 1)).mul hb).add
    (hornerUpdate_unaryFn hp hx (hornerCoefficient_unaryFn hp hi hbits) (hs.mod hb))

/-- Actual upstream machine-time certificate for a polynomially bounded Horner loop. -/
theorem hornerAccumulator_unaryFn {p x count : List Bool → ℕ}
    {bits : List Bool → List Bool} (hp : UnaryFn p) (hx : UnaryFn x)
    (hc : UnaryFn count) (hbits : bits ∈ FP) :
    UnaryFn fun z => hornerAccumulator (p z) (x z) (bits z) (count z) := by
  have hstep := hornerLoopStep_unaryFn hp.lift hx.lift UnaryFn.index
    (mem_FP_comp Cobham.fstBlock_mem_FP hbits)
  have hbound := (hc.add (UnaryFn.const 1)).mul (hp.add (UnaryFn.const 1))
  have hloop := UnaryFn.iterate (s := fun z => hornerLoopStep (p z) (x z) (bits z))
    hstep (UnaryFn.const 0) hc hbound (fun z j hj =>
      (hornerLoopStep_iterate_le _ _ _ _).trans (Nat.mul_le_mul_right _ (by omega)))
  refine (hloop.mod (hp.add (UnaryFn.const 1))).of_eq (fun z => ?_)
  rw [hornerLoopStep_iterate]
  have ha : hornerAccumulator (p z) (x z) (bits z) (count z) < p z + 1 := by
    have := hornerAccumulator_le (p z) (x z) (bits z) (count z)
    omega
  simp [Nat.add_mod, Nat.mod_eq_of_lt ha]

@[simp] theorem hornerBlockCount_encodeMessage {p : ℕ} (as : List (ZMod p)) :
    hornerBlockCount p (encodeMessage as) = as.length := by
  have hw : 0 < residueWidth p := by simp [residueWidth]
  simp [hornerBlockCount, Nat.ne_of_gt hw]

theorem hornerCoefficient_encodeMessage {p : ℕ} [NeZero p]
    (as : List (ZMod p)) (i : ℕ) (hi : i < as.length) :
    hornerCoefficient p (encodeMessage as) i = as[as.length - (i + 1)].val := by
  have hindex : as.length - (i + 1) < as.length := by omega
  rw [hornerCoefficient, hornerBlockCount_encodeMessage,
    messageWordBits_encodeMessage_getElem as _ hindex]
  simp [Nat.min_eq_left (Nat.le_of_lt (as[as.length - (i + 1)].val_lt))]

theorem hornerUpdate_cast {p : ℕ} [NeZero p] (x coefficient accumulator : ℕ) :
    (hornerUpdate p x coefficient accumulator : ZMod p) =
      (coefficient : ZMod p) + (x : ZMod p) * (accumulator : ZMod p) := by
  rw [hornerUpdate, min_eq_left (Nat.le_of_lt (Nat.mod_lt _ (NeZero.pos p)))]
  simp

/-- After `n` reverse-order updates the accumulator evaluates exactly the last
`n` coefficients. This is the semantic invariant of the actual bounded loop. -/
theorem hornerAccumulator_encodeMessage {p : ℕ} [NeZero p]
    (x : ZMod p) (as : List (ZMod p)) (n : ℕ) (hn : n ≤ as.length) :
    (hornerAccumulator p x.val (encodeMessage as) n : ZMod p) =
      (coefficientsEvalWithCost x (as.drop (as.length - n))).1 := by
  induction n with
  | zero => simp [hornerAccumulator, coefficientsEvalWithCost]
  | succ n ih =>
    have hlt : n < as.length := by omega
    have hindex : as.length - (n + 1) < as.length := by omega
    have hsucc : as.length - (n + 1) + 1 = as.length - n := by omega
    rw [hornerAccumulator, hornerUpdate_cast, hornerCoefficient_encodeMessage as n hlt,
      List.drop_eq_getElem_cons hindex, hsucc]
    simp [coefficientsEvalWithCost, ih (by omega)]

/-- The completed numeric machine loop equals the existing field-list evaluator. -/
theorem hornerAccumulator_value {p : ℕ} [NeZero p]
    (x : ZMod p) (as : List (ZMod p)) :
    (hornerAccumulator p x.val (encodeMessage as)
      (hornerBlockCount p (encodeMessage as)) : ZMod p) =
      (coefficientsEvalWithCost x as).1 := by
  simpa using hornerAccumulator_encodeMessage x as as.length le_rfl

/-- A total bounded raw-message evaluator. The empty string encodes failure;
successful words always have the positive residue width. -/
def evaluateMessageBits (p limit : ℕ) (x bits : List Bool) : List Bool :=
  if CanonicalResidueBits p x ∧ validateMessageBits p limit bits = true then
    wordBits (reduceResidueWord p (hornerAccumulator p (min (Nat.fromBits x) p) bits
      (hornerBlockCount p bits)))
  else []

theorem evaluateMessageBits_mem_FP {p limit : List Bool → ℕ}
    {x bits : List Bool → List Bool} (hp : UnaryFn p) (hlimit : UnaryFn limit)
    (hx : x ∈ FP) (hbits : bits ∈ FP) :
    (fun z => evaluateMessageBits (p z) (limit z) (x z) (bits z)) ∈ FP := by
  have hvalid := (messageBitsValid_fppred hp hlimit hbits).of_iff
    (fun _ => (validateMessageBits_eq_true _ _ _).symm)
  exact ((canonicalResidueBits_fppred hp hx).and hvalid).ite_mem_FP
    (reduceResidueWord_bits_mem_FP hp
      (hornerAccumulator_unaryFn hp (fromBits_min_unaryFn hx hp)
        (hornerBlockCount_unaryFn hp hbits) hbits)) (constFn_mem_FP [])

@[simp] theorem evaluateMessageBits_encodeMessage {p : ℕ} [NeZero p]
    (limit : ℕ) (x : ZMod p) (as : List (ZMod p)) (hlen : as.length ≤ limit) :
    evaluateMessageBits p limit (wordBits (encodeResidue x)) (encodeMessage as) =
      wordBits (encodeResidue (coefficientsEvalWithCost x as).1) := by
  have hvalid : validateMessageBits p limit (encodeMessage as) = true :=
    (validateMessageBits_eq_true _ _ _).mpr
      ((messageBitsValid_iff_encoding _ _).mpr ⟨as, rfl, hlen⟩)
  simp only [evaluateMessageBits, canonicalResidueBits_wordBits, encodeResidue_toNat,
    x.val_lt, hvalid, and_self, ite_true, fromBits_wordBits,
    min_eq_left (Nat.le_of_lt x.val_lt)]
  rw [reduceResidueWord_eq_encodeResidue, hornerAccumulator_value]

/-- The total evaluator respects the residue-word output budget on every input. -/
theorem evaluateMessageBits_length_le (p limit : ℕ) (x bits : List Bool) :
    (evaluateMessageBits p limit x bits).length ≤ residueWidth p := by
  unfold evaluateMessageBits
  split <;> simp

/-- Exact agreement with parsing followed by the existing coefficient evaluator,
for every modulus and every raw challenge/message, including malformed inputs. -/
theorem evaluateMessageBits_eq (p limit : ℕ) (x bits : List Bool) :
    evaluateMessageBits p limit x bits =
      if CanonicalResidueBits p x then
        match parseMessage p limit bits with
        | none => []
        | some as => wordBits (encodeResidue
            (coefficientsEvalWithCost (Nat.fromBits x : ZMod p) as).1)
      else [] := by
  by_cases hx : CanonicalResidueBits p x
  · have hp : p ≠ 0 := by have := hx.2; omega
    let : NeZero p := ⟨hp⟩
    obtain ⟨a, ha⟩ := (canonicalResidueBits_iff_encode x).mp hx
    have havalue : (Nat.fromBits x : ZMod p) = a := by
      rw [← ha, fromBits_wordBits, encodeResidue_toNat, ZMod.natCast_zmod_val]
    rw [ite_eq_left hx, havalue]
    cases hparse : parseMessage p limit bits with
    | none =>
      have hvalid : validateMessageBits p limit bits = false := by
        rw [validateMessageBits_eq_parseMessage_isSome, hparse]
        rfl
      simp [evaluateMessageBits, hvalid]
    | some as =>
      obtain ⟨hbits, hlen⟩ := parseMessage_sound limit bits as hparse
      rw [← ha, ← hbits]
      exact evaluateMessageBits_encodeMessage limit a as hlen
  · simp [evaluateMessageBits, hx]

/-- Runtime certificate for the original parser and field evaluator composed
at their exact semantic interface, with canonical point validation. -/
theorem parseMessage_coefficientsEval_mem_FP {p limit : List Bool → ℕ}
    {x bits : List Bool → List Bool} (hp : UnaryFn p) (hlimit : UnaryFn limit)
    (hx : x ∈ FP) (hbits : bits ∈ FP) :
    (fun z => if CanonicalResidueBits (p z) (x z) then
      match parseMessage (p z) (limit z) (bits z) with
      | none => []
      | some as => wordBits (encodeResidue
          (coefficientsEvalWithCost (Nat.fromBits (x z) : ZMod (p z)) as).1)
      else []) ∈ FP :=
  mem_FP_of_eq (evaluateMessageBits_mem_FP hp hlimit hx hbits)
    (fun z => by
      rw [evaluateMessageBits_eq]
      by_cases h : CanonicalResidueBits (p z) (x z)
      · simp only [h, ite_true]
        cases parseMessage (p z) (limit z) (bits z) <;> rfl
      · simp [h])

/-- Failure is exactly a malformed challenge or a rejected bounded message. -/
theorem evaluateMessageBits_eq_nil_iff (p limit : ℕ) (x bits : List Bool) :
    evaluateMessageBits p limit x bits = [] ↔
      ¬ (CanonicalResidueBits p x ∧ ∃ as, parseMessage p limit bits = some as) := by
  have hword : wordBits (reduceResidueWord p (hornerAccumulator p
      (min (Nat.fromBits x) p) bits (hornerBlockCount p bits))) ≠ [] :=
    List.cons_ne_nil _ _
  simp [evaluateMessageBits, hword, validateMessageBits_eq_true,
    messageBitsValid_iff_parseMessage]

/-- The exact existing field-list Horner value has a genuine `FP` certificate
whenever its canonical encoded point and coefficient message are in `FP`. -/
theorem coefficientsEval_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (x : (z : List Bool) → ZMod (p z))
    (as : (z : List Bool) → List (ZMod (p z)))
    (hx : (fun z => wordBits (encodeResidue (x z))) ∈ FP)
    (has : (fun z => encodeMessage (as z)) ∈ FP) :
    (fun z => wordBits (encodeResidue (coefficientsEvalWithCost (x z) (as z)).1)) ∈ FP := by
  apply mem_FP_of_eq
    (evaluateMessageBits_mem_FP hp (hornerBlockCount_unaryFn hp has) hx has)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  exact evaluateMessageBits_encodeMessage _ (x z) (as z) (by simp)

/-- The runtime certificate applies to the existing checked word-level Horner
implementation on canonical encoded coefficients. -/
theorem wordHorner_encoded_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (x : (z : List Bool) → ZMod (p z))
    (as : (z : List Bool) → List (ZMod (p z)))
    (hx : (fun z => wordBits (encodeResidue (x z))) ∈ FP)
    (has : (fun z => encodeMessage (as z)) ∈ FP) :
    (fun z => wordResultBits (wordHorner (p z) (encodeResidue (x z))
      ((as z).map encodeResidue))) ∈ FP := by
  apply mem_FP_of_eq (coefficientsEval_bits_mem_FP hp hnz x as hx has)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  simp [wordResultBits]

/-- Evaluation of the semantic polynomial is computed by the certified Horner
machine; no polynomial expansion is part of that computation. -/
theorem coefficientsPolynomial_eval_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (x : (z : List Bool) → ZMod (p z))
    (as : (z : List Bool) → List (ZMod (p z)))
    (hx : (fun z => wordBits (encodeResidue (x z))) ∈ FP)
    (has : (fun z => encodeMessage (as z)) ∈ FP) :
    (fun z => wordBits (encodeResidue ((coefficientsPolynomial (as z)).eval (x z)))) ∈ FP := by
  exact mem_FP_of_eq (coefficientsEval_bits_mem_FP hp hnz x as hx has)
    (fun z => by rw [coefficientsEvalWithCost_value])

end IPPSPACE

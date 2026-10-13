/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.RawView
import IPPSPACE.Protocol.WordArithmeticFP
import IPPSPACE.Protocol.SyntaxResourcesFP
import IPPSPACE.Protocol.ScheduleFP

/-!
# Polynomial-time access to the private challenge tape

Consecutive fixed-width blocks use the original most-significant-first word
convention. Missing raw coins are false. Reading a block and reducing its value
modulo the polynomially bounded field size have actual upstream FP certificates.
The refinement theorem identifies these blocks with the existing decoded tape.
-/

namespace IPPSPACE

open Complexity

theorem wordBits_bitsToWord {width : ℕ} (bits : Fin width → Bool) :
    wordBits (bitsToWord bits) = List.ofFn bits := by
  induction width with
  | zero => rfl
  | succ width ih => simp [bitsToWord, wordBits, ih, List.ofFn_succ, Fin.tail_def]

/-- One raw private block. Missing coins have the existing false default. -/
def rawCoinWord (p index : ℕ) (coins : List Bool) : BitVec (residueWidth p) :=
  bitsToWord (fun i => coins[index * residueWidth p + i.val]?.getD false)

theorem rawCoinWord_bits (p index : ℕ) (coins : List Bool) :
    wordBits (rawCoinWord p index coins) =
      (List.range (residueWidth p)).map
        (fun i => coins[index * residueWidth p + i]?.getD false) := by
  rw [rawCoinWord, wordBits_bitsToWord]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem rawCoinWord_bits_mem_FP {p index : List Bool → ℕ} {coins : List Bool → List Bool}
    (hp : UnaryFn p) (hindex : UnaryFn index) (hcoins : coins ∈ FP) :
    (fun z => wordBits (rawCoinWord (p z) (index z) (coins z))) ∈ FP := by
  have hw := residueWidth_unaryFn hp
  have hbit := getBit_mem_FP (mem_FP_comp pairFst_mem_FP hcoins)
    ((hindex.lift.mul hw.lift).add UnaryFn.index)
  apply mem_FP_of_eq (flatMap_range_mem_FP hbit hw.mem_FP)
  intro z
  simp only [rawCoinWord_bits, pairFst_pair, pairSnd_pair, List.length_replicate]
  simp only [Function.comp_apply, pairFst_pair, List.map_eq_flatMap]

theorem rawCoinWord_value_unaryFn {p index : List Bool → ℕ} {coins : List Bool → List Bool}
    (hp : UnaryFn p) (hindex : UnaryFn index) (hcoins : coins ∈ FP) :
    UnaryFn fun z => (rawCoinWord (p z) (index z) (coins z)).toNat :=
  residueWordValue_unaryFn hp _ (rawCoinWord_bits_mem_FP hp hindex hcoins)

/-- The actual sampled field value, in its canonical residue-word encoding. -/
def rawCoinChallengeBits (p index : ℕ) (coins : List Bool) : List Bool :=
  wordBits (encodeResidue (sampleResidue p (rawCoinWord p index coins)))

theorem rawCoinChallengeBits_mem_FP {p index : List Bool → ℕ}
    {coins : List Bool → List Bool} (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (hindex : UnaryFn index) (hcoins : coins ∈ FP) :
    (fun z => rawCoinChallengeBits (p z) (index z) (coins z)) ∈ FP := by
  apply mem_FP_of_eq
    (reduceResidueWord_bits_mem_FP hp (rawCoinWord_value_unaryFn hp hindex hcoins))
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  rw [reduceResidueWord_eq_encodeResidue]
  rfl

@[simp] theorem rawCoinChallengeBits_length (p index : ℕ) (coins : List Bool) :
    (rawCoinChallengeBits p index coins).length = residueWidth p := by
  simp [rawCoinChallengeBits]

theorem decodedTapeWords_raw_eq (input coins : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) (h : decodeClosedPrenex input = some φ)
    (index : ℕ) (hi : index < φ.val.schedule.length) :
    decodedTapeWords input (coinTapeFromList input coins) φ h index =
      rawCoinWord (protocolPrime (nodeCount φ.val.toQBF)) index coins := by
  simp only [decodedTapeWords, hi, dite_true, randomTapeEquiv, Equiv.coe_fn_mk,
    coinTapeFromList, rawCoinWord, finProdFinEquiv]
  congr 1
  funext i
  congr 2
  simp only [Nat.mul_comm, Nat.add_comm]

/-- The outgoing procedure uses the number of completed transcript pairs. Only
the previous real-round challenge is revealed; the first and dummy messages are
empty. Its input guard is the original closed-prenex decoder. -/
def verifierMessageAtCount (input coins : List Bool) (count : ℕ) : List Bool :=
  if (decodeClosedPrenex input).isSome ∧ 0 < count / 2 ∧
      count / 2 < ((decodePrenex input).map (fun φ => φ.schedule.length)).getD 0 then
    rawCoinChallengeBits (protocolPrime (((decodeQBF input).map nodeCount).getD 0))
      (count / 2 - 1) coins
  else []

theorem verifierMessageAtCount_mem_FP {input coins : List Bool → List Bool}
    {count : List Bool → ℕ} (hinput : input ∈ FP) (hcoins : coins ∈ FP)
    (hcount : UnaryFn count) :
    (fun z => verifierMessageAtCount (input z) (coins z) (count z)) ∈ FP := by
  have hround := hcount.div (UnaryFn.const 2)
  have hprime := decodedProtocolPrime_unaryFn hinput
  have hnonzero : ∀ z, protocolPrime (((decodeQBF (input z)).map nodeCount).getD 0) ≠ 0 :=
    fun z => (protocolPrime_spec _).1.ne_zero
  exact ((decodeClosedPrenex_success_fppred hinput).and
    ((FPPred.lt (UnaryFn.const 0) hround).and
      (FPPred.lt hround (decodePrenex_scheduleLength_unaryFn hinput)))).ite_mem_FP
        (rawCoinChallengeBits_mem_FP hprime hnonzero (hround.sub (UnaryFn.const 1)) hcoins)
        (constFn_mem_FP [])

theorem verifierMessageAtCount_eq (input coins : List Bool) (history : List (List Bool)) :
    verifierMessageAtCount input coins history.length = rawVerifierMessage input coins history := by
  cases hd : decodeClosedPrenex input with
  | none =>
    simp only [verifierMessageAtCount, hd, Option.isSome_none, Bool.false_eq_true,
      false_and, ↓reduceIte]
    unfold rawVerifierMessage encodedVerifierMessage
    split
    · rfl
    · rename_i φ hφ
      simp [hd] at hφ
  | some φ =>
    have he := (decodeClosedPrenex_eq_some_iff input φ).mp hd
    have hq : decodeQBF input = some φ.val.toQBF := by rw [← he]; simp
    have hp : decodePrenex input = some φ.val := by rw [← he]; simp
    rw [rawVerifierMessage, encodedVerifierMessage_decoded input _ history φ hd]
    simp only [verifierMessageAtCount, hd, hq, hp, Option.isSome_some, Option.map_some,
      Option.getD_some, true_and]
    by_cases hn : history.length / 2 < φ.val.schedule.length
    · cases hr : history.length / 2 with
      | zero => simp
      | succ round =>
        have hi : round < φ.val.schedule.length := by omega
        simp only [Nat.succ_pos, true_and, Nat.add_sub_cancel,
          paddedVerifierMessage, delayedVerifierMessage]
        rw [decodedTapeWords_raw_eq input coins φ hd round hi]
        simp [rawCoinChallengeBits, encodeMessage]
    · simp [hn, paddedVerifierMessage]

/-- Runtime of the exact existing outgoing message function. Its dependence on
the history is entirely through the polynomial-time message count. -/
theorem rawVerifierMessage_mem_FP {input coins : List Bool → List Bool}
    (history : List Bool → List (List Bool)) (hinput : input ∈ FP) (hcoins : coins ∈ FP)
    (hcount : UnaryFn fun z => (history z).length) :
    (fun z => rawVerifierMessage (input z) (coins z) (history z)) ∈ FP :=
  mem_FP_of_eq (verifierMessageAtCount_mem_FP hinput hcoins hcount)
    (fun z => verifierMessageAtCount_eq (input z) (coins z) (history z))

end IPPSPACE

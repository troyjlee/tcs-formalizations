/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.P.StringAccess
import IPPSPACE.Protocol.WordArithmeticFP

/-!
# Polynomial-time validation of coefficient messages

The accepted raw strings of the existing bounded coefficient parser are exactly
those of bounded total length whose occupied fixed-width blocks are canonical
residue words. Checking all possible occupied blocks is polynomial-time using
upstream's actual `FP` string slicing and bounded-quantifier certificates.
This validates the input bytes; it does not certify construction of a decoded
coefficient list, Horner iteration, or the entire interactive verifier.
-/

namespace IPPSPACE

open Complexity

/-- The block at coefficient index `index`, retaining a partial final word. -/
def messageWordBits (p index : ℕ) (bits : List Bool) : List Bool :=
  (bits.drop (index * residueWidth p)).take (residueWidth p)

/-- Check every occupied coefficient slot, including a partial last slot.
The explicit total-length bound also rejects data beyond the slot budget. -/
def MessageBitsValid (p limit : ℕ) (bits : List Bool) : Prop :=
  bits.length ≤ limit * residueWidth p ∧
    ∀ i < limit, i * residueWidth p < bits.length →
      CanonicalResidueBits p (messageWordBits p i bits)

@[simp] theorem messageBitsValid_nil (p limit : ℕ) : MessageBitsValid p limit [] := by
  simp [MessageBitsValid]

@[simp] theorem messageBitsValid_zero (p : ℕ) (bits : List Bool) :
    MessageBitsValid p 0 bits ↔ bits = [] := by
  simp [MessageBitsValid]

private theorem messageWordBits_prepend_zero (p : ℕ) (word rest : List Bool)
    (hlen : word.length = residueWidth p) :
    messageWordBits p 0 (word ++ rest) = word := by
  simp [messageWordBits, ← hlen]

private theorem messageWordBits_prepend_succ (p i : ℕ) (word rest : List Bool)
    (hlen : word.length = residueWidth p) :
    messageWordBits p (i + 1) (word ++ rest) = messageWordBits p i rest := by
  simp only [messageWordBits, Nat.add_mul, Nat.one_mul]
  rw [Nat.add_comm (i * residueWidth p), ← hlen, ← List.drop_drop,
    List.drop_left]

theorem messageBitsValid_prepend (p limit : ℕ) (word rest : List Bool)
    (hlen : word.length = residueWidth p) :
    MessageBitsValid p (limit + 1) (word ++ rest) ↔
      CanonicalResidueBits p word ∧ MessageBitsValid p limit rest := by
  have hw : 0 < residueWidth p := by simp [residueWidth]
  simp only [MessageBitsValid, List.length_append, hlen, Nat.add_mul, Nat.one_mul]
  constructor
  · rintro ⟨hlength, hblocks⟩
    refine ⟨?_, by omega, ?_⟩
    · simpa only [messageWordBits_prepend_zero p word rest hlen] using
        hblocks 0 (by omega) (by omega)
    · intro i hi hoccupied
      have hlt : (i + 1) * residueWidth p < residueWidth p + rest.length := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [messageWordBits_prepend_succ p i word rest hlen] using
        hblocks (i + 1) (by omega) hlt
  · rintro ⟨hfirst, hlength, hblocks⟩
    refine ⟨by omega, ?_⟩
    intro i hi hoccupied
    cases i with
    | zero => simpa only [messageWordBits_prepend_zero p word rest hlen] using hfirst
    | succ i =>
      rw [Nat.add_mul, Nat.one_mul] at hoccupied
      simpa only [Nat.succ_eq_add_one, messageWordBits_prepend_succ p i word rest hlen] using
        hblocks i (by omega) (by omega)

/-- Every canonical raw word is the exact encoding of one field element. -/
theorem canonicalResidueBits_iff_encode {p : ℕ} [NeZero p] (bits : List Bool) :
    CanonicalResidueBits p bits ↔ ∃ a : ZMod p, wordBits (encodeResidue a) = bits := by
  constructor
  · rintro ⟨hlen, hvalue⟩
    refine ⟨(Nat.fromBits bits : ZMod p), ?_⟩
    rw [wordBits_eq_toBits, encodeResidue_toNat, ZMod.val_natCast_of_lt hvalue,
      ← hlen, Nat.toBits_fromBits]
  · rintro ⟨a, rfl⟩
    simpa using a.val_lt

/-- The chunk condition is exactly canonical bounded-list encoding. -/
theorem messageBitsValid_iff_encoding {p : ℕ} [NeZero p] (limit : ℕ) (bits : List Bool) :
    MessageBitsValid p limit bits ↔
      ∃ as : List (ZMod p), encodeMessage as = bits ∧ as.length ≤ limit := by
  induction limit generalizing bits with
  | zero =>
    simp only [messageBitsValid_zero]
    constructor
    · rintro rfl
      exact ⟨[], rfl, le_rfl⟩
    · rintro ⟨as, hencoding, hlength⟩
      have heq : as = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [heq, encodeMessage] using hencoding.symm
  | succ limit ih =>
    by_cases hnil : bits = []
    · subst bits
      exact ⟨fun _ => ⟨[], rfl, by simp⟩, fun _ => messageBitsValid_nil _ _⟩
    constructor
    · intro hvalid
      have hfirst : CanonicalResidueBits p (bits.take (residueWidth p)) := by
        have h := hvalid.2 0 (by omega) (by simpa using List.length_pos_iff.mpr hnil)
        simpa [messageWordBits] using h
      obtain ⟨a, ha⟩ := (canonicalResidueBits_iff_encode _).mp hfirst
      have hsplit : wordBits (encodeResidue a) ++ bits.drop (residueWidth p) = bits := by
        rw [ha, List.take_append_drop]
      have hrest : MessageBitsValid p limit (bits.drop (residueWidth p)) := by
        exact ((messageBitsValid_prepend p limit _ _ (length_wordBits _)).mp
          (hsplit.symm ▸ hvalid)).2
      obtain ⟨as, has, hlength⟩ := (ih _).mp hrest
      exact ⟨a :: as, by rw [encodeMessage, has, hsplit], by simpa using Nat.succ_le_succ hlength⟩
    · rintro ⟨as, hencoding, hlength⟩
      cases as with
      | nil => exact (hnil (by simpa [encodeMessage] using hencoding.symm)).elim
      | cons a as =>
        rw [← hencoding, encodeMessage]
        apply (messageBitsValid_prepend p limit _ _ (length_wordBits _)).mpr
        refine ⟨(canonicalResidueBits_iff_encode _).mpr ⟨a, rfl⟩, ?_⟩
        exact (ih _).mpr ⟨as, rfl, by simpa using Nat.le_of_succ_le_succ hlength⟩

/-- At modulus zero no nonempty residue word is canonical. -/
theorem messageBitsValid_zero_modulus (limit : ℕ) (bits : List Bool) :
    MessageBitsValid 0 limit bits ↔ bits = [] := by
  constructor
  · intro hvalid
    by_contra hnil
    have hpos : 0 < bits.length := List.length_pos_iff.mpr hnil
    have hlimit : 0 < limit := by
      have := hvalid.1
      by_contra h
      have : limit = 0 := by omega
      simp_all
    have hfirst := hvalid.2 0 hlimit (by simpa using hpos)
    exact Nat.not_lt_zero _ hfirst.2
  · rintro rfl
    exact messageBitsValid_nil _ _

/-- The existing parser also accepts only the empty message at modulus zero. -/
theorem parseMessage_zero_modulus_isSome (limit : ℕ) (bits : List Bool) :
    (parseMessage 0 limit bits).isSome ↔ bits = [] := by
  cases bits with
  | nil => simp
  | cons b bs =>
    cases limit with
    | zero => simp [parseMessage, parseMessageWithCost]
    | succ limit =>
      rw [parseMessage_step 0 limit _ (by simp)]
      cases hread : (readWordWithCost (residueWidth 0) (b :: bs)).1 with
      | none => simp
      | some result => simp [decodeResidue]

/-- Exact validation of the existing parser for every modulus, retaining count,
partial-word, and out-of-range rejection. -/
theorem messageBitsValid_iff_parseMessage (p limit : ℕ) (bits : List Bool) :
    MessageBitsValid p limit bits ↔ ∃ as, parseMessage p limit bits = some as := by
  by_cases hp : p = 0
  · subst p
    rw [messageBitsValid_zero_modulus, ← Option.isSome_iff_exists,
      parseMessage_zero_modulus_isSome]
  · let : NeZero p := ⟨hp⟩
    rw [messageBitsValid_iff_encoding]
    exact exists_congr (fun as => (parseMessage_eq_some_iff limit bits as).symm)

/-- A direct Boolean validator using only length and fixed-width block checks. -/
def validateMessageBits (p limit : ℕ) (bits : List Bool) : Bool :=
  decide (bits.length ≤ limit * residueWidth p) &&
    (List.range limit).all (fun i =>
      !(decide (i * residueWidth p < bits.length)) ||
        decide (CanonicalResidueBits p (messageWordBits p i bits)))

@[simp] theorem validateMessageBits_eq_true (p limit : ℕ) (bits : List Bool) :
    validateMessageBits p limit bits = true ↔ MessageBitsValid p limit bits := by
  simp [validateMessageBits, MessageBitsValid, List.all_eq_true, imp_iff_not_or]

theorem validateMessageBits_eq_parseMessage_isSome (p limit : ℕ) (bits : List Bool) :
    validateMessageBits p limit bits = (parseMessage p limit bits).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [validateMessageBits_eq_true, messageBitsValid_iff_parseMessage,
    Option.isSome_iff_exists]

/-- Selecting one potentially partial coefficient block is genuinely in `FP`. -/
theorem messageWordBits_mem_FP {p index : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hi : UnaryFn index) (hbits : bits ∈ FP) :
    (fun z => messageWordBits (p z) (index z) (bits z)) ∈ FP :=
  take_mem_FP (drop_mem_FP hbits (hi.mul (residueWidth_unaryFn hp))) (residueWidth_unaryFn hp)

/-- Genuine machine-level polynomial-time validation, on arbitrary raw strings.
Only the input-producing functions and numeric budgets require FP certificates. -/
theorem messageBitsValid_fppred {p limit : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hlimit : UnaryFn limit) (hbits : bits ∈ FP) :
    FPPred fun z => MessageBitsValid (p z) (limit z) (bits z) := by
  have hw := residueWidth_unaryFn hp
  have hlen := UnaryFn.length hbits
  have hchunk : (fun w => messageWordBits (p (pairFst w)) (pairSnd w).length
      (bits (pairFst w))) ∈ FP :=
    messageWordBits_mem_FP hp.lift UnaryFn.index (mem_FP_comp Cobham.fstBlock_mem_FP hbits)
  have hbody : FPPred fun w => ¬ (pairSnd w).length * residueWidth (p (pairFst w)) <
      (bits (pairFst w)).length ∨ CanonicalResidueBits (p (pairFst w))
        (messageWordBits (p (pairFst w)) (pairSnd w).length (bits (pairFst w))) :=
    ((FPPred.lt (UnaryFn.index.mul hw.lift) hlen.lift).not).or
      (canonicalResidueBits_fppred hp.lift hchunk)
  refine ((FPPred.le hlen (hlimit.mul hw)).and (FPPred.forall_lt hlimit hbody)).of_iff
    (fun z => ?_)
  simp only [MessageBitsValid, pairFst_pair, pairSnd_pair, List.length_replicate]
  simp only [imp_iff_not_or]

/-- The parser's successful-input language is a genuine polynomial-time test,
including zero modulus and all malformed inputs. -/
theorem parseMessage_success_fppred {p limit : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hlimit : UnaryFn limit) (hbits : bits ∈ FP) :
    FPPred fun z => ∃ as, parseMessage (p z) (limit z) (bits z) = some as := by
  refine (messageBitsValid_fppred hp hlimit hbits).of_iff (fun z => ?_)
  exact messageBitsValid_iff_parseMessage _ _ _

/-- The concrete Boolean block validator has an actual `FP` certificate. -/
theorem validateMessageBits_mem_FP {p limit : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hlimit : UnaryFn limit) (hbits : bits ∈ FP) :
    (fun z => [validateMessageBits (p z) (limit z) (bits z)]) ∈ FP := by
  have htest := (messageBitsValid_fppred hp hlimit hbits).of_iff
    (fun z => (validateMessageBits_eq_true _ _ _).symm)
  simpa only [Bool.decide_eq_true] using htest.flag_mem_FP

/-- Polynomial-time computation of the existing parser's Boolean success flag.
This does not assert an FP encoding of its decoded coefficient-list output. -/
theorem parseMessage_isSome_mem_FP {p limit : List Bool → ℕ} {bits : List Bool → List Bool}
    (hp : UnaryFn p) (hlimit : UnaryFn limit) (hbits : bits ∈ FP) :
    (fun z => [(parseMessage (p z) (limit z) (bits z)).isSome]) ∈ FP :=
  mem_FP_of_eq (validateMessageBits_mem_FP hp hlimit hbits)
    (fun _ => congrArg (fun b => [b]) (validateMessageBits_eq_parseMessage_isSome _ _ _))

end IPPSPACE

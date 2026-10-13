/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.PrimeField

/-!
# Bounded binary coefficient messages

A message concatenates canonical fixed-width residue words, most significant bit
first. The empty message represents the empty coefficient list. Parsing rejects
partial words, noncanonical residues, and too many coefficients. Its fuel limits
inspection even when an adversarial message has an arbitrarily long tail.

The instrumentation counts inspected input-list constructors and calls to residue
validation. It excludes the implementation costs of word construction, arithmetic,
and allocation; it is not a machine-time bound.
-/

namespace IPPSPACE

/-- Most-significant-bit-first list representation of a word. -/
def wordBits : {w : ℕ} → BitVec w → List Bool
  | 0, _ => []
  | w + 1, word => word.msb :: wordBits (word.setWidth w)

@[simp] theorem length_wordBits {w : ℕ} (word : BitVec w) :
    (wordBits word).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [wordBits, ih]

/-- Read exactly `w` bits, returning the uninspected suffix. -/
def readWordWithCost : (w : ℕ) → List Bool → Option (BitVec w × List Bool) × ℕ
  | 0, bs => (some (BitVec.nil, bs), 0)
  | _ + 1, [] => (none, 1)
  | w + 1, b :: bs =>
      let rest := readWordWithCost w bs
      (rest.1.map (fun result => (BitVec.cons b result.1, result.2)), rest.2 + 1)

theorem readWordWithCost_cost_le (w : ℕ) (bs : List Bool) :
    (readWordWithCost w bs).2 ≤ w := by
  induction w generalizing bs with
  | zero => simp [readWordWithCost]
  | succ w ih =>
    cases bs with
    | nil => simp [readWordWithCost]
    | cons b bs => simpa [readWordWithCost] using Nat.add_le_add_right (ih bs) 1

@[simp] theorem readWordWithCost_wordBits {w : ℕ} (word : BitVec w) (bs : List Bool) :
    (readWordWithCost w (wordBits word ++ bs)).1 = some (word, bs) := by
  induction w with
  | zero => simp [wordBits, readWordWithCost, BitVec.eq_nil word]
  | succ w ih => simp [wordBits, readWordWithCost, ih]

theorem readWordWithCost_eq_some {w : ℕ} {bs rest : List Bool} {word : BitVec w}
    (h : (readWordWithCost w bs).1 = some (word, rest)) : wordBits word ++ rest = bs := by
  induction w generalizing bs with
  | zero => simpa [readWordWithCost, wordBits] using (congrArg Prod.snd (Option.some.inj h)).symm
  | succ w ih =>
    cases bs with
    | nil => simp [readWordWithCost] at h
    | cons b bs =>
      cases hr : (readWordWithCost w bs).1 with
      | none => simp [readWordWithCost, hr] at h
      | some result =>
        rcases result with ⟨tail, suffix⟩
        have heq : (BitVec.cons b tail, suffix) = (word, rest) := by
          simpa [readWordWithCost, hr] using h
        cases heq
        simpa [wordBits] using congrArg (List.cons b) (ih hr)

/-- Concatenated canonical field words, with no padding between coefficients. -/
def encodeMessage {p : ℕ} : List (ZMod p) → List Bool
  | [] => []
  | a :: as => wordBits (encodeResidue a) ++ encodeMessage as

@[simp] theorem length_encodeMessage {p : ℕ} (as : List (ZMod p)) :
    (encodeMessage as).length = as.length * residueWidth p := by
  induction as with
  | nil => simp [encodeMessage]
  | cons a as ih => simp [encodeMessage, ih, Nat.add_mul, Nat.add_comm]

/-- The fuel counts coefficients. A zero budget inspects only the first list
constructor, and each positive step reads at most one fixed-width word. -/
def parseMessageWithCost (p : ℕ) : ℕ → List Bool → Option (List (ZMod p)) × ℕ
  | _, [] => (some [], 1)
  | 0, _ :: _ => (none, 1)
  | limit + 1, b :: bs =>
      let word := readWordWithCost (residueWidth p) (b :: bs)
      match word.1 with
      | none => (none, word.2 + 1)
      | some (w, suffix) =>
        match decodeResidue p w with
        | none => (none, word.2 + 2)
        | some a =>
          let rest := parseMessageWithCost p limit suffix
          (rest.1.map (List.cons a), word.2 + 2 + rest.2)

/-- The executable decoder used by the verifier. -/
def parseMessage (p limit : ℕ) (bits : List Bool) : Option (List (ZMod p)) :=
  (parseMessageWithCost p limit bits).1

theorem parseMessageWithCost_cost_le (p limit : ℕ) (bits : List Bool) :
    (parseMessageWithCost p limit bits).2 ≤ limit * (residueWidth p + 2) + 1 := by
  induction limit generalizing bits with
  | zero => cases bits <;> simp [parseMessageWithCost]
  | succ limit ih =>
    cases bits with
    | nil => simp [parseMessageWithCost]
    | cons b bs =>
      have hw := readWordWithCost_cost_le (residueWidth p) (b :: bs)
      simp only [parseMessageWithCost, Nat.add_mul, Nat.one_mul]
      cases hr : (readWordWithCost (residueWidth p) (b :: bs)).1 with
      | none => simp only; omega
      | some result =>
        rcases result with ⟨w, suffix⟩
        simp only
        cases hd : decodeResidue p w with
        | none => simp only; omega
        | some a =>
          simp only
          have hi := ih suffix
          omega


@[simp] theorem parseMessage_nil (p limit : ℕ) : parseMessage p limit [] = some [] := by
  cases limit <;> rfl

theorem parseMessage_step (p limit : ℕ) (bits : List Bool) (hbits : bits ≠ []) :
    parseMessage p (limit + 1) bits =
      (readWordWithCost (residueWidth p) bits).1.bind (fun result =>
        (decodeResidue p result.1).bind (fun a =>
          (parseMessage p limit result.2).map (List.cons a))) := by
  cases bits with
  | nil => contradiction
  | cons b bs =>
    simp only [parseMessage, parseMessageWithCost]
    split
    · simp_all
    · split <;> simp_all

/-- Every bounded coefficient list survives canonical encoding and parsing. -/
theorem parseMessage_encode {p : ℕ} [NeZero p] (limit : ℕ) (as : List (ZMod p))
    (h : as.length ≤ limit) : parseMessage p limit (encodeMessage as) = some as := by
  induction limit generalizing as with
  | zero =>
    have : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst as
    rfl
  | succ limit ih =>
    cases as with
    | nil => exact parseMessage_nil p (limit + 1)
    | cons a as =>
      have hn : wordBits (encodeResidue a) ++ encodeMessage as ≠ [] := by
        intro he
        have hlen := congrArg List.length he
        rw [List.length_append, length_wordBits] at hlen
        simp only [List.length_nil, residueWidth] at hlen
        omega
      rw [encodeMessage, parseMessage_step p limit _ hn, readWordWithCost_wordBits]
      simp [ih as (by simpa using Nat.le_of_succ_le_succ h)]

/-- Success forces both canonical representation and the coefficient-count bound. -/
theorem parseMessage_sound {p : ℕ} [NeZero p] (limit : ℕ) (bits : List Bool)
    (as : List (ZMod p)) (h : parseMessage p limit bits = some as) :
    encodeMessage as = bits ∧ as.length ≤ limit := by
  induction limit generalizing bits as with
  | zero =>
    cases bits with
    | nil =>
      have : as = [] := (Option.some.inj h).symm
      subst as
      simp [encodeMessage]
    | cons b bs => simp [parseMessage, parseMessageWithCost] at h
  | succ limit ih =>
    cases bits with
    | nil =>
      have : as = [] := (Option.some.inj h).symm
      subst as
      simp [encodeMessage]
    | cons b bs =>
      rw [parseMessage_step p limit _ (by simp)] at h
      cases hr : (readWordWithCost (residueWidth p) (b :: bs)).1 with
      | none => simp [hr] at h
      | some result =>
        rcases result with ⟨word, suffix⟩
        simp only [hr, Option.bind_some] at h
        cases hd : decodeResidue p word with
        | none => simp [hd] at h
        | some a =>
          simp only [hd, Option.bind_some] at h
          cases ht : parseMessage p limit suffix with
          | none => simp [ht] at h
          | some tail =>
            have heq : a :: tail = as := by simpa [ht] using h
            subst as
            obtain ⟨henc, hlen⟩ := ih suffix tail ht
            constructor
            · rw [encodeMessage, encodeResidue_decodeResidue word a hd, henc]
              exact readWordWithCost_eq_some hr
            · simpa using Nat.succ_le_succ hlen

/-- Exact characterization: malformed, partial, noncanonical, and oversized
messages are excluded by canonical encoding and the length bound. -/
theorem parseMessage_eq_some_iff {p : ℕ} [NeZero p] (limit : ℕ)
    (bits : List Bool) (as : List (ZMod p)) :
    parseMessage p limit bits = some as ↔ encodeMessage as = bits ∧ as.length ≤ limit := by
  constructor
  · exact parseMessage_sound limit bits as
  · rintro ⟨rfl, h⟩
    exact parseMessage_encode limit as h

/-- A successful message has exactly one fixed-width word per coefficient. -/
theorem parseMessage_bit_length {p : ℕ} [NeZero p] (limit : ℕ) (bits : List Bool)
    (as : List (ZMod p)) (h : parseMessage p limit bits = some as) :
    bits.length = as.length * residueWidth p ∧ bits.length ≤ limit * residueWidth p := by
  obtain ⟨rfl, hlen⟩ := parseMessage_sound limit bits as h
  rw [length_encodeMessage]
  exact ⟨rfl, Nat.mul_le_mul_right _ hlen⟩


/-- Oversized inputs are rejected regardless of their contents. -/
theorem parseMessage_reject_overlong {p : ℕ} [NeZero p] (limit : ℕ) (bits : List Bool)
    (h : limit * residueWidth p < bits.length) : parseMessage p limit bits = none := by
  cases hp : parseMessage p limit bits with
  | none => rfl
  | some as =>
    have := (parseMessage_bit_length limit bits as hp).2
    omega

/-- A partial trailing word cannot be a successful message. -/
theorem parseMessage_reject_partial {p : ℕ} [NeZero p] (limit : ℕ) (bits : List Bool)
    (h : bits.length % residueWidth p ≠ 0) : parseMessage p limit bits = none := by
  cases hp : parseMessage p limit bits with
  | none => rfl
  | some as =>
    have hlen := (parseMessage_bit_length limit bits as hp).1
    simp [hlen] at h

/-- A noncanonical first word is rejected without parsing its suffix. -/
theorem parseMessage_reject_noncanonical (p limit : ℕ) (word : BitVec (residueWidth p))
    (suffix : List Bool) (h : p ≤ word.toNat) :
    parseMessage p limit (wordBits word ++ suffix) = none := by
  have hn : wordBits word ++ suffix ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    rw [List.length_append, length_wordBits] at hlen
    simp only [List.length_nil, residueWidth] at hlen
    omega
  cases limit with
  | zero =>
    cases hb : wordBits word ++ suffix with
    | nil => exact (hn hb).elim
    | cons b bs => rfl
  | succ limit =>
    rw [parseMessage_step p limit _ hn, readWordWithCost_wordBits,
      Option.bind_some, (decodeResidue_eq_none_iff p word).mpr h]
    rfl

end IPPSPACE

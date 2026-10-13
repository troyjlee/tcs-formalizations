/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.BitVec

/-!
# A computable prime field and canonical binary words

A bounded search chooses a prime greater than `6 * (N + 1)^3` and at most twice
that threshold. The extra factor two accommodates modular sampling from binary
words. Bertrand's theorem proves that the executable search succeeds.

Residues are encoded by fixed-width words; decoding rejects noncanonical words.
This gives explicit representations, not a machine-time analysis of prime search
or field arithmetic.
-/

namespace IPPSPACE

/-- Search a finite interval for a prime above `n`; the default is unreachable
when `n` is positive. -/
def boundedPrime (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).find? (fun p => decide (n < p ∧ p.Prime))).getD 2

theorem boundedPrime_spec (n : ℕ) (hn : n ≠ 0) :
    (boundedPrime n).Prime ∧ n < boundedPrime n ∧ boundedPrime n ≤ 2 * n := by
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  unfold boundedPrime
  cases hfind : (List.range (2 * n + 1)).find? (fun p => decide (n < p ∧ p.Prime)) with
  | none =>
    have hnone := List.find?_eq_none.mp hfind p (List.mem_range.mpr (by omega))
    simp [hnp, hp] at hnone
  | some q =>
    have hq : n < q ∧ q.Prime := by simpa using List.find?_some hfind
    have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
    exact ⟨hq.2, hq.1, by simpa using Nat.le_of_lt_succ hmem⟩

/-- Enough field elements to absorb the factor-two modular sampling bias. -/
def protocolPrime (N : ℕ) : ℕ := boundedPrime (6 * (N + 1) ^ 3)

theorem protocolPrime_spec (N : ℕ) :
    (protocolPrime N).Prime ∧ 6 * (N + 1) ^ 3 < protocolPrime N ∧
      protocolPrime N ≤ 12 * (N + 1) ^ 3 := by
  have h := boundedPrime_spec (6 * (N + 1) ^ 3) (by positivity)
  refine ⟨h.1, h.2.1, h.2.2.trans_eq ?_⟩
  ring

instance protocolPrime_prime (N : ℕ) : Fact (protocolPrime N).Prime :=
  ⟨(protocolPrime_spec N).1⟩

/-- The protocol uses the ordinary prime field with the searched modulus. -/
abbrev ProtocolField (N : ℕ) := ZMod (protocolPrime N)

/-- A positive-width word with enough room for every residue. -/
def residueWidth (p : ℕ) : ℕ := p.log2 + 1

theorem lt_two_pow_residueWidth (p : ℕ) : p < 2 ^ residueWidth p := Nat.lt_log2_self

theorem two_pow_residueWidth_le (p : ℕ) (hp : p ≠ 0) : 2 ^ residueWidth p ≤ 2 * p := by
  simpa [residueWidth, pow_succ, Nat.mul_comm] using
    Nat.mul_le_mul_left 2 (Nat.log2_self_le hp)

theorem residueWidth_le (p : ℕ) : residueWidth p ≤ p + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self p) 1

/-- The canonical encoding of a residue is its least nonnegative representative. -/
def encodeResidue {p : ℕ} (a : ZMod p) : BitVec (residueWidth p) :=
  BitVec.ofNat (residueWidth p) a.val

/-- Reject a word representing a number outside `[0, p)`. -/
def decodeResidue (p : ℕ) (word : BitVec (residueWidth p)) : Option (ZMod p) :=
  if word.toNat < p then some (word.toNat : ZMod p) else none

@[simp] theorem encodeResidue_toNat {p : ℕ} [NeZero p] (a : ZMod p) :
    (encodeResidue a).toNat = a.val := by
  simp [encodeResidue, Nat.mod_eq_of_lt (a.val_lt.trans (lt_two_pow_residueWidth p))]

@[simp] theorem decodeResidue_encodeResidue {p : ℕ} [NeZero p] (a : ZMod p) :
    decodeResidue p (encodeResidue a) = some a := by
  simp [decodeResidue, a.val_lt]

theorem encodeResidue_decodeResidue {p : ℕ} [NeZero p]
    (word : BitVec (residueWidth p)) (a : ZMod p) (h : decodeResidue p word = some a) :
    encodeResidue a = word := by
  unfold decodeResidue at h
  split at h
  next hlt =>
    have ha : (word.toNat : ZMod p) = a := Option.some.inj h
    apply BitVec.eq_of_toNat_eq
    rw [encodeResidue_toNat, ← ha, ZMod.val_natCast_of_lt hlt]
  next => simp at h

theorem decodeResidue_eq_none_iff (p : ℕ) (word : BitVec (residueWidth p)) :
    decodeResidue p word = none ↔ p ≤ word.toNat := by
  simp [decodeResidue]

end IPPSPACE

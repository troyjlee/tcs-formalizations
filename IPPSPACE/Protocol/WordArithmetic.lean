/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.PrimeField
import IPPSPACE.Protocol.Coefficients

/-!
# Arithmetic on canonical residue words

The executable operations below validate their operands, perform natural-number
arithmetic, reduce modulo the modulus, and return a canonical word. Their
refinement theorems connect these algorithms to ordinary `ZMod` arithmetic.
The bounds concern the sizes of intermediate numbers, not machine running time.
-/

namespace IPPSPACE

/-- Reduce a natural number modulo `p` and store the result in a residue word. -/
def reduceResidueWord (p n : ℕ) : BitVec (residueWidth p) :=
  BitVec.ofNat (residueWidth p) (n % p)

@[simp] theorem reduceResidueWord_toNat {p : ℕ} [NeZero p] (n : ℕ) :
    (reduceResidueWord p n).toNat = n % p := by
  simp [reduceResidueWord,
    Nat.mod_eq_of_lt ((Nat.mod_lt n (NeZero.pos p)).trans (lt_two_pow_residueWidth p))]

theorem reduceResidueWord_canonical {p : ℕ} [NeZero p] (n : ℕ) :
    (reduceResidueWord p n).toNat < p := by
  simpa using Nat.mod_lt n (NeZero.pos p)

theorem reduceResidueWord_eq_encodeResidue {p : ℕ} [NeZero p] (n : ℕ) :
    reduceResidueWord p n = encodeResidue (n : ZMod p) := by
  apply BitVec.eq_of_toNat_eq
  simp [ZMod.val_natCast]

@[simp] theorem decodeResidue_reduceResidueWord {p : ℕ} [NeZero p] (n : ℕ) :
    decodeResidue p (reduceResidueWord p n) = some (n : ZMod p) := by
  rw [reduceResidueWord_eq_encodeResidue, decodeResidue_encodeResidue]

/-- Validate two words before evaluating a natural-number arithmetic operation. -/
def checkedWordBinary (p : ℕ) (f : ℕ → ℕ → ℕ)
    (a b : BitVec (residueWidth p)) : Option (BitVec (residueWidth p)) :=
  if a.toNat < p ∧ b.toNat < p then
    some (reduceResidueWord p (f a.toNat b.toNat))
  else none

/-- Modular addition; malformed operands are rejected. -/
def wordAdd (p : ℕ) := checkedWordBinary p (· + ·)

/-- Modular multiplication; malformed operands are rejected. -/
def wordMul (p : ℕ) := checkedWordBinary p (· * ·)

/-- Adding the modulus before subtraction avoids truncated negative differences. -/
def wordSub (p : ℕ) := checkedWordBinary p (fun a b => a + p - b)

/-- Modular negation; malformed operands are rejected. -/
def wordNeg (p : ℕ) (a : BitVec (residueWidth p)) :
    Option (BitVec (residueWidth p)) :=
  if a.toNat < p then some (reduceResidueWord p (p - a.toNat)) else none

theorem checkedWordBinary_eq_none_iff (p : ℕ) (f : ℕ → ℕ → ℕ)
    (a b : BitVec (residueWidth p)) :
    checkedWordBinary p f a b = none ↔ p ≤ a.toNat ∨ p ≤ b.toNat := by
  simp [checkedWordBinary]
  omega

theorem wordNeg_eq_none_iff (p : ℕ) (a : BitVec (residueWidth p)) :
    wordNeg p a = none ↔ p ≤ a.toNat := by
  simp [wordNeg]

theorem checkedWordBinary_canonical {p : ℕ} [NeZero p] (f : ℕ → ℕ → ℕ)
    (a b c : BitVec (residueWidth p)) (h : checkedWordBinary p f a b = some c) :
    c.toNat < p := by
  unfold checkedWordBinary at h
  split at h
  · cases Option.some.inj h
    exact reduceResidueWord_canonical _
  · simp at h

theorem wordNeg_canonical {p : ℕ} [NeZero p]
    (a c : BitVec (residueWidth p)) (h : wordNeg p a = some c) : c.toNat < p := by
  unfold wordNeg at h
  split at h
  · cases Option.some.inj h
    exact reduceResidueWord_canonical _
  · simp at h

@[simp] theorem wordAdd_encodeResidue {p : ℕ} [NeZero p] (a b : ZMod p) :
    wordAdd p (encodeResidue a) (encodeResidue b) = some (encodeResidue (a + b)) := by
  simp [wordAdd, checkedWordBinary, a.val_lt, b.val_lt,
    reduceResidueWord_eq_encodeResidue]

@[simp] theorem wordMul_encodeResidue {p : ℕ} [NeZero p] (a b : ZMod p) :
    wordMul p (encodeResidue a) (encodeResidue b) = some (encodeResidue (a * b)) := by
  simp [wordMul, checkedWordBinary, a.val_lt, b.val_lt,
    reduceResidueWord_eq_encodeResidue]

@[simp] theorem wordSub_encodeResidue {p : ℕ} [NeZero p] (a b : ZMod p) :
    wordSub p (encodeResidue a) (encodeResidue b) = some (encodeResidue (a - b)) := by
  have hle : b.val ≤ a.val + p := by have := b.val_lt; omega
  simp [wordSub, checkedWordBinary, a.val_lt, b.val_lt,
    reduceResidueWord_eq_encodeResidue, Nat.cast_sub hle]

@[simp] theorem wordNeg_encodeResidue {p : ℕ} [NeZero p] (a : ZMod p) :
    wordNeg p (encodeResidue a) = some (encodeResidue (-a)) := by
  simp [wordNeg, a.val_lt, reduceResidueWord_eq_encodeResidue,
    Nat.cast_sub (Nat.le_of_lt a.val_lt)]

theorem wordAdd_of_decode {p : ℕ} [NeZero p]
    (a b : BitVec (residueWidth p)) (x y : ZMod p)
    (ha : decodeResidue p a = some x) (hb : decodeResidue p b = some y) :
    wordAdd p a b = some (encodeResidue (x + y)) := by
  rw [← encodeResidue_decodeResidue a x ha, ← encodeResidue_decodeResidue b y hb]
  exact wordAdd_encodeResidue x y

theorem wordMul_of_decode {p : ℕ} [NeZero p]
    (a b : BitVec (residueWidth p)) (x y : ZMod p)
    (ha : decodeResidue p a = some x) (hb : decodeResidue p b = some y) :
    wordMul p a b = some (encodeResidue (x * y)) := by
  rw [← encodeResidue_decodeResidue a x ha, ← encodeResidue_decodeResidue b y hb]
  exact wordMul_encodeResidue x y

theorem wordSub_of_decode {p : ℕ} [NeZero p]
    (a b : BitVec (residueWidth p)) (x y : ZMod p)
    (ha : decodeResidue p a = some x) (hb : decodeResidue p b = some y) :
    wordSub p a b = some (encodeResidue (x - y)) := by
  rw [← encodeResidue_decodeResidue a x ha, ← encodeResidue_decodeResidue b y hb]
  exact wordSub_encodeResidue x y

theorem wordNeg_of_decode {p : ℕ} [NeZero p]
    (a : BitVec (residueWidth p)) (x : ZMod p) (ha : decodeResidue p a = some x) :
    wordNeg p a = some (encodeResidue (-x)) := by
  rw [← encodeResidue_decodeResidue a x ha]
  exact wordNeg_encodeResidue x

/-- Horner's rule implemented entirely with checked natural-number word operations.
The surrounding `wordCoefficientsEval` also checks `x` for an empty message. -/
def wordHorner (p : ℕ) (x : BitVec (residueWidth p)) :
    List (BitVec (residueWidth p)) → Option (BitVec (residueWidth p))
  | [] => some (reduceResidueWord p 0)
  | a :: as => do
      let rest ← wordHorner p x as
      let product ← wordMul p x rest
      wordAdd p a product

/-- Validate the evaluation point, then evaluate a list of coefficient words. -/
def wordCoefficientsEval (p : ℕ) (x : BitVec (residueWidth p))
    (as : List (BitVec (residueWidth p))) : Option (BitVec (residueWidth p)) :=
  if x.toNat < p then wordHorner p x as else none

@[simp] theorem wordHorner_encodeResidue {p : ℕ} [NeZero p]
    (x : ZMod p) (as : List (ZMod p)) :
    wordHorner p (encodeResidue x) (as.map encodeResidue) =
      some (encodeResidue (coefficientsEvalWithCost x as).1) := by
  induction as with
  | nil => simp [wordHorner, reduceResidueWord_eq_encodeResidue, coefficientsEvalWithCost]
  | cons a as ih => simp [wordHorner, ih, coefficientsEvalWithCost]

@[simp] theorem wordCoefficientsEval_encodeResidue {p : ℕ} [NeZero p]
    (x : ZMod p) (as : List (ZMod p)) :
    wordCoefficientsEval p (encodeResidue x) (as.map encodeResidue) =
      some (encodeResidue (coefficientsEvalWithCost x as).1) := by
  simp [wordCoefficientsEval, x.val_lt]

/-- The word implementation evaluates the same polynomial as the semantic list. -/
theorem wordCoefficientsEval_polynomial {p : ℕ} [NeZero p]
    (x : ZMod p) (as : List (ZMod p)) :
    wordCoefficientsEval p (encodeResidue x) (as.map encodeResidue) =
      some (encodeResidue ((coefficientsPolynomial as).eval x)) := by
  rw [wordCoefficientsEval_encodeResidue, coefficientsEvalWithCost_value]

theorem wordHorner_canonical {p : ℕ} [NeZero p]
    (x : BitVec (residueWidth p)) (as : List (BitVec (residueWidth p)))
    (r : BitVec (residueWidth p)) (h : wordHorner p x as = some r) : r.toNat < p := by
  cases as with
  | nil =>
    simp only [wordHorner, Option.some.injEq] at h
    rw [← h]
    exact reduceResidueWord_canonical _
  | cons a as =>
    cases hrest : wordHorner p x as with
    | none => simp [wordHorner, hrest] at h
    | some rest =>
      cases hproduct : wordMul p x rest with
      | none => simp [wordHorner, hrest, hproduct] at h
      | some product =>
        have hadd : wordAdd p a product = some r := by
          simpa [wordHorner, hrest, hproduct] using h
        exact checkedWordBinary_canonical _ a product r hadd

/-- With a canonical point, the internal evaluator succeeds exactly when every
coefficient word is canonical. -/
theorem wordHorner_isSome_iff {p : ℕ} [NeZero p]
    (x : BitVec (residueWidth p)) (hx : x.toNat < p)
    (as : List (BitVec (residueWidth p))) :
    (wordHorner p x as).isSome ↔ ∀ a ∈ as, a.toNat < p := by
  induction as with
  | nil => simp [wordHorner]
  | cons a as ih =>
    cases hrest : wordHorner p x as with
    | none =>
      simp only [hrest, Option.isSome_none, Bool.false_eq_true, false_iff] at ih
      simp [wordHorner, hrest, ih]
    | some rest =>
      have hr := wordHorner_canonical x as rest hrest
      have has : ∀ b ∈ as, b.toNat < p := ih.mp (by simp [hrest])
      simp [wordHorner, hrest, wordMul, wordAdd, checkedWordBinary, hx, hr]
      intro _
      exact ⟨fun _ => has, fun _ => Nat.mod_lt _ (NeZero.pos p)⟩

/-- The checked evaluator rejects exactly noncanonical points or coefficients. -/
theorem wordCoefficientsEval_isSome_iff {p : ℕ} [NeZero p]
    (x : BitVec (residueWidth p)) (as : List (BitVec (residueWidth p))) :
    (wordCoefficientsEval p x as).isSome ↔
      x.toNat < p ∧ ∀ a ∈ as, a.toNat < p := by
  by_cases hx : x.toNat < p
  · simp [wordCoefficientsEval, hx, wordHorner_isSome_iff x hx]
  · simp [wordCoefficientsEval, hx]

theorem wordCoefficientsEval_canonical {p : ℕ} [NeZero p]
    (x : BitVec (residueWidth p)) (as : List (BitVec (residueWidth p)))
    (r : BitVec (residueWidth p)) (h : wordCoefficientsEval p x as = some r) :
    r.toNat < p := by
  unfold wordCoefficientsEval at h
  split at h
  · exact wordHorner_canonical x as r h
  · simp at h

/-- The unreduced sum uses at most twice the modulus. -/
theorem wordAdd_intermediate_lt {p : ℕ} (a b : BitVec (residueWidth p))
    (ha : a.toNat < p) (hb : b.toNat < p) : a.toNat + b.toNat < 2 * p := by omega

/-- The unreduced product uses at most the square of the modulus. -/
theorem wordMul_intermediate_lt {p : ℕ} (a b : BitVec (residueWidth p))
    (ha : a.toNat < p) (hb : b.toNat < p) : a.toNat * b.toNat < p ^ 2 := by
  simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt ha hb

/-- The addition and truncated difference in subtraction are both bounded. -/
theorem wordSub_intermediate_lt {p : ℕ} (a b : BitVec (residueWidth p))
    (ha : a.toNat < p) : a.toNat + p < 2 * p ∧ a.toNat + p - b.toNat < 2 * p := by
  omega

theorem wordNeg_intermediate_le {p : ℕ} (a : BitVec (residueWidth p)) :
    p - a.toNat ≤ p := Nat.sub_le _ _

/-- All natural operands used by the arithmetic algorithms are polynomially
bounded for the protocol's computed modulus. This is a size bound only. -/
theorem protocolWord_intermediates_le (N : ℕ)
    (a b : BitVec (residueWidth (protocolPrime N)))
    (ha : a.toNat < protocolPrime N) (hb : b.toNat < protocolPrime N) :
    a.toNat + b.toNat ≤ 24 * (N + 1) ^ 3 ∧
      a.toNat * b.toNat ≤ (12 * (N + 1) ^ 3) ^ 2 ∧
      a.toNat + protocolPrime N ≤ 24 * (N + 1) ^ 3 ∧
      a.toNat + protocolPrime N - b.toNat ≤ 24 * (N + 1) ^ 3 ∧
      protocolPrime N - a.toNat ≤ 12 * (N + 1) ^ 3 := by
  have hp := (protocolPrime_spec N).2.2
  have hmul : a.toNat * b.toNat ≤ (12 * (N + 1) ^ 3) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul ((Nat.le_of_lt ha).trans hp) ((Nat.le_of_lt hb).trans hp)
  exact ⟨by omega, hmul, by omega, by omega, by omega⟩

end IPPSPACE

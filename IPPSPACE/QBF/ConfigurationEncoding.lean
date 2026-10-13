/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Fixed-width codes for the components of bounded machine configurations

The component product below is the exact shape of `Complexity.Code` in the
pinned upstream `Classes/Containments/Internal/ConfigCount.lean`, with its
four-symbol alphabet exposed as a parameter. State numbering and a two-bit
alphabet equivalence are explicit, so the codec is executable once supplied.
The input tape's contents are fixed by the input and are not stored again.
The actual upstream alphabet has constructors `zero`, `one`, `blank`, `start`;
one possible two-bit numbering is respectively `00`, `01`, `10`, `11`.
The companion `MachineConfiguration` module instantiates that equivalence
against the actual imported upstream type.

This generic module does not define a replacement machine model. The companion
module imports unchanged upstream machine/configuration-count sources. The
upstream `cfgCode_inj` theorem additionally requires
`Windowed` (fixed input contents and blank cells beyond the work/output window)
as well as `WithinDecisionSpace`; head bounds alone do not imply injectivity.
The companion module composes this codec with that actual finite code and proves
both directions of bounded configuration reconstruction.
No transition formula or complexity-class inclusion is assumed or proved here.
-/

namespace IPPSPACE

/-- An executable fixed-width encoder and a left-inverse partial decoder. -/
structure FixedWidthCodec (α : Type) (width : ℕ) where
  encode : α → (Fin width → Bool)
  decode : (Fin width → Bool) → Option α
  decode_encode : ∀ a, decode (encode a) = some a

namespace FixedWidthCodec

variable {α β : Type} {width v : ℕ}

theorem encode_injective (codec : FixedWidthCodec α width) :
    Function.Injective codec.encode := by
  intro a b h
  have := congrArg codec.decode h
  simpa only [codec.decode_encode, Option.some.injEq] using this

/-- Every such code gives the finite configuration-count bound needed for
the repeated-squaring reachability construction. -/
theorem card_le_two_pow [Fintype α] (codec : FixedWidthCodec α width) :
    Fintype.card α ≤ 2 ^ width := by
  simpa using Fintype.card_le_of_injective codec.encode codec.encode_injective

/-- Also check that the input is canonical. This rejects every word outside
the encoder's image, even when the component decoder chooses a default value. -/
def decodeCanonical (codec : FixedWidthCodec α width) (bits : Fin width → Bool) : Option α := do
  let a ← codec.decode bits
  if codec.encode a = bits then some a else none

@[simp] theorem decodeCanonical_encode (codec : FixedWidthCodec α width) (a : α) :
    codec.decodeCanonical (codec.encode a) = some a := by
  simp [decodeCanonical, codec.decode_encode]

theorem decodeCanonical_eq_some_iff (codec : FixedWidthCodec α width)
    (bits : Fin width → Bool) (a : α) :
    codec.decodeCanonical bits = some a ↔ codec.encode a = bits := by
  constructor
  · intro h
    unfold decodeCanonical at h
    cases hd : codec.decode bits with
    | none => simp [hd] at h
    | some b =>
      rw [hd] at h
      change (if codec.encode b = bits then some b else none) = some a at h
      split at h
      · next hb =>
        have hba : b = a := Option.some.inj h
        exact hba ▸ hb
      · simp at h
  · rintro rfl
    exact codec.decodeCanonical_encode a

/-- Transport an existing codec across explicit data equivalence. -/
def ofEquiv (e : α ≃ β) (codec : FixedWidthCodec β width) : FixedWidthCodec α width where
  encode a := codec.encode (e a)
  decode bits := (codec.decode bits).map e.symm
  decode_encode a := by simp [codec.decode_encode]

/-- Reassociate an arithmetic width expression without changing the bits. -/
def castWidth (h : width = v) (codec : FixedWidthCodec α width) : FixedWidthCodec α v :=
  h ▸ codec

/-- A word is its own fixed-width representation. -/
def word (width : ℕ) : FixedWidthCodec (Fin width → Bool) width where
  encode := id
  decode := some
  decode_encode _ := rfl

/-- Place product fields in consecutive blocks. -/
def prod (left : FixedWidthCodec α width) (right : FixedWidthCodec β v) :
    FixedWidthCodec (α × β) (width + v) where
  encode a := Fin.append (left.encode a.1) (right.encode a.2)
  decode bits := do
    let a ← left.decode (fun i => bits (Fin.castAdd v i))
    let b ← right.decode (fun i => bits (Fin.natAdd width i))
    pure (a, b)
  decode_encode a := by simp [left.decode_encode, right.decode_encode]

/-- Decode each member of a fixed finite tuple, failing if any member fails. -/
def sequence : {n : ℕ} → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, values => do
    let a ← values 0
    let tail ← sequence (fun i : Fin n => values i.succ)
    pure (Fin.cons a tail)

@[simp] theorem sequence_some {n : ℕ} (values : Fin n → α) :
    sequence (fun i => some (values i)) = some values := by
  induction n with
  | zero =>
    change some Fin.elim0 = some values
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    simp only [sequence, ih, pure, bind, Option.bind]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Row-major concatenation of a fixed number of equal-width fields. -/
def vector (codec : FixedWidthCodec α width) (n : ℕ) :
    FixedWidthCodec (Fin n → α) (n * width) where
  encode values i := codec.encode (values (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2
  decode bits := sequence (fun i => codec.decode (fun j => bits (finProdFinEquiv (i, j))))
  decode_encode values := by simp [codec.decode_encode]

/-- One-hot positions. The linear number of bits makes the eventual transition
formula local and keeps the configuration width polynomial. -/
def encodeFin {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (i = j)

/-- Select the first set bit; canonical decoding separately checks uniqueness. -/
def decodeFin : (n : ℕ) → (Fin n → Bool) → Option (Fin n)
  | 0, _ => none
  | n + 1, bits =>
    if bits 0 then some 0 else (decodeFin n (fun i => bits i.succ)).map Fin.succ

@[simp] theorem decodeFin_encodeFin {n : ℕ} (i : Fin n) :
    decodeFin n (encodeFin i) = some i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [decodeFin, encodeFin]
    · simpa [decodeFin, encodeFin] using
        congrArg (Option.map Fin.succ) (show decodeFin n (fun l => decide (j = l)) = some j
          from ih j)

/-- An `n`-element finite index occupies `n` one-hot bits. -/
def fin (n : ℕ) : FixedWidthCodec (Fin n) n where
  encode := encodeFin
  decode := decodeFin n
  decode_encode := decodeFin_encodeFin

end FixedWidthCodec

/-- The finite fields stored by upstream `Complexity.Code`, parameterized only
over its state type and four-symbol alphabet. Cells include position zero.
Work heads/cells have `space + 1` positions; the output also has its free verdict
cell, and the input head includes the input and first trailing blank. -/
abbrev ConfigurationComponents (Q Γ : Type) (tapes inputLength space : ℕ) : Type :=
  Q × Fin (inputLength + space + 2) ×
    (Fin tapes → Fin (space + 1) × (Fin (space + 1) → Γ)) ×
    (Fin (space + 2) × (Fin (space + 2) → Γ))

/-- Fixed machine constants are `states` and `tapes`; the width is linear in
input length and the space budget. -/
def configurationWidth (states tapes inputLength space : ℕ) : ℕ :=
  states + (inputLength + space + 2) + 3 * tapes * (space + 1) + 3 * (space + 2)

/-- An explicit codec for every field of the upstream finite configuration
code. The tape alphabet occupies exactly two bits per cell. -/
def configurationCodec {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ) :
    FixedWidthCodec (ConfigurationComponents Q Γ tapes inputLength space)
      (configurationWidth states tapes inputLength space) :=
  let symbol := FixedWidthCodec.ofEquiv symbolBits (FixedWidthCodec.word 2)
  let tape := fun n => (FixedWidthCodec.fin n).prod (symbol.vector n)
  let raw := (FixedWidthCodec.ofEquiv stateNumber (FixedWidthCodec.fin states)).prod
    ((FixedWidthCodec.fin (inputLength + space + 2)).prod
      (((tape (space + 1)).vector tapes).prod (tape (space + 2))))
  raw.castWidth (by dsimp [configurationWidth]; ring)

@[simp] theorem configurationCodec_roundtrip {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (c : ConfigurationComponents Q Γ tapes inputLength space) :
    (configurationCodec stateNumber symbolBits tapes inputLength space).decodeCanonical
      ((configurationCodec stateNumber symbolBits tapes inputLength space).encode c) = some c :=
  FixedWidthCodec.decodeCanonical_encode _ c

theorem configurationCodec_injective {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ) :
    Function.Injective (configurationCodec stateNumber symbolBits tapes inputLength space).encode :=
  FixedWidthCodec.encode_injective _

/-- The exact linear width polynomial; substituting a polynomial space bound
therefore yields a polynomial bound in encoded input length. -/
theorem configurationWidth_eq (states tapes inputLength space : ℕ) :
    configurationWidth states tapes inputLength space =
      (3 * tapes + 4) * space + inputLength + (states + 3 * tapes + 8) := by
  unfold configurationWidth
  ring

/-- The exact configuration width after substituting a polynomial space
budget. The state and tape counts are constants for a fixed machine. -/
noncomputable def configurationWidthPolynomial
    (states tapes : ℕ) (space : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3 * tapes + 4) * space + Polynomial.X +
    Polynomial.C (states + 3 * tapes + 8)

@[simp] theorem configurationWidthPolynomial_eval
    (states tapes : ℕ) (space : Polynomial ℕ) (inputLength : ℕ) :
    (configurationWidthPolynomial states tapes space).eval inputLength =
      configurationWidth states tapes inputLength (space.eval inputLength) := by
  simp [configurationWidthPolynomial, configurationWidth_eq]

end IPPSPACE

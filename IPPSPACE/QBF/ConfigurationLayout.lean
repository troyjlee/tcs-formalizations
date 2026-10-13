/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationEncoding

/-!
# Bit positions in the finite configuration codec

These positions expose every field of `configurationCodec`. They are defined
through its product/vector layout, so projection theorems also account for the
final arithmetic width cast. Their natural-number values are explicit offsets
usable as variable names in Boolean transition and acceptance formulas.
-/

namespace IPPSPACE

namespace FixedWidthCodec

@[simp] theorem castWidth_encode {α : Type} {width v : ℕ} (h : width = v)
    (codec : FixedWidthCodec α width) (a : α) (i : Fin width) :
    (codec.castWidth h).encode a (Fin.cast h i) = codec.encode a i := by
  cases h
  rfl

@[simp] theorem vector_encode {α : Type} {width : ℕ} (codec : FixedWidthCodec α width)
    (n : ℕ) (values : Fin n → α) (i : Fin n) (j : Fin width) :
    (codec.vector n).encode values (finProdFinEquiv (i, j)) = codec.encode (values i) j := by
  simp only [vector, Equiv.symm_apply_apply]

end FixedWidthCodec

/-- One head block followed by two symbol bits per tape cell. -/
def configurationTapeWidth (cells : ℕ) : ℕ := cells + cells * 2

/-- Width before reassociating the codec's nested products. -/
def configurationRawWidth (states tapes inputLength space : ℕ) : ℕ :=
  states + ((inputLength + space + 2) +
    (tapes * configurationTapeWidth (space + 1) + configurationTapeWidth (space + 2)))

theorem configurationRawWidth_eq (states tapes inputLength space : ℕ) :
    configurationRawWidth states tapes inputLength space =
      configurationWidth states tapes inputLength space := by
  unfold configurationRawWidth configurationTapeWidth configurationWidth
  ring

/-- State-number one-hot coordinate. -/
def configurationStateIndex (states tapes inputLength space : ℕ) (i : Fin states) :
    Fin (configurationWidth states tapes inputLength space) :=
  Fin.cast (configurationRawWidth_eq states tapes inputLength space)
    (Fin.castAdd _ i)

/-- Input-head one-hot coordinate. -/
def configurationInputHeadIndex (states tapes inputLength space : ℕ)
    (i : Fin (inputLength + space + 2)) :
    Fin (configurationWidth states tapes inputLength space) :=
  Fin.cast (configurationRawWidth_eq states tapes inputLength space)
    (Fin.natAdd states (Fin.castAdd _ i))

/-- Position inside the concatenation of the work-tape records. -/
def configurationWorkIndex (states tapes inputLength space : ℕ)
    (i : Fin (tapes * configurationTapeWidth (space + 1))) :
    Fin (configurationWidth states tapes inputLength space) :=
  Fin.cast (configurationRawWidth_eq states tapes inputLength space)
    (Fin.natAdd states (Fin.natAdd (inputLength + space + 2) (Fin.castAdd _ i)))

/-- Position inside the final output-tape record. -/
def configurationOutputIndex (states tapes inputLength space : ℕ)
    (i : Fin (configurationTapeWidth (space + 2))) :
    Fin (configurationWidth states tapes inputLength space) :=
  Fin.cast (configurationRawWidth_eq states tapes inputLength space)
    (Fin.natAdd states (Fin.natAdd (inputLength + space + 2)
      (Fin.natAdd (tapes * configurationTapeWidth (space + 1)) i)))

/-- Work-head one-hot coordinate, tape by tape. -/
def configurationWorkHeadIndex (states tapes inputLength space : ℕ)
    (tape : Fin tapes) (cell : Fin (space + 1)) :
    Fin (configurationWidth states tapes inputLength space) :=
  configurationWorkIndex states tapes inputLength space
    (finProdFinEquiv (tape, Fin.castAdd ((space + 1) * 2) cell))

/-- A work cell's first or second symbol bit. -/
def configurationWorkCellIndex (states tapes inputLength space : ℕ)
    (tape : Fin tapes) (cell : Fin (space + 1)) (bit : Fin 2) :
    Fin (configurationWidth states tapes inputLength space) :=
  configurationWorkIndex states tapes inputLength space
    (finProdFinEquiv (tape, Fin.natAdd (space + 1) (finProdFinEquiv (cell, bit))))

/-- Output-head one-hot coordinate. -/
def configurationOutputHeadIndex (states tapes inputLength space : ℕ)
    (cell : Fin (space + 2)) : Fin (configurationWidth states tapes inputLength space) :=
  configurationOutputIndex states tapes inputLength space
    (Fin.castAdd ((space + 2) * 2) cell)

/-- An output cell's first or second symbol bit. -/
def configurationOutputCellIndex (states tapes inputLength space : ℕ)
    (cell : Fin (space + 2)) (bit : Fin 2) :
    Fin (configurationWidth states tapes inputLength space) :=
  configurationOutputIndex states tapes inputLength space
    (Fin.natAdd (space + 2) (finProdFinEquiv (cell, bit)))

@[simp] theorem configurationStateIndex_val (q k n s : ℕ) (i : Fin q) :
    (configurationStateIndex q k n s i).val = i.val := rfl

@[simp] theorem configurationInputHeadIndex_val (q k n s : ℕ) (i : Fin (n + s + 2)) :
    (configurationInputHeadIndex q k n s i).val = q + i.val := rfl

@[simp] theorem configurationWorkHeadIndex_val (q k n s : ℕ)
    (t : Fin k) (i : Fin (s + 1)) :
    (configurationWorkHeadIndex q k n s t i).val =
      q + (n + s + 2) + 3 * (s + 1) * t.val + i.val := by
  change q + (n + s + 2 + (i.val + (s + 1 + (s + 1) * 2) * t.val)) = _
  ring

@[simp] theorem configurationWorkCellIndex_val (q k n s : ℕ)
    (t : Fin k) (i : Fin (s + 1)) (b : Fin 2) :
    (configurationWorkCellIndex q k n s t i b).val =
      q + (n + s + 2) + 3 * (s + 1) * t.val + (s + 1) + 2 * i.val + b.val := by
  change q + (n + s + 2 + (s + 1 + (b.val + 2 * i.val) +
    (s + 1 + (s + 1) * 2) * t.val)) = _
  ring

@[simp] theorem configurationOutputHeadIndex_val (q k n s : ℕ) (i : Fin (s + 2)) :
    (configurationOutputHeadIndex q k n s i).val =
      q + (n + s + 2) + 3 * k * (s + 1) + i.val := by
  change q + (n + s + 2 + (k * (s + 1 + (s + 1) * 2) + i.val)) = _
  ring

@[simp] theorem configurationOutputCellIndex_val (q k n s : ℕ)
    (i : Fin (s + 2)) (b : Fin 2) :
    (configurationOutputCellIndex q k n s i b).val =
      q + (n + s + 2) + 3 * k * (s + 1) + (s + 2) + 2 * i.val + b.val := by
  change q + (n + s + 2 + (k * (s + 1 + (s + 1) * 2) +
    (s + 2 + (b.val + 2 * i.val)))) = _
  ring

section Projections

set_option backward.isDefEq.respectTransparency false

variable {Q Γ : Type} {q : ℕ} (stateNumber : Q ≃ Fin q)
  (symbolBits : Γ ≃ (Fin 2 → Bool)) (k n s : ℕ)
  (c : ConfigurationComponents Q Γ k n s)

@[simp] theorem configurationCodec_encode_state (i : Fin q) :
    (configurationCodec stateNumber symbolBits k n s).encode c
      (configurationStateIndex q k n s i) = decide (stateNumber c.1 = i) := by
  simp [configurationCodec, configurationStateIndex, configurationRawWidth,
    configurationTapeWidth, FixedWidthCodec.prod,
    FixedWidthCodec.ofEquiv, FixedWidthCodec.fin, FixedWidthCodec.encodeFin]

@[simp] theorem configurationCodec_encode_inputHead (i : Fin (n + s + 2)) :
    (configurationCodec stateNumber symbolBits k n s).encode c
      (configurationInputHeadIndex q k n s i) = decide (c.2.1 = i) := by
  simp [configurationCodec, configurationInputHeadIndex, configurationRawWidth,
    configurationTapeWidth, FixedWidthCodec.prod,
    FixedWidthCodec.fin, FixedWidthCodec.encodeFin]

@[simp] theorem configurationCodec_encode_workHead (t : Fin k) (i : Fin (s + 1)) :
    (configurationCodec stateNumber symbolBits k n s).encode c
      (configurationWorkHeadIndex q k n s t i) = decide ((c.2.2.1 t).1 = i) := by
  simp [configurationCodec, configurationWorkHeadIndex, configurationWorkIndex, configurationRawWidth, configurationTapeWidth,
    FixedWidthCodec.prod, FixedWidthCodec.fin, FixedWidthCodec.encodeFin]

@[simp] theorem configurationCodec_encode_workCell
    (t : Fin k) (i : Fin (s + 1)) (b : Fin 2) :
    (configurationCodec stateNumber symbolBits k n s).encode c
      (configurationWorkCellIndex q k n s t i b) = symbolBits ((c.2.2.1 t).2 i) b := by
  simp [configurationCodec, configurationWorkCellIndex, configurationWorkIndex, configurationRawWidth, configurationTapeWidth,
    FixedWidthCodec.prod, FixedWidthCodec.ofEquiv, FixedWidthCodec.word]

@[simp] theorem configurationCodec_encode_outputHead (i : Fin (s + 2)) :
    (configurationCodec stateNumber symbolBits k n s).encode c
      (configurationOutputHeadIndex q k n s i) = decide (c.2.2.2.1 = i) := by
  simp [configurationCodec, configurationOutputHeadIndex, configurationOutputIndex, configurationRawWidth, configurationTapeWidth,
    FixedWidthCodec.prod, FixedWidthCodec.fin, FixedWidthCodec.encodeFin]

@[simp] theorem configurationCodec_encode_outputCell (i : Fin (s + 2)) (b : Fin 2) :
    (configurationCodec stateNumber symbolBits k n s).encode c
      (configurationOutputCellIndex q k n s i b) = symbolBits (c.2.2.2.2 i) b := by
  simp [configurationCodec, configurationOutputCellIndex, configurationOutputIndex, configurationRawWidth, configurationTapeWidth,
    FixedWidthCodec.prod, FixedWidthCodec.ofEquiv, FixedWidthCodec.word]

end Projections

end IPPSPACE

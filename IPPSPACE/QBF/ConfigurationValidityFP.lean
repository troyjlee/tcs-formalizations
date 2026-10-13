/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.OneHotFP
import IPPSPACE.QBF.MachineConfiguration

/-!
# Polynomial-time construction of full configuration validity

The exact validity formula follows the codec's nested products and tape rows.
Its one-hot state and head checks, unrestricted symbol checks, binary variable
names, and syntax tags are all constructed in upstream's actual `FP` class.
-/

namespace IPPSPACE

open Complexity

private theorem castWidth_formula {α : Type} {width v bound : ℕ}
    {codec : FixedWidthCodec α width} (valid : CodecValidity codec bound)
    (h : width = v) (names : Fin v → ℕ) :
    (valid.castWidth h).formula names = valid.formula (fun i => names (Fin.cast h i)) := by
  cases h
  rfl

private theorem qbfAllFin_val_eq_range (n : ℕ) (f : ℕ → QBF) :
    qbfAllFin n (fun i => f i.val) = qbfAll ((List.range n).map f) := by
  unfold qbfAllFin
  congr 1
  apply List.ext_get
  · simp
  · intro i hl hr
    simp

/-- Exact head/symbol validity syntax of one tape row. The symbol checks retain
one `tru` node per cell, as in the existing codec validity construction. -/
def tapeValiditySyntax (start cells : ℕ) : QBF :=
  .conj ((CodecValidity.fin cells).formula (blockNames start cells))
    (qbfAll ((List.range cells).map (fun _ => QBF.tru)))

theorem configurationValidityFormula_eq_blocks {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space start : ℕ) :
    configurationValidityFormula stateNumber symbolBits tapes inputLength space
      (blockNames start (configurationWidth states tapes inputLength space)) =
      .conj ((CodecValidity.fin states).formula (blockNames start states))
        (.conj ((CodecValidity.fin (inputLength + space + 2)).formula
          (blockNames (start + states) (inputLength + space + 2)))
          (.conj
            (qbfAll ((List.range tapes).map fun i => tapeValiditySyntax
              (start + states + (inputLength + space + 2) +
                (space + 1 + (space + 1) * 2) * i) (space + 1)))
            (tapeValiditySyntax
              (start + states + (inputLength + space + 2) +
                tapes * (space + 1 + (space + 1) * 2)) (space + 2)))) := by
  unfold configurationValidityFormula configurationValidity
  rw [castWidth_formula]
  simp only [tapeValiditySyntax]
  simp only [CodecValidity.prod, CodecValidity.ofEquiv, CodecValidity.vector,
    CodecValidity.word, Function.comp_def, blockNames, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd, Nat.add_assoc]
  congr 1
  congr 1
  · congr 1
    funext i
    simp [blockNames, Nat.add_assoc]
  · congr 1
    · rw [← qbfAllFin_val_eq_range]
      congr 1
      funext i
      congr 1
      · congr 1
        funext j
        dsimp [blockNames, finProdFinEquiv]
        ring
      · exact qbfAllFin_val_eq_range _ (fun _ => QBF.tru)
    · congr 1
      · congr 1
        funext j
        dsimp [blockNames]
        omega
      · exact qbfAllFin_val_eq_range _ (fun _ => QBF.tru)

theorem encode_tapeValiditySyntax_mem_FP {start cells : List Bool → ℕ}
    (hstart : UnaryFn start) (hcells : UnaryFn cells) :
    (fun z => encodeQBF (tapeValiditySyntax (start z) (cells z))) ∈ FP :=
  encodeQBF_conj_mem_FP (encode_finValidity_mem_FP hstart hcells)
    (encodeQBF_qbfAll_range_mem_FP hcells (constFn_mem_FP (encodeQBF .tru)))

/-- Construct the complete exact-image guard at a polynomial-time block offset.
The state and tape counts are fixed machine parameters. -/
theorem encode_configurationValidityFormula_mem_FP {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool)) (tapes : ℕ)
    {inputLength space start : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space) (hstart : UnaryFn start) :
    (fun z => encodeQBF (configurationValidityFormula stateNumber symbolBits tapes
      (inputLength z) (space z)
      (blockNames (start z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP := by
  have hinput := (hn.add hs).add (UnaryFn.const 2)
  have hwork := hs.add (UnaryFn.const 1)
  have houtput := hs.add (UnaryFn.const 2)
  have htapeWidth := hwork.add (hwork.mul (UnaryFn.const 2))
  have hheadStart := hstart.add (UnaryFn.const states)
  have hworkStart := hheadStart.add hinput
  have hrows := encodeQBF_qbfAll_range_mem_FP (count := fun _ => tapes)
    (body := fun z i => tapeValiditySyntax
      (start z + states + (inputLength z + space z + 2) +
        (space z + 1 + (space z + 1) * 2) * i) (space z + 1))
    (UnaryFn.const tapes)
    (encode_tapeValiditySyntax_mem_FP
      (hworkStart.lift.add (htapeWidth.lift.mul UnaryFn.index)) hwork.lift)
  have hout := encode_tapeValiditySyntax_mem_FP
    (hworkStart.add ((UnaryFn.const tapes).mul htapeWidth)) houtput
  have h := encodeQBF_conj_mem_FP (encode_finValidity_mem_FP hstart (UnaryFn.const states))
    (encodeQBF_conj_mem_FP (encode_finValidity_mem_FP hheadStart hinput)
      (encodeQBF_conj_mem_FP hrows hout))
  simpa only [configurationValidityFormula_eq_blocks] using h

end IPPSPACE

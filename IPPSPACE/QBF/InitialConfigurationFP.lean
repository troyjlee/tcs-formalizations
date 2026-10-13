/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineTransitionFP
import Complexitylib.Classes.P.StringAccess

/-!
# Polynomial-time output of the actual initial configuration

The initial code stores the initial control state, zero head positions, and the
start/blank work and output cells. Input contents are supplied by reconstruction,
so only their length appears in this finite code. The results below serialize
the exact existing Boolean codec and construct its fixed-source equality block.
-/

namespace IPPSPACE

open Complexity

private theorem ofFn_val_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_get
  · simp
  · intro i hleft hright
    simp

private theorem codec_castWidth_bits {α : Type} {w v : ℕ}
    (codec : FixedWidthCodec α w) (h : w = v) (a : α) :
    List.ofFn ((codec.castWidth h).encode a) = List.ofFn (codec.encode a) := by
  cases h
  rfl

private theorem codec_prod_bits {α β : Type} {w v : ℕ}
    (left : FixedWidthCodec α w) (right : FixedWidthCodec β v) (a : α) (b : β) :
    List.ofFn ((left.prod right).encode (a, b)) =
      List.ofFn (left.encode a) ++ List.ofFn (right.encode b) :=
  List.ofFn_fin_append _ _

private theorem codec_vector_bits {α : Type} {w : ℕ}
    (codec : FixedWidthCodec α w) (n : ℕ) (values : Fin n → α) :
    List.ofFn ((codec.vector n).encode values) =
      (List.ofFn (fun i => List.ofFn (codec.encode (values i)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hbound : i.val * w + j.val < n * w := by
    have hi := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    omega
  have hindex : (⟨i.val * w + j.val, hbound⟩ : Fin (n * w)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [hindex]
  exact FixedWidthCodec.vector_encode codec n values i j

/-- The exact one-hot string, also defined when its width is zero. -/
def initialOneHotBits (width hot : ℕ) : List Bool :=
  (List.range width).map (fun i => decide (hot = i))

private theorem codec_fin_bits {n : ℕ} (head : Fin n) :
    List.ofFn ((FixedWidthCodec.fin n).encode head) = initialOneHotBits n head.val := by
  change List.ofFn (fun i : Fin n => decide (head = i)) = _
  simp only [Fin.ext_iff]
  exact ofFn_val_eq_range n (fun i => decide (head.val = i))

/-- Head zero and the exact `Γ.start = 11`, `Γ.blank = 10` initial cells. -/
def initialTapeBits (cells : ℕ) : List Bool :=
  initialOneHotBits cells 0 ++ (List.range cells).flatMap (fun i => [true, decide (i = 0)])

private theorem initialSymbol_bits (index : ℕ) :
    List.ofFn (machineSymbolBits ((Tape.init []).cells index)) = [true, decide (index = 0)] := by
  by_cases h : index = 0
  · subst index
    rfl
  · simp [Tape.init, h, machineSymbolBits, encodeMachineSymbol, List.ofFn_succ]

set_option backward.isDefEq.respectTransparency false in
private theorem initialTape_codec_bits (space : ℕ) :
    List.ofFn (((FixedWidthCodec.fin (space + 1)).prod
      ((FixedWidthCodec.ofEquiv machineSymbolBits (FixedWidthCodec.word 2)).vector (space + 1))).encode
        ((⟨0, by omega⟩ : Fin (space + 1)), fun i => (Tape.init []).cells i.val)) =
      initialTapeBits (space + 1) := by
  rw [codec_prod_bits, codec_fin_bits, codec_vector_bits]
  simp only [FixedWidthCodec.ofEquiv, FixedWidthCodec.word, id_eq]
  simp only [initialSymbol_bits]
  rw [ofFn_val_eq_range (space + 1) (fun i => [true, decide (i = 0)])]
  rfl

/-- The actual codec's vector serialized in its original order. -/
def initialConfigurationBits {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) : List Bool :=
  List.ofFn (encodeMachineConfiguration stateNumber input.length space (tm.initCfg input))

set_option backward.isDefEq.respectTransparency false in
/-- Exact byte identity, including all width casts and zero-space/zero-tape
cases. The fixed input contents are not duplicated in the configuration code. -/
theorem initialConfigurationBits_eq {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    initialConfigurationBits tm stateNumber input space =
      initialOneHotBits states (stateNumber tm.qstart).val ++
        (initialOneHotBits (input.length + space + 2) 0 ++
          ((List.range tapes).flatMap (fun _ => initialTapeBits (space + 1)) ++
            initialTapeBits (space + 2))) := by
  unfold initialConfigurationBits encodeMachineConfiguration machineConfigurationCodec configurationCodec
  rw [codec_castWidth_bits]
  simp only [cfgCode, Tape.init_head, Nat.zero_min,
    codec_prod_bits, codec_vector_bits, codec_fin_bits, FixedWidthCodec.ofEquiv]
  simp only [FixedWidthCodec.word, id_eq, initialSymbol_bits]
  rw [ofFn_val_eq_range (space + 1) (fun i => [true, decide (i = 0)]),
    ofFn_val_eq_range (space + 2) (fun i => [true, decide (i = 0)])]
  change _ ++ (_ ++ ((List.ofFn (fun _ : Fin tapes => initialTapeBits (space + 1))).flatten ++
    initialTapeBits (space + 2))) = _
  rw [ofFn_val_eq_range tapes (fun _ => initialTapeBits (space + 1))]
  rfl

/-- Construct the exact one-hot string in polynomial time. -/
theorem initialOneHotBits_mem_FP {width hot : List Bool → ℕ}
    (hwidth : UnaryFn width) (hhot : UnaryFn hot) :
    (fun z => initialOneHotBits (width z) (hot z)) ∈ FP := by
  exact bitwise_mem_FP hwidth.mem_FP (FPPred.eq hhot.lift UnaryFn.index).flag_mem_FP
    (fun _ _ => by simp only [pairFst_pair, pairSnd_pair, List.length_replicate])

/-- The finite initial tape string is polynomial-time, with no positivity
precondition on its supplied number of cells. -/
theorem initialTapeBits_mem_FP {cells : List Bool → ℕ} (hcells : UnaryFn cells) :
    (fun z => initialTapeBits (cells z)) ∈ FP := by
  have hbit := (FPPred.eq UnaryFn.index (UnaryFn.const 0)).flag_mem_FP
  have hcell := Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hbit
  have hcells' : (fun z => (List.range (cells z)).flatMap
      (fun i => [true, decide (i = 0)])) ∈ FP := by
    simpa only [pairSnd_pair, List.length_replicate, List.cons_append, List.nil_append]
      using flatMap_range_mem_FP hcell hcells.mem_FP
  exact Cobham.appendFn_mem_FP (initialOneHotBits_mem_FP hcells (UnaryFn.const 0)) hcells'

/-- The exact codec output of the actual initial configuration is in upstream
`FP`, for an `FP` input string and a polynomial-time unary space budget. -/
theorem encode_initialConfigurationBits_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {input : List Bool → List Bool}
    {space : List Bool → ℕ} (hinput : input ∈ FP) (hspace : UnaryFn space) :
    (fun z => initialConfigurationBits tm stateNumber (input z) (space z)) ∈ FP := by
  have hhead := initialOneHotBits_mem_FP
    (((UnaryFn.length hinput).add hspace).add (UnaryFn.const 2)) (UnaryFn.const 0)
  have hwork := initialTapeBits_mem_FP (hspace.add (UnaryFn.const 1))
  have hworks : (fun z => (List.range tapes).flatMap
      (fun _ => initialTapeBits (space z + 1))) ∈ FP := by
    simpa only [Function.comp_apply, pairFst_pair, List.length_replicate] using
      flatMap_range_mem_FP (mem_FP_comp pairFst_mem_FP hwork) (UnaryFn.const tapes).mem_FP
  have hout := initialTapeBits_mem_FP (hspace.add (UnaryFn.const 2))
  have h := Cobham.appendFn_mem_FP
    (constFn_mem_FP (initialOneHotBits states (stateNumber tm.qstart).val))
    (Cobham.appendFn_mem_FP hhead (Cobham.appendFn_mem_FP hworks hout))
  exact mem_FP_of_eq h (fun z => (initialConfigurationBits_eq tm stateNumber (input z) (space z)).symm)

/-- A polynomial-time Boolean vector supplies the exact literal values of a
contiguous fixed-source block. Only bit lookup is used; no numeric value of the
whole vector is required. -/
theorem encodeQBF_blockValues_ofFn_mem_FP {start width : List Bool → ℕ}
    {values : (z : List Bool) → Fin (width z) → Bool}
    (hstart : UnaryFn start) (hwidth : UnaryFn width)
    (hbits : (fun z => List.ofFn (values z)) ∈ FP) :
    (fun z => encodeQBF (blockValues (blockNames (start z) (width z)) (values z))) ∈ FP := by
  have h := encodeQBF_blockValues_contiguous_mem_FP
    (values := fun z i => (List.ofFn (values z))[i]?.getD false) hstart hwidth
    (FPPred.getBit (mem_FP_comp pairFst_mem_FP hbits) UnaryFn.index)
  refine mem_FP_of_eq h (fun z => ?_)
  congr 2
  funext i
  simp

/-- Construct the actual initial-configuration equality block at any
polynomial-time starting variable. -/
theorem encode_initialConfigurationBlock_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {input : List Bool → List Bool}
    {space start : List Bool → ℕ} (hinput : input ∈ FP)
    (hspace : UnaryFn space) (hstart : UnaryFn start) :
    (fun z => encodeQBF (blockValues
      (blockNames (start z) (configurationWidth states tapes (input z).length (space z)))
      (encodeMachineConfiguration stateNumber (input z).length (space z)
        (tm.initCfg (input z))))) ∈ FP :=
  encodeQBF_blockValues_ofFn_mem_FP hstart
    (configurationWidth_unaryFn states tapes (UnaryFn.length hinput) hspace)
    (encode_initialConfigurationBits_mem_FP tm stateNumber hinput hspace)

end IPPSPACE

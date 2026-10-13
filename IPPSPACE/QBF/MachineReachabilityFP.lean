/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.InitialConfigurationFP
import IPPSPACE.QBF.ReachabilityFP
import IPPSPACE.Protocol.ResourceFP

/-!
# Polynomial-time construction of actual machine accepting reachability

The actual validity, transition, and acceptance formulas are constructed directly
at the named endpoint blocks of the existing succinct reachability formula. This
gives an unconditional upstream `FP` certificate and exact machine-acceptance
semantics under the existing reachable-configuration space bound. A universal
prefix over the polynomial name range closes the syntax, giving an `FP` encoding
of every actual `PSPACE` language into encoded closed true QBF. This does not
certify template renaming, `closeQBF`, or the prenex target `encodeMachineAcceptance`.
-/

namespace IPPSPACE

open Complexity

/-- The exact endpoint-validity guards and actual transition table, at arbitrary
supplied variable names. -/
def machineGuardedEdgeAt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (before after : Fin (configurationWidth states tapes input.length space) → ℕ) : QBF :=
  .conj (configurationValidityFormula stateNumber machineSymbolBits tapes input.length space before)
    (.conj (configurationValidityFormula stateNumber machineSymbolBits tapes input.length space after)
      (machineTransitionFormula tm stateNumber input space before after))

/-- Exact validity followed by the halt-state and accepting output-cell test. -/
def machineGuardedAcceptanceAt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  .conj (configurationValidityFormula stateNumber machineSymbolBits tapes inputLength space names)
    (machineAcceptanceFormula stateNumber tm.qhalt tapes inputLength space names)

theorem machineGuardedEdgeAt_base {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    machineGuardedEdgeAt tm stateNumber input space Fin.val
      (fun i => configurationWidth states tapes input.length space + i.val) =
      machineGuardedEdge tm stateNumber input space := rfl

theorem machineGuardedAcceptanceAt_base {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ) :
    machineGuardedAcceptanceAt tm stateNumber inputLength space Fin.val =
      machineGuardedAcceptance tm stateNumber inputLength space := rfl

theorem eval_machineGuardedEdgeAt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (before after : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) :
    (machineGuardedEdgeAt tm stateNumber input space before after).eval assignment = true ↔
      (machineConfigurationCodec stateNumber tapes input.length space).liftRelation
        (machineCodeEdge tm input space) (assignment ∘ before) (assignment ∘ after) := by
  simp only [machineGuardedEdgeAt, QBF.eval_conj, Bool.and_eq_true,
    eval_configurationValidityFormula, FixedWidthCodec.liftRelation_iff]
  constructor
  · rintro ⟨⟨source, hsource⟩, ⟨target, htarget⟩, hstep⟩
    refine ⟨source, target, hsource, htarget, ?_⟩
    exact (machineCodeStep_eq_some_iff tm input space source target).mpr
      ((eval_machineTransitionFormula tm stateNumber input space before after assignment
        source target hsource.symm htarget.symm).mp hstep)
  · rintro ⟨source, target, hsource, htarget, hstep⟩
    refine ⟨⟨source, hsource⟩, ⟨target, htarget⟩, ?_⟩
    exact (eval_machineTransitionFormula tm stateNumber input space before after assignment
      source target hsource.symm htarget.symm).mpr
      ((machineCodeStep_eq_some_iff tm input space source target).mp hstep)

theorem eval_machineGuardedAcceptanceAt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) :
    (machineGuardedAcceptanceAt tm stateNumber input.length space names).eval assignment = true ↔
      (machineConfigurationCodec stateNumber tapes input.length space).liftPredicate
        (machineCodeAccepts tm input space) (assignment ∘ names) := by
  have hlocal (code : Code tm.Q tapes input.length space)
      (hcode : (machineConfigurationCodec stateNumber tapes input.length space).encode code =
        assignment ∘ names) :
      (machineAcceptanceFormula stateNumber tm.qhalt tapes input.length space names).eval assignment =
        true ↔ machineCodeAccepts tm input space code := by
    have h := eval_configurationAcceptanceFormula stateNumber machineSymbolBits tm.qhalt Γ.one
      tapes input.length space names code assignment (fun i => congrFun hcode.symm i)
    simpa only [machineAcceptanceFormula, machineCodeAccepts, TM.halted,
      machineConfigurationOfCode, machineTapeOfCode, configurationVerdictCell,
      dite_eq_left (show 1 < space + 2 by omega)] using h
  simp only [machineGuardedAcceptanceAt, QBF.eval_conj, Bool.and_eq_true,
    eval_configurationValidityFormula, FixedWidthCodec.liftPredicate_iff]
  constructor
  · rintro ⟨⟨code, hcode⟩, haccept⟩
    exact ⟨code, hcode, (hlocal code hcode).mp haccept⟩
  · rintro ⟨code, hcode, haccept⟩
    exact ⟨⟨code, hcode⟩, (hlocal code hcode).mpr haccept⟩

theorem encode_machineGuardedEdgeAt_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {input : List Bool → List Bool}
    {space beforeStart afterStart : List Bool → ℕ} (hinput : input ∈ FP)
    (hs : UnaryFn space) (hb : UnaryFn beforeStart) (ha : UnaryFn afterStart) :
    (fun z => encodeQBF (machineGuardedEdgeAt tm stateNumber (input z) (space z)
      (blockNames (beforeStart z) (configurationWidth states tapes (input z).length (space z)))
      (blockNames (afterStart z) (configurationWidth states tapes (input z).length (space z))))) ∈ FP :=
  encodeQBF_conj_mem_FP
    (encode_configurationValidityFormula_mem_FP stateNumber machineSymbolBits tapes
      (UnaryFn.length hinput) hs hb)
    (encodeQBF_conj_mem_FP
      (encode_configurationValidityFormula_mem_FP stateNumber machineSymbolBits tapes
        (UnaryFn.length hinput) hs ha)
      (encode_machineTransitionFormula_mem_FP tm stateNumber hinput hs hb ha))

theorem encode_machineGuardedAcceptanceAt_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {inputLength space start : List Bool → ℕ}
    (hn : UnaryFn inputLength) (hs : UnaryFn space) (hstart : UnaryFn start) :
    (fun z => encodeQBF (machineGuardedAcceptanceAt tm stateNumber (inputLength z) (space z)
      (blockNames (start z) (configurationWidth states tapes (inputLength z) (space z))))) ∈ FP :=
  encodeQBF_conj_mem_FP
    (encode_configurationValidityFormula_mem_FP stateNumber machineSymbolBits tapes hn hs hstart)
    (encode_machineAcceptanceFormula_mem_FP stateNumber tm.qhalt tapes hn hs hstart)

/-- The existing succinct accepting-reachability construction, using the actual
machine formulas directly at each configuration block and its actual initial code. -/
def machineReachabilityFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) : QBF :=
  acceptingReachFormula (configurationWidth states tapes input.length space)
    (machineGuardedEdgeAt tm stateNumber input space)
    (machineGuardedAcceptanceAt tm stateNumber input.length space)
    (encodeMachineConfiguration stateNumber input.length space (tm.initCfg input))

/-- Complete construction of this exact machine reachability syntax is in the
actual upstream `FP`. No renaming, transition, or acceptance runtime premise remains. -/
theorem encode_machineReachabilityFormula_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {input : List Bool → List Bool}
    {space : List Bool → ℕ} (hinput : input ∈ FP) (hs : UnaryFn space) :
    (fun z => encodeQBF (machineReachabilityFormula tm stateNumber (input z) (space z))) ∈ FP := by
  have hw := configurationWidth_unaryFn states tapes (UnaryFn.length hinput) hs
  have hleft := (UnaryFn.const 3).mul (hw.pow_const 2)
  exact encode_acceptingReachFormula_mem_FP
    (fun z => machineGuardedEdgeAt tm stateNumber (input z) (space z))
    (fun z => machineGuardedAcceptanceAt tm stateNumber (input z).length (space z))
    (fun z => encodeMachineConfiguration stateNumber (input z).length (space z) (tm.initCfg (input z)))
    hw (encode_initialConfigurationBlock_mem_FP tm stateNumber hinput hs (UnaryFn.const 0))
    (encode_machineGuardedAcceptanceAt_mem_FP tm stateNumber (UnaryFn.length hinput) hs hw)
    (encode_machineGuardedEdgeAt_mem_FP tm stateNumber hinput hs hleft (hleft.add hw))

/-- Evaluation is independent of the external assignment and is exactly actual
machine acceptance, provided all reachable configurations satisfy the space bound. -/
theorem eval_machineReachabilityFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (hspace : ∀ c, tm.reaches (tm.initCfg input) c → c.WithinDecisionSpace input.length space)
    (assignment : ℕ → Bool) :
    (machineReachabilityFormula tm stateNumber input space).eval assignment = true ↔
      tm.Accepts input := by
  rw [machineReachabilityFormula, eval_acceptingReachFormula _ _ _
    (eval_machineGuardedEdgeAt tm stateNumber input space) _ _
    (eval_machineGuardedAcceptanceAt tm stateNumber input space)]
  change (∃ target, _ ∧ Relation.ReflTransGen _
    ((machineConfigurationCodec stateNumber tapes input.length space).encode
      (cfgCode input.length space (tm.initCfg input))) target) ↔ _
  rw [FixedWidthCodec.liftRelation_accepting_reachable_iff]
  exact machineCode_accepts_iff tm input space hspace

/-- The same semantic statement under upstream's actual space-decider contract. -/
theorem machine_decider_reachability_iff {states tapes : ℕ} {tm : TM tapes}
    (stateNumber : tm.Q ≃ Fin states) {language : Language} {space : ℕ → ℕ}
    (hdec : tm.DecidesInSpace language space) (input : List Bool) :
    (machineReachabilityFormula tm stateNumber input (space input.length)).IsTrue ↔
      input ∈ language :=
  (eval_machineReachabilityFormula tm stateNumber input _ (hdec.1 input) _).trans
    (machine_decider_accepts_iff hdec input)

/-- Direct machine guards introduce only the supplied endpoint names. -/
theorem qbfNames_machineGuardedEdgeAt_lt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (before after : Fin (configurationWidth states tapes input.length space) → ℕ)
    (B : ℕ) (hb : ∀ j, before j < B) (ha : ∀ j, after j < B) :
    ∀ i ∈ qbfNames (machineGuardedEdgeAt tm stateNumber input space before after), i < B := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact qbfNames_configurationValidityFormula_lt stateNumber machineSymbolBits tapes
      input.length space before B hb i hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_configurationValidityFormula_lt stateNumber machineSymbolBits tapes
        input.length space after B ha i hi
    · rcases mem_qbfNames_machineTransitionFormula tm stateNumber input space before after hi with
        ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact hb j
      · exact ha j

theorem qbfNames_machineGuardedAcceptanceAt_lt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (B : ℕ) (hn : ∀ j, names j < B) :
    ∀ i ∈ qbfNames (machineGuardedAcceptanceAt tm stateNumber inputLength space names), i < B := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact qbfNames_configurationValidityFormula_lt stateNumber machineSymbolBits tapes
      inputLength space names B hn i hi
  · obtain ⟨j, rfl⟩ := configurationAcceptanceFormula_names stateNumber machineSymbolBits
      tm.qhalt Γ.one tapes inputLength space names i hi
    exact hn j

/-- The direct formula has exactly the same polynomial name-range budget as
the existing template-based construction. -/
theorem qbfNames_machineReachabilityFormula_lt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    ∀ i ∈ qbfNames (machineReachabilityFormula tm stateNumber input space),
      i < reachabilityNameBudget (configurationWidth states tapes input.length space) := by
  let width := configurationWidth states tapes input.length space
  have hreach := qbfNames_reachFormula_lt width
    (stutterFormula width (machineGuardedEdgeAt tm stateNumber input space))
    (qbfNames_stutterFormula_lt width _
      (qbfNames_machineGuardedEdgeAt_lt tm stateNumber input space))
    width (2 * width) (blockNames 0 width) (blockNames width width)
    (blockNames_lt_of_le _ _ _ (by omega)) (blockNames_lt_of_le _ _ _ (by omega))
  change ∀ i ∈ qbfNames (acceptingReachFormula width _ _ _),
    i < 2 * width + 3 * width * width
  unfold acceptingReachFormula
  apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
  apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact qbfNames_blockValues_lt _ _ _ (blockNames_lt_of_le _ _ _ (by omega)) i hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_machineGuardedAcceptanceAt_lt tm stateNumber input.length space _ _
        (blockNames_lt_of_le _ _ _ (by omega)) i hi
    · exact hreach i hi

/-- Universal binding of a contiguous range removes exactly its free names. -/
theorem mem_freeVars_forallBlock (start width : ℕ) (formula : QBF) (i : ℕ) :
    i ∈ (forallBlock start width formula).freeVars ↔
      i ∈ formula.freeVars ∧ (i < start ∨ start + width ≤ i) := by
  induction width generalizing start with
  | zero =>
    simp only [forallBlock, Nat.add_zero]
    have horder : i < start ∨ start ≤ i := by omega
    simp only [horder, and_true]
  | succ width ih =>
    simp only [forallBlock, QBF.freeVars, Finset.mem_sdiff, Finset.mem_singleton, ih]
    by_cases hfree : i ∈ formula.freeVars <;> simp only [hfree, true_and, false_and]
    · omega

/-- Binding every name below a known upper bound closes the formula, without
requiring computation of its free-variable set. -/
theorem forallBlock_closed_of_name_bound (formula : QBF) (B : ℕ)
    (h : ∀ i ∈ qbfNames formula, i < B) : (forallBlock 0 B formula).Closed := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  obtain ⟨hfree, houtside⟩ := (mem_freeVars_forallBlock 0 B formula i).mp hi
  have hbound := h i (freeVars_subset_qbfNames formula hfree)
  omega

/-- A closed, generally non-prenex QBF for actual machine acceptance. The
explicit polynomial binder range has its own construction-time certificate. -/
def closedMachineReachabilityFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) : QBF :=
  forallBlock 0 (reachabilityNameBudget (configurationWidth states tapes input.length space))
    (machineReachabilityFormula tm stateNumber input space)

theorem closedMachineReachabilityFormula_closed {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    (closedMachineReachabilityFormula tm stateNumber input space).Closed :=
  forallBlock_closed_of_name_bound _ _
    (qbfNames_machineReachabilityFormula_lt tm stateNumber input space)

theorem encode_closedMachineReachabilityFormula_mem_FP {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) {input : List Bool → List Bool}
    {space : List Bool → ℕ} (hinput : input ∈ FP) (hs : UnaryFn space) :
    (fun z => encodeQBF (closedMachineReachabilityFormula tm stateNumber (input z) (space z))) ∈ FP := by
  have hw := configurationWidth_unaryFn states tapes (UnaryFn.length hinput) hs
  exact encodeQBF_forallBlock_mem_FP (UnaryFn.const 0)
    (((UnaryFn.const 2).mul hw).add (((UnaryFn.const 3).mul hw).mul hw))
    (encode_machineReachabilityFormula_mem_FP tm stateNumber hinput hs)

theorem eval_closedMachineReachabilityFormula {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (hspace : ∀ c, tm.reaches (tm.initCfg input) c → c.WithinDecisionSpace input.length space)
    (assignment : ℕ → Bool) :
    (closedMachineReachabilityFormula tm stateNumber input space).eval assignment = true ↔
      tm.Accepts input := by
  simp only [closedMachineReachabilityFormula, eval_forallBlock,
    eval_machineReachabilityFormula tm stateNumber input space hspace, forall_const]

/-- Exact language preservation for the new closed constructor. -/
theorem encodedTrueQBF_closedMachineReachability_iff {states tapes : ℕ} {tm : TM tapes}
    (stateNumber : tm.Q ≃ Fin states) {language : Language} {space : ℕ → ℕ}
    (hdec : tm.DecidesInSpace language space) (input : List Bool) :
    EncodedTrueQBF (encodeQBF (closedMachineReachabilityFormula tm stateNumber input
      (space input.length))) ↔ input ∈ language := by
  rw [encodedTrueQBF_encode_iff]
  have hclosed := closedMachineReachabilityFormula_closed tm stateNumber input (space input.length)
  simp only [hclosed, true_and, QBF.IsTrue]
  exact (eval_closedMachineReachabilityFormula tm stateNumber input _ (hdec.1 input) _).trans
    (machine_decider_accepts_iff hdec input)

/-- Every language in actual upstream `PSPACE` has a genuine upstream `FP`
many-one encoding into canonical closed true QBF. This target allows arbitrary
quantifier shape; no prenex conversion runtime is assumed. -/
theorem pspace_has_FP_closedQBF_encoding {language : Language}
    (hlanguage : language ∈ PSPACE) :
    ∃ encode : List Bool → List Bool, encode ∈ FP ∧
      ∀ input, EncodedTrueQBF (encode input) ↔ input ∈ language := by
  obtain ⟨tapes, tm, space, hdec⟩ := (pspace_iff_exists_polynomial_space language).mp hlanguage
  let stateNumber := Fintype.equivFin tm.Q
  have hid : (fun input : List Bool => input) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (mem_FP_pairWithInput (constFn_mem_FP [])) pairSnd_mem_FP)
      (fun input => by simp)
  refine ⟨(fun input => encodeQBF
    (closedMachineReachabilityFormula tm stateNumber input (space.eval input.length))), ?_, ?_⟩
  · exact encode_closedMachineReachabilityFormula_mem_FP tm stateNumber hid
      (polynomial_eval_length_unaryFn space)
  · intro input
    exact encodedTrueQBF_closedMachineReachability_iff (states := Fintype.card tm.Q)
      (tapes := tapes) (tm := tm) (language := language) (space := fun n => space.eval n)
      stateNumber hdec input

end IPPSPACE

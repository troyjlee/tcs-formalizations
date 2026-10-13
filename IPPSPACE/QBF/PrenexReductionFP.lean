/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexMachineFP
import IPPSPACE.QBF.PrenexParsingFP
import IPPSPACE.QBF.MachineReachabilityFP

/-!
# Polynomial-time reduction to closed prenex syntax

The original converter preserves the exact set of free variables. Its certified
binary implementation therefore lets closed-prenex recognition implement the
original reduction's source-closedness guard, including all malformed inputs.
-/

namespace IPPSPACE

open Complexity

/-- Free source occurrences survive in the converter's matrix. Their names
may be renamed by the lexical environment, but are never discarded. -/
theorem mem_freeVars_prenexAux_matrix (formula : QBF) (env : ℕ → ℕ) (start : ℕ)
    (h : ∀ i ∈ qbfNames formula, env i < start) :
    ∀ i ∈ formula.freeVars,
      env i ∈ (prenexAux formula env start h).formula.matrix.freeVars := by
  induction formula generalizing env start with
  | var name =>
    intro i hi
    have heq : i = name := by simpa [QBF.freeVars] using hi
    subst i
    simp [prenexAux, PrenexResult.quantifierFree, renameQBF, QBF.freeVars]
  | tru => simp [QBF.freeVars]
  | fls => simp [QBF.freeVars]
  | neg child ih =>
    intro i hi
    exact ih env start h i hi
  | conj left right ihleft ihright =>
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (ihleft env start _ i hi)
    · exact Finset.mem_union_right _ (ihright env _ _ i hi)
  | disj left right ihleft ihright =>
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (ihleft env start _ i hi)
    · exact Finset.mem_union_right _ (ihright env _ _ i hi)
  | ex name child ih =>
    intro i hi
    obtain ⟨hi, hne⟩ := Finset.mem_sdiff.mp hi
    have hne' : i ≠ name := by simpa using hne
    simpa only [prenexAux, PrenexResult.quantify, Function.update_of_ne hne'] using
      ih (Function.update env name start) (start + 1) _ i hi
  | all name child ih =>
    intro i hi
    obtain ⟨hi, hne⟩ := Finset.mem_sdiff.mp hi
    have hne' : i ≠ name := by simpa using hne
    simpa only [prenexAux, PrenexResult.quantify, Function.update_of_ne hne'] using
      ih (Function.update env name start) (start + 1) _ i hi

/-- Fresh prefix binders cannot capture any renamed free source variable. -/
theorem mem_freeVars_prenexAux (formula : QBF) (env : ℕ → ℕ) (start : ℕ)
    (h : ∀ i ∈ qbfNames formula, env i < start) (i : ℕ) (hi : i ∈ formula.freeVars) :
    env i ∈ (prenexAux formula env start h).formula.toQBF.freeVars := by
  apply (mem_freeVars_prefixQBF _ _ _).mpr
  refine ⟨mem_freeVars_prenexAux_matrix formula env start h i hi, ?_⟩
  intro q hq heq
  have hlow := h i (freeVars_subset_qbfNames formula hi)
  have hhigh := ((prenexAux formula env start h).prefix_range q hq).1
  omega

/-- Capture-safe prenex conversion preserves syntactic free-variable names in
both directions, even when names are arbitrarily large binary numbers. -/
@[simp] theorem freeVars_toPrenex (formula : QBF) :
    (toPrenex formula).toQBF.freeVars = formula.freeVars := by
  apply Finset.Subset.antisymm (freeVars_toPrenex_subset formula)
  intro i hi
  exact mem_freeVars_prenexAux formula id (qbfMaxVar formula + 1) _ i hi

@[simp] theorem toPrenex_closed_iff (formula : QBF) :
    (toPrenex formula).toQBF.Closed ↔ formula.Closed := by
  simp [QBF.Closed]

@[simp] theorem decodeClosedPrenex_encode_isSome (formula : PrenexQBF) :
    (decodeClosedPrenex (encodeQBF formula.toQBF)).isSome = true ↔ formula.toQBF.Closed := by
  simp only [decodeClosedPrenex, decodePrenex_encode, Option.bind_eq_bind, Option.bind_some]
  split <;> simp_all [QBF.Closed]

@[simp] theorem decodeClosedPrenex_toPrenex_isSome (formula : QBF) :
    (decodeClosedPrenex (encodeQBF (toPrenex formula).toQBF)).isSome = true ↔ formula.Closed := by
  rw [decodeClosedPrenex_encode_isSome, toPrenex_closed_iff]

/-- The converted closedness test reproduces exactly the original source guard.
The separate full-decoding test rejects malformed input before any fallback can
become a target-language member. -/
theorem prenexReduction_eq_guarded_converter (bits : List Bool) :
    prenexReduction bits =
      if (decodeQBF bits).isSome = true ∧
          (decodeClosedPrenex (encodeQBF (toPrenex ((decodeQBF bits).getD .fls)).toQBF)).isSome = true
      then encodeQBF (toPrenex ((decodeQBF bits).getD .fls)).toQBF else [] := by
  cases hd : decodeQBF bits with
  | none => simp [prenexReduction, hd]
  | some formula =>
    simp only [prenexReduction, hd, Option.isSome_some, Option.getD_some, true_and]
    by_cases hc : formula.Closed
    · have ht := (decodeClosedPrenex_toPrenex_isSome formula).mpr hc
      simp [show formula.freeVars = ∅ from hc, ht]
    · have ht : (decodeClosedPrenex (encodeQBF (toPrenex formula).toQBF)).isSome ≠ true :=
        fun h => hc ((decodeClosedPrenex_toPrenex_isSome formula).mp h)
      simp [show formula.freeVars ≠ ∅ from hc, ht]

/-- Syntactic closedness of an FP-produced QBF is recognizable in actual FP,
without unary bounds on any variable name. -/
theorem qbfClosed_fppred {formula : List Bool → QBF}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) :
    FPPred fun z => (formula z).Closed :=
  (decodeClosedPrenex_success_fppred (encode_toPrenex_mem_FP hformula)).of_iff
    (fun z => decodeClosedPrenex_toPrenex_isSome (formula z))

/-- The existing total reduction is polynomial-time on arbitrary input strings,
with exactly its original malformed/open-input rejection behavior. -/
theorem prenexReduction_comp_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => prenexReduction (bits z)) ∈ FP := by
  have hconverted := encode_toPrenex_mem_FP (encode_decodeQBF_getD_mem_FP .fls hbits)
  have hguard := (decodeQBF_success_fppred hbits).and
    (decodeClosedPrenex_success_fppred hconverted)
  exact mem_FP_of_eq (hguard.ite_mem_FP hconverted (constFn_mem_FP []))
    (fun z => (prenexReduction_eq_guarded_converter (bits z)).symm)

theorem prenexReduction_mem_FP : prenexReduction ∈ FP :=
  prenexReduction_comp_mem_FP (CobhamFP_subset_FP (Cobham.proj 0))

/-- An actual polynomial-time many-one map from closed true QBF encodings to
closed true prenex encodings, stated with the concrete original transformation. -/
theorem prenexReduction_polynomial_reduction :
    prenexReduction ∈ FP ∧
      ∀ input, EncodedTrueQBF input ↔ EncodedTruePrenex (prenexReduction input) :=
  ⟨prenexReduction_mem_FP, encodedTrueQBF_iff_prenexReduction⟩

/-- Every language in the actual upstream PSPACE class has an actual upstream
FP many-one encoding into canonical closed true prenex QBF. -/
theorem pspace_has_FP_prenex_encoding {language : Language} (hlanguage : language ∈ PSPACE) :
    ∃ encode : List Bool → List Bool, encode ∈ FP ∧
      ∀ input, EncodedTruePrenex (encode input) ↔ input ∈ language := by
  obtain ⟨encode, hencode, hcorrect⟩ := pspace_has_FP_closedQBF_encoding hlanguage
  refine ⟨fun input => prenexReduction (encode input), prenexReduction_comp_mem_FP hencode, ?_⟩
  intro input
  exact (encodedTrueQBF_iff_prenexReduction (encode input)).symm.trans (hcorrect input)

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.ReducedQBF
import IPPSPACE.QBF.Syntax

/-!
# Syntactic control of polynomial variables

Both arithmetizations use only free variables of the input formula. Combined
with the executable `freeVarList`, this permits degree reduction without
computing the support of an expanded polynomial.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial Complexity

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

theorem vars_one_sub_subset (p : MvPolynomial σ R) : (1 - p).vars ⊆ p.vars := by
  simpa only [vars_one, Finset.empty_union] using
    (vars_sub_subset (p := (1 : MvPolynomial σ R)) (q := p))

theorem vars_or_subset (p q : MvPolynomial σ R) :
    (1 - (1 - p) * (1 - q)).vars ⊆ p.vars ∪ q.vars :=
  (vars_one_sub_subset _).trans ((vars_mul _ _).trans
    (Finset.union_subset_union (vars_one_sub_subset p) (vars_one_sub_subset q)))

theorem vars_forall_subset [Nontrivial R] (i : σ) (p : MvPolynomial σ R) :
    (restrict i 0 p * restrict i 1 p).vars ⊆ p.vars.erase i :=
  (vars_mul _ _).trans (Finset.union_subset
    (vars_restrict_subset i 0 p) (vars_restrict_subset i 1 p))

theorem vars_exists_subset [Nontrivial R] (i : σ) (p : MvPolynomial σ R) :
    (1 - (1 - restrict i 0 p) * (1 - restrict i 1 p)).vars ⊆ p.vars.erase i :=
  (vars_or_subset _ _).trans (Finset.union_subset
    (vars_restrict_subset i 0 p) (vars_restrict_subset i 1 p))

/-- The naive translation contains only variables free in the QBF. -/
theorem vars_arithmetize_subset_freeVars [Nontrivial R] (φ : QBF) :
    (arithmetize (R := R) φ).vars ⊆ φ.freeVars := by
  induction φ with
  | var i => simp [arithmetize, QBF.freeVars]
  | tru => simp [arithmetize, QBF.freeVars]
  | fls => simp [arithmetize, QBF.freeVars]
  | neg φ ih => exact (vars_one_sub_subset _).trans ih
  | conj φ ψ ihφ ihψ =>
    exact (vars_mul _ _).trans (Finset.union_subset_union ihφ ihψ)
  | disj φ ψ ihφ ihψ =>
    exact (vars_or_subset _ _).trans (Finset.union_subset_union ihφ ihψ)
  | ex i φ ih =>
    simpa [arithmetize, QBF.freeVars, Finset.erase_eq] using
      (vars_exists_subset i (arithmetize (R := R) φ)).trans (Finset.erase_subset_erase i ih)
  | all i φ ih =>
    simpa [arithmetize, QBF.freeVars, Finset.erase_eq] using
      (vars_forall_subset i (arithmetize (R := R) φ)).trans (Finset.erase_subset_erase i ih)

/-- Degree reduction also introduces no variables outside the syntactic free set. -/
theorem vars_reducedArithmetize_subset_freeVars [Nontrivial R] (φ : QBF) :
    (reducedArithmetize (R := R) φ).vars ⊆ φ.freeVars := by
  induction φ with
  | var i =>
    simpa [reducedArithmetize, QBF.freeVars] using
      vars_multilinearize_subset (X i : MvPolynomial ℕ R)
  | tru =>
    simpa [reducedArithmetize, QBF.freeVars] using
      vars_multilinearize_subset (1 : MvPolynomial ℕ R)
  | fls =>
    simpa [reducedArithmetize, QBF.freeVars] using
      vars_multilinearize_subset (0 : MvPolynomial ℕ R)
  | neg φ ih => exact (vars_multilinearize_subset _).trans ((vars_one_sub_subset _).trans ih)
  | conj φ ψ ihφ ihψ =>
    exact (vars_multilinearize_subset _).trans
      ((vars_mul _ _).trans (Finset.union_subset_union ihφ ihψ))
  | disj φ ψ ihφ ihψ =>
    exact (vars_multilinearize_subset _).trans
      ((vars_or_subset _ _).trans (Finset.union_subset_union ihφ ihψ))
  | ex i φ ih =>
    simpa [reducedArithmetize, QBF.freeVars, Finset.erase_eq] using
      (vars_multilinearize_subset _).trans
        ((vars_exists_subset i (reducedArithmetize (R := R) φ)).trans
          (Finset.erase_subset_erase i ih))
  | all i φ ih =>
    simpa [reducedArithmetize, QBF.freeVars, Finset.erase_eq] using
      (vars_multilinearize_subset _).trans
        ((vars_forall_subset i (reducedArithmetize (R := R) φ)).trans
          (Finset.erase_subset_erase i ih))

/-- A formula's syntactic free-variable list covers its polynomial variables. -/
theorem arithmetize_vars_mem_freeVarList [Nontrivial R] (φ : QBF) (i : ℕ)
    (hi : i ∈ (arithmetize (R := R) φ).vars) : i ∈ freeVarList φ :=
  (mem_freeVarList i φ).mpr (vars_arithmetize_subset_freeVars φ hi)

/-- A quantifier-free matrix has individual degree bounded by its syntax size. -/
theorem degreeOf_arithmetize_quantifierFree_le [Nontrivial R] (φ : QBF)
    (hφ : φ.QuantifierFree) (i : ℕ) :
    (arithmetize (R := R) φ).degreeOf i ≤ nodeCount φ := by
  induction φ with
  | var j => simp [arithmetize, nodeCount, degreeOf_X]; split <;> decide
  | tru => simp [arithmetize, nodeCount]
  | fls => simp [arithmetize, nodeCount]
  | neg φ ih =>
    exact ((degreeOf_one_sub_le i _).trans (ih hφ)).trans (Nat.le_add_right _ 1)
  | conj φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := QBF.quantifierFree_conj.mp hφ
    exact ((degreeOf_mul_le i _ _).trans (Nat.add_le_add (ihφ hφ) (ihψ hψ))).trans
      (Nat.le_add_right _ 1)
  | disj φ ψ ihφ ihψ =>
    have hs : φ.QuantifierFree ∧ ψ.QuantifierFree := by
      simpa [QBF.QuantifierFree, QBF.quantDepth] using hφ
    exact ((degreeOf_or_le i _ _).trans (Nat.add_le_add (ihφ hs.1) (ihψ hs.2))).trans
      (Nat.le_add_right _ 1)
  | ex j φ _ => simp [QBF.QuantifierFree, QBF.quantDepth] at hφ
  | all j φ _ => simp [QBF.QuantifierFree, QBF.quantDepth] at hφ

end IPPSPACE

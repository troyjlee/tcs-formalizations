/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Linearization
import Mathlib.Data.List.Perm.Basic

/-!
# Repeated coordinate linearization

An arbitrary list of coordinates can be reduced, including repetitions. Every
processed coordinate has degree at most one; untouched coordinates keep their
previous bounds. The order does not matter and repeating the list has no effect.
Linearizing the finite set of variables of a polynomial gives a multilinear
polynomial with the same Boolean-cube evaluations.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

/-- Composition of coordinate linearizations, with the head acting outermost. -/
def linearizeMany : List σ → MvPolynomial σ R → MvPolynomial σ R
  | [], p => p
  | i :: is, p => linearize i (linearizeMany is p)

@[simp] theorem linearizeMany_nil (p : MvPolynomial σ R) : linearizeMany [] p = p := rfl

@[simp] theorem linearizeMany_cons (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    linearizeMany (i :: is) p = linearize i (linearizeMany is p) := rfl

theorem linearizeMany_append (is js : List σ) (p : MvPolynomial σ R) :
    linearizeMany (is ++ js) p = linearizeMany is (linearizeMany js p) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, linearizeMany_cons, ih]

/-- It suffices for the processed coordinates of the evaluation point to be Boolean. -/
theorem eval_linearizeMany (is : List σ) (x : σ → R) (p : MvPolynomial σ R)
    (hx : ∀ i ∈ is, x i = 0 ∨ x i = 1) : eval x (linearizeMany is p) = eval x p := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [linearizeMany_cons, eval_linearize_of_bool x i _ (hx i (by simp))]
    exact ih (fun j hj => hx j (by simp [hj]))

/-- A variable omitted from the list never gains degree. -/
theorem degreeOf_linearizeMany_of_not_mem [Nontrivial R] (is : List σ)
    (j : σ) (p : MvPolynomial σ R) (hj : j ∉ is) :
    (linearizeMany is p).degreeOf j ≤ p.degreeOf j := by
  induction is with
  | nil => exact le_rfl
  | cons i is ih =>
    have hji : j ≠ i := fun h => hj (by simp [h])
    have hjs : j ∉ is := fun h => hj (by simp [h])
    exact (degreeOf_linearize_of_ne i j _ hji).trans (ih hjs)

/-- Every processed coordinate has degree at most one, regardless of repetitions. -/
theorem degreeOf_linearizeMany_of_mem [Nontrivial R] (is : List σ)
    (j : σ) (p : MvPolynomial σ R) (hj : j ∈ is) :
    (linearizeMany is p).degreeOf j ≤ 1 := by
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    by_cases hji : j = i
    · subst j
      exact degreeOf_linearize_self i _
    · exact (degreeOf_linearize_of_ne i j _ hji).trans (ih (by simpa [hji] using hj))

/-- A uniform bound of at least one survives every partial reduction list. -/
theorem degreeOf_linearizeMany_le [Nontrivial R] (is : List σ)
    (j : σ) (p : MvPolynomial σ R) {d : ℕ} (hd : 1 ≤ d) (hp : p.degreeOf j ≤ d) :
    (linearizeMany is p).degreeOf j ≤ d := by
  by_cases hj : j ∈ is
  · exact (degreeOf_linearizeMany_of_mem is j p hj).trans hd
  · exact (degreeOf_linearizeMany_of_not_mem is j p hj).trans hp

/-- Adding one more coordinate reduction commutes with a whole list. -/
theorem linearizeMany_linearize (is : List σ) (i : σ) (p : MvPolynomial σ R) :
    linearizeMany is (linearize i p) = linearize i (linearizeMany is p) := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [linearizeMany_cons, ih]
    exact linearize_comm j i _

/-- Reducing a coordinate already in the list makes no further change. -/
theorem linearize_linearizeMany_of_mem (is : List σ) (i : σ)
    (p : MvPolynomial σ R) (hi : i ∈ is) :
    linearize i (linearizeMany is p) = linearizeMany is p := by
  induction is with
  | nil => simp at hi
  | cons j is ih =>
    rcases List.mem_cons.mp hi with h | h
    · subst j
      exact linearize_idempotent i _
    · simp only [linearizeMany_cons]
      rw [linearize_comm, ih h]

theorem linearizeMany_eq_self_of_fixed (is : List σ) (p : MvPolynomial σ R)
    (hp : ∀ i ∈ is, linearize i p = p) : linearizeMany is p = p := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [linearizeMany_cons, ih (fun j hj => hp j (by simp [hj]))]
    exact hp i (by simp)

/-- Running the same reduction list twice has exactly the same result. -/
@[simp] theorem linearizeMany_idempotent (is : List σ) (p : MvPolynomial σ R) :
    linearizeMany is (linearizeMany is p) = linearizeMany is p :=
  linearizeMany_eq_self_of_fixed is _ (fun i hi => linearize_linearizeMany_of_mem is i p hi)

/-- Permuting the reduction list does not change the resulting polynomial. -/
theorem linearizeMany_eq_of_perm {is js : List σ} (h : is.Perm js)
    (p : MvPolynomial σ R) : linearizeMany is p = linearizeMany js p := by
  induction h with
  | nil => rfl
  | cons i _ ih => simp only [linearizeMany_cons, ih]
  | swap i j is => exact linearize_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A polynomial is multilinear when each individual degree is at most one. -/
def IsMultilinear (p : MvPolynomial σ R) : Prop := ∀ i, p.degreeOf i ≤ 1

/-- Any list covering the polynomial's variables suffices; extra variables are harmless. -/
theorem isMultilinear_linearizeMany_of_cover [Nontrivial R] (is : List σ)
    (p : MvPolynomial σ R) (hcover : ∀ i ∈ p.vars, i ∈ is) :
    IsMultilinear (linearizeMany is p) := by
  intro i
  by_cases hi : i ∈ is
  · exact degreeOf_linearizeMany_of_mem is i p hi
  · have hn : i ∉ p.vars := fun h => hi (hcover i h)
    have hz : p.degreeOf i = 0 := by simpa [mem_vars_iff_degreeOf_ne_zero] using hn
    exact (degreeOf_linearizeMany_of_not_mem is i p hi).trans (by simp [hz])

theorem vars_linearizeMany_subset [Nontrivial R] (is : List σ) (p : MvPolynomial σ R) :
    (linearizeMany is p).vars ⊆ p.vars := by
  induction is with
  | nil => exact Finset.Subset.refl _
  | cons i is ih => exact (vars_linearize_subset i _).trans ih

/-- Linearize all variables that actually occur; the ambient variable type may be infinite. -/
def multilinearize (p : MvPolynomial σ R) : MvPolynomial σ R :=
  linearizeMany p.vars.toList p

theorem vars_multilinearize_subset [Nontrivial R] (p : MvPolynomial σ R) :
    (multilinearize p).vars ⊆ p.vars := vars_linearizeMany_subset _ p

/-- Reducing the occurring variables produces a multilinear polynomial. -/
theorem isMultilinear_multilinearize [Nontrivial R] (p : MvPolynomial σ R) :
    IsMultilinear (multilinearize p) := by
  intro i
  by_cases hi : i ∈ p.vars
  · exact degreeOf_linearizeMany_of_mem _ i p (by simpa using hi)
  · have hz : p.degreeOf i = 0 := by simpa [mem_vars_iff_degreeOf_ne_zero] using hi
    exact (degreeOf_linearizeMany_of_not_mem _ i p (by simpa using hi)).trans (by simp [hz])

/-- Full multilinearization agrees with the original polynomial on the Boolean cube. -/
theorem eval_multilinearize (x : σ → R) (p : MvPolynomial σ R)
    (hx : ∀ i, x i = 0 ∨ x i = 1) : eval x (multilinearize p) = eval x p :=
  eval_linearizeMany _ x p (fun i _ => hx i)

end IPPSPACE

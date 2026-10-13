/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Syntax
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Blocks of Boolean variables

Contiguous blocks give finite Boolean vectors a concrete representation in the
upstream QBF syntax. Block quantifiers range over every vector exactly as their
individual Boolean quantifiers prescribe. Equality tests and their node counts
will be used by the succinct reachability construction.
-/

namespace IPPSPACE

open Complexity

/-- The names in a contiguous block of `width` Boolean variables. -/
def blockNames (start width : ℕ) : Fin width → ℕ := fun i => start + i.val

/-- Assign every variable in a contiguous block, leaving other names unchanged. -/
def writeBlock (start : ℕ) : {width : ℕ} → (Fin width → Bool) → (ℕ → Bool) → (ℕ → Bool)
  | 0, _, assignment => assignment
  | _ + 1, values, assignment =>
      writeBlock (start + 1) (Fin.tail values) (Function.update assignment start (values 0))

theorem writeBlock_outside (start : ℕ) {width : ℕ} (values : Fin width → Bool)
    (assignment : ℕ → Bool) (j : ℕ) (h : j < start ∨ start + width ≤ j) :
    writeBlock start values assignment j = assignment j := by
  induction width generalizing start assignment with
  | zero => rfl
  | succ width ih =>
    rw [writeBlock, ih (start + 1) (Fin.tail values) _
      (by rcases h with h | h <;> omega)]
    apply Function.update_of_ne
    rcases h with h | h <;> omega

@[simp] theorem writeBlock_at (start : ℕ) {width : ℕ} (values : Fin width → Bool)
    (assignment : ℕ → Bool) (i : Fin width) :
    writeBlock start values assignment (start + i.val) = values i := by
  induction width generalizing start assignment with
  | zero => exact Fin.elim0 i
  | succ width ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [writeBlock, writeBlock_outside _ _ _ _ (Or.inl (by simp))]
      simp
    · have hindex : start + i.succ.val = (start + 1) + i.val := by simp; omega
      rw [writeBlock, hindex, ih]
      rfl

@[simp] theorem writeBlock_comp_blockNames (start : ℕ) {width : ℕ}
    (values : Fin width → Bool) (assignment : ℕ → Bool) :
    writeBlock start values assignment ∘ blockNames start width = values := by
  funext i
  exact writeBlock_at start values assignment i

theorem writeBlock_comp_before (start : ℕ) {width n : ℕ}
    (values : Fin width → Bool) (assignment : ℕ → Bool) (names : Fin n → ℕ)
    (h : ∀ i, names i < start) :
    writeBlock start values assignment ∘ names = assignment ∘ names := by
  funext i
  exact writeBlock_outside start values assignment (names i) (Or.inl (h i))

theorem writeBlock_comp_after (start : ℕ) {width n : ℕ}
    (values : Fin width → Bool) (assignment : ℕ → Bool) (names : Fin n → ℕ)
    (h : ∀ i, start + width ≤ names i) :
    writeBlock start values assignment ∘ names = assignment ∘ names := by
  funext i
  exact writeBlock_outside start values assignment (names i) (Or.inr (h i))

/-- Existentially quantify all coordinates of a contiguous block. -/
def existsBlock (start : ℕ) : ℕ → QBF → QBF
  | 0, φ => φ
  | width + 1, φ => .ex start (existsBlock (start + 1) width φ)

/-- Universally quantify all coordinates of a contiguous block. -/
def forallBlock (start : ℕ) : ℕ → QBF → QBF
  | 0, φ => φ
  | width + 1, φ => .all start (forallBlock (start + 1) width φ)

theorem eval_existsBlock (start width : ℕ) (φ : QBF) (assignment : ℕ → Bool) :
    (existsBlock start width φ).eval assignment = true ↔
      ∃ values : Fin width → Bool, φ.eval (writeBlock start values assignment) = true := by
  induction width generalizing start assignment with
  | zero => simp [existsBlock, writeBlock]
  | succ width ih =>
    rw [existsBlock, QBF.eval_ex_iff]
    simp only [ih]
    constructor
    · rintro ⟨b, values, h⟩
      exact ⟨Fin.cons b values, by simpa [writeBlock] using h⟩
    · rintro ⟨values, h⟩
      exact ⟨values 0, Fin.tail values, h⟩

theorem eval_forallBlock (start width : ℕ) (φ : QBF) (assignment : ℕ → Bool) :
    (forallBlock start width φ).eval assignment = true ↔
      ∀ values : Fin width → Bool, φ.eval (writeBlock start values assignment) = true := by
  induction width generalizing start assignment with
  | zero => simp [forallBlock, writeBlock]
  | succ width ih =>
    rw [forallBlock, QBF.eval_all_iff]
    simp only [ih]
    constructor
    · intro h values
      exact h (values 0) (Fin.tail values)
    · intro h b values
      simpa [writeBlock] using h (Fin.cons b values)

@[simp] theorem nodeCount_existsBlock (start width : ℕ) (φ : QBF) :
    nodeCount (existsBlock start width φ) = nodeCount φ + width := by
  induction width generalizing start with
  | zero => rfl
  | succ width ih => simp [existsBlock, nodeCount, ih, Nat.add_assoc]

@[simp] theorem nodeCount_forallBlock (start width : ℕ) (φ : QBF) :
    nodeCount (forallBlock start width φ) = nodeCount φ + width := by
  induction width generalizing start with
  | zero => rfl
  | succ width ih => simp [forallBlock, nodeCount, ih, Nat.add_assoc]

/-- Equality of two variable bits, expressed only with upstream QBF constructors. -/
def bitEquality (a b : ℕ) : QBF :=
  .disj (.conj (.var a) (.var b)) (.conj (.neg (.var a)) (.neg (.var b)))

@[simp] theorem eval_bitEquality (a b : ℕ) (assignment : ℕ → Bool) :
    (bitEquality a b).eval assignment = true ↔ assignment a = assignment b := by
  simp only [bitEquality, QBF.eval]
  cases assignment a <;> cases assignment b <;> decide

/-- Coordinatewise equality of two equally wide named Boolean vectors. -/
def blockEquality : {width : ℕ} → (Fin width → ℕ) → (Fin width → ℕ) → QBF
  | 0, _, _ => .tru
  | _ + 1, a, b =>
      .conj (bitEquality (a 0) (b 0)) (blockEquality (Fin.tail a) (Fin.tail b))

theorem eval_blockEquality {width : ℕ} (a b : Fin width → ℕ) (assignment : ℕ → Bool) :
    (blockEquality a b).eval assignment = true ↔ assignment ∘ a = assignment ∘ b := by
  induction width with
  | zero => simp [blockEquality]; exact Subsingleton.elim _ _
  | succ width ih =>
    simp only [blockEquality, QBF.eval_conj, Bool.and_eq_true, eval_bitEquality, ih]
    constructor
    · rintro ⟨hzero, htail⟩
      funext i
      refine Fin.cases hzero (fun j => congrFun htail j) i
    · intro h
      exact ⟨congrFun h 0, funext (fun i => congrFun h i.succ)⟩

@[simp] theorem nodeCount_bitEquality (a b : ℕ) : nodeCount (bitEquality a b) = 9 := rfl

@[simp] theorem nodeCount_blockEquality {width : ℕ} (a b : Fin width → ℕ) :
    nodeCount (blockEquality a b) = 10 * width + 1 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [blockEquality, nodeCount, ih]; omega

/-- A variable constrained to one specified Boolean value. -/
def bitValue (name : ℕ) (value : Bool) : QBF :=
  if value then .var name else .neg (.var name)

theorem eval_bitValue (name : ℕ) (value : Bool) (assignment : ℕ → Bool) :
    (bitValue name value).eval assignment = true ↔ assignment name = value := by
  cases value <;> cases h : assignment name <;> simp [bitValue, QBF.eval, h]

/-- A named vector constrained to a concrete Boolean vector. -/
def blockValues : {width : ℕ} → (Fin width → ℕ) → (Fin width → Bool) → QBF
  | 0, _, _ => .tru
  | _ + 1, names, values =>
      .conj (bitValue (names 0) (values 0)) (blockValues (Fin.tail names) (Fin.tail values))

theorem eval_blockValues {width : ℕ} (names : Fin width → ℕ) (values : Fin width → Bool)
    (assignment : ℕ → Bool) :
    (blockValues names values).eval assignment = true ↔ assignment ∘ names = values := by
  induction width with
  | zero => simp [blockValues]; exact Subsingleton.elim _ _
  | succ width ih =>
    simp only [blockValues, QBF.eval_conj, Bool.and_eq_true, eval_bitValue, ih]
    constructor
    · rintro ⟨hzero, htail⟩
      funext i
      exact Fin.cases hzero (fun j => congrFun htail j) i
    · intro h
      exact ⟨congrFun h 0, funext (fun i => congrFun h i.succ)⟩

theorem nodeCount_bitValue_le (name : ℕ) (value : Bool) :
    nodeCount (bitValue name value) ≤ 2 := by
  cases value <;> simp [bitValue, nodeCount]

theorem nodeCount_blockValues_le {width : ℕ} (names : Fin width → ℕ)
    (values : Fin width → Bool) : nodeCount (blockValues names values) ≤ 3 * width + 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
    have hv := nodeCount_bitValue_le (names 0) (values 0)
    have hr := ih (Fin.tail names) (Fin.tail values)
    simp only [blockValues, nodeCount]
    omega

/-- Universally bind an arbitrary finite list of names. Repetitions are harmless. -/
def forallNames : List ℕ → QBF → QBF
  | [], φ => φ
  | i :: names, φ => .all i (forallNames names φ)

theorem mem_freeVars_forallNames (names : List ℕ) (φ : QBF) (i : ℕ) :
    i ∈ (forallNames names φ).freeVars ↔ i ∈ φ.freeVars ∧ i ∉ names := by
  induction names with
  | nil => simp [forallNames]
  | cons j names ih =>
    simp [forallNames, QBF.freeVars, ih, and_assoc, and_comm]

theorem nodeCount_forallNames (names : List ℕ) (φ : QBF) :
    nodeCount (forallNames names φ) = nodeCount φ + names.length := by
  induction names with
  | nil => rfl
  | cons i names ih => simp [forallNames, nodeCount, ih, Nat.add_assoc]

/-- If a formula has an assignment-independent meaning, universal binding
preserves that meaning regardless of the names chosen. -/
theorem eval_forallNames_of_constant (names : List ℕ) (φ : QBF) (P : Prop)
    (h : ∀ assignment, φ.eval assignment = true ↔ P) (assignment : ℕ → Bool) :
    (forallNames names φ).eval assignment = true ↔ P := by
  induction names generalizing assignment with
  | nil => exact h assignment
  | cons i names ih =>
    rw [forallNames, QBF.eval_all_iff]
    simp only [ih, forall_const]

/-- Close the syntax even if a supplied base formula contains semantically
irrelevant free variables. This adds at most one binder per original node. -/
def closeQBF (φ : QBF) : QBF := forallNames (freeVarList φ) φ

theorem closeQBF_closed (φ : QBF) : (closeQBF φ).Closed := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  obtain ⟨hfree, hnot⟩ := (mem_freeVars_forallNames (freeVarList φ) φ i).mp hi
  exact hnot ((mem_freeVarList i φ).mpr hfree)

theorem nodeCount_closeQBF_le (φ : QBF) : nodeCount (closeQBF φ) ≤ 2 * nodeCount φ := by
  rw [closeQBF, nodeCount_forallNames]
  have := freeVarList_length_le φ
  omega

theorem eval_closeQBF_of_constant (φ : QBF) (P : Prop)
    (h : ∀ assignment, φ.eval assignment = true ↔ P) (assignment : ℕ → Bool) :
    (closeQBF φ).eval assignment = true ↔ P :=
  eval_forallNames_of_constant _ φ P h assignment

end IPPSPACE

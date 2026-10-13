/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Arithmetization.Operators

/-!
# A polynomial-length algebraic schedule for prenex QBF

The schedule reduces a fixed syntactic variable list before the innermost
quantifier and after every quantifier. Its length is quadratic in syntax-node
count. Every intermediate individual degree is at most the maximum of two and
the matrix's node count. The latter term covers the initial matrix reduction;
quantifiers applied to already reduced polynomials have degree at most two.

Schedule construction is executable. Polynomial interpretation remains a
semantic specification, not an algorithm for expanding the polynomials. Prenex
conversion, encoded running time, and the interactive protocol are not supplied
by these results.
-/

namespace IPPSPACE

open MvPolynomial Complexity

/-- A fixed reduction block after each quantifier and at the matrix.
As with `applyOperators`, the head is the outermost operation. -/
def reductionSchedule (is : List ℕ) : List Quantifier → List AlgebraicOperator
  | [] => is.map AlgebraicOperator.reduce
  | q :: qs => is.map AlgebraicOperator.reduce ++ .quantify q :: reductionSchedule is qs

/-- Exact operator count, including the matrix's initial reduction block. -/
theorem length_reductionSchedule (is : List ℕ) (qs : List Quantifier) :
    (reductionSchedule is qs).length = (qs.length + 1) * is.length + qs.length := by
  induction qs with
  | nil => simp [reductionSchedule]
  | cons q qs ih =>
    simp only [reductionSchedule, List.length_append, List.length_map, List.length_cons, ih]
    ring

/-- Compute the complete schedule from the matrix and prefix syntax. -/
def PrenexQBF.schedule (φ : PrenexQBF) : List AlgebraicOperator :=
  reductionSchedule (freeVarList φ.matrix) φ.quantifiers

theorem PrenexQBF.schedule_length_le (φ : PrenexQBF) :
    φ.schedule.length ≤ (φ.quantifiers.length + 1) * nodeCount φ.matrix + φ.quantifiers.length := by
  rw [PrenexQBF.schedule, length_reductionSchedule]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (freeVarList_length_le φ.matrix)) _

/-- A quadratic bound in the number of nodes of the underlying prenex formula. -/
theorem PrenexQBF.schedule_length_le_square (φ : PrenexQBF) :
    φ.schedule.length ≤ (nodeCount φ.toQBF + 1) ^ 2 := by
  rw [PrenexQBF.toQBF, nodeCount_prefixQBF]
  calc
    _ ≤ (φ.quantifiers.length + 1) * nodeCount φ.matrix + φ.quantifiers.length :=
      φ.schedule_length_le
    _ ≤ (φ.quantifiers.length + 1) * nodeCount φ.matrix +
        (φ.quantifiers.length + 1) * φ.quantifiers.length :=
      Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
    _ = (φ.quantifiers.length + 1) * (nodeCount φ.matrix + φ.quantifiers.length) := by ring
    _ ≤ (nodeCount φ.matrix + φ.quantifiers.length + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (Nat.le_succ _)

/-- The number of rounds times the uniform degree limit is cubic in syntax size. -/
theorem PrenexQBF.schedule_length_mul_degree_le_cube (φ : PrenexQBF) :
    φ.schedule.length * max 2 (nodeCount φ.matrix) ≤ (nodeCount φ.toQBF + 1) ^ 3 := by
  have hm : nodeCount φ.matrix ≤ nodeCount φ.toQBF := by
    rw [PrenexQBF.toQBF, nodeCount_prefixQBF]
    exact Nat.le_add_right _ _
  have hn := nodeCount_pos φ.toQBF
  calc
    _ ≤ (nodeCount φ.toQBF + 1) ^ 2 * (nodeCount φ.toQBF + 1) :=
      Nat.mul_le_mul φ.schedule_length_le_square (max_le (by omega) (by omega))
    _ = (nodeCount φ.toQBF + 1) ^ 3 := by ring

noncomputable section

variable {R : Type*} [CommRing R]

@[simp] theorem apply_reductionSchedule_nil (is : List ℕ) (p : MvPolynomial ℕ R) :
    applyOperators (reductionSchedule is []) p = linearizeMany is p :=
  applyOperators_map_reduce is p

@[simp] theorem apply_reductionSchedule_cons (is : List ℕ) (q : Quantifier)
    (qs : List Quantifier) (p : MvPolynomial ℕ R) :
    applyOperators (reductionSchedule is (q :: qs)) p =
      linearizeMany is (q.act (applyOperators (reductionSchedule is qs) p)) := by
  rw [reductionSchedule, applyOperators_append, applyOperators_map_reduce]
  rfl

theorem eval_linearizeMany_bit (is : List ℕ) (x : ℕ → Bool) (p : MvPolynomial ℕ R) :
    eval (fun i => bit (x i)) (linearizeMany is p) = eval (fun i => bit (x i)) p := by
  apply eval_linearizeMany
  intro i _
  cases x i <;> simp

/-- The fixed syntactic schedule preserves QBF semantics on Boolean assignments. -/
theorem eval_apply_reductionSchedule (is : List ℕ) (qs : List Quantifier)
    (φ : QBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i))
      (applyOperators (reductionSchedule is qs) (arithmetize φ)) =
        bit ((prefixQBF qs φ).eval x) := by
  induction qs generalizing x with
  | nil => rw [apply_reductionSchedule_nil, eval_linearizeMany_bit, eval_arithmetize]; rfl
  | cons q qs ih =>
    rw [apply_reductionSchedule_cons, eval_linearizeMany_bit]
    exact eval_quantifier_act q _ _ ih x

/-- A list covering the starting variables suffices at every stage. -/
theorem isMultilinear_apply_reductionSchedule [Nontrivial R] (is : List ℕ)
    (qs : List Quantifier) (p : MvPolynomial ℕ R) (hp : ∀ i ∈ p.vars, i ∈ is) :
    IsMultilinear (applyOperators (reductionSchedule is qs) p) := by
  cases qs with
  | nil =>
    rw [apply_reductionSchedule_nil]
    exact isMultilinear_linearizeMany_of_cover is p hp
  | cons q qs =>
    rw [apply_reductionSchedule_cons]
    apply isMultilinear_linearizeMany_of_cover
    intro i hi
    exact hp i (vars_applyOperators_subset (reductionSchedule is qs) p
      (vars_quantifier_act_subset q _ hi))

/-- The uniform bound covers every operation, including partial reduction blocks. -/
theorem degreeBoundedChain_reductionSchedule [Nontrivial R] (is : List ℕ)
    (qs : List Quantifier) (p : MvPolynomial ℕ R) {d : ℕ} (hd : 2 ≤ d)
    (hp : ∀ j, p.degreeOf j ≤ d) (hcover : ∀ i ∈ p.vars, i ∈ is) :
    DegreeBoundedChain (reductionSchedule is qs) p d := by
  have hd₁ : 1 ≤ d := (by decide : 1 ≤ 2).trans hd
  induction qs with
  | nil => exact degreeBoundedChain_map_reduce is p hd₁ hp
  | cons q qs ih =>
    have hq : ∀ j, (q.act (applyOperators (reductionSchedule is qs) p)).degreeOf j ≤ d :=
      fun j => (degreeOf_quantifier_act_le_two q _
        (isMultilinear_apply_reductionSchedule is qs p hcover) j).trans hd
    exact degreeBoundedChain_append _ _ p d
      (degreeBoundedChain_map_reduce is _ hd₁ hq) ⟨hq, ih⟩

/-- Quantifier elimination removes its bound variable from the scheduled polynomial. -/
theorem vars_apply_reductionSchedule_subset_freeVars [Nontrivial R] (is : List ℕ)
    (qs : List Quantifier) (φ : QBF) :
    (applyOperators (reductionSchedule is qs) (arithmetize (R := R) φ)).vars ⊆
      (prefixQBF qs φ).freeVars := by
  induction qs with
  | nil =>
    rw [apply_reductionSchedule_nil]
    exact (vars_linearizeMany_subset is _).trans (vars_arithmetize_subset_freeVars φ)
  | cons q qs ih =>
    rw [apply_reductionSchedule_cons]
    apply (vars_linearizeMany_subset is _).trans
    cases q with
    | ex i =>
      simpa only [prefixQBF_cons, Quantifier.bind, QBF.freeVars, Finset.erase_eq,
        Quantifier.act] using
        (vars_exists_subset i (applyOperators (reductionSchedule is qs) (arithmetize (R := R) φ))).trans
          (Finset.erase_subset_erase i ih)
    | all i =>
      simpa only [prefixQBF_cons, Quantifier.bind, QBF.freeVars, Finset.erase_eq,
        Quantifier.act] using
        (vars_forall_subset i (applyOperators (reductionSchedule is qs) (arithmetize (R := R) φ))).trans
          (Finset.erase_subset_erase i ih)

/-- The symbolic polynomial described by the prenex schedule. -/
def PrenexQBF.polynomial (φ : PrenexQBF) : MvPolynomial ℕ R :=
  applyOperators φ.schedule (arithmetize φ.matrix)

theorem PrenexQBF.eval_polynomial (φ : PrenexQBF) (x : ℕ → Bool) :
    eval (fun i => bit (R := R) (x i)) φ.polynomial = bit (φ.toQBF.eval x) :=
  eval_apply_reductionSchedule _ _ _ x

theorem PrenexQBF.isMultilinear_polynomial [Nontrivial R] (φ : PrenexQBF) :
    IsMultilinear (φ.polynomial (R := R)) :=
  isMultilinear_apply_reductionSchedule _ _ _ (arithmetize_vars_mem_freeVarList φ.matrix)

/-- All intermediate polynomials, including the unreduced matrix, satisfy a linear degree bound. -/
theorem PrenexQBF.degreeBoundedChain_schedule [Nontrivial R] (φ : PrenexQBF) :
    DegreeBoundedChain φ.schedule (arithmetize (R := R) φ.matrix)
      (max 2 (nodeCount φ.matrix)) :=
  degreeBoundedChain_reductionSchedule _ _ _ (le_max_left _ _)
    (fun j => (degreeOf_arithmetize_quantifierFree_le φ.matrix φ.matrix_quantifierFree j).trans
      (le_max_right _ _))
    (arithmetize_vars_mem_freeVarList φ.matrix)

theorem PrenexQBF.degreeOf_intermediate_le [Nontrivial R] (φ : PrenexQBF) (k j : ℕ) :
    (applyOperators (φ.schedule.drop k) (arithmetize (R := R) φ.matrix)).degreeOf j ≤
      max 2 (nodeCount φ.matrix) :=
  φ.degreeBoundedChain_schedule.degreeOf_drop k j

theorem PrenexQBF.vars_polynomial_subset [Nontrivial R] (φ : PrenexQBF) :
    (φ.polynomial (R := R)).vars ⊆ φ.toQBF.freeVars :=
  vars_apply_reductionSchedule_subset_freeVars _ _ _

/-- For closed prenex inputs, the output is the constant zero or one truth value. -/
theorem PrenexQBF.polynomial_eq_C_of_closed [Nontrivial R] (φ : PrenexQBF)
    (hφ : φ.toQBF.Closed) :
    φ.polynomial (R := R) = C (bit (φ.toQBF.eval (fun _ => false))) := by
  change φ.toQBF.freeVars = ∅ at hφ
  have hv : (φ.polynomial (R := R)).vars = ∅ := by
    apply Finset.subset_empty.mp
    simpa only [hφ] using φ.vars_polynomial_subset (R := R)
  have hc := vars_eq_empty_iff_eq_C.mp hv
  have he := φ.eval_polynomial (R := R) (fun _ => false)
  rw [hc, eval_C] at he
  exact hc.trans (congrArg C he)

end

end IPPSPACE

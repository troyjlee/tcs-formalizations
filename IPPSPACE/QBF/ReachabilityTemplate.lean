/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Reachability
import IPPSPACE.QBF.Renaming

/-!
# Reachability from one quantifier-free edge template

A formula on the first two width-sized variable blocks describes one edge
between Boolean states. Renaming these free variables instantiates the template
at any endpoints, without duplicating or expanding the template. The resulting
closed reachability QBF is quadratic in state width beyond the base formula.

This is a concrete Boolean-formula construction. A machine configuration codec,
its local transition formula, and polynomial-time production of the encoded
output are still needed for PSPACE hardness.
-/

namespace IPPSPACE

open Complexity

/-- Interpret the first two variable blocks as the source and target states.
Other variables have the default value false. -/
def edgeBlockAssignment {width : ℕ} (source target : Fin width → Bool) (i : ℕ) : Bool :=
  if hi : i < width then source ⟨i, hi⟩
  else if hj : i < 2 * width then target ⟨i - width, by omega⟩
  else false

/-- Instantiate the two endpoint blocks of an edge formula at arbitrary names. -/
def edgeBlockRenaming {width : ℕ} (a b : Fin width → ℕ) (i : ℕ) : ℕ :=
  if hi : i < width then a ⟨i, hi⟩
  else if hj : i < 2 * width then b ⟨i - width, by omega⟩
  else i

/-- A concrete relation specified by one Boolean formula on two state blocks. -/
def templateEdge {width : ℕ} (base : QBF) (source target : Fin width → Bool) : Prop :=
  base.eval (edgeBlockAssignment source target) = true

/-- Reuse the same base syntax at any pair of named endpoint blocks. -/
def instantiateEdge {width : ℕ} (base : QBF) (a b : Fin width → ℕ) : QBF :=
  renameQBF (edgeBlockRenaming a b) base

theorem eval_instantiateEdge {width : ℕ} (base : QBF) (hbase : base.QuantifierFree)
    (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (a b : Fin width → ℕ) (assignment : ℕ → Bool) :
    (instantiateEdge base a b).eval assignment = true ↔
      templateEdge base (assignment ∘ a) (assignment ∘ b) := by
  rw [instantiateEdge, eval_renameQBF_quantifierFree _ base hbase]
  have heq := base.eval_eq_of_agree (assignment ∘ edgeBlockRenaming a b)
    (edgeBlockAssignment (assignment ∘ a) (assignment ∘ b)) (by
      intro i hi
      have hbound := hvars i hi
      by_cases hfirst : i < width <;>
        simp [edgeBlockRenaming, edgeBlockAssignment, hfirst, hbound])
  rw [heq]
  rfl

@[simp] theorem nodeCount_instantiateEdge {width : ℕ} (base : QBF) (a b : Fin width → ℕ) :
    nodeCount (instantiateEdge base a b) = nodeCount base :=
  nodeCount_renameQBF _ _

/-- The closed succinct reachability formula for a concrete local edge template. -/
def templateReachability {width : ℕ} (base : QBF) (source target : Fin width → Bool) : QBF :=
  closedReachabilityFormula width (instantiateEdge base) source target

theorem templateReachability_closed {width : ℕ} (base : QBF)
    (source target : Fin width → Bool) : (templateReachability base source target).Closed :=
  closedReachabilityFormula_closed _ _ _ _

/-- The generated QBF is true exactly when the target is reachable in the
graph actually computed by the supplied quantifier-free edge template. -/
theorem templateReachability_true_iff {width : ℕ} (base : QBF) (hbase : base.QuantifierFree)
    (hvars : ∀ i ∈ base.freeVars, i < 2 * width) (source target : Fin width → Bool) :
    (templateReachability base source target).IsTrue ↔
      Relation.ReflTransGen (templateEdge base) source target :=
  closedReachabilityFormula_true_iff width _ _ (eval_instantiateEdge base hbase hvars) source target

/-- The supplied edge template occurs once; all extra nodes have quadratic
growth in the number of state bits. -/
theorem nodeCount_templateReachability_le {width : ℕ} (base : QBF)
    (source target : Fin width → Bool) :
    nodeCount (templateReachability base source target) ≤
      2 * (nodeCount base + 18 * width + 6 + width * (43 * width + 9)) :=
  nodeCount_closedReachabilityFormula_le width _ (nodeCount base)
    (fun _ _ => (nodeCount_instantiateEdge _ _ _).le) source target

end IPPSPACE

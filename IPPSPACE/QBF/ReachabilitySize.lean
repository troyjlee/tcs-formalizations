/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.AcceptingReachability

/-!
# Encoded reachability bounds from local formula sizes

This interface accounts for binary variable names as well as formula nodes.
It turns polynomial node budgets for an edge and acceptance test into a
polynomial budget for the actual closed-prenex output bitstring.
-/

namespace IPPSPACE

open Complexity

theorem length_encodeQBF_le_of_quantifierFree (formula : QBF)
    (hformula : formula.QuantifierFree) (nameBound : ℕ)
    (hnames : ∀ i ∈ formula.freeVars, i < nameBound) :
    (encodeQBF formula).length ≤ nodeCount formula * (2 * nameBound + 4) := by
  apply length_encodeQBF_le_of_name_size
  intro i hi
  rw [qbfNames_eq_freeVars_of_quantifierFree formula hformula] at hi
  exact (nat_size_le_self i).trans (hnames i hi).le

/-- A numeric budget depending only on local node counts and configuration width. -/
def acceptingReachabilitySize (edgeNodes acceptNodes width : ℕ) : ℕ :=
  21600 * (edgeNodes * (4 * width + 4) + acceptNodes * (2 * width + 4) +
    2 * width + 1) ^ 4

theorem encodeAcceptingReachability_length_le_of_nodeCount {width : ℕ}
    (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (edgeNodes acceptNodes : ℕ)
    (hedgeNodes : nodeCount base ≤ edgeNodes) (hacceptNodes : nodeCount accept ≤ acceptNodes)
    (source : Fin width → Bool) :
    (encodeAcceptingReachability base accept source).length ≤
      acceptingReachabilitySize edgeNodes acceptNodes width := by
  have he := (length_encodeQBF_le_of_quantifierFree base hbase _ hbaseVars).trans
    (Nat.mul_le_mul_right _ hedgeNodes)
  have ha := (length_encodeQBF_le_of_quantifierFree accept haccept _ hacceptVars).trans
    (Nat.mul_le_mul_right _ hacceptNodes)
  rw [show 2 * (2 * width) + 4 = 4 * width + 4 by omega] at he
  apply (encodeAcceptingReachability_length_le_poly base accept hbase hbaseVars
    haccept hacceptVars source).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- Substitute input-length polynomials for the three numeric budgets. -/
noncomputable def acceptingReachabilityPolynomial
    (edgeNodes acceptNodes width : Polynomial ℕ) : Polynomial ℕ :=
  21600 * (edgeNodes * (4 * width + 4) + acceptNodes * (2 * width + 4) +
    2 * width + 1) ^ 4

@[simp] theorem acceptingReachabilityPolynomial_eval
    (edgeNodes acceptNodes width : Polynomial ℕ) (n : ℕ) :
    (acceptingReachabilityPolynomial edgeNodes acceptNodes width).eval n =
      acceptingReachabilitySize (edgeNodes.eval n) (acceptNodes.eval n) (width.eval n) := by
  simp [acceptingReachabilityPolynomial, acceptingReachabilitySize]

end IPPSPACE

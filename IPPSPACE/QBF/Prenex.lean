/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Syntax

/-!
# Quantifier prefixes over the upstream QBF syntax

This represents inputs already in prenex form. Conversion of arbitrary QBFs,
including bound-variable renaming and its size bound, is a separate obligation.
Variable names in a prefix need not be distinct.
-/

namespace IPPSPACE

open Complexity

/-- A quantifier together with its bound variable. -/
inductive Quantifier where
  | ex (index : ℕ)
  | all (index : ℕ)
  deriving DecidableEq

def Quantifier.bind : Quantifier → QBF → QBF
  | .ex i, φ => .ex i φ
  | .all i, φ => .all i φ

/-- Apply a prefix, with its head the outermost quantifier. -/
def prefixQBF : List Quantifier → QBF → QBF
  | [], φ => φ
  | q :: qs, φ => q.bind (prefixQBF qs φ)

@[simp] theorem prefixQBF_nil (φ : QBF) : prefixQBF [] φ = φ := rfl

@[simp] theorem prefixQBF_cons (q : Quantifier) (qs : List Quantifier) (φ : QBF) :
    prefixQBF (q :: qs) φ = q.bind (prefixQBF qs φ) := rfl

theorem nodeCount_prefixQBF (qs : List Quantifier) (φ : QBF) :
    nodeCount (prefixQBF qs φ) = nodeCount φ + qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    cases q <;> simp [Quantifier.bind, nodeCount, ih, Nat.add_assoc]

/-- A syntactic prenex input, with a proof that its matrix contains no quantifiers. -/
structure PrenexQBF where
  quantifiers : List Quantifier
  matrix : QBF
  matrix_quantifierFree : matrix.QuantifierFree

def PrenexQBF.toQBF (φ : PrenexQBF) : QBF := prefixQBF φ.quantifiers φ.matrix

end IPPSPACE

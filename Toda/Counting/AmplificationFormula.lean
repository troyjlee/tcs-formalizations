import Toda.Arithmetic.Amplification
import Toda.Arithmetic.IterationBounds
import Complexitylib.Asymptotics.PolyBound

/-!
# Explicit small formulas for amplification

Polynomial degree alone does not bound an arithmetic formula's description.
Here an explicit tree formula evaluates to iterated amplification, contains
only the constants two and three, and has quadratically bounded node count
at the chosen logarithmic number of rounds. Each occurrence of a subtree is
counted separately; no sharing is assumed.

This file proves a syntactic size bound. `GapPClosure` proves GapP closure for
each fixed formula. `UniformAmplification` separately constructs a uniform
counting machine for this particular input-dependent amplification family.
-/

namespace Toda.Counting

open Toda.Arithmetic Complexity

/-- Integer formulas with one input and the operations needed for amplification. -/
inductive CountingFormula where
  | input
  | constant (value : ℤ)
  | sub (left right : CountingFormula)
  | mul (left right : CountingFormula)

namespace CountingFormula

/-- Evaluate a formula at an integer input. -/
def eval : CountingFormula → ℤ → ℤ
  | input, m => m
  | constant a, _ => a
  | sub a b, m => a.eval m - b.eval m
  | mul a b, m => a.eval m * b.eval m

/-- Count every node, including repeated copies of a subtree. -/
def nodes : CountingFormula → ℕ
  | input => 1
  | constant _ => 1
  | sub a b => a.nodes + b.nodes + 1
  | mul a b => a.nodes + b.nodes + 1

/-- Require a property of every literal integer appearing in a formula. -/
def AllConstants (p : ℤ → Prop) : CountingFormula → Prop
  | input => True
  | constant a => p a
  | sub a b => a.AllConstants p ∧ b.AllConstants p
  | mul a b => a.AllConstants p ∧ b.AllConstants p

/-- The factored amplification formula uses three copies of its argument. -/
def amplify (e : CountingFormula) : CountingFormula :=
  mul (mul e e) (sub (constant 3) (mul (constant 2) e))

theorem eval_amplify (e : CountingFormula) (m : ℤ) :
    e.amplify.eval m = Arithmetic.amplify (e.eval m) := by
  simp only [amplify, eval, Arithmetic.amplify]
  ring

theorem nodes_amplify (e : CountingFormula) :
    e.amplify.nodes = 3 * e.nodes + 6 := by
  simp only [amplify, nodes]
  omega

/-- Expand the formula recursively, without using a composition-closure assumption. -/
def iteratedAmplify : ℕ → CountingFormula
  | 0 => input
  | k + 1 => (iteratedAmplify k).amplify

theorem eval_iteratedAmplify (k : ℕ) (m : ℤ) :
    (iteratedAmplify k).eval m = amplifyIterate k m := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iteratedAmplify, eval_amplify, ih, amplifyIterate_succ]

/-- An exact node-count identity for the expanded formula. -/
theorem nodes_iteratedAmplify (k : ℕ) :
    (iteratedAmplify k).nodes + 3 = 4 * 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedAmplify, nodes_amplify, pow_succ]
    omega

/-- Literal sizes stay constant as the formula grows. -/
theorem constants_iteratedAmplify (k : ℕ) :
    (iteratedAmplify k).AllConstants (fun z => z = 2 ∨ z = 3) := by
  induction k with
  | zero => trivial
  | succ k ih => simp [iteratedAmplify, amplify, AllConstants, ih]

/-- The formula required for counting `q`-bit strings has quadratic size. -/
theorem nodes_at_amplificationRounds_le (q : ℕ) :
    (iteratedAmplify (amplificationRounds q)).nodes ≤ 16 * (q + 1) ^ 2 := by
  have hexact := nodes_iteratedAmplify (amplificationRounds q)
  have hdegree := three_pow_amplificationRounds_le q
  omega

/-- A polynomial random-tape length gives a polynomial formula node bound. -/
theorem nodes_at_amplificationRounds_polyBound {q : ℕ → ℕ} (hq : PolyBound q) :
    PolyBound (fun n => (iteratedAmplify (amplificationRounds (q n))).nodes) := by
  apply ((PolyBound.const 16).mul ((hq.add (PolyBound.const 1)).pow 2)).mono
  exact fun n => nodes_at_amplificationRounds_le (q n)

end CountingFormula
end Toda.Counting

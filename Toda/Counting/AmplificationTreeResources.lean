import Toda.Counting.AmplificationChoices.Defs
import Toda.Counting.AmplificationResources

/-!
# Polynomial-time bounds for the preorder amplification tree

The complete ternary tree includes a choice bit at every node, including the
leaves. Its exact node count is `(3^(k+1)-1)/2`, so a unary polynomial-time
bound for `3^k` also computes the required witness and product widths.
-/

namespace Toda.Counting

open Complexity Arithmetic AmplificationChoices

/-- Compute the exact tree size whenever its cubic growth is unary
polynomial-time computable. The exponent need not be a fixed constant. -/
theorem unaryFn_amplificationTreeNodes {k : List Bool → ℕ}
    (hdegree : UnaryFn fun x => 3 ^ k x) :
    UnaryFn fun x => nodeCount (k x) := by
  apply ((((UnaryFn.const 3).mul hdegree).sub (UnaryFn.const 1)).div
    (UnaryFn.const 2)).of_eq
  intro x
  have h := nodeCount_arithmetic (k x)
  rw [pow_succ] at h
  omega

/-- The preorder tree at the chosen logarithmic depth has a unary
polynomial-time node count, hence computable witness and product widths. -/
theorem unaryFn_amplificationTreeNodes_rounds {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn fun x => nodeCount (amplificationRounds (q x)) :=
  unaryFn_amplificationTreeNodes (unaryFn_amplificationDegree hq)

/-- An explicit quadratic bound for every node of the chosen tree. -/
theorem amplificationTreeNodes_rounds_le (q : ℕ) :
    nodeCount (amplificationRounds q) ≤ 6 * (q + 1) ^ 2 := by
  have hn := nodeCount_arithmetic (amplificationRounds q)
  rw [pow_succ] at hn
  have hd := three_pow_amplificationRounds_le q
  omega

end Toda.Counting

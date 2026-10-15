import Toda.Counting.AmplificationFormula
import Complexitylib.Classes.P.Unary

/-!
# Polynomial-time computation of amplification resource bounds

The logarithmic round count, resulting degree, modulus exponent, and formula
node count can all be computed in unary polynomial time when the original
string width can. These are actual FP consequences of the numerical bounds.
`UniformAmplification` uses these bounds in a separate construction realizing
input-dependent amplification as a GapP function.
-/

namespace Toda.Counting

open Complexity Arithmetic

/-- Compute the logarithmic amplification round count in unary polynomial time. -/
theorem unaryFn_amplificationRounds {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn fun x => amplificationRounds (q x) :=
  ((UnaryFn.const 2).log (hq.add (UnaryFn.const 1))).add (UnaryFn.const 1)

/-- The exponent of the amplified modulus has linear size in the original
width, so its unary representation is polynomial-time computable. -/
theorem unaryFn_amplificationModulusExponent {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn fun x => 2 ^ amplificationRounds (q x) :=
  (UnaryFn.const 2).pow_of_le (unaryFn_amplificationRounds hq)
    ((UnaryFn.const 2).mul (hq.add (UnaryFn.const 1)))
    (fun x => two_pow_amplificationRounds_le (q x))

/-- The amplification polynomial's degree is computable in unary polynomial
time, using the quadratic bound to justify the variable exponentiation. -/
theorem unaryFn_amplificationDegree {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn fun x => 3 ^ amplificationRounds (q x) :=
  (UnaryFn.const 3).pow_of_le (unaryFn_amplificationRounds hq)
    ((UnaryFn.const 4).mul ((hq.add (UnaryFn.const 1)).pow_const 2))
    (fun x => three_pow_amplificationRounds_le (q x))

/-- The exact node count of the expanded amplification formula is also a
unary polynomial-time function. Formula generation is a separate obligation. -/
theorem unaryFn_amplificationNodes {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn fun x => (CountingFormula.iteratedAmplify (amplificationRounds (q x))).nodes := by
  apply (((UnaryFn.const 4).mul (unaryFn_amplificationDegree hq)).sub
    (UnaryFn.const 3)).of_eq
  intro x
  have h := CountingFormula.nodes_iteratedAmplify (amplificationRounds (q x))
  omega

end Toda.Counting

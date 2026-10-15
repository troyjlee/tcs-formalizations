import Toda.Counting.VerifierWitness
import Complexitylib.Classes.P.Unary
import Complexitylib.Classes.P

/-!
# A common clock for polynomially bounded paired inputs

Every second component of length at most `q x` gives a paired input of length
at most `2 * |x| + 2 + q x`. An explicit source clock at this bound is both
unary polynomial-time computable and sufficient for all these source inputs.
Canonical witness padding preserves accepting-leaf counts at the common width.
-/

namespace Toda.Counting

open Complexity

/-- Evaluate an explicit polynomial clock on a unary polynomial-time number. -/
theorem unaryFn_polynomialClock (A B : ℕ) {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn fun x => polynomialClock A B (q x) :=
  (UnaryFn.const A).mul ((hq.add (UnaryFn.const 1)).pow_const B)

/-- A common witness width for second components of length at most `q x`. -/
def pairedClock (A B : ℕ) (q : List Bool → ℕ) (x : List Bool) : ℕ :=
  polynomialClock A B (2 * x.length + 2 + q x)

/-- The common paired-input clock can be computed in unary in polynomial time. -/
theorem unaryFn_pairedClock (A B : ℕ) {q : List Bool → ℕ} (hq : UnaryFn q) :
    UnaryFn (pairedClock A B q) :=
  unaryFn_polynomialClock A B
    ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 2)).add hq)

/-- Increasing the second-component length to its bound gives a sufficient
source clock for every permitted paired input. -/
theorem sourceClock_le_pairedClock (A B : ℕ) (q : List Bool → ℕ)
    (x y : List Bool) (hy : y.length ≤ q x) :
    polynomialClock A B (pair x y).length ≤ pairedClock A B q x := by
  apply polynomialClock_mono
  simpa only [pair_length] using Nat.add_le_add_left hy (2 * x.length + 2)

/-- A source counting function is represented by its canonical verifier at
the shared width, even for shorter second components and early-halting paths. -/
theorem canonical_pair_verifier_count {f : List Bool → ℕ} {n : ℕ}
    (N : NTM n) (A B : ℕ) (hN : N.AllPathsHaltIn (polynomialClock A B))
    (hcount : ∀ z, f z = N.acceptLeafCount z (polynomialClock A B z.length))
    (q : List Bool → ℕ) (x y : List Bool) (hy : y.length ≤ q x) :
    f (pair x y) =
      (verifierWitnesses (EncodedVerifier.canonicalLanguage N) (pair x y)
        (pairedClock A B q x)).card := by
  rw [verifierWitnesses_canonicalLanguage, card_canonicalWitnesses,
    N.acceptLeafCount_eq_of_le_of_allChoicesHalt (pair x y)
      (sourceClock_le_pairedClock A B q x y hy) (hN (pair x y))]
  exact hcount (pair x y)

end Toda.Counting

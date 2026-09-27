import QuantumQueryComplexity.Quantum.Postcomp
import QuantumQueryComplexity.Quantum.Characterization

/-!
# Using the standalone quantum query library

The library is a pinned Git dependency of this project. These examples
exercise its public APIs without maintaining another copy of its source.
-/

namespace QuantumQueryUsage

open QuantumQueryComplexity

/-- Reading one Boolean input coordinate and removing the blank output costs one query. -/
theorem first_bit (n : ℕ) :
    qQuery (fun x : Fin (n + 1) → Bool => x 0) 0 ≤ 1 := by
  have h := (computesWithErrorOn_proj
    (id : (Fin (n + 1) → Bool) → Fin (n + 1) → Bool) 0
    (le_refl (0 : ℝ))).postcomp (fun bit : Option Bool => bit.getD false)
  exact qQueryOn_le (by simpa using h)

/-- An adversary estimate supplies a natural-number query lower bound. -/
theorem query_lower_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (k : ℕ) (h : 36 * (k : ℝ) ≤ advPM f) :
    k ≤ boundedErrorQQuery f := by
  have hq := mul_advPM_le_boundedErrorQQuery f
  have hk : (k : ℝ) ≤ (boundedErrorQQuery f : ℝ) := by linarith
  exact_mod_cast hk

end QuantumQueryUsage

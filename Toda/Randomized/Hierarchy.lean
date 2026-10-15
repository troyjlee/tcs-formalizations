import Toda.Randomized.Existential

/-!
# The canonical polynomial hierarchy has randomized parity predicates

The unchanged polynomial hierarchy starts with machine-based P and alternates
polynomially bounded quantification and complement. Uniform existential
elimination and complement closure place every level in the internal
bounded-error parity witness operator. A separate costed oracle simulation
is required to reach the final counting-oracle class.
-/

namespace Toda.Randomized

open Complexity

/-- Every canonical existential level has a bounded-error parity predicate. -/
theorem sigmaP_subset_bpParityP (level : ℕ) : SigmaP level ⊆ BPParityP := by
  induction level with
  | zero => exact p_subset_bpParityP
  | succ level ih =>
      rintro language ⟨polynomial, source, hsource, rfl⟩
      have hcomplement : sourceᶜ ∈ SigmaP level := hsource
      have hsource' : source ∈ BPParityP := by
        simpa using compl_mem_bpParityP (ih hcomplement)
      exact polyExistsLang_mem_bpParityP hsource' polynomial

/-- The universal levels satisfy the same inclusion by complement closure. -/
theorem piP_subset_bpParityP (level : ℕ) : PiP level ⊆ BPParityP := by
  intro language hlanguage
  have hcomplement : languageᶜ ∈ SigmaP level := hlanguage
  simpa using compl_mem_bpParityP (sigmaP_subset_bpParityP level hcomplement)

/-- The canonical polynomial hierarchy is contained in the uniform
bounded-error parity witness operator. -/
theorem PH_subset_bpParityP : PH ⊆ BPParityP := by
  intro language hlanguage
  obtain ⟨level, hlevel⟩ := mem_PH_iff.mp hlanguage
  exact sigmaP_subset_bpParityP level hlevel

end Toda.Randomized

import Toda.Parity.Class
import Toda.Randomized.Finite

/-!
# Randomized parity predicates

An internal witness operator for the PH proof: one polynomial-width uniform
seed is fed to a canonical ParityP language. The error is at most 1/16 on
every input. This definition does not identify the operator with a randomized
oracle-machine class. Its use in Toda requires the constructions below it and
the final costed #P-oracle simulation.
-/

namespace Toda.Randomized

open Complexity Toda.Parity

/-- Seeds on which the randomized predicate disagrees with the target language. -/
noncomputable def errorSeeds (language predicate : Language)
    (width : List Bool → ℕ) (input : List Bool) : Finset (Fin (width input) → Bool) := by
  classical
  exact Finset.univ.filter fun seed =>
    ¬ (pair input (List.ofFn seed) ∈ predicate ↔ input ∈ language)

/-- The internal bounded-error randomized parity witness operator. -/
def BPParityP : Set Language :=
  {language | ∃ (predicate : Language) (width : List Bool → ℕ),
    predicate ∈ ParityP ∧ UnaryFn width ∧ ∀ input,
      16 * (errorSeeds language predicate width input).card ≤ 2 ^ width input}

/-- Complementing both the target and its predicate preserves the error set. -/
@[simp] theorem errorSeeds_compl (language predicate : Language)
    (width : List Bool → ℕ) (input : List Bool) :
    errorSeeds languageᶜ predicateᶜ width input = errorSeeds language predicate width input := by
  classical
  ext seed
  simp only [errorSeeds, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff]
  tauto

theorem compl_mem_bpParityP {language : Language} (hlanguage : language ∈ BPParityP) :
    languageᶜ ∈ BPParityP := by
  obtain ⟨predicate, width, hpredicate, hwidth, herror⟩ := hlanguage
  exact ⟨predicateᶜ, width, compl_mem_parityP hpredicate, hwidth,
    fun input => by simpa using herror input⟩

/-- A deterministic parity predicate needs no random bits and has zero error. -/
theorem parityP_subset_bpParityP : ParityP ⊆ BPParityP := by
  classical
  intro language hlanguage
  refine ⟨pairFst ⁻¹' language, fun _ => 0,
    preimage_mem_parityP hlanguage pairFst_mem_FP, UnaryFn.const 0, ?_⟩
  intro input
  simp [errorSeeds]

theorem p_subset_bpParityP : P ⊆ BPParityP :=
  fun _ h => parityP_subset_bpParityP (P_subset_parityP h)

/-- Actual polynomial-time preprocessing preserves the witness operator,
including the exact input-dependent random width and error count. -/
theorem preimage_mem_bpParityP {language : Language} {prepare : List Bool → List Bool}
    (hlanguage : language ∈ BPParityP) (hprepare : prepare ∈ FP) :
    prepare ⁻¹' language ∈ BPParityP := by
  obtain ⟨predicate, width, hpredicate, hwidth, herror⟩ := hlanguage
  let transform : List Bool → List Bool :=
    fun z => pair (prepare (pairFst z)) (pairSnd z)
  have htransform : transform ∈ FP :=
    mem_FP_pair (mem_FP_comp pairFst_mem_FP hprepare) pairSnd_mem_FP
  refine ⟨transform ⁻¹' predicate, fun x => width (prepare x),
    preimage_mem_parityP hpredicate htransform, hwidth.comp hprepare, ?_⟩
  intro input
  have heq : errorSeeds (prepare ⁻¹' language) (transform ⁻¹' predicate)
      (fun x => width (prepare x)) input = errorSeeds language predicate width (prepare input) := by
    classical
    ext seed
    simp [errorSeeds, transform]
  rw [heq]
  exact herror (prepare input)

end Toda.Randomized

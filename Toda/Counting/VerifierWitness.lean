import Toda.Counting.SharpPWitness
import Toda.Counting.EncodedVerifier

/-!
# Polynomial-time predicates for counting witnesses

Canonical choice tapes now have an ordinary encoded-input verifier. These
results give the forward direction of the witness characterization of #P,
and a common-width pair of polynomial-time predicates for GapP. They do not
assert the general converse compiler for arbitrary encoded-input verifiers.
-/

namespace Toda.Counting

open Complexity

/-- Width-`T` witnesses whose paired encoding lies in a language. Classical
decidability only defines this finite set; polynomial-time verification is a
separate, machine-based assertion about the language. -/
noncomputable def verifierWitnesses (L : Language) (x : List Bool) (T : ℕ) :
    Finset (Fin T → Bool) := by
  classical
  exact Finset.univ.filter (fun w => pair x (List.ofFn w) ∈ L)

@[simp] theorem mem_verifierWitnesses (L : Language) (x : List Bool) (T : ℕ)
    (w : Fin T → Bool) :
    w ∈ verifierWitnesses L x T ↔ pair x (List.ofFn w) ∈ L := by
  classical
  simp [verifierWitnesses]

theorem verifierWitnesses_canonicalLanguage {n : ℕ} (N : NTM n)
    (x : List Bool) (T : ℕ) :
    verifierWitnesses (EncodedVerifier.canonicalLanguage N) x T = canonicalWitnesses N x T := by
  ext w
  simp only [mem_verifierWitnesses, EncodedVerifier.pair_mem_canonicalLanguage_iff,
    CanonicalVerifier.canonicalListFrom_ofFn_iff, canonicalWitnesses,
    mem_canonicalWitnessesFrom]

/-- Every canonical #P function counts polynomial-width witnesses accepted by
an actual polynomial-time decider on the ordinary paired input encoding. -/
theorem sharpP_exists_polytime_verifier {f : List Bool → ℕ} (hf : f ∈ SharpP) :
    ∃ (L : Language) (coefficient exponent : ℕ), L ∈ Complexity.P ∧
      ∀ x, f x = (verifierWitnesses L x
        (polynomialClock coefficient exponent x.length)).card := by
  obtain ⟨n, N, A, B, _, hcount⟩ := sharpP_iff_exists_canonicalWitnesses.mp hf
  refine ⟨EncodedVerifier.canonicalLanguage N, A, B,
    EncodedVerifier.canonicalLanguage_mem_P N, fun x => ?_⟩
  rw [verifierWitnesses_canonicalLanguage]
  exact hcount x

/-- Every canonical GapP function is a difference of two polynomial-time
verifier counts using the same explicit polynomial witness width. -/
theorem gapP_exists_common_polytime_verifiers {f : List Bool → ℤ} (hf : f ∈ GapP) :
    ∃ (L R : Language) (coefficient exponent : ℕ),
      L ∈ Complexity.P ∧ R ∈ Complexity.P ∧ ∀ x, f x =
        ((verifierWitnesses L x (polynomialClock coefficient exponent x.length)).card : ℤ) -
        ((verifierWitnesses R x (polynomialClock coefficient exponent x.length)).card : ℤ) := by
  obtain ⟨n, m, N, M, A, B, _, _, hcount⟩ :=
    gapP_iff_exists_common_clock_witnesses.mp hf
  refine ⟨EncodedVerifier.canonicalLanguage N, EncodedVerifier.canonicalLanguage M,
    A, B, EncodedVerifier.canonicalLanguage_mem_P N,
    EncodedVerifier.canonicalLanguage_mem_P M, fun x => ?_⟩
  rw [verifierWitnesses_canonicalLanguage, verifierWitnesses_canonicalLanguage]
  exact hcount x

end Toda.Counting

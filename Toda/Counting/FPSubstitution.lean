import Toda.Counting.VerifierCharacterization
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Cobham.Internal

/-!
# Polynomial-time substitution in counting classes

An ordinary polynomial-time string function can preprocess a counting input.
The transformed canonical verifier keeps the same witness, while a polynomial
bound on the preprocessing output length supplies a sufficient witness width
in the original input length. Canonical false padding preserves the count
when that width exceeds the source clock.
-/

namespace Toda.Counting

open Complexity

/-- Preprocess the input component of a paired verifier input and preserve
the witness component. Total pair projections specify every malformed input. -/
def substitutionLanguage (L : Language) (h : List Bool → List Bool) : Language :=
  (fun z => pair (h (pairFst z)) (pairSnd z)) ⁻¹' L

/-- Polynomial-time input substitution preserves polynomial-time verification. -/
theorem substitutionLanguage_mem_P (L : Language) (h : List Bool → List Bool)
    (hL : L ∈ Complexity.P) (hh : h ∈ FP) :
    substitutionLanguage L h ∈ Complexity.P := by
  exact mem_P_preimage
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hh) pairSnd_mem_FP) hL

/-- Preprocessing changes the verifier input without changing any witness. -/
theorem verifierWitnesses_substitutionLanguage (L : Language)
    (h : List Bool → List Bool) (x : List Bool) (T : ℕ) :
    verifierWitnesses (substitutionLanguage L h) x T =
      verifierWitnesses L (h x) T := by
  ext w
  simp [substitutionLanguage]

/-- #P is closed under preprocessing by an ordinary polynomial-time function.
The resulting witness clock is polynomial in the original input length. -/
theorem sharpP_comp_fp {f : List Bool → ℕ} {h : List Bool → List Bool}
    (hf : f ∈ SharpP) (hh : h ∈ FP) :
    (fun x => f (h x)) ∈ SharpP := by
  obtain ⟨n, N, A, B, hN, hcount⟩ := sharpP_iff_exists_polynomialClock.mp hf
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hh
  obtain ⟨C, D, hmajorant⟩ :=
    (polyBound_comp (polynomialClock_polyBound A B) (PolyBound.eval p)).exists_mul_pow_bound
  have hclock (x : List Bool) :
      polynomialClock A B (h x).length ≤ polynomialClock C D x.length :=
    (polynomialClock_mono A B (hp x)).trans (hmajorant x.length)
  apply sharpP_iff_exists_polytime_verifier.mpr
  refine ⟨substitutionLanguage (EncodedVerifier.canonicalLanguage N) h, C, D,
    substitutionLanguage_mem_P _ h (EncodedVerifier.canonicalLanguage_mem_P N) hh,
    fun x => ?_⟩
  rw [verifierWitnesses_substitutionLanguage, verifierWitnesses_canonicalLanguage,
    card_canonicalWitnesses,
    N.acceptLeafCount_eq_of_le_of_allChoicesHalt (h x) (hclock x) (hN (h x))]
  exact hcount (h x)

/-- GapP is closed under polynomial-time string preprocessing. This uses
substitution of the input, with no composition claim for GapP-valued outputs. -/
theorem gapP_comp_fp {f : List Bool → ℤ} {h : List Bool → List Bool}
    (hf : f ∈ GapP) (hh : h ∈ FP) :
    (fun x => f (h x)) ∈ GapP := by
  obtain ⟨f₁, f₂, hf₁, hf₂, hcount⟩ := hf
  exact ⟨(fun x => f₁ (h x)), (fun x => f₂ (h x)),
    sharpP_comp_fp hf₁ hh, sharpP_comp_fp hf₂ hh, fun x => hcount (h x)⟩

end Toda.Counting

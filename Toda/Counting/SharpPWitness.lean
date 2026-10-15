import Toda.Counting.CanonicalWitness
import Toda.Counting.PolynomialClock

/-!
# Canonical counting witnesses at an explicit polynomial width

The counting-machine definitions of #P and GapP can be expressed using
canonical padded choice tapes of explicit polynomial width. In the GapP
normal form, both constituent machines use the same width.

The witness predicates in this module refer to the original machine's execution.
`VerifierCharacterization` connects them to ordinary polynomial-time deciders
and proves the converse compiler using actual counting machines.
-/

namespace Toda.Counting

open Complexity

/-- A count-preserving choice-tape normal form for the canonical #P class. -/
theorem sharpP_iff_exists_canonicalWitnesses {f : List Bool → ℕ} :
    f ∈ SharpP ↔
      ∃ (tapes : ℕ) (machine : NTM tapes) (coefficient exponent : ℕ),
        machine.AllPathsHaltIn (polynomialClock coefficient exponent) ∧
        ∀ x, f x = (canonicalWitnesses machine x
          (polynomialClock coefficient exponent x.length)).card := by
  constructor
  · intro hf
    obtain ⟨tapes, machine, coefficient, exponent, hhalt, hcount⟩ :=
      sharpP_iff_exists_polynomialClock.mp hf
    refine ⟨tapes, machine, coefficient, exponent, hhalt, fun x => ?_⟩
    rw [card_canonicalWitnesses]
    exact hcount x
  · rintro ⟨tapes, machine, coefficient, exponent, hhalt, hcount⟩
    apply sharpP_iff_exists_polynomialClock.mpr
    refine ⟨tapes, machine, coefficient, exponent, hhalt, fun x => ?_⟩
    rw [← card_canonicalWitnesses]
    exact hcount x

/-- Two #P functions can use a common explicit polynomial clock without
changing either accepting-leaf count. -/
theorem sharpP_pair_exists_polynomialClock {f g : List Bool → ℕ}
    (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    ∃ (tapes₁ tapes₂ : ℕ) (machine₁ : NTM tapes₁) (machine₂ : NTM tapes₂)
      (coefficient exponent : ℕ),
      machine₁.AllPathsHaltIn (polynomialClock coefficient exponent) ∧
      machine₂.AllPathsHaltIn (polynomialClock coefficient exponent) ∧
      (∀ x, f x = machine₁.acceptLeafCount x
        (polynomialClock coefficient exponent x.length)) ∧
      (∀ x, g x = machine₂.acceptLeafCount x
        (polynomialClock coefficient exponent x.length)) := by
  obtain ⟨n, N, a, b, hN, hfval⟩ := sharpP_iff_exists_polynomialClock.mp hf
  obtain ⟨m, M, c, d, hM, hgval⟩ := sharpP_iff_exists_polynomialClock.mp hg
  obtain ⟨A, B, hmajorant⟩ :=
    ((polynomialClock_polyBound a b).add
      (polynomialClock_polyBound c d)).exists_mul_pow_bound
  have hleft (i : ℕ) : polynomialClock a b i ≤ polynomialClock A B i :=
    (Nat.le_add_right _ _).trans (hmajorant i)
  have hright (i : ℕ) : polynomialClock c d i ≤ polynomialClock A B i :=
    (Nat.le_add_left _ _).trans (hmajorant i)
  refine ⟨n, m, N, M, A, B, hN.mono hleft, hM.mono hright, ?_, ?_⟩
  · intro x
    rw [N.acceptLeafCount_eq_of_le_of_allPathsHaltIn hleft hN]
    exact hfval x
  · intro x
    rw [M.acceptLeafCount_eq_of_le_of_allPathsHaltIn hright hM]
    exact hgval x

/-- GapP is a difference of two canonical witness counts with one common
polynomial width. The verifier-machine bridge is in `VerifierCharacterization`. -/
theorem gapP_iff_exists_common_clock_witnesses {h : List Bool → ℤ} :
    h ∈ GapP ↔
      ∃ (tapes₁ tapes₂ : ℕ) (machine₁ : NTM tapes₁) (machine₂ : NTM tapes₂)
        (coefficient exponent : ℕ),
        machine₁.AllPathsHaltIn (polynomialClock coefficient exponent) ∧
        machine₂.AllPathsHaltIn (polynomialClock coefficient exponent) ∧
        ∀ x, h x =
          ((canonicalWitnesses machine₁ x
            (polynomialClock coefficient exponent x.length)).card : ℤ) -
          ((canonicalWitnesses machine₂ x
            (polynomialClock coefficient exponent x.length)).card : ℤ) := by
  constructor
  · rintro ⟨f, g, hf, hg, hval⟩
    obtain ⟨n, m, N, M, a, b, hN, hM, hfval, hgval⟩ :=
      sharpP_pair_exists_polynomialClock hf hg
    refine ⟨n, m, N, M, a, b, hN, hM, fun x => ?_⟩
    rw [card_canonicalWitnesses, card_canonicalWitnesses,
      ← hfval x, ← hgval x]
    exact hval x
  · rintro ⟨n, m, N, M, a, b, hN, hM, hval⟩
    refine ⟨(fun x => (canonicalWitnesses N x (polynomialClock a b x.length)).card),
      (fun x => (canonicalWitnesses M x (polynomialClock a b x.length)).card),
      ?_, ?_, hval⟩
    · exact sharpP_iff_exists_canonicalWitnesses.mpr ⟨n, N, a, b, hN, fun _ => rfl⟩
    · exact sharpP_iff_exists_canonicalWitnesses.mpr ⟨m, M, a, b, hM, fun _ => rfl⟩

end Toda.Counting

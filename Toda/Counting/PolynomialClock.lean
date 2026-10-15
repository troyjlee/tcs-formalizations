import Complexitylib.Classes.SharpP
import Complexitylib.Asymptotics.PolyBound
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Size

/-!
# Explicit polynomial clocks for counting machines

The clock in `Complexity.SharpP` is an arbitrary natural-number function with
a polynomial big-O bound. Such a function need not itself be computable.
Every witness can instead use a clock of the form `A * (n + 1) ^ B`, without
changing its accepting-leaf count. This file proves that replacement using
upstream clock invariance, and bounds the binary lengths of #P values and
GapP magnitudes.

These theorems give explicit finite-parameter bounds. `PolynomialCounter`
realizes the clock on a machine; `VerifierCharacterization` supplies the
count-preserving witness compiler.
-/

namespace Toda.Counting

open Complexity

/-- A computable numerical clock with two fixed natural-number parameters. -/
def polynomialClock (coefficient exponent inputLength : ℕ) : ℕ :=
  coefficient * (inputLength + 1) ^ exponent

/-- The explicit clock has a pointwise polynomial bound. -/
theorem polynomialClock_polyBound (coefficient exponent : ℕ) :
    PolyBound (polynomialClock coefficient exponent) := by
  exact (PolyBound.const coefficient).mul
    ((PolyBound.id.add (PolyBound.const 1)).pow exponent)

/-- Polynomial resource bounds compose without assuming the original bound
functions are monotone or computable. -/
theorem polyBound_comp {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f (g n)) := by
  obtain ⟨A, B, hmajorant⟩ := hf.exists_mul_pow_bound
  exact ((PolyBound.const A).mul ((hg.add (PolyBound.const 1)).pow B)).mono
    (fun n => hmajorant (g n))

/-- Increasing the input length cannot decrease this clock. -/
theorem polynomialClock_mono (coefficient exponent : ℕ) :
    Monotone (polynomialClock coefficient exponent) := by
  intro n m hnm
  exact Nat.mul_le_mul_left coefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hnm 1) exponent)

/-- Every polynomial big-O bound admits a pointwise clock with fixed
parameters. The original function is not assumed computable. -/
theorem exists_polynomialClock_majorant {timeBound : ℕ → ℕ} {degree : ℕ}
    (hpoly : timeBound =O (· ^ degree)) :
    ∃ coefficient exponent : ℕ,
      ∀ n, timeBound n ≤ polynomialClock coefficient exponent n := by
  exact PolyBound.exists_mul_pow_bound (BigO.pow_polynomial_bound hpoly)

/-- The canonical #P definition is unchanged when its existential time bound
is restricted to explicit finite-parameter polynomial clocks. -/
theorem sharpP_iff_exists_polynomialClock {f : List Bool → ℕ} :
    f ∈ SharpP ↔
      ∃ (tapes : ℕ) (machine : NTM tapes) (coefficient exponent : ℕ),
        machine.AllPathsHaltIn (polynomialClock coefficient exponent) ∧
        ∀ x, f x = machine.acceptLeafCount x
          (polynomialClock coefficient exponent x.length) := by
  constructor
  · rintro ⟨tapes, machine, timeBound, degree, hhalt, hpoly, hcount⟩
    obtain ⟨coefficient, exponent, hmajorant⟩ :=
      exists_polynomialClock_majorant hpoly
    refine ⟨tapes, machine, coefficient, exponent,
      hhalt.mono hmajorant, fun x => ?_⟩
    rw [machine.acceptLeafCount_eq_of_le_of_allPathsHaltIn hmajorant hhalt]
    exact hcount x
  · rintro ⟨tapes, machine, coefficient, exponent, hhalt, hcount⟩
    obtain ⟨degree, hpoly⟩ := (polynomialClock_polyBound coefficient exponent).bigO
    exact ⟨tapes, machine, polynomialClock coefficient exponent, degree,
      hhalt, hpoly, hcount⟩

/-- #P values have an explicit exponential bound and a polynomial binary
length bound, valid at every input length including zero. -/
theorem sharpP_exists_value_size_bound {f : List Bool → ℕ} (hf : f ∈ SharpP) :
    ∃ coefficient exponent : ℕ, ∀ x,
      f x ≤ 2 ^ polynomialClock coefficient exponent x.length ∧
      (f x).size ≤ polynomialClock coefficient exponent x.length + 1 := by
  obtain ⟨tapes, machine, coefficient, exponent, _, hcount⟩ :=
    sharpP_iff_exists_polynomialClock.mp hf
  refine ⟨coefficient, exponent, fun x => ?_⟩
  have hbound : f x ≤ 2 ^ polynomialClock coefficient exponent x.length := by
    rw [hcount x]
    exact machine.acceptLeafCount_le x _
  exact ⟨hbound, by simpa only [Nat.size_pow] using Nat.size_le_size hbound⟩

/-- GapP magnitudes also have an explicit exponential bound and a polynomial
binary length bound. A signed output encoding is not defined here. -/
theorem gapP_exists_natAbs_size_bound {h : List Bool → ℤ} (hh : h ∈ GapP) :
    ∃ coefficient exponent : ℕ, ∀ x,
      (h x).natAbs ≤ 2 ^ polynomialClock coefficient exponent x.length ∧
      (h x).natAbs.size ≤ polynomialClock coefficient exponent x.length + 1 := by
  obtain ⟨f, g, hf, hg, hval⟩ := hh
  obtain ⟨a, b, hab⟩ := sharpP_exists_value_size_bound hf
  obtain ⟨c, d, hcd⟩ := sharpP_exists_value_size_bound hg
  obtain ⟨coefficient, exponent, hmajorant⟩ :=
    ((polynomialClock_polyBound a b).add
      (polynomialClock_polyBound c d)).exists_mul_pow_bound
  refine ⟨coefficient, exponent, fun x => ?_⟩
  have hab_le : polynomialClock a b x.length ≤
      polynomialClock coefficient exponent x.length :=
    (Nat.le_add_right _ _).trans (hmajorant x.length)
  have hcd_le : polynomialClock c d x.length ≤
      polynomialClock coefficient exponent x.length :=
    (Nat.le_add_left _ _).trans (hmajorant x.length)
  have hbound : (h x).natAbs ≤
      2 ^ polynomialClock coefficient exponent x.length := by
    rw [hval x]
    exact Int.natAbs_coe_sub_coe_le_of_le
      ((hab x).1.trans (Nat.pow_le_pow_right (by decide) hab_le))
      ((hcd x).1.trans (Nat.pow_le_pow_right (by decide) hcd_le))
  exact ⟨hbound, by simpa only [Nat.size_pow] using Nat.size_le_size hbound⟩

end Toda.Counting

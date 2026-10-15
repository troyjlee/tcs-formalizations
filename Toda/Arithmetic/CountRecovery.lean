import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Recovering a finite count from amplified residues

If each integer in a finite sum is congruent to a predicate's zero-or-one
indicator, the sum is congruent to the number of indices satisfying the
predicate. When that count is smaller than the positive modulus, taking the
integer remainder recovers the count exactly. The summands may be negative.

The binary-tape specialization uses modulus `2^(q+1)` for `2^q` tapes. These
are arithmetic statements; no counting-complexity membership is asserted.
-/

namespace Toda.Arithmetic

open scoped BigOperators

variable {α : Type*}

/-- Summing zero-or-one residues gives the residue of the predicate's count. -/
theorem sum_modEq_filter_card (s : Finset α) (h : α → ℤ)
    (p : α → Prop) [DecidablePred p] {M : ℤ}
    (hh : ∀ i ∈ s, h i ≡ (if p i then 1 else 0) [ZMOD M]) :
    (∑ i ∈ s, h i) ≡ ((s.filter p).card : ℤ) [ZMOD M] := by
  simpa only [Finset.sum_boole] using Int.ModEq.sum hh

/-- A modulus larger than the predicate's count recovers that count exactly. -/
theorem sum_emod_eq_filter_card (s : Finset α) (h : α → ℤ)
    (p : α → Prop) [DecidablePred p] {M : ℤ}
    (hcount : ((s.filter p).card : ℤ) < M)
    (hh : ∀ i ∈ s, h i ≡ (if p i then 1 else 0) [ZMOD M]) :
    (∑ i ∈ s, h i) % M = ((s.filter p).card : ℤ) := by
  exact (sum_modEq_filter_card s h p hh).eq.trans
    (Int.emod_eq_of_lt (Int.natCast_nonneg _) hcount)

/-- Bounding all indices suffices to choose a modulus before knowing the count. -/
theorem sum_emod_eq_filter_card_of_card_lt (s : Finset α) (h : α → ℤ)
    (p : α → Prop) [DecidablePred p] {M : ℤ}
    (hcard : (s.card : ℤ) < M)
    (hh : ∀ i ∈ s, h i ≡ (if p i then 1 else 0) [ZMOD M]) :
    (∑ i ∈ s, h i) % M = ((s.filter p).card : ℤ) := by
  apply sum_emod_eq_filter_card s h p _ hh
  exact lt_of_le_of_lt (Int.ofNat_le.mpr (Finset.card_filter_le s p)) hcard

/-- There are fewer than `2^(q+1)` binary tapes of length `q`. -/
theorem binary_tape_card_lt (q : ℕ) :
    (Fintype.card (Fin q → Bool) : ℤ) < 2 ^ (q + 1) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  exact lt_mul_of_one_lt_right (pow_pos (by norm_num : (0 : ℤ) < 2) q) (by norm_num)

/-- For `q`-bit tapes, modulus `2^(q+1)` suffices to recover any predicate count. -/
theorem binary_sum_emod_eq_filter_card (q : ℕ) (h : (Fin q → Bool) → ℤ)
    (p : (Fin q → Bool) → Prop) [DecidablePred p]
    (hh : ∀ i, h i ≡ (if p i then 1 else 0) [ZMOD 2 ^ (q + 1)]) :
    (∑ i, h i) % (2 ^ (q + 1)) = ((Finset.univ.filter p).card : ℤ) := by
  apply sum_emod_eq_filter_card_of_card_lt Finset.univ h p
  · simpa only [Finset.card_univ] using binary_tape_card_lt q
  · intro i _
    exact hh i

end Toda.Arithmetic

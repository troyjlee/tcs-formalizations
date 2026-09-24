/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityRemoval

/-!
# Cardinality and product accounting for the capacity induction

The target monomial includes the spectator, evaluated at one. Its target
exponent is immaterial. Column removal spends the first profile factor;
deterministic-row removal spends none.
-/

namespace TSPGap.CapacityMatrix

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem card_delete_add_one (c : C) :
    Fintype.card {j // j ≠ c} + 1 = Fintype.card C := by
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun _ : C => (1 : ℕ)) c
  simpa [add_comm] using h.symm

theorem active_card_delete {s c : C} (hsc : s ≠ c) :
    (Finset.univ.erase (⟨s, hsc⟩ : {j // j ≠ c})).card + 1 =
      (Finset.univ.erase s).card := by
  have h := card_delete_add_one c
  have h1 := Finset.card_erase_add_one (Finset.mem_univ s)
  have h2 := Finset.card_erase_add_one
    (Finset.mem_univ (⟨s, hsc⟩ : {j // j ≠ c}))
  simp only [Finset.card_univ] at h1 h2
  omega

/-- The full target monomial; an evaluation of one ignores its exponent. -/
noncomputable def targetValue (κ : C → ℕ) (x : C → ℝ) : ℝ := ∏ j, x j ^ κ j

omit [DecidableEq C] in
theorem targetValue_nonneg (κ : C → ℕ) {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) :
    0 ≤ targetValue κ x := Finset.prod_nonneg (fun j _ => pow_nonneg (hx j) _)

theorem targetValue_erase (κ : C → ℕ) (x : C → ℝ) (c : C) :
    targetValue κ x = x c ^ κ c * targetValue (fun j : {j // j ≠ c} => κ j.val)
      (fun j => x j.val) := Fintype.prod_eq_mul_prod_subtype_ne _ c

/-- Exact monomial factoring, including deterministic spectator rows. -/
theorem targetValue_decrement {κ : C → ℕ} {x : C → ℝ} {s c : C}
    (hs : x s = 1) (hc : c = s ∨ κ c = 1) :
    targetValue κ x = x c * targetValue (fun j => if j = c then κ j - 1 else κ j) x := by
  rw [targetValue_erase κ x c, targetValue_erase _ x c]
  have he : targetValue (fun j : {j // j ≠ c} => if j.val = c then κ j.val - 1 else κ j.val)
      (fun j => x j.val) = targetValue (fun j : {j // j ≠ c} => κ j.val) (fun j => x j.val) := by
    apply Finset.prod_congr rfl
    intro j _
    dsimp only
    rw [if_neg j.property]
  rw [he]
  simp only [ite_true]
  rcases hc with rfl | hc
  · simp [hs]
  · simp [hc]

/-- The ordered factors at the remaining profile levels. -/
noncomputable def profileProduct (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, b (k + 1)

theorem profileProduct_zero (b : ℕ → ℝ) : profileProduct b 0 = 1 := by
  simp [profileProduct]

theorem profileProduct_succ (b : ℕ → ℝ) (n : ℕ) :
    profileProduct b (n + 1) = b 1 * profileProduct (fun k => b (k + 1)) n := by
  simpa [profileProduct, mul_comm, Nat.add_assoc] using
    Finset.prod_range_succ' (fun k => b (k + 1)) n

theorem profileProduct_nonneg {b : ℕ → ℝ} {n : ℕ}
    (hb : ∀ k, 1 ≤ k → k ≤ n → 0 ≤ b k) : 0 ≤ profileProduct b n := by
  exact Finset.prod_nonneg (fun k hk => hb (k + 1) (by omega)
    (by have := Finset.mem_range.mp hk; omega))

theorem profileProduct_le_one {b : ℕ → ℝ} {n : ℕ}
    (hb : ∀ k, 1 ≤ k → k ≤ n → 0 ≤ b k ∧ b k ≤ 1) : profileProduct b n ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro k hk
    exact (hb (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega)).1
  · intro k hk
    exact (hb (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega)).2

end TSPGap.CapacityMatrix

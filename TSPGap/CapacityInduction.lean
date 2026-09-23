/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityActive
import TSPGap.CapacityFactors
import TSPGap.CapacitySpectator

/-!
# The matrix capacity bound with one spectator

The active targets are zero or one; the number of rows is arbitrary.
Induction on rows plus columns covers zero-target normalization,
deterministic rows, and active leaf columns. A spectator of zero mass is
allowed. This is a pointwise product bound, before coefficient extraction.
-/

namespace TSPGap.CapacityMatrix

universe u v

private theorem lower_bound_aux (N : ℕ) :
    ∀ (R : Type u) (C : Type v) [Fintype R] [Fintype C] [DecidableEq C]
      (A : R → C → ℝ) (s : C) (κ : C → ℕ) (b : ℕ → ℝ) (x : C → ℝ),
    Fintype.card R + Fintype.card C ≤ N →
    IsStochastic A → IsRigid A →
    (∀ j, j ≠ s → κ j ≤ 1) →
    (∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s).card → 0 < b k ∧ b k ≤ 1) →
    AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b →
    (∀ j, 0 ≤ x j) → x s = 1 →
    profileProduct b (Finset.univ.erase s).card * targetValue κ x ≤ value A x := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro R C _ _ _ A s κ b x hN hA hrig hκ hb hp hx hs
    have hb1 (c : C) (hcs : c ≠ s) : 0 < b 1 :=
      (hb 1 le_rfl (Finset.card_pos.mpr ⟨c, by simp [hcs]⟩)).1
    cases isEmpty_or_nonempty R with
    | inl hR =>
      letI := hR
      have hk0 (j : C) (hjs : j ≠ s) : κ j = 0 := by
        have h := hp.singleton (c := j) (by simp [hjs])
        simp only [columnSum, Finset.univ_eq_empty, Finset.sum_empty, zero_sub, abs_neg,
          Nat.abs_cast] at h
        have hbj := hb1 j hjs
        by_contra hn
        have hk : (1 : ℝ) ≤ κ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        linarith
      have ht : targetValue κ x = 1 := by
        apply Finset.prod_eq_one
        intro j _
        by_cases hj : j = s
        · simp [hj, hs]
        · simp [hk0 j hj]
      rw [ht, mul_one]
      have hv : value A x = 1 := by simp [value]
      rw [hv]
      exact profileProduct_le_one (fun k hk hn => ⟨(hb k hk hn).1.le, (hb k hk hn).2⟩)
    | inr hR =>
      letI := hR
      by_cases hzero : ∃ c, c ≠ s ∧ κ c = 0
      · obtain ⟨c, hcs, hkc⟩ := hzero
        let C' := {j : C // j ≠ c}
        let s' : C' := ⟨s, hcs.symm⟩
        let B := normalizeEraseColumn A c
        have hmass := hp.singleton (c := c) (by simp [hcs])
        rw [hkc, Nat.cast_zero, sub_zero, abs_le] at hmass
        have hsmall : columnSum A c < 1 := by linarith [hmass.2, hb1 c hcs]
        have hd : Fintype.card C' + 1 = Fintype.card C := card_delete_add_one c
        have ha : (Finset.univ.erase s').card + 1 = (Finset.univ.erase s).card :=
          active_card_delete hcs.symm
        have hκ' : ∀ j : C', j ≠ s' → κ j.val ≤ 1 := by
          intro j hj
          exact hκ j.val (fun h => hj (Subtype.ext h))
        have hb' : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s').card →
            0 < b (k + 1) ∧ b (k + 1) ≤ 1 := by
          intro k hk hn
          exact hb (k + 1) (by omega) (by omega)
        have hi := ih (Fintype.card R + Fintype.card C') (by omega)
          R C' B s' (fun j => κ j.val) (fun k => b (k + 1)) (fun j => x j.val)
          le_rfl (hA.normalizeEraseColumn hsmall) (hrig.normalizeEraseColumn c) hκ' hb'
          (zeroColumn_profile hA hcs hkc hp (hb1 c hcs)) (fun j => hx j.val) hs
        have hprod : profileProduct b (Finset.univ.erase s).card =
            b 1 * profileProduct (fun k => b (k + 1)) (Finset.univ.erase s').card := by
          rw [← ha, profileProduct_succ]
        have ht : targetValue κ x = targetValue (fun j : C' => κ j.val) (fun j => x j.val) := by
          rw [targetValue_erase κ x c, hkc, pow_zero, one_mul]
        calc
          _ = b 1 * (profileProduct (fun k => b (k + 1)) (Finset.univ.erase s').card *
              targetValue (fun j : C' => κ j.val) (fun j => x j.val)) := by rw [hprod, ht]; ring
          _ ≤ b 1 * value B (fun j => x j.val) := mul_le_mul_of_nonneg_left hi (hb1 c hcs).le
          _ ≤ value A x := zeroColumn_value_bound hA (hb1 c hcs) hmass.2 hx
      · have hone : ∀ j, j ≠ s → κ j = 1 := by
          intro j hj
          have hne : κ j ≠ 0 := fun h => hzero ⟨j, hj, h⟩
          have hle := hκ j hj
          omega
        by_cases hrow : ∃ r, rowDegree A r = 1
        · obtain ⟨r, hr⟩ := hrow
          obtain ⟨c, hc, hzc⟩ := hA.leaf_row hr
          let R' := {i : R // i ≠ r}
          let κ' : C → ℕ := fun j => if j = c then κ j - 1 else κ j
          have hd : Fintype.card R' + 1 = Fintype.card R := card_delete_add_one r
          have hκ' : ∀ j, j ≠ s → κ' j ≤ 1 := by
            intro j hj
            have h := hκ j hj
            dsimp [κ']
            split_ifs <;> omega
          have hi := ih (Fintype.card R' + Fintype.card C) (by omega)
            R' C (eraseRow A r) s κ' b x le_rfl (hA.eraseRow r) (hrig.eraseRow r) hκ' hb
            (deterministicRow_profile hc hzc (hone c) hp) hx hs
          have htarget : c = s ∨ κ c = 1 := by
            by_cases h : c = s
            · exact Or.inl h
            · exact Or.inr (hone c h)
          have ht := targetValue_decrement hs (c := c) (κ := κ) htarget
          calc
            _ = x c * (profileProduct b (Finset.univ.erase s).card * targetValue κ' x) := by
              rw [ht]; ring
            _ ≤ x c * value (eraseRow A r) x := mul_le_mul_of_nonneg_left hi (hx c)
            _ = value A x := (value_eq_coord_mul_eraseRow hc hzc x).symm
        · have hn : ∀ r, rowDegree A r ≠ 1 := fun r h => hrow ⟨r, h⟩
          have hcols (j : C) (hjs : j ≠ s) : 0 < rowDegree (fun j i => A i j) j := by
            have h := hp.singleton (c := j) (by simp [hjs])
            rw [hone j hjs, Nat.cast_one, abs_le] at h
            apply columnDegree_pos_of_mass_pos
            linarith [h.1, hb1 j hjs]
          obtain ⟨c, hcs, hleaf⟩ := hrig.active_column_leaf hA s hn hcols
          obtain ⟨r, _, hc⟩ := exists_row_of_column_leaf hleaf
          let R' := {i : R // i ≠ r}
          let C' := {j : C // j ≠ c}
          let s' : C' := ⟨s, hcs.symm⟩
          let B := eraseLeaf A r c
          have hdr : Fintype.card R' + 1 = Fintype.card R := card_delete_add_one r
          have hdc : Fintype.card C' + 1 = Fintype.card C := card_delete_add_one c
          have ha : (Finset.univ.erase s').card + 1 = (Finset.univ.erase s).card :=
            active_card_delete hcs.symm
          have hκ' : ∀ j : C', j ≠ s' → κ j.val ≤ 1 := by
            intro j hj
            exact hκ j.val (fun h => hj (Subtype.ext h))
          have hb' : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s').card →
              0 < b (k + 1) ∧ b (k + 1) ≤ 1 := by
            intro k hk hn
            exact hb (k + 1) (by omega) (by omega)
          have hi := ih (Fintype.card R' + Fintype.card C') (by omega)
            R' C' B s' (fun j => κ j.val) (fun k => b (k + 1)) (fun j => x j.val)
            le_rfl (hA.eraseLeaf hc) (hrig.eraseLeaf r c) hκ' hb'
            (leafColumn_profile hA hcs hc (hone c hcs) hp) (fun j => hx j.val) hs
          have hprod : profileProduct b (Finset.univ.erase s).card =
              b 1 * profileProduct (fun k => b (k + 1)) (Finset.univ.erase s').card := by
            rw [← ha, profileProduct_succ]
          have ht : targetValue κ x = x c *
              targetValue (fun j : C' => κ j.val) (fun j => x j.val) := by
            rw [targetValue_erase κ x c, hone c hcs, pow_one]
          have hmass := hp.singleton (c := c) (by simp [hcs])
          rw [hone c hcs, Nat.cast_one, abs_le] at hmass
          have hbc : b 1 ≤ columnSum A c := by linarith [hmass.1]
          calc
            _ = (b 1 * x c) *
                (profileProduct (fun k => b (k + 1)) (Finset.univ.erase s').card *
                  targetValue (fun j : C' => κ j.val) (fun j => x j.val)) := by
              rw [hprod, ht]; ring
            _ ≤ (b 1 * x c) * value B (fun j => x j.val) :=
              mul_le_mul_of_nonneg_left hi (mul_nonneg (hb1 c hcs).le (hx c))
            _ ≤ value A x := leafColumn_value_bound hA hc hbc hx

/-- The absolute-profile matrix bound. No row-count bound, positive column
mass, or positive evaluation is assumed; only the profile levels are positive. -/
theorem rigid_profile_lower_bound {R : Type u} {C : Type v}
    [Fintype R] [Fintype C] [DecidableEq C] {A : R → C → ℝ}
    (hA : IsStochastic A) (hrig : IsRigid A) (s : C) (κ : C → ℕ) (b : ℕ → ℝ)
    (hκ : ∀ j, j ≠ s → κ j ≤ 1)
    (hb : ∀ k, 1 ≤ k → k ≤ (Finset.univ.erase s).card → 0 < b k ∧ b k ≤ 1)
    (hp : AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b)
    {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) (hs : x s = 1) :
    profileProduct b (Finset.univ.erase s).card * targetValue κ x ≤ value A x := by
  classical
  exact lower_bound_aux (Fintype.card R + Fintype.card C) R C A s κ b x le_rfl
    hA hrig hκ hb hp hx hs

end TSPGap.CapacityMatrix

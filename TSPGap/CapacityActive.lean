/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityRemoval

/-!
# Active-coordinate profiles on smaller matrix types

Deleting a column changes the index type. These adapters transport the
absolute subset-error bounds without identifying a subtype sum with an
ambient sum implicitly. The spectator is retained and never charged.
-/

namespace TSPGap

variable {C : Type*} [DecidableEq C]

omit [DecidableEq C] in
theorem AtMostErrorProfile.congr {e f : C → ℝ} {active : Finset C} {b : ℕ → ℝ}
    (he : AtMostErrorProfile e active b) (hf : ∀ j ∈ active, f j = e j) :
    AtMostErrorProfile f active b := by
  intro S hS hne k hk hka
  convert he S hS hne k hk hka using 1
  congr 1
  exact Finset.sum_congr rfl (fun j hj => hf j (hS hj))

omit [DecidableEq C] in
theorem AtMostErrorProfile.singleton {e : C → ℝ} {active : Finset C} {b : ℕ → ℝ}
    (he : AtMostErrorProfile e active b) {c : C} (hc : c ∈ active) :
    |e c| ≤ 1 - b 1 := by
  classical
  simpa using he {c} (Finset.singleton_subset_iff.mpr hc)
    (Finset.singleton_nonempty c) 1 (by simp)
    (Finset.card_pos.mpr ⟨c, hc⟩)

/-- A deletion interval shifts the profile on the actual surviving subtype. -/
theorem AtMostErrorProfile.subtype_shift {e : C → ℝ} {active : Finset C} {b : ℕ → ℝ}
    (he : AtMostErrorProfile e active b) {c : C} (hc : c ∈ active)
    (f : {j // j ≠ c} → ℝ)
    (hf : ∀ S : Finset {j // j ≠ c}, S ⊆ active.subtype (· ≠ c) →
      ((∑ j ∈ S, e j.val) ≤ (∑ j ∈ S, f j) ∧
        (∑ j ∈ S, f j) ≤ e c + ∑ j ∈ S, e j.val) ∨
      (e c + (∑ j ∈ S, e j.val) ≤ (∑ j ∈ S, f j) ∧
        (∑ j ∈ S, f j) ≤ ∑ j ∈ S, e j.val)) :
    AtMostErrorProfile f (active.subtype (· ≠ c)) (fun k => b (k + 1)) := by
  intro S hS hne k hk hka
  let T := S.map (Function.Embedding.subtype (· ≠ c))
  have hT : T ⊆ active := by
    intro j hj
    obtain ⟨k, hk, hkj⟩ := Finset.mem_map.mp
      (show j ∈ S.map (Function.Embedding.subtype (· ≠ c)) from hj)
    rw [← hkj]
    exact Finset.mem_subtype.mp (hS hk)
  have hcT : c ∉ T := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    exact j.property hj
  have hmap : (active.subtype (· ≠ c)).map
      (Function.Embedding.subtype (· ≠ c)) = active.erase c := by
    rw [Finset.subtype_map]
    ext j
    simp [and_comm]
  have hcard : (active.subtype (· ≠ c)).card + 1 = active.card := by
    have h := congrArg Finset.card hmap
    simp only [Finset.card_map] at h
    have h' := Finset.card_erase_add_one hc
    omega
  have hka' : k + 1 ≤ active.card := by omega
  have hlo := he T hT hne.map (k + 1) (by simpa [T] using hk.trans (Nat.le_succ k)) hka'
  have hhi := he (insert c T) (Finset.insert_subset hc hT)
    (Finset.insert_nonempty _ _) (k + 1) (by simp [hcT, T]; omega) hka'
  rw [Finset.sum_insert hcT] at hhi
  simp only [T, Finset.sum_map, Function.Embedding.coe_subtype] at hlo hhi
  rw [abs_le] at hlo hhi ⊢
  rcases hf S hS with h | h <;> constructor <;> linarith [h.1, h.2]

/-- The spectator in the surviving subtype is precisely the old spectator. -/
theorem active_subtype_eq [Fintype C] {s c : C} (hsc : s ≠ c) :
    (Finset.univ.erase s).subtype (· ≠ c) =
      Finset.univ.erase (⟨s, hsc⟩ : {j // j ≠ c}) := by
  ext j
  simp [Subtype.ext_iff]

namespace CapacityMatrix

variable {R : Type*} [Fintype R] [Fintype C]

theorem zeroColumn_profile {A : R → C → ℝ} (hA : IsStochastic A)
    {s c : C} (hcs : c ≠ s) {κ : C → ℕ} (hκ : κ c = 0)
    {b : ℕ → ℝ}
    (hp : AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b)
    (hb : 0 < b 1) :
    AtMostErrorProfile
      (fun j => columnSum (normalizeEraseColumn A c) j - (κ j.val : ℝ))
      (Finset.univ.erase (⟨s, hcs.symm⟩ : {j // j ≠ c})) (fun k => b (k + 1)) := by
  have hc := hp.singleton (c := c) (by simp [hcs])
  rw [hκ, Nat.cast_zero, sub_zero, abs_le] at hc
  have hsmall : columnSum A c < 1 := by linarith [hc.2]
  rw [← active_subtype_eq hcs.symm]
  exact hp.subtype_shift (by simp [hcs]) _ (fun S _ =>
    Or.inl (zeroColumn_error_interval hA hsmall (fun j => (κ j : ℝ)) (by simp [hκ]) S))

theorem leafColumn_profile [DecidableEq R] {A : R → C → ℝ} (hA : IsStochastic A)
    {r : R} {s c : C} (hcs : c ≠ s) (hc : ∀ i, i ≠ r → A i c = 0)
    {κ : C → ℕ} (hκ : κ c = 1) {b : ℕ → ℝ}
    (hp : AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b) :
    AtMostErrorProfile
      (fun j => columnSum (eraseLeaf A r c) j - (κ j.val : ℝ))
      (Finset.univ.erase (⟨s, hcs.symm⟩ : {j // j ≠ c})) (fun k => b (k + 1)) := by
  rw [← active_subtype_eq hcs.symm]
  exact hp.subtype_shift (by simp [hcs]) _ (fun S _ =>
    Or.inr (leafColumn_error_interval hA hc (fun j => (κ j : ℝ)) (by simp [hκ]) S))

/-- Removing a deterministic row changes the target by the same unit vector.
At the spectator no target condition is required, since it is not measured. -/
theorem deterministicRow_profile [DecidableEq R] {A : R → C → ℝ}
    {r : R} {s c : C} (hc : A r c = 1) (hz : ∀ j, j ≠ c → A r j = 0)
    {κ : C → ℕ} (hκ : c ≠ s → κ c = 1) {b : ℕ → ℝ}
    (hp : AtMostErrorProfile (fun j => columnSum A j - (κ j : ℝ)) (Finset.univ.erase s) b) :
    AtMostErrorProfile
      (fun j => columnSum (eraseRow A r) j - ((if j = c then κ j - 1 else κ j : ℕ) : ℝ))
      (Finset.univ.erase s) b := by
  apply hp.congr
  intro j hj
  rw [columnSum_eraseRow_of_deterministic hc hz]
  by_cases hjc : j = c
  · subst j
    have hcs : c ≠ s := (Finset.mem_erase.mp hj).1
    simp [hκ hcs]
  · simp [hjc]

end CapacityMatrix
end TSPGap

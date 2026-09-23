/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LayerTails
import TSPGap.Conditioning

/-!
# Conditioning on a maximum face

A stable fixed-rank law supported on `|T ∩ F| ≤ m`, conditioned on the top
layer `|T ∩ F| = m`.  Writing `q = m − E[F_T]` for the **deficiency**:

* the face carries mass at least `1 − q`;
* inside the face's own coordinates, `A ⊆ F`, counts only go up, and by at
  most `q` in total: `E[A] ≤ E[A ∣ face] ≤ E[A] + q`;
* outside them, `B ⊆ Fᶜ`, counts only go down, and by at most `q`:
  `E[B] − q ≤ E[B ∣ face] ≤ E[B]`.

Everything is cross-multiplied by the face mass, so no positivity of the face
is needed anywhere and the degenerate case `q ≥ 1` is an instance rather than
an exclusion.

## Where each half comes from

The two directions have entirely different sources.

*Inside* is **layer monotonicity**: for `a ∈ F` the conditional marginal of `a`
is nondecreasing in the layer index, which is `layer_le_mono`.  Summing the
comparison over all layers — the ones above `m` are empty by hypothesis, so
they contribute `0 ≤ 0` — gives `E[a]·faceMass ≤ E[a ∣ face]`.

*Outside* is **negative association**: for `b ∉ F` the events `b ∈ T` and
`m ≤ |T ∩ F|` are both increasing and depend on disjoint coordinate sets, so
Feder–Mihail makes them negatively correlated.  The upper bound follows, and
the *lower* bound is then pure **fixed-rank conservation**: the face fixes
`E[F ∣ face] = m` exactly, so the whole deficiency is absorbed inside `F` and
`Fᶜ` loses exactly `q`.

The two remaining bounds are each the complement of one of these: the inside
*upper* bound is the inside lower bound applied to `F ∖ A`, and the outside
*lower* bound is the outside upper bound applied to `Fᶜ ∖ B`.

## Why one abstraction

Two very different conditionings in KKO22 §5.3 are instances.  Conditioning a
one-hot bundle to be **present** is `F = E`, `m = 1`.  Conditioning three atoms
**simultaneously** to induce trees is `F` the union of their internal edge
sets, `m` the sum of `|atom| − 1`.  ⚠️ The simultaneous form matters:
conditioning the atoms one after another can enlarge the later atoms'
deficiencies, so the three-atom bound must come from a single face.

## Main results

* `faceWeight`, `faceDeficiency`.
* `one_sub_faceDeficiency_le_faceMass`.
* `expCard_face_inside_lower`, `expCard_face_inside_upper`.
* `expCard_face_outside_upper`, `expCard_face_outside_lower`.
* `isRealStableOrZero_genPoly_maxFace`, `isRealStable_genPoly_maxFaceDist` —
  stability of the conditioned law, through the complementary cost.
* `abs_weightMass_face_sub_le`, `abs_condProb_sub_le` — event perturbation.
* `faceDeficiency_union` — additivity over disjoint faces.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The face and its deficiency -/

/-- The cost function that simply counts membership in `F`, so that the
`FaceStability` machinery applies verbatim: `setCost (indicatorCost F) S` is
`|S ∩ F|`. -/
def indicatorCost (F : Finset ι) : ι → ℕ := fun i => if i ∈ F then 1 else 0

omit [Fintype ι] in
theorem setCost_indicatorCost (F S : Finset ι) :
    setCost (indicatorCost F) S = (S ∩ F).card := by
  classical
  simp only [setCost, indicatorCost]
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter]

omit [Fintype ι] in
theorem faceWeight_indicatorCost_apply (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ)
    (S : Finset ι) :
    faceWeight w (indicatorCost F) m S = if (S ∩ F).card = m then w S else 0 := by
  rw [faceWeight, setCost_indicatorCost]

/-- `q = m − E[F_T]`: how far the law falls short of always filling the face. -/
noncomputable def faceDeficiency (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ) : ℝ :=
  (m : ℝ) - expCard w F

open Classical in
theorem weightMass_face (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ)
    (Q : Finset ι → Prop) :
    weightMass (faceWeight w (indicatorCost F) m) Q
      = weightMass w (fun S => Q S ∧ (S ∩ F).card = m) := by
  classical
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [faceWeight_indicatorCost_apply]
  by_cases hc : (S ∩ F).card = m
  · by_cases hQ : Q S <;> simp [hc, hQ]
  · by_cases hQ : Q S <;> simp [hc, hQ]

theorem totalMass_face (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ) :
    totalMass (faceWeight w (indicatorCost F) m)
      = weightMass w (fun S => (S ∩ F).card = m) := by
  rw [← weightMass_true (faceWeight w (indicatorCost F) m), weightMass_face]
  exact weightMass_congr fun S => by simp

/-- On the face the count over `F` is exactly `m`. -/
theorem expCard_face_self (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ) :
    expCard (faceWeight w (indicatorCost F) m) F
      = m * totalMass (faceWeight w (indicatorCost F) m) := by
  classical
  rw [expCard, totalMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [faceWeight_indicatorCost_apply]
  by_cases hc : (S ∩ F).card = m
  · rw [if_pos hc, hc]; ring
  · rw [if_neg hc]; ring

/-! ### The layers above `m` are empty -/

theorem weightMass_projLayer_eq_zero {w : Finset ι → ℝ} {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {j : ℕ} (hj : m < j)
    (Q : Finset ι → Prop) : weightMass (projLayer w F j) Q = 0 := by
  classical
  rw [weightMass_projLayer]
  rw [weightMass_congr_of_support (B := fun _ => False) ?_, weightMass_false]
  intro S hS
  constructor
  · rintro ⟨h1, -⟩
    have := hsup S hS
    omega
  · exact False.elim

theorem totalMass_projLayer_eq_zero {w : Finset ι → ℝ} {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {j : ℕ} (hj : m < j) :
    totalMass (projLayer w F j) = 0 := by
  rw [← weightMass_true (projLayer w F j)]
  exact weightMass_projLayer_eq_zero hsup hj _

theorem totalMass_projLayer_eq_face (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ) :
    totalMass (projLayer w F m) = totalMass (faceWeight w (indicatorCost F) m) := by
  rw [← weightMass_true (projLayer w F m), weightMass_projLayer, totalMass_face]
  exact weightMass_congr fun S => by simp

/-! ### The face carries most of the mass -/

open Classical in
/-- **Face mass.**  Every set off the face wastes at least one unit of the
budget `m`, so the total waste `q` bounds the off-face mass. -/
theorem one_sub_faceDeficiency_le_faceMass {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) :
    1 - faceDeficiency w F m ≤ totalMass (faceWeight w (indicatorCost F) m) := by
  classical
  have hm : (m : ℝ) = ∑ S : Finset ι, w S * (m : ℝ) := by
    rw [← Finset.sum_mul]
    have hs : ∑ S : Finset ι, w S = 1 := htot
    rw [hs, one_mul]
  have hexpand : ∑ S : Finset ι, w S * ((m : ℝ) - ((S ∩ F).card : ℝ))
      = (∑ S : Finset ι, w S * (m : ℝ))
        - ∑ S : Finset ι, w S * ((S ∩ F).card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun S _ => by ring
  have hq : faceDeficiency w F m
      = ∑ S : Finset ι, w S * ((m : ℝ) - ((S ∩ F).card : ℝ)) := by
    rw [faceDeficiency, expCard, hexpand, ← hm]
  have hoff : totalMass w - totalMass (faceWeight w (indicatorCost F) m)
      = ∑ S : Finset ι, w S * (if (S ∩ F).card = m then (0 : ℝ) else 1) := by
    rw [totalMass, totalMass, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [faceWeight_indicatorCost_apply]
    by_cases hc : (S ∩ F).card = m <;> simp [hc]
  have hle : ∑ S : Finset ι, w S * (if (S ∩ F).card = m then (0 : ℝ) else 1)
      ≤ ∑ S : Finset ι, w S * ((m : ℝ) - ((S ∩ F).card : ℝ)) := by
    refine Finset.sum_le_sum fun S _ => ?_
    rcases eq_or_ne (w S) 0 with h0 | h0
    · simp [h0]
    refine mul_le_mul_of_nonneg_left ?_ (hnn S)
    have hb := hsup S h0
    by_cases hc : (S ∩ F).card = m
    · rw [if_pos hc, hc]
      simp
    · rw [if_neg hc]
      have : ((S ∩ F).card : ℝ) + 1 ≤ (m : ℝ) := by
        have : (S ∩ F).card + 1 ≤ m := by omega
        exact_mod_cast this
      linarith
  rw [hq]
  linarith [hoff, hle, htot]

/-! ### Inside the face: counts go up -/

open Classical in
/-- **Inside, lower.**  For `a ∈ F` the conditional marginal is at least the
unconditional one — layer monotonicity summed over all layers. -/
theorem marginal_face_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {a : ι} (haF : a ∈ F) :
    weightMass w (fun S => a ∈ S) * totalMass (faceWeight w (indicatorCost F) m)
      ≤ weightMass (faceWeight w (indicatorCost F) m) (fun S => a ∈ S) := by
  classical
  have hQmono : Monotone (fun S : Finset ι => a ∈ S) := fun _ _ hST h => hST h
  have hQdep : EventDependsOn (fun S : Finset ι => a ∈ S) F := by
    intro S T hST
    constructor
    · intro h
      have : a ∈ S ∩ F := Finset.mem_inter.mpr ⟨h, haF⟩
      exact (Finset.mem_inter.mp (hST ▸ this)).1
    · intro h
      have : a ∈ T ∩ F := Finset.mem_inter.mpr ⟨h, haF⟩
      exact (Finset.mem_inter.mp (hST.symm ▸ this)).1
  -- the layerwise comparison, trivially true above `m`
  have hterm : ∀ j ∈ Finset.range (F.card + 1),
      weightMass (projLayer w F j) (fun S => a ∈ S) * totalMass (projLayer w F m)
        ≤ weightMass (projLayer w F m) (fun S => a ∈ S) * totalMass (projLayer w F j) := by
    intro j _
    rcases le_or_gt j m with hj | hj
    · exact layer_le_mono hst hr hnn htot F hQmono hj
    · rw [weightMass_projLayer_eq_zero hsup hj, totalMass_projLayer_eq_zero hsup hj]
      simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  -- the two partitions
  have hpart₁ : ∑ j ∈ Finset.range (F.card + 1),
      weightMass (projLayer w F j) (fun S => a ∈ S) = weightMass w (fun S => a ∈ S) := by
    have hlayer : ∀ j ∈ Finset.range (F.card + 1),
        weightMass (projLayer w F j) (fun S => a ∈ S)
          = weightMass w (fun S => (S ∩ F).card = j ∧ a ∈ S) := fun j _ =>
      weightMass_projLayer_of_dependsOn w j hQdep
    rw [Finset.sum_congr rfl hlayer, ← weightMass_layer_partition w F (fun S => a ∈ S)]
  have hpart₂ : ∑ j ∈ Finset.range (F.card + 1), totalMass (projLayer w F j) = 1 := by
    have hlayer : ∀ j ∈ Finset.range (F.card + 1), totalMass (projLayer w F j)
        = weightMass w (fun S => (S ∩ F).card = j ∧ True) := by
      intro j _
      rw [← weightMass_true (projLayer w F j), weightMass_projLayer]
    rw [Finset.sum_congr rfl hlayer, ← weightMass_layer_partition w F (fun _ => True),
      weightMass_true, htot]
  rw [hpart₁, hpart₂, mul_one, totalMass_projLayer_eq_face,
    weightMass_projLayer_of_dependsOn w m hQdep] at hsum
  rw [weightMass_face]
  exact le_trans hsum (le_of_eq (weightMass_congr fun S => and_comm))

open Classical in
/-- **Inside, lower**, summed over a set of face coordinates. -/
theorem expCard_face_inside_lower {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {A : Finset ι} (hA : A ⊆ F) :
    expCard w A * totalMass (faceWeight w (indicatorCost F) m)
      ≤ expCard (faceWeight w (indicatorCost F) m) A := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.sum_mul]
  exact Finset.sum_le_sum fun a ha =>
    marginal_face_ge hst hr hnn htot hsup (hA ha)

/-! ### Outside the face: counts go down -/

open Classical in
/-- **Outside, upper.**  For `b ∉ F`, `b ∈ T` and `m ≤ |T ∩ F|` are increasing
events on disjoint coordinate sets, hence negatively correlated. -/
theorem marginal_face_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {b : ι} (hbF : b ∉ F) :
    weightMass (faceWeight w (indicatorCost F) m) (fun S => b ∈ S)
      ≤ weightMass w (fun S => b ∈ S) * totalMass (faceWeight w (indicatorCost F) m) := by
  classical
  have hmA : Monotone (fun S : Finset ι => b ∈ S) := fun _ _ hST h => hST h
  have hmB : Monotone (fun S : Finset ι => m ≤ (S ∩ F).card) := by
    intro S T hST h
    exact le_trans h (Finset.card_le_card (Finset.inter_subset_inter hST le_rfl))
  have hdA : EventDependsOn (fun S : Finset ι => b ∈ S) {b} := by
    intro S T hST
    constructor
    · intro h
      have : b ∈ S ∩ {b} := Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self b⟩
      exact (Finset.mem_inter.mp (hST ▸ this)).1
    · intro h
      have : b ∈ T ∩ {b} := Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self b⟩
      exact (Finset.mem_inter.mp (hST.symm ▸ this)).1
  have hdB : EventDependsOn (fun S : Finset ι => m ≤ (S ∩ F).card) F := by
    intro S T hST
    change m ≤ (S ∩ F).card ↔ m ≤ (T ∩ F).card
    rw [hST]
  have hdisj : Disjoint ({b} : Finset ι) F :=
    Finset.disjoint_singleton_left.mpr hbF
  have hNC := increasing_events_negCorrelation Finset.univ w r
    (fun S => b ∈ S) (fun S => m ≤ (S ∩ F).card) {b} F hnn hr
    (fun S _ => Finset.subset_univ S) (rayleighNonneg_genPoly hst) hmA hmB hdA hdB
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj
  unfold NegCorrelated at hNC
  rw [htot, mul_one] at hNC
  -- on the support the two face descriptions agree
  have hconv : ∀ Q : Finset ι → Prop,
      weightMass w (fun S => Q S ∧ m ≤ (S ∩ F).card)
        = weightMass w (fun S => Q S ∧ (S ∩ F).card = m) := by
    intro Q
    refine weightMass_congr_of_support fun S hS => ?_
    have := hsup S hS
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  rw [hconv (fun S => b ∈ S)] at hNC
  have hB : weightMass w (fun S => m ≤ (S ∩ F).card)
      = totalMass (faceWeight w (indicatorCost F) m) := by
    rw [totalMass_face]
    refine weightMass_congr_of_support fun S hS => ?_
    have := hsup S hS
    constructor
    · intro h; omega
    · intro h; omega
  rw [hB] at hNC
  rwa [weightMass_face]

open Classical in
/-- **Outside, upper**, summed over a set of non-face coordinates. -/
theorem expCard_face_outside_upper {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {B : Finset ι} (hB : B ⊆ Fᶜ) :
    expCard (faceWeight w (indicatorCost F) m) B
      ≤ expCard w B * totalMass (faceWeight w (indicatorCost F) m) := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.sum_mul]
  exact Finset.sum_le_sum fun b hb =>
    marginal_face_le hst hr hnn htot hsup (Finset.mem_compl.mp (hB hb))

/-! ### The two complementary bounds -/

open Classical in
/-- **Inside, upper.**  The whole deficiency is absorbed inside `F`, so no
subset of `F` can gain more than `q`. -/
theorem expCard_face_inside_upper {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {A : Finset ι} (hA : A ⊆ F) :
    expCard (faceWeight w (indicatorCost F) m) A
      ≤ (expCard w A + faceDeficiency w F m) * totalMass (faceWeight w (indicatorCost F) m) := by
  have hsd := expCard_sdiff_of_subset (faceWeight w (indicatorCost F) m) hA
  have hsd' := expCard_sdiff_of_subset w hA
  have hlow := expCard_face_inside_lower hst hr hnn htot hsup
    (A := F \ A) Finset.sdiff_subset
  have hself := expCard_face_self w F m
  rw [hsd'] at hlow
  rw [hsd, hself] at hlow
  have hring : (expCard w A + ((m : ℝ) - expCard w F))
        * totalMass (faceWeight w (indicatorCost F) m)
      = (m : ℝ) * totalMass (faceWeight w (indicatorCost F) m)
        - (expCard w F - expCard w A) * totalMass (faceWeight w (indicatorCost F) m) := by
    ring
  rw [faceDeficiency, hring]
  linarith [hlow]

open Classical in
/-- **Outside, lower.**  Fixed-rank conservation: the face pins `E[F] = m`, so
`Fᶜ` loses exactly `q`, and no subset of it can lose more. -/
theorem expCard_face_outside_lower {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) {B : Finset ι} (hB : B ⊆ Fᶜ) :
    (expCard w B - faceDeficiency w F m) * totalMass (faceWeight w (indicatorCost F) m)
      ≤ expCard (faceWeight w (indicatorCost F) m) B := by
  classical
  -- conservation on both laws
  have hunion : F ∪ Fᶜ = (Finset.univ : Finset ι) := Finset.union_compl F
  have hdisj : Disjoint F (Fᶜ : Finset ι) := disjoint_compl_right
  have hcons : expCard w F + expCard w Fᶜ = r := by
    have h1 := expCard_union_of_disjoint w hdisj
    rw [hunion, expCard_univ hr, htot, mul_one] at h1
    linarith
  have hconsF : expCard (faceWeight w (indicatorCost F) m) F
        + expCard (faceWeight w (indicatorCost F) m) Fᶜ
      = r * totalMass (faceWeight w (indicatorCost F) m) := by
    have h1 := expCard_union_of_disjoint (faceWeight w (indicatorCost F) m) hdisj
    rw [hunion, expCard_univ (fixedRankWeight_faceWeight hr (indicatorCost F) m)] at h1
    linarith
  have hself := expCard_face_self w F m
  have hsd := expCard_sdiff_of_subset (faceWeight w (indicatorCost F) m) hB
  have hsd' := expCard_sdiff_of_subset w hB
  have hup := expCard_face_outside_upper hst hr hnn htot hsup
    (B := Fᶜ \ B) Finset.sdiff_subset
  have hFc : expCard w Fᶜ = (r : ℝ) - expCard w F := by linarith
  have hfaceFc : expCard (faceWeight w (indicatorCost F) m) Fᶜ
      = (r : ℝ) * totalMass (faceWeight w (indicatorCost F) m)
        - (m : ℝ) * totalMass (faceWeight w (indicatorCost F) m) := by linarith
  rw [hsd, hsd', hFc, hfaceFc] at hup
  have hring : (expCard w B - ((m : ℝ) - expCard w F))
        * totalMass (faceWeight w (indicatorCost F) m)
      = ((r : ℝ) * totalMass (faceWeight w (indicatorCost F) m)
          - (m : ℝ) * totalMass (faceWeight w (indicatorCost F) m))
        - ((r : ℝ) - expCard w F - expCard w B)
          * totalMass (faceWeight w (indicatorCost F) m) := by ring
  rw [faceDeficiency, hring]
  linarith [hup]

/-! ### Stability of the conditioned law

⚠️ `isRealStableOrZero_genPoly_faceWeight` conditions on a **minimum**-cost
face, so it does *not* apply to `indicatorCost F` here: our `m` is a maximum.
Stability transfers through the **complementary cost** instead.  On rank-`r`
support

`|S ∩ F| = m  ↔  |S ∖ F| = r − m`,

and `r − m` genuinely *is* the minimum of `|S ∖ F|`, because `|S ∩ F| ≤ m`.
For `m > r` the maximum face is empty, so positive face mass already forces
`m ≤ r`. -/

theorem card_inter_add_card_inter_compl (S F : Finset ι) :
    (S ∩ F).card + (S ∩ Fᶜ).card = S.card := by
  classical
  have hdisj : Disjoint (S ∩ F) (S ∩ Fᶜ) :=
    Finset.disjoint_left.mpr fun x hx hx' =>
      (Finset.mem_compl.mp (Finset.mem_inter.mp hx').2) (Finset.mem_inter.mp hx).2
  have hunion : (S ∩ F) ∪ (S ∩ Fᶜ) = S := by
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- **The maximum face is a minimum face for the complementary cost.** -/
theorem faceWeight_max_eq_compl {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (F : Finset ι) {m : ℕ} (hmr : m ≤ r) :
    faceWeight w (indicatorCost F) m = faceWeight w (indicatorCost Fᶜ) (r - m) := by
  classical
  funext S
  rw [faceWeight_indicatorCost_apply, faceWeight_indicatorCost_apply]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · split <;> split <;> simp [h0]
  · have hcard := hr S h0
    have hsplit := card_inter_add_card_inter_compl S F
    rw [hcard] at hsplit
    by_cases hc : (S ∩ F).card = m
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega)]

/-- Positive face mass forces `m ≤ r`. -/
theorem le_rank_of_faceMass_pos {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) {F : Finset ι} {m : ℕ}
    (hmass : 0 < totalMass (faceWeight w (indicatorCost F) m)) : m ≤ r := by
  classical
  by_contra hc
  refine absurd ?_ (ne_of_gt hmass)
  rw [totalMass]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [faceWeight_indicatorCost_apply]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · split <;> simp [h0]
  · have hcard := hr S h0
    have hle : (S ∩ F).card ≤ r := by
      rw [← hcard]; exact Finset.card_le_card Finset.inter_subset_left
    rw [if_neg (by omega)]

theorem isRealStableOrZero_genPoly_maxFace {w : Finset ι → ℝ} {r : ℕ}
    {F : Finset ι} {m : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m) :
    IsRealStableOrZero (genPoly (faceWeight w (indicatorCost F) m)) := by
  classical
  by_cases hmr : m ≤ r
  · rw [faceWeight_max_eq_compl hr F hmr]
    refine isRealStableOrZero_genPoly_faceWeight hst hr hnn ?_
    intro S hS
    rw [setCost_indicatorCost]
    have hcard := hr S hS
    have hsplit := card_inter_add_card_inter_compl S F
    rw [hcard] at hsplit
    have := hsup S hS
    omega
  · left
    have hzero : faceWeight w (indicatorCost F) m = fun _ => (0 : ℝ) := by
      funext S
      rw [faceWeight_indicatorCost_apply]
      rcases eq_or_ne (w S) 0 with h0 | h0
      · split <;> simp [h0]
      · have hcard := hr S h0
        have hle : (S ∩ F).card ≤ r := by
          rw [← hcard]; exact Finset.card_le_card Finset.inter_subset_left
        rw [if_neg (by omega)]
    rw [hzero, genPoly]
    simp

/-- **Stability of the normalized maximum-face law.** -/
theorem isRealStable_genPoly_maxFaceDist {w : Finset ι → ℝ} {r : ℕ}
    {F : Finset ι} {m : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    (hsup : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight w (indicatorCost F) m)) :
    IsRealStable (genPoly (faceDist w (indicatorCost F) m)) := by
  classical
  have hmr : m ≤ r := le_rank_of_faceMass_pos hr hmass
  have hmin : ∀ S, w S ≠ 0 → r - m ≤ setCost (indicatorCost Fᶜ) S := by
    intro S hS
    rw [setCost_indicatorCost]
    have hcard := hr S hS
    have hsplit := card_inter_add_card_inter_compl S F
    rw [hcard] at hsplit
    have := hsup S hS
    omega
  have heq : faceDist w (indicatorCost F) m = faceDist w (indicatorCost Fᶜ) (r - m) := by
    funext S
    rw [faceDist, faceDist, faceWeight_max_eq_compl hr F hmr]
  rw [heq]
  refine isRealStable_genPoly_faceDist hst hr hnn hmin ?_
  rw [← faceWeight_max_eq_compl hr F hmr]
  exact hmass

/-! ### Event perturbation -/

open Classical in
/-- **Conditioning moves any event by at most `M(1 − M)`.**  Needs only a
normalized nonnegative law: no stability, no rank. -/
theorem abs_weightMass_face_sub_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) (F : Finset ι) (m : ℕ) (Q : Finset ι → Prop) :
    |weightMass (faceWeight w (indicatorCost F) m) Q
        - totalMass (faceWeight w (indicatorCost F) m) * weightMass w Q|
      ≤ totalMass (faceWeight w (indicatorCost F) m)
          * (1 - totalMass (faceWeight w (indicatorCost F) m)) := by
  classical
  have hface := weightMass_face w F m Q
  have hMdef := totalMass_face w F m
  have hcell : weightMass w (fun S => Q S ∧ ¬ ((S ∩ F).card = m))
      = weightMass w Q - weightMass w (fun S => Q S ∧ (S ∩ F).card = m) :=
    weightMass_and_not w Q (fun S => (S ∩ F).card = m)
  have ha0 : 0 ≤ weightMass w (fun S => Q S ∧ (S ∩ F).card = m) :=
    weightMass_nonneg hnn _
  have hb0 : 0 ≤ weightMass w (fun S => Q S ∧ ¬ ((S ∩ F).card = m)) :=
    weightMass_nonneg hnn _
  have haM : weightMass w (fun S => Q S ∧ (S ∩ F).card = m)
      ≤ weightMass w (fun S => (S ∩ F).card = m) :=
    weightMass_mono hnn fun S hS => hS.2
  have hbM : weightMass w (fun S => Q S ∧ ¬ ((S ∩ F).card = m))
      ≤ weightMass w (fun S => ¬ ((S ∩ F).card = m)) :=
    weightMass_mono hnn fun S hS => hS.2
  have hnot : weightMass w (fun S => ¬ ((S ∩ F).card = m))
      = 1 - weightMass w (fun S => (S ∩ F).card = m) := by
    rw [weightMass_not w (fun S => (S ∩ F).card = m), htot]
  have hM0 : 0 ≤ weightMass w (fun S => (S ∩ F).card = m) := weightMass_nonneg hnn _
  have hM1 : weightMass w (fun S => (S ∩ F).card = m) ≤ 1 := by
    rw [← htot]; exact weightMass_le_totalMass hnn _
  rw [hface, hMdef, abs_le]
  constructor
  · nlinarith [ha0, hb0, haM, hbM, hM0, hM1, hcell, hnot]
  · nlinarith [ha0, hb0, haM, hbM, hM0, hM1, hcell, hnot]

open Classical in
/-- The normalized form: conditional probabilities move by at most the
deficiency. -/
theorem abs_condProb_sub_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) {F : Finset ι} {m : ℕ} {q : ℝ}
    (hq : 1 - q ≤ totalMass (faceWeight w (indicatorCost F) m))
    (hmass : 0 < totalMass (faceWeight w (indicatorCost F) m))
    (Q : Finset ι → Prop) :
    |weightMass (faceWeight w (indicatorCost F) m) Q
        / totalMass (faceWeight w (indicatorCost F) m) - weightMass w Q| ≤ q := by
  have hbase := abs_weightMass_face_sub_le hnn htot F m Q
  rw [abs_le] at hbase
  have hne : totalMass (faceWeight w (indicatorCost F) m) ≠ 0 := ne_of_gt hmass
  have hdiv : (weightMass (faceWeight w (indicatorCost F) m) Q
        - totalMass (faceWeight w (indicatorCost F) m) * weightMass w Q)
        / totalMass (faceWeight w (indicatorCost F) m)
      = weightMass (faceWeight w (indicatorCost F) m) Q
        / totalMass (faceWeight w (indicatorCost F) m) - weightMass w Q := by
    rw [sub_div, mul_div_cancel_left₀ _ hne]
  have hslack : 0 ≤ totalMass (faceWeight w (indicatorCost F) m) - 1 + q := by linarith
  rw [abs_le, ← hdiv]
  constructor
  · rw [le_div_iff₀ hmass]
    nlinarith [hbase.1, hmass, mul_nonneg hmass.le hslack]
  · rw [div_le_iff₀ hmass]
    nlinarith [hbase.2, hmass, mul_nonneg hmass.le hslack]

/-! ### Additivity of the deficiency -/

theorem faceDeficiency_union {w : Finset ι → ℝ} {F₁ F₂ : Finset ι}
    (h : Disjoint F₁ F₂) (m₁ m₂ : ℕ) :
    faceDeficiency w (F₁ ∪ F₂) (m₁ + m₂)
      = faceDeficiency w F₁ m₁ + faceDeficiency w F₂ m₂ := by
  rw [faceDeficiency, faceDeficiency, faceDeficiency, expCard_union_of_disjoint w h]
  push_cast
  ring

end TSPGap

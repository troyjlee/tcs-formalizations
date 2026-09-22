/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MaxFace
import TSPGap.ThreeAtomFace
import TSPGap.TreeDistBridge

/-!
# The nested face of KKO21 Lemma 5.16

Lemma 5.16 conditions a max-entropy tree law on `u`, `v`, `W = S ∖ u` and
`S` inducing trees, where `v ⊆ W ⊂ S` and `u ⊂ S` are nested — not disjoint
atoms, so the two- and three-atom faces do not apply.  The four events are
one **maximum face** of the *multiplicity cost*

`c(e) = 𝟙_{E(u)}(e) + 𝟙_{E(v)}(e) + 𝟙_{E(W)}(e) + 𝟙_{E(S)}(e)`

at the budget `Σ (|X| − 1)`: on a spanning tree every summand is capped by
the forest bound, so the sum reaches the budget iff every summand does, i.e.
iff all four induce trees (`setCost_nestedCost_eq_iff`).

The general facts, for any integer cost `c ≤ C` on a fixed-rank weight:

* the maximum face of `c` is the minimum face of the negated cost `C − c`
  (`faceWeight_eq_compl_cost`), so `FaceStability`'s minimum-face theorem
  gives **stability** of the normalized maximum-face law
  (`isRealStable_genPoly_faceDist_max`);
* the face carries mass at least `1 − (m − E[c])`
  (`one_sub_costDeficiency_le_faceMass`);
* **faces iterate**: the face of a face is the face of the summed cost
  (`faceWeight_faceWeight`, `faceDist_faceDist`), so the nested law is also
  the result of four successive indicator-face conditionings — which is how
  the marginal bridges of `MaxFace` reach it.

At a tree law with subtour-LP marginals the deficiency is exact:
`Σ_X (x(δ(X))/2 − 1)` (`costDeficiency_nested_eq`).
-/

namespace TSPGap
open Finset

/-! ### General integer costs -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The expected cost `E[c(T)]`. -/
noncomputable def expCost (w : Finset ι → ℝ) (c : ι → ℕ) : ℝ :=
  ∑ S, w S * (setCost c S : ℝ)

/-- The deficiency `m − E[c(T)]` of the cost-`m` face. -/
noncomputable def costDeficiency (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) : ℝ :=
  (m : ℝ) - expCost w c

omit [Fintype ι] [DecidableEq ι] in
theorem faceWeight_apply (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) (S : Finset ι) :
    faceWeight w c m S = if setCost c S = m then w S else 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem setCost_add (c₁ c₂ : ι → ℕ) (S : Finset ι) :
    setCost (fun i => c₁ i + c₂ i) S = setCost c₁ S + setCost c₂ S :=
  Finset.sum_add_distrib

/-- **Face mass for a general cost**: every set off the face wastes at least
one unit of the budget. -/
theorem one_sub_costDeficiency_le_faceMass {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {c : ι → ℕ} {m : ℕ}
    (hsup : ∀ S, w S ≠ 0 → setCost c S ≤ m) :
    1 - costDeficiency w c m ≤ totalMass (faceWeight w c m) := by
  classical
  have hm : (m : ℝ) = ∑ S : Finset ι, w S * (m : ℝ) := by
    rw [← Finset.sum_mul]
    have hs : ∑ S : Finset ι, w S = 1 := htot
    rw [hs, one_mul]
  have hq : costDeficiency w c m
      = ∑ S : Finset ι, w S * ((m : ℝ) - (setCost c S : ℝ)) := by
    rw [costDeficiency, expCost]
    conv_lhs => rw [hm]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun S _ => by ring
  have hoff : totalMass w - totalMass (faceWeight w c m)
      = ∑ S : Finset ι, w S * (if setCost c S = m then (0 : ℝ) else 1) := by
    rw [totalMass, totalMass, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [faceWeight_apply]
    by_cases hc : setCost c S = m <;> simp [hc]
  have hle : ∑ S : Finset ι, w S * (if setCost c S = m then (0 : ℝ) else 1)
      ≤ ∑ S : Finset ι, w S * ((m : ℝ) - (setCost c S : ℝ)) := by
    refine Finset.sum_le_sum fun S _ => ?_
    rcases eq_or_ne (w S) 0 with h0 | h0
    · simp [h0]
    refine mul_le_mul_of_nonneg_left ?_ (hnn S)
    have hb := hsup S h0
    by_cases hc : setCost c S = m
    · rw [if_pos hc, hc]
      simp
    · rw [if_neg hc]
      have : (setCost c S : ℝ) + 1 ≤ (m : ℝ) := by
        have : setCost c S + 1 ≤ m := by omega
        exact_mod_cast this
      linarith
  rw [hq]
  linarith [hoff, hle, htot]

omit [Fintype ι] [DecidableEq ι] in
/-- A cost bounded by `C` and its negation sum to `C · |S|`. -/
theorem setCost_compl_cost {c : ι → ℕ} {C : ℕ} (hC : ∀ i, c i ≤ C) (S : Finset ι) :
    setCost (fun i => C - c i) S + setCost c S = C * S.card := by
  unfold setCost
  rw [← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hC i), Finset.sum_const, smul_eq_mul,
    mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- **The maximum face is the minimum face of the negated cost** on a
fixed-rank weight. -/
theorem faceWeight_eq_compl_cost {w : Finset ι → ℝ} {r : ℕ} (hr : FixedRankWeight r w)
    {c : ι → ℕ} {C : ℕ} (hC : ∀ i, c i ≤ C) {m : ℕ} (hm : m ≤ C * r) :
    faceWeight w c m = faceWeight w (fun i => C - c i) (C * r - m) := by
  funext S
  rw [faceWeight_apply, faceWeight_apply]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · split <;> split <;> simp [h0]
  · have hcard := hr S h0
    have hs := setCost_compl_cost hC S
    rw [hcard] at hs
    by_cases hc : setCost c S = m
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega)]

omit [DecidableEq ι] in
theorem exists_of_faceMass_pos {w : Finset ι → ℝ} {c : ι → ℕ} {m : ℕ}
    (h : 0 < totalMass (faceWeight w c m)) : ∃ S, w S ≠ 0 ∧ setCost c S = m := by
  obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  rw [faceWeight_apply] at hS
  split at hS
  · exact ⟨S, hS, ‹_›⟩
  · exact absurd rfl hS

/-- **Stability of the normalized maximum-face law of a bounded integer
cost.** -/
theorem isRealStable_genPoly_faceDist_max {w : Finset ι → ℝ} {r : ℕ}
    {c : ι → ℕ} {C : ℕ} {m : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w) (hC : ∀ i, c i ≤ C)
    (hsup : ∀ S, w S ≠ 0 → setCost c S ≤ m)
    (hmass : 0 < totalMass (faceWeight w c m)) :
    IsRealStable (genPoly (faceDist w c m)) := by
  have hm : m ≤ C * r := by
    obtain ⟨S, hS, hc⟩ := exists_of_faceMass_pos hmass
    have := setCost_compl_cost hC S
    rw [hr S hS] at this
    omega
  have heq := faceWeight_eq_compl_cost hr hC hm
  have hmin : ∀ S, w S ≠ 0 → C * r - m ≤ setCost (fun i => C - c i) S := by
    intro S hS
    have h1 := setCost_compl_cost hC S
    rw [hr S hS] at h1
    have h2 := hsup S hS
    omega
  have hmass' : 0 < totalMass (faceWeight w (fun i => C - c i) (C * r - m)) := by
    rw [← heq]; exact hmass
  have := isRealStable_genPoly_faceDist hst hr hnn hmin hmass'
  unfold faceDist at this ⊢
  rw [heq]
  exact this

/-! ### Faces iterate -/

omit [Fintype ι] [DecidableEq ι] in
/-- The face of a face is the face of the summed cost, on a support where
both costs are capped. -/
theorem faceWeight_faceWeight (w : Finset ι → ℝ) {c₁ c₂ : ι → ℕ} {m₁ m₂ : ℕ}
    (hsup : ∀ S, w S ≠ 0 → setCost c₁ S ≤ m₁ ∧ setCost c₂ S ≤ m₂) :
    faceWeight (faceWeight w c₁ m₁) c₂ m₂
      = faceWeight w (fun i => c₁ i + c₂ i) (m₁ + m₂) := by
  funext S
  rw [faceWeight_apply, faceWeight_apply, faceWeight_apply, setCost_add]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · obtain ⟨h1, h2⟩ := hsup S h0
    by_cases e1 : setCost c₁ S = m₁
    · by_cases e2 : setCost c₂ S = m₂
      · rw [if_pos e2, if_pos e1, if_pos (by omega)]
      · rw [if_neg e2, if_neg (by omega)]
    · by_cases e2 : setCost c₂ S = m₂
      · rw [if_pos e2, if_neg e1, if_neg (by omega)]
      · rw [if_neg e2, if_neg (by omega)]

/-- **The face law of a face law is the face law of the summed cost.** -/
theorem faceDist_faceDist (w : Finset ι → ℝ) {c₁ c₂ : ι → ℕ} {m₁ m₂ : ℕ}
    (hsup : ∀ S, w S ≠ 0 → setCost c₁ S ≤ m₁ ∧ setCost c₂ S ≤ m₂)
    (hM : totalMass (faceWeight w c₁ m₁) ≠ 0) :
    faceDist (faceDist w c₁ m₁) c₂ m₂ = faceDist w (fun i => c₁ i + c₂ i) (m₁ + m₂) := by
  have h1 : faceDist w c₁ m₁
      = fun S => (totalMass (faceWeight w c₁ m₁))⁻¹ * faceWeight w c₁ m₁ S := by
    funext S; rw [faceDist, div_eq_inv_mul]
  rw [h1, faceDist_smul (inv_ne_zero hM)]
  unfold faceDist
  rw [faceWeight_faceWeight w hsup]

end General

/-! ### The nested cost of Lemma 5.16 -/

section Nested

variable {n : ℕ}

/-- The multiplicity cost of the four nested sets `u`, `v`, `W`, `S`. -/
def nestedCost (u v W S : Finset (Fin n)) : Sym2 (Fin n) → ℕ := fun e =>
  indicatorCost (internalEdges u) e + indicatorCost (internalEdges v) e
    + indicatorCost (internalEdges W) e + indicatorCost (internalEdges S) e

/-- The budget `Σ (|X| − 1)`. -/
def nestedBudget (u v W S : Finset (Fin n)) : ℕ :=
  (u.card - 1) + (v.card - 1) + (W.card - 1) + (S.card - 1)

theorem nestedCost_le_four (u v W S : Finset (Fin n)) (e : Sym2 (Fin n)) :
    nestedCost u v W S e ≤ 4 := by
  unfold nestedCost indicatorCost
  split_ifs <;> omega

theorem setCost_nestedCost (u v W S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    setCost (nestedCost u v W S) T
      = (internalEdges u ∩ T).card + (internalEdges v ∩ T).card
        + (internalEdges W ∩ T).card + (internalEdges S ∩ T).card := by
  have h : ∀ F : Finset (Sym2 (Fin n)), ∑ e ∈ T, indicatorCost F e = (F ∩ T).card := by
    intro F
    rw [Finset.inter_comm]
    exact setCost_indicatorCost F T
  unfold setCost nestedCost
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, h, h, h, h]

/-- A spanning tree meets the nested cost within its budget. -/
theorem setCost_nestedCost_le {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    {u v W S : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty) (hW : W.Nonempty)
    (hS : S.Nonempty) : setCost (nestedCost u v W S) T ≤ nestedBudget u v W S := by
  rw [setCost_nestedCost]
  unfold nestedBudget
  have h1 := card_internal_inter_add_one_le hT hu
  have h2 := card_internal_inter_add_one_le hT hv
  have h3 := card_internal_inter_add_one_le hT hW
  have h4 := card_internal_inter_add_one_le hT hS
  omega

/-- **The nested face is exactly the four tree events.** -/
theorem setCost_nestedCost_eq_iff {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    {u v W S : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty) (hW : W.Nonempty)
    (hS : S.Nonempty) :
    setCost (nestedCost u v W S) T = nestedBudget u v W S
      ↔ InducesTreeOn u T ∧ InducesTreeOn v T ∧ InducesTreeOn W T ∧ InducesTreeOn S T := by
  rw [setCost_nestedCost, inducesTreeOn_iff_card hT, inducesTreeOn_iff_card hT,
    inducesTreeOn_iff_card hT, inducesTreeOn_iff_card hT]
  unfold nestedBudget
  have h1 := card_internal_inter_add_one_le hT hu
  have h2 := card_internal_inter_add_one_le hT hv
  have h3 := card_internal_inter_add_one_le hT hW
  have h4 := card_internal_inter_add_one_le hT hS
  omega

/-- The expected nested cost is the sum of the four internal expected counts. -/
theorem expCost_nestedCost (w : Finset (Sym2 (Fin n)) → ℝ) (u v W S : Finset (Fin n)) :
    expCost w (nestedCost u v W S)
      = expCard w (internalEdges u) + expCard w (internalEdges v)
        + expCard w (internalEdges W) + expCard w (internalEdges S) := by
  unfold expCost expCard
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [setCost_nestedCost, Finset.inter_comm _ T, Finset.inter_comm _ T, Finset.inter_comm _ T,
    Finset.inter_comm _ T]
  push_cast
  ring

/-- **The nested deficiency is exact** at a tree law with subtour-LP marginals:
`Σ_X (x(δ(X))/2 − 1)`. -/
theorem costDeficiency_nested_eq {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) {u v W S : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty)
    (hW : W.Nonempty) (hS : S.Nonempty) (hu0 : AvoidsRootEdge e₀ u) (hv0 : AvoidsRootEdge e₀ v)
    (hW0 : AvoidsRootEdge e₀ W) (hS0 : AvoidsRootEdge e₀ S) :
    costDeficiency μ.prob (nestedCost u v W S) (nestedBudget u v W S)
      = (cutSum x u / 2 - 1) + (cutSum x v / 2 - 1) + (cutSum x W / 2 - 1)
        + (cutSum x S / 2 - 1) := by
  have hu1 : 1 ≤ u.card := Finset.card_pos.mpr hu
  have hv1 : 1 ≤ v.card := Finset.card_pos.mpr hv
  have hW1 : 1 ≤ W.card := Finset.card_pos.mpr hW
  have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hS
  rw [costDeficiency, expCost_nestedCost, expCard_prob_internalEdges, expCard_prob_internalEdges,
    expCard_prob_internalEdges, expCard_prob_internalEdges,
    sum_internalEdges_eq_of_avoids hx hu0, sum_internalEdges_eq_of_avoids hx hv0,
    sum_internalEdges_eq_of_avoids hx hW0, sum_internalEdges_eq_of_avoids hx hS0]
  unfold nestedBudget
  push_cast [Nat.cast_sub hu1, Nat.cast_sub hv1, Nat.cast_sub hW1, Nat.cast_sub hS1]
  ring

end Nested

end TSPGap

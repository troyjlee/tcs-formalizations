/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma516Tails
import TSPGap.Lemma516Decay
import TSPGap.Lemma516Newton
import TSPGap.ThreeCell
import TSPGap.LayerTails
import TSPGap.Lemma527Tools
import TSPGap.Lemma527Generic
import TSPGap.BundleProjection

/-!
# The analytic kernel of KKO21 Lemma 5.16

Under the nested law `ν` (`u`, `v`, `W`, `S` trees), with `A := δ↑(u)` and
`B := δ(v)` (disjoint, `B_T ≥ 1` on the support), KKO's `X = A_T`,
`Y = B_T − 1` satisfy `E[X] ∈ [0.5 + 9ε₂ − ε_η/2, 1 + ε_η]`,
`E[Y] ∈ [0.5 + 9ε₂ − 4.5ε_η, 1.5 − 9ε₂ + 4ε_η]`, and the claim is
`P[X = Y = 1] = P[A_T = 1 ∧ B_T = 2] ≥ 6ε₂`.  With `Z := A ∪ B` (baseline `1`):

* **Case 1**, `P[Z_T = 3] ≥ 73ε₂`: the shifted Corollary 5.5
  (`three_cell_bound_shifted` at baselines `(0, 1)`) with the one-cell tails
  `P[A ≤ 1] ≥ 0.4999`, `P[B ≥ 2] ≥ 0.39`, `P[A ≥ 1] ≥ 0.39`, `P[B ≤ 2] ≥ 0.25`
  gives `P[A = 1 ∧ B = 2] ≥ 0.0853 · P[Z = 3] ≥ 6.2ε₂`.
* **Case 2**, `P[Z_T = 3] < 73ε₂`: then `E[Z] < 2.1` (else `P[Z = 3] ≥ 0.036`),
  `P[Z = 2] ≥ 0.25`, `P[Z = 3] ≥ 0.97 (18ε₂ − 5ε_η)` (Lemma 2.21), and the
  ratio `γ ≤ 0.06` makes the tails geometric (Lemma 2.18):
  `P[Z ≥ 4] ≤ 0.00094`, `E[(Z−1)𝟙{Z≥3}] ≤ 0.0321`.  Hence `P[A ≥ 1]`,
  `P[B ≥ 2] ≥ 0.4679`, and by layer monotonicity the same holds conditioned
  on `Z = 3` up to `P[Z ≥ 4]`.  On the layer `Z = 3` the count `A_T ∈ {0,1,2}`
  is a Bernoulli sum, so **Newton's inequality** `4p₀p₂ ≤ p₁²`
  (`bernoulli_newton_two`) with `p₀, p₂ ≤ 0.534` forces `p₁ ≥ 0.36`, and
  `P[A = 1 ∧ B = 2] = p₁ · P[Z = 3] ≥ 0.36 · 17.4ε₂ ≥ 6ε₂`.

KKO's Theorem 2.15 (Hoeffding) is not needed: the `7/16` it supplies for
`P[Y ≤ 1]` is replaced by the baseline Markov bound `1/4`, which the `73ε₂`
threshold absorbs.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Mass bookkeeping -/

/-- `P[X ≤ k] + P[k + 1 ≤ X] = 1`. -/
theorem weightMass_le_add_ge {w : Finset ι → ℝ} (htot : totalMass w = 1) (F : Finset ι)
    (k : ℕ) :
    weightMass w (fun T => (T ∩ F).card ≤ k) + weightMass w (fun T => k + 1 ≤ (T ∩ F).card)
      = 1 := by
  have hor := weightMass_or w (fun T => (T ∩ F).card ≤ k) (fun T => k + 1 ≤ (T ∩ F).card)
  have hand : weightMass w (fun T => (T ∩ F).card ≤ k ∧ k + 1 ≤ (T ∩ F).card) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    constructor
    · rintro ⟨h1, h2⟩; omega
    · intro h; exact h.elim
  have hall : weightMass w (fun T => (T ∩ F).card ≤ k ∨ k + 1 ≤ (T ∩ F).card) = 1 := by
    rw [weightMass_congr (B := fun _ => True) fun T => ⟨fun _ => trivial, fun _ => by omega⟩,
      weightMass_true, htot]
  linarith

/-- The layers of `F` below `n` partition an event. -/
theorem weightMass_card_le_and_eq_sum (w : Finset ι → ℝ) (F : Finset ι)
    (Q : Finset ι → Prop) (n : ℕ) :
    weightMass w (fun T => (T ∩ F).card ≤ n ∧ Q T)
      = ∑ j ∈ Finset.range (n + 1), weightMass w (fun T => (T ∩ F).card = j ∧ Q T) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    exact weightMass_congr fun T => by rw [Nat.le_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hor := weightMass_or w (fun T => (T ∩ F).card ≤ n ∧ Q T)
      (fun T => (T ∩ F).card = n + 1 ∧ Q T)
    have hand : weightMass w (fun T => ((T ∩ F).card ≤ n ∧ Q T)
        ∧ ((T ∩ F).card = n + 1 ∧ Q T)) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      constructor
      · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
      · intro h; exact h.elim
    have hall : weightMass w (fun T => ((T ∩ F).card ≤ n ∧ Q T)
        ∨ ((T ∩ F).card = n + 1 ∧ Q T)) = weightMass w (fun T => (T ∩ F).card ≤ n + 1 ∧ Q T) := by
      refine weightMass_congr fun T => ?_
      constructor
      · rintro (⟨h1, hQ⟩ | ⟨h1, hQ⟩) <;> exact ⟨by omega, hQ⟩
      · rintro ⟨h1, hQ⟩
        rcases Nat.lt_or_ge (T ∩ F).card (n + 1) with h | h
        · exact Or.inl ⟨by omega, hQ⟩
        · exact Or.inr ⟨by omega, hQ⟩
    linarith

/-! ### Restricted means -/

/-- `E[A] ≤ P[A ≥ 1] + E[(Z − 1)𝟙{Z ≥ 3}]` when `B ≥ 1` on the support and
`Z = A ⊔ B`. -/
theorem expCard_le_ge_add_tail {w : Finset ι → ℝ} (hnn : WeightNonneg w) {A B : Finset ι}
    (hAB : Disjoint A B) (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card) :
    expCard w A ≤ weightMass w (fun T => 1 ≤ (T ∩ A).card)
      + ∑ T, w T * ((((T ∩ (A ∪ B)).card : ℝ) - 1)
        * (if 3 ≤ (T ∩ (A ∪ B)).card then (1 : ℝ) else 0)) := by
  rw [weightMass_eq_sum_mul_ite, expCard, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  rcases eq_or_ne (w T) 0 with h0 | h0
  · simp [h0]
  have hb := hbase T h0
  rw [card_inter_union_of_disjoint hAB T, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hnn T)
  push_cast
  split_ifs with h1 h3 h3
  · have : (1 : ℝ) ≤ (T ∩ B).card := by exact_mod_cast hb
    linarith
  · have : (T ∩ A).card ≤ 1 := by omega
    have : ((T ∩ A).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · have : (T ∩ A).card = 0 := by omega
    have : ((T ∩ A).card : ℝ) = 0 := by exact_mod_cast this
    have : (1 : ℝ) ≤ (T ∩ B).card := by exact_mod_cast hb
    linarith
  · have : (T ∩ A).card = 0 := by omega
    have : ((T ∩ A).card : ℝ) = 0 := by exact_mod_cast this
    linarith

/-- `E[B] − 1 ≤ P[B ≥ 2] + E[(Z − 1)𝟙{Z ≥ 3}]` when `B ≥ 1` on the support. -/
theorem expCard_sub_one_le_ge_add_tail {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) {A B : Finset ι} (hAB : Disjoint A B)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card) :
    expCard w B - 1 ≤ weightMass w (fun T => 2 ≤ (T ∩ B).card)
      + ∑ T, w T * ((((T ∩ (A ∪ B)).card : ℝ) - 1)
        * (if 3 ≤ (T ∩ (A ∪ B)).card then (1 : ℝ) else 0)) := by
  have h1 : expCard w B - 1 = ∑ T, w T * (((T ∩ B).card : ℝ) - 1) := by
    have h : (1 : ℝ) = ∑ T, w T := by rw [← htot]; rfl
    rw [expCard]
    conv_lhs => rw [h]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [h1, weightMass_eq_sum_mul_ite, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  rcases eq_or_ne (w T) 0 with h0 | h0
  · simp [h0]
  have hb := hbase T h0
  rw [card_inter_union_of_disjoint hAB T, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hnn T)
  push_cast
  split_ifs with h2 h3 h3
  · have : (0 : ℝ) ≤ (T ∩ A).card := Nat.cast_nonneg _
    linarith
  · have : (T ∩ B).card ≤ 2 := by omega
    have : ((T ∩ B).card : ℝ) ≤ 2 := by exact_mod_cast this
    linarith
  · have : (T ∩ B).card ≤ 1 := by omega
    have : ((T ∩ B).card : ℝ) ≤ 1 := by exact_mod_cast this
    have : (0 : ℝ) ≤ (T ∩ A).card := Nat.cast_nonneg _
    linarith
  · have : (T ∩ B).card ≤ 1 := by omega
    have : ((T ∩ B).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith

/-! ### Conditioning an increasing event on the layer `Z = 3` -/

/-- **Layer monotonicity aggregated**: for an increasing event `Q` determined
by `F`, `(P[Q] − P[F ≥ 4]) · P[F = 3] ≤ P[F = 3 ∧ Q]`. -/
theorem layer_three_cond_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι)
    {Q : Finset ι → Prop} (hQ : Monotone Q) (hQF : EventDependsOn Q F) :
    (weightMass w Q - weightMass w (fun T => 4 ≤ (T ∩ F).card))
        * weightMass w (fun T => (T ∩ F).card = 3)
      ≤ weightMass w (fun T => (T ∩ F).card = 3 ∧ Q T) := by
  -- each layer `j ≤ 3` against the layer `3`
  have hj : ∀ j ∈ Finset.range 4,
      weightMass w (fun T => (T ∩ F).card = j ∧ Q T) * weightMass w (fun T => (T ∩ F).card = 3)
        ≤ weightMass w (fun T => (T ∩ F).card = 3 ∧ Q T)
          * weightMass w (fun T => (T ∩ F).card = j) := by
    intro j hj
    have h := layer_le_mono hst hr hnn htot F hQ (j := j) (n := 3)
      (by have := Finset.mem_range.mp hj; omega)
    rwa [weightMass_projLayer_of_dependsOn w j hQF, weightMass_projLayer_of_dependsOn w 3 hQF,
      totalMass_projLayer, totalMass_projLayer] at h
  have hsum := Finset.sum_le_sum hj
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  -- the layers below `4` carry at most the whole mass
  have hle3 : ∑ j ∈ Finset.range 4, weightMass w (fun T => (T ∩ F).card = j) ≤ 1 := by
    have h := weightMass_card_le_and_eq_sum w F (fun _ => True) 3
    have h' : weightMass w (fun T => (T ∩ F).card ≤ 3 ∧ True) ≤ 1 := weightMass_le_one hnn htot _
    rw [h] at h'
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) h'
    exact weightMass_congr fun T => by simp
  have hpart := weightMass_card_le_and_eq_sum w F Q 3
  -- `P[F ≤ 3 ∧ Q] ≥ P[Q] − P[F ≥ 4]`
  have hsub := weightMass_and_ge_sub hnn Q (fun T => (T ∩ F).card ≤ 3)
  have hcompl : weightMass w (fun T => ¬ (T ∩ F).card ≤ 3)
      = weightMass w (fun T => 4 ≤ (T ∩ F).card) :=
    weightMass_congr fun T => by omega
  have hcomm : weightMass w (fun T => Q T ∧ (T ∩ F).card ≤ 3)
      = weightMass w (fun T => (T ∩ F).card ≤ 3 ∧ Q T) :=
    weightMass_congr fun T => and_comm
  rw [hcompl, hcomm, hpart] at hsub
  have h3nn := weightMass_nonneg hnn (fun T => (T ∩ F).card = 3)
  have h3Qnn := weightMass_nonneg hnn (fun T => (T ∩ F).card = 3 ∧ Q T)
  calc (weightMass w Q - weightMass w (fun T => 4 ≤ (T ∩ F).card))
        * weightMass w (fun T => (T ∩ F).card = 3)
      ≤ (∑ j ∈ Finset.range 4, weightMass w (fun T => (T ∩ F).card = j ∧ Q T))
        * weightMass w (fun T => (T ∩ F).card = 3) :=
        mul_le_mul_of_nonneg_right hsub h3nn
    _ ≤ weightMass w (fun T => (T ∩ F).card = 3 ∧ Q T)
        * ∑ j ∈ Finset.range 4, weightMass w (fun T => (T ∩ F).card = j) := hsum
    _ ≤ weightMass w (fun T => (T ∩ F).card = 3 ∧ Q T) * 1 :=
        mul_le_mul_of_nonneg_left hle3 h3Qnn
    _ = _ := mul_one _

/-! ### The layer `Z = 3` split by the `A`-count -/

/-- On `Z = 3` the `A`-count is at most `2`, so the layer splits three ways. -/
theorem layer_three_split {w : Finset ι → ℝ} {A B : Finset ι} (hAB : Disjoint A B)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = 3)
      = weightMass w (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
        + weightMass w (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
        + weightMass w (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2) := by
  have h1 : weightMass w (fun T => (T ∩ (A ∪ B)).card = 3)
      = weightMass w (fun T => (T ∩ A).card ≤ 2 ∧ (T ∩ (A ∪ B)).card = 3) := by
    refine weightMass_congr_of_support fun T hT => ?_
    have hb := hbase T hT
    have hz := card_inter_union_of_disjoint hAB T
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [h1, weightMass_card_le_and_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have e0 := weightMass_congr (w := w)
    (A := fun T => (T ∩ A).card = 0 ∧ (T ∩ (A ∪ B)).card = 3)
    (B := fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0) fun T => and_comm
  have e1 := weightMass_congr (w := w)
    (A := fun T => (T ∩ A).card = 1 ∧ (T ∩ (A ∪ B)).card = 3)
    (B := fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1) fun T => and_comm
  have e2 := weightMass_congr (w := w)
    (A := fun T => (T ∩ A).card = 2 ∧ (T ∩ (A ∪ B)).card = 3)
    (B := fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2) fun T => and_comm
  rw [e0, e1, e2]

/-! ### Newton on the layer -/

/-- **Newton's inequality on the layer `Z = 3`**: the `A`-count there is a
Bernoulli sum supported on `{0, 1, 2}`. -/
theorem newton_on_layer {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {A B : Finset ι} (hAB : Disjoint A B)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ B).card)
    (hmpos : 0 < weightMass w (fun T => (T ∩ (A ∪ B)).card = 3)) :
    4 * weightMass w (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
        * weightMass w (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)
      ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1) ^ 2 := by
  classical
  set F := A ∪ B with hF
  set m := weightMass w (fun T => (T ∩ F).card = 3) with hm
  have hmne : m ≠ 0 := hmpos.ne'
  -- the normalized layer
  have hLnn : WeightNonneg (projLayer w F 3) := weightNonneg_projLayer hnn F 3
  have hLmass : totalMass (projLayer w F 3) = m := by rw [totalMass_projLayer]
  have hLpos : 0 < totalMass (projLayer w F 3) := by rw [hLmass]; exact hmpos
  obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ := exists_layer_interval hst hr hnn htot F
  have hlayer := (hiff 3).mp hLpos
  have hLst : IsRealStable (genPoly (projLayer w F 3)) :=
    isRealStable_projLayer_interval hst hr hnn hab hbr hiff hsupp 3 hlayer.1 hlayer.2
  let ρ : Finset ι → ℝ := fun U => m⁻¹ * projLayer w F 3 U
  have hρnn : WeightNonneg ρ := fun U => mul_nonneg (inv_nonneg.mpr hmpos.le) (hLnn U)
  have hρrank : FixedRankWeight 3 ρ := by
    intro U hU
    exact fixedRankWeight_projLayer w F 3 U fun hzero => hU (by
      change m⁻¹ * projLayer w F 3 U = 0
      rw [hzero, mul_zero])
  have hρtot : totalMass ρ = 1 := by
    change totalMass (fun U => m⁻¹ * projLayer w F 3 U) = 1
    rw [totalMass_smul, hLmass, inv_mul_cancel₀ hmne]
  have hρst : IsRealStable (genPoly ρ) := by
    change IsRealStable (genPoly (fun U => m⁻¹ * projLayer w F 3 U))
    rw [← const_mul_genPoly]
    exact IsRealStable.const_mul (inv_ne_zero hmne) hLst
  have hAF : A ⊆ F := Finset.subset_union_left
  have hρmass : ∀ k, weightMass ρ (fun T => (T ∩ A).card = k)
      = m⁻¹ * weightMass w (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card = k) := by
    intro k
    change weightMass (fun U => m⁻¹ * projLayer w F 3 U) _ = _
    rw [weightMass_smul, weightMass_projLayer_of_dependsOn w 3
      ((eventDependsOn_card_eq A k).mono hAF)]
  -- the Bernoulli law of the `A`-count on the layer
  obtain ⟨m', q, -, hlaw⟩ := exists_bernoulli_rank_law hρst hρrank hρnn hρtot A
  have h3 : ∀ k, 3 ≤ k → Bernoulli.probCount q k = 0 := by
    intro k hk
    rw [← hlaw k, hρmass k]
    have : weightMass w (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card = k) = 0 := by
      refine (weightMass_congr_of_support (B := fun _ => False) fun T hT => ?_).trans
        (weightMass_false _)
      have hb := hbase T hT
      have hz : (T ∩ F).card = (T ∩ A).card + (T ∩ B).card := card_inter_union_of_disjoint hAB T
      constructor
      · rintro ⟨h1, h2⟩; omega
      · intro h; exact h.elim
    rw [this, mul_zero]
  have hN := bernoulli_newton_two q h3
  rw [← hlaw 0, ← hlaw 1, ← hlaw 2, hρmass 0, hρmass 1, hρmass 2] at hN
  -- clear the normalization
  have hinv : 0 < m⁻¹ := inv_pos.mpr hmpos
  set x₀ := weightMass w (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card = 0)
  set x₁ := weightMass w (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card = 1)
  set x₂ := weightMass w (fun T => (T ∩ F).card = 3 ∧ (T ∩ A).card = 2)
  have h : m⁻¹ * m⁻¹ * (4 * x₀ * x₂) ≤ m⁻¹ * m⁻¹ * x₁ ^ 2 := by
    calc m⁻¹ * m⁻¹ * (4 * x₀ * x₂) = 4 * (m⁻¹ * x₀) * (m⁻¹ * x₂) := by ring
      _ ≤ (m⁻¹ * x₁) ^ 2 := hN
      _ = m⁻¹ * m⁻¹ * x₁ ^ 2 := by ring
  exact le_of_mul_le_mul_left h (mul_pos hinv hinv)

/-- The minimization: `p₀, p₂ ≤ 0.534 m`, `p₀ + p₁ + p₂ = m`, `4p₀p₂ ≤ p₁²`
force `p₁ ≥ 0.36 m`. -/
theorem p_one_ge_of_newton {m p₀ p₁ p₂ : ℝ} (hm : 0 < m) (hsum : p₀ + p₁ + p₂ = m)
    (h0 : 0 ≤ p₀) (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (hn : 4 * p₀ * p₂ ≤ p₁ ^ 2)
    (hb0 : p₀ ≤ 0.534 * m) (hb2 : p₂ ≤ 0.534 * m) : 0.36 * m ≤ p₁ := by
  by_contra hc
  push_neg at hc
  have hprod := mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr hb2)
  have hsq : p₁ * p₁ ≤ 0.36 * m * (0.36 * m) := mul_le_mul hc.le hc.le h1 (by positivity)
  nlinarith [mul_pos hm hm]

/-! ### The kernel -/

/-- **The analytic kernel of Lemma 5.16**: `P[A_T = 1 ∧ B_T = 2] ≥ 6ε₂`. -/
theorem lemma_5_16_kernel {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ B).card)
    {ε₂ εη : ℝ} (hε₂ : 0 < ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεη : 0 ≤ εη) (hεηsq : εη ≤ ε₂ ^ 2)
    (hA1 : 1 / 2 + 9 * ε₂ - εη / 2 ≤ expCard ν A) (hA2 : expCard ν A ≤ 1 + εη)
    (hB1 : 3 / 2 + 9 * ε₂ - 9 / 2 * εη ≤ expCard ν B)
    (hB2 : expCard ν B ≤ 5 / 2 - 9 * ε₂ + 4 * εη) :
    6 * ε₂ ≤ weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2) := by
  classical
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hεηε : εη ≤ 0.0002 * ε₂ := by nlinarith
  -- the sum count
  have hZ : expCard ν (A ∪ B) = expCard ν A + expCard ν B := expCard_union_of_disjoint _ hAB
  have hbaseZ : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card := by
    intro T hT
    rw [card_inter_union_of_disjoint hAB T]
    have := hbase T hT
    omega
  have htarget : weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2)
      = weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1) := by
    refine weightMass_congr fun T => ?_
    rw [card_inter_union_of_disjoint hAB T]
    omega
  have hP3nn := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3)
  by_cases hP3 : 73 * ε₂ ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3)
  · /- ### Case 1: the shifted three-cell bound -/
    have hAle : (0.4999 : ℝ) ≤ weightMass ν (fun T => (T ∩ A).card ≤ 1) := by
      have h := two_mul_weightMass_le_one_ge hnn A
      rw [htot] at h
      linarith
    have hBge : (0.39 : ℝ) ≤ weightMass ν (fun T => 2 ≤ (T ∩ B).card) :=
      weightMass_two_le_ge_of_baseline hst hr hnn htot hbase (by linarith)
    have hAge : (0.39 : ℝ) ≤ weightMass ν (fun T => 1 ≤ (T ∩ A).card) :=
      weightMass_one_le_ge_4977 hst hr hnn htot (by linarith)
    have hBle : (0.25 : ℝ) ≤ weightMass ν (fun T => (T ∩ B).card ≤ 2) := by
      have h := mul_weightMass_ge_le_of_baseline hnn (F := B) (b := 1) (k := 3)
        (by norm_num) hbase
      rw [htot] at h
      have h2 := weightMass_le_add_ge htot B 2
      norm_num at h h2
      linarith
    have hlow : (0.097 : ℝ) ≤ weightMass ν (fun T => (T ∩ A).card ≤ 0 + 1)
        * weightMass ν (fun T => 1 + 1 ≤ (T ∩ B).card) := by
      show (0.097 : ℝ) ≤ weightMass ν (fun T => (T ∩ A).card ≤ 1)
        * weightMass ν (fun T => 2 ≤ (T ∩ B).card)
      nlinarith [mul_le_mul hAle hBge (by norm_num) (weightMass_nonneg hnn _)]
    have hhigh : (0.097 : ℝ) ≤ weightMass ν (fun T => 0 + 1 ≤ (T ∩ A).card)
        * weightMass ν (fun T => (T ∩ B).card ≤ 1 + 1) := by
      show (0.097 : ℝ) ≤ weightMass ν (fun T => 1 ≤ (T ∩ A).card)
        * weightMass ν (fun T => (T ∩ B).card ≤ 2)
      nlinarith [mul_le_mul hAge hBle (by norm_num) (weightMass_nonneg hnn _)]
    have h := three_cell_bound_shifted hst hr hnn htot hAB 0 1 (fun _ _ => Nat.zero_le _) hbase
      (ε := 0.097) (by norm_num) (by norm_num) hlow hhigh
    have h' : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) * 0.097 * (1 - 3 * 0.097)
        ≤ weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2) * (1 - 2 * 0.097) := h
    linarith
  · /- ### Case 2: the layer `Z = 3` is thin -/
    push_neg at hP3
    -- `E[Z] < 2.1`, else the layer is at least `0.036`
    have hZlt : expCard ν (A ∪ B) < 2.1 := by
      by_contra hc
      push_neg at hc
      have := weightMass_eq_three_ge_of_baseline_mid hst hr hnn htot hbaseZ hc
        (by rw [hZ]; linarith)
      linarith
    have hP2 : (0.25 : ℝ) ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card = 2) :=
      weightMass_eq_two_ge_of_baseline_low hst hr hnn htot hbaseZ (by rw [hZ]; linarith) hZlt.le
    have hm : 0.97 * (18 * ε₂ - 5 * εη) ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) :=
      weightMass_eq_three_ge_of_baseline_small hst hr hnn htot hbaseZ (η := 18 * ε₂ - 5 * εη)
        (by linarith) (by linarith) (by rw [hZ]; linarith) (by linarith)
    have hmpos : 0 < weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) := by linarith
    -- the geometric tails at ratio `0.06`
    obtain ⟨hT4, hR⟩ := tails_of_baseline hst hr hnn htot hbaseZ (by linarith) (γ := 0.06)
      (by norm_num) (by norm_num) (by linarith)
    have hT4' : weightMass ν (fun T => 4 ≤ (T ∩ (A ∪ B)).card) ≤ 0.00094 := by
      norm_num at hT4; linarith
    have hR' : ∑ T, ν T * ((((T ∩ (A ∪ B)).card : ℝ) - 1) * (if 3 ≤ (T ∩ (A ∪ B)).card then (1 : ℝ) else 0))
        ≤ 0.0321 := by
      have hc : (2 * (1 - (0.06 : ℝ))⁻¹ + 0.06 / (1 - 0.06) ^ 2) ≤ 2.196 := by norm_num
      have hP : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) ≤ 0.0146 := by linarith
      calc _ ≤ _ := hR
        _ ≤ 0.0146 * 2.196 := mul_le_mul hP hc (by norm_num) (by norm_num)
        _ ≤ 0.0321 := by norm_num
    -- the one-cell lower tails
    have hAge : (0.4679 : ℝ) ≤ weightMass ν (fun T => 1 ≤ (T ∩ A).card) := by
      have := expCard_le_ge_add_tail hnn hAB hbase
      linarith
    have hBge : (0.4679 : ℝ) ≤ weightMass ν (fun T => 2 ≤ (T ∩ B).card) := by
      have := expCard_sub_one_le_ge_add_tail hnn htot hAB hbase
      linarith
    -- conditioned on the layer `Z = 3`
    have hQA := layer_three_cond_ge hst hr hnn htot (A ∪ B) (Q := fun T => 1 ≤ (T ∩ A).card)
      (fun T T' hTT' h => le_trans h (Finset.card_le_card
        (Finset.inter_subset_inter hTT' (Finset.Subset.refl _))))
      ((eventDependsOn_le_card A 1).mono Finset.subset_union_left)
    have hQB := layer_three_cond_ge hst hr hnn htot (A ∪ B) (Q := fun T => 2 ≤ (T ∩ B).card)
      (fun T T' hTT' h => le_trans h (Finset.card_le_card
        (Finset.inter_subset_inter hTT' (Finset.Subset.refl _))))
      ((eventDependsOn_le_card B 2).mono Finset.subset_union_right)
    -- the three cells of the layer
    set x₀ := weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0) with hx₀
    set x₁ := weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1) with hx₁
    set x₂ := weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2) with hx₂
    have hsplit := layer_three_split hAB hbase
    have hA1 : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 1 ≤ (T ∩ A).card) = x₁ + x₂ := by
      have hor := weightMass_or ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
        (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)
      have hand : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
          ∧ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)) = 0 := by
        refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
        constructor
        · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩; omega
        · intro h; exact h.elim
      have hall : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
          ∨ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2))
          = weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 1 ≤ (T ∩ A).card) := by
        refine weightMass_congr_of_support fun T hT => ?_
        have hb := hbase T hT
        have hz := card_inter_union_of_disjoint hAB T
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge (T ∩ A).card 2 with h | h
          · exact Or.inl ⟨h1, by omega⟩
          · exact Or.inr ⟨h1, by omega⟩
      linarith
    have hB2 : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 2 ≤ (T ∩ B).card) = x₀ + x₁ := by
      have hor := weightMass_or ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
        (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
      have hand : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
          ∧ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)) = 0 := by
        refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
        constructor
        · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩; omega
        · intro h; exact h.elim
      have hall : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
          ∨ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1))
          = weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 2 ≤ (T ∩ B).card) := by
        refine weightMass_congr fun T => ?_
        have hz := card_inter_union_of_disjoint hAB T
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge (T ∩ A).card 1 with h | h
          · exact Or.inl ⟨h1, by omega⟩
          · exact Or.inr ⟨h1, by omega⟩
      linarith
    rw [hA1] at hQA
    rw [hB2] at hQB
    have hN := newton_on_layer hst hr hnn htot hAB hbase hmpos
    have hx0 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
    have hx1 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
    have hx2 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)
    -- `x₀, x₂ ≤ 0.534 m`
    have hb0 : x₀ ≤ 0.534 * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) := by
      have : (0.466 : ℝ) * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) ≤ x₁ + x₂ :=
        le_trans (mul_le_mul_of_nonneg_right (by linarith) hP3nn) hQA
      linarith
    have hb2 : x₂ ≤ 0.534 * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) := by
      have : (0.466 : ℝ) * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) ≤ x₀ + x₁ :=
        le_trans (mul_le_mul_of_nonneg_right (by linarith) hP3nn) hQB
      linarith
    have hp1 := p_one_ge_of_newton hmpos hsplit.symm hx0 hx1 hx2 hN hb0 hb2
    rw [htarget]
    linarith only [hp1, hm, hεηε, hε₂]

end TSPGap

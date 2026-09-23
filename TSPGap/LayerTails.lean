/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.AdjacentLayers

/-!
# The marker calculus IV: layer tails and KKO21 Lemma 5.4

The division-free tail aggregation.  Throughout, `N T = |T ∩ F|` with
`F = A ∪ B` disjointly, `n = n_A + n_B`, `m = W(N = n)`, and
`s = W(N = n ∧ |T∩A| ≤ n_A)` — which on the layer equals
`W(N = n ∧ |T∩B| ≥ n_B)`, and is *not* the split-count mass.

* `layer_le_mono` / `layer_le_anti` — arbitrary-layer comparisons
  `e_j(Q)·m_n ≤ e_n(Q)·m_j`, iterated from the adjacent ones; the
  intermediate mass cancels when positive, and a vanishing intermediate
  layer kills one side of the interval outright.
* `weightMass_layer_partition` — the finite layer partition of any event,
  summed over `range (F.card + 1)`.
* `crossTail` — the exact-layer-versus-tail cross inequality
  `m·W(Q ∧ c(N)) ≤ e_n(Q)·W(c(N))` for any tail condition `c` whose
  layers all compare to the anchor `n`.
* `layerProduct_le_of_le_ge` / `layerProduct_le_of_ge_le` — **KKO21
  Lemma 5.4**, division-free:
  `m·W(A ≤ n_A)·W(B ≥ n_B) ≤ s·M²` and its mirror.  The pointwise
  partition `{A ≤ n_A, B ≥ n_B} = {A ≤ n_A, N ≥ n} ⊔ {B ≥ n_B, N < n}`
  has its weak/strict boundary load-bearing: on `N ≥ n` the `A`-condition
  forces the `B`-one, and on `N < n` conversely, strictly.  The product
  bound is the existing mixed-sign positive correlation.

The statements carry `totalMass w = 1` — inherited from the adjacent
comparisons — and display `M = totalMass w` symbolically: this is the
normalized export, not an arbitrary-mass theorem.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Arbitrary-layer comparisons -/

/-- Climbing to the anchor from below, for increasing events. -/
theorem layer_le_mono {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι)
    {Q : Finset ι → Prop} (hQ : Monotone Q) {j n : ℕ} (hjn : j ≤ n) :
    weightMass (projLayer w F j) Q * totalMass (projLayer w F n)
      ≤ weightMass (projLayer w F n) Q * totalMass (projLayer w F j) := by
  classical
  obtain ⟨a, b, hab, hbr, hiff, -⟩ := exists_layer_interval hst hr hnn htot F
  have hnullm : ∀ i, ¬ (a ≤ i ∧ i ≤ b) →
      totalMass (projLayer w F i) = 0 := by
    intro i hi
    by_contra hc
    exact hi ((hiff i).mp (lt_of_le_of_ne
      (totalMass_nonneg (weightNonneg_projLayer hnn F i)) (Ne.symm hc)))
  have hnulle : ∀ i, totalMass (projLayer w F i) = 0 →
      weightMass (projLayer w F i) Q = 0 := fun i hi => le_antisymm
    (hi ▸ weightMass_le_totalMass (weightNonneg_projLayer hnn F i) Q)
    (weightMass_nonneg (weightNonneg_projLayer hnn F i) Q)
  have main : ∀ d jj, jj + d = n →
      weightMass (projLayer w F jj) Q * totalMass (projLayer w F n)
        ≤ weightMass (projLayer w F n) Q * totalMass (projLayer w F jj) := by
    intro d
    induction d with
    | zero =>
      intro jj hje
      obtain rfl : jj = n := by omega
      exact le_rfl
    | succ d ih =>
      intro jj hje
      have hadj := adjacent_layer_mono hst hr hnn htot F jj hQ
      have hIH := ih (jj + 1) (by omega)
      have hmid_nn : 0 ≤ totalMass (projLayer w F (jj + 1)) :=
        totalMass_nonneg (weightNonneg_projLayer hnn F (jj + 1))
      rcases eq_or_lt_of_le hmid_nn with hmid0 | hmidpos
      · have hnotin : ¬ (a ≤ jj + 1 ∧ jj + 1 ≤ b) := fun hc => by
          have := (hiff (jj + 1)).mpr hc
          rw [← hmid0] at this
          exact lt_irrefl 0 this
        rcases Nat.lt_or_ge (jj + 1) a with hlow | hhigh
        · have hej0 := hnulle jj (hnullm jj (by omega))
          rw [hej0, zero_mul]
          exact mul_nonneg
            (weightMass_nonneg (weightNonneg_projLayer hnn F n) Q)
            (totalMass_nonneg (weightNonneg_projLayer hnn F jj))
        · have hbj : ¬ (jj + 1 ≤ b) := fun hc => hnotin ⟨hhigh, hc⟩
          have hmn0 : totalMass (projLayer w F n) = 0 :=
            hnullm n (by omega)
          rw [hmn0, mul_zero]
          exact mul_nonneg
            (weightMass_nonneg (weightNonneg_projLayer hnn F n) Q)
            (totalMass_nonneg (weightNonneg_projLayer hnn F jj))
      · have hmn_nn : 0 ≤ totalMass (projLayer w F n) :=
          totalMass_nonneg (weightNonneg_projLayer hnn F n)
        have hmj_nn : 0 ≤ totalMass (projLayer w F jj) :=
          totalMass_nonneg (weightNonneg_projLayer hnn F jj)
        have h1 := mul_le_mul_of_nonneg_right hadj hmn_nn
        have h2 := mul_le_mul_of_nonneg_right hIH hmj_nn
        have hkey : totalMass (projLayer w F (jj + 1))
            * (weightMass (projLayer w F jj) Q
              * totalMass (projLayer w F n))
            ≤ totalMass (projLayer w F (jj + 1))
              * (weightMass (projLayer w F n) Q
                * totalMass (projLayer w F jj)) := by
          nlinarith [h1, h2]
        exact le_of_mul_le_mul_left hkey hmidpos
  exact main (n - j) j (by omega)

/-- Descending to the anchor from above, for decreasing events. -/
theorem layer_le_anti {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι)
    {Q : Finset ι → Prop} (hQ : Antitone Q) {j n : ℕ} (hnj : n ≤ j) :
    weightMass (projLayer w F j) Q * totalMass (projLayer w F n)
      ≤ weightMass (projLayer w F n) Q * totalMass (projLayer w F j) := by
  classical
  obtain ⟨a, b, hab, hbr, hiff, -⟩ := exists_layer_interval hst hr hnn htot F
  have hnullm : ∀ i, ¬ (a ≤ i ∧ i ≤ b) →
      totalMass (projLayer w F i) = 0 := by
    intro i hi
    by_contra hc
    exact hi ((hiff i).mp (lt_of_le_of_ne
      (totalMass_nonneg (weightNonneg_projLayer hnn F i)) (Ne.symm hc)))
  have hnulle : ∀ i, totalMass (projLayer w F i) = 0 →
      weightMass (projLayer w F i) Q = 0 := fun i hi => le_antisymm
    (hi ▸ weightMass_le_totalMass (weightNonneg_projLayer hnn F i) Q)
    (weightMass_nonneg (weightNonneg_projLayer hnn F i) Q)
  have main : ∀ d jj, jj = n + d →
      weightMass (projLayer w F jj) Q * totalMass (projLayer w F n)
        ≤ weightMass (projLayer w F n) Q * totalMass (projLayer w F jj) := by
    intro d
    induction d with
    | zero =>
      intro jj hje
      obtain rfl : jj = n := by omega
      exact le_rfl
    | succ d ih =>
      intro jj hje
      have hadj := adjacent_layer_anti hst hr hnn htot F (n + d) hQ
      have hIH := ih (n + d) rfl
      have hmid_nn : 0 ≤ totalMass (projLayer w F (n + d)) :=
        totalMass_nonneg (weightNonneg_projLayer hnn F (n + d))
      rcases eq_or_lt_of_le hmid_nn with hmid0 | hmidpos
      · have hnotin : ¬ (a ≤ n + d ∧ n + d ≤ b) := fun hc => by
          have := (hiff (n + d)).mpr hc
          rw [← hmid0] at this
          exact lt_irrefl 0 this
        rcases Nat.lt_or_ge (n + d) a with hlow | hhigh
        · have hmn0 : totalMass (projLayer w F n) = 0 :=
            hnullm n (by omega)
          rw [hmn0, mul_zero]
          exact mul_nonneg
            (weightMass_nonneg (weightNonneg_projLayer hnn F n) Q)
            (totalMass_nonneg (weightNonneg_projLayer hnn F jj))
        · have hbj : ¬ (n + d ≤ b) := fun hc => hnotin ⟨hhigh, hc⟩
          have hej0 := hnulle jj (hnullm jj (by omega))
          rw [hej0, zero_mul]
          exact mul_nonneg
            (weightMass_nonneg (weightNonneg_projLayer hnn F n) Q)
            (totalMass_nonneg (weightNonneg_projLayer hnn F jj))
      · have hmn_nn : 0 ≤ totalMass (projLayer w F n) :=
          totalMass_nonneg (weightNonneg_projLayer hnn F n)
        have hmj_nn : 0 ≤ totalMass (projLayer w F jj) :=
          totalMass_nonneg (weightNonneg_projLayer hnn F jj)
        have hadj' : weightMass (projLayer w F jj) Q
            * totalMass (projLayer w F (n + d))
            ≤ weightMass (projLayer w F (n + d)) Q
              * totalMass (projLayer w F jj) := by
          rw [hje]
          exact hadj
        have h1 := mul_le_mul_of_nonneg_right hadj' hmn_nn
        have h2 := mul_le_mul_of_nonneg_right hIH hmj_nn
        have hkey : totalMass (projLayer w F (n + d))
            * (weightMass (projLayer w F jj) Q
              * totalMass (projLayer w F n))
            ≤ totalMass (projLayer w F (n + d))
              * (weightMass (projLayer w F n) Q
                * totalMass (projLayer w F jj)) := by
          nlinarith [h1, h2]
        exact le_of_mul_le_mul_left hkey hmidpos
  exact main (j - n) j (by omega)

/-! ### The layer partition -/

/-- Every event partitions along the layers of `F`.  Built entirely from
`weightMass_congr`, `weightMass_or`, and `weightMass_false` — no indicator
bookkeeping. -/
theorem weightMass_layer_partition (w : Finset ι → ℝ) (F : Finset ι)
    (P : Finset ι → Prop) :
    weightMass w P
      = ∑ jj ∈ Finset.range (F.card + 1),
          weightMass w (fun S => (S ∩ F).card = jj ∧ P S) := by
  classical
  have hstep : ∀ n : ℕ,
      weightMass w (fun S => (S ∩ F).card < n ∧ P S)
        = ∑ jj ∈ Finset.range n,
            weightMass w (fun S => (S ∩ F).card = jj ∧ P S) := by
    intro n
    induction n with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      have h0 : weightMass w (fun S => (S ∩ F).card < 0 ∧ P S)
          = weightMass w (fun _ : Finset ι => False) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨h, -⟩
            omega
          · exact fun h => h.elim
      rw [h0, weightMass_false]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hor : weightMass w (fun S =>
            ((S ∩ F).card < n ∧ P S) ∨ ((S ∩ F).card = n ∧ P S))
          + weightMass w (fun S =>
            ((S ∩ F).card < n ∧ P S) ∧ ((S ∩ F).card = n ∧ P S))
          = weightMass w (fun S => (S ∩ F).card < n ∧ P S)
          + weightMass w (fun S => (S ∩ F).card = n ∧ P S) :=
        weightMass_or w _ _
      have hnever : weightMass w (fun S =>
            ((S ∩ F).card < n ∧ P S) ∧ ((S ∩ F).card = n ∧ P S))
          = weightMass w (fun _ : Finset ι => False) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨⟨h1, -⟩, h2, -⟩
            omega
          · exact fun h => h.elim
      have hcov : weightMass w (fun S => (S ∩ F).card < n + 1 ∧ P S)
          = weightMass w (fun S =>
            ((S ∩ F).card < n ∧ P S) ∨ ((S ∩ F).card = n ∧ P S)) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨h, hp⟩
            by_cases h' : (S ∩ F).card = n
            · exact Or.inr ⟨h', hp⟩
            · exact Or.inl ⟨by omega, hp⟩
          · rintro (⟨h, hp⟩ | ⟨h, hp⟩)
            · exact ⟨by omega, hp⟩
            · exact ⟨by omega, hp⟩
      rw [hnever, weightMass_false, add_zero] at hor
      rw [hcov]
      exact hor
  have hall : weightMass w P
      = weightMass w (fun S => (S ∩ F).card < F.card + 1 ∧ P S) :=
    weightMass_congr fun S => by
      have hle : (S ∩ F).card ≤ F.card :=
        Finset.card_le_card Finset.inter_subset_right
      constructor
      · exact fun h => ⟨by omega, h⟩
      · exact fun h => h.2
  rw [hall, hstep]

/-! ### The exact-layer-versus-tail cross inequality -/

/-- **The cross inequality**: for a tail condition `c` all of whose layers
compare to the anchor `n`, the anchor mass times the tail's event mass is
at most the anchor's event mass times the tail mass.  Pure aggregation:
no nonnegativity of the weight is needed — the inequality lives entirely
in `hcomp`, and the off-tail layers contribute equal zeros. -/
theorem crossTail {w : Finset ι → ℝ} (F : Finset ι)
    {Q : Finset ι → Prop} (hQdep : EventDependsOn Q F) (n : ℕ)
    (c : ℕ → Prop)
    (hcomp : ∀ jj, c jj →
      weightMass (projLayer w F jj) Q * totalMass (projLayer w F n)
        ≤ weightMass (projLayer w F n) Q * totalMass (projLayer w F jj)) :
    weightMass w (fun S => (S ∩ F).card = n)
        * weightMass w (fun S => Q S ∧ c ((S ∩ F).card))
      ≤ weightMass w (fun S => (S ∩ F).card = n ∧ Q S)
        * weightMass w (fun S => c ((S ∩ F).card)) := by
  classical
  have hQpart : weightMass w (fun S => Q S ∧ c ((S ∩ F).card))
      = ∑ jj ∈ Finset.range (F.card + 1),
          weightMass w (fun S =>
            (S ∩ F).card = jj ∧ (Q S ∧ c ((S ∩ F).card))) :=
    weightMass_layer_partition w F _
  have hcpart : weightMass w (fun S => c ((S ∩ F).card))
      = ∑ jj ∈ Finset.range (F.card + 1),
          weightMass w (fun S =>
            (S ∩ F).card = jj ∧ c ((S ∩ F).card)) :=
    weightMass_layer_partition w F _
  have hQlayer : ∀ jj, weightMass w
      (fun S => (S ∩ F).card = jj ∧ (Q S ∧ c ((S ∩ F).card)))
      = if c jj then weightMass w (fun S => (S ∩ F).card = jj ∧ Q S)
        else 0 := by
    intro jj
    by_cases hc : c jj
    · rw [if_pos hc]
      refine weightMass_congr fun S => ?_
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, h2, ?_⟩
        rw [h1]
        exact hc
    · rw [if_neg hc]
      have hfalse : weightMass w
          (fun S => (S ∩ F).card = jj ∧ (Q S ∧ c ((S ∩ F).card)))
          = weightMass w (fun _ : Finset ι => False) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨h1, -, h3⟩
            rw [h1] at h3
            exact hc h3
          · exact fun h => h.elim
      rw [hfalse, weightMass_false]
  have hclayer : ∀ jj, weightMass w
      (fun S => (S ∩ F).card = jj ∧ c ((S ∩ F).card))
      = if c jj then weightMass w (fun S => (S ∩ F).card = jj)
        else 0 := by
    intro jj
    by_cases hc : c jj
    · rw [if_pos hc]
      refine weightMass_congr fun S => ?_
      constructor
      · rintro ⟨h1, -⟩
        exact h1
      · intro h1
        refine ⟨h1, ?_⟩
        rw [h1]
        exact hc
    · rw [if_neg hc]
      have hfalse : weightMass w
          (fun S => (S ∩ F).card = jj ∧ c ((S ∩ F).card))
          = weightMass w (fun _ : Finset ι => False) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨h1, h3⟩
            rw [h1] at h3
            exact hc h3
          · exact fun h => h.elim
      rw [hfalse, weightMass_false]
  have hQpart2 : weightMass w (fun S => Q S ∧ c ((S ∩ F).card))
      = ∑ jj ∈ Finset.range (F.card + 1),
          (if c jj then weightMass w (fun S => (S ∩ F).card = jj ∧ Q S)
            else 0) := by
    rw [hQpart]
    exact Finset.sum_congr rfl fun jj _ => hQlayer jj
  have hcpart2 : weightMass w (fun S => c ((S ∩ F).card))
      = ∑ jj ∈ Finset.range (F.card + 1),
          (if c jj then weightMass w (fun S => (S ∩ F).card = jj)
            else 0) := by
    rw [hcpart]
    exact Finset.sum_congr rfl fun jj _ => hclayer jj
  rw [hQpart2, hcpart2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun jj _ => ?_
  by_cases hc : c jj
  · rw [if_pos hc, if_pos hc]
    have hthis := hcomp jj hc
    rw [weightMass_projLayer_of_dependsOn w jj hQdep,
      weightMass_projLayer_of_dependsOn w n hQdep,
      totalMass_projLayer, totalMass_projLayer] at hthis
    exact (mul_comm _ _).trans_le hthis
  · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]

/-! ### The threshold events -/

omit [Fintype ι] in
theorem antitone_card_le (A : Finset ι) (nA : ℕ) :
    Antitone (fun T => (T ∩ A).card ≤ nA) := by
  intro S T hST h
  exact le_trans (Finset.card_le_card
    (Finset.inter_subset_inter hST (Finset.Subset.refl A))) h

omit [Fintype ι] in
theorem monotone_le_card (B : Finset ι) (nB : ℕ) :
    Monotone (fun T => nB ≤ (T ∩ B).card) := by
  intro S T hST h
  exact le_trans h (Finset.card_le_card
    (Finset.inter_subset_inter hST (Finset.Subset.refl B)))

omit [Fintype ι] in
theorem eventDependsOn_card_le (A : Finset ι) (nA : ℕ) :
    EventDependsOn (fun T => (T ∩ A).card ≤ nA) A := by
  intro S T hST
  change (S ∩ A).card ≤ nA ↔ (T ∩ A).card ≤ nA
  rw [hST]

omit [Fintype ι] in
theorem eventDependsOn_le_card (B : Finset ι) (nB : ℕ) :
    EventDependsOn (fun T => nB ≤ (T ∩ B).card) B := by
  intro S T hST
  change nB ≤ (S ∩ B).card ↔ nB ≤ (T ∩ B).card
  rw [hST]

omit [Fintype ι] in
/-- Counts add along a disjoint union. -/
theorem card_inter_union_of_disjoint {A B : Finset ι}
    (hAB : Disjoint A B) (T : Finset ι) :
    (T ∩ (A ∪ B)).card = (T ∩ A).card + (T ∩ B).card := by
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint
      (Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
        hAB)]

/-! ### KKO21 Lemma 5.4, division-free -/

/-- **KKO21 Lemma 5.4** (`A ≤, B ≥` direction), division-free:
`m·W(A ≤ n_A)·W(B ≥ n_B) ≤ s·M²`. -/
theorem layerProduct_le_of_le_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (nA nB : ℕ) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = nA + nB)
        * (weightMass w (fun T => (T ∩ A).card ≤ nA)
          * weightMass w (fun T => nB ≤ (T ∩ B).card))
      ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = nA + nB
            ∧ (T ∩ A).card ≤ nA)
        * (totalMass w * totalMass w) := by
  classical
  set F := A ∪ B with hF
  have hcards : ∀ T : Finset ι,
      (T ∩ F).card = (T ∩ A).card + (T ∩ B).card := fun T => by
    rw [hF]
    exact card_inter_union_of_disjoint hAB T
  have hdepA : EventDependsOn (fun T => (T ∩ A).card ≤ nA) F :=
    (eventDependsOn_card_le A nA).mono Finset.subset_union_left
  have hdepB : EventDependsOn (fun T => nB ≤ (T ∩ B).card) F :=
    (eventDependsOn_le_card B nB).mono Finset.subset_union_right
  have h1 := crossTail F hdepA (nA + nB) (fun jj => nA + nB ≤ jj)
    (fun jj hjj => layer_le_anti hst hr hnn htot F
      (antitone_card_le A nA) hjj)
  have h2 := crossTail F hdepB (nA + nB) (fun jj => jj < nA + nB)
    (fun jj hjj => layer_le_mono hst hr hnn htot F
      (monotone_le_card B nB) (le_of_lt hjj))
  have hs : weightMass w (fun T => (T ∩ F).card = nA + nB
        ∧ nB ≤ (T ∩ B).card)
      = weightMass w (fun T => (T ∩ F).card = nA + nB
        ∧ (T ∩ A).card ≤ nA) := by
    refine weightMass_congr fun T => and_congr_right fun hN => ?_
    have := hcards T
    omega
  rw [hs] at h2
  have hpartition : weightMass w (fun T => (T ∩ A).card ≤ nA
        ∧ nB ≤ (T ∩ B).card)
      = weightMass w (fun T => (T ∩ A).card ≤ nA
          ∧ nA + nB ≤ (T ∩ F).card)
        + weightMass w (fun T => nB ≤ (T ∩ B).card
          ∧ (T ∩ F).card < nA + nB) := by
    have hor : weightMass w (fun T =>
          ((T ∩ A).card ≤ nA ∧ nA + nB ≤ (T ∩ F).card)
            ∨ (nB ≤ (T ∩ B).card ∧ (T ∩ F).card < nA + nB))
        + weightMass w (fun T =>
          ((T ∩ A).card ≤ nA ∧ nA + nB ≤ (T ∩ F).card)
            ∧ (nB ≤ (T ∩ B).card ∧ (T ∩ F).card < nA + nB))
        = weightMass w (fun T => (T ∩ A).card ≤ nA
          ∧ nA + nB ≤ (T ∩ F).card)
        + weightMass w (fun T => nB ≤ (T ∩ B).card
          ∧ (T ∩ F).card < nA + nB) :=
      weightMass_or w _ _
    have hnever : weightMass w (fun T =>
          ((T ∩ A).card ≤ nA ∧ nA + nB ≤ (T ∩ F).card)
            ∧ (nB ≤ (T ∩ B).card ∧ (T ∩ F).card < nA + nB))
        = weightMass w (fun _ : Finset ι => False) :=
      weightMass_congr fun T => by
        constructor
        · rintro ⟨⟨-, hu⟩, -, hv⟩
          omega
        · exact fun h => h.elim
    have hcover : weightMass w (fun T =>
          ((T ∩ A).card ≤ nA ∧ nA + nB ≤ (T ∩ F).card)
            ∨ (nB ≤ (T ∩ B).card ∧ (T ∩ F).card < nA + nB))
        = weightMass w (fun T => (T ∩ A).card ≤ nA
          ∧ nB ≤ (T ∩ B).card) := by
      refine weightMass_congr fun T => ?_
      have hT := hcards T
      constructor
      · rintro (⟨hA1, hN⟩ | ⟨hB1, hN⟩)
        · exact ⟨hA1, by omega⟩
        · exact ⟨by omega, hB1⟩
      · rintro ⟨hA1, hB1⟩
        by_cases hN : nA + nB ≤ (T ∩ F).card
        · exact Or.inl ⟨hA1, hN⟩
        · exact Or.inr ⟨hB1, by omega⟩
    rw [hnever, weightMass_false, add_zero] at hor
    rw [← hcover]
    exact hor
  have htails : weightMass w (fun T => nA + nB ≤ (T ∩ F).card)
      + weightMass w (fun T => (T ∩ F).card < nA + nB)
      = totalMass w := by
    have hnot : weightMass w (fun T => ¬ (nA + nB ≤ (T ∩ F).card))
        = totalMass w
          - weightMass w (fun T => nA + nB ≤ (T ∩ F).card) :=
      weightMass_not w _
    have hc : weightMass w (fun T => ¬ (nA + nB ≤ (T ∩ F).card))
        = weightMass w (fun T => (T ∩ F).card < nA + nB) :=
      weightMass_congr fun T => by omega
    linarith
  set m := weightMass w (fun T => (T ∩ F).card = nA + nB) with hm
  set s := weightMass w (fun T => (T ∩ F).card = nA + nB
    ∧ (T ∩ A).card ≤ nA) with hsdef
  have hsum : m * weightMass w (fun T => (T ∩ A).card ≤ nA
        ∧ nB ≤ (T ∩ B).card) ≤ s * totalMass w := by
    rw [hpartition, mul_add, ← htails, mul_add]
    exact add_le_add h1 h2
  have hpos := mixed_events_posCorrelation' hnn hr
    (fun S _ => Finset.subset_univ S) (rayleighNonneg_genPoly hst)
    (antitone_card_le A nA) (monotone_le_card B nB)
    (eventDependsOn_card_le A nA) (eventDependsOn_le_card B nB)
    (Finset.subset_univ A) (Finset.subset_univ B) hAB
  unfold PosCorrelated at hpos
  have hm_nn : 0 ≤ m := weightMass_nonneg hnn _
  have hM_nn : 0 ≤ totalMass w := totalMass_nonneg hnn
  calc m * (weightMass w (fun T => (T ∩ A).card ≤ nA)
        * weightMass w (fun T => nB ≤ (T ∩ B).card))
      ≤ m * (weightMass w (fun T => (T ∩ A).card ≤ nA
          ∧ nB ≤ (T ∩ B).card) * totalMass w) :=
        mul_le_mul_of_nonneg_left hpos hm_nn
    _ = (m * weightMass w (fun T => (T ∩ A).card ≤ nA
          ∧ nB ≤ (T ∩ B).card)) * totalMass w := by ring
    _ ≤ (s * totalMass w) * totalMass w :=
        mul_le_mul_of_nonneg_right hsum hM_nn
    _ = s * (totalMass w * totalMass w) := by ring

/-- **KKO21 Lemma 5.4** (`A ≥, B ≤` direction), the mirror: the partition
is `{A ≥ n_A, N ≤ n} ⊔ {B ≤ n_B, N > n}`. -/
theorem layerProduct_le_of_ge_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (nA nB : ℕ) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = nA + nB)
        * (weightMass w (fun T => nA ≤ (T ∩ A).card)
          * weightMass w (fun T => (T ∩ B).card ≤ nB))
      ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = nA + nB
            ∧ nA ≤ (T ∩ A).card)
        * (totalMass w * totalMass w) := by
  classical
  set F := A ∪ B with hF
  have hcards : ∀ T : Finset ι,
      (T ∩ F).card = (T ∩ A).card + (T ∩ B).card := fun T => by
    rw [hF]
    exact card_inter_union_of_disjoint hAB T
  have hdepA : EventDependsOn (fun T => nA ≤ (T ∩ A).card) F :=
    (eventDependsOn_le_card A nA).mono Finset.subset_union_left
  have hdepB : EventDependsOn (fun T => (T ∩ B).card ≤ nB) F :=
    (eventDependsOn_card_le B nB).mono Finset.subset_union_right
  have h1 := crossTail F hdepA (nA + nB) (fun jj => jj ≤ nA + nB)
    (fun jj hjj => layer_le_mono hst hr hnn htot F
      (monotone_le_card A nA) hjj)
  have h2 := crossTail F hdepB (nA + nB) (fun jj => nA + nB < jj)
    (fun jj hjj => layer_le_anti hst hr hnn htot F
      (antitone_card_le B nB) (le_of_lt hjj))
  have hs : weightMass w (fun T => (T ∩ F).card = nA + nB
        ∧ (T ∩ B).card ≤ nB)
      = weightMass w (fun T => (T ∩ F).card = nA + nB
        ∧ nA ≤ (T ∩ A).card) := by
    refine weightMass_congr fun T => and_congr_right fun hN => ?_
    have := hcards T
    omega
  rw [hs] at h2
  have hpartition : weightMass w (fun T => nA ≤ (T ∩ A).card
        ∧ (T ∩ B).card ≤ nB)
      = weightMass w (fun T => nA ≤ (T ∩ A).card
          ∧ (T ∩ F).card ≤ nA + nB)
        + weightMass w (fun T => (T ∩ B).card ≤ nB
          ∧ nA + nB < (T ∩ F).card) := by
    have hor : weightMass w (fun T =>
          (nA ≤ (T ∩ A).card ∧ (T ∩ F).card ≤ nA + nB)
            ∨ ((T ∩ B).card ≤ nB ∧ nA + nB < (T ∩ F).card))
        + weightMass w (fun T =>
          (nA ≤ (T ∩ A).card ∧ (T ∩ F).card ≤ nA + nB)
            ∧ ((T ∩ B).card ≤ nB ∧ nA + nB < (T ∩ F).card))
        = weightMass w (fun T => nA ≤ (T ∩ A).card
          ∧ (T ∩ F).card ≤ nA + nB)
        + weightMass w (fun T => (T ∩ B).card ≤ nB
          ∧ nA + nB < (T ∩ F).card) :=
      weightMass_or w _ _
    have hnever : weightMass w (fun T =>
          (nA ≤ (T ∩ A).card ∧ (T ∩ F).card ≤ nA + nB)
            ∧ ((T ∩ B).card ≤ nB ∧ nA + nB < (T ∩ F).card))
        = weightMass w (fun _ : Finset ι => False) :=
      weightMass_congr fun T => by
        constructor
        · rintro ⟨⟨-, hu⟩, -, hv⟩
          omega
        · exact fun h => h.elim
    have hcover : weightMass w (fun T =>
          (nA ≤ (T ∩ A).card ∧ (T ∩ F).card ≤ nA + nB)
            ∨ ((T ∩ B).card ≤ nB ∧ nA + nB < (T ∩ F).card))
        = weightMass w (fun T => nA ≤ (T ∩ A).card
          ∧ (T ∩ B).card ≤ nB) := by
      refine weightMass_congr fun T => ?_
      have hT := hcards T
      constructor
      · rintro (⟨hA1, hN⟩ | ⟨hB1, hN⟩)
        · exact ⟨hA1, by omega⟩
        · exact ⟨by omega, hB1⟩
      · rintro ⟨hA1, hB1⟩
        by_cases hN : (T ∩ F).card ≤ nA + nB
        · exact Or.inl ⟨hA1, hN⟩
        · exact Or.inr ⟨hB1, by omega⟩
    rw [hnever, weightMass_false, add_zero] at hor
    rw [← hcover]
    exact hor
  have htails : weightMass w (fun T => (T ∩ F).card ≤ nA + nB)
      + weightMass w (fun T => nA + nB < (T ∩ F).card)
      = totalMass w := by
    have hnot : weightMass w (fun T => ¬ ((T ∩ F).card ≤ nA + nB))
        = totalMass w
          - weightMass w (fun T => (T ∩ F).card ≤ nA + nB) :=
      weightMass_not w _
    have hc : weightMass w (fun T => ¬ ((T ∩ F).card ≤ nA + nB))
        = weightMass w (fun T => nA + nB < (T ∩ F).card) :=
      weightMass_congr fun T => by omega
    linarith
  set m := weightMass w (fun T => (T ∩ F).card = nA + nB) with hm
  set s := weightMass w (fun T => (T ∩ F).card = nA + nB
    ∧ nA ≤ (T ∩ A).card) with hsdef
  have hsum : m * weightMass w (fun T => nA ≤ (T ∩ A).card
        ∧ (T ∩ B).card ≤ nB) ≤ s * totalMass w := by
    rw [hpartition, mul_add, ← htails, mul_add]
    exact add_le_add h1 h2
  have hpos := mixed_events_posCorrelation hnn hr
    (fun S _ => Finset.subset_univ S) (rayleighNonneg_genPoly hst)
    (monotone_le_card A nA) (antitone_card_le B nB)
    (eventDependsOn_le_card A nA) (eventDependsOn_card_le B nB)
    (Finset.subset_univ A) (Finset.subset_univ B) hAB
  unfold PosCorrelated at hpos
  have hm_nn : 0 ≤ m := weightMass_nonneg hnn _
  have hM_nn : 0 ≤ totalMass w := totalMass_nonneg hnn
  calc m * (weightMass w (fun T => nA ≤ (T ∩ A).card)
        * weightMass w (fun T => (T ∩ B).card ≤ nB))
      ≤ m * (weightMass w (fun T => nA ≤ (T ∩ A).card
          ∧ (T ∩ B).card ≤ nB) * totalMass w) :=
        mul_le_mul_of_nonneg_left hpos hm_nn
    _ = (m * weightMass w (fun T => nA ≤ (T ∩ A).card
          ∧ (T ∩ B).card ≤ nB)) * totalMass w := by ring
    _ ≤ (s * totalMass w) * totalMass w :=
        mul_le_mul_of_nonneg_right hsum hM_nn
    _ = s * (totalMass w * totalMass w) := by ring

end TSPGap

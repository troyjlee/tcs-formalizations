/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ProjectedLayers
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# The marker calculus III: the adjacent-layer bridge

Increment 3 of the tagged-bridge route, in the mandated order.

**Preliminaries.**  `weightMass_projLayer` — the projected event-mass
bridge, with the `EventDependsOn Q F` adapter for original-space events;
`probCount_pos_iff` and `exists_layer_interval` — **Bernoulli interval
support**, proved *before* any global induction: the layer masses are
positive exactly on `[a, b] ⊆ [0, r]`, with the pointwise support bounds;
the promotions from stable-or-zero to stable.

**The certified descent.**  `markerStable_first_block` and
`markerStable_second_block` carry their certificates explicitly — the
first block's leading coefficient is always a positive multiple of `E_a`,
the second's a positive multiple of the already-established `E_{k+1}` —
and every `MarkerStableOrZero` is promoted back to `MarkerStable` through
a surviving nonzero coefficient, never chained.
`markerStable_adjacent_pair` is the marker-stable extracted pair.

**The tagged bridge.**  `taggedWeight w F k α β` on `Finset (Option ι)`:
marker present carries `α·(k`-layer`)`, absent `β·((k+1)`-layer`)` —
rank `k+1`, with `sum_option_split` the reindexing workhorse.
`isRealStable_genPoly_taggedWeight` transfers the pair's marker stability
by direct evaluation (marker to `z none`, coordinates to `z ∘ some`), and
`isRealStable_projLayer_of_tagged` harvests `E_k` back through the
marker-contraction and the face machinery's `X`-cancellation — the next
certificate of the downward induction, closed in
`isRealStable_projLayer_interval`.

**The zero-safe export.**  `adjacent_layer_mono`:
`e_k(Q)·m_{k+1} ≤ e_{k+1}(Q)·m_k` for every increasing `Q` and *every*
`k` — outside the interval a vanishing layer mass makes both sides zero;
inside, Feder–Mihail negative association between the marker and the
lifted event, applied to the bridge normalized branchwise by
`(m_{k+1}, m_k)` (no division in the weight), gives the inequality after
one cross-multiplied cancellation.  `adjacent_layer_anti` is the
complementation mirror for decreasing events.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The projected event-mass bridge -/

/-- **The event-mass bridge**: the mass an event `Q` on projected sets
receives from the `j`-layer is the original mass of "the projection is in
the `j`-layer and satisfies `Q`". -/
theorem weightMass_projLayer (w : Finset ι → ℝ) (F : Finset ι) (j : ℕ)
    (Q : Finset ι → Prop) :
    weightMass (projLayer w F j) Q
      = weightMass w fun S => (S ∩ F).card = j ∧ Q (S ∩ F) := by
  classical
  rw [weightMass, weightMass]
  have hU : ∀ U : Finset ι, (if Q U then projLayer w F j U else 0)
      = ∑ S ∈ Finset.univ.filter (fun S => S ∩ F = U),
          (if (S ∩ F).card = j ∧ Q (S ∩ F) then w S else 0) := by
    intro U
    by_cases hQ : Q U
    · rw [if_pos hQ, projLayer]
      split_ifs with hcard
      · refine Finset.sum_congr rfl fun S hS => ?_
        rw [(Finset.mem_filter.mp hS).2, if_pos ⟨hcard, hQ⟩]
      · symm
        refine Finset.sum_eq_zero fun S hS => ?_
        rw [(Finset.mem_filter.mp hS).2, if_neg fun hc => hcard hc.1]
    · rw [if_neg hQ]
      symm
      refine Finset.sum_eq_zero fun S hS => ?_
      rw [(Finset.mem_filter.mp hS).2, if_neg fun hc => hQ hc.2]
  rw [Finset.sum_congr rfl fun U _ => hU U,
    Finset.sum_fiberwise Finset.univ (fun S : Finset ι => S ∩ F)
      (fun S => if (S ∩ F).card = j ∧ Q (S ∩ F) then w S else 0)]
  exact Finset.sum_congr rfl fun S _ => by
    by_cases h : (S ∩ F).card = j ∧ Q (S ∩ F) <;> simp [h]

/-- The adapter for original-space events: under `EventDependsOn Q F` the
projection in the event may be dropped. -/
theorem weightMass_projLayer_of_dependsOn (w : Finset ι → ℝ)
    {F : Finset ι} (j : ℕ) {Q : Finset ι → Prop}
    (hQ : EventDependsOn Q F) :
    weightMass (projLayer w F j) Q
      = weightMass w fun S => (S ∩ F).card = j ∧ Q S := by
  rw [weightMass_projLayer]
  refine weightMass_congr fun S => ?_
  exact and_congr_right fun _ =>
    hQ (S ∩ F) S (by rw [Finset.inter_assoc, Finset.inter_self])

/-! ### Bernoulli interval support -/

omit [DecidableEq ι] in
/-- A weight-mass event with positive mass has a supported witness. -/
theorem exists_of_weightMass_pos {w : Finset ι → ℝ}
    {Q : Finset ι → Prop} (h : 0 < weightMass w Q) :
    ∃ S, Q S ∧ w S ≠ 0 := by
  classical
  rw [weightMass] at h
  obtain ⟨S, -, hS⟩ := Finset.exists_lt_of_sum_lt
    (f := fun _ : Finset ι => (0 : ℝ)) (by simpa using h)
  by_cases hQ : Q S
  · rw [if_pos hQ] at hS
    exact ⟨S, hQ, fun h0 => by rw [h0] at hS; exact lt_irrefl 0 hS⟩
  · rw [if_neg hQ] at hS
    exact absurd hS (lt_irrefl 0)

/-- **Bernoulli interval support**: with every success probability in
`(0, 1]`, exactly the counts between the number `a` of deterministic
successes and the number `m` of coordinates are hit. -/
theorem probCount_pos_iff {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q : κ → ℝ} (hq : ∀ i, 0 < q i ∧ q i ≤ 1) (j : ℕ) :
    0 < Bernoulli.probCount q j
      ↔ (Finset.univ.filter fun i => q i = 1).card ≤ j
        ∧ j ≤ Fintype.card κ := by
  classical
  have hatom_nonneg : ∀ t : Finset κ, 0 ≤ Bernoulli.atomProb q t := by
    intro t
    rw [Bernoulli.atomProb]
    refine mul_nonneg (Finset.prod_nonneg fun i _ => (hq i).1.le)
      (Finset.prod_nonneg fun i _ => ?_)
    linarith [(hq i).2]
  constructor
  · intro hpos
    constructor
    · by_contra hc
      rw [Bernoulli.probCount_eq_zero_of_lt q
        (Finset.univ.filter fun i => q i = 1)
        (fun i hi => (Finset.mem_filter.mp hi).2) (by omega)] at hpos
      exact lt_irrefl 0 hpos
    · by_contra hc
      have hempty : Finset.univ.powersetCard j = (∅ : Finset (Finset κ)) :=
        Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_univ]; omega)
      rw [Bernoulli.probCount_def, hempty, Finset.sum_empty] at hpos
      exact lt_irrefl 0 hpos
  · rintro ⟨ha, hb⟩
    set D := Finset.univ.filter fun i : κ => q i = 1 with hD
    obtain ⟨E, hE_sub, hE_card⟩ := Finset.exists_subset_card_eq
      (s := Dᶜ) (n := j - D.card) (by rw [Finset.card_compl]; omega)
    have hdisj : Disjoint D E := Finset.disjoint_left.mpr
      fun i hiD hiE => (Finset.mem_compl.mp (hE_sub hiE)) hiD
    have ht_card : (D ∪ E).card = j := by
      rw [Finset.card_union_of_disjoint hdisj, hE_card]
      omega
    have hatom : 0 < Bernoulli.atomProb q (D ∪ E) := by
      rw [Bernoulli.atomProb]
      refine mul_pos (Finset.prod_pos fun i _ => (hq i).1)
        (Finset.prod_pos fun i hi => ?_)
      have hit : i ∉ D ∪ E := (Finset.mem_sdiff.mp hi).2
      have hiD : i ∉ D := fun h => hit (Finset.mem_union_left _ h)
      have hne : q i ≠ 1 := fun h =>
        hiD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have := lt_of_le_of_ne (hq i).2 hne
      linarith
    calc (0 : ℝ) < Bernoulli.atomProb q (D ∪ E) := hatom
      _ ≤ Bernoulli.probCount q j := by
          rw [Bernoulli.probCount_def]
          exact Finset.single_le_sum (fun t _ => hatom_nonneg t)
            (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ht_card⟩)

/-- **The layer interval**: through the Bernoulli rank law, the projected
layers of a normalized stable fixed-rank weight have positive mass exactly
on an interval `[a, b] ⊆ [0, r]`, and every supported set meets `F` in
`[a, b]` coordinates. -/
theorem exists_layer_interval {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ r ∧
      (∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ b) ∧
      ∀ S, w S ≠ 0 → a ≤ (S ∩ F).card ∧ (S ∩ F).card ≤ b := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  set a := (Finset.univ.filter fun i : Fin m => q i = 1).card with ha
  have hmass : ∀ j, totalMass (projLayer w F j) = Bernoulli.probCount q j :=
    fun j => by rw [totalMass_projLayer]; exact hlaw j
  have hiff : ∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ m := by
    intro j
    rw [hmass j, probCount_pos_iff hq j, Fintype.card_fin]
  have hab : a ≤ m := by
    have := Finset.card_le_univ (Finset.univ.filter fun i : Fin m => q i = 1)
    rwa [Fintype.card_fin] at this
  have hbm : 0 < totalMass (projLayer w F m) := (hiff m).mpr ⟨hab, le_rfl⟩
  have hbr : m ≤ r := by
    rw [totalMass_projLayer] at hbm
    obtain ⟨S, hSm, hS0⟩ := exists_of_weightMass_pos hbm
    calc m = (S ∩ F).card := hSm.symm
      _ ≤ S.card := Finset.card_le_card Finset.inter_subset_left
      _ = r := hr S hS0
  refine ⟨a, m, hab, hbr, hiff, fun S hS0 => ?_⟩
  have hpos : 0 < totalMass (projLayer w F ((S ∩ F).card)) := by
    rw [totalMass_projLayer]
    refine lt_of_lt_of_le ?_ (le_weightMass hnn rfl)
    exact lt_of_le_of_ne (hnn S) (Ne.symm hS0)
  exact (hiff _).mp hpos

/-! ### Promotions -/

omit [Fintype ι] [DecidableEq ι] in
/-- Positive integer multiples preserve stability. -/
theorem isRealStable_nsmul {q : MvPolynomial ι ℝ} (h : IsRealStable q)
    {n : ℕ} (hn : 0 < n) : IsRealStable (n • q) := by
  intro z hz
  rw [show ((n • q).map (algebraMap ℝ ℂ))
      = n • (q.map (algebraMap ℝ ℂ)) from map_nsmul _ _ _,
    map_nsmul, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (h z hz)

omit [Fintype ι] [DecidableEq ι] in
/-- ... and reflect it: stability of a positive multiple returns stability. -/
theorem isRealStable_of_nsmul {q : MvPolynomial ι ℝ} {n : ℕ}
    (h : IsRealStable (n • q)) : IsRealStable q := by
  intro z hz
  have := h z hz
  rw [show ((n • q).map (algebraMap ℝ ℂ))
      = n • (q.map (algebraMap ℝ ℂ)) from map_nsmul _ _ _,
    map_nsmul, nsmul_eq_mul] at this
  exact fun hc => this (by rw [hc, mul_zero])

/-- **The promotion**: a stable-or-zero layer with positive mass is stable. -/
theorem isRealStable_projLayer_of_pos {w : Finset ι → ℝ} {F : Finset ι}
    {j : ℕ} (hOrZero : IsRealStableOrZero (genPoly (projLayer w F j)))
    (hmass : 0 < totalMass (projLayer w F j)) :
    IsRealStable (genPoly (projLayer w F j)) := by
  rcases hOrZero with h0 | h
  · exfalso
    have hzero : projLayer w F j = fun _ => (0 : ℝ) :=
      genPoly_injective (ι := ι) (by rw [h0, genPoly_zero])
    rw [totalMass, hzero] at hmass
    simp at hmass
  · exact h

/-- **The endpoint promotions**: the extreme layers of the interval are
genuinely stable — the certificates the descent starts from. -/
theorem isRealStable_projLayer_endpoints {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {a b : ℕ} (hab : a ≤ b)
    (hbr : b ≤ r)
    (hiff : ∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ b)
    (hsupp : ∀ S, w S ≠ 0 → a ≤ (S ∩ F).card ∧ (S ∩ F).card ≤ b) :
    IsRealStable (genPoly (projLayer w F a))
      ∧ IsRealStable (genPoly (projLayer w F b)) := by
  constructor
  · exact isRealStable_projLayer_of_pos
      (isRealStableOrZero_projLayer_min hst hr hnn (by omega)
        fun S h0 => (hsupp S h0).1)
      ((hiff a).mpr ⟨le_rfl, hab⟩)
  · exact isRealStable_projLayer_of_pos
      (isRealStableOrZero_projLayer_max hst hr hnn hbr
        fun S h0 => (hsupp S h0).2)
      ((hiff b).mpr ⟨hab, le_rfl⟩)

/-! ### The certified descent

Both derivative blocks carry their certificates explicitly: the first
block's leading coefficient is always a positive multiple of `E_a`, the
second block's a positive multiple of the already-established `E_{k+1}`.
Every `MarkerStableOrZero` result is promoted back to `MarkerStable`
through a surviving nonzero coefficient — the OrZero results are never
chained. -/

omit [Fintype ι] [DecidableEq ι] in
theorem MarkerStable.neg {P : Polynomial (MvPolynomial ι ℝ)}
    (h : MarkerStable P) : MarkerStable (-P) := by
  intro z y hz hy
  rw [Polynomial.eval₂_neg]
  exact neg_ne_zero.mpr (h z y hz hy)

omit [Fintype ι] [DecidableEq ι] in
/-- The promotion pattern: stable-or-zero plus one surviving coefficient. -/
theorem markerStable_of_orZero_coeff {P : Polynomial (MvPolynomial ι ℝ)}
    (h : MarkerStableOrZero P) {n : ℕ} (hc : P.coeff n ≠ 0) :
    MarkerStable P := by
  rcases h with rfl | h
  · exact absurd (Polynomial.coeff_zero n) hc
  · exact h

omit [Fintype ι] [DecidableEq ι] in
theorem natDegree_leadingCoeff_of_coeff {P : Polynomial (MvPolynomial ι ℝ)}
    {d : ℕ} (htop : P.coeff d ≠ 0)
    (hvanish : ∀ n, d < n → P.coeff n = 0) :
    P.natDegree = d ∧ P.leadingCoeff = P.coeff d := by
  have hdeg : P.natDegree = d := le_antisymm
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hvanish)
    (Polynomial.le_natDegree_of_ne_zero htop)
  exact ⟨hdeg,
    by rw [show P.leadingCoeff = P.coeff P.natDegree from rfl, hdeg]⟩

/-- A layer with vanishing mass vanishes outright. -/
theorem genPoly_projLayer_eq_zero_of_mass {w : Finset ι → ℝ}
    {F : Finset ι} {j : ℕ} (hnn : WeightNonneg w)
    (h : ¬ 0 < totalMass (projLayer w F j)) :
    genPoly (projLayer w F j) = 0 := by
  have hnn' := weightNonneg_projLayer hnn F j
  have h0 : totalMass (projLayer w F j) = 0 :=
    le_antisymm (not_lt.mp h) (totalMass_nonneg hnn')
  rw [totalMass] at h0
  have hz : projLayer w F j = fun _ => (0 : ℝ) := funext fun U =>
    (Finset.sum_eq_zero_iff_of_nonneg fun S _ => hnn' S).mp h0 U
      (Finset.mem_univ U)
  rw [hz, genPoly_zero]

/-- **The first derivative block is marker-stable at every stage**, with
`E_a` certifying each step. -/
theorem markerStable_first_block {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {a b : ℕ} (har : a ≤ r)
    (hiff : ∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ b)
    (hEa : IsRealStable (genPoly (projLayer w F a))) :
    ∀ i, i ≤ r - a →
      MarkerStable (Polynomial.derivative^[i] (markerPoly w F r)) := by
  have hzero_layer : ∀ j, j < a → genPoly (projLayer w F j) = 0 :=
    fun j hj => genPoly_projLayer_eq_zero_of_mass hnn
      fun hpos => by have := (hiff j).mp hpos; omega
  have hEa_ne : genPoly (projLayer w F a) ≠ 0 := hEa.ne_zero
  have htop : ∀ i, i ≤ r - a →
      (Polynomial.derivative^[i] (markerPoly w F r)).coeff (r - a - i)
        ≠ 0 := by
    intro i hi
    rw [Polynomial.coeff_iterate_derivative,
      show r - a - i + i = r - a from by omega, coeff_markerPoly,
      if_pos (by omega : r - a ≤ r), show r - (r - a) = a from by omega,
      ← Nat.cast_smul_eq_nsmul ℝ]
    exact smul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hi).ne') hEa_ne
  have hvanish : ∀ i n, r - a - i < n →
      (Polynomial.derivative^[i] (markerPoly w F r)).coeff n = 0 := by
    intro i n hn
    rw [Polynomial.coeff_iterate_derivative, coeff_markerPoly]
    by_cases hle : n + i ≤ r
    · rw [if_pos hle, hzero_layer (r - (n + i)) (by omega), smul_zero]
    · rw [if_neg hle, smul_zero]
  intro i hi
  induction i with
  | zero => exact markerStable_markerPoly hst hr F
  | succ i ih =>
    have hi' : i ≤ r - a := by omega
    have hlead : IsRealStableOrZero
        (Polynomial.derivative^[i] (markerPoly w F r)).leadingCoeff := by
      obtain ⟨-, hlc⟩ :=
        natDegree_leadingCoeff_of_coeff (htop i hi') (hvanish i)
      rw [hlc, Polynomial.coeff_iterate_derivative,
        show r - a - i + i = r - a from by omega, coeff_markerPoly,
        if_pos (by omega : r - a ≤ r), show r - (r - a) = a from by omega]
      exact Or.inr (isRealStable_nsmul hEa
        (Nat.descFactorial_pos.mpr hi'))
    have hOZ := markerStableOrZero_derivative (ih hi') hlead
    rw [← Function.iterate_succ_apply' Polynomial.derivative i
      (markerPoly w F r)] at hOZ
    exact markerStable_of_orZero_coeff hOZ (htop (i + 1) hi)

/-- **The second derivative block is marker-stable at every stage**, with
the already-established `E_{k+1}` certifying each step. -/
theorem markerStable_second_block {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {a b k : ℕ}
    (hiff : ∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ b)
    (hEa : IsRealStable (genPoly (projLayer w F a)))
    (hak : a ≤ k) (hkb : k + 1 ≤ b) (hbr : b ≤ r)
    (hEk1 : IsRealStable (genPoly (projLayer w F (k + 1)))) :
    ∀ j, j ≤ k →
      MarkerStable (Polynomial.derivative^[j] (markerReflect (k + 1)
        (Polynomial.derivative^[r - (k + 1)] (markerPoly w F r)))) := by
  have hk1r : k + 1 ≤ r := by omega
  have hEk1_ne : genPoly (projLayer w F (k + 1)) ≠ 0 := hEk1.ne_zero
  have htop : ∀ j, j ≤ k →
      (Polynomial.derivative^[j] (markerReflect (k + 1)
        (Polynomial.derivative^[r - (k + 1)]
          (markerPoly w F r)))).coeff (k + 1 - j) ≠ 0 := by
    intro j hj
    rw [Polynomial.coeff_iterate_derivative,
      show k + 1 - j + j = k + 1 from by omega,
      coeff_reflect_iterate_markerPoly w F hk1r,
      if_pos (le_refl (k + 1)),
      show k + 1 - (k + 1) = 0 from by omega, pow_zero, one_mul,
      Nat.descFactorial_self, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ]
    refine smul_ne_zero (Nat.cast_ne_zero.mpr ?_) hEk1_ne
    exact (Nat.mul_pos (Nat.descFactorial_pos.mpr (by omega))
      (Nat.factorial_pos _)).ne'
  have hvanish : ∀ j n, k + 1 - j < n →
      (Polynomial.derivative^[j] (markerReflect (k + 1)
        (Polynomial.derivative^[r - (k + 1)]
          (markerPoly w F r)))).coeff n = 0 := by
    intro j n hn
    rw [Polynomial.coeff_iterate_derivative,
      coeff_reflect_iterate_markerPoly w F hk1r,
      if_neg (by omega : ¬ n + j ≤ k + 1), smul_zero]
  intro j hj
  induction j with
  | zero =>
    refine (markerStable_first_block hst hr hnn (by omega : a ≤ r) hiff hEa
      (r - (k + 1)) (by omega)).markerReflect ?_
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
      rw [coeff_iterate_markerPoly w F hk1r, if_neg (not_le.mpr hm)]
  | succ j ih =>
    have hj' : j ≤ k := by omega
    have hlead : IsRealStableOrZero
        (Polynomial.derivative^[j] (markerReflect (k + 1)
          (Polynomial.derivative^[r - (k + 1)]
            (markerPoly w F r)))).leadingCoeff := by
      obtain ⟨-, hlc⟩ :=
        natDegree_leadingCoeff_of_coeff (htop j hj') (hvanish j)
      rw [hlc, Polynomial.coeff_iterate_derivative,
        show k + 1 - j + j = k + 1 from by omega,
        coeff_reflect_iterate_markerPoly w F hk1r,
        if_pos (le_refl (k + 1)),
        show k + 1 - (k + 1) = 0 from by omega, pow_zero, one_mul,
        Nat.descFactorial_self, smul_smul]
      exact Or.inr (isRealStable_nsmul hEk1
        (Nat.mul_pos (Nat.descFactorial_pos.mpr (by omega))
          (Nat.factorial_pos _)))
    have hOZ := markerStableOrZero_derivative (ih hj') hlead
    rw [← Function.iterate_succ_apply' Polynomial.derivative j
      (markerReflect (k + 1) (Polynomial.derivative^[r - (k + 1)]
        (markerPoly w F r)))] at hOZ
    exact markerStable_of_orZero_coeff hOZ (htop (j + 1) hj)

/-- **The extracted adjacent pair is marker-stable**:
`C (B•E_{k+1}) + C (A•E_k)·X` with `A = k!(r−k)!`, `B = (k+1)!(r−(k+1))!`. -/
theorem markerStable_adjacent_pair {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {a b k : ℕ}
    (hiff : ∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ b)
    (hEa : IsRealStable (genPoly (projLayer w F a)))
    (hak : a ≤ k) (hkb : k + 1 ≤ b) (hbr : b ≤ r)
    (hEk1 : IsRealStable (genPoly (projLayer w F (k + 1)))) :
    MarkerStable
      (Polynomial.C (((k + 1).factorial * (r - (k + 1)).factorial)
          • genPoly (projLayer w F (k + 1)))
        + Polynomial.C ((k.factorial * (r - k).factorial)
            • genPoly (projLayer w F k)) * Polynomial.X) := by
  have hk1r : k + 1 ≤ r := by omega
  have hC := markerStable_second_block hst hr hnn hiff hEa hak hkb hbr
    hEk1 k le_rfl
  have hCdeg : (Polynomial.derivative^[k] (markerReflect (k + 1)
      (Polynomial.derivative^[r - (k + 1)]
        (markerPoly w F r)))).natDegree ≤ 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
      rw [coeff_second_block w F hk1r, if_neg (by omega : ¬ m = 0),
        if_neg (by omega : ¬ m = 1)]
  have hfinal := (hC.markerReflect hCdeg).neg
  rwa [extraction_adjacent w F hk1r] at hfinal

/-! ### The tagged bridge weight -/

omit [Fintype ι] [DecidableEq ι] in
theorem eraseNone_insertNone' (V : Finset ι) :
    Finset.eraseNone (Finset.insertNone V) = V := by
  ext x
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem none_notMem_map_some (V : Finset ι) :
    (none : Option ι) ∉ V.map Function.Embedding.some := by
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem map_some_eraseNone_of_notMem {T : Finset (Option ι)}
    (h : none ∉ T) :
    (Finset.eraseNone T).map Function.Embedding.some = T := by
  ext o
  cases o with
  | none => simp [h]
  | some x => simp

omit [Fintype ι] [DecidableEq ι] in
theorem insertNone_eraseNone_of_mem {T : Finset (Option ι)}
    (h : none ∈ T) : Finset.insertNone (Finset.eraseNone T) = T := by
  ext o
  cases o with
  | none => simp [h]
  | some x => simp

omit [Fintype ι] in
theorem insertNone_eq_insert (V : Finset ι) :
    Finset.insertNone V = insert none (V.map Function.Embedding.some) := by
  ext o
  cases o <;> simp

omit [Fintype ι] in
theorem eraseNone_insert_none (T : Finset (Option ι)) :
    Finset.eraseNone (insert none T) = Finset.eraseNone T := by
  ext x
  simp

omit [DecidableEq ι] in
/-- Summation over `Finset (Option ι)` splits along the marker. -/
theorem sum_option_split {M : Type*} [AddCommMonoid M]
    (f : Finset (Option ι) → M) :
    ∑ T : Finset (Option ι), f T
      = ∑ V : Finset ι, f (Finset.insertNone V)
        + ∑ V : Finset ι, f (V.map Function.Embedding.some) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun T : Finset (Option ι) => none ∈ T)]
  congr 1
  · refine Finset.sum_nbij' (fun T => Finset.eraseNone T)
      (fun V => Finset.insertNone V) ?_ ?_ ?_ ?_ ?_
    · intro T _
      exact Finset.mem_univ _
    · intro V _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact Finset.none_mem_insertNone
    · intro T hT
      exact insertNone_eraseNone_of_mem (Finset.mem_filter.mp hT).2
    · intro V _
      exact eraseNone_insertNone' V
    · intro T hT
      rw [insertNone_eraseNone_of_mem (Finset.mem_filter.mp hT).2]
  · refine Finset.sum_nbij' (fun T => Finset.eraseNone T)
      (fun V => V.map Function.Embedding.some) ?_ ?_ ?_ ?_ ?_
    · intro T _
      exact Finset.mem_univ _
    · intro V _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact none_notMem_map_some V
    · intro T hT
      exact map_some_eraseNone_of_notMem (Finset.mem_filter.mp hT).2
    · intro V _
      exact Finset.eraseNone_map_some V
    · intro T hT
      rw [map_some_eraseNone_of_notMem (Finset.mem_filter.mp hT).2]

/-- The **tagged weight**: marker present carries the scaled `k`-layer,
marker absent the scaled `(k+1)`-layer. -/
noncomputable def taggedWeight (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ)
    (α β : ℝ) : Finset (Option ι) → ℝ :=
  fun T => if none ∈ T then α * projLayer w F k (Finset.eraseNone T)
           else β * projLayer w F (k + 1) (Finset.eraseNone T)

theorem weightNonneg_taggedWeight {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) (k : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    WeightNonneg (taggedWeight w F k α β) := by
  intro T
  rw [taggedWeight]
  split_ifs
  · exact mul_nonneg hα (weightNonneg_projLayer hnn F k _)
  · exact mul_nonneg hβ (weightNonneg_projLayer hnn F (k + 1) _)

theorem fixedRankWeight_taggedWeight (w : Finset ι → ℝ) (F : Finset ι)
    (k : ℕ) (α β : ℝ) :
    FixedRankWeight (k + 1) (taggedWeight w F k α β) := by
  intro T hT
  rw [taggedWeight] at hT
  split_ifs at hT with h
  · have hproj : projLayer w F k (Finset.eraseNone T) ≠ 0 :=
      fun h0 => hT (by rw [h0, mul_zero])
    have hcard := fixedRankWeight_projLayer w F k _ hproj
    rw [← insertNone_eraseNone_of_mem h, Finset.card_insertNone, hcard]
  · have hproj : projLayer w F (k + 1) (Finset.eraseNone T) ≠ 0 :=
      fun h0 => hT (by rw [h0, mul_zero])
    have hcard := fixedRankWeight_projLayer w F (k + 1) _ hproj
    rw [← map_some_eraseNone_of_notMem h, Finset.card_map, hcard]

/-- Event masses of the tagged weight, branch by branch. -/
theorem weightMass_taggedWeight (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ)
    (α β : ℝ) (P : Finset (Option ι) → Prop) :
    weightMass (taggedWeight w F k α β) P
      = α * weightMass (projLayer w F k)
            (fun V => P (Finset.insertNone V))
        + β * weightMass (projLayer w F (k + 1))
            (fun V => P (V.map Function.Embedding.some)) := by
  classical
  rw [weightMass, sum_option_split
    (f := fun T => if P T then taggedWeight w F k α β T else 0)]
  congr 1
  · rw [weightMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [taggedWeight, if_pos Finset.none_mem_insertNone,
      eraseNone_insertNone' V]
    split_ifs <;> ring
  · rw [weightMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [taggedWeight, if_neg (none_notMem_map_some V),
      Finset.eraseNone_map_some V]
    split_ifs <;> ring

theorem totalMass_taggedWeight (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ)
    (α β : ℝ) :
    totalMass (taggedWeight w F k α β)
      = α * totalMass (projLayer w F k)
        + β * totalMass (projLayer w F (k + 1)) := by
  rw [← weightMass_true, weightMass_taggedWeight, weightMass_true,
    weightMass_true]

/-- **Stability of the tagged weight**, from marker stability of the
adjacent pair, by direct evaluation — the marker goes to `z none`, the
coordinates to `z ∘ some`. -/
theorem isRealStable_genPoly_taggedWeight {w : Finset ι → ℝ}
    {F : Finset ι} {k : ℕ} {α β : ℝ} (hpair : MarkerStable
      (Polynomial.C (β • genPoly (projLayer w F (k + 1)))
        + Polynomial.C (α • genPoly (projLayer w F k)) * Polynomial.X)) :
    IsRealStable (genPoly (taggedWeight w F k α β)) := by
  have hsm : ∀ (c : ℝ) (q : MvPolynomial ι ℝ) (z : ι → ℂ),
      coeffHom z (c • q) = (algebraMap ℝ ℂ) c * coeffHom z q := by
    intro c q z
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    congr 1
    rw [coeffHom_apply]
    simp
  intro z hz
  have heval : MvPolynomial.eval z
      ((genPoly (taggedWeight w F k α β)).map (algebraMap ℝ ℂ))
      = Polynomial.eval₂ (coeffHom (fun i => z (some i))) (z none)
          (Polynomial.C (β • genPoly (projLayer w F (k + 1)))
            + Polynomial.C (α • genPoly (projLayer w F k))
              * Polynomial.X) := by
    rw [eval_map_genPoly, sum_option_split
      (f := fun T => (algebraMap ℝ ℂ) (taggedWeight w F k α β T)
        * ∏ o ∈ T, z o)]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, Polynomial.eval₂_X, hsm, hsm,
      coeffHom_apply, coeffHom_apply, eval_map_genPoly, eval_map_genPoly]
    have hprod : ∀ V : Finset ι, ∏ o ∈ Finset.insertNone V, z o
        = z none * ∏ i ∈ V, z (some i) := by
      intro V
      rw [insertNone_eq_insert, Finset.prod_insert (none_notMem_map_some V),
        Finset.prod_map]
      rfl
    have h1 : ∑ V : Finset ι,
        (algebraMap ℝ ℂ) (taggedWeight w F k α β (Finset.insertNone V))
          * ∏ o ∈ Finset.insertNone V, z o
        = (algebraMap ℝ ℂ) α
            * (∑ U : Finset ι, (algebraMap ℝ ℂ) (projLayer w F k U)
              * ∏ i ∈ U, z (some i)) * z none := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun V _ => ?_
      rw [taggedWeight, if_pos Finset.none_mem_insertNone,
        eraseNone_insertNone' V, hprod V, map_mul]
      ring
    have h2 : ∑ V : Finset ι,
        (algebraMap ℝ ℂ) (taggedWeight w F k α β
          (V.map Function.Embedding.some))
          * ∏ o ∈ V.map Function.Embedding.some, z o
        = (algebraMap ℝ ℂ) β
            * ∑ U : Finset ι, (algebraMap ℝ ℂ) (projLayer w F (k + 1) U)
              * ∏ i ∈ U, z (some i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun V _ => ?_
      rw [taggedWeight, if_neg (none_notMem_map_some V),
        Finset.eraseNone_map_some V, Finset.prod_map, map_mul]
      simp only [Function.Embedding.some_apply]
      ring
    rw [h1, h2]
    ring
  rw [heval]
  exact hpair _ _ (fun i => hz (some i)) (hz none)

/-- **The descent's harvest**: the marker-contraction of the tagged weight
is the `k`-layer, so its stability comes back through the `X`-cancellation
of the face machinery. -/
theorem isRealStable_projLayer_of_tagged {w : Finset ι → ℝ}
    {F : Finset ι} {k : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hnn : WeightNonneg w)
    (hstU : IsRealStable (genPoly (taggedWeight w F k α β)))
    (hmass : 0 < totalMass (projLayer w F k)) :
    IsRealStable (genPoly (projLayer w F k)) := by
  classical
  have hcon := isRealStableOrZero_genPoly_contractWeight hstU
    (fixedRankWeight_taggedWeight w F k α β)
    (weightNonneg_taggedWeight hnn F k hα.le hβ.le) none
  have hid : contractWeight (taggedWeight w F k α β) none
      = fun V' : Finset (Option ι) =>
          if none ∈ V' then 0
          else α * projLayer w F k (Finset.eraseNone V') := by
    funext V'
    rw [contractWeight]
    split_ifs with h
    · rfl
    · rw [taggedWeight, if_pos (Finset.mem_insert_self none V'),
        eraseNone_insert_none]
  rw [hid] at hcon
  rcases hcon with h0 | hstC
  · exfalso
    have hzero : (fun V' : Finset (Option ι) =>
        if none ∈ V' then 0
        else α * projLayer w F k (Finset.eraseNone V')) = fun _ => (0 : ℝ) :=
      genPoly_injective (ι := Option ι) (by rw [h0, genPoly_zero])
    have hlayer : projLayer w F k = fun _ => (0 : ℝ) := by
      funext V
      have hV := congrFun hzero (V.map Function.Embedding.some)
      rw [if_neg (none_notMem_map_some V), Finset.eraseNone_map_some V]
        at hV
      have hV' : α * projLayer w F k V = 0 := by simpa using hV
      rcases mul_eq_zero.mp hV' with h | h
      · exact absurd h hα.ne'
      · exact h
    rw [totalMass, hlayer] at hmass
    simp at hmass
  · intro z hz
    have hzOpt : ∀ o : Option ι,
        0 < ((fun o : Option ι => o.elim Complex.I z) o).im := by
      intro o
      cases o with
      | none => simp
      | some i => exact hz i
    have hne := hstC _ hzOpt
    have heval : MvPolynomial.eval (fun o : Option ι => o.elim Complex.I z)
        ((genPoly (fun V' : Finset (Option ι) =>
          if none ∈ V' then 0
          else α * projLayer w F k (Finset.eraseNone V'))).map
            (algebraMap ℝ ℂ))
        = (algebraMap ℝ ℂ) α * MvPolynomial.eval z
            ((genPoly (projLayer w F k)).map (algebraMap ℝ ℂ)) := by
      rw [eval_map_genPoly, sum_option_split
        (f := fun T => (algebraMap ℝ ℂ)
          (if none ∈ T then 0
            else α * projLayer w F k (Finset.eraseNone T))
          * ∏ o ∈ T, (fun o : Option ι => o.elim Complex.I z) o)]
      rw [eval_map_genPoly, Finset.mul_sum]
      have h1 : ∀ V : Finset ι, (algebraMap ℝ ℂ)
          (if none ∈ Finset.insertNone V then 0
            else α * projLayer w F k
              (Finset.eraseNone (Finset.insertNone V)))
          * ∏ o ∈ Finset.insertNone V,
              (fun o : Option ι => o.elim Complex.I z) o = 0 := by
        intro V
        rw [if_pos Finset.none_mem_insertNone, map_zero, zero_mul]
      rw [Finset.sum_congr rfl fun V _ => h1 V, Finset.sum_const,
        smul_zero, zero_add]
      refine Finset.sum_congr rfl fun V _ => ?_
      rw [if_neg (none_notMem_map_some V), Finset.eraseNone_map_some V,
        Finset.prod_map, map_mul]
      simp only [Function.Embedding.some_apply, Option.elim_some]
      ring
    rw [heval] at hne
    intro hc
    exact hne (by rw [hc, mul_zero])

/-! ### The descent and the zero-safe export -/

omit [Fintype ι] [DecidableEq ι] in
/-- Rescaling the adjacent pair: an overall nonzero scalar and a positive
marker scaling preserve marker stability of a linear pair. -/
theorem markerStable_pair_rescale {q0 q1 : MvPolynomial ι ℝ} {c lam : ℝ}
    (hc : c ≠ 0) (hlam : 0 < lam)
    (h : MarkerStable (Polynomial.C q0 + Polynomial.C q1 * Polynomial.X)) :
    MarkerStable (Polynomial.C (c • q0)
      + Polynomial.C ((c * lam) • q1) * Polynomial.X) := by
  have hsm : ∀ (c' : ℝ) (q : MvPolynomial ι ℝ) (z : ι → ℂ),
      coeffHom z (c' • q) = (algebraMap ℝ ℂ) c' * coeffHom z q := by
    intro c' q z
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    congr 1
    rw [coeffHom_apply]
    simp
  intro z y hz hy
  have hyim : 0 < ((algebraMap ℝ ℂ) lam * y).im := by
    rw [Complex.mul_im, show ((algebraMap ℝ ℂ) lam).re = lam from rfl,
      show ((algebraMap ℝ ℂ) lam).im = 0 from rfl, zero_mul, add_zero]
    exact mul_pos hlam hy
  have h0 := h z ((algebraMap ℝ ℂ) lam * y) hz hyim
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_C, Polynomial.eval₂_X] at h0 ⊢
  rw [hsm, hsm, map_mul]
  intro hzero
  refine h0 ?_
  have hcne : (algebraMap ℝ ℂ) c ≠ 0 := by
    simpa using hc
  have hfac : (algebraMap ℝ ℂ) c
      * (coeffHom z q0 + coeffHom z q1 * ((algebraMap ℝ ℂ) lam * y))
      = 0 := by
    linear_combination hzero
  rcases mul_eq_zero.mp hfac with hcc | hin
  · exact absurd hcc hcne
  · exact hin

/-- **The certified descent**: every layer of the interval is stable. -/
theorem isRealStable_projLayer_interval {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {a b : ℕ} (hab : a ≤ b)
    (hbr : b ≤ r)
    (hiff : ∀ j, 0 < totalMass (projLayer w F j) ↔ a ≤ j ∧ j ≤ b)
    (hsupp : ∀ S, w S ≠ 0 → a ≤ (S ∩ F).card ∧ (S ∩ F).card ≤ b) :
    ∀ j, a ≤ j → j ≤ b → IsRealStable (genPoly (projLayer w F j)) := by
  obtain ⟨hEa, hEb⟩ :=
    isRealStable_projLayer_endpoints hst hr hnn hab hbr hiff hsupp
  have main : ∀ d j, a ≤ j → j + d = b →
      IsRealStable (genPoly (projLayer w F j)) := by
    intro d
    induction d with
    | zero =>
      intro j _ hjb
      rw [show j = b from by omega]
      exact hEb
    | succ d ih =>
      intro j hja hjb
      have hEk1 : IsRealStable (genPoly (projLayer w F (j + 1))) :=
        ih (j + 1) (by omega) (by omega)
      have hpair := markerStable_adjacent_pair hst hr hnn hiff hEa hja
        (by omega) hbr hEk1
      rw [← Nat.cast_smul_eq_nsmul ℝ ((j + 1).factorial
          * (r - (j + 1)).factorial),
        ← Nat.cast_smul_eq_nsmul ℝ (j.factorial * (r - j).factorial)]
        at hpair
      have hstU := isRealStable_genPoly_taggedWeight
        (α := ((j.factorial * (r - j).factorial : ℕ) : ℝ))
        (β := (((j + 1).factorial * (r - (j + 1)).factorial : ℕ) : ℝ))
        hpair
      exact isRealStable_projLayer_of_tagged
        (Nat.cast_pos.mpr
          (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)))
        (Nat.cast_pos.mpr
          (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)))
        hnn hstU ((hiff j).mpr ⟨hja, by omega⟩)
  exact fun j hja hjb => main (b - j) j hja (by omega)

omit [DecidableEq ι] in
theorem weightMass_false (w : Finset ι → ℝ) :
    weightMass w (fun _ => False) = 0 := by
  rw [weightMass]
  simp

/-- **The zero-safe adjacent monotonicity**: for an increasing event `Q`,
`e_k(Q)·m_{k+1} ≤ e_{k+1}(Q)·m_k`, for *every* `k`.  Outside the support
interval a vanishing layer mass makes both sides zero; inside, the tagged
bridge — marker branch `m_{k+1}·(k\text{-layer})`, plain branch
`m_k·((k+1)\text{-layer})` — is stable, and Feder–Mihail negative
association between the marker and the lifted event does the rest. -/
theorem adjacent_layer_mono {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι)
    (k : ℕ) {Q : Finset ι → Prop} (hQ : Monotone Q) :
    weightMass (projLayer w F k) Q * totalMass (projLayer w F (k + 1))
      ≤ weightMass (projLayer w F (k + 1)) Q
        * totalMass (projLayer w F k) := by
  classical
  obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ :=
    exists_layer_interval hst hr hnn htot F
  set ek := weightMass (projLayer w F k) Q with hek
  set ek1 := weightMass (projLayer w F (k + 1)) Q with hek1
  set mk := totalMass (projLayer w F k) with hmk
  set mk1 := totalMass (projLayer w F (k + 1)) with hmk1
  have hek_nn : 0 ≤ ek :=
    weightMass_nonneg (weightNonneg_projLayer hnn F k) Q
  have hek1_nn : 0 ≤ ek1 :=
    weightMass_nonneg (weightNonneg_projLayer hnn F (k + 1)) Q
  have hmk_nn : 0 ≤ mk := totalMass_nonneg (weightNonneg_projLayer hnn F k)
  have hmk1_nn : 0 ≤ mk1 :=
    totalMass_nonneg (weightNonneg_projLayer hnn F (k + 1))
  by_cases hka : a ≤ k
  case neg =>
    have hm : mk = 0 := by
      by_contra hc
      have := (hiff k).mp (lt_of_le_of_ne hmk_nn (Ne.symm hc))
      omega
    have he : ek = 0 := le_antisymm
      (hm ▸ weightMass_le_totalMass (weightNonneg_projLayer hnn F k) Q)
      hek_nn
    rw [he, zero_mul]
    exact mul_nonneg hek1_nn hmk_nn
  by_cases hkb : k + 1 ≤ b
  case neg =>
    have hm1 : mk1 = 0 := by
      by_contra hc
      have := (hiff (k + 1)).mp (lt_of_le_of_ne hmk1_nn (Ne.symm hc))
      omega
    have he1 : ek1 = 0 := le_antisymm
      (hm1 ▸ weightMass_le_totalMass
        (weightNonneg_projLayer hnn F (k + 1)) Q)
      hek1_nn
    rw [hm1, mul_zero, he1, zero_mul]
  -- the live case: both layers inside the interval
  have hmkpos : 0 < mk := (hiff k).mpr ⟨hka, by omega⟩
  have hmk1pos : 0 < mk1 := (hiff (k + 1)).mpr ⟨by omega, hkb⟩
  have hEa :=
    (isRealStable_projLayer_endpoints hst hr hnn hab hbr hiff hsupp).1
  have hEk1 := isRealStable_projLayer_interval hst hr hnn hab hbr hiff
    hsupp (k + 1) (by omega) hkb
  have hpair := markerStable_adjacent_pair hst hr hnn hiff hEa hka hkb
    hbr hEk1
  rw [← Nat.cast_smul_eq_nsmul ℝ ((k + 1).factorial
      * (r - (k + 1)).factorial),
    ← Nat.cast_smul_eq_nsmul ℝ (k.factorial * (r - k).factorial)]
    at hpair
  set A : ℝ := ((k.factorial * (r - k).factorial : ℕ) : ℝ) with hA
  set B : ℝ := (((k + 1).factorial * (r - (k + 1)).factorial : ℕ) : ℝ)
    with hB
  have hApos : 0 < A := Nat.cast_pos.mpr
    (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have hBpos : 0 < B := Nat.cast_pos.mpr
    (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have hres := markerStable_pair_rescale (c := mk / B)
    (lam := mk1 * B / (mk * A)) (by positivity) (by positivity) hpair
  have hs1 : (mk / B) • (B • genPoly (projLayer w F (k + 1)))
      = mk • genPoly (projLayer w F (k + 1)) := by
    rw [smul_smul]
    congr 1
    field_simp
  have hs2 : (mk / B * (mk1 * B / (mk * A)))
        • (A • genPoly (projLayer w F k))
      = mk1 • genPoly (projLayer w F k) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [hs1, hs2] at hres
  have hstU := isRealStable_genPoly_taggedWeight (α := mk1) (β := mk) hres
  have hRnn := rayleighNonneg_genPoly hstU
  have hdA : EventDependsOn (fun T : Finset (Option ι) => none ∈ T)
      {none} := by
    intro S T hST
    constructor
    · intro h
      have hm : (none : Option ι) ∈ S ∩ {none} :=
        Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self _⟩
      rw [hST] at hm
      exact (Finset.mem_inter.mp hm).1
    · intro h
      have hm : (none : Option ι) ∈ T ∩ {none} :=
        Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self _⟩
      rw [← hST] at hm
      exact (Finset.mem_inter.mp hm).1
  have hdB : EventDependsOn
      (fun T : Finset (Option ι) => Q (Finset.eraseNone T))
      ({none}ᶜ) := by
    intro S T hST
    have herase : Finset.eraseNone S = Finset.eraseNone T := by
      ext x
      simp only [Finset.mem_eraseNone]
      constructor
      · intro h
        have hm : (some x : Option ι) ∈ S ∩ ({none}ᶜ) :=
          Finset.mem_inter.mpr ⟨h, by simp⟩
        rw [hST] at hm
        exact (Finset.mem_inter.mp hm).1
      · intro h
        have hm : (some x : Option ι) ∈ T ∩ ({none}ᶜ) :=
          Finset.mem_inter.mpr ⟨h, by simp⟩
        rw [← hST] at hm
        exact (Finset.mem_inter.mp hm).1
    change Q (Finset.eraseNone S) ↔ Q (Finset.eraseNone T)
    rw [herase]
  have hFM := negCorrelated_of_disjoint_monotone
    (weightNonneg_taggedWeight hnn F k hmk1pos.le hmkpos.le)
    (fixedRankWeight_taggedWeight w F k mk1 mk)
    (fun S _ => Finset.subset_univ S) hRnn
    (fun S T hST h => hST h)
    (fun S T hST h => hQ (Finset.eraseNone.monotone hST) h)
    hdA hdB (Finset.subset_univ _) (Finset.subset_univ _)
    disjoint_compl_right
  unfold NegCorrelated at hFM
  have hFM' : weightMass (taggedWeight w F k mk1 mk)
        (fun T => none ∈ T ∧ Q (Finset.eraseNone T))
        * totalMass (taggedWeight w F k mk1 mk)
      ≤ weightMass (taggedWeight w F k mk1 mk) (fun T => none ∈ T)
        * weightMass (taggedWeight w F k mk1 mk)
          (fun T => Q (Finset.eraseNone T)) := hFM
  have hW1 : weightMass (taggedWeight w F k mk1 mk)
      (fun T => none ∈ T ∧ Q (Finset.eraseNone T)) = mk1 * ek := by
    rw [weightMass_taggedWeight,
      weightMass_congr (w := projLayer w F k) (B := Q) (fun V => by
        rw [eraseNone_insertNone']
        simp),
      weightMass_congr (w := projLayer w F (k + 1)) (B := fun _ => False)
        (fun V => by simp),
      weightMass_false, mul_zero, add_zero, ← hek]
  have hW2 : weightMass (taggedWeight w F k mk1 mk)
      (fun T => none ∈ T) = mk1 * mk := by
    rw [weightMass_taggedWeight,
      weightMass_congr (w := projLayer w F k) (B := fun _ => True)
        (fun V => by simp),
      weightMass_congr (w := projLayer w F (k + 1)) (B := fun _ => False)
        (fun V => by simp),
      weightMass_true, weightMass_false, mul_zero, add_zero, ← hmk]
  have hW3 : weightMass (taggedWeight w F k mk1 mk)
      (fun T => Q (Finset.eraseNone T)) = mk1 * ek + mk * ek1 := by
    rw [weightMass_taggedWeight,
      weightMass_congr (w := projLayer w F k) (B := Q) (fun V => by
        rw [eraseNone_insertNone']),
      weightMass_congr (w := projLayer w F (k + 1)) (B := Q) (fun V => by
        rw [Finset.eraseNone_map_some]),
      ← hek, ← hek1]
  rw [hW1, hW2, hW3, totalMass_taggedWeight, ← hmk, ← hmk1] at hFM'
  have hgoal : mk * mk1 * (ek * mk1) ≤ mk * mk1 * (ek1 * mk) := by
    nlinarith [hFM']
  exact le_of_mul_le_mul_left hgoal (mul_pos hmkpos hmk1pos)

/-- The decreasing mirror, by complementation. -/
theorem adjacent_layer_anti {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (F : Finset ι)
    (k : ℕ) {Q : Finset ι → Prop} (hQ : Antitone Q) :
    weightMass (projLayer w F (k + 1)) Q * totalMass (projLayer w F k)
      ≤ weightMass (projLayer w F k) Q
        * totalMass (projLayer w F (k + 1)) := by
  have hmono := adjacent_layer_mono hst hr hnn htot F k
    (TSPGap.Antitone.not_monotone hQ)
  rw [weightMass_not, weightMass_not] at hmono
  nlinarith [hmono]

end TSPGap

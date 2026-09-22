/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountEstimates

/-!
# KKO21 Lemma 5.7

`A' ⊆ A`, `B' ⊆ B` with `A`, `B` disjoint, `E[A], E[B] ≤ 1 + η`,
`E[A' ∪ B'] ≥ 1 + α`, `100η < α ≤ 1/50`.  Then all four counts equal one
with probability at least `0.11 α³`.

⚠️ The paper caps `α < 0.001`; every numeric step here has room up to
`1/50`, and the ceiling is stated at that value because Proposition 5.6
applies the lemma at the cap.  The binding constraint is
`one_sub_exp_ge` (`1 − e^{−x} ≥ 0.98x` needs `x ≤ 1/50`).

The proof conditions on `D = (A ∖ A') ∪ (B ∖ B')` being avoided.  Two facts
drive everything:

* the conditioning event has mass `≥ α − 2η ≥ 0.98α` (Markov at zero), and
* `E[D] = (E[A] + E[B]) − E[A' ∪ B']` **exactly**, so the conditional mean
  `E_ν[A' ∪ B'] ≤ E[A' ∪ B'] + E[D] = E[A] + E[B] ≤ 2 + 2η` — the *whole*
  point of the `E[F] + E[D]` shape of `expCard_avoid_le`.

Then `E_ν[A' ∪ B']` is either high (`> 3/2`, where `probCount_two_ge` gives
layer mass `≥ 0.25` and Markov gives the `α/2`-size tails) or low (`≤ 3/2`,
where `probCount_two_ge_low` gives layer mass `≥ 0.6α` and Markov gives
`≥ 1/4`-size tails), and `three_cell_bound` converts either into the middle
cell.  The two branches clear the constant with room:
`0.98·0.25·0.45 = 0.11025` and `0.98·0.6·0.2 = 0.1176`.

Under `ν` the counts on `A'` and `A` agree, which is what turns the middle
cell into the four-count event (`weightMass_conj_avoid_le`).

Only the *upper* halves `E[A], E[B] ≤ 1 + η` of the paper's two-sided
hypothesis are used; the lower halves never enter, so the statement here is
slightly more general.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Small helpers -/

/-- The expected count under the normalized conditioned law,
cross-multiplied. -/
theorem expCard_avoidDist_mul (w : Finset ι → ℝ) (D F : Finset ι)
    (hmass : 0 < totalMass (avoidWeight w D)) :
    expCard (avoidDist w D) F * totalMass (avoidWeight w D)
      = expCard (avoidWeight w D) F := by
  classical
  have hsplit : expCard (avoidDist w D) F
      = expCard (avoidWeight w D) F / totalMass (avoidWeight w D) := by
    rw [expCard, expCard, Finset.sum_div]
    exact Finset.sum_congr rfl fun S _ => by rw [avoidDist, div_mul_eq_mul_div]
  rw [hsplit, div_mul_cancel₀ _ hmass.ne']

/-- **Markov at threshold two.** -/
theorem two_mul_weightMass_two_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) :
    2 * weightMass w (fun T => 2 ≤ (T ∩ F).card) ≤ expCard w F := by
  classical
  rw [weightMass, expCard, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases h : 2 ≤ (S ∩ F).card
  · rw [if_pos h]
    have h2 : (2:ℝ) ≤ ((S ∩ F).card : ℝ) := by exact_mod_cast h
    nlinarith [hnn S]
  · rw [if_neg h, mul_zero]
    exact mul_nonneg (hnn S) (Nat.cast_nonneg _)

/-- Markov, in the form the three-cell tails need. -/
theorem two_mul_weightMass_le_one_ge {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) :
    2 * totalMass w - expCard w F
      ≤ 2 * weightMass w (fun T => (T ∩ F).card ≤ 1) := by
  have hnot := weightMass_not w (fun T => 2 ≤ (T ∩ F).card)
  have hcongr : weightMass w (fun T => ¬ 2 ≤ (T ∩ F).card)
      = weightMass w (fun T => (T ∩ F).card ≤ 1) :=
    weightMass_congr fun T => by omega
  rw [hcongr] at hnot
  linarith [two_mul_weightMass_two_le hnn F, hnot]

/-- **`P[X ≥ 1] ≥ 1 − exp(−E X)`** for a stable fixed-rank law, through the
Bernoulli rank law. -/
theorem one_sub_exp_le_weightMass_one_le {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1) (F : Finset ι) :
    1 - Real.exp (-(expCard ν F))
      ≤ weightMass ν (fun T => 1 ≤ (T ∩ F).card) := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard ν F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  have hzero : weightMass ν (fun T => (T ∩ F).card = 0)
      ≤ Real.exp (-(expCard ν F)) := by
    rw [hlaw 0, hmean]
    exact probCount_zero_le_exp q fun i => (hq i).2
  have hnot := weightMass_not ν (fun T => 1 ≤ (T ∩ F).card)
  have hcongr : weightMass ν (fun T => ¬ 1 ≤ (T ∩ F).card)
      = weightMass ν (fun T => (T ∩ F).card = 0) :=
    weightMass_congr fun T => by omega
  rw [hcongr, htot] at hnot
  linarith [hzero, hnot]

/-! ### The low-mean point mass -/

/-- **`P[X = 2] ≥ 0.6α`** when the mean lies in `[1 + α, 3/2]`.  Here the
`l = 1` branch of `poi_le_probCount` degrades to `(p−1)e^{−(p−1)}`, which is
why the bound is proportional to `α` rather than constant. -/
theorem probCount_two_ge_low {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : κ → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) {α : ℝ} (hα0 : 0 < α)
    (hα : α ≤ 1 / 50) (h1 : 1 + α ≤ ∑ i, q i) (h2 : ∑ i, q i ≤ 1.5) :
    0.6 * α ≤ Bernoulli.probCount q 2 := by
  classical
  obtain ⟨l, hl2, hlp, hbound⟩ := Bernoulli.poi_le_probCount q hq 2
    (by push_cast; linarith) (by push_cast; linarith)
  refine le_trans ?_ hbound
  simp only [Nat.cast_ofNat]
  set p : ℝ := ∑ i, q i with hp
  have hmax : max (p - 2) 0 = 0 := max_eq_right (by linarith)
  interval_cases l
  · -- `l = 0`: the point mass is bounded below by a constant here
    rw [Nat.cast_zero, sub_zero, show (2 - 0 : ℕ) = 2 from rfl, Bernoulli.poi,
      show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num,
      show ((2:ℕ) : ℝ) + 1 = 3 from by norm_num, hmax, Real.rpow_zero, mul_one]
    have hem : (0.222 : ℝ) ≤ Real.exp (-1.5) := by
      have h : (1:ℝ) / 4.5 ≤ 1 / Real.exp 1.5 :=
        one_div_le_one_div_of_le (Real.exp_pos 1.5) exp_three_halves_le
      rw [Real.exp_neg, ← one_div]
      linarith [h]
    have hmono : Real.exp (-1.5) ≤ Real.exp (-p) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpsq : (1:ℝ) ≤ p ^ 2 := by nlinarith
    have hprod : (0.222 : ℝ) * 1 ≤ Real.exp (-p) * p ^ 2 :=
      mul_le_mul (by linarith) hpsq (by norm_num) (by positivity)
    linarith [hprod]
  · -- `l = 1`: the branch that produces the factor `α`
    rw [Nat.cast_one, show (2 - 1 : ℕ) = 1 from rfl, Bernoulli.poi,
      show ((Nat.factorial 1 : ℕ) : ℝ) = 1 from by norm_num,
      show (1:ℝ) + 1 = 2 from by norm_num, hmax, Real.rpow_zero, mul_one,
      pow_one]
    have hexp : (0.6 : ℝ) ≤ Real.exp (-(p - 1)) := by
      have hmono : Real.exp (-0.5) ≤ Real.exp (-(p - 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith [exp_neg_half_ge, hmono]
    have hprod : (0.6 : ℝ) * α ≤ Real.exp (-(p - 1)) * (p - 1) :=
      mul_le_mul hexp (by linarith) hα0.le (Real.exp_pos _).le
    linarith [hprod]
  · -- `l = 2` cannot occur: it would force the mean to be at least two
    exfalso
    have : (2:ℝ) ≤ p := by exact_mod_cast hlp
    linarith

/-! ### Layer-two masses -/

theorem weightMass_layer_two_ge_high {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1) (F : Finset ι)
    (h1 : 1.5 ≤ expCard ν F) (h2 : expCard ν F ≤ 2 + 1 / 1000) :
    (0.25 : ℝ) ≤ weightMass ν (fun T => (T ∩ F).card = 2) := by
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard ν F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  rw [hlaw 2]
  refine probCount_two_ge q (fun i => ⟨(hq i).1.le, (hq i).2⟩) ?_ ?_
  · rw [← hmean]; exact h1
  · rw [← hmean]; exact h2

theorem weightMass_layer_two_ge_low {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1) (F : Finset ι) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ 1 / 50) (h1 : 1 + α ≤ expCard ν F)
    (h2 : expCard ν F ≤ 1.5) :
    0.6 * α ≤ weightMass ν (fun T => (T ∩ F).card = 2) := by
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot F
  have hmean : expCard ν F = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  rw [hlaw 2]
  refine probCount_two_ge_low q (fun i => ⟨(hq i).1.le, (hq i).2⟩) hα0 hα ?_ ?_
  · rw [← hmean]; exact h1
  · rw [← hmean]; exact h2

/-! ### The avoidance-event equivalence -/

/-- On the conditioning event the counts on `A'` and `A` agree, so the
middle cell of the three-cell bound *is* the four-count event. -/
theorem weightMass_conj_avoid_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {A B A' B' : Finset ι} (hA' : A' ⊆ A) (hB' : B' ⊆ B) :
    weightMass w (fun T => ((T ∩ A').card = 1 ∧ (T ∩ B').card = 1)
        ∧ (T ∩ ((A \ A') ∪ (B \ B'))).card = 0)
      ≤ weightMass w (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 1
          ∧ (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) := by
  classical
  refine weightMass_mono hnn fun T hT => ?_
  obtain ⟨⟨hA1, hB1⟩, hD0⟩ := hT
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hD0
  have hAeq : T ∩ A = T ∩ A' := by
    refine Finset.Subset.antisymm (fun a ha => ?_)
      (Finset.inter_subset_inter (Finset.Subset.refl T) hA')
    obtain ⟨haT, haA⟩ := Finset.mem_inter.mp ha
    by_cases haA' : a ∈ A'
    · exact Finset.mem_inter.mpr ⟨haT, haA'⟩
    · exact absurd (Finset.mem_inter.mpr ⟨haT,
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haA, haA'⟩)⟩) (hD0 a)
  have hBeq : T ∩ B = T ∩ B' := by
    refine Finset.Subset.antisymm (fun a ha => ?_)
      (Finset.inter_subset_inter (Finset.Subset.refl T) hB')
    obtain ⟨haT, haB⟩ := Finset.mem_inter.mp ha
    by_cases haB' : a ∈ B'
    · exact Finset.mem_inter.mpr ⟨haT, haB'⟩
    · exact absurd (Finset.mem_inter.mpr ⟨haT,
        Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨haB, haB'⟩)⟩) (hD0 a)
  exact ⟨hA1, hB1, by rw [hAeq]; exact hA1, by rw [hBeq]; exact hB1⟩

/-! ### Branch arithmetic

Kept separate from the measure-theoretic context: `linarith` and `nlinarith`
see only these few real variables, which keeps them fast and predictable. -/

omit [Fintype ι] [DecidableEq ι] in
theorem mul_lower {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : a ≤ x)
    (hy : b ≤ y) : a * b ≤ x * y :=
  mul_le_mul hx hy hb (le_trans ha hx)

omit [Fintype ι] [DecidableEq ι] in
theorem sq_small {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 50) : α ^ 2 ≤ 0.0004 := by
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- The low-mean branch: layer mass `0.6α`, tail product `0.24α`. -/
theorem low_branch_bound {L M α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 50)
    (hL : 0.6 * α ≤ L) (hM : 0 ≤ M)
    (hcell : L * (0.24 * α) * (1 - 3 * (0.24 * α))
      ≤ M * (1 - 2 * (0.24 * α))) :
    0.1125 * α ^ 2 ≤ M := by
  have he : (0:ℝ) ≤ 0.24 * α := by linarith
  have h3 : (0:ℝ) ≤ 1 - 3 * (0.24 * α) := by linarith
  have hstep : (0.6 * α) * (0.24 * α) * (1 - 3 * (0.24 * α))
      ≤ L * (0.24 * α) * (1 - 3 * (0.24 * α)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL he) h3
  have hMle : M * (1 - 2 * (0.24 * α)) ≤ M := by nlinarith
  have hnum : 0.1125 * α ^ 2
      ≤ (0.6 * α) * (0.24 * α) * (1 - 3 * (0.24 * α)) := by nlinarith
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- The high-mean branch: layer mass `0.25`, tail product `0.47α²`. -/
theorem high_branch_bound {L M α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 50)
    (hL : 0.25 ≤ L) (hM : 0 ≤ M)
    (hcell : L * (0.47 * α ^ 2) * (1 - 3 * (0.47 * α ^ 2))
      ≤ M * (1 - 2 * (0.47 * α ^ 2))) :
    0.1125 * α ^ 2 ≤ M := by
  have hsq : α ^ 2 ≤ 0.0004 := by nlinarith
  have he : (0:ℝ) ≤ 0.47 * α ^ 2 := by positivity
  have h3 : (0:ℝ) ≤ 1 - 3 * (0.47 * α ^ 2) := by linarith
  have hstep : (0.25 : ℝ) * (0.47 * α ^ 2) * (1 - 3 * (0.47 * α ^ 2))
      ≤ L * (0.47 * α ^ 2) * (1 - 3 * (0.47 * α ^ 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL he) h3
  have hMle : M * (1 - 2 * (0.47 * α ^ 2)) ≤ M := by nlinarith
  have hnum : 0.1125 * α ^ 2
      ≤ (0.25 : ℝ) * (0.47 * α ^ 2) * (1 - 3 * (0.47 * α ^ 2)) := by nlinarith
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Undoing the conditioning: `0.98α · 0.1125α² ≥ 0.11α³`. -/
theorem final_bound {Mid m₀ α : ℝ} (hα0 : 0 < α) (hmid : 0.1125 * α ^ 2 ≤ Mid)
    (hm : 0.98 * α ≤ m₀) (hMid : 0 ≤ Mid) : 0.11 * α ^ 3 ≤ Mid * m₀ := by
  have h := mul_le_mul hmid hm (by linarith) hMid
  nlinarith [h]

/-! ### Lemma 5.7 -/

/-- **KKO21 Lemma 5.7.**  Only the upper halves of the paper's
`E[A], E[B] ∈ [1 − η, 1 + η]` are needed. -/
theorem lemma_5_7 {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B A' B' : Finset ι} (hAB : Disjoint A B) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    {η α : ℝ} (hη0 : 0 ≤ η) (hηα : 100 * η < α) (hα : α ≤ 1 / 50)
    (hEA : expCard w A ≤ 1 + η) (hEB : expCard w B ≤ 1 + η)
    (hEU : 1 + α ≤ expCard w (A' ∪ B')) :
    0.11 * α ^ 3
      ≤ weightMass w (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 1
          ∧ (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) := by
  classical
  have hα0 : 0 < α := by linarith
  -- the conditioning set and its disjointness
  set D : Finset ι := (A \ A') ∪ (B \ B') with hDdef
  have hA'B' : Disjoint A' B' :=
    Finset.disjoint_left.mpr fun a ha hb =>
      Finset.disjoint_left.mp hAB (hA' ha) (hB' hb)
  have hUD : Disjoint (A' ∪ B') D := by
    refine Finset.disjoint_left.mpr fun a ha haD => ?_
    rcases Finset.mem_union.mp ha with ha' | hb'
    · rcases Finset.mem_union.mp haD with hd | hd
      · exact (Finset.mem_sdiff.mp hd).2 ha'
      · exact Finset.disjoint_left.mp hAB (hA' ha') (Finset.mem_sdiff.mp hd).1
    · rcases Finset.mem_union.mp haD with hd | hd
      · exact Finset.disjoint_left.mp hAB (Finset.mem_sdiff.mp hd).1 (hB' hb')
      · exact (Finset.mem_sdiff.mp hd).2 hb'
  have hA'D : Disjoint A' D :=
    Finset.disjoint_of_subset_left Finset.subset_union_left hUD
  have hB'D : Disjoint B' D :=
    Finset.disjoint_of_subset_left Finset.subset_union_right hUD
  -- the mass identity for `D`
  have hsplitD : expCard w D = expCard w (A \ A') + expCard w (B \ B') :=
    expCard_union_of_disjoint w (Finset.disjoint_left.mpr fun a ha hb =>
      Finset.disjoint_left.mp hAB (Finset.mem_sdiff.mp ha).1
        (Finset.mem_sdiff.mp hb).1)
  have hEU' : expCard w (A' ∪ B') = expCard w A' + expCard w B' :=
    expCard_union_of_disjoint w hA'B'
  have hED : expCard w D
      = expCard w A + expCard w B - expCard w (A' ∪ B') := by
    rw [hsplitD, expCard_sdiff_of_subset w hA', expCard_sdiff_of_subset w hB',
      hEU']
    ring
  -- the conditioning event carries mass at least `0.98 α`
  set m₀ : ℝ := totalMass (avoidWeight w D) with hm₀def
  have hm₀ge : 0.98 * α ≤ m₀ := by
    have h := le_weightMass_avoid hnn D
    rw [htot, ← totalMass_avoidWeight w D, ← hm₀def] at h
    linarith [hED, hEA, hEB, hEU, hηα]
  have hm₀pos : 0 < m₀ := by linarith
  -- the conditioned law
  set ν : Finset ι → ℝ := avoidDist w D with hνdef
  have hpack := fixedRankNormalized_avoidDist (D := D) hr hnn hm₀pos
  have hνnn : WeightNonneg ν := hpack.nonneg
  have hνtot : totalMass ν = 1 := hpack.total
  have hνrank : FixedRankWeight r ν := fun S hS => by
    by_contra hc
    exact hS (hpack.supported S hc)
  have hνst : IsRealStable (genPoly ν) :=
    isRealStable_genPoly_avoidDist hst hr hnn hm₀pos
  -- transfer of the conditional expectation bounds to the normalized law
  have htransfer_ge : ∀ F : Finset ι, Disjoint F D → expCard w F ≤ expCard ν F := by
    intro F hFD
    have h := expCard_avoid_ge hst hr hnn hFD
    rw [htot, mul_one, ← expCard_avoidDist_mul w D F hm₀pos, ← hνdef] at h
    exact le_of_mul_le_mul_right h hm₀pos
  have htransfer_le : ∀ F : Finset ι, Disjoint F D →
      expCard ν F ≤ expCard w F + expCard w D := by
    intro F hFD
    have h := expCard_avoid_le hst hr hnn hFD
    rw [htot, mul_one, ← expCard_avoidDist_mul w D F hm₀pos, ← hνdef] at h
    exact le_of_mul_le_mul_right h hm₀pos
  -- the conditional means
  have hUlb : 1 + α ≤ expCard ν (A' ∪ B') :=
    le_trans hEU (htransfer_ge _ hUD)
  have hUub : expCard ν (A' ∪ B') ≤ 2 + 2 * η := by
    have h := htransfer_le _ hUD
    linarith [hED, hEA, hEB]
  have hA'lb : α - η ≤ expCard ν A' := by
    have hb : expCard w B' ≤ expCard w B :=
      expCard_mono hnn (le_trans hB' (Finset.Subset.refl B))
    have h := htransfer_ge _ hA'D
    linarith [hEU', hEU, hEB]
  have hB'lb : α - η ≤ expCard ν B' := by
    have ha : expCard w A' ≤ expCard w A :=
      expCard_mono hnn (le_trans hA' (Finset.Subset.refl A))
    have h := htransfer_ge _ hB'D
    linarith [hEU', hEU, hEA]
  have hA'ub : expCard ν A' ≤ 2 + 3 * η - α := by
    have ha : expCard w A' ≤ expCard w A :=
      expCard_mono hnn (le_trans hA' (Finset.Subset.refl A))
    have h := htransfer_le _ hA'D
    linarith [hED, hEA, hEB, hEU]
  have hB'ub : expCard ν B' ≤ 2 + 3 * η - α := by
    have hb : expCard w B' ≤ expCard w B :=
      expCard_mono hnn (le_trans hB' (Finset.Subset.refl B))
    have h := htransfer_le _ hB'D
    linarith [hED, hEA, hEB, hEU]
  -- the positive tails, common to both branches
  have htail_ge : ∀ F : Finset ι, α - η ≤ expCard ν F →
      0.97 * α ≤ weightMass ν (fun T => 1 ≤ (T ∩ F).card) := by
    intro F hF
    have hmain := one_sub_exp_le_weightMass_one_le hνst hνrank hνnn hνtot F
    have hmono : Real.exp (-(expCard ν F)) ≤ Real.exp (-(0.99 * α)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hnum : 0.98 * (0.99 * α) ≤ 1 - Real.exp (-(0.99 * α)) :=
      one_sub_exp_ge (by linarith) (by linarith)
    linarith [hmain, hmono, hnum]
  have hA'ge := htail_ge A' hA'lb
  have hB'ge := htail_ge B' hB'lb
  -- the middle cell, in either branch
  have hmid : 0.1125 * α ^ 2
      ≤ weightMass ν (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 1) := by
    rcases le_or_gt (expCard ν (A' ∪ B')) 1.5 with hlow | hhigh
    · -- low mean: the layer is thin but both `≤ 1` tails are fat
      have hlayer := weightMass_layer_two_ge_low hνst hνrank hνnn hνtot
        (A' ∪ B') hα0 (by linarith) hUlb hlow
      have hA'le : expCard ν A' ≤ 1.5 :=
        le_trans (expCard_mono hνnn Finset.subset_union_left) hlow
      have hB'le : expCard ν B' ≤ 1.5 :=
        le_trans (expCard_mono hνnn Finset.subset_union_right) hlow
      have hA'small : (0.25 : ℝ)
          ≤ weightMass ν (fun T => (T ∩ A').card ≤ 1) := by
        have h := two_mul_weightMass_le_one_ge hνnn A'
        rw [hνtot] at h
        linarith
      have hB'small : (0.25 : ℝ)
          ≤ weightMass ν (fun T => (T ∩ B').card ≤ 1) := by
        have h := two_mul_weightMass_le_one_ge hνnn B'
        rw [hνtot] at h
        linarith
      have hprod1 : 0.24 * α
          ≤ weightMass ν (fun T => (T ∩ A').card ≤ 1)
            * weightMass ν (fun T => 1 ≤ (T ∩ B').card) := by
        have h := mul_lower (by norm_num : (0:ℝ) ≤ 0.25)
          (by linarith : (0:ℝ) ≤ 0.97 * α) hA'small hB'ge
        linarith
      have hprod2 : 0.24 * α
          ≤ weightMass ν (fun T => 1 ≤ (T ∩ A').card)
            * weightMass ν (fun T => (T ∩ B').card ≤ 1) := by
        have h := mul_lower (by linarith : (0:ℝ) ≤ 0.97 * α)
          (by norm_num : (0:ℝ) ≤ 0.25) hA'ge hB'small
        linarith
      have hcell := three_cell_bound hνst hνrank hνnn hνtot hA'B'
        (ε := 0.24 * α) (by linarith) (by linarith) hprod1 hprod2
      exact low_branch_bound hα0 (by linarith) hlayer
        (weightMass_nonneg hνnn _) hcell
    · -- high mean: the layer is fat but both `≤ 1` tails are of size `α`
      have hlayer := weightMass_layer_two_ge_high hνst hνrank hνnn hνtot
        (A' ∪ B') (le_of_lt hhigh) (by linarith)
      have hA'small : 0.485 * α
          ≤ weightMass ν (fun T => (T ∩ A').card ≤ 1) := by
        have h := two_mul_weightMass_le_one_ge hνnn A'
        rw [hνtot] at h
        linarith [hA'ub, hηα]
      have hB'small : 0.485 * α
          ≤ weightMass ν (fun T => (T ∩ B').card ≤ 1) := by
        have h := two_mul_weightMass_le_one_ge hνnn B'
        rw [hνtot] at h
        linarith [hB'ub, hηα]
      have hsq : α ^ 2 ≤ 0.0004 := sq_small hα0 hα
      have hprod1 : 0.47 * α ^ 2
          ≤ weightMass ν (fun T => (T ∩ A').card ≤ 1)
            * weightMass ν (fun T => 1 ≤ (T ∩ B').card) := by
        have h := mul_lower (by linarith : (0:ℝ) ≤ 0.485 * α)
          (by linarith : (0:ℝ) ≤ 0.97 * α) hA'small hB'ge
        linarith [h, sq_nonneg α]
      have hprod2 : 0.47 * α ^ 2
          ≤ weightMass ν (fun T => 1 ≤ (T ∩ A').card)
            * weightMass ν (fun T => (T ∩ B').card ≤ 1) := by
        have h := mul_lower (by linarith : (0:ℝ) ≤ 0.97 * α)
          (by linarith : (0:ℝ) ≤ 0.485 * α) hA'ge hB'small
        linarith [h, sq_nonneg α]
      have hcell := three_cell_bound hνst hνrank hνnn hνtot hA'B'
        (ε := 0.47 * α ^ 2) (by positivity) (by linarith) hprod1 hprod2
      exact high_branch_bound hα0 (by linarith) hlayer
        (weightMass_nonneg hνnn _) hcell
  -- undo the conditioning
  have hback : weightMass ν (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 1)
      * m₀
      = weightMass w (fun T => ((T ∩ A').card = 1 ∧ (T ∩ B').card = 1)
        ∧ (T ∩ D).card = 0) :=
    weightMass_avoidDist_mul hm₀pos _
  have hfour := weightMass_conj_avoid_le hnn hA' hB'
  rw [← hDdef] at hfour
  have hchain : 0.11 * α ^ 3
      ≤ weightMass ν (fun T => (T ∩ A').card = 1 ∧ (T ∩ B').card = 1) * m₀ :=
    final_bound hα0 hmid hm₀ge (weightMass_nonneg hνnn _)
  rw [hback] at hchain
  linarith [hchain, hfour]

end TSPGap

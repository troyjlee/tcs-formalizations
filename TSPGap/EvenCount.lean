/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountEstimates
import TSPGap.LayerTails

/-!
# KKO21 Corollary 2.17 for a count under a stable law

`Bernoulli.evenMass_le_of_sum_le` bounds the even-parity mass of a Bernoulli
sum *at the level of atoms* — a sum over subsets of the index type, filtered
by the parity of their cardinality.  What the applications (Corollaries 5.10
and 5.11) need is the parity of a **count** `|T ∩ D|` under a stable
fixed-rank law.  The bridge is:

* `sum_even_probCount` — regrouping the powerset by cardinality turns the
  atom sum into `∑_{k even} P[X = k]`, the powerset being the disjoint union
  of its cardinality layers;
* `weightMass_layer_partition` (already in `LayerTails`) — every event splits
  along the layers of `D`, so the even-parity mass is `∑_{k even} W(|T∩D| = k)`;
* `exists_bernoulli_rank_law` — those layer masses *are* a Bernoulli sum's
  point masses, and `expCard_eq_sum_of_rankLaw` identifies the mean.

The export is `evenCount_le`: `W[|T ∩ D| even] ≤ (1 + e^{−2·E[|T∩D|]})/2`
whenever `E[|T∩D|] ≤ 1.2`.  ⚠️ Until now `Bernoulli.evenMass_le_of_sum_le`
had **no consumer** — Lemmas 5.21/5.22 were arranged to avoid parity — so
this is the first place the parity half of §2 is used.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Regrouping the powerset by cardinality -/

/-- The even-parity atom mass is the sum of the even point masses. -/
theorem sum_even_probCount (q : ι → ℝ) {N : ℕ} (hN : Fintype.card ι ≤ N) :
    ∑ k ∈ (Finset.range (N + 1)).filter (fun k => Even k), Bernoulli.probCount q k
      = ∑ t ∈ Finset.univ.powerset.filter (fun t => Even t.card), Bernoulli.atomProb q t := by
  classical
  have hbi : Finset.univ.powerset.filter (fun t : Finset ι => Even t.card)
      = ((Finset.range (N + 1)).filter (fun k => Even k)).biUnion
        (fun k => Finset.univ.powersetCard k) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨-, he⟩
      have hcard : t.card ≤ Fintype.card ι := Finset.card_le_univ t
      exact ⟨t.card, ⟨by omega, he⟩, Finset.subset_univ t, rfl⟩
    · rintro ⟨k, ⟨-, hk⟩, -, rfl⟩
      exact ⟨Finset.subset_univ t, hk⟩
  have hdisj : Set.PairwiseDisjoint
      (((Finset.range (N + 1)).filter (fun k => Even k) : Finset ℕ) : Set ℕ)
      (fun k => (Finset.univ : Finset ι).powersetCard k) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun t ht ht' => hab ?_
    rw [← (Finset.mem_powersetCard.mp ht).2, ← (Finset.mem_powersetCard.mp ht').2]
  rw [hbi, Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl fun k _ => Bernoulli.probCount_def q k

/-! ### The layer masses above the size of `D` vanish -/

theorem weightMass_card_eq_zero (w : Finset ι → ℝ) {D : Finset ι} {k : ℕ} (hk : D.card < k) :
    weightMass w (fun S => (S ∩ D).card = k) = 0 := by
  rw [show (fun S : Finset ι => (S ∩ D).card = k) = fun _ => False from ?_, weightMass_false]
  funext S
  have hle : (S ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
  exact propext ⟨fun h => absurd (h ▸ hle) (by omega), fun h => h.elim⟩

/-! ### The export -/

/-- **Corollary 2.17 for a count**: under a stable, fixed-rank, normalized law,
the even-parity mass of `|T ∩ D|` is at most `(1 + e^{−2 E[|T∩D|]})/2`, as
soon as the mean is at most `1.2`. -/
theorem evenCount_le {w : Finset ι → ℝ} {r : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (D : Finset ι) (hmean : expCard w D ≤ 1.2) :
    weightMass w (fun T => Even (T ∩ D).card)
      ≤ (1 + Real.exp (-2 * expCard w D)) / 2 := by
  classical
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot D
  have hmean' : expCard w D = ∑ i, q i := expCard_eq_sum_of_rankLaw hlaw
  -- the even mass is the filtered layer sum
  have hterm : ∀ jj : ℕ, weightMass w (fun S => (S ∩ D).card = jj ∧ Even (S ∩ D).card)
      = if Even jj then Bernoulli.probCount q jj else 0 := by
    intro jj
    by_cases he : Even jj
    · rw [if_pos he, ← hlaw jj]
      exact weightMass_congr fun S => ⟨fun h => h.1, fun h => ⟨h, h ▸ he⟩⟩
    · rw [if_neg he,
        show (fun S : Finset ι => (S ∩ D).card = jj ∧ Even (S ∩ D).card) = fun _ => False from ?_,
        weightMass_false]
      funext S
      exact propext ⟨fun h => he (h.1 ▸ h.2), fun h => h.elim⟩
  have hsmall : weightMass w (fun T => Even (T ∩ D).card)
      = ∑ k ∈ (Finset.range (D.card + 1)).filter (fun k => Even k),
          Bernoulli.probCount q k := by
    rw [weightMass_layer_partition w D (fun T => Even (T ∩ D).card),
      Finset.sum_congr rfl (fun jj _ => hterm jj), ← Finset.sum_filter]
  -- extend the range so that the atom regrouping applies
  have hext : ∑ k ∈ (Finset.range (D.card + 1)).filter (fun k => Even k),
        Bernoulli.probCount q k
      = ∑ k ∈ (Finset.range (max D.card m + 1)).filter (fun k => Even k),
          Bernoulli.probCount q k := by
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hk1
                                  have := le_max_left D.card m
                                  omega), hk2⟩
    · obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      have hgt : D.card < k := by
        by_contra hc
        exact hk' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk2⟩)
      rw [← hlaw k]
      exact weightMass_card_eq_zero w hgt
  rw [hsmall, hext,
    sum_even_probCount q (by rw [Fintype.card_fin]; exact le_max_right D.card m), hmean']
  exact Bernoulli.evenMass_le_of_sum_le q (fun i => (hq i).1.le) (by rw [← hmean']; exact hmean)

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Coupling
import TSPGap.Conditioning

/-!
# Towards KKO21 Lemma 2.26: projection algebra and aggregation

Two of the three pieces of Lemma 2.26.  The graph exchange is deliberately
*not* here: it is the only step with real risk, and keeping it out of the
projection algebra and the finite-sum aggregation makes any failure easy to
localize.

* **The singleton-complement identities.**  Projecting along `univ.erase e`
  at a fixed rank `k+1` gives exactly the conditioned weights:
  `projLayer w (univ.erase e) k = contractWeight w e` and
  `projLayer w (univ.erase e) (k+1) = deleteWeight w e`.  ⚠️ The fibre of
  `S ↦ S ∩ (univ.erase e) = S.erase e` over `U` is `{U, insert e U}`, and
  fixed rank kills exactly one of the two — which is the whole content.
* `exists_edge_covering` — the coupling of `Coupling.lean`, repackaged: rows
  `m_out · contract`, columns `m_in · delete`, every arc adding one edge.
* `expCard_split_delete_contract` — the expected count splits along `e`.
* `expCard_delete_le_of_exchange` — **the aggregation**, taking the pointwise
  exchange inequality as a hypothesis on the supports.  Zero-safe and
  division-free: `E_out ≤ m_out · E + m_in · P_path`.  Only a paper-facing
  corollary should divide, and it must assume `0 < m_out`; KKO leaves that
  zero-probability corner implicit.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The fibres of the singleton-complement projection -/

theorem inter_univ_erase (S : Finset ι) (e : ι) :
    S ∩ (Finset.univ.erase e) = S.erase e := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

theorem filter_inter_erase_of_mem {e : ι} {U : Finset ι} (heU : e ∈ U) :
    Finset.univ.filter (fun S : Finset ι => S ∩ (Finset.univ.erase e) = U)
      = ∅ := by
  classical
  refine Finset.filter_eq_empty_iff.mpr fun S _ hS => ?_
  rw [inter_univ_erase] at hS
  exact (Finset.notMem_erase e S) (hS ▸ heU)

theorem filter_inter_erase {e : ι} {U : Finset ι} (heU : e ∉ U) :
    Finset.univ.filter (fun S : Finset ι => S ∩ (Finset.univ.erase e) = U)
      = {U, insert e U} := by
  classical
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rw [inter_univ_erase]
  constructor
  · intro hS
    by_cases heS : e ∈ S
    · exact Or.inr (by rw [← hS, Finset.insert_erase heS])
    · exact Or.inl (by rw [← hS, Finset.erase_eq_of_notMem heS])
  · rintro (rfl | rfl)
    · exact Finset.erase_eq_of_notMem heU
    · exact Finset.erase_insert heU

/-! ### The singleton-complement identities -/

theorem projLayer_erase_contract {w : Finset ι → ℝ} {k : ℕ}
    (hr : FixedRankWeight (k + 1) w) (e : ι) :
    projLayer w (Finset.univ.erase e) k = contractWeight w e := by
  classical
  funext U
  rw [projLayer, contractWeight]
  by_cases heU : e ∈ U
  · rw [if_pos heU]
    split_ifs with hcard
    · rw [filter_inter_erase_of_mem heU, Finset.sum_empty]
    · rfl
  · rw [if_neg heU]
    have hne : U ≠ insert e U := fun hc => heU (hc ▸ Finset.mem_insert_self e U)
    have hcardins : (insert e U).card = U.card + 1 :=
      Finset.card_insert_of_notMem heU
    split_ifs with hcard
    · rw [filter_inter_erase heU, Finset.sum_pair hne]
      have hU0 : w U = 0 := by
        by_contra hc
        have := hr U hc
        omega
      rw [hU0, zero_add]
    · have hins0 : w (insert e U) = 0 := by
        by_contra hc
        have := hr _ hc
        omega
      rw [hins0]

theorem projLayer_erase_delete {w : Finset ι → ℝ} {k : ℕ}
    (hr : FixedRankWeight (k + 1) w) (e : ι) :
    projLayer w (Finset.univ.erase e) (k + 1) = deleteWeight w e := by
  classical
  funext U
  rw [projLayer, deleteWeight]
  by_cases heU : e ∈ U
  · rw [if_pos heU]
    split_ifs with hcard
    · rw [filter_inter_erase_of_mem heU, Finset.sum_empty]
    · rfl
  · rw [if_neg heU]
    have hne : U ≠ insert e U := fun hc => heU (hc ▸ Finset.mem_insert_self e U)
    have hcardins : (insert e U).card = U.card + 1 :=
      Finset.card_insert_of_notMem heU
    split_ifs with hcard
    · rw [filter_inter_erase heU, Finset.sum_pair hne]
      have hins0 : w (insert e U) = 0 := by
        by_contra hc
        have := hr _ hc
        omega
      rw [hins0, add_zero]
    · have hU0 : w U = 0 := by
        by_contra hc
        have := hr U hc
        omega
      rw [hU0]

/-! ### The coupling across one edge -/

/-- **The single-edge covering.**  Rows carry `m_out · contract`, columns
`m_in · delete`, and every arc of the coupling adds exactly one edge. -/
theorem exists_edge_covering {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (e : ι) :
    ∃ z : Finset ι → Finset ι → ℝ, (∀ S T, 0 ≤ z S T)
      ∧ (∀ S T, z S T ≠ 0 → S ⊆ T)
      ∧ (∀ S, ∑ T, z S T
          = totalMass (deleteWeight w e) * contractWeight w e S)
      ∧ (∀ T, ∑ S, z S T
          = totalMass (contractWeight w e) * deleteWeight w e T) := by
  obtain ⟨z, hz0, harc, hrow, hcol⟩ :=
    exists_adjacent_covering hst hr hnn htot (Finset.univ.erase e) k
  refine ⟨z, hz0, fun S T hST => (harc S T hST).1, fun S => ?_, fun T => ?_⟩
  · rw [hrow S, projLayer_erase_contract hr e, projLayer_erase_delete hr e]
  · rw [hcol T, projLayer_erase_contract hr e, projLayer_erase_delete hr e]

/-! ### The count splits along the edge -/

/-- **The contraction reindexing.**  Summing a function of `insert e S`
against `contractWeight` is summing it over the trees containing `e`. -/
theorem sum_contract_eq (w : Finset ι → ℝ) (e : ι) (g : Finset ι → ℝ) :
    ∑ S, contractWeight w e S * g (insert e S)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S), w S * g S := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun S : Finset ι => e ∈ S)
    (fun S => contractWeight w e S * g (insert e S))]
  have hzero : ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S),
      contractWeight w e S * g (insert e S) = 0 := by
    refine Finset.sum_eq_zero fun S hS => ?_
    rw [contractWeight, if_pos (Finset.mem_filter.mp hS).2, zero_mul]
  rw [hzero, zero_add]
  refine Finset.sum_nbij' (fun S => insert e S) (fun S => S.erase e) ?_ ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self e S⟩
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.notMem_erase e S⟩
  · intro S hS
    exact Finset.erase_insert (by simpa using (Finset.mem_filter.mp hS).2)
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro S hS
    rw [contractWeight, if_neg (by simpa using (Finset.mem_filter.mp hS).2)]

/-- The total mass splits along `e`. -/
theorem totalMass_split_delete_contract (w : Finset ι → ℝ) (e : ι) :
    totalMass w
      = totalMass (contractWeight w e) + totalMass (deleteWeight w e) := by
  classical
  have h1 : totalMass (contractWeight w e)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S), w S := by
    have h := sum_contract_eq w e (fun _ => 1)
    simpa [totalMass] using h
  have h2 : totalMass (deleteWeight w e)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => ¬ e ∈ S), w S := by
    rw [totalMass, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset ι => e ∈ S) (deleteWeight w e)]
    have hzero : ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S),
        deleteWeight w e S = 0 :=
      Finset.sum_eq_zero fun S hS => by
        rw [deleteWeight, if_pos (Finset.mem_filter.mp hS).2]
    rw [hzero, zero_add]
    exact Finset.sum_congr rfl fun S hS => by
      rw [deleteWeight, if_neg (by simpa using (Finset.mem_filter.mp hS).2)]
  rw [h1, h2, totalMass,
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset ι => e ∈ S) w]

/-- The expected count splits into the trees containing `e` and those
avoiding it. -/
theorem expCard_split_delete_contract (w : Finset ι → ℝ) (e : ι)
    (D : Finset ι) :
    expCard w D
      = (∑ S, contractWeight w e S * (((insert e S) ∩ D).card : ℝ))
        + expCard (deleteWeight w e) D := by
  classical
  have hcontract : ∑ S, contractWeight w e S * (((insert e S) ∩ D).card : ℝ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S),
          w S * ((S ∩ D).card : ℝ) :=
    sum_contract_eq w e (fun S => ((S ∩ D).card : ℝ))
  have hdelete : expCard (deleteWeight w e) D
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => ¬ e ∈ S),
          w S * ((S ∩ D).card : ℝ) := by
    rw [expCard, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset ι => e ∈ S)
      (fun S => deleteWeight w e S * ((S ∩ D).card : ℝ))]
    have hzero : ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S),
        deleteWeight w e S * ((S ∩ D).card : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun S hS => ?_
      rw [deleteWeight, if_pos (Finset.mem_filter.mp hS).2, zero_mul]
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [deleteWeight, if_neg (by simpa using (Finset.mem_filter.mp hS).2)]
  rw [hcontract, hdelete, expCard,
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset ι => e ∈ S) (fun S => w S * ((S ∩ D).card : ℝ))]

/-! ### The aggregation -/

open Classical in
/-- **KKO21 Lemma 2.26, aggregated.**  The pointwise exchange inequality,
summed against the unnormalized coupling.  Zero-safe: no division, and the
degenerate cases where `e` is almost surely present or absent are instances
rather than exclusions. -/
theorem expCard_delete_le_of_exchange {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (e : ι) (D : Finset ι)
    (P : Finset ι → Prop)
    (hexch : ∀ S T : Finset ι, contractWeight w e S ≠ 0 →
      deleteWeight w e T ≠ 0 → S ⊆ T →
      ((T ∩ D).card : ℝ)
        ≤ (((insert e S) ∩ D).card : ℝ) + (if P T then 1 else 0)) :
    expCard (deleteWeight w e) D
      ≤ totalMass (deleteWeight w e) * expCard w D
        + totalMass (contractWeight w e) * weightMass (deleteWeight w e) P := by
  classical
  obtain ⟨z, hz0, harc, hrow, hcol⟩ := exists_edge_covering hst hr hnn htot e
  set mIn : ℝ := totalMass (contractWeight w e) with hmIn
  set mOut : ℝ := totalMass (deleteWeight w e) with hmOut
  -- the three aggregated sums
  have hLHS : ∑ T, (∑ S, z S T) * ((T ∩ D).card : ℝ)
      = mIn * expCard (deleteWeight w e) D := by
    rw [expCard, Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by rw [hcol T]; ring
  have hR1 : ∑ S, (∑ T, z S T) * (((insert e S) ∩ D).card : ℝ)
      = mOut * ∑ S, contractWeight w e S * (((insert e S) ∩ D).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by rw [hrow S]; ring
  have hR2 : ∑ T, (∑ S, z S T) * (if P T then 1 else 0)
      = mIn * weightMass (deleteWeight w e) P := by
    rw [weightMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hcol T]
    by_cases hP : P T
    · rw [if_pos hP, if_pos hP, mul_one]
    · rw [if_neg hP, if_neg hP, mul_zero, mul_zero]
  -- the pointwise inequality, summed
  have hpoint : ∀ S T : Finset ι, z S T * ((T ∩ D).card : ℝ)
      ≤ z S T * ((((insert e S) ∩ D).card : ℝ) + (if P T then 1 else 0)) := by
    intro S T
    rcases eq_or_lt_of_le (hz0 S T) with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ hpos.le
      have hzne : z S T ≠ 0 := ne_of_gt hpos
      have hrowpos : (0:ℝ) < ∑ T', z S T' :=
        lt_of_lt_of_le hpos
          (Finset.single_le_sum (fun T' _ => hz0 S T') (Finset.mem_univ T))
      have hcolpos : (0:ℝ) < ∑ S', z S' T :=
        lt_of_lt_of_le hpos
          (Finset.single_le_sum (fun S' _ => hz0 S' T) (Finset.mem_univ S))
      rw [hrow S] at hrowpos
      rw [hcol T] at hcolpos
      refine hexch S T (fun h0 => ?_) (fun h0 => ?_) (harc S T hzne)
      · rw [h0, mul_zero] at hrowpos
        exact lt_irrefl 0 hrowpos
      · rw [h0, mul_zero] at hcolpos
        exact lt_irrefl 0 hcolpos
  have hsum : ∑ T, (∑ S, z S T) * ((T ∩ D).card : ℝ)
      ≤ (∑ S, (∑ T, z S T) * (((insert e S) ∩ D).card : ℝ))
        + ∑ T, (∑ S, z S T) * (if P T then 1 else 0) := by
    have hexpand : ∀ T : Finset ι, (∑ S, z S T) * ((T ∩ D).card : ℝ)
        = ∑ S, z S T * ((T ∩ D).card : ℝ) := fun T => by rw [Finset.sum_mul]
    have hexpand1 : ∀ S : Finset ι,
        (∑ T, z S T) * (((insert e S) ∩ D).card : ℝ)
        = ∑ T, z S T * (((insert e S) ∩ D).card : ℝ) := fun S => by
      rw [Finset.sum_mul]
    have hexpand2 : ∀ T : Finset ι, (∑ S, z S T) * (if P T then 1 else 0)
        = ∑ S, z S T * (if P T then 1 else 0) := fun T => by rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun T _ => hexpand T),
      Finset.sum_congr rfl (fun S _ => hexpand1 S),
      Finset.sum_congr rfl (fun T _ => hexpand2 T), Finset.sum_comm
        (f := fun T S => z S T * (if P T then 1 else 0)),
      Finset.sum_comm (f := fun T S => z S T * ((T ∩ D).card : ℝ)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun T _ => ?_
    have := hpoint S T
    nlinarith [this]
  -- combine: `m_in E_out ≤ m_out E_in + m_in P`, then use `m_in + m_out = 1`
  rw [hLHS, hR1, hR2] at hsum
  have hsplit := expCard_split_delete_contract w e D
  have hmass : mIn + mOut = 1 := by
    rw [hmIn, hmOut, ← htot]
    exact (totalMass_split_delete_contract w e).symm
  -- `E_out = (m_in + m_out) E_out`, then substitute the split
  have hprod : (mIn + mOut) * expCard (deleteWeight w e) D
      = expCard (deleteWeight w e) D := by rw [hmass, one_mul]
  have hprod2 : mOut * expCard w D
      = mOut * (∑ S, contractWeight w e S * (((insert e S) ∩ D).card : ℝ))
        + mOut * expCard (deleteWeight w e) D := by rw [hsplit]; ring
  linarith [hsum, hprod, hprod2]

end TSPGap

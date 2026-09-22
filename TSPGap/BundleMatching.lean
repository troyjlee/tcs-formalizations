/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleGoodness
import TSPGap.MatchingHall
import TSPGap.MatchingNetwork

/-!
# Matching capacities and allocations for a goodness policy

The ordered-bundle network uses an explicit goodness policy. The atom demands,
flow theorem and unoriented allocation function are the existing ones. The
capacity bounds use unique bad partners; Hall's inequality itself is supplied
by `SongMatching` at Song's parameters.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset

variable (P : BundleGoodnessPolicy) {n : ℕ} {x : Sym2 (Fin n) → ℝ}

open Classical in
/-- The capacity of the ordered row `(u, u')`. -/
noncomputable def rowCap (μ : TreeDist n x) (α : ℝ) (u u' : Finset (Fin n)) : ℝ :=
  if P.IsGood μ u u' then (1 + α) * pairSum x u u' / 2 else 0

open Classical in
/-- The capacity of the ordered rows touching a family `Q` of atoms. -/
noncomputable def touchCap (μ : TreeDist n x) (α : ℝ) (ch Q : Finset (Finset (Fin n))) :
    ℝ :=
  ∑ u ∈ ch, ∑ u' ∈ ch.erase u, if u ∈ Q ∨ u' ∈ Q then rowCap P μ α u u' else 0

theorem rowCap_nonneg (hx : ∀ e, 0 ≤ x e) (μ : TreeDist n x) {α : ℝ} (hα : 0 ≤ α)
    {u u' : Finset (Fin n)} (huu' : Disjoint u u') : 0 ≤ rowCap P μ α u u' := by
  classical
  unfold rowCap
  split_ifs
  · have := pairSum_nonneg_lp hx huu'
    positivity
  · exact le_rfl

theorem rowCap_comm (μ : TreeDist n x) (α : ℝ) (u u' : Finset (Fin n)) :
    rowCap P μ α u u' = rowCap P μ α u' u := by
  classical
  unfold rowCap
  rw [pairSum_comm]
  by_cases h : P.IsGood μ u u'
  · rw [if_pos h, if_pos (isGood_comm.mp h)]
  · rw [if_neg h, if_neg fun h' => h (isGood_comm.mp h')]

theorem rowCap_legacy (μ : TreeDist n x) (eps α : ℝ) (u v : Finset (Fin n)) :
    (legacy eps).rowCap μ α u v = TSPGap.rowCap μ eps α u v := rfl

theorem touchCap_legacy (μ : TreeDist n x) (eps α : ℝ)
    (ch Q : Finset (Finset (Fin n))) :
    (legacy eps).touchCap μ α ch Q = TSPGap.touchCap μ eps α ch Q := rfl

section Bounds
variable {e₀ : RootEdge n} {eta : ℝ} (H : Hierarchy x e₀ eta)

open Classical in
/-- The bad ordered rows touching `Q` carry at most `j (1/2 + P.halfWidth)`, `j` the
number of bad-incident atoms of `Q` (union bound over the orientations). -/
theorem badCap_touch_le {μ : TreeDist n x} {S : Finset (Fin n)} {k : ℝ}
    (D : P.MatchingInputs H μ S k) (hx : IsRestrictedLP e₀ x)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) :
    ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if (u ∈ Q ∨ u' ∈ Q) ∧ ¬ P.IsGood μ u u' then pairSum x u u' / 2 else 0)
      ≤ ((Q.filter (P.IsBadIncident H μ S)).card : ℝ) * (1 / 2 + P.halfWidth) := by
  classical
  set ch := H.children S with hch
  have hps : ∀ u ∈ ch, ∀ u' ∈ ch.erase u, 0 ≤ pairSum x u u' := fun u hu u' hu' =>
    pairSum_nonneg_lp hx.nonneg (H.children_disjoint (H.mem_children.mp hu)
      (H.mem_children.mp (Finset.mem_erase.mp hu').2) (Ne.symm (Finset.mem_erase.mp hu').1))
  -- union bound on the indicator
  have hsplit : ∀ u ∈ ch, ∀ u' ∈ ch.erase u,
      (if (u ∈ Q ∨ u' ∈ Q) ∧ ¬ P.IsGood μ u u' then pairSum x u u' / 2 else 0)
        ≤ (if u ∈ Q then (if ¬ P.IsGood μ u u' then pairSum x u u' else 0) / 2 else 0)
          + (if u' ∈ Q then (if ¬ P.IsGood μ u u' then pairSum x u u' else 0) / 2
            else 0) := by
    intro u hu u' hu'
    have := hps u hu u' hu'
    by_cases h1 : u ∈ Q
    all_goals by_cases h2 : u' ∈ Q
    all_goals by_cases h3 : P.IsGood μ u u'
    all_goals simp [h1, h2, h3]
    all_goals linarith
  refine le_trans (Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun u' hu' =>
    hsplit u hu u' hu') ?_
  simp_rw [Finset.sum_add_distrib]
  -- the first orientation
  have e1 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u,
      (if u ∈ Q then (if ¬ P.IsGood μ u u' then pairSum x u u' else 0) / 2 else 0)
      ≤ ((Q.filter (P.IsBadIncident H μ S)).card : ℝ) * (1 / 2 + P.halfWidth) / 2 := by
    have : ∀ u ∈ ch, ∑ u' ∈ ch.erase u,
        (if u ∈ Q then (if ¬ P.IsGood μ u u' then pairSum x u u' else 0) / 2 else 0)
        = if u ∈ Q then (∑ u' ∈ ch.erase u,
            (if ¬ P.IsGood μ u u' then pairSum x u u' else 0)) / 2 else 0 := by
      intro u _
      split_ifs
      · rw [Finset.sum_div]
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ]
    calc ∑ u ∈ Q, (∑ u' ∈ ch.erase u,
          (if ¬ P.IsGood μ u u' then pairSum x u u' else 0)) / 2
        ≤ ∑ u ∈ Q, (if P.IsBadIncident H μ S u then 1 / 2 + P.halfWidth else 0) / 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact div_le_div_of_nonneg_right (D.sum_bad_pairSum_le (hQ hu)) (by norm_num)
      _ = ((Q.filter (P.IsBadIncident H μ S)).card : ℝ) * (1 / 2 + P.halfWidth) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- the second orientation, by symmetry
  have e2 : ∑ u ∈ ch, ∑ u' ∈ ch.erase u,
      (if u' ∈ Q then (if ¬ P.IsGood μ u u' then pairSum x u u' else 0) / 2 else 0)
      ≤ ((Q.filter (P.IsBadIncident H μ S)).card : ℝ) * (1 / 2 + P.halfWidth) / 2 := by
    rw [sum_erase_comm]
    have : ∀ u' ∈ ch, ∑ u ∈ ch.erase u',
        (if u' ∈ Q then (if ¬ P.IsGood μ u u' then pairSum x u u' else 0) / 2 else 0)
        = if u' ∈ Q then (∑ u ∈ ch.erase u',
            (if ¬ P.IsGood μ u' u then pairSum x u' u else 0)) / 2 else 0 := by
      intro u' _
      split_ifs
      · rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [pairSum_comm]
        by_cases hg : P.IsGood μ u' u
        · rw [if_neg (not_not.mpr (isGood_comm.mp hg)), if_neg (not_not.mpr hg)]
        · rw [if_pos (fun h => hg (isGood_comm.mp h)), if_pos hg]
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hQ]
    calc ∑ u ∈ Q, (∑ u' ∈ ch.erase u,
          (if ¬ P.IsGood μ u u' then pairSum x u u' else 0)) / 2
        ≤ ∑ u ∈ Q, (if P.IsBadIncident H μ S u then 1 / 2 + P.halfWidth else 0) / 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact div_le_div_of_nonneg_right (D.sum_bad_pairSum_le (hQ hu)) (by norm_num)
      _ = ((Q.filter (P.IsBadIncident H μ S)).card : ℝ) * (1 / 2 + P.halfWidth) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  linarith

open Classical in
/-- **All bad rows** carry at most `j (1/2 + P.halfWidth)/2`: each is counted from its
own first endpoint. -/
theorem badCap_all_le {μ : TreeDist n x} {S : Finset (Fin n)} {k : ℝ}
    (D : P.MatchingInputs H μ S k) :
    ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if ¬ P.IsGood μ u u' then pairSum x u u' / 2 else 0)
      ≤ (((H.children S).filter (P.IsBadIncident H μ S)).card : ℝ) * (1 / 2 + P.halfWidth) / 2 := by
  classical
  calc ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if ¬ P.IsGood μ u u' then pairSum x u u' / 2 else 0)
      = ∑ u ∈ H.children S, (∑ u' ∈ (H.children S).erase u,
        (if ¬ P.IsGood μ u u' then pairSum x u u' else 0)) / 2 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun u' _ => by split_ifs <;> simp
    _ ≤ ∑ u ∈ H.children S, (if P.IsBadIncident H μ S u then 1 / 2 + P.halfWidth else 0) / 2 := by
        refine Finset.sum_le_sum fun u hu => ?_
        exact div_le_div_of_nonneg_right (D.sum_bad_pairSum_le hu) (by norm_num)
    _ = _ := by
        rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

open Classical in
/-- The capacity of the rows touching `Q` is `(1 + α)` times the touching mass
minus the bad touching mass. -/
theorem touchCap_eq {μ : TreeDist n x} {S : Finset (Fin n)} {α : ℝ}
    (Q : Finset (Finset (Fin n))) :
    touchCap P μ α (H.children S) Q
      = (1 + α) * (∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
          (if u ∈ Q ∨ u' ∈ Q then pairSum x u u' / 2 else 0)
        - ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
          (if (u ∈ Q ∨ u' ∈ Q) ∧ ¬ P.IsGood μ u u' then pairSum x u u' / 2 else 0)) := by
  classical
  unfold touchCap
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u' _ => ?_
  unfold rowCap
  by_cases h1 : u ∈ Q ∨ u' ∈ Q
  all_goals by_cases h2 : P.IsGood μ u u'
  all_goals simp [h1, h2]
  all_goals ring

end Bounds

section Network

variable (x) (μ : TreeDist n x) (S : Finset (Fin n)) (ch : Finset (Finset (Fin n)))
  (α εB : ℝ) (k : ℕ)

open Classical in
/-- Row capacities. -/
noncomputable def rowCapacity (p : OrientedBundle ch) : ℝ := rowCap P μ α p.fst p.snd

open Classical in
/-- Arc capacities: a row reaches its two endpoints. -/
noncomputable def arcCapacity (p : OrientedBundle ch) (u : {u // u ∈ ch}) : ℝ :=
  if u.1 = p.fst ∨ u.1 = p.snd then rowCapacity P x μ ch α p else 0

open Classical in
/-- **The cut condition from Hall.**  If every atom family's demand is covered
by the rows touching it, every cut has capacity at least the total demand. -/
theorem cutCap_ge_of_hall (hx : ∀ e, 0 ≤ x e) (hα : 0 ≤ α)
    (hdisj : ∀ u ∈ ch, ∀ u' ∈ ch, u ≠ u' → Disjoint u u')
    (hall : ∀ Q ⊆ ch, ∑ u ∈ Q, demand x S εB k u ≤ touchCap P μ α ch Q)
    (SA : Finset (OrientedBundle ch)) (SB : Finset {u // u ∈ ch}) :
    totalDemand x S ch εB k ≤ cutCap (arcCapacity P x μ ch α) (rowCapacity P x μ ch α)
      (colCapacity x S ch εB k) SA SB := by
  classical
  unfold cutCap totalDemand
  set Q := atomsOf ch SB with hQ
  have hrow_nn : ∀ p : OrientedBundle ch, 0 ≤ rowCapacity P x μ ch α p := fun p =>
    rowCap_nonneg P hx μ hα (hdisj _ p.fst_mem _ p.snd_mem p.ne)
  -- the rows touching `Q`
  have htouch : touchCap P μ α ch Q
      = ∑ p : OrientedBundle ch,
          (if p.fst ∈ Q ∨ p.snd ∈ Q then rowCapacity P x μ ch α p else 0) := by
    unfold touchCap rowCapacity
    exact (OrientedBundle.sum_eq _).symm
  -- split the columns
  have hcol : ∑ u : {u // u ∈ ch}, colCapacity x S ch εB k u
      = ∑ u ∈ SB, colCapacity x S ch εB k u + ∑ u ∈ SBᶜ, colCapacity x S ch εB k u := by
    rw [← Finset.sum_add_sum_compl SB]
  rw [hcol, sum_col_compl]
  -- a touching row pays either as an uncaptured row or across an arc
  have hpay : ∑ p : OrientedBundle ch,
      (if p.fst ∈ Q ∨ p.snd ∈ Q then rowCapacity P x μ ch α p else 0)
      ≤ ∑ p ∈ SAᶜ, rowCapacity P x μ ch α p
        + ∑ p ∈ SA, ∑ u ∈ SBᶜ, arcCapacity P x μ ch α p u := by
    rw [← Finset.sum_add_sum_compl SA (fun p =>
      if p.fst ∈ Q ∨ p.snd ∈ Q then rowCapacity P x μ ch α p else 0), add_comm]
    refine add_le_add (Finset.sum_le_sum fun p _ => ?_) (Finset.sum_le_sum fun p _ => ?_)
    · split_ifs
      · exact le_rfl
      · exact hrow_nn p
    · split_ifs with h
      · -- an endpoint of `p` is an atom of `SBᶜ`
        obtain ⟨v, hv, hveq⟩ : ∃ v : {u // u ∈ ch}, v ∉ SB ∧ (v.1 = p.fst ∨ v.1 = p.snd) := by
          rcases h with h | h
          · obtain ⟨v, hv, hve⟩ := (mem_atomsOf ch).mp h; exact ⟨v, hv, Or.inl hve⟩
          · obtain ⟨v, hv, hve⟩ := (mem_atomsOf ch).mp h; exact ⟨v, hv, Or.inr hve⟩
        have hvmem : v ∈ SBᶜ := Finset.mem_compl.mpr hv
        calc rowCapacity P x μ ch α p = arcCapacity P x μ ch α p v := by
              unfold arcCapacity; rw [if_pos hveq]
          _ ≤ ∑ u ∈ SBᶜ, arcCapacity P x μ ch α p u :=
              Finset.single_le_sum (f := fun u => arcCapacity P x μ ch α p u)
                (fun u _ => by unfold arcCapacity; split_ifs <;> [exact hrow_nn p; exact le_rfl])
                hvmem
      · exact Finset.sum_nonneg fun u _ => by
          unfold arcCapacity; split_ifs <;> [exact hrow_nn p; exact le_rfl]
  have hH := hall Q (atomsOf_subset ch SB)
  rw [htouch] at hH
  linarith

/-- **The saturating flow.** -/
theorem exists_saturating_flow (hx : ∀ e, 0 ≤ x e) (hα : 0 ≤ α) (hεB : εB ≤ 1)
    (hdisj : ∀ u ∈ ch, ∀ u' ∈ ch, u ≠ u' → Disjoint u u')
    (hall : ∀ Q ⊆ ch, ∑ u ∈ Q, demand x S εB k u ≤ touchCap P μ α ch Q) :
    ∃ z : OrientedBundle ch → {u // u ∈ ch} → ℝ,
      IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z
      ∧ ∀ u, ∑ p, z p u = colCapacity x S ch εB k u := by
  classical
  have hrow_nn : ∀ p : OrientedBundle ch, 0 ≤ rowCapacity P x μ ch α p := fun p =>
    rowCap_nonneg P hx μ hα (hdisj _ p.fst_mem _ p.snd_mem p.ne)
  have hcol_nn : ∀ u : {u // u ∈ ch}, 0 ≤ colCapacity x S ch εB k u := by
    intro u
    unfold colCapacity demand
    have hF : 0 ≤ fFactor x S εB u.1 := by unfold fFactor; split_ifs <;> linarith
    have hZ : 0 ≤ zFactor x S k u.1 := by
      have := one_le_zFactor (x := x) S k u.1; linarith
    exact mul_nonneg (mul_nonneg (upSum_nonneg hx S u.1) hF) hZ
  obtain ⟨z, hz, htot⟩ := exists_flow_of_cut
    (y := arcCapacity P x μ ch α) (cA := rowCapacity P x μ ch α)
    (cB := colCapacity x S ch εB k) (τ := totalDemand x S ch εB k)
    (fun p u => by unfold arcCapacity; split_ifs <;> [exact hrow_nn p; exact le_rfl])
    hrow_nn hcol_nn (Finset.sum_nonneg fun u _ => hcol_nn u)
    (cutCap_ge_of_hall P x μ S ch α εB k hx hα hdisj hall)
  refine ⟨z, hz, ?_⟩
  -- the column inequalities sum to an equality
  have hsum : ∑ u : {u // u ∈ ch}, ∑ p, z p u = ∑ u : {u // u ∈ ch}, colCapacity x S ch εB k u := by
    rw [← flowTotal_eq_col, htot]; rfl
  exact fun u => (Finset.sum_eq_sum_iff_of_le (fun u _ => hz.col u)).mp hsum u (Finset.mem_univ u)

end Network

section Alloc

variable (x) {ch : Finset (Finset (Fin n))} (S : Finset (Fin n)) (εB : ℝ)
  (z : OrientedBundle ch → {u // u ∈ ch} → ℝ)

variable {μ : TreeDist n x} {α : ℝ} {k : ℕ}

theorem bundleAlloc_nonneg (hεB : εB < 1)
    (hz : IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z)
    (u u' : Finset (Fin n)) : 0 ≤ bundleAlloc x S εB z u u' := by
  classical
  unfold bundleAlloc
  split_ifs
  · exact div_nonneg (add_nonneg (hz.nonneg _ _) (hz.nonneg _ _)) (fFactor_pos hεB u).le
  · exact le_rfl

/-- A nonzero allocation sits on a good bundle at one of its endpoints. -/
theorem bundleAlloc_support
    (hz : IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z)
    {u u' : Finset (Fin n)} (h : bundleAlloc x S εB z u u' ≠ 0) :
    u ∈ ch ∧ u' ∈ ch ∧ u ≠ u' ∧ P.IsGood μ u u' := by
  classical
  unfold bundleAlloc at h
  split_ifs at h with hm
  · refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
    by_contra hbad
    apply h
    have h1 : z ⟨u, u', hm.1, hm.2.1, hm.2.2⟩ ⟨u, hm.1⟩ = 0 := by
      refine le_antisymm ?_ (hz.nonneg _ _)
      refine (hz.le_cap _ _).trans ?_
      unfold arcCapacity rowCapacity rowCap
      split_ifs <;> simp_all
    have h2 : z ⟨u', u, hm.2.1, hm.1, hm.2.2.symm⟩ ⟨u, hm.1⟩ = 0 := by
      refine le_antisymm ?_ (hz.nonneg _ _)
      refine (hz.le_cap _ _).trans ?_
      unfold arcCapacity rowCapacity rowCap
      have : ¬ P.IsGood μ u' u := fun h' => hbad (isGood_comm.mp h')
      split_ifs <;> simp_all
    rw [h1, h2, add_zero, zero_div]
  · exact absurd rfl h

/-- The flow out of a row goes to its two endpoints only. -/
theorem row_sum_eq
    (hz : IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z)
    (p : OrientedBundle ch) :
    ∑ f, z p f = z p ⟨p.fst, p.fst_mem⟩ + z p ⟨p.snd, p.snd_mem⟩ := by
  classical
  have hzero : ∀ f : {u // u ∈ ch}, f ≠ ⟨p.fst, p.fst_mem⟩ → f ≠ ⟨p.snd, p.snd_mem⟩ →
      z p f = 0 := by
    intro f h1 h2
    refine le_antisymm ?_ (hz.nonneg _ _)
    refine (hz.le_cap _ _).trans ?_
    unfold arcCapacity
    rw [if_neg]
    rintro (h | h)
    · exact h1 (Subtype.ext h)
    · exact h2 (Subtype.ext h)
  have hne : (⟨p.fst, p.fst_mem⟩ : {u // u ∈ ch}) ≠ ⟨p.snd, p.snd_mem⟩ :=
    fun h => p.ne (congrArg Subtype.val h)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨p.fst, p.fst_mem⟩),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)]
  rw [Finset.sum_eq_zero fun f hf => hzero f (Finset.mem_erase.mp (Finset.mem_erase.mp hf).2).1
    (Finset.mem_erase.mp hf).1]
  ring

/-- **A bundle allocates at most `(1 + α) x_e`** over its two endpoints: the
two orientations' row sums. -/
theorem bundleAlloc_bound (hx : ∀ e, 0 ≤ x e) (hεB : εB < 1)
    (hz : IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z)
    {u u' : Finset (Fin n)} (hu : u ∈ ch) (hu' : u' ∈ ch) (huu' : u ≠ u') (hd : Disjoint u u')
    (hα : 0 ≤ α) :
    bundleAlloc x S εB z u u' * fFactor x S εB u + bundleAlloc x S εB z u' u * fFactor x S εB u'
      ≤ (1 + α) * pairSum x u u' := by
  classical
  have hF : fFactor x S εB u ≠ 0 := (fFactor_pos hεB u).ne'
  have hF' : fFactor x S εB u' ≠ 0 := (fFactor_pos hεB u').ne'
  set p : OrientedBundle ch := ⟨u, u', hu, hu', huu'⟩ with hp
  set p' : OrientedBundle ch := ⟨u', u, hu', hu, huu'.symm⟩ with hp'
  have e1 : bundleAlloc x S εB z u u' * fFactor x S εB u
      = z p ⟨u, hu⟩ + z p' ⟨u, hu⟩ := by
    unfold bundleAlloc
    rw [dif_pos ⟨hu, hu', huu'⟩, div_mul_cancel₀ _ hF]
  have e2 : bundleAlloc x S εB z u' u * fFactor x S εB u'
      = z p' ⟨u', hu'⟩ + z p ⟨u', hu'⟩ := by
    unfold bundleAlloc
    rw [dif_pos ⟨hu', hu, huu'.symm⟩, div_mul_cancel₀ _ hF']
  have r1 := hz.row p
  have r2 := hz.row p'
  rw [row_sum_eq P x S εB z hz] at r1 r2
  have hcap : rowCapacity P x μ ch α p + rowCapacity P x μ ch α p' ≤ (1 + α) * pairSum x u u' := by
    unfold rowCapacity
    change rowCap P μ α u u' + rowCap P μ α u' u ≤ (1 + α) * pairSum x u u'
    rw [rowCap_comm P μ α u' u]
    unfold rowCap
    have := pairSum_nonneg_lp hx hd
    split_ifs
    · linarith
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + α) this]
  rw [e1, e2]
  change z p ⟨u, hu⟩ + z p' ⟨u, hu⟩ + (z p' ⟨u', hu'⟩ + z p ⟨u', hu'⟩) ≤ _
  linarith

/-- The flow into an atom, regrouped by the first and the second endpoint. -/
theorem col_sum_eq
    (hz : IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z)
    {u : Finset (Fin n)} (hu : u ∈ ch) :
    ∑ p, z p ⟨u, hu⟩
      = ∑ u' ∈ ch.erase u, (if h : u' ∈ ch ∧ u' ≠ u then
          z ⟨u, u', hu, h.1, h.2.symm⟩ ⟨u, hu⟩ + z ⟨u', u, h.1, hu, h.2⟩ ⟨u, hu⟩ else 0) := by
  classical
  -- read the flow off the pair
  set g : Finset (Fin n) → Finset (Fin n) → ℝ := fun a b =>
    if h : a ∈ ch ∧ b ∈ ch ∧ a ≠ b then z ⟨a, b, h.1, h.2.1, h.2.2⟩ ⟨u, hu⟩ else 0 with hg
  have h1 : ∑ p, z p ⟨u, hu⟩ = ∑ p : OrientedBundle ch, g p.fst p.snd := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hg]
    simp only [p.fst_mem, p.snd_mem, p.ne, and_self, ne_eq, not_false_eq_true, dite_true]
  rw [h1, OrientedBundle.sum_eq]
  -- rows not at `u` carry nothing into `u`
  have hzero : ∀ a ∈ ch, ∀ b ∈ ch.erase a, a ≠ u → b ≠ u → g a b = 0 := by
    intro a ha b hb hau hbu
    rw [hg]
    simp only
    split_ifs with h
    · refine le_antisymm ?_ (hz.nonneg _ _)
      refine (hz.le_cap _ _).trans ?_
      unfold arcCapacity
      rw [if_neg]
      rintro (h' | h')
      · exact hau h'.symm
      · exact hbu h'.symm
    · rfl
  -- split off the first index `u`
  rw [← Finset.add_sum_erase _ _ hu]
  have h2 : ∑ a ∈ ch.erase u, ∑ b ∈ ch.erase a, g a b = ∑ a ∈ ch.erase u, g a u := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have hau := (Finset.mem_erase.mp ha).1
    rw [Finset.sum_eq_single u]
    · intro b hb hbu; exact hzero a (Finset.mem_erase.mp ha).2 b hb hau hbu
    · intro h; exact absurd (Finset.mem_erase.mpr ⟨hau.symm, hu⟩) h
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u' hu' => ?_
  have hu'u := (Finset.mem_erase.mp hu').1
  have hu'c := (Finset.mem_erase.mp hu').2
  rw [dif_pos ⟨hu'c, hu'u⟩, hg]
  simp only [hu, hu'c, hu'u, hu'u.symm, and_self, ne_eq, not_false_eq_true, dite_true]

/-- **The allocation at an atom sums to `x(δ↑(u)) Z_u`** (KKO (27)). -/
theorem sum_bundleAlloc (hεB : εB < 1)
    (hz : IsFlow (arcCapacity P x μ ch α) (rowCapacity P x μ ch α) (colCapacity x S ch εB k) z)
    (hsat : ∀ v, ∑ p, z p v = colCapacity x S ch εB k v)
    {u : Finset (Fin n)} (hu : u ∈ ch) :
    ∑ u' ∈ ch.erase u, bundleAlloc x S εB z u u' = upSum x S u * zFactor x S k u := by
  classical
  have hF : fFactor x S εB u ≠ 0 := (fFactor_pos hεB u).ne'
  have hcol := hsat ⟨u, hu⟩
  rw [col_sum_eq P x S εB z hz hu] at hcol
  have hsum : (∑ u' ∈ ch.erase u, bundleAlloc x S εB z u u') * fFactor x S εB u
      = ∑ u' ∈ ch.erase u, (if h : u' ∈ ch ∧ u' ≠ u then
          z ⟨u, u', hu, h.1, h.2.symm⟩ ⟨u, hu⟩ + z ⟨u', u, h.1, hu, h.2⟩ ⟨u, hu⟩ else 0) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    have hu'u := (Finset.mem_erase.mp hu').1
    have hu'c := (Finset.mem_erase.mp hu').2
    unfold bundleAlloc
    rw [dif_pos ⟨hu, hu'c, hu'u.symm⟩, dif_pos ⟨hu'c, hu'u⟩, div_mul_cancel₀ _ hF]
  rw [hcol] at hsum
  unfold colCapacity demand at hsum
  have hsum' : (∑ u' ∈ ch.erase u, bundleAlloc x S εB z u u') * fFactor x S εB u
      = (upSum x S u * zFactor x S k u) * fFactor x S εB u := by
    rw [hsum]; ring
  exact mul_right_cancel₀ hF hsum'

end Alloc


/-- The matching allocation with its goodness policy and numerical weights explicit. -/
structure MatchingData {e₀ : RootEdge n} {eta : ℝ} (H : Hierarchy x e₀ eta)
    (μ : TreeDist n x) (S : Finset (Fin n)) (epsilonB alpha : ℝ) where
  m : Finset (Fin n) → Finset (Fin n) → ℝ
  nonneg : ∀ u v, 0 ≤ m u v
  support : ∀ u v, m u v ≠ 0 →
    u ∈ H.children S ∧ v ∈ H.children S ∧ u ≠ v ∧ P.IsGood μ u v
  bound : ∀ u ∈ H.children S, ∀ v ∈ H.children S, u ≠ v →
    m u v * fFactor x S epsilonB u + m v u * fFactor x S epsilonB v ≤
      (1 + alpha) * pairSum x u v
  sum : ∀ u ∈ H.children S,
    ∑ v ∈ (H.children S).erase u, m u v = upSum x S u * zFactor x S (H.children S).card u

/-- Hall's condition constructs the full allocation data for the selected policy. -/
theorem exists_matchingData_of_hall {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) {eta : ℝ} (H : Hierarchy x e₀ eta) (S : Finset (Fin n))
    {epsilonB alpha : ℝ} (hB : epsilonB < 1) (ha : 0 ≤ alpha)
    (hall : ∀ Q ⊆ H.children S, ∑ u ∈ Q, demand x S epsilonB (H.children S).card u ≤
      P.touchCap μ alpha (H.children S) Q) :
    Nonempty (P.MatchingData H μ S epsilonB alpha) := by
  classical
  have hdisj : ∀ u ∈ H.children S, ∀ v ∈ H.children S, u ≠ v → Disjoint u v :=
    fun u hu v hv huv => H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hv) huv
  obtain ⟨z, hz, hsat⟩ := P.exists_saturating_flow x μ S (H.children S) alpha epsilonB
    (H.children S).card hx.nonneg ha hB.le hdisj hall
  refine ⟨⟨bundleAlloc x S epsilonB z,
    fun u v => P.bundleAlloc_nonneg x S epsilonB z hB hz u v,
    fun u v hm => P.bundleAlloc_support x S epsilonB z hz hm,
    fun u hu v hv huv => ?_, fun u hu => P.sum_bundleAlloc x S epsilonB z hB hz hsat hu⟩⟩
  exact P.bundleAlloc_bound x S epsilonB z hx.nonneg hB hz hu hv huv (hdisj u hu v hv huv) ha

/-- The support field also gives the zero allocation on every excluded pair. -/
theorem MatchingData.m_eq_zero_of_not {e₀ : RootEdge n} {eta : ℝ} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {S : Finset (Fin n)} {epsilonB alpha : ℝ}
    (M : P.MatchingData H μ S epsilonB alpha) {u v : Finset (Fin n)}
    (hn : ¬ (u ∈ H.children S ∧ v ∈ H.children S ∧ u ≠ v ∧ P.IsGood μ u v)) :
    M.m u v = 0 := by
  by_contra hm
  exact hn (M.support u v hm)

end TSPGap.BundleGoodnessPolicy

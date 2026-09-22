/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Tactic

/-!
# Max-flow / min-cut for the four-layer network `s → A → B → t`

Proposition 5.6 builds a flow network with an arc `e → f` of capacity
`y e f` for every `e ∈ A`, `f ∈ B`, source arcs of capacity `cA e` and sink
arcs of capacity `cB f`, and needs a flow of a *prescribed* value `τ` from a
lower bound on every cut.  Mathlib has no max-flow theorem, so this file
proves the specialization, standalone.

The route is compact maximization plus residual reachability.

* `IsFlow`, `flowTotal`, `cutCap` — the network; a cut is named by the pair
  `(SA, SB)` it keeps on the source side.
* `ReachRow` — residual reachability of a *row*, carrying the `Finset` of
  columns still available.  ⚠️ That bookkeeping is what makes the induction
  compose: the flow produced for a row reached through `S.erase f` agrees
  with the original on column `f`, so the residual arc the next step needs
  is still there.  Without it each step can destroy the arcs later steps
  rely on, and the induction fails — which is why the textbook proof builds
  a whole augmenting path before touching the flow.
* `reachRow_slack` — from a reachable row, a flow of the *same value* with
  slack at that row.  This is the augmenting path, carried as an invariant
  rather than built as a list.
* `exists_flow_of_cut` — the theorem: if every cut has capacity at least
  `τ ≥ 0`, there is a flow of value exactly `τ`.
-/

namespace TSPGap

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-! ### The network -/

/-- A feasible flow: nonnegative, and within the arc, source and sink
capacities. -/
structure IsFlow (y : α → β → ℝ) (cA : α → ℝ) (cB : β → ℝ)
    (z : α → β → ℝ) : Prop where
  nonneg : ∀ e f, 0 ≤ z e f
  le_cap : ∀ e f, z e f ≤ y e f
  row : ∀ e, ∑ f, z e f ≤ cA e
  col : ∀ f, ∑ e, z e f ≤ cB f

/-- The value of a flow. -/
noncomputable def flowTotal (z : α → β → ℝ) : ℝ := ∑ e, ∑ f, z e f

/-- The capacity of the cut keeping `SA ⊆ A` and `SB ⊆ B` on the source
side. -/
noncomputable def cutCap (y : α → β → ℝ) (cA : α → ℝ) (cB : β → ℝ)
    (SA : Finset α) (SB : Finset β) : ℝ :=
  (∑ e ∈ SAᶜ, cA e) + (∑ f ∈ SB, cB f) + ∑ e ∈ SA, ∑ f ∈ SBᶜ, y e f

omit [DecidableEq α] [DecidableEq β] in
theorem flowTotal_eq_col (z : α → β → ℝ) :
    flowTotal z = ∑ f, ∑ e, z e f := Finset.sum_comm

/-! ### Two indicator sums -/

omit [Fintype α] in
theorem sum_ite_and_row (e : α) (f : β) (ε : ℝ) (a : α) :
    ∑ b, (if a = e ∧ b = f then ε else 0) = if a = e then ε else 0 := by
  classical
  by_cases ha : a = e
  · rw [if_pos ha]
    rw [Finset.sum_congr rfl (fun b _ => by
      by_cases hb : b = f
      · rw [if_pos ⟨ha, hb⟩, if_pos hb]
      · rw [if_neg (fun hc => hb hc.2), if_neg hb] :
        ∀ b ∈ Finset.univ, (if a = e ∧ b = f then ε else 0)
          = if b = f then ε else 0)]
    simp
  · rw [if_neg ha]
    exact Finset.sum_eq_zero fun b _ => if_neg fun hc => ha hc.1

omit [Fintype β] in
theorem sum_ite_and_col (e : α) (f : β) (ε : ℝ) (b : β) :
    ∑ a, (if a = e ∧ b = f then ε else 0) = if b = f then ε else 0 := by
  classical
  by_cases hb : b = f
  · rw [if_pos hb]
    rw [Finset.sum_congr rfl (fun a _ => by
      by_cases ha : a = e
      · rw [if_pos ⟨ha, hb⟩, if_pos ha]
      · rw [if_neg (fun hc => ha hc.1), if_neg ha] :
        ∀ a ∈ Finset.univ, (if a = e ∧ b = f then ε else 0)
          = if a = e then ε else 0)]
    simp
  · rw [if_neg hb]
    exact Finset.sum_eq_zero fun a _ => if_neg fun hc => hb hc.2

/-! ### Residual reachability -/

/-- `ReachRow y cA z S e`: the source reaches row `e` through residual arcs,
using each column of `S` at most once. -/
inductive ReachRow (y : α → β → ℝ) (cA : α → ℝ) (z : α → β → ℝ) :
    Finset β → α → Prop
  | src {S : Finset β} {e : α} (h : ∑ f, z e f < cA e) : ReachRow y cA z S e
  | back {S : Finset β} {e e' : α} {f : β} (hfS : f ∈ S)
      (he' : ReachRow y cA z (S.erase f) e') (hres : z e' f < y e' f)
      (hpos : 0 < z e f) : ReachRow y cA z S e

omit [Fintype α] [DecidableEq α] in
theorem ReachRow.mono {y : α → β → ℝ} {cA : α → ℝ} {z : α → β → ℝ}
    {S S' : Finset β} {e : α} (h : ReachRow y cA z S e) (hSS : S ⊆ S') :
    ReachRow y cA z S' e := by
  induction h generalizing S' with
  | src h => exact ReachRow.src h
  | back hfS _ hres hpos ih =>
    exact ReachRow.back (hSS hfS) (ih (Finset.erase_subset_erase _ hSS)) hres hpos

omit [Fintype α] [DecidableEq α] in
/-- Freeing one column: either the row stays reachable without it, or that
column is itself reachable. -/
theorem ReachRow.erase_or {y : α → β → ℝ} {cA : α → ℝ} {z : α → β → ℝ}
    {S : Finset β} {e : α} (h : ReachRow y cA z S e) (f : β) :
    ReachRow y cA z (S.erase f) e ∨
      ∃ e', ReachRow y cA z (S.erase f) e' ∧ z e' f < y e' f := by
  induction h with
  | src h => exact Or.inl (ReachRow.src h)
  | @back S e e' g hgS he' hres hpos ih =>
    by_cases hgf : g = f
    · subst hgf
      exact Or.inr ⟨e', he', hres⟩
    · rcases ih with hleft | ⟨e'', he'', hres''⟩
      · refine Or.inl (ReachRow.back (Finset.mem_erase.mpr ⟨hgf, hgS⟩) ?_ hres hpos)
        rwa [Finset.erase_right_comm]
      · exact Or.inr ⟨e'', he''.mono
          (Finset.erase_subset_erase _ (Finset.erase_subset _ _)), hres''⟩

/-! ### Pushing along one residual arc -/

/-- Add `ε` on the arc `(e', f)` and remove it from `(e, f)`. -/
noncomputable def shift (z : α → β → ℝ) (e' e : α) (f : β) (ε : ℝ) :
    α → β → ℝ :=
  fun a b => z a b + (if a = e' ∧ b = f then ε else 0)
    - (if a = e ∧ b = f then ε else 0)

omit [Fintype α] [Fintype β] in
theorem shift_of_ne {z : α → β → ℝ} {e' e : α} {f : β} {ε : ℝ} {a : α} {b : β}
    (hb : b ≠ f) : shift z e' e f ε a b = z a b := by
  rw [shift, if_neg (fun h => hb h.2), if_neg (fun h => hb h.2)]
  ring

omit [Fintype α] [Fintype β] in
theorem shift_fwd {z : α → β → ℝ} {e' e : α} {f : β} {ε : ℝ} (hee : e ≠ e') :
    shift z e' e f ε e' f = z e' f + ε := by
  rw [shift, if_pos ⟨rfl, rfl⟩, if_neg (fun hc => hee hc.1.symm)]
  ring

omit [Fintype α] [Fintype β] in
theorem shift_bwd {z : α → β → ℝ} {e' e : α} {f : β} {ε : ℝ} (hee : e ≠ e') :
    shift z e' e f ε e f = z e f - ε := by
  rw [shift, if_neg (fun hc => hee hc.1), if_pos ⟨rfl, rfl⟩]
  ring

omit [Fintype α] [Fintype β] in
theorem shift_other {z : α → β → ℝ} {e' e : α} {f : β} {ε : ℝ} {a : α} {b : β}
    (h1 : ¬(a = e' ∧ b = f)) (h2 : ¬(a = e ∧ b = f)) :
    shift z e' e f ε a b = z a b := by
  rw [shift, if_neg h1, if_neg h2]
  ring

omit [Fintype α] in
theorem sum_row_shift {z : α → β → ℝ} {e' e : α} {f : β} {ε : ℝ} (a : α) :
    ∑ b, shift z e' e f ε a b
      = (∑ b, z a b) + (if a = e' then ε else 0) - (if a = e then ε else 0) := by
  classical
  simp only [shift, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_ite_and_row]

omit [Fintype β] in
theorem sum_col_shift {z : α → β → ℝ} {e' e : α} {f : β} {ε : ℝ} (b : β) :
    ∑ a, shift z e' e f ε a b = ∑ a, z a b := by
  classical
  simp only [shift, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_ite_and_col]
  ring

/-! ### The augmenting invariant -/

omit [DecidableEq α] in
/-- **From a reachable row, a flow of the same value with slack there.**
The augmenting path, carried as an invariant: the flow produced for a row
reached through `S.erase f` agrees with the original on column `f`. -/
theorem reachRow_slack {y : α → β → ℝ} {cA : α → ℝ} {cB : β → ℝ}
    {z : α → β → ℝ} (hz : IsFlow y cA cB z) {S : Finset β} {e : α}
    (h : ReachRow y cA z S e) :
    ∃ (z' : α → β → ℝ) (ε : ℝ), 0 < ε ∧ IsFlow y cA cB z' ∧
      (∀ a b, b ∉ S → z' a b = z a b) ∧
      (∀ b, ∑ a, z' a b = ∑ a, z a b) ∧
      (∑ b, z' e b) + ε ≤ cA e := by
  classical
  induction h with
  | @src S e hslack =>
    exact ⟨z, cA e - ∑ f, z e f, by linarith, hz, fun _ _ _ => rfl,
      fun _ => rfl, by linarith⟩
  | @back S e e' f hfS he' hres hpos ih =>
    obtain ⟨z₁, ε₁, hε₁, hz₁, hsupp, hcolz, hslack⟩ := ih
    have hzf : ∀ a, z₁ a f = z a f := fun a =>
      hsupp a f (Finset.notMem_erase f S)
    by_cases hee : e = e'
    · -- the arc returns to the row we came from: the old flow already works
      subst hee
      exact ⟨z₁, ε₁, hε₁, hz₁,
        fun a b hb => hsupp a b (fun hc => hb (Finset.mem_of_mem_erase hc)),
        hcolz, hslack⟩
    · set ε := min ε₁ (min (y e' f - z e' f) (z e f)) with hεdef
      have hε0 : 0 < ε := by
        refine lt_min hε₁ (lt_min ?_ hpos)
        linarith
      have hε1 : ε ≤ ε₁ := min_le_left _ _
      have hε2 : ε ≤ y e' f - z e' f :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hε3 : ε ≤ z e f := le_trans (min_le_right _ _) (min_le_right _ _)
      refine ⟨shift z₁ e' e f ε, ε, hε0, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · intro a b
        by_cases h1 : a = e' ∧ b = f
        · obtain ⟨ha, hb⟩ := h1
          subst ha
          subst hb
          rw [shift_fwd hee]
          linarith [hz₁.nonneg a b, hε0]
        · by_cases h2 : a = e ∧ b = f
          · obtain ⟨ha, hb⟩ := h2
            subst ha
            subst hb
            rw [shift_bwd hee, hzf]
            linarith
          · rw [shift_other h1 h2]
            exact hz₁.nonneg a b
      · intro a b
        by_cases h1 : a = e' ∧ b = f
        · obtain ⟨ha, hb⟩ := h1
          subst ha
          subst hb
          rw [shift_fwd hee, hzf]
          linarith
        · by_cases h2 : a = e ∧ b = f
          · obtain ⟨ha, hb⟩ := h2
            subst ha
            subst hb
            rw [shift_bwd hee]
            linarith [hz₁.le_cap a b, hε0]
          · rw [shift_other h1 h2]
            exact hz₁.le_cap a b
      · intro a
        rw [sum_row_shift]
        by_cases ha' : a = e'
        · subst ha'
          rw [if_pos rfl, if_neg (fun hc => hee hc.symm)]
          linarith [hslack]
        · rw [if_neg ha']
          by_cases ha : a = e
          · subst ha
            rw [if_pos rfl]
            linarith [hz₁.row a, hε0]
          · rw [if_neg ha]
            linarith [hz₁.row a]
      · intro b
        rw [sum_col_shift, hcolz b]
        exact hz.col b
      · intro a b hb
        rw [shift_of_ne (fun hc => hb (by rw [hc]; exact hfS)),
          hsupp a b (fun hc => hb (Finset.mem_of_mem_erase hc))]
      · intro b
        rw [sum_col_shift, hcolz b]
      · rw [sum_row_shift, if_neg (fun hc => hee hc), if_pos rfl]
        linarith [hz₁.row e]

/-! ### No augmenting path at a maximum -/

omit [DecidableEq α] in
/-- If a reachable column still has slack, the flow is not maximal. -/
theorem exists_better_of_reach {y : α → β → ℝ} {cA : α → ℝ} {cB : β → ℝ}
    {z : α → β → ℝ} (hz : IsFlow y cA cB z) {e : α} {f : β}
    (hreach : ReachRow y cA z (Finset.univ.erase f) e) (hres : z e f < y e f)
    (hslack : ∑ a, z a f < cB f) :
    ∃ z', IsFlow y cA cB z' ∧ flowTotal z < flowTotal z' := by
  classical
  obtain ⟨z₁, ε₁, hε₁, hz₁, hsupp, hcolz, hslack₁⟩ := reachRow_slack hz hreach
  have hzf : ∀ a, z₁ a f = z a f := fun a =>
    hsupp a f (Finset.notMem_erase f Finset.univ)
  set ε := min ε₁ (min (y e f - z e f) (cB f - ∑ a, z a f)) with hεdef
  have hε0 : 0 < ε := lt_min hε₁ (lt_min (by linarith) (by linarith))
  have hε1 : ε ≤ ε₁ := min_le_left _ _
  have hε2 : ε ≤ y e f - z e f := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε3 : ε ≤ cB f - ∑ a, z a f :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have htot1 : flowTotal z₁ = flowTotal z := by
    rw [flowTotal_eq_col, flowTotal_eq_col]
    exact Finset.sum_congr rfl fun b _ => hcolz b
  refine ⟨fun a b => z₁ a b + (if a = e ∧ b = f then ε else 0),
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    by_cases hc : a = e ∧ b = f
    · rw [if_pos hc]
      linarith [hz₁.nonneg a b, hε0]
    · rw [if_neg hc]
      linarith [hz₁.nonneg a b]
  · intro a b
    by_cases hc : a = e ∧ b = f
    · obtain ⟨ha, hb⟩ := hc
      subst ha
      subst hb
      rw [if_pos ⟨rfl, rfl⟩, hzf]
      linarith
    · rw [if_neg hc]
      linarith [hz₁.le_cap a b]
  · intro a
    rw [Finset.sum_add_distrib, sum_ite_and_row]
    by_cases ha : a = e
    · subst ha
      rw [if_pos rfl]
      linarith [hslack₁]
    · rw [if_neg ha]
      linarith [hz₁.row a]
  · intro b
    rw [Finset.sum_add_distrib, sum_ite_and_col, hcolz b]
    by_cases hb : b = f
    · subst hb
      rw [if_pos rfl]
      linarith
    · rw [if_neg hb]
      linarith [hz.col b]
  · have hval : flowTotal (fun a b => z₁ a b + (if a = e ∧ b = f then ε else 0))
        = flowTotal z₁ + ε := by
      rw [flowTotal, flowTotal]
      rw [Finset.sum_congr rfl (fun a _ => by
        rw [Finset.sum_add_distrib, sum_ite_and_row] :
          ∀ a ∈ Finset.univ, ∑ b, (z₁ a b + (if a = e ∧ b = f then ε else 0))
            = (∑ b, z₁ a b) + (if a = e then ε else 0))]
      rw [Finset.sum_add_distrib]
      simp
    rw [hval, htot1]
    linarith

/-! ### Maximization -/

omit [DecidableEq α] [DecidableEq β] in
theorem exists_max_flow {y : α → β → ℝ} {cA : α → ℝ} {cB : β → ℝ}
    (hy : ∀ e f, 0 ≤ y e f) (hcA : ∀ e, 0 ≤ cA e) (hcB : ∀ f, 0 ≤ cB f) :
    ∃ z, IsFlow y cA cB z ∧
      ∀ z', IsFlow y cA cB z' → flowTotal z' ≤ flowTotal z := by
  classical
  have hcont : Continuous (flowTotal : (α → β → ℝ) → ℝ) := by
    refine continuous_finsetSum _ fun e _ => continuous_finsetSum _ fun f _ => ?_
    exact (continuous_apply f).comp (continuous_apply e)
  have h1 : IsClosed {z : α → β → ℝ | ∀ e f, 0 ≤ z e f} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun e => isClosed_iInter fun f =>
      isClosed_le continuous_const ((continuous_apply f).comp (continuous_apply e))
  have h2 : IsClosed {z : α → β → ℝ | ∀ e f, z e f ≤ y e f} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun e => isClosed_iInter fun f =>
      isClosed_le ((continuous_apply f).comp (continuous_apply e)) continuous_const
  have h3 : IsClosed {z : α → β → ℝ | ∀ e, ∑ f, z e f ≤ cA e} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun e => isClosed_le ?_ continuous_const
    exact continuous_finsetSum _ fun f _ =>
      (continuous_apply f).comp (continuous_apply e)
  have h4 : IsClosed {z : α → β → ℝ | ∀ f, ∑ e, z e f ≤ cB f} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun f => isClosed_le ?_ continuous_const
    exact continuous_finsetSum _ fun e _ =>
      (continuous_apply f).comp (continuous_apply e)
  have hKeq : {z : α → β → ℝ | IsFlow y cA cB z}
      = ({z : α → β → ℝ | ∀ e f, 0 ≤ z e f} ∩ {z | ∀ e f, z e f ≤ y e f})
        ∩ ({z | ∀ e, ∑ f, z e f ≤ cA e} ∩ {z | ∀ f, ∑ e, z e f ≤ cB f}) := by
    ext z
    exact ⟨fun h => ⟨⟨h.nonneg, h.le_cap⟩, h.row, h.col⟩,
      fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩⟩
  have hcl : IsClosed {z : α → β → ℝ | IsFlow y cA cB z} := by
    rw [hKeq]
    exact (h1.inter h2).inter (h3.inter h4)
  have hsub : {z : α → β → ℝ | IsFlow y cA cB z} ⊆ Set.Icc (0 : α → β → ℝ) y :=
    fun z hz => ⟨fun a b => hz.nonneg a b, fun a b => hz.le_cap a b⟩
  have hcomp : IsCompact {z : α → β → ℝ | IsFlow y cA cB z} :=
    IsCompact.of_isClosed_subset isCompact_Icc hcl hsub
  have hne : {z : α → β → ℝ | IsFlow y cA cB z}.Nonempty :=
    ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, fun e f => hy e f,
      fun e => by simpa using hcA e, fun f => by simpa using hcB f⟩⟩
  obtain ⟨z, hzK, hmax⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
  exact ⟨z, hzK, fun z' hz' => hmax hz'⟩

/-! ### The theorem -/

/-- **Max-flow from min-cut.**  A cut bound `τ ≥ 0` produces a flow of value
exactly `τ`. -/
theorem exists_flow_of_cut {y : α → β → ℝ} {cA : α → ℝ} {cB : β → ℝ} {τ : ℝ}
    (hy : ∀ e f, 0 ≤ y e f) (hcA : ∀ e, 0 ≤ cA e) (hcB : ∀ f, 0 ≤ cB f)
    (hτ0 : 0 ≤ τ) (hcut : ∀ SA SB, τ ≤ cutCap y cA cB SA SB) :
    ∃ z, IsFlow y cA cB z ∧ flowTotal z = τ := by
  classical
  obtain ⟨z, hz, hmax⟩ := exists_max_flow hy hcA hcB
  set SA : Finset α :=
    Finset.univ.filter (fun e => ReachRow y cA z Finset.univ e) with hSA
  set SB : Finset β := Finset.univ.filter
    (fun f => ∃ e, ReachRow y cA z (Finset.univ.erase f) e ∧ z e f < y e f)
    with hSB
  -- (i) rows off `SA` are saturated
  have hrowsat : ∀ e ∈ SAᶜ, ∑ f, z e f = cA e := by
    intro e he
    refine le_antisymm (hz.row e) (le_of_not_gt fun hlt => ?_)
    have : e ∈ SA := by
      rw [hSA, Finset.mem_filter]
      exact ⟨Finset.mem_univ e, ReachRow.src hlt⟩
    exact (Finset.mem_compl.mp he) this
  -- (ii) columns in `SB` are saturated
  have hcolsat : ∀ f ∈ SB, ∑ e, z e f = cB f := by
    intro f hf
    obtain ⟨-, e, hreach, hres⟩ := Finset.mem_filter.mp hf
    refine le_antisymm (hz.col f) (le_of_not_gt fun hlt => ?_)
    obtain ⟨z', hz', hgt⟩ := exists_better_of_reach hz hreach hres hlt
    exact absurd (hmax z' hz') (not_le.mpr hgt)
  -- (iii) arcs from `SA` to `SBᶜ` are saturated
  have harcsat : ∀ e ∈ SA, ∀ f ∈ SBᶜ, z e f = y e f := by
    intro e he f hf
    refine le_antisymm (hz.le_cap e f) (le_of_not_gt fun hlt => ?_)
    have hreach : ReachRow y cA z Finset.univ e := (Finset.mem_filter.mp he).2
    have hmem : f ∈ SB := by
      rw [hSB, Finset.mem_filter]
      refine ⟨Finset.mem_univ f, ?_⟩
      rcases hreach.erase_or f with hleft | ⟨e', he', hres'⟩
      · exact ⟨e, hleft, hlt⟩
      · exact ⟨e', he', hres'⟩
    exact (Finset.mem_compl.mp hf) hmem
  -- (iv) arcs from `SAᶜ` into `SB` are empty
  have hzero : ∀ e ∈ SAᶜ, ∀ f ∈ SB, z e f = 0 := by
    intro e he f hf
    refine le_antisymm (le_of_not_gt fun hpos => ?_) (hz.nonneg e f)
    obtain ⟨-, e', hreach, hres⟩ := Finset.mem_filter.mp hf
    have : e ∈ SA := by
      rw [hSA, Finset.mem_filter]
      exact ⟨Finset.mem_univ e,
        ReachRow.back (Finset.mem_univ f) hreach hres hpos⟩
    exact (Finset.mem_compl.mp he) this
  -- the cut identity
  have hsplit : ∀ g : α → β → ℝ, ∑ e, ∑ f, g e f
      = ((∑ e ∈ SA, ∑ f ∈ SB, g e f) + ∑ e ∈ SA, ∑ f ∈ SBᶜ, g e f)
        + ∑ e ∈ SAᶜ, ∑ f, g e f := by
    intro g
    rw [← Finset.sum_add_sum_compl SA (fun e => ∑ f, g e f)]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ =>
      (Finset.sum_add_sum_compl SB (fun f => g e f)).symm
  have hid : cutCap y cA cB SA SB = flowTotal z := by
    rw [cutCap, flowTotal, hsplit z]
    have e1 : ∑ e ∈ SAᶜ, cA e = ∑ e ∈ SAᶜ, ∑ f, z e f :=
      (Finset.sum_congr rfl fun e he => hrowsat e he).symm
    have e2 : ∑ f ∈ SB, cB f = ∑ e ∈ SA, ∑ f ∈ SB, z e f := by
      have step : ∀ f ∈ SB, cB f = ∑ e ∈ SA, z e f := by
        intro f hf
        rw [← hcolsat f hf, ← Finset.sum_add_sum_compl SA (fun e => z e f),
          Finset.sum_eq_zero (fun e he => hzero e he f hf), add_zero]
      rw [Finset.sum_congr rfl step]
      exact Finset.sum_comm
    have e3 : ∑ e ∈ SA, ∑ f ∈ SBᶜ, y e f = ∑ e ∈ SA, ∑ f ∈ SBᶜ, z e f :=
      Finset.sum_congr rfl fun e he =>
        Finset.sum_congr rfl fun f hf => (harcsat e he f hf).symm
    rw [e1, e2, e3]
    ring
  have hge : τ ≤ flowTotal z := by
    rw [← hid]
    exact hcut SA SB
  -- scale down to exactly `τ`
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact ⟨z, hz, heq.symm⟩
  · have hpos : 0 < flowTotal z := lt_of_le_of_lt hτ0 hlt
    set c : ℝ := τ / flowTotal z with hc
    have hc0 : 0 ≤ c := div_nonneg hτ0 hpos.le
    have hc1 : c ≤ 1 := (div_le_one hpos).mpr hlt.le
    refine ⟨fun a b => c * z a b, ⟨fun a b => mul_nonneg hc0 (hz.nonneg a b),
      fun a b => ?_, fun a => ?_, fun b => ?_⟩, ?_⟩
    · calc c * z a b ≤ 1 * z a b :=
            mul_le_mul_of_nonneg_right hc1 (hz.nonneg a b)
        _ = z a b := one_mul _
        _ ≤ y a b := hz.le_cap a b
    · rw [← Finset.mul_sum]
      calc c * ∑ f, z a f ≤ 1 * ∑ f, z a f :=
            mul_le_mul_of_nonneg_right hc1
              (Finset.sum_nonneg fun f _ => hz.nonneg a f)
        _ = ∑ f, z a f := one_mul _
        _ ≤ cA a := hz.row a
    · rw [← Finset.mul_sum]
      calc c * ∑ e, z e b ≤ 1 * ∑ e, z e b :=
            mul_le_mul_of_nonneg_right hc1
              (Finset.sum_nonneg fun e _ => hz.nonneg e b)
        _ = ∑ e, z e b := one_mul _
        _ ≤ cB b := hz.col b
    · have : flowTotal (fun a b => c * z a b) = c * flowTotal z := by
        rw [flowTotal, flowTotal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      rw [this, hc, div_mul_cancel₀ _ hpos.ne']

end TSPGap

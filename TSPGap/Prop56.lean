/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CutRepair
import TSPGap.Selected

/-!
# KKO21 Proposition 5.6

The max-flow construction, assembled.  The network is unconditional: arc
capacities are the joint pair-cell masses `J e f = pairCellMass w A B e f`,
source and sink capacities are `b · x e` with `b = 0.11(0.473ζ)²`, and the
target flow is `M = b · keep` with `keep = 1 − η − ζ/2.1`.

A cut with underlying sets `X ⊆ A`, `Y ⊆ B` has capacity
`b·x(A∖X) + b·x(Y) + J(X, B∖Y)`.  Writing `γ = x(X) − x(Y)`, the outer arcs
alone give `b(x(A) − γ) ≥ b·keep` whenever `γ ≤ ζ/2.1`; otherwise
`cut_repair` supplies `J(X, B∖Y) ≥ b(γ − ζ/2.1)` and the two pieces again
sum to `b·keep`.  `sum_pairCellMass_rect` is what matches the middle term to
`cut_repair`'s four-count event — the rectangle of cells over `X × (B∖Y)` is
exactly the event `|T∩X| = |T∩(B∖Y)| = |T∩A| = |T∩B| = 1`.

⚠️ The conclusion is the existence of a **selected subweight**, not of an
event: the flow prescribes a real fraction of each cell (see
`Selected.lean`).  The conditional-marginal form divides by `M`, which is
positive, and is stated separately.

⚠️ The total-variation constant is the corrected one.  `tv_closure` is where
`2b·loss(1+η) + M·η ≤ ζM` is checked, `M·η` included — the paper drops that
term by treating `x|_A` as normalized although `x(A) ∈ [1−η, 1+η]`.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The rectangular pair-cell identity -/

omit [Fintype ι] in
open Classical in
/-- A rectangle of pair cells is exactly a four-count event. -/
theorem sum_rect_cell_indicator {A B X Y : Finset ι} (hX : X ⊆ A) (hY : Y ⊆ B)
    (c : ℝ) (T : Finset ι) :
    ∑ e ∈ X, ∑ f ∈ Y, (if PairCell A B e f T then c else 0)
      = if ((T ∩ X).card = 1 ∧ (T ∩ Y).card = 1 ∧ (T ∩ A).card = 1
          ∧ (T ∩ B).card = 1) then c else 0 := by
  classical
  by_cases h : (T ∩ X).card = 1 ∧ (T ∩ Y).card = 1 ∧ (T ∩ A).card = 1
      ∧ (T ∩ B).card = 1
  · rw [if_pos h]
    obtain ⟨e, heX⟩ := Finset.card_eq_one.mp h.1
    obtain ⟨f, hfY⟩ := Finset.card_eq_one.mp h.2.1
    have heTX : e ∈ T ∩ X := by rw [heX]; exact Finset.mem_singleton_self e
    have hfTY : f ∈ T ∩ Y := by rw [hfY]; exact Finset.mem_singleton_self f
    have heXmem : e ∈ X := (Finset.mem_inter.mp heTX).2
    have hfYmem : f ∈ Y := (Finset.mem_inter.mp hfTY).2
    have heA : T ∩ A = {e} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro a ha
        rw [Finset.mem_singleton] at ha
        subst ha
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp heTX).1, hX heXmem⟩
      · rw [h.2.2.1, Finset.card_singleton]
    have hfB : T ∩ B = {f} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro a ha
        rw [Finset.mem_singleton] at ha
        subst ha
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hfTY).1, hY hfYmem⟩
      · rw [h.2.2.2, Finset.card_singleton]
    have hcell : PairCell A B e f T := ⟨heA, hfB⟩
    rw [Finset.sum_eq_single_of_mem e heXmem
      (fun a _ ha => Finset.sum_eq_zero fun g _ =>
        if_neg fun hc => ha (pairCell_unique hc hcell).1),
      Finset.sum_eq_single_of_mem f hfYmem
      (fun g _ hg => if_neg fun hc => hg (pairCell_unique hc hcell).2),
      if_pos hcell]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun e he => Finset.sum_eq_zero fun f hf => ?_
    refine if_neg fun hcell => h ⟨?_, ?_, ?_, ?_⟩
    · have hsub : T ∩ X ⊆ {e} := by
        rw [← hcell.1]
        exact Finset.inter_subset_inter (Finset.Subset.refl T) hX
      have hmem : e ∈ T ∩ X :=
        Finset.mem_inter.mpr ⟨mem_of_pairCell hcell, he⟩
      rw [Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem),
        Finset.card_singleton]
    · have hsub : T ∩ Y ⊆ {f} := by
        rw [← hcell.2]
        exact Finset.inter_subset_inter (Finset.Subset.refl T) hY
      have hmem : f ∈ T ∩ Y :=
        Finset.mem_inter.mpr ⟨mem_of_pairCell_right hcell, hf⟩
      rw [Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem),
        Finset.card_singleton]
    · rw [hcell.1, Finset.card_singleton]
    · rw [hcell.2, Finset.card_singleton]

/-- **The rectangle of pair-cell masses is the four-count mass.** -/
theorem sum_pairCellMass_rect (w : Finset ι → ℝ) {A B X Y : Finset ι}
    (hX : X ⊆ A) (hY : Y ⊆ B) :
    ∑ e ∈ X, ∑ f ∈ Y, pairCellMass w A B e f
      = weightMass w (fun T => (T ∩ X).card = 1 ∧ (T ∩ Y).card = 1
          ∧ (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) := by
  classical
  have hexp : ∀ e ∈ X, ∀ f ∈ Y, pairCellMass w A B e f
      = ∑ T : Finset ι, (if PairCell A B e f T then w T else 0) :=
    fun e _ f _ => rfl
  rw [Finset.sum_congr rfl (fun e he =>
    Finset.sum_congr rfl (fun f hf => hexp e he f hf))]
  rw [Finset.sum_congr rfl (fun e _ => Finset.sum_comm), Finset.sum_comm,
    weightMass]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sum_rect_cell_indicator hX hY (w T) T]
  by_cases hc : ((T ∩ X).card = 1 ∧ (T ∩ Y).card = 1 ∧ (T ∩ A).card = 1
      ∧ (T ∩ B).card = 1)
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

/-! ### The numeric closure -/

omit [Fintype ι] [DecidableEq ι] in
/-- **`2b·loss(1+η) + M·η ≤ ζM`**, with `M = b·keep`.  The corrected
constant closes, including the `M·η` term the paper drops. -/
theorem tv_closure {η ζ b : ℝ} (hη0 : 0 ≤ η) (hζη : 330 * η < ζ)
    (hζ : ζ < 0.003) (hb : 0 ≤ b) :
    2 * b * (η + ζ / 2.1) * (1 + η) + b * (1 - η - ζ / 2.1) * η
      ≤ ζ * (b * (1 - η - ζ / 2.1)) := by
  have hζ0 : 0 < ζ := by linarith
  have hdiv : ζ / 2.1 = ζ * (10 / 21) := by ring
  rw [hdiv]
  -- the scalar inequality, then scale by `b ≥ 0`
  have key : 2 * (η + ζ * (10 / 21)) * (1 + η) + (1 - η - ζ * (10 / 21)) * η
      ≤ ζ * (1 - η - ζ * (10 / 21)) := by
    have p1 : 330 * (η * η) ≤ ζ * η := by nlinarith
    have p2 : 330 * (ζ * η) ≤ ζ * ζ := by nlinarith
    have p3 : ζ * ζ ≤ 0.003 * ζ := by nlinarith
    nlinarith [p1, p2, p3, hζη, hη0, hζ0]
  nlinarith [key, hb]

/-! ### Proposition 5.6 -/

/-- **KKO21 Proposition 5.6.**  A selected subweight of mass
`M = 0.11(0.473ζ)²(1 − η − ζ/2.1)`, supported on trees meeting each of `A`
and `B` exactly once, whose `A`- and `B`-marginals are within total
variation `ζM` of `M · x`. -/
theorem prop_5_6 {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B)
    {η ζ : ℝ} (hη0 : 0 ≤ η) (hζη : 330 * η < ζ) (hζ : ζ < 0.003)
    (hAup : expCard w A ≤ 1 + η) (hBup : expCard w B ≤ 1 + η)
    (hAlow : 1 - η ≤ expCard w A) (hBlow : 1 - η ≤ expCard w B) :
    ∃ v : Finset ι → ℝ, IsSelectedWeight w v
      ∧ (∀ T, v T ≠ 0 → (T ∩ A).card = 1 ∧ (T ∩ B).card = 1)
      ∧ totalMass v = 0.11 * (0.473 * ζ) ^ 2 * (1 - η - ζ / 2.1)
      ∧ (∑ e ∈ A, |weightMass v (fun T => e ∈ T)
          - totalMass v * weightMass w (fun T => e ∈ T)| ≤ ζ * totalMass v)
      ∧ (∑ f ∈ B, |weightMass v (fun T => f ∈ T)
          - totalMass v * weightMass w (fun T => f ∈ T)| ≤ ζ * totalMass v)
      ∧ ∃ z : ↥A → ↥B → ℝ, v = selectedWeight w A B z := by
  classical
  set x : ι → ℝ := fun e => weightMass w (fun T => e ∈ T) with hxdef
  set b : ℝ := 0.11 * (0.473 * ζ) ^ 2 with hbdef
  set keep : ℝ := 1 - η - ζ / 2.1 with hkeepdef
  have hζ0 : 0 < ζ := by linarith
  have hb0 : 0 < b := by
    rw [hbdef]
    positivity
  have hkeep0 : 0 < keep := by
    rw [hkeepdef]
    have : ζ / 2.1 = ζ * (10 / 21) := by ring
    rw [this]
    nlinarith
  have hx0 : ∀ e, 0 ≤ x e := fun e => weightMass_nonneg hnn _
  have hxA : ∑ e ∈ A, x e = expCard w A := (expCard_eq_sum_marginal w A).symm
  have hxB : ∑ f ∈ B, x f = expCard w B := (expCard_eq_sum_marginal w B).symm
  -- the cut condition
  have hcut : ∀ (SA : Finset ↥A) (SB : Finset ↥B),
      b * keep ≤ cutCap (α := ↥A) (β := ↥B)
        (fun (e : ↥A) (f : ↥B) => pairCellMass w A B ↑e ↑f)
        (fun (e : ↥A) => b * x ↑e) (fun (f : ↥B) => b * x ↑f) SA SB := by
    intro SA SB
    set X : Finset ι := SA.map (Function.Embedding.subtype _) with hXdef
    set Y : Finset ι := SB.map (Function.Embedding.subtype _) with hYdef
    have hXA : X ⊆ A := by
      intro a ha
      obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp ha
      exact e.2
    have hYB : Y ⊆ B := by
      intro a ha
      obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp ha
      exact f.2
    have c1 : ∑ e ∈ SAᶜ, b * x ↑e = b * ∑ a ∈ A \ X, x a := by
      rw [← Finset.mul_sum, sum_compl_subtype]
    have c2 : ∑ f ∈ SB, b * x ↑f = b * ∑ a ∈ Y, x a := by
      rw [← Finset.mul_sum, hYdef, Finset.sum_map]
      rfl
    have c3 : ∑ e ∈ SA, ∑ f ∈ SBᶜ, pairCellMass w A B ↑e ↑f
        = ∑ a ∈ X, ∑ c ∈ B \ Y, pairCellMass w A B a c := by
      rw [hXdef, Finset.sum_map]
      exact Finset.sum_congr rfl fun e _ => sum_compl_subtype B SB _
    rw [cutCap, c1, c2, c3]
    -- split off the outer arcs
    have hxAX : ∑ a ∈ A \ X, x a = (∑ a ∈ A, x a) - ∑ a ∈ X, x a :=
      Finset.sum_sdiff_eq_sub hXA
    have hxBY : ∑ a ∈ B \ Y, x a = (∑ a ∈ B, x a) - ∑ a ∈ Y, x a :=
      Finset.sum_sdiff_eq_sub hYB
    have hJ0 : 0 ≤ ∑ a ∈ X, ∑ c ∈ B \ Y, pairCellMass w A B a c :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ =>
        weightMass_nonneg hnn _
    set γ : ℝ := (∑ a ∈ X, x a) - ∑ a ∈ Y, x a with hγdef
    rcases le_or_gt γ (ζ / 2.1) with hsmall | hbig
    · -- the outer arcs already pay for the cut
      have : b * keep ≤ b * (∑ a ∈ A \ X, x a) + b * ∑ a ∈ Y, x a := by
        rw [hxAX, hkeepdef]
        have hxsum : 1 - η ≤ ∑ a ∈ A, x a := by rw [hxA]; exact hAlow
        nlinarith [hb0, hsmall, hxsum]
      linarith [hJ0]
    · -- `cut_repair` pays for the middle
      have hγ1 : γ ≤ 1 + η := by
        have h1 : ∑ a ∈ X, x a ≤ ∑ a ∈ A, x a :=
          Finset.sum_le_sum_of_subset_of_nonneg hXA fun a _ _ => hx0 a
        have h2 : 0 ≤ ∑ a ∈ Y, x a := Finset.sum_nonneg fun a _ => hx0 a
        rw [hγdef, hxA] at *
        linarith
      have hunion : 1 - η + γ ≤ expCard w (X ∪ (B \ Y)) := by
        have hdisj : Disjoint X (B \ Y) :=
          Finset.disjoint_left.mpr fun a ha hb =>
            Finset.disjoint_left.mp hAB (hXA ha) (Finset.mem_sdiff.mp hb).1
        rw [expCard_union_of_disjoint w hdisj]
        have h1 : expCard w X = ∑ a ∈ X, x a := expCard_eq_sum_marginal w X
        have h2 : expCard w (B \ Y) = ∑ a ∈ B \ Y, x a :=
          expCard_eq_sum_marginal w (B \ Y)
        have hxsumB : 1 - η ≤ ∑ a ∈ B, x a := by rw [hxB]; exact hBlow
        rw [h1, h2, hxBY, hγdef]
        linarith
      have hrep := cut_repair hst hr hnn htot hAB hXA (Y := Y) hη0 hζη hζ
        hbig hγ1 hAup hBup hunion
      have hrect := sum_pairCellMass_rect w hXA (Finset.sdiff_subset (s := B) (t := Y))
      rw [← hrect, ← hbdef] at hrep
      have houter : b * (∑ a ∈ A \ X, x a) + b * (∑ a ∈ Y, x a)
          = b * ((∑ a ∈ A, x a) - γ) := by
        rw [hxAX, hγdef]
        ring
      have hxsum : 1 - η ≤ ∑ a ∈ A, x a := by rw [hxA]; exact hAlow
      rw [houter, hkeepdef]
      nlinarith [hrep, hb0, hxsum]
  -- the flow
  obtain ⟨z, hzflow, hztot⟩ :=
    exists_flow_of_cut (α := ↥A) (β := ↥B)
      (y := fun (e : ↥A) (f : ↥B) => pairCellMass w A B ↑e ↑f)
      (cA := fun (e : ↥A) => b * x ↑e) (cB := fun (f : ↥B) => b * x ↑f)
      (τ := b * keep)
      (fun e f => weightMass_nonneg hnn _)
      (fun e => mul_nonneg hb0.le (hx0 _))
      (fun f => mul_nonneg hb0.le (hx0 _))
      (mul_nonneg hb0.le hkeep0.le) hcut
  -- the selection
  refine ⟨selectedWeight w A B z, isSelectedWeight_selectedWeight hnn
    (fun e f => hzflow.le_cap e f) (fun e f => hzflow.nonneg e f),
    fun T hT => card_eq_one_of_selected hT, ?_, ?_, ?_, ⟨z, rfl⟩⟩
  · rw [totalMass_selectedWeight (fun e f => hzflow.le_cap e f)
      (fun e f => hzflow.nonneg e f), hztot]
  · -- the `A`-marginals
    have hMv : totalMass (selectedWeight w A B z) = b * keep := by
      rw [totalMass_selectedWeight (fun e f => hzflow.le_cap e f)
        (fun e f => hzflow.nonneg e f), hztot]
    rw [hMv]
    refine le_trans (marginal_deviation_le A
      (fun e => weightMass (selectedWeight w A B z) (fun T => e ∈ T)) x
      (b := b) (loss := η + ζ / 2.1) hb0.le (by positivity) (fun e _ => hx0 e)
      (by rw [hxA]; exact hAup) ?_ (by rw [hkeepdef]; ring_nf; linarith) ?_) ?_
    · intro e he
      have := weightMass_mem_selected_left (w := w) (A := A) (B := B) (z := z)
        (fun e f => hzflow.le_cap e f) (fun e f => hzflow.nonneg e f) ⟨e, he⟩
      rw [this]
      exact hzflow.row ⟨e, he⟩
    · rw [← Finset.sum_coe_sort A
        (fun e => weightMass (selectedWeight w A B z) (fun T => e ∈ T))]
      rw [Finset.sum_congr rfl (fun e _ => weightMass_mem_selected_left
        (fun e f => hzflow.le_cap e f) (fun e f => hzflow.nonneg e f) e)]
      exact hztot
    · exact tv_closure hη0 hζη hζ hb0.le
  · -- the `B`-marginals
    have hMv : totalMass (selectedWeight w A B z) = b * keep := by
      rw [totalMass_selectedWeight (fun e f => hzflow.le_cap e f)
        (fun e f => hzflow.nonneg e f), hztot]
    rw [hMv]
    refine le_trans (marginal_deviation_le B
      (fun f => weightMass (selectedWeight w A B z) (fun T => f ∈ T)) x
      (b := b) (loss := η + ζ / 2.1) hb0.le (by positivity) (fun f _ => hx0 f)
      (by rw [hxB]; exact hBup) ?_ (by rw [hkeepdef]; ring_nf; linarith) ?_) ?_
    · intro f hf
      have := weightMass_mem_selected_right (w := w) (A := A) (B := B) (z := z)
        (fun e f => hzflow.le_cap e f) (fun e f => hzflow.nonneg e f) ⟨f, hf⟩
      rw [this]
      exact hzflow.col ⟨f, hf⟩
    · rw [← Finset.sum_coe_sort B
        (fun f => weightMass (selectedWeight w A B z) (fun T => f ∈ T))]
      rw [Finset.sum_congr rfl (fun f _ => weightMass_mem_selected_right
        (fun e f => hzflow.le_cap e f) (fun e f => hzflow.nonneg e f) f)]
      exact (flowTotal_eq_col z).symm.trans hztot
    · exact tv_closure hη0 hζη hζ hb0.le

/-- **The conditional form.**  Dividing by the (positive) selected mass, the
selected marginals are within total variation `ζ` of `x`.  This is the shape
the paper states; the subweight form above is the one that is actually
constructed.  The exact mass is retained, so this wrapper alone carries both
the probability lower bound and the conditional marginals. -/
theorem prop_5_6_conditional {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B)
    {η ζ : ℝ} (hη0 : 0 ≤ η) (hζη : 330 * η < ζ) (hζ : ζ < 0.003)
    (hAup : expCard w A ≤ 1 + η) (hBup : expCard w B ≤ 1 + η)
    (hAlow : 1 - η ≤ expCard w A) (hBlow : 1 - η ≤ expCard w B) :
    ∃ v : Finset ι → ℝ, IsSelectedWeight w v ∧ 0 < totalMass v
      ∧ totalMass v = 0.11 * (0.473 * ζ) ^ 2 * (1 - η - ζ / 2.1)
      ∧ (∀ T, v T ≠ 0 → (T ∩ A).card = 1 ∧ (T ∩ B).card = 1)
      ∧ (∑ e ∈ A, |weightMass v (fun T => e ∈ T) / totalMass v
          - weightMass w (fun T => e ∈ T)| ≤ ζ)
      ∧ (∑ f ∈ B, |weightMass v (fun T => f ∈ T) / totalMass v
          - weightMass w (fun T => f ∈ T)| ≤ ζ) := by
  obtain ⟨v, hsel, hsupp, hmass, hA, hB, -⟩ :=
    prop_5_6 hst hr hnn htot hAB hη0 hζη hζ hAup hBup hAlow hBlow
  have hζ0 : 0 < ζ := by linarith
  have hM0 : 0 < totalMass v := by
    rw [hmass]
    have hkeep : (0:ℝ) < 1 - η - ζ / 2.1 := by
      have hdiv : ζ / 2.1 = ζ * (10 / 21) := by ring
      rw [hdiv]
      nlinarith
    positivity
  refine ⟨v, hsel, hM0, hmass, hsupp, ?_, ?_⟩
  · have hdiv : ∀ e : ι, |weightMass v (fun T => e ∈ T) / totalMass v
        - weightMass w (fun T => e ∈ T)|
        = |weightMass v (fun T => e ∈ T)
          - totalMass v * weightMass w (fun T => e ∈ T)| / totalMass v := by
      intro e
      rw [← abs_of_pos hM0, ← abs_div, abs_of_pos hM0]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl (fun e _ => hdiv e), ← Finset.sum_div,
      div_le_iff₀ hM0]
    calc ∑ e ∈ A, |weightMass v (fun T => e ∈ T)
            - totalMass v * weightMass w (fun T => e ∈ T)|
        ≤ ζ * totalMass v := hA
      _ = ζ * totalMass v := rfl
  · have hdiv : ∀ f : ι, |weightMass v (fun T => f ∈ T) / totalMass v
        - weightMass w (fun T => f ∈ T)|
        = |weightMass v (fun T => f ∈ T)
          - totalMass v * weightMass w (fun T => f ∈ T)| / totalMass v := by
      intro f
      rw [← abs_of_pos hM0, ← abs_div, abs_of_pos hM0]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl (fun f _ => hdiv f), ← Finset.sum_div,
      div_le_iff₀ hM0]
    exact hB

end TSPGap

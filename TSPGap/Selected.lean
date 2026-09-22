/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Flow
import TSPGap.Conditioning

/-!
# Selected subweights and the pair-cell construction

Proposition 5.6 turns a flow `z` into an "event" by taking, for each pair
`(e, f)`, a `z e f` fraction of the trees `T` with `T ∩ A = {e}` and
`T ∩ B = {f}`.  ⚠️ That is *not* an event: an arbitrary real fraction of a
cell is not a set of trees.  What it is, is a **subweight** — a nonnegative
`v ≤ w` — and that is what this file constructs.

* `IsSelectedWeight w v` — `v` is nonnegative and pointwise below `w`.
* `PairCell A B e f` — the cell `T ∩ A = {e}`, `T ∩ B = {f}`; the cells are
  pairwise disjoint (`pairCell_unique`), which is what makes the whole
  construction a *sum* over cells rather than a choice of one.
* `selectedWeight w A B z` — the construction: scale the cell `(e, f)` from
  its mass `pairCellMass` down to `z e f`.  ⚠️ On a cell of mass zero the
  hypothesis `z e f ≤ pairCellMass` forces `z e f = 0`, and the division
  `z / 0 = 0` gives the right answer for the right reason; the zero branch
  is derived, never assumed.
* The exact outputs: cell masses, total mass `flowTotal z`, `A`- and
  `B`-marginals as row and column sums, support in trees meeting each of
  `A`, `B` exactly once, and inheritance of fixed rank and of `w`'s support.
* `marginal_deviation_le` — the arithmetic of the total-variation estimate,
  with `keep` and `loss` named.  ⚠️ It needs only `∑ x ≤ 1 + η`; neither a
  lower bound on `∑ x` nor nonnegativity of the selected marginals enters,
  and the `M·η` term is the one the paper drops by treating `x|_A` as
  normalized.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Selections and pair cells -/

/-- `v` is a selection from `w`: nonnegative and pointwise below it. -/
def IsSelectedWeight (w v : Finset ι → ℝ) : Prop :=
  WeightNonneg v ∧ ∀ T, v T ≤ w T

/-- The pair cell of `(e, f)`: trees meeting `A` exactly in `e` and `B`
exactly in `f`. -/
def PairCell (A B : Finset ι) (e f : ι) (T : Finset ι) : Prop :=
  T ∩ A = {e} ∧ T ∩ B = {f}

/-- The mass of a pair cell. -/
noncomputable def pairCellMass (w : Finset ι → ℝ) (A B : Finset ι) (e f : ι) : ℝ :=
  weightMass w (PairCell A B e f)

omit [Fintype ι] in
/-- **The cells are disjoint.**  A tree lies in at most one of them, which
is why the construction can sum over all cells instead of selecting one. -/
theorem pairCell_unique {A B : Finset ι} {e e' f f' : ι} {T : Finset ι}
    (h : PairCell A B e f T) (h' : PairCell A B e' f' T) : e = e' ∧ f = f' :=
  ⟨Finset.singleton_inj.mp (h.1.symm.trans h'.1),
    Finset.singleton_inj.mp (h.2.symm.trans h'.2)⟩

omit [Fintype ι] in
theorem mem_of_pairCell {A B : Finset ι} {e f : ι} {T : Finset ι}
    (h : PairCell A B e f T) : e ∈ T := by
  have : e ∈ T ∩ A := by rw [h.1]; exact Finset.mem_singleton_self e
  exact (Finset.mem_inter.mp this).1

omit [Fintype ι] in
theorem mem_of_pairCell_right {A B : Finset ι} {e f : ι} {T : Finset ι}
    (h : PairCell A B e f T) : f ∈ T := by
  have : f ∈ T ∩ B := by rw [h.2]; exact Finset.mem_singleton_self f
  exact (Finset.mem_inter.mp this).1

/-! ### The construction -/

open Classical in
/-- Scale each pair cell from its own mass down to `z e f`. -/
noncomputable def selectedWeight (w : Finset ι → ℝ) (A B : Finset ι)
    (z : ↥A → ↥B → ℝ) : Finset ι → ℝ := fun T =>
  ∑ e : ↥A, ∑ f : ↥B,
    (if PairCell A B ↑e ↑f T then z e f / pairCellMass w A B ↑e ↑f * w T else 0)

theorem selectedWeight_of_cell {w : Finset ι → ℝ} {A B : Finset ι}
    (z : ↥A → ↥B → ℝ) {T : Finset ι} {e₀ : ↥A} {f₀ : ↥B}
    (h : PairCell A B ↑e₀ ↑f₀ T) :
    selectedWeight w A B z T
      = z e₀ f₀ / pairCellMass w A B ↑e₀ ↑f₀ * w T := by
  classical
  rw [selectedWeight, Finset.sum_eq_single_of_mem e₀ (Finset.mem_univ e₀)
    (fun e _ he => Finset.sum_eq_zero fun f _ =>
      if_neg fun hc => he (Subtype.ext (pairCell_unique hc h).1)),
    Finset.sum_eq_single_of_mem f₀ (Finset.mem_univ f₀)
    (fun f _ hf => if_neg fun hc => hf (Subtype.ext (pairCell_unique hc h).2)),
    if_pos h]

theorem selectedWeight_of_not_cell {w : Finset ι → ℝ} {A B : Finset ι}
    (z : ↥A → ↥B → ℝ) {T : Finset ι}
    (h : ∀ (e : ↥A) (f : ↥B), ¬ PairCell A B ↑e ↑f T) :
    selectedWeight w A B z T = 0 := by
  classical
  rw [selectedWeight]
  exact Finset.sum_eq_zero fun e _ =>
    Finset.sum_eq_zero fun f _ => if_neg (h e f)

/-- **The master mass identity**: any event's selected mass splits over the
cells. -/
theorem weightMass_selectedWeight (w : Finset ι → ℝ) (A B : Finset ι)
    (z : ↥A → ↥B → ℝ) (P : Finset ι → Prop) :
    weightMass (selectedWeight w A B z) P
      = ∑ e : ↥A, ∑ f : ↥B, z e f / pairCellMass w A B ↑e ↑f
          * weightMass w (fun T => P T ∧ PairCell A B ↑e ↑f T) := by
  classical
  have hstep : ∀ T : Finset ι, (if P T then selectedWeight w A B z T else 0)
      = ∑ e : ↥A, ∑ f : ↥B, (if P T ∧ PairCell A B ↑e ↑f T then
          z e f / pairCellMass w A B ↑e ↑f * w T else 0) := by
    intro T
    by_cases hP : P T
    · rw [if_pos hP, selectedWeight]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
      by_cases hc : PairCell A B ↑e ↑f T
      · rw [if_pos hc, if_pos ⟨hP, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · rw [if_neg hP]
      exact (Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun f _ =>
        if_neg fun h => hP h.1).symm
  rw [weightMass, Finset.sum_congr rfl (fun T _ => hstep T), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [weightMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hc : P T ∧ PairCell A B ↑e ↑f T
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-! ### The exact outputs -/

variable {w : Finset ι → ℝ} {A B : Finset ι} {z : ↥A → ↥B → ℝ}

/-- The scaling factor times the cell mass returns the flow value — with the
zero-mass branch *derived* from `z ≤ pairCellMass`. -/
theorem scale_mul_cellMass (hzle : ∀ e f, z e f ≤ pairCellMass w A B ↑e ↑f)
    (hz0 : ∀ e f, 0 ≤ z e f) (e : ↥A) (f : ↥B) :
    z e f / pairCellMass w A B ↑e ↑f * pairCellMass w A B ↑e ↑f = z e f := by
  rcases eq_or_ne (pairCellMass w A B ↑e ↑f) 0 with h0 | h0
  · have : z e f = 0 := le_antisymm (h0 ▸ hzle e f) (hz0 e f)
    rw [h0, this]
    simp
  · rw [div_mul_cancel₀ _ h0]

/-- **Each selected cell has mass `z e f`.** -/
theorem weightMass_pairCell_selected
    (hzle : ∀ e f, z e f ≤ pairCellMass w A B ↑e ↑f) (hz0 : ∀ e f, 0 ≤ z e f)
    (e₀ : ↥A) (f₀ : ↥B) :
    weightMass (selectedWeight w A B z) (PairCell A B ↑e₀ ↑f₀) = z e₀ f₀ := by
  classical
  rw [weightMass_selectedWeight]
  rw [Finset.sum_eq_single_of_mem e₀ (Finset.mem_univ e₀) ?_,
    Finset.sum_eq_single_of_mem f₀ (Finset.mem_univ f₀) ?_]
  · have hself : weightMass w (fun T => PairCell A B ↑e₀ ↑f₀ T
        ∧ PairCell A B ↑e₀ ↑f₀ T) = pairCellMass w A B ↑e₀ ↑f₀ :=
      weightMass_congr fun T => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
    rw [hself, scale_mul_cellMass hzle hz0]
  · intro f _ hf
    have : weightMass w (fun T => PairCell A B ↑e₀ ↑f₀ T
        ∧ PairCell A B ↑e₀ ↑f T) = weightMass w (fun _ : Finset ι => False) :=
      weightMass_congr fun T => ⟨fun h =>
        hf (Subtype.ext (pairCell_unique h.2 h.1).2), fun h => h.elim⟩
    rw [this, weightMass_false, mul_zero]
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    have : weightMass w (fun T => PairCell A B ↑e₀ ↑f₀ T
        ∧ PairCell A B ↑e ↑f T) = weightMass w (fun _ : Finset ι => False) :=
      weightMass_congr fun T => ⟨fun h =>
        he (Subtype.ext (pairCell_unique h.2 h.1).1), fun h => h.elim⟩
    rw [this, weightMass_false, mul_zero]

/-- **The total selected mass is the value of the flow.** -/
theorem totalMass_selectedWeight
    (hzle : ∀ e f, z e f ≤ pairCellMass w A B ↑e ↑f) (hz0 : ∀ e f, 0 ≤ z e f) :
    totalMass (selectedWeight w A B z) = flowTotal z := by
  classical
  have hall : totalMass (selectedWeight w A B z)
      = weightMass (selectedWeight w A B z) (fun _ => True) := by
    rw [totalMass, weightMass]
    exact Finset.sum_congr rfl fun T _ => (if_pos trivial).symm
  rw [hall, weightMass_selectedWeight, flowTotal]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have : weightMass w (fun T => True ∧ PairCell A B ↑e ↑f T)
      = pairCellMass w A B ↑e ↑f :=
    weightMass_congr fun T => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [this, scale_mul_cellMass hzle hz0]

/-- **The `A`-marginals are the row sums.** -/
theorem weightMass_mem_selected_left
    (hzle : ∀ e f, z e f ≤ pairCellMass w A B ↑e ↑f) (hz0 : ∀ e f, 0 ≤ z e f)
    (e₀ : ↥A) :
    weightMass (selectedWeight w A B z) (fun T => (↑e₀ : ι) ∈ T)
      = ∑ f, z e₀ f := by
  classical
  rw [weightMass_selectedWeight]
  rw [Finset.sum_eq_single_of_mem e₀ (Finset.mem_univ e₀) ?_]
  · refine Finset.sum_congr rfl fun f _ => ?_
    have : weightMass w (fun T => (↑e₀ : ι) ∈ T ∧ PairCell A B ↑e₀ ↑f T)
        = pairCellMass w A B ↑e₀ ↑f :=
      weightMass_congr fun T =>
        ⟨fun h => h.2, fun h => ⟨mem_of_pairCell h, h⟩⟩
    rw [this, scale_mul_cellMass hzle hz0]
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    have : weightMass w (fun T => (↑e₀ : ι) ∈ T ∧ PairCell A B ↑e ↑f T)
        = weightMass w (fun _ : Finset ι => False) := by
      refine weightMass_congr fun T => ⟨fun h => ?_, fun h => h.elim⟩
      refine he (Subtype.ext ?_).symm
      have hmem : (↑e₀ : ι) ∈ T ∩ A :=
        Finset.mem_inter.mpr ⟨h.1, e₀.2⟩
      rw [h.2.1] at hmem
      exact (Finset.mem_singleton.mp hmem)
    rw [this, weightMass_false, mul_zero]

/-- **The `B`-marginals are the column sums.** -/
theorem weightMass_mem_selected_right
    (hzle : ∀ e f, z e f ≤ pairCellMass w A B ↑e ↑f) (hz0 : ∀ e f, 0 ≤ z e f)
    (f₀ : ↥B) :
    weightMass (selectedWeight w A B z) (fun T => (↑f₀ : ι) ∈ T)
      = ∑ e, z e f₀ := by
  classical
  rw [weightMass_selectedWeight]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single_of_mem f₀ (Finset.mem_univ f₀) ?_]
  · have : weightMass w (fun T => (↑f₀ : ι) ∈ T ∧ PairCell A B ↑e ↑f₀ T)
        = pairCellMass w A B ↑e ↑f₀ :=
      weightMass_congr fun T =>
        ⟨fun h => h.2, fun h => ⟨mem_of_pairCell_right h, h⟩⟩
    rw [this, scale_mul_cellMass hzle hz0]
  · intro f _ hf
    have : weightMass w (fun T => (↑f₀ : ι) ∈ T ∧ PairCell A B ↑e ↑f T)
        = weightMass w (fun _ : Finset ι => False) := by
      refine weightMass_congr fun T => ⟨fun h => ?_, fun h => h.elim⟩
      refine hf (Subtype.ext ?_).symm
      have hmem : (↑f₀ : ι) ∈ T ∩ B :=
        Finset.mem_inter.mpr ⟨h.1, f₀.2⟩
      rw [h.2.2] at hmem
      exact (Finset.mem_singleton.mp hmem)
    rw [this, weightMass_false, mul_zero]

/-! ### Structural inheritance -/

/-- The selection is supported on trees meeting `A` and `B` exactly once. -/
theorem card_eq_one_of_selected (hT : selectedWeight w A B z T ≠ 0) :
    (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 := by
  classical
  by_contra hc
  refine hT (selectedWeight_of_not_cell z fun e f hcell => ?_)
  exact hc ⟨by rw [hcell.1, Finset.card_singleton],
    by rw [hcell.2, Finset.card_singleton]⟩

/-- The selection lives on `w`'s support. -/
theorem support_selected (hT : selectedWeight w A B z T ≠ 0) : w T ≠ 0 := by
  classical
  intro h0
  refine hT ?_
  by_cases hc : ∀ (e : ↥A) (f : ↥B), ¬ PairCell A B ↑e ↑f T
  · exact selectedWeight_of_not_cell z hc
  · obtain ⟨e, he⟩ := not_forall.mp hc
    obtain ⟨f, hf⟩ := not_forall.mp he
    rw [selectedWeight_of_cell z (not_not.mp hf), h0, mul_zero]

theorem fixedRankWeight_selected {r : ℕ} (hr : FixedRankWeight r w) :
    FixedRankWeight r (selectedWeight w A B z) :=
  fun T hT => hr T (support_selected hT)

/-- **The construction is a selection.** -/
theorem isSelectedWeight_selectedWeight (hnn : WeightNonneg w)
    (hzle : ∀ e f, z e f ≤ pairCellMass w A B ↑e ↑f) (hz0 : ∀ e f, 0 ≤ z e f) :
    IsSelectedWeight w (selectedWeight w A B z) := by
  classical
  have hcell : ∀ (e : ↥A) (f : ↥B), 0 ≤ pairCellMass w A B ↑e ↑f :=
    fun e f => weightMass_nonneg hnn _
  constructor
  · intro T
    by_cases hc : ∀ (e : ↥A) (f : ↥B), ¬ PairCell A B ↑e ↑f T
    · rw [selectedWeight_of_not_cell z hc]
    · obtain ⟨e, he⟩ := not_forall.mp hc
      obtain ⟨f, hf⟩ := not_forall.mp he
      rw [selectedWeight_of_cell z (not_not.mp hf)]
      exact mul_nonneg (div_nonneg (hz0 e f) (hcell e f)) (hnn T)
  · intro T
    by_cases hc : ∀ (e : ↥A) (f : ↥B), ¬ PairCell A B ↑e ↑f T
    · rw [selectedWeight_of_not_cell z hc]
      exact hnn T
    · obtain ⟨e, he⟩ := not_forall.mp hc
      obtain ⟨f, hf⟩ := not_forall.mp he
      rw [selectedWeight_of_cell z (not_not.mp hf)]
      rcases eq_or_lt_of_le (hcell e f) with h0 | hpos
      · have hz : z e f = 0 := le_antisymm (h0 ▸ hzle e f) (hz0 e f)
        rw [hz, ← h0]
        simpa using hnn T
      · have hle1 : z e f / pairCellMass w A B ↑e ↑f ≤ 1 :=
          (div_le_one hpos).mpr (hzle e f)
        calc z e f / pairCellMass w A B ↑e ↑f * w T ≤ 1 * w T :=
              mul_le_mul_of_nonneg_right hle1 (hnn T)
          _ = w T := one_mul _

/-! ### The subtype/`Finset` bridge -/

omit [Fintype ι] in
theorem map_compl_subtype (A : Finset ι) (S : Finset ↥A) :
    (Sᶜ).map (Function.Embedding.subtype _)
      = A \ S.map (Function.Embedding.subtype _) := by
  classical
  ext a
  simp only [Finset.mem_map, Finset.mem_compl, Finset.mem_sdiff,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rintro ⟨y, hy, hya⟩
    have hyx : y = x := Subtype.ext hya
    subst hyx
    exact hx hy
  · rintro ⟨haA, hnot⟩
    exact ⟨⟨a, haA⟩, fun hc => hnot ⟨⟨a, haA⟩, hc, rfl⟩, rfl⟩

omit [Fintype ι] in
/-- A sum over the subtype complement is a sum over the `Finset`
difference. -/
theorem sum_compl_subtype (A : Finset ι) (S : Finset ↥A) (g : ι → ℝ) :
    ∑ e ∈ Sᶜ, g ↑e = ∑ a ∈ A \ S.map (Function.Embedding.subtype _), g a := by
  classical
  rw [← map_compl_subtype A S, Finset.sum_map]
  rfl

/-! ### The marginal estimate -/

omit [Fintype ι] [DecidableEq ι] in
/-- **The total-variation arithmetic.**  With `keep = 1 − η − ζ/2.1` and
`loss = η + ζ/2.1`, the selected mass is `M = b · keep` and the deviation of
the selected marginals from `M · x` is at most `2b·loss·(1+η) + M·η`.

⚠️ The final `M · η` is the term the paper drops by treating `x|_A` as
normalized.  Only `∑ x ≤ 1 + η` is used — no lower bound on `∑ x`, no
nonnegativity of the marginals `W`, and not even `0 ≤ M`: the combination
`2b·loss + M ≥ b(1 + loss) ≥ 0` that the estimate needs already follows from
`b − M ≤ b·loss`. -/
theorem marginal_deviation_le {κ : Type*} (A : Finset κ) (W x : κ → ℝ)
    {M b loss η : ℝ} (hb : 0 ≤ b) (hloss : 0 ≤ loss)
    (hx : ∀ e ∈ A, 0 ≤ x e) (hxsum : ∑ e ∈ A, x e ≤ 1 + η)
    (hWx : ∀ e ∈ A, W e ≤ b * x e) (hbM : b - M ≤ b * loss)
    (hWsum : ∑ e ∈ A, W e = M) :
    ∑ e ∈ A, |W e - M * x e| ≤ 2 * b * loss * (1 + η) + M * η := by
  have hpt : ∀ e ∈ A, |W e - M * x e|
      ≤ 2 * (b * loss * x e) - (W e - M * x e) := by
    intro e he
    have hxe := hx e he
    have h1 : W e - M * x e ≤ b * loss * x e := by
      nlinarith [hWx e he, hxe, hbM]
    have h2 : (0:ℝ) ≤ b * loss * x e := by positivity
    rcases abs_cases (W e - M * x e) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] <;>
      linarith
  have hsum : ∑ e ∈ A, (2 * (b * loss * x e) - (W e - M * x e))
      = 2 * (b * loss) * (∑ e ∈ A, x e) - (∑ e ∈ A, W e)
        + M * (∑ e ∈ A, x e) := by
    rw [Finset.sum_congr rfl (fun e _ => by ring :
      ∀ e ∈ A, 2 * (b * loss * x e) - (W e - M * x e)
        = 2 * (b * loss) * x e - W e + M * x e)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hbl : (0:ℝ) ≤ b * loss := mul_nonneg hb hloss
  calc ∑ e ∈ A, |W e - M * x e|
      ≤ ∑ e ∈ A, (2 * (b * loss * x e) - (W e - M * x e)) :=
        Finset.sum_le_sum hpt
    _ = 2 * (b * loss) * (∑ e ∈ A, x e) - (∑ e ∈ A, W e)
        + M * (∑ e ∈ A, x e) := hsum
    _ ≤ 2 * b * loss * (1 + η) + M * η := by
        rw [hWsum]
        nlinarith [hxsum, hbl, hbM, hb, hloss]

end TSPGap

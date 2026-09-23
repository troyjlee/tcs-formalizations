/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ExcludedCycles

/-!
# Near-minimum cuts contain no comb (BG08 Lemma 23)

BG08 Definition 2: four sets `H, T₁, T₂, T₃` form a *comb* with handle `H` and
teeth `T₁, T₂, T₃` if the handle meets the three teeth in three nonempty cells of
one of two forms — `H ∩ Tᵢ ∖ (Tᵢ₋₁ ∪ Tᵢ₊₁)` for all `i`, or `H ∩ (Tᵢ₋₁ ∩ Tᵢ₊₁ ∖ Tᵢ)`
for all `i` — and the same holds for the complement of the handle.  Combs are the
second obstruction to BG08's polygon representation (Theorem 4), next to
3-cycles.

BG08 Lemma 23: among `η`-near minimum cuts of a subtour-LP point with `η < 2/5`
there is no comb.  The proof is the edge count

`x(δ(T₁)) + x(δ(T₂)) + x(δ(T₃)) + 2x(δ(H)) ≥ ∑ᵢ x(δ(Cᵢ)) + ∑ᵢ x(δ(Dᵢ))`

for the three cells `Cᵢ ⊆ H` and `Dᵢ ⊆ Hᶜ` — checked on the memberships of the two
endpoints of an edge — and the LP bound `2` on each of the six nonempty proper
cells: `12 ≤ 5(2 + η)` forces `η ≥ 2/5`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- The three cells of a handle `H` against teeth `T₁, T₂, T₃`, in either of BG08
Definition 2's two forms. -/
def IsCombCells (H T₁ T₂ T₃ C₁ C₂ C₃ : Finset (Fin n)) : Prop :=
  (C₁ = (H ∩ T₁) \ (T₃ ∪ T₂) ∧ C₂ = (H ∩ T₂) \ (T₁ ∪ T₃) ∧ C₃ = (H ∩ T₃) \ (T₂ ∪ T₁))
    ∨ (C₁ = H ∩ ((T₃ ∩ T₂) \ T₁) ∧ C₂ = H ∩ ((T₁ ∩ T₃) \ T₂) ∧ C₃ = H ∩ ((T₂ ∩ T₁) \ T₃))

/-- **BG08 Definition 2**: `H, T₁, T₂, T₃` form a comb with handle `H`. -/
def IsComb (H T₁ T₂ T₃ : Finset (Fin n)) : Prop :=
  (∃ C₁ C₂ C₃, IsCombCells H T₁ T₂ T₃ C₁ C₂ C₃ ∧ C₁.Nonempty ∧ C₂.Nonempty ∧ C₃.Nonempty)
    ∧ (∃ D₁ D₂ D₃, IsCombCells Hᶜ T₁ T₂ T₃ D₁ D₂ D₃ ∧ D₁.Nonempty ∧ D₂.Nonempty ∧ D₃.Nonempty)

theorem IsCombCells.subset {H T₁ T₂ T₃ C₁ C₂ C₃ : Finset (Fin n)}
    (h : IsCombCells H T₁ T₂ T₃ C₁ C₂ C₃) : C₁ ⊆ H ∧ C₂ ⊆ H ∧ C₃ ⊆ H := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨Finset.sdiff_subset.trans Finset.inter_subset_left,
      Finset.sdiff_subset.trans Finset.inter_subset_left,
      Finset.sdiff_subset.trans Finset.inter_subset_left⟩
  · exact ⟨Finset.inter_subset_left, Finset.inter_subset_left, Finset.inter_subset_left⟩

set_option maxHeartbeats 4000000 in
-- four cell-form combinations, each a 256-case membership check
/-- Per edge: the comb count.  Both cell forms on each side of the handle. -/
theorem edge_count_comb {H T₁ T₂ T₃ C₁ C₂ C₃ D₁ D₂ D₃ : Finset (Fin n)}
    (hC : IsCombCells H T₁ T₂ T₃ C₁ C₂ C₃) (hD : IsCombCells Hᶜ T₁ T₂ T₃ D₁ D₂ D₃)
    (a b : Fin n) :
    cutInd C₁ s(a, b) + cutInd C₂ s(a, b) + cutInd C₃ s(a, b)
        + cutInd D₁ s(a, b) + cutInd D₂ s(a, b) + cutInd D₃ s(a, b)
      ≤ cutInd T₁ s(a, b) + cutInd T₂ s(a, b) + cutInd T₃ s(a, b) + 2 * cutInd H s(a, b) := by
  rcases hC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hD with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  simp only [cutInd_mk, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union,
    Finset.mem_compl] <;>
  by_cases h1 : a ∈ H <;> by_cases h2 : a ∈ T₁ <;> by_cases h3 : a ∈ T₂ <;> by_cases h4 : a ∈ T₃ <;>
    by_cases h5 : b ∈ H <;> by_cases h6 : b ∈ T₁ <;> by_cases h7 : b ∈ T₂ <;> by_cases h8 : b ∈ T₃ <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- **BG08's inequality (2)**: the comb count, summed with the LP weights. -/
theorem comb_cutSum_le (hx : ∀ e, 0 ≤ x e) {H T₁ T₂ T₃ C₁ C₂ C₃ D₁ D₂ D₃ : Finset (Fin n)}
    (hC : IsCombCells H T₁ T₂ T₃ C₁ C₂ C₃) (hD : IsCombCells Hᶜ T₁ T₂ T₃ D₁ D₂ D₃) :
    cutSum x C₁ + cutSum x C₂ + cutSum x C₃ + cutSum x D₁ + cutSum x D₂ + cutSum x D₃
      ≤ cutSum x T₁ + cutSum x T₂ + cutSum x T₃ + 2 * cutSum x H := by
  classical
  simp only [cutSum_eq_sum_cutInd, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have h := edge_count_comb hC hD
  induction e using Sym2.ind with
  | h a b =>
    have hab := h a b
    have hx' := hx s(a, b)
    have : (x s(a, b) * ((cutInd C₁ s(a, b) : ℕ) : ℝ) + x s(a, b) * ((cutInd C₂ s(a, b) : ℕ) : ℝ)
        + x s(a, b) * ((cutInd C₃ s(a, b) : ℕ) : ℝ) + x s(a, b) * ((cutInd D₁ s(a, b) : ℕ) : ℝ)
        + x s(a, b) * ((cutInd D₂ s(a, b) : ℕ) : ℝ) + x s(a, b) * ((cutInd D₃ s(a, b) : ℕ) : ℝ))
        = x s(a, b) * ((cutInd C₁ s(a, b) + cutInd C₂ s(a, b) + cutInd C₃ s(a, b)
          + cutInd D₁ s(a, b) + cutInd D₂ s(a, b) + cutInd D₃ s(a, b) : ℕ) : ℝ) := by
      push_cast; ring
    have that : (x s(a, b) * ((cutInd T₁ s(a, b) : ℕ) : ℝ) + x s(a, b) * ((cutInd T₂ s(a, b) : ℕ) : ℝ)
        + x s(a, b) * ((cutInd T₃ s(a, b) : ℕ) : ℝ) + 2 * (x s(a, b) * ((cutInd H s(a, b) : ℕ) : ℝ)))
        = x s(a, b) * ((cutInd T₁ s(a, b) + cutInd T₂ s(a, b) + cutInd T₃ s(a, b)
          + 2 * cutInd H s(a, b) : ℕ) : ℝ) := by
      push_cast; ring
    rw [this, that]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hx'

/-- **BG08 Lemma 23, proved.**  Among `η`-near minimum cuts of a subtour-LP point with
`η < 2/5` there is no comb. -/
theorem no_comb (hx : x ∈ subtourLP n) {η : ℝ} (hη : η < 2 / 5) {H T₁ T₂ T₃ : Finset (Fin n)}
    (hH : IsNearMinCut x η H) (h1 : IsNearMinCut x η T₁) (h2 : IsNearMinCut x η T₂)
    (h3 : IsNearMinCut x η T₃) : ¬ IsComb H T₁ T₂ T₃ := by
  rintro ⟨⟨C₁, C₂, C₃, hC, hC1, hC2, hC3⟩, ⟨D₁, D₂, D₃, hD, hD1, hD2, hD3⟩⟩
  have hx0 : ∀ e, 0 ≤ x e := hx.1
  have hsubC := hC.subset
  have hsubD := hD.subset
  have hHne : H ≠ Finset.univ := hH.ne_univ
  have hHcne : Hᶜ ≠ Finset.univ := by
    intro h
    obtain ⟨v, hv⟩ := hH.nonempty
    have : v ∈ Hᶜ := h ▸ Finset.mem_univ v
    exact (Finset.mem_compl.mp this) hv
  have hproper : ∀ {S : Finset (Fin n)}, S ⊆ H → S ≠ Finset.univ := fun hS h =>
    hHne (Finset.univ_subset_iff.mp (h ▸ hS))
  have hproper' : ∀ {S : Finset (Fin n)}, S ⊆ Hᶜ → S ≠ Finset.univ := fun hS h =>
    hHcne (Finset.univ_subset_iff.mp (h ▸ hS))
  have e1 := two_le_cutSum hx hC1 (hproper hsubC.1)
  have e2 := two_le_cutSum hx hC2 (hproper hsubC.2.1)
  have e3 := two_le_cutSum hx hC3 (hproper hsubC.2.2)
  have f1 := two_le_cutSum hx hD1 (hproper' hsubD.1)
  have f2 := two_le_cutSum hx hD2 (hproper' hsubD.2.1)
  have f3 := two_le_cutSum hx hD3 (hproper' hsubD.2.2)
  have hineq := comb_cutSum_le hx0 hC hD
  have := hH.cut_le
  have := h1.cut_le
  have := h2.cut_le
  have := h3.cut_le
  linarith

end TSPGap

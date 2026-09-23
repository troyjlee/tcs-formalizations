/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MatchingInputs
import TSPGap.Theorem528

/-!
# The data of KKO21's matching lemma (Lemma 6.2)

At a cut `S` with atoms `A(S) = H.children S`, `ε_F = 1/10`:

* `x(δ↑(u))` is **fractional** if `1/10 ≤ x(δ↑(u)) ≤ 9/10`;
* `F_u = 1 − ε_B` if `x(δ↑(u))` is fractional, else `1`;
* `Z_u = 2` if `|A(S)| ≥ 4` and `x(δ↑(u)) ≤ 1/10`, else `1`;
* the **demand** of the atom `u` (the sink capacity) is `x(δ↑(u)) F_u Z_u`;
* the **ordered row** `(u, u')` (a bundle with a distinguished endpoint) has
  capacity `(1 + α) x(E(u,u'))/2` when the bundle is good and `0` otherwise —
  the two orientations of a good bundle together carry `(1 + α) x_e`.

The Hall condition of the network (`MatchingHall.lean`) compares the demand
of an atom family `Q` with the capacity of the ordered rows touching `Q`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- `ε_F`-fractional at `ε_F = 1/10`. -/
def IsFractional (z : ℝ) : Prop := 1 / 10 ≤ z ∧ z ≤ 9 / 10

/-- `F_u`. -/
noncomputable def fFactor (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) (εB : ℝ)
    (u : Finset (Fin n)) : ℝ :=
  if IsFractional (upSum x S u) then 1 - εB else 1

/-- `Z_u`, with `k = |A(S)|`. -/
noncomputable def zFactor (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) (k : ℕ)
    (u : Finset (Fin n)) : ℝ :=
  if 4 ≤ k ∧ upSum x S u ≤ 1 / 10 then 2 else 1

/-- The demand `x(δ↑(u)) F_u Z_u`. -/
noncomputable def demand (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) (εB : ℝ) (k : ℕ)
    (u : Finset (Fin n)) : ℝ :=
  upSum x S u * fFactor x S εB u * zFactor x S k u

/-- The capacity of the ordered row `(u, u')`. -/
noncomputable def rowCap (μ : TreeDist n x) (ε₂ α : ℝ) (u u' : Finset (Fin n)) : ℝ :=
  if IsGoodBundle μ ε₂ u u' then (1 + α) * pairSum x u u' / 2 else 0

/-- The capacity of the ordered rows touching a family `Q` of atoms. -/
noncomputable def touchCap (μ : TreeDist n x) (ε₂ α : ℝ) (ch Q : Finset (Finset (Fin n))) :
    ℝ :=
  ∑ u ∈ ch, ∑ u' ∈ ch.erase u, if u ∈ Q ∨ u' ∈ Q then rowCap μ ε₂ α u u' else 0

theorem fFactor_le_one {S : Finset (Fin n)} {εB : ℝ} (hεB : 0 ≤ εB) (u : Finset (Fin n)) :
    fFactor x S εB u ≤ 1 := by
  unfold fFactor; split_ifs <;> linarith

theorem fFactor_pos {S : Finset (Fin n)} {εB : ℝ} (hεB : εB < 1) (u : Finset (Fin n)) :
    0 < fFactor x S εB u := by
  unfold fFactor; split_ifs <;> linarith

theorem zFactor_le_two (S : Finset (Fin n)) (k : ℕ) (u : Finset (Fin n)) :
    zFactor x S k u ≤ 2 := by
  unfold zFactor; split_ifs <;> norm_num

theorem one_le_zFactor (S : Finset (Fin n)) (k : ℕ) (u : Finset (Fin n)) :
    1 ≤ zFactor x S k u := by
  unfold zFactor; split_ifs <;> norm_num

theorem rowCap_nonneg (hx : ∀ e, 0 ≤ x e) (μ : TreeDist n x) {ε₂ α : ℝ} (hα : 0 ≤ α)
    {u u' : Finset (Fin n)} (huu' : Disjoint u u') : 0 ≤ rowCap μ ε₂ α u u' := by
  unfold rowCap
  split_ifs
  · have := pairSum_nonneg_lp hx huu'
    positivity
  · exact le_rfl

theorem rowCap_comm (μ : TreeDist n x) (ε₂ α : ℝ) (u u' : Finset (Fin n)) :
    rowCap μ ε₂ α u u' = rowCap μ ε₂ α u' u := by
  unfold rowCap
  rw [pairSum_comm]
  by_cases h : IsGoodBundle μ ε₂ u u'
  · rw [if_pos h, if_pos (isGoodBundle_comm.mp h)]
  · rw [if_neg h, if_neg fun h' => h (isGoodBundle_comm.mp h')]

end TSPGap

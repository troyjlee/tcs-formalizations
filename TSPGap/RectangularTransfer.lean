/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonIndep
import TSPGap.TopThinningsExists

/-!
# What rectangularity buys

`IsRectangularAt u E` says `E T ↔ InducesTree u T ∧ Q T` with `Q` reading only
the edges outside `u`.  Conditioning on such an `E` therefore leaves the law
*inside* `u` exactly where conditioning on "`u` induces a tree" leaves it —
which is Fact 2.8's content, and is what fails for an arbitrary subevent of a
happy event.

The export is the division-free factorization

`W(E ∧ A ∧ B) = W_face(A) · W(E ∧ B)`

for `A` inside-determined and `B` outside-determined at `u`
(`IsRectangularAt.weightMass_factor`), where `W_face` is the law conditioned on
`InducesTreeOn u`.  Everything else follows: the `B = True` case
(`weightMass_factor'`), the transfer of an inside bound through a uniform
thinning (`thin_weightMass_le`), and the same for expected counts
(`thin_expCard_le`).

⚠️ **`InducesTree` is not `InducesTreeOn`.**  The latter also asserts that `T`
is a spanning tree, and the two are *not* pointwise equivalent.  The conversion
is legitimate only on `μ.prob`'s support (`TreeDist.support_spanningTree`), so
it is done once, inside `weightMass_factor`, through
`weightMass_congr_of_support`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The support conversion -/

/-- On `μ`'s support, inducing a tree on `u` **is** inducing a tree on `u` as a
spanning tree.  ⚠️ Off the support the two differ, so this may not be used as a
pointwise rewrite. -/
theorem inducesTree_iff_of_support (μ : TreeDist n x) {u : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0) :
    InducesTree u T ↔ InducesTreeOn u T :=
  ⟨fun h => ⟨μ.support_spanningTree T hT, h⟩, fun h => h.2⟩

/-! ### The factorization -/

set_option maxHeartbeats 400000 in
-- four `weightMass` unwindings plus Fact 2.8 in one chain
/-- **Inside-event mass factorization through a rectangular event.**  For `A`
inside-determined and `B` outside-determined at `u`, conditioning on a
rectangular `E` factors the inside part off at the tree face. -/
theorem IsRectangularAt.weightMass_factor (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt u E)
    {A : Finset (Sym2 (Fin n)) → Prop} (hA : InsideDetermined u A)
    {B : Finset (Sym2 (Fin n)) → Prop} (hB : OutsideDetermined u B) :
    weightMass μ.prob (fun T => E T ∧ A T ∧ B T)
      = weightMass (treeFace μ.prob u) A * weightMass μ.prob (fun T => E T ∧ B T) := by
  classical
  obtain ⟨Q, hQ, hEQ⟩ := hE
  have hsupp : ∀ T, μ.prob T ≠ 0 → (E T ↔ (Q T ∧ InducesTreeOn u T)) := by
    intro T hT
    rw [hEQ T, inducesTree_iff_of_support μ hT]
    tauto
  have h1 : weightMass μ.prob (fun T => E T ∧ A T ∧ B T)
      = weightMass μ.prob (fun T => (A T ∧ (Q T ∧ B T)) ∧ InducesTreeOn u T) := by
    refine weightMass_congr_of_support fun T hT => ?_
    rw [hsupp T hT]
    tauto
  have h2 : weightMass μ.prob (fun T => E T ∧ B T)
      = weightMass μ.prob (fun T => (Q T ∧ B T) ∧ InducesTreeOn u T) := by
    refine weightMass_congr_of_support fun T hT => ?_
    rw [hsupp T hT]
    tauto
  have hu1 := treeFace_unwind μ hune hmass (fun T => A T ∧ (Q T ∧ B T))
  have hu2 := treeFace_unwind μ hune hmass (fun T => Q T ∧ B T)
  rw [h1, h2, ← hu1, ← hu2, treeFace_indep μ hμ hune hmass hA (hQ.and hB)]
  ring

/-- The `B = True` case: the inside event's face mass factors off outright. -/
theorem IsRectangularAt.weightMass_factor' (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt u E)
    {A : Finset (Sym2 (Fin n)) → Prop} (hA : InsideDetermined u A) :
    weightMass μ.prob (fun T => E T ∧ A T)
      = weightMass (treeFace μ.prob u) A * weightMass μ.prob E := by
  have h := hE.weightMass_factor μ hμ hune hmass hA
    (B := fun _ => True) (fun _ _ _ => Iff.rfl)
  rw [weightMass_congr (A := fun T => E T ∧ A T ∧ True) (B := fun T => E T ∧ A T)
      (fun T => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, trivial⟩⟩)] at h
  rw [weightMass_congr (A := fun T => E T ∧ True) (B := E)
      (fun T => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)] at h
  exact h

/-! ### Transfer through a uniform thinning -/

/-- **An inside bound at the tree face transfers to any uniform thinning of a
rectangular event.**  Zero-safe: a massless event forces `p = 0`. -/
theorem IsRectangularAt.thin_weightMass_le (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt u E)
    {v : Finset (Sym2 (Fin n)) → ℝ} {p : ℝ} (hv : IsUniformThinning μ.prob v E p)
    {A : Finset (Sym2 (Fin n)) → Prop} (hA : InsideDetermined u A)
    {c : ℝ} (h : weightMass (treeFace μ.prob u) A ≤ c) :
    weightMass v A ≤ p * c := by
  refine hv.weightMass_le μ.weightNonneg ?_
  rw [hE.weightMass_factor' μ hμ hune hmass hA]
  exact mul_le_mul_of_nonneg_right h (weightMass_nonneg μ.weightNonneg E)

/-- **Inside `expCard` factorization**, in the form the claims consume: a mean
bound at the tree face becomes a mean bound at the thinning. -/
theorem IsRectangularAt.thin_expCard_le (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {u : Finset (Fin n)} (hune : u.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges u)) (u.card - 1)))
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt u E)
    {v : Finset (Sym2 (Fin n)) → ℝ} {p : ℝ} (hv : IsUniformThinning μ.prob v E p)
    {D : Finset (Sym2 (Fin n))} (hD : ∀ e ∈ D, ∀ w ∈ e, w ∈ u)
    {c : ℝ} (h : expCard (treeFace μ.prob u) D ≤ c) :
    expCard v D ≤ p * c := by
  classical
  have hp0 : 0 ≤ p := by rw [← hv.total]; exact totalMass_nonneg hv.nonneg
  rw [expCard_eq_sum_marginal]
  calc ∑ e ∈ D, weightMass v (fun T => e ∈ T)
      ≤ ∑ e ∈ D, p * weightMass (treeFace μ.prob u) (fun T => e ∈ T) :=
        Finset.sum_le_sum fun e he => hE.thin_weightMass_le μ hμ hune hmass hv
          (insideDetermined_mem (hD e he)) le_rfl
    _ = p * expCard (treeFace μ.prob u) D := by
        rw [expCard_eq_sum_marginal, Finset.mul_sum]
    _ ≤ p * c := mul_le_mul_of_nonneg_left h hp0

end TSPGap

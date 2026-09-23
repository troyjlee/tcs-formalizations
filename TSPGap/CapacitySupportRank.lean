/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacitySupportReduction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The edge bound for rigid support

Supported entry weights map injectively to their row and column marginals
when support is rigid. The marginals satisfy one linear relation, so the
number of supported entries is at most the number of vertices minus one.
This is the forest edge bound in the algebraic interface; no converse or
graph-acyclicity assertion is needed here.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- Extend weights on the nonzero entries by zero. -/
noncomputable def edgeLift (A : R → C → ℝ) :
    (↥(support A) → ℝ) →ₗ[ℝ] (R → C → ℝ) := by
  classical
  exact
    { toFun := fun w i j => if h : (i, j) ∈ support A then w ⟨(i, j), h⟩ else 0
      map_add' := fun w v => by
        funext i j
        simp only [Pi.add_apply]
        split_ifs <;> simp only [add_zero]
      map_smul' := fun t w => by
        funext i j
        simp only [Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp only [smul_zero] }

theorem edgeLift_supported (A : R → C → ℝ) (w : ↥(support A) → ℝ) :
    SupportedBy (edgeLift A w) A := by
  classical
  intro i j h
  simp [edgeLift, h]

theorem edgeLift_injective (A : R → C → ℝ) : Function.Injective (edgeLift A) := by
  classical
  intro w v h
  funext e
  have he := congrFun (congrFun h e.val.1) e.val.2
  simpa only [edgeLift, LinearMap.coe_mk, AddHom.coe_mk, dif_pos e.property] using he

/-- The map recording both families of marginals. -/
noncomputable def marginalMap : (R → C → ℝ) →ₗ[ℝ] ((R → ℝ) × (C → ℝ)) where
  toFun D := (fun i => ∑ j, D i j, fun j => ∑ i, D i j)
  map_add' D E := by
    ext <;> simp [Finset.sum_add_distrib]
  map_smul' t D := by
    ext <;> simp [Finset.mul_sum]

/-- Row total minus column total is the redundant marginal equation. -/
noncomputable def totalDiff : ((R → ℝ) × (C → ℝ)) →ₗ[ℝ] ℝ where
  toFun z := ∑ i, z.1 i - ∑ j, z.2 j
  map_add' z w := by simp [Finset.sum_add_distrib]; ring
  map_smul' t z := by simp [Finset.mul_sum, mul_sub]

theorem totalDiff_marginalMap (D : R → C → ℝ) :
    totalDiff (marginalMap D) = 0 := by
  change (∑ i, ∑ j, D i j) - (∑ j, ∑ i, D i j) = 0
  rw [Finset.sum_comm, sub_self]

theorem totalDiff_surjective [Nonempty R] :
    Function.Surjective (totalDiff (R := R) (C := C)) := by
  classical
  intro t
  let i : R := Classical.choice inferInstance
  refine ⟨(Pi.single i t, 0), ?_⟩
  simp [totalDiff]

theorem marginalMap_edgeLift_injective {A : R → C → ℝ} (hA : IsRigid A) :
    Function.Injective (marginalMap.comp (edgeLift A)) := by
  intro w v h
  have hz : marginalMap (edgeLift A (w - v)) = 0 := by
    rw [map_sub, map_sub, sub_eq_zero]
    exact h
  have hb : IsBalanced (edgeLift A (w - v)) := by
    constructor
    · intro i
      exact congrFun (congrArg Prod.fst hz) i
    · intro j
      exact congrFun (congrArg Prod.snd hz) j
  have he := hA _ hb (edgeLift_supported A (w - v))
  apply sub_eq_zero.mp
  apply edgeLift_injective A
  simpa using he

/-- The forest edge bound. Subtraction on naturals makes the empty matrix
a valid instance; the stronger leaf bound will explicitly require a vertex. -/
theorem IsRigid.support_card_le {A : R → C → ℝ} (hA : IsRigid A) :
    (support A).card ≤ Fintype.card R + Fintype.card C - 1 := by
  classical
  cases isEmpty_or_nonempty R with
  | inl h =>
    letI := h
    have : support A = ∅ := by ext e; exact isEmptyElim e.1
    simp [this]
  | inr h =>
    letI := h
    let f := (marginalMap (R := R) (C := C)).comp (edgeLift A)
    let g := f.codRestrict (totalDiff (R := R) (C := C)).ker
      (fun w => totalDiff_marginalMap (edgeLift A w))
    have hg : Function.Injective g := by
      intro w v he
      exact marginalMap_edgeLift_injective hA (congrArg Subtype.val he)
    have hdim := LinearMap.finrank_le_finrank_of_injective hg
    have hrank := (totalDiff (R := R) (C := C)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr totalDiff_surjective, finrank_top,
      Module.finrank_self, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdim
    omega

/-- Rigidity survives any support restriction, regardless of its values. -/
theorem IsRigid.of_supportedBy {A B : R → C → ℝ} (hA : IsRigid A)
    (hBA : SupportedBy B A) : IsRigid B :=
  fun D hD hDB => hA D hD (hDB.trans hBA)

/-- The two sides of the bipartition may be interchanged. -/
theorem IsRigid.transpose {A : R → C → ℝ} (hA : IsRigid A) :
    IsRigid (fun j i => A i j) := by
  intro D hD hs
  have he := hA (fun i j => D j i) ⟨hD.2, hD.1⟩ (fun i j => hs j i)
  funext j i
  exact congrFun (congrFun he i) j

end TSPGap.CapacityMatrix

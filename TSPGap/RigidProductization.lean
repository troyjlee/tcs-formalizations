/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HomogeneousProductization
import TSPGap.CapacityLeaves

/-!
# Productization with rigid support

At a positive evaluation vector, combine the exact homogeneous
productization with the support-reduction theorem. The resulting product
is a lower bound, not an exact factorization. Its column sums are still the
original gradient. This is the entry point for the remaining leaf-removal
capacity induction, not a capacity or coefficient estimate by itself.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] {p : MvPolynomial ι ℝ}

/-- Each positive evaluation has a stochastic rigid-support product below
it, with the same degree and gradient. No forest premise is imposed on `p`. -/
theorem homogeneous_rigid_productization {d : ℕ} (hd : 0 < d)
    (hp : p.IsHomogeneous d) (h1 : MvPolynomial.eval (fun _ => 1) p = 1)
    (hst : ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0)
    (x : ι → ℝ) (hx : ∀ j, 0 < x j) :
    Fintype.card (RootOccurrence (diagonalLine x p)) = d ∧
    ∃ B : RootOccurrence (diagonalLine x p) → ι → ℝ,
      CapacityMatrix.IsStochastic B ∧
      (∀ j, ∑ a, B a j = MvPolynomial.eval (fun _ => 1) (MvPolynomial.pderiv j p)) ∧
      CapacityMatrix.IsRigid B ∧
      CapacityMatrix.value B x ≤ MvPolynomial.eval x p ∧
      (CapacityMatrix.support B).card ≤ d + Fintype.card ι - 1 := by
  obtain ⟨hcard, A, hn, hr, hc, he⟩ := homogeneous_productization hd hp h1 hst x
  obtain ⟨B, hB, hcols, hval, hrigid, _⟩ :=
    CapacityMatrix.exists_rigid_reduction ⟨hn, hr⟩ hx
  refine ⟨hcard, B, hB, fun j => (hcols j).trans (hc j), hrigid, ?_, ?_⟩
  · apply hval.trans_eq
    simpa only [CapacityMatrix.value, mul_comm] using he
  · simpa only [hcard] using hrigid.support_card_le

end TSPGap

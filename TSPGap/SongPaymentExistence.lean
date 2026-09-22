/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SeparatedRepair
import TSPGap.HierarchyExistence

/-!
# Song's main payment with separate repairs

Construct the hierarchy, the actual main payment and both repairs from
the restricted LP and its maximum-entropy tree law. This package retains
the sharper bottom saving and classified mass; the deterministic threshold
reweighting is a subsequent step.
-/

namespace TSPGap.Song
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {η β : ℝ}

/-- The complete payment and separate repairs for every positive Song threshold. -/
theorem exists_payment_with_repairs (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ Song.H) (hβ : 0 ≤ β) :
    ∃ (H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)) (Eg : Finset (Sym2 (Fin n)))
      (s sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      Song.PaymentCore H μ β Eg s ∧ SeparatedRepair H μ β Eg s sTwo sOne := by
  have hsmall : η ≤ 1e-12 := hη.trans (by norm_num [Song.H])
  obtain ⟨F⟩ := exists_oneSideFamily hx₀ hη0.le (by linarith) e₀
  obtain ⟨H, hH, hDegree⟩ :=
    exists_hierarchy_of_oneSideFamily hx₀ hx₀e F hη0 (by linarith)
  obtain ⟨s, hcore⟩ := exists_globalPayment_seven_mul
    (restrict_isRestrictedLP hx₀) μ hμ hη0.le hη H hDegree hβ
  obtain ⟨sTwo, sOne, hrepair⟩ := exists_separatedRepair hcore hH hx₀ hx₀e hn hη0 hη hβ
  exact ⟨H, goodness.goodEdges H μ, s, sTwo, sOne, hcore, hrepair⟩

end TSPGap.Song

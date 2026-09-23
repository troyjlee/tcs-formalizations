/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SlackVector
import TSPGap.LemmaSevenThreeConsumer

/-!
# KKO21 §7.2: the increase of a polygon cut on an edge set, and Eq. (50)

For a set `D ⊆ δ(S)` of edges of a polygon cut `S` with polygon partition
`A, B, C`, KKO21 Eq. (48) defines

`I_S(D) = (1 + ε_η)(max{r(A ∩ D) 1{S not left happy}, r(B ∩ D) 1{S not right
happy}} + r(C ∩ D) 1{S not happy})`,

so that `I_S(δ(S)) = I_S` (Eq. (32), `BottomThinning.increase`) and `I_S` is
**subadditive** over disjoint sets.  The bound of Lemma 7.7 is then organized
as `I_S ≤ I_S↑ + I_S→` with `I_S↑ = I_S(δ↑(S))` bounded by Eq. (50) — every
edge of `δ↑(S)` paying the trivial `(1 + ε_η) τ p x_f`, except the bottom
edges of `A` and `B`, which pay `0.56797 β p x_f` by Corollary 5.11 at their
own near-cycle parent — and `I_S→ = I_S(δ→(S))` left to Lemmas 7.8–7.11.

Everything here is on the base with a generic reduction vector; Eq. (50) is at
the partition-free `ReductionCertificate`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

namespace NearCycle

variable (N : NearCycle x εη)

/-- **Eq. (48)**: the increase of the polygon on the edge set `D`. -/
noncomputable def increaseOn (r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    (D : Finset (Sym2 (Fin n))) (T : Finset (Sym2 (Fin n))) : ℝ :=
  (1 + εη) * (max ((∑ f ∈ N.partA ∩ D, r T f) * (if N.LeftHappy T then 0 else 1))
      ((∑ f ∈ N.partB ∩ D, r T f) * (if N.RightHappy T then 0 else 1))
    + (∑ f ∈ N.partC ∩ D, r T f) * (if N.Happy T then 0 else 1))

variable {N}

/-- Not left happy, hence not happy. -/
theorem not_happy_of_not_leftHappy {T : Finset (Sym2 (Fin n))} (h : ¬ N.LeftHappy T) :
    ¬ N.Happy T := fun hh => h ⟨hh.1, hh.2.2⟩

theorem not_happy_of_not_rightHappy {T : Finset (Sym2 (Fin n))} (h : ¬ N.RightHappy T) :
    ¬ N.Happy T := fun hh => h ⟨hh.2.1, hh.2.2⟩

/-- The indicator of the negation, in the other orientation. -/
theorem ite_not_eq {Q : Prop} : (if Q then (0:ℝ) else 1) = if ¬ Q then 1 else 0 := by
  by_cases h : Q <;> simp [h]

/-- `C ⊆ δ(root)`. -/
theorem partC_subset_cutEdges_root' : N.partC ⊆ cutEdges N.root := by
  unfold NearCycle.partC
  exact Finset.sdiff_subset

theorem increaseOn_nonneg (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) (D : Finset (Sym2 (Fin n))) :
    0 ≤ N.increaseOn r D T := by
  unfold increaseOn
  have hA : 0 ≤ (∑ f ∈ N.partA ∩ D, r T f) * (if N.LeftHappy T then 0 else 1) := by
    have := Finset.sum_nonneg fun f (_ : f ∈ N.partA ∩ D) => hr f
    split_ifs <;> simp [this]
  have hC : 0 ≤ (∑ f ∈ N.partC ∩ D, r T f) * (if N.Happy T then 0 else 1) := by
    have := Finset.sum_nonneg fun f (_ : f ∈ N.partC ∩ D) => hr f
    split_ifs <;> simp [this]
  exact mul_nonneg (by linarith) (add_nonneg (le_trans hA (le_max_left _ _)) hC)

/-- **Subadditivity** over disjoint edge sets, for a nonnegative reduction. -/
theorem increaseOn_union_le (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) {D₁ D₂ : Finset (Sym2 (Fin n))}
    (hdisj : Disjoint D₁ D₂) :
    N.increaseOn r (D₁ ∪ D₂) T ≤ N.increaseOn r D₁ T + N.increaseOn r D₂ T := by
  unfold increaseOn
  have hsplit : ∀ X : Finset (Sym2 (Fin n)), ∑ f ∈ X ∩ (D₁ ∪ D₂), r T f
      = (∑ f ∈ X ∩ D₁, r T f) + ∑ f ∈ X ∩ D₂, r T f := by
    intro X
    rw [Finset.inter_union_distrib_left, Finset.sum_union]
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj)
  rw [hsplit, hsplit, hsplit]
  have hmax : ∀ a b c d : ℝ, max (a + b) (c + d) ≤ max a c + max b d := fun a b c d =>
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_le_add (le_max_right _ _) (le_max_right _ _))
  have h := hmax ((∑ f ∈ N.partA ∩ D₁, r T f) * (if N.LeftHappy T then 0 else 1))
    ((∑ f ∈ N.partA ∩ D₂, r T f) * (if N.LeftHappy T then 0 else 1))
    ((∑ f ∈ N.partB ∩ D₁, r T f) * (if N.RightHappy T then 0 else 1))
    ((∑ f ∈ N.partB ∩ D₂, r T f) * (if N.RightHappy T then 0 else 1))
  rw [← add_mul, ← add_mul] at h
  have hC : ((∑ f ∈ N.partC ∩ D₁, r T f) + ∑ f ∈ N.partC ∩ D₂, r T f)
      * (if N.Happy T then 0 else 1)
      = (∑ f ∈ N.partC ∩ D₁, r T f) * (if N.Happy T then 0 else 1)
        + (∑ f ∈ N.partC ∩ D₂, r T f) * (if N.Happy T then 0 else 1) := add_mul _ _ _
  rw [hC]
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  nlinarith [h, h1]

/-- Subadditivity over the edges of `D`, one at a time. -/
theorem increaseOn_le_sum_singleton (hεη : 0 ≤ εη)
    {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ} {T : Finset (Sym2 (Fin n))}
    (hr : ∀ g, 0 ≤ r T g) (D : Finset (Sym2 (Fin n))) :
    N.increaseOn r D T ≤ ∑ f ∈ D, N.increaseOn r {f} T := by
  induction D using Finset.induction_on with
  | empty =>
    unfold increaseOn
    simp
  | insert f D hf ih =>
    rw [Finset.sum_insert hf, Finset.insert_eq]
    refine le_trans (increaseOn_union_le hεη hr (Finset.disjoint_singleton_left.mpr hf)) ?_
    linarith

/-- **The trivial bound with the happiness indicator**: on an unhappy tree
`I_S(D) ≤ (1 + ε_η) r(δ(S) ∩ D)`, and `I_S(D) = 0` on a happy one. -/
theorem increaseOn_le_sum_root (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) (D : Finset (Sym2 (Fin n))) :
    N.increaseOn r D T
      ≤ (1 + εη) * (∑ f ∈ cutEdges N.root ∩ D, r T f) * (if N.Happy T then 0 else 1) := by
  unfold increaseOn
  have hA0 : 0 ≤ ∑ f ∈ N.partA ∩ D, r T f := Finset.sum_nonneg fun f _ => hr f
  have hB0 : 0 ≤ ∑ f ∈ N.partB ∩ D, r T f := Finset.sum_nonneg fun f _ => hr f
  have hC0 : 0 ≤ ∑ f ∈ N.partC ∩ D, r T f := Finset.sum_nonneg fun f _ => hr f
  have hAB : Disjoint (N.partA ∩ D) (N.partB ∩ D) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left N.partA_disjoint_partB)
  have hABC : Disjoint (N.partA ∩ D ∪ N.partB ∩ D) (N.partC ∩ D) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left N.partA_disjoint_partC),
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left N.partB_disjoint_partC)⟩
  have hsum : ∑ f ∈ cutEdges N.root ∩ D, r T f
      = (∑ f ∈ N.partA ∩ D, r T f) + (∑ f ∈ N.partB ∩ D, r T f)
        + ∑ f ∈ N.partC ∩ D, r T f := by
    rw [← N.partA_union_partB_union_partC, Finset.union_inter_distrib_right,
      Finset.union_inter_distrib_right, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum]
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  by_cases hH : N.Happy T
  · have hL : N.LeftHappy T := ⟨hH.1, hH.2.2⟩
    have hR : N.RightHappy T := ⟨hH.2.1, hH.2.2⟩
    rw [if_pos hH, if_pos hL, if_pos hR]
    simp
  · rw [if_neg hH]
    by_cases hL : N.LeftHappy T <;> by_cases hR : N.RightHappy T
    · exact absurd ⟨hL.1, hR.1, hL.2⟩ hH
    · rw [if_pos hL, if_neg hR]
      have : max ((∑ f ∈ N.partA ∩ D, r T f) * 0) ((∑ f ∈ N.partB ∩ D, r T f) * 1)
          = ∑ f ∈ N.partB ∩ D, r T f := by
        rw [mul_zero, mul_one]; exact max_eq_right hB0
      rw [this]
      nlinarith
    · rw [if_neg hL, if_pos hR]
      have : max ((∑ f ∈ N.partA ∩ D, r T f) * 1) ((∑ f ∈ N.partB ∩ D, r T f) * 0)
          = ∑ f ∈ N.partA ∩ D, r T f := by
        rw [mul_zero, mul_one]; exact max_eq_left hA0
      rw [this]
      nlinarith
    · rw [if_neg hL, if_neg hR]
      have : max ((∑ f ∈ N.partA ∩ D, r T f) * 1) ((∑ f ∈ N.partB ∩ D, r T f) * 1)
          ≤ (∑ f ∈ N.partA ∩ D, r T f) + ∑ f ∈ N.partB ∩ D, r T f := by
        rw [mul_one, mul_one]; exact max_le (by linarith) (by linarith)
      nlinarith

/-- The trivial bound: `I_S(D) ≤ (1 + ε_η) r(δ(S) ∩ D)`. -/
theorem increaseOn_le_sum_root' (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) (D : Finset (Sym2 (Fin n))) :
    N.increaseOn r D T ≤ (1 + εη) * ∑ f ∈ cutEdges N.root ∩ D, r T f := by
  refine le_trans (increaseOn_le_sum_root hεη hr D) ?_
  have h0 : 0 ≤ (1 + εη) * ∑ f ∈ cutEdges N.root ∩ D, r T f :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun f _ => hr f)
  split_ifs <;> simp [h0]

/-! ### The increase at a single edge -/

theorem increaseOn_singleton_partA {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) {f : Sym2 (Fin n)} (hf : f ∈ N.partA) :
    N.increaseOn r {f} T = (1 + εη) * (r T f * if N.LeftHappy T then 0 else 1) := by
  unfold increaseOn
  have hA : N.partA ∩ {f} = {f} := by
    rw [Finset.inter_singleton_of_mem hf]
  have hB : N.partB ∩ {f} = ∅ := by
    rw [Finset.inter_singleton_of_notMem]
    exact Finset.disjoint_left.mp N.partA_disjoint_partB hf
  have hC : N.partC ∩ {f} = ∅ := by
    rw [Finset.inter_singleton_of_notMem]
    exact Finset.disjoint_left.mp N.partA_disjoint_partC hf
  rw [hA, hB, hC, Finset.sum_singleton, Finset.sum_empty, zero_mul, zero_mul, add_zero]
  have h0 : 0 ≤ r T f * (if N.LeftHappy T then 0 else 1) := by
    have := hr f; split_ifs <;> simp [this]
  rw [max_eq_left h0]

theorem increaseOn_singleton_partB {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) {f : Sym2 (Fin n)} (hf : f ∈ N.partB) :
    N.increaseOn r {f} T = (1 + εη) * (r T f * if N.RightHappy T then 0 else 1) := by
  unfold increaseOn
  have hA : N.partA ∩ {f} = ∅ := by
    rw [Finset.inter_singleton_of_notMem]
    exact Finset.disjoint_right.mp N.partA_disjoint_partB hf
  have hB : N.partB ∩ {f} = {f} := by
    rw [Finset.inter_singleton_of_mem hf]
  have hC : N.partC ∩ {f} = ∅ := by
    rw [Finset.inter_singleton_of_notMem]
    exact Finset.disjoint_left.mp N.partB_disjoint_partC hf
  rw [hA, hB, hC, Finset.sum_singleton, Finset.sum_empty, zero_mul, zero_mul, add_zero]
  have h0 : 0 ≤ r T f * (if N.RightHappy T then 0 else 1) := by
    have := hr f; split_ifs <;> simp [this]
  rw [max_eq_right h0]

/-- An edge of `δ(S)` pays at most `(1 + ε_η) r_f` outright. -/
theorem increaseOn_singleton_le (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) (f : Sym2 (Fin n)) :
    N.increaseOn r {f} T ≤ (1 + εη) * r T f := by
  refine le_trans (increaseOn_le_sum_root' hεη hr {f}) ?_
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  have hle : ∑ g ∈ cutEdges N.root ∩ {f}, r T g ≤ r T f := by
    by_cases hf : f ∈ cutEdges N.root
    · rw [Finset.inter_singleton_of_mem hf, Finset.sum_singleton]
    · rw [Finset.inter_singleton_of_notMem hf, Finset.sum_empty]; exact hr f
  exact mul_le_mul_of_nonneg_left hle h1

/-- `I_S = I_S(δ(S))`: the increase of Eq. (32) is the increase on the whole cut. -/
theorem increaseOn_cutEdges_root (r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    (T : Finset (Sym2 (Fin n))) :
    N.increaseOn r (cutEdges N.root) T
      = (1 + εη) * (max ((∑ f ∈ N.partA, r T f) * (if N.LeftHappy T then 0 else 1))
          ((∑ f ∈ N.partB, r T f) * (if N.RightHappy T then 0 else 1))
        + (∑ f ∈ N.partC, r T f) * (if N.Happy T then 0 else 1)) := by
  unfold increaseOn
  rw [Finset.inter_eq_left.mpr N.partA_subset_cutEdges_root,
    Finset.inter_eq_left.mpr N.partB_subset_cutEdges_root,
    Finset.inter_eq_left.mpr N.partC_subset_cutEdges_root']

end NearCycle

/-! ### The split `I_S ≤ I_S↑ + I_S→` -/

namespace BottomThinning

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {p : ℝ}
  (Ξ : BottomThinning H μ S p)

/-- The presenting near-cycle's root cut is `δ(S)`. -/
theorem cutEdges_root : cutEdges Ξ.cycle.root = cutEdges S := by
  rw [Ξ.presents.1, cutEdges_compl]

/-- `I_S` is `I_S(δ(S))`. -/
theorem increase_eq_increaseOn (r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    (T : Finset (Sym2 (Fin n))) :
    Ξ.increase r T = Ξ.cycle.increaseOn r (cutEdges S) T := by
  rw [← Ξ.cutEdges_root, NearCycle.increaseOn_cutEdges_root]
  rfl

/-- **`I_S ≤ I_S↑ + I_S→`**, at the parent `Ŝ`. -/
theorem increase_le_up_add_arrow (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) (Ŝ : Finset (Fin n)) :
    Ξ.increase r T
      ≤ Ξ.cycle.increaseOn r (upEdges Ŝ S) T
        + Ξ.cycle.increaseOn r (cutEdges S \ cutEdges Ŝ) T := by
  rw [Ξ.increase_eq_increaseOn]
  have hsplit : cutEdges S = upEdges Ŝ S ∪ (cutEdges S \ cutEdges Ŝ) := by
    unfold upEdges
    rw [Finset.inter_comm, Finset.union_comm, Finset.sdiff_union_inter]
  have hdisj : Disjoint (upEdges Ŝ S) (cutEdges S \ cutEdges Ŝ) := by
    unfold upEdges
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left Finset.disjoint_sdiff
  have := NearCycle.increaseOn_union_le (N := Ξ.cycle) hεη hr hdisj
  rw [← hsplit] at this
  exact this

end BottomThinning

/-! ### Eq. (50): the tail `δ↑(S)` -/

namespace ReductionCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  (C : ReductionCertificate H μ ε₂ p)

/-- `E[ρ_{e,u}] ≤ p` at every ordered pair, for `p ≥ 0`. -/
theorem _root_.TSPGap.TopDensities.expect_rho_le {S : Finset (Fin n)}
    (Θ : TopDensities H μ S ε₂ p) (hp : 0 ≤ p) (u u' : Finset (Fin n)) :
    μ.expect (Θ.rho u u') ≤ p := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact le_of_eq (Θ.expect_rho u h.1 u' h.2.1 h.2.2.1 h.2.2.2)
  · have : Θ.rho u u' = fun _ => 0 := funext fun T => Θ.rho_eq_zero_of_not_good u u' h T
    rw [this, μ.expect_const]
    exact hp

/-- **`E[r_f] ≤ τ p x_f` on every non-bottom edge.** -/
theorem expect_reduction_le_of_not_bottom (hx : ∀ e, 0 ≤ x e) {β τ : ℝ} (hτ : 0 ≤ τ)
    (hp : 0 ≤ p) {f : Sym2 (Fin n)} (hgen : f ∈ edgeFinset n) (hnb : ¬ IsBottomEdge H f) :
    μ.expect (fun T => C.reduction β τ T f) ≤ τ * p * x f := by
  have hxf := hx f
  have hnn : 0 ≤ τ * p * x f := by positivity
  by_cases hpar : ∃ V, H.IsEdgeParent f V
  · obtain ⟨V, hV⟩ := hpar
    have hcyc : ¬ H.IsNearCycleCut V := fun h => hnb ⟨V, hV, h⟩
    by_cases hdeg : DegreeCutData H V
    · have hdiag : ¬ f.IsDiag := (Finset.mem_filter.mp hgen).2
      rcases H.exists_between_children_of_isEdgeParent hV hdiag with
        ⟨a, ha, b, hb, hab, hfab⟩ | hnone
      · have hpt : (fun T => C.reduction β τ T f)
            = fun T => τ * x f / 2 * (C.top V hdeg).rho a b T
                + τ * x f / 2 * (C.top V hdeg).rho b a T := by
          funext T
          rw [C.reduction_top hV hdeg, (C.top V hdeg).reduction_eq ha hb hab hfab]
          ring
        rw [hpt, μ.expect_add, μ.expect_mul_left, μ.expect_mul_left]
        have h1 := (C.top V hdeg).expect_rho_le hp a b
        have h2 := (C.top V hdeg).expect_rho_le hp b a
        have h3 : 0 ≤ τ * x f / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h3]
      · have hpt : (fun T => C.reduction β τ T f) = fun _ => 0 := by
          funext T
          rw [C.reduction_top hV hdeg]
          exact (C.top V hdeg).reduction_eq_zero_of_not
            (fun a ha _ _ _ _ => hnone a (H.mem_children.mp ha)) τ T
        rw [hpt, μ.expect_const]
        exact hnn
    · have hpt : (fun T => C.reduction β τ T f) = fun _ => 0 := by
        funext T
        exact C.reduction_eq_zero_of_neither hV hcyc hdeg
      rw [hpt, μ.expect_const]
      exact hnn
  · have hpt : (fun T => C.reduction β τ T f) = fun _ => 0 := by
      funext T
      exact C.reduction_eq_zero_of_noParent fun V hV => hpar ⟨V, hV⟩
    rw [hpt, μ.expect_const]
    exact hnn

/-- The expectation is monotone. -/
theorem _root_.TSPGap.TreeDist.expect_le_expect (μ : TreeDist n x)
    {f g : Finset (Sym2 (Fin n)) → ℝ} (h : ∀ T, f T ≤ g T) : μ.expect f ≤ μ.expect g := by
  unfold TreeDist.expect
  exact Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (h T) (μ.prob_nonneg T)

set_option maxHeartbeats 800000 in
-- every edge of the tail, by its parent: bottom in `A`/`B` (Corollary 5.11), bottom in
-- `C` (trivially), or not bottom (the top trivial bound)
/-- **KKO21 Eq. (50)** at the certificate: for the polygon cut `S` with parent `Ŝ`,
`E[I_S↑] ≤ (1 + ε_η) τ p x(δ↑(S)) + (1 + ε_η) β p · 3ε_η`, provided
`0.56797 β ≤ τ`.  The `C`-part of the tail pays the trivial `β p x_f`, and its
mass is at most `x(C) ≤ 3ε_η`. -/
theorem expect_increaseOn_up_le (hx : ∀ e, 0 ≤ x e) (hBG : C.HasBottomGuarantees)
    (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hβτ : 0.56797 * β ≤ τ) (hp : 0 ≤ p)
    {S Ŝ : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ) (upEdges Ŝ S) T)
      ≤ (1 + εη) * τ * p * upSum x Ŝ S + (1 + εη) * β * p * (3 * εη) := by
  set Ξ := C.bottom S hS hcyc with hΞ
  set N := Ξ.cycle with hN
  have hpres : H.Presents N S := Ξ.presents
  have hrnn : ∀ T g, 0 ≤ C.reduction β τ T g := fun T g => C.reduction_nonneg hβ hτ (hx g) T
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  -- per edge
  have hedge : ∀ f ∈ upEdges Ŝ S, μ.expect (fun T => N.increaseOn (C.reduction β τ) {f} T)
      ≤ (1 + εη) * τ * p * x f + (if f ∈ N.partC then (1 + εη) * β * p * x f else 0) := by
    intro f hf
    have hfS : f ∈ cutEdges S := (Finset.mem_inter.mp hf).2
    have hgen : f ∈ edgeFinset n := cutEdges_subset_edgeFinset S hfS
    have hxf := hx f
    by_cases hnb : IsBottomEdge H f
    · obtain ⟨V, hV, hVcyc⟩ := hnb
      have hlt : S ⊂ V := ssubset_of_isEdgeParent H hS hfS hV
      have hbot : ∀ T, C.reduction β τ T f = β * x f * (C.bottom V hV.1 hVcyc).rho T :=
        fun T => C.reduction_bottom hV hVcyc
      have hguar := hBG.bottom_guar V hV.1 hVcyc
      -- three positions in the polygon partition
      have hfroot : f ∈ cutEdges N.root := by rw [Ξ.cutEdges_root]; exact hfS
      have hpos : f ∈ N.partA ∨ f ∈ N.partB ∨ f ∈ N.partC := by
        have := N.partA_union_partB_union_partC ▸ hfroot
        rcases Finset.mem_union.mp this with hAB | hC
        · rcases Finset.mem_union.mp hAB with hA | hB
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · exact Or.inr (Or.inr hC)
      rcases hpos with hA | hB | hC
      · -- `A`: Corollary 5.11, left
        have hnotC : f ∉ N.partC := Finset.disjoint_left.mp N.partA_disjoint_partC hA
        rw [if_neg hnotC, add_zero]
        have hpt : (fun T => N.increaseOn (C.reduction β τ) {f} T)
            = fun T => (1 + εη) * β * x f * ((C.bottom V hV.1 hVcyc).rho T
                * if ¬ N.LeftHappy T then 1 else 0) := by
          funext T
          rw [NearCycle.increaseOn_singleton_partA (hrnn T) hA, hbot T,
            NearCycle.ite_not_eq]
          ring
        rw [hpt, μ.expect_mul_left]
        have hb := (C.bottom V hV.1 hVcyc).expect_rho_le (Q := fun T => ¬ N.LeftHappy T)
          (hguar.notLeftHappy_le S hS hlt N hpres)
        have hbr : μ.expect (fun T => (C.bottom V hV.1 hVcyc).rho T
            * if ¬ N.LeftHappy T then 1 else 0) ≤ 0.56797 * p :=
          le_trans (le_of_eq (congrArg μ.expect (funext fun T =>
            congrArg (fun z : ℝ => (C.bottom V hV.1 hVcyc).rho T * z)
              (ite_instance_congr _ _ _ (1 : ℝ) 0)))) hb
        have hc : 0 ≤ (1 + εη) * β * x f := by positivity
        calc (1 + εη) * β * x f * μ.expect (fun T => (C.bottom V hV.1 hVcyc).rho T
              * if ¬ N.LeftHappy T then 1 else 0)
            ≤ (1 + εη) * β * x f * (0.56797 * p) := mul_le_mul_of_nonneg_left hbr hc
          _ ≤ (1 + εη) * τ * p * x f := by nlinarith [mul_nonneg h1 (mul_nonneg hp hxf)]
      · -- `B`: Corollary 5.11, right
        have hnotC : f ∉ N.partC := Finset.disjoint_left.mp N.partB_disjoint_partC hB
        rw [if_neg hnotC, add_zero]
        have hpt : (fun T => N.increaseOn (C.reduction β τ) {f} T)
            = fun T => (1 + εη) * β * x f * ((C.bottom V hV.1 hVcyc).rho T
                * if ¬ N.RightHappy T then 1 else 0) := by
          funext T
          rw [NearCycle.increaseOn_singleton_partB (hrnn T) hB, hbot T,
            NearCycle.ite_not_eq]
          ring
        rw [hpt, μ.expect_mul_left]
        have hb := (C.bottom V hV.1 hVcyc).expect_rho_le (Q := fun T => ¬ N.RightHappy T)
          (hguar.notRightHappy_le S hS hlt N hpres)
        have hbr : μ.expect (fun T => (C.bottom V hV.1 hVcyc).rho T
            * if ¬ N.RightHappy T then 1 else 0) ≤ 0.56797 * p :=
          le_trans (le_of_eq (congrArg μ.expect (funext fun T =>
            congrArg (fun z : ℝ => (C.bottom V hV.1 hVcyc).rho T * z)
              (ite_instance_congr _ _ _ (1 : ℝ) 0)))) hb
        have hc : 0 ≤ (1 + εη) * β * x f := by positivity
        calc (1 + εη) * β * x f * μ.expect (fun T => (C.bottom V hV.1 hVcyc).rho T
              * if ¬ N.RightHappy T then 1 else 0)
            ≤ (1 + εη) * β * x f * (0.56797 * p) := mul_le_mul_of_nonneg_left hbr hc
          _ ≤ (1 + εη) * τ * p * x f := by nlinarith [mul_nonneg h1 (mul_nonneg hp hxf)]
      · -- `C`: the trivial bound
        rw [if_pos hC]
        refine le_trans (μ.expect_le_expect fun T => N.increaseOn_singleton_le hεη (hrnn T) f) ?_
        rw [μ.expect_mul_left, C.expect_reduction_bottom hV hVcyc]
        have : 0 ≤ (1 + εη) * τ * p * x f := by positivity
        nlinarith
    · -- not a bottom edge: the top trivial bound
      have h0 : (0:ℝ) ≤ if f ∈ N.partC then (1 + εη) * β * p * x f else 0 := by
        split_ifs <;> positivity
      refine le_trans (μ.expect_le_expect fun T => N.increaseOn_singleton_le hεη (hrnn T) f) ?_
      rw [μ.expect_mul_left]
      have := C.expect_reduction_le_of_not_bottom (β := β) hx hτ hp hgen hnb
      nlinarith [mul_le_mul_of_nonneg_left this h1]
  -- sum over the tail
  have hsub := μ.expect_le_expect fun T =>
    NearCycle.increaseOn_le_sum_singleton (N := N) hεη (hrnn T) (upEdges Ŝ S)
  refine le_trans hsub ?_
  rw [μ.expect_sum]
  refine le_trans (Finset.sum_le_sum hedge) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  have hCmass : ∑ f ∈ (upEdges Ŝ S).filter (fun f => f ∈ N.partC), (1 + εη) * β * p * x f
      ≤ (1 + εη) * β * p * (3 * εη) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun f hf => (Finset.mem_filter.mp hf).2) fun e _ _ => hx e) N.sum_partC_le
  have hq : upSum x Ŝ S = ∑ f ∈ upEdges Ŝ S, x f := rfl
  rw [hq]
  linarith

end ReductionCertificate

end TSPGap

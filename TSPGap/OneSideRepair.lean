/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SharpPaymentHierarchy
import TSPGap.PaymentDefs

/-!
# One-sided repairs with bottom support and exact mass

The component and triangle repairs cost `44` at the existing scaling.
Keep their support on good bottom edges when summing over the hierarchy,
and retain the nested-cut mass `1 - 7η/2` instead of weakening it to `3/4`.
The original hierarchy repair API remains available.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {η β : ℝ} {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}

/-- A nested cut's good mass retains the full geometric lower bound. -/
theorem good_mass_of_nested_sharp {ε : ℝ} {H : Hierarchy (e₀.restrict x₀) e₀ ε}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hx₀ : x₀ ∈ subtourLP n)
    {S' : Finset (Fin n)} (hcyc : H.IsNearCycleCut S')
    {N : NearCycle (e₀.restrict x₀) ε} (hpres : H.Presents N S')
    {i j : Fin (N.k + 3)} (h0 : (0 : Fin (N.k + 3)) ∉ Finset.Icc i j)
    (hne : (N.outerCut \ N.interval i j).Nonempty)
    {d : ℝ} (hS : IsNearMinCut x₀ d (N.interval i j)) :
    1 - ε / 2 ≤ ∑ e ∈ cutEdges (N.interval i j) ∩ Eg, e₀.restrict x₀ e := by
  have havoid : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t) :=
    fun _ ht => hpres.avoids_atom ht
  have hsub := N.interval_subset_outerCut h0
  have hmass := N.one_sub_half_le_sum_sideEdges hx₀ havoid hsub hS hne
  have hgood : N.sideEdges (N.interval i j) ⊆ cutEdges (N.interval i j) ∩ Eg := by
    intro e he
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp he).1,
      hMP.bottom_good e S' (N.sideEdges_subset_edges havoid hsub e he).1
        (hpres.isEdgeParent_of_mem_sideEdges h0 he) hcyc⟩
  exact hmass.trans (Finset.sum_le_sum_of_subset_of_nonneg hgood
    (fun e _ _ => RootEdge.restrict_nonneg hx₀.1 e))

/-- Interior-group support implies support on genuine good bottom edges. -/
theorem bottom_support_of_group_support {ε : ℝ}
    {H : Hierarchy (e₀.restrict x₀) e₀ ε} {μ : TreeDist n (e₀.restrict x₀)}
    {Eg : Finset (Sym2 (Fin n))}
    {s sv : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) {N : NearCycle (e₀.restrict x₀) ε}
    {S' : Finset (Fin n)} (hpres : H.Presents N S') (hcyc : H.IsNearCycleCut S')
    (hsupp : ∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
      sv T e = 0) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n))
    (hne : sv T e ≠ 0) : e ∈ Eg ∧ IsBottomEdge H e := by
  classical
  have hex : ∃ g : Fin (N.k + 3), g ≠ 0 ∧ g + 1 ≠ 0 ∧ e ∈ N.group g := by
    by_contra hc
    push Not at hc
    exact hne (hsupp T e hc)
  obtain ⟨g, hg0, hg1, hge⟩ := hex
  have hp := hpres.isEdgeParent_of_mem_group hg0 hg1 hge
  have hgen := betweenEdges_subset_edgeFinset
    (N.atom_disjoint g (g + 1) (N.ne_add_one g)) hge
  exact ⟨hMP.bottom_good e S' hgen hp hcyc, S', hp, hcyc⟩

/-- The actual hierarchy repair, with its exact nested mass and bottom-only support. -/
theorem exists_slackStar_hierarchy_supported {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hH : F.IsHierarchyOf H)
    (hx₀ : x₀ ∈ subtourLP n) (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S' S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        S' ∈ H.cuts → H.IsNearCycleCut S' → Responsible F H S' S →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ S' S : Finset (Fin n), S' ∈ H.cuts → H.IsNearCycleCut S' →
        Responsible F H S' S → IsRootedNearMinCut e₀ x₀ η S →
        1 - 7 * η / 2 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (44 * η)
            * e₀.restrict x₀ e) ∧
      (∀ T e, s' T e ≠ 0 → e ∈ Eg ∧ IsBottomEdge H e) := by
  classical
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  have hCnn : (0:ℝ) ≤ (2 + η) * β / (1 - 7 * η) :=
    div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  -- every hierarchy cut is near minimum over the LP point itself
  have hconv : ∀ A ∈ H.cuts, IsNearMinCut x₀ (7 * η) A := fun A hA =>
    ⟨(H.nearMin A hA).nonempty, (H.nearMin A hA).ne_univ, by
      rw [← cutSum_restrict (H.avoids A hA)]; exact (H.nearMin A hA).cut_le⟩
  set 𝒩 : Finset (Finset (Fin n)) := H.cuts.filter H.IsNearCycleCut with h𝒩
  have hkey : ∀ p : {S' // S' ∈ 𝒩}, ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (sv : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      H.Presents N p.1 ∧ (∀ T e, 0 ≤ sv T e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        sv T e = 0) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), Responsible F H p.1 S →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + sv T e)) ∧
      (∀ S : Finset (Fin n), Responsible F H p.1 S →
        IsRootedNearMinCut e₀ x₀ η S →
        1 - 7 * η / 2 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => sv T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (44 * η)
            * e₀.restrict x₀ e) := by
    rintro ⟨S', hS'𝒩⟩
    obtain ⟨hS', hcyc⟩ := Finset.mem_filter.mp hS'𝒩
    by_cases hout : ∃ i, F.outerCut i = S'
    · -- a component's outer cut: Appendix A
      obtain ⟨i, hi⟩ := hout
      obtain ⟨N, sv, hpres, hnn, hpay, hexp, hsupp⟩ :=
        OneSideFamily.exists_slackStar_of_index_sharp hx₀ μ hH i (F.relevantAtoms i)
          (fun A hA => F.mem_relevantAtoms.mp hA) hη0 hη hβ0
      have hpres' : H.Presents N S' := hi ▸ hpres
      have hmemS : ∀ S, Responsible F H S' S → IsRootedNearMinCut e₀ x₀ η S →
          S ∈ F.comp i ∪ F.relevantAtoms i := by
        intro S hresp hSnm
        rcases hresp with hchild | ⟨j, hj, hcomp⟩
        · refine Finset.mem_union_right _ (F.mem_relevantAtoms.mpr ?_)
          obtain ⟨h1, h2⟩ := (hH.children_outer i S).mp (by rw [hi]; exact hchild)
          exact ⟨h1, h2, hSnm.nearMin.cut_le⟩
        · have hji : j = i := hH.outer_injective (by rw [hj, hi])
          exact Finset.mem_union_left _ (hji ▸ hcomp)
      refine ⟨N, sv, hpres', hnn, hsupp, fun S T hresp hSnm hodd => ?_,
        fun S hresp hSnm => ?_, fun e => ?_⟩
      · obtain ⟨a, b, hab, h1, h2, h3, hp⟩ := hpay S (hmemS S hresp hSnm)
        exact payment_of_nearCycleCut hMP hx₀ hS' hcyc hpres' hab h1 h2 h3
          hSnm (hnn T) hodd (hp T hodd) hβ0 hxnn
      · obtain ⟨a, b, hab, h1, h2, h3, -⟩ := hpay S (hmemS S hresp hSnm)
        subst hab
        refine good_mass_of_nested_sharp hMP hx₀ hcyc hpres' ?_ ?_ hSnm.nearMin
        · rw [Finset.mem_Icc]
          rintro ⟨hle, -⟩
          exact absurd hle (not_le.mpr h1)
        · exact N.nonempty_outerCut_sdiff_of_proper h1 (Fin.le_last _) h3
      · exact hexp e
    · -- otherwise Fact B.5 leaves only a triangle: Lemma A.13
      have htri : H.IsTriangleCut S' := by
        by_contra hc
        exact hout (hH.exists_index_of_nearCycle S' hS' hcyc hc)
      obtain ⟨X, Y, hX, hY, hXY, hall⟩ := htri
      have hunion : X ∪ Y = S' := by
        refine Finset.Subset.antisymm
          (Finset.union_subset (H.child_subset hX) (H.child_subset hY)) fun v hv => ?_
        rcases H.union_children S' hS' v hv with ⟨a, ha, hva⟩ | hnone
        · rcases hall a ha with rfl | rfl
          · exact Finset.mem_union_left _ hva
          · exact Finset.mem_union_right _ hva
        · exact absurd hX (hnone X)
      have hchild : ∀ a : Finset (Fin n), IsChildOf H.cuts a S' ↔ (a = X ∨ a = Y) :=
        fun a => ⟨fun h => hall a h, fun h => by rcases h with rfl | rfl; exacts [hX, hY]⟩
      obtain ⟨N, sv, hpres, hnn, hpay, hexp, hsupp⟩ :=
        exists_slackStar_triangle_sharp hx₀ μ hunion hchild
          (H.children_disjoint hX hY hXY) (hconv X hX.1) (hconv Y hY.1) (hconv S' hS')
          (H.avoids S' hS')
          hη0 hη hβ0
      have hmemS : ∀ S, Responsible F H S' S → (S = X ∨ S = Y) := by
        intro S hresp
        rcases hresp with hc | ⟨i, hi, -⟩
        · exact hall S hc
        · exact absurd ⟨i, hi⟩ hout
      refine ⟨N, sv, hpres, hnn, hsupp, fun S T hresp hSnm hodd => ?_,
        fun S hresp hSnm => ?_, hexp⟩
      · obtain ⟨a, b, hab, h1, h2, h3, hp⟩ := hpay S (hmemS S hresp)
        exact payment_of_nearCycleCut hMP hx₀ hS' hcyc hpres hab h1 h2 h3 hSnm
          (hnn T) hodd (hp T hodd) hβ0 hxnn
      · obtain ⟨a, b, hab, h1, h2, h3, -⟩ := hpay S (hmemS S hresp)
        subst hab
        refine good_mass_of_nested_sharp hMP hx₀ hcyc hpres ?_ ?_ hSnm.nearMin
        · rw [Finset.mem_Icc]
          rintro ⟨hle, -⟩
          exact absurd hle (not_le.mpr h1)
        · exact N.nonempty_outerCut_sdiff_of_proper h1 (Fin.le_last _) h3
  choose N sv hpres hnn hsupp hpay hgood hexp using hkey
  refine ⟨fun T e => ∑ p : {S' // S' ∈ 𝒩}, sv p T e,
    fun T e => ?_, ?_, ?_, fun e => ?_, ?_⟩
  · exact Finset.sum_nonneg fun p _ => hnn p T e
  · intro S' S T hS' hcyc hresp hSnm hodd
    set p : {S'' // S'' ∈ 𝒩} := ⟨S', Finset.mem_filter.mpr ⟨hS', hcyc⟩⟩ with hp
    refine le_trans (hpay p S T hresp hSnm hodd) (Finset.sum_le_sum fun e _ => ?_)
    have := Finset.single_le_sum (f := fun q : {S'' // S'' ∈ 𝒩} => sv q T e)
      (fun q _ => hnn q T e) (Finset.mem_univ p)
    linarith
  · intro S' S hS' hcyc hresp hSnm
    exact hgood ⟨S', Finset.mem_filter.mpr ⟨hS', hcyc⟩⟩ S hresp hSnm
  · -- at most one near-cycle cut charges any given edge
    have hkeyE : ∀ (p : {S' // S' ∈ 𝒩}) (T : Finset (Sym2 (Fin n))),
        sv p T e ≠ 0 → H.IsEdgeParent e p.1 := by
      intro p T hne
      by_cases hall : ∀ g : Fin ((N p).k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ (N p).group g
      · exact absurd (hsupp p T e hall) hne
      · push Not at hall
        obtain ⟨g, hg0, hg1, hgm⟩ := hall
        exact (hpres p).isEdgeParent_of_mem_group hg0 hg1 hgm
    have huniq : ∀ (p q : {S' // S' ∈ 𝒩}) (T T' : Finset (Sym2 (Fin n))),
        sv p T e ≠ 0 → sv q T' e ≠ 0 → p = q := fun p q T T' hp hq =>
      Subtype.ext (Hierarchy.IsEdgeParent.unique H (hkeyE p T hp) (hkeyE q T' hq))
    rw [μ.expect_sum' Finset.univ fun p T => sv p T e]
    by_cases hex : ∃ (p : {S' // S' ∈ 𝒩}) (T : Finset (Sym2 (Fin n))), sv p T e ≠ 0
    · obtain ⟨p₀, T₀, hp₀⟩ := hex
      have hzero : ∀ p ∈ (Finset.univ : Finset {S' // S' ∈ 𝒩}), p ≠ p₀ →
          μ.expect (fun T => sv p T e) = 0 := by
        intro p _ hne
        have hz : ∀ T, sv p T e = 0 := fun T => by
          by_contra hc
          exact hne (huniq p p₀ T T₀ hc hp₀)
        simp only [hz]
        exact μ.expect_const 0
      rw [Finset.sum_eq_single_of_mem p₀ (Finset.mem_univ p₀) hzero]
      exact hexp p₀ e
    · push Not at hex
      have hall : ∑ p : {S' // S' ∈ 𝒩}, μ.expect (fun T => sv p T e) = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        simp only [hex p]
        exact μ.expect_const 0
      rw [hall]
      exact mul_nonneg (mul_nonneg hCnn (by linarith)) (hxnn e)
  · intro T e hne
    obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact bottom_support_of_group_support hMP (hpres p)
      (Finset.mem_filter.mp p.2).2 (hsupp p) T e hp

end TSPGap

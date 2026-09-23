/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SharpComponentSlack
import TSPGap.SharpTriangleSlack

/-!
# The hierarchy repair at KKO's coefficient 125

The sharp component charge is `44αη`; the triangle costs at most that much.
The existing edge-parent argument keeps different components disjointly
supported. Adding the both-sides repair gives `125ηβxₑ`.

This leaf keeps the original, weaker hierarchy APIs available without
rebuilding the probabilistic payment development.
-/

namespace TSPGap

open Finset
variable {n : ℕ} {η β : ℝ}

theorem exists_slackStar_oneSide_sharp {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : PolygonRep 𝒞) (hcomp : IsOneSideComponent e₀ x₀ η 𝒞)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom ∧ cutSum x₀ A ≤ 2 + η)
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      N.root = P.rootAtom ∧
      (∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
        ↔ A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S ∈ 𝒞 ∪ 𝒜, ∃ i j : Fin (N.k + 3), N.interval i j = S ∧
        0 < i ∧ i ≤ j ∧ ¬ (i = 1 ∧ j = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (i = 1 → N.LeftHappy T) → (j = N.lastIdx → N.RightHappy T) →
          (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (44 * η)
            * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s' T e = 0) := by
  have hαnn : 0 ≤ (2 + η) * β / (1 - 7 * η) :=
    div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  obtain ⟨N, s', hNroot, hNatom, hs'nn, hs'pay, hs'exp, hs'supp⟩ :=
    exists_happySlack_of_oneSideComponent_sharp (α := (2 + η) * β / (1 - 7 * η))
      hx₀ μ P hcomp 𝒜 h𝒜 hαnn hη0 hη
  refine ⟨N, s', hNroot, hNatom, hs'nn, fun S hS => ?_, hs'exp, hs'supp⟩
  obtain ⟨i, j, hij, hp1, hp2, hp3, hpay⟩ := hs'pay S hS
  refine ⟨i, j, hij, hp1, hp2, hp3, fun T hodd hL hR => ?_⟩
  have h := hpay T hodd hL hR
  rwa [alpha_mul_one_sub (by linarith : (7 : ℝ) * η ≠ 1)] at h

theorem OneSideFamily.exists_slackStar_of_index_sharp {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    (hH : F.IsHierarchyOf H) (i : Fin F.N) (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms (F.comp i) ∧ A ≠ F.rootAtom i ∧ cutSum x₀ A ≤ 2 + η)
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      H.Presents N (F.outerCut i) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S ∈ F.comp i ∪ 𝒜, ∃ a b : Fin (N.k + 3), N.interval a b = S ∧
        0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
          (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (44 * η)
            * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s' T e = 0) := by
  obtain ⟨N, s', hNroot, hNatom, hnn, hpay, hexp, hsupp⟩ :=
    exists_slackStar_oneSide_sharp (𝒞 := F.comp i) hx₀ μ (F.rep i) (F.isComp i)
      𝒜 h𝒜 hη0 hη hβ0
  exact ⟨N, s', hH.presents i hNroot hNatom, hnn, hpay, hexp, hsupp⟩

theorem exists_slackStar_triangle_sharp {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    {S' X Y : Finset (Fin n)} (hXY : X ∪ Y = S')
    (hchild : ∀ a : Finset (Fin n), IsChildOf H.cuts a S' ↔ (a = X ∨ a = Y))
    (hd : Disjoint X Y)
    (hX : IsNearMinCut x₀ (7 * η) X) (hY : IsNearMinCut x₀ (7 * η) Y)
    (hS : IsNearMinCut x₀ (7 * η) S') (havoid : AvoidsRootEdge e₀ S')
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      H.Presents N S' ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S : Finset (Fin n), (S = X ∨ S = Y) → ∃ a b : Fin (N.k + 3),
        N.interval a b = S ∧ 0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
          (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (44 * η)
            * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s' T e = 0) := by
  have hαnn : 0 ≤ (2 + η) * β / (1 - 7 * η) :=
    div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  subst hXY
  obtain ⟨N, s', hroot, hatom, hnn, hpay, hexp, hsupp⟩ :=
    exists_happySlack_triangle_sharp (α := (2 + η) * β / (1 - 7 * η))
      hx₀ μ hd hX hY hS havoid hαnn (by linarith)
  refine ⟨N, s',
    H.presents_of_atom_iff (C := fun A => A = X ∨ A = Y) hroot hatom hchild,
    hnn, fun S hS0 => ?_, ?_, hsupp⟩
  · obtain ⟨a, b, hab, h1, h2, h3, hp⟩ := hpay S hS0
    refine ⟨a, b, hab, h1, h2, h3, fun T hodd hL hR => ?_⟩
    have h := hp T hodd hL hR
    rwa [alpha_mul_one_sub (by linarith : (7 : ℝ) * η ≠ 1)] at h
  · intro e
    refine le_trans (hexp e) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : (1.5 : ℝ) * (7 * η) ≤ 44 * η) hαnn)
      (RootEdge.restrict_nonneg hx₀.1 e)

theorem exists_slackStar_hierarchy_sharp {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
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
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (44 * η)
            * e₀.restrict x₀ e) := by
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
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) ∧
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
        refine good_mass_of_nested hMP hx₀ (by linarith) hcyc hpres' ?_ ?_ hSnm.nearMin
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
        refine good_mass_of_nested hMP hx₀ (by linarith) hcyc hpres ?_ ?_ hSnm.nearMin
        · rw [Finset.mem_Icc]
          rintro ⟨hle, -⟩
          exact absurd hle (not_le.mpr h1)
        · exact N.nonempty_outerCut_sdiff_of_proper h1 (Fin.le_last _) h3
  choose N sv hpres hnn hsupp hpay hgood hexp using hkey
  refine ⟨fun T e => ∑ p : {S' // S' ∈ 𝒩}, sv p T e, fun T e => ?_, ?_, ?_, fun e => ?_⟩
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

theorem exists_payment_of_hierarchy_sharp {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hH : F.IsHierarchyOf H)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ S : Finset (Fin n), IsRootedNearMinCut e₀ x₀ η S →
        ¬ CrossedBothSides e₀ x₀ η S → S ≠ e₀.rootCut →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) := by
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  obtain ⟨s2, hs2nn, hs2pay, hs2exp⟩ :=
    exists_slackStar_bothSides e₀ hx₀ μ hη0 (by linarith) (le_of_lt hβ0)
  obtain ⟨sA, hAnn, hApay, hAgood, hAexp⟩ :=
    exists_slackStar_hierarchy_sharp hMP hH hx₀ hη0 (by linarith) (le_of_lt hβ0)
  have hnn' : ∀ (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)), 0 ≤ s2 T e + sA T e :=
    fun T e => add_nonneg (hs2nn T e) (hAnn T e)
  refine ⟨fun T e => s2 T e + sA T e, hnn', ?_, ?_, ?_⟩
  · -- the five types, plus the root cut by parity
    intro S T hTprob hS hodd
    by_cases hroot : S = e₀.rootCut
    · exfalso
      rw [hroot, RootEdge.rootCut, cutEdges_compl,
        card_cut_inter_rootPair hx₀ hx₀e μ hn hTprob] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    · refine payment_of_hierarchy hMP hH (le_of_lt hβ0) hxnn hnn' ?_ ?_ ?_ S T hS hroot hodd
      · intro S₀ T₀ hS₀ hboth hodd₀
        refine le_trans (hs2pay S₀ T₀ hS₀ hboth hodd₀) (Finset.sum_le_sum fun e _ => ?_)
        have := hAnn T₀ e
        linarith
      · intro i S₀ T₀ hmem hS₀ hodd₀
        have hresp : Responsible F H (F.outerCut i) S₀ := by
          rcases hmem with h | h
          · exact Or.inr ⟨i, rfl, h⟩
          · exact Or.inl h
        refine le_trans (hApay (F.outerCut i) S₀ T₀ (hH.outer_mem i)
          (hH.outer_nearCycle i) hresp hS₀ hodd₀) (Finset.sum_le_sum fun e _ => ?_)
        have := hs2nn T₀ e
        linarith
      · intro S₀ S' T₀ hchild hcyc _ hS₀ hodd₀
        refine le_trans (hApay S' S₀ T₀ hchild.2.1 hcyc (Or.inl hchild) hS₀ hodd₀)
          (Finset.sum_le_sum fun e _ => ?_)
        have := hs2nn T₀ e
        linarith
  · -- the cost: Theorem 5.2's `18αη` and Appendix A's `44αη`
    intro e
    have hb1 : (2 + η) * β / (1 - η) ≤ 2.01 * β := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hb2 : (2 + η) * β / (1 - 7 * η) ≤ 2.01 * β := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hx := hxnn e
    have hηx : 0 ≤ η * e₀.restrict x₀ e := mul_nonneg (le_of_lt hη0) hx
    have k1 : 0 ≤ (2.01 * β - (2 + η) * β / (1 - η)) * (η * e₀.restrict x₀ e) :=
      mul_nonneg (sub_nonneg.mpr hb1) hηx
    have k2 : 0 ≤ (2.01 * β - (2 + η) * β / (1 - 7 * η)) * (η * e₀.restrict x₀ e) :=
      mul_nonneg (sub_nonneg.mpr hb2) hηx
    have k3 : 0 ≤ η * β * e₀.restrict x₀ e :=
      mul_nonneg (mul_nonneg (le_of_lt hη0) (le_of_lt hβ0)) hx
    have h1 := hs2exp e
    have h2 := hAexp e
    have hsum : μ.expect (fun T => s2 T e + sA T e)
        = μ.expect (fun T => s2 T e) + μ.expect (fun T => sA T e) :=
      μ.expect_add _ _
    rw [hsum]
    nlinarith [k1, k2, k3, h1, h2]
  · -- clause (iv)
    intro S hS hboth hroot
    rcases hH.classify hS hroot with hb | ⟨S', hchild, hdeg⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ |
      ⟨S', hchild, hcyc, -⟩
    · exact absurd hb hboth
    · exact hMP.good_mass S S' hchild hdeg
    · exact hAgood (F.outerCut i) S (hH.outer_mem i) (hH.outer_nearCycle i)
        (Or.inr ⟨i, rfl, hi⟩) hS
    · exact hAgood (F.outerCut i) S (hH.outer_mem i) (hH.outer_nearCycle i)
        (Or.inl hi) hS
    · exact hAgood S' S hchild.2.1 hcyc (Or.inl hchild) hS

end TSPGap

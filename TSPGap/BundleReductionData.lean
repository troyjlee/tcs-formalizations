/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleTopThinningDensity
import TSPGap.PolygonBottomGuarantees

/-!
# Reduction vectors with an explicit bundle goodness policy

Top thinnings on arbitrary pieces and base bottom thinnings share a common
mass. The vector retains its exact top and bottom expectations, support at
even endpoints, and pointwise bounds. Bottom guarantees keep all polygon
parameters and the complete selection witness. Legacy conversions preserve
the actual vector.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace TopThinningsOn
variable {G : BundleGoodnessPolicy} {R : EdgeRefinement x Dr ε₁}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {p : ℝ}
  {P : R.DegreePartitionsOn H} (Θ : G.TopThinningsOn R H μ S p P)


open Classical in
/-- **The reduction of the edge `g` at the cut `S`**, on pieces:
`(τ x_g / 2)(ρ̂_{f,u} + ρ̂_{f,u'})` for `g ∈ f = (u, u')`. -/
noncomputable def reduction (τ : ℝ) (Ť : Finset R.Piece) (g : Sym2 (Fin n)) : ℝ :=
  ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
    if g ∈ betweenEdges u u' then τ * x g / 2 * Θ.rho u u' Ť else 0

open Classical in
/-- The two-orientation formula on an edge of the bundle `E(a,b)`. -/
theorem reduction_eq {a b : Finset (Fin n)} (ha : a ∈ H.children S) (hb : b ∈ H.children S)
    (hab : a ≠ b) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges a b) (τ : ℝ)
    (Ť : Finset R.Piece) :
    Θ.reduction τ Ť g = τ * x g / 2 * (Θ.rho a b Ť + Θ.rho b a Ť) := by
  unfold reduction
  rw [H.sum_ordered_pairs_eq ha hb hab hg (fun u u' => τ * x g / 2 * Θ.rho u u' Ť)]
  ring

open Classical in
/-- An edge in no bundle of `S` is not reduced at `S`. -/
theorem reduction_eq_zero_of_not {g : Sym2 (Fin n)}
    (h : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → g ∉ betweenEdges a b) (τ : ℝ)
    (Ť : Finset R.Piece) : Θ.reduction τ Ť g = 0 := by
  unfold reduction
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun u' hu' => ?_
  rw [if_neg (h u hu u' (Finset.mem_of_mem_erase hu') (Ne.symm (Finset.ne_of_mem_erase hu')))]

open Classical in
theorem reduction_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (Ť : Finset R.Piece) : 0 ≤ Θ.reduction τ Ť g := by
  unfold reduction
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => ?_
  split_ifs
  · have := Θ.rho_nonneg u u' Ť
    positivity
  · exact le_rfl

open Classical in
/-- `r_g ≤ τ x_g`. -/
theorem reduction_le {τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (Ť : Finset R.Piece) : Θ.reduction τ Ť g ≤ τ * x g := by
  by_cases h : ∃ a ∈ H.children S, ∃ b ∈ H.children S, a ≠ b ∧ g ∈ betweenEdges a b
  · obtain ⟨a, ha, b, hb, hab, hg⟩ := h
    rw [Θ.reduction_eq ha hb hab hg]
    have h1 := Θ.rho_le_one a b Ť
    have h2 := Θ.rho_le_one b a Ť
    have h0 := Θ.rho_nonneg a b Ť
    have h0' := Θ.rho_nonneg b a Ť
    nlinarith [mul_nonneg hτ hxg]
  · rw [Θ.reduction_eq_zero_of_not]
    · positivity
    · intro a ha b hb hab hg
      exact h ⟨a, ha, b, hb, hab, hg⟩

open Classical in
/-- **No reduction on `δ(u)` at an odd atom `u`**, in the piece count. -/
theorem reduction_eq_zero_of_odd {u : Finset (Fin n)} (hu : u ∈ H.children S)
    {Ť : Finset R.Piece} (hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card) {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges u) (τ : ℝ) : Θ.reduction τ Ť g = 0 := by
  unfold reduction
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  have hbmem := Finset.mem_of_mem_erase hb
  split_ifs with hab
  · obtain ⟨p, hp, q, hq, rfl⟩ := mem_betweenEdges_iff.mp hab
    obtain ⟨p', hp', q', hq', h⟩ := mem_cutEdges_iff''.mp hg
    rw [Finset.mem_compl] at hq'
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hau : a = u := H.eq_of_mem_children_of_mem ha hu hp hp'
      subst hau
      rw [Θ.rho_eq_zero_of_odd hodd, mul_zero]
    · have hbu : b = u := H.eq_of_mem_children_of_mem hbmem hu hq hp'
      subst hbu
      rw [Θ.rho_eq_zero_of_odd' hodd, mul_zero]
  · rfl

open Classical in
/-- **The top reduction vanishes on a bad bundle**, pointwise. -/
theorem reduction_eq_zero_of_bad_bundle {U w : Finset (Fin n)}
    (hU : U ∈ H.children S) (hw : w ∈ H.children S) (hne : U ≠ w)
    (hbad : ¬ G.IsGood μ U w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges U w) (τ : ℝ) (Ť : Finset R.Piece) :
    Θ.reduction τ Ť g = 0 := by
  have hbad' : ¬ G.IsGood μ w U := fun h => hbad (isGood_comm.mp h)
  rw [Θ.reduction_eq hU hw hne hg τ Ť,
    Θ.rho_eq_zero_of_not_good (fun h => hbad h.2.2.2) Ť,
    Θ.rho_eq_zero_of_not_good (fun h => hbad' h.2.2.2) Ť]
  ring

open Classical in
/-- The same, summed over the fiber. -/
theorem sum_reduction_bad_fiber {U w u : Finset (Fin n)}
    (hU : U ∈ H.children S) (hw : w ∈ H.children S) (hne : U ≠ w)
    (hbad : ¬ G.IsGood μ U w) (τ : ℝ) (Ť : Finset R.Piece) :
    ∑ g ∈ betweenEdges U w ∩ cutEdges u, Θ.reduction τ Ť g = 0 :=
  Finset.sum_eq_zero fun _ hg =>
    Θ.reduction_eq_zero_of_bad_bundle hU hw hne hbad (Finset.mem_inter.mp hg).1 τ Ť

open Classical in
/-- Exact agreement with the original top reduction under the legacy policy. -/
theorem reduction_legacy {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {S : Finset (Fin n)} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (Θ : (legacy h).TopThinningsOn R H μ S a P) (τ : ℝ) (T : Finset R.Piece)
    (g : Sym2 (Fin n)) : Θ.reduction τ T g = Θ.toLegacy.reduction τ T g := rfl

end TopThinningsOn

open Classical in
/-- **The reduction data of the hierarchy on pieces**: piece top thinnings at
every degree cut, base bottom thinnings at every near-cycle cut. -/
structure ReductionDataOn (G : BundleGoodnessPolicy) (R : EdgeRefinement x Dr ε₁)
    (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (p : ℝ) (P : R.DegreePartitionsOn H) where
  top : ∀ S, DegreeCutData H S → G.TopThinningsOn R H μ S p P
  bottom : ∀ S, S ∈ H.cuts → H.IsNearCycleCut S → BottomThinning H μ S p

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {G : BundleGoodnessPolicy} {p : ℝ}
  {P : R.DegreePartitionsOn H} (D : G.ReductionDataOn R H μ p P)

open Classical in
/-- The reduction of the edge `g` at the cut `S`, if `S` is its edge parent:
the bottom density is read on the projection. -/
noncomputable def reductionAt (β τ : ℝ) (Ť : Finset R.Piece) (g : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  if hS : H.IsEdgeParent g S then
    (if hcyc : H.IsNearCycleCut S then β * x g * (D.bottom S hS.1 hcyc).rho (R.project Ť)
      else if hdeg : DegreeCutData H S then (D.top S hdeg).reduction τ Ť g else 0)
  else 0

open Classical in
/-- **The reduction vector on pieces**, summed over the cuts of the hierarchy. -/
noncomputable def reduction (β τ : ℝ) (Ť : Finset R.Piece) (g : Sym2 (Fin n)) : ℝ :=
  ∑ S ∈ H.cuts, D.reductionAt β τ Ť g S

open Classical in
theorem reductionAt_of_not {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent g S) : D.reductionAt β τ Ť g S = 0 := by
  unfold reductionAt
  rw [dif_neg h]

open Classical in
/-- The reduction is the term at the edge parent. -/
theorem reduction_eq_of_isEdgeParent {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) :
    D.reduction β τ Ť g = D.reductionAt β τ Ť g S := by
  unfold reduction
  refine Finset.sum_eq_single_of_mem S hS.1 fun S' _ hne => ?_
  exact D.reductionAt_of_not fun h => hne (Hierarchy.IsEdgeParent.unique H h hS)

open Classical in
/-- **Bottom edges**: `r_g = β x_g ρ_S(project Ť)` when `p(g) = S` is a near-cycle cut. -/
theorem reduction_bottom {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    D.reduction β τ Ť g = β * x g * (D.bottom S hS.1 hcyc).rho (R.project Ť) := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_pos hcyc]

open Classical in
/-- **Top edges**: `r_g` is the piece reduction at the degree cut `p(g) = S`. -/
theorem reduction_top {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hdeg : DegreeCutData H S) :
    D.reduction β τ Ť g = (D.top S hdeg).reduction τ Ť g := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hdeg.notNearCycle, dif_pos hdeg]

open Classical in
/-- `E[r_e] = β·p·x_e` on a bottom edge, under the lifted law. -/
theorem expect_reduction_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť e) = β * p * x e := by
  have hpt : (fun Ť => D.reduction β τ Ť e)
      = fun Ť => β * x e * (D.bottom S hS.1 hcyc).rho (R.project Ť) := by
    funext Ť
    rw [D.reduction_bottom hS hcyc]
  rw [hpt, R.liftExpect_mul_left, R.liftExpect_project, (D.bottom S hS.1 hcyc).expect_rho]
  ring

open Classical in
/-- `E[r_e] = τ·p·x_e` on a good top bundle. -/
theorem expect_reduction_top {β τ : ℝ} {S a b : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b)
    (hgood : G.IsGood μ a b) {e : Sym2 (Fin n)} (he : e ∈ betweenEdges a b) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť e) = τ * p * x e := by
  have hSe : H.IsEdgeParent e S :=
    H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb) hab he
  have hpt : (fun Ť => D.reduction β τ Ť e)
      = fun Ť => τ * x e / 2 * (D.top S hdeg).rho a b Ť
          + τ * x e / 2 * (D.top S hdeg).rho b a Ť := by
    funext Ť
    rw [D.reduction_top hSe hdeg, (D.top S hdeg).reduction_eq ha hb hab he]
    ring
  rw [hpt, R.liftExpect_add, R.liftExpect_mul_left, R.liftExpect_mul_left,
    (D.top S hdeg).expect_rho ha hb hab hgood,
    (D.top S hdeg).expect_rho hb ha (Ne.symm hab) (isGood_comm.mp hgood)]
  ring

open Classical in
/-- An edge whose parent is neither a near-cycle cut nor a degree cut is not
reduced. -/
theorem reduction_eq_zero_of_neither {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : D.reduction β τ Ť g = 0 := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hcyc, dif_neg hdeg]

open Classical in
/-- An edge with no edge parent is not reduced. -/
theorem reduction_eq_zero_of_noParent {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent g S) : D.reduction β τ Ť g = 0 := by
  unfold reduction
  exact Finset.sum_eq_zero fun S _ => D.reductionAt_of_not (h S)

open Classical in
theorem reductionAt_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (Ť : Finset R.Piece) (S : Finset (Fin n)) :
    0 ≤ D.reductionAt β τ Ť g S := by
  unfold reductionAt
  split_ifs with hS hcyc hdeg
  · have := (D.bottom S hS.1 hcyc).rho_nonneg (R.project Ť)
    positivity
  · exact (D.top S hdeg).reduction_nonneg hτ hxg Ť
  · exact le_rfl
  · exact le_rfl

open Classical in
theorem reduction_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (Ť : Finset R.Piece) : 0 ≤ D.reduction β τ Ť g :=
  Finset.sum_nonneg fun S _ => D.reductionAt_nonneg hβ hτ hxg Ť S

open Classical in
/-- **`r_g ≤ β x_g`** for `τ ≤ β`. -/
theorem reduction_le {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (Ť : Finset R.Piece) : D.reduction β τ Ť g ≤ β * x g := by
  have hβ : 0 ≤ β := hτ.trans hτβ
  by_cases h : ∃ S, H.IsEdgeParent g S
  · obtain ⟨S, hS⟩ := h
    rw [D.reduction_eq_of_isEdgeParent hS]
    unfold reductionAt
    rw [dif_pos hS]
    split_ifs with hcyc hdeg
    · have h1 := (D.bottom S hS.1 hcyc).rho_le_one (R.project Ť)
      have h0 := (D.bottom S hS.1 hcyc).rho_nonneg (R.project Ť)
      nlinarith [mul_nonneg hβ hxg]
    · calc (D.top S hdeg).reduction τ Ť g ≤ τ * x g := (D.top S hdeg).reduction_le hτ hxg Ť
        _ ≤ β * x g := mul_le_mul_of_nonneg_right hτβ hxg
    · positivity
  · rw [D.reduction_eq_zero_of_noParent fun S hS => h ⟨S, hS⟩]
    positivity

open Classical in
/-- **No reduction on `δ(u)` at an odd atom `u` of a degree cut**, in the piece
count, for the edges whose parent is that cut. -/
theorem reduction_eq_zero_of_odd {β τ : ℝ} {S u : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) {Ť : Finset R.Piece}
    (hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
    {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u) (hS : H.IsEdgeParent g S) :
    D.reduction β τ Ť g = 0 := by
  rw [D.reduction_top hS hdeg]
  exact (D.top S hdeg).reduction_eq_zero_of_odd hu hodd hg τ

/-! #### The certificates, carried alongside -/

open Classical in
/-- **The top certificate on pieces**: rectangularity in the piece sense at
every degree cut. -/
structure HasTopRectangularOn : Prop where
  top_rect : ∀ S, ∀ hS : DegreeCutData H S, G.TopRectangularOn R (D.top S hS)

open Classical in
/-- Bottom guarantees keep the selection tolerance, mass floor and both bounds explicit. -/
structure HasBottomGuarantees (ζ minMass oddBound unhappyBound : ℝ) : Prop where
  bottom_guar : ∀ S, ∀ hS : S ∈ H.cuts, ∀ hcyc : H.IsNearCycleCut S,
    PolygonBottomGuarantees ζ minMass oddBound unhappyBound H μ S p (D.bottom S hS hcyc)

variable {D} {ζ minMass oddBound unhappyBound : ℝ}

open Classical in
theorem topRect (h : D.HasTopRectangularOn) (S : Finset (Fin n)) (hS : DegreeCutData H S) :
    G.TopRectangularOn R (D.top S hS) := h.top_rect S hS

open Classical in
theorem bottomGuar (h : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) :
    PolygonBottomGuarantees ζ minMass oddBound unhappyBound H μ S p (D.bottom S hS hcyc) :=
  h.bottom_guar S hS hcyc

open Classical in
theorem bottomPolygonWitness (h : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    (S : Finset (Fin n))
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    Nonempty (PolygonBottomWitness ζ minMass H μ S p (D.bottom S hS hcyc)) :=
  (h.bottom_guar S hS hcyc).polygonWitness

open Classical in
/-- The bottom odd-parity bound in the piece expectation form: the bottom
density is a projected function and the odd piece count is the odd edge
count on the support, so it is the base bound. -/
theorem expect_rho_bottom_odd_le (h : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) :
    R.liftExpect μ (fun Ť => (D.bottom S hS hcyc).rho (R.project Ť)
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ oddBound * p := by
  rw [R.liftExpect_project_odd μ (D.bottom S hS hcyc).rho (cutEdges u)]
  have h1 := (D.bottom S hS hcyc).expect_rho_le ((h.bottom_guar S hS hcyc).odd_le u hu hlt)
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => (D.bottom S hS hcyc).rho T * z)
    (ite_instance_congr _ _ _ (1 : ℝ) 0)

open Classical in
/-- Left unhappiness keeps its separate parameter under the lifted law. -/
theorem expect_rho_bottom_notLeftHappy_le
    (h : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) (K : NearCycle x εη) (hK : H.Presents K u) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if ¬ K.LeftHappy (R.project T) then 1 else 0) ≤ unhappyBound * p := by
  have heq := R.liftExpect_project μ (fun T => (D.bottom S hS hcyc).rho T *
    if ¬ K.LeftHappy T then 1 else 0)
  rw [heq]
  have h1 := (D.bottom S hS hcyc).expect_rho_le
    ((h.bottom_guar S hS hcyc).notLeftHappy_le u hu hlt K hK)
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => (D.bottom S hS hcyc).rho T * z)
    (ite_instance_congr _ _ _ (1 : ℝ) 0)

open Classical in
/-- The same explicit unhappiness bound holds on the right. -/
theorem expect_rho_bottom_notRightHappy_le
    (h : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) (K : NearCycle x εη) (hK : H.Presents K u) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if ¬ K.RightHappy (R.project T) then 1 else 0) ≤ unhappyBound * p := by
  have heq := R.liftExpect_project μ (fun T => (D.bottom S hS hcyc).rho T *
    if ¬ K.RightHappy T then 1 else 0)
  rw [heq]
  have h1 := (D.bottom S hS hcyc).expect_rho_le
    ((h.bottom_guar S hS hcyc).notRightHappy_le u hu hlt K hK)
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => (D.bottom S hS hcyc).rho T * z)
    (ite_instance_congr _ _ _ (1 : ℝ) 0)

variable (D)

/-! #### The root tail carries no reduction -/

open Classical in
/-- An edge of the root tail has zero reduction: it has no edge parent at all. -/
theorem reduction_eq_zero_of_mem_root_tail {u : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hg : g ∈ tail u e₀.rootCut) (β τ : ℝ) (Ť : Finset R.Piece) :
    D.reduction β τ Ť g = 0 :=
  Finset.sum_eq_zero fun S _ =>
    D.reductionAt_of_not (not_isEdgeParent_of_mem_root_tail H hg S)

open Classical in
/-- Summed over the root tail. -/
theorem sum_reduction_root_tail (u : Finset (Fin n)) (β τ : ℝ) (Ť : Finset R.Piece) :
    ∑ g ∈ tail u e₀.rootCut, D.reduction β τ Ť g = 0 :=
  Finset.sum_eq_zero fun _ hg => D.reduction_eq_zero_of_mem_root_tail hg β τ Ť

open Classical in
/-- And in the expectation form Lemma 7.3 sums. -/
theorem sum_expect_reduction_root_tail_odd (u : Finset (Fin n)) (β τ : ℝ) :
    ∑ g ∈ tail u e₀.rootCut,
        R.liftExpect μ (fun Ť => D.reduction β τ Ť g
          * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) = 0 := by
  refine Finset.sum_eq_zero fun g hg => ?_
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_eq_zero fun Ť _ => ?_
  simp [D.reduction_eq_zero_of_mem_root_tail hg β τ Ť]

/-- Recover the original datum without changing the thinnings. -/
def toLegacy {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : (legacy h).ReductionDataOn R H μ a P) : TSPGap.ReductionDataOn R H μ h a P :=
  ⟨fun S hS => (D.top S hS).toLegacy, D.bottom⟩

/-- Regard the original datum as data for the legacy policy. -/
def ofLegacy {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : TSPGap.ReductionDataOn R H μ h a P) : (legacy h).ReductionDataOn R H μ a P :=
  ⟨fun S hS => TopThinningsOn.ofLegacy (D.top S hS), D.bottom⟩

theorem toLegacy_ofLegacy {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : TSPGap.ReductionDataOn R H μ h a P) : (ofLegacy D).toLegacy = D := by
  cases D; rfl

theorem ofLegacy_toLegacy {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : (legacy h).ReductionDataOn R H μ a P) : ofLegacy D.toLegacy = D := by
  cases D; rfl

/-- Legacy conversion preserves the full reduction vector pointwise. -/
theorem reduction_legacy {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : (legacy h).ReductionDataOn R H μ a P) (β τ : ℝ) (T : Finset R.Piece)
    (g : Sym2 (Fin n)) : D.reduction β τ T g = D.toLegacy.reduction β τ T g := rfl

/-- Both endpoint rectangles survive the legacy conversion. -/
theorem hasTopRectangularOn_legacy_iff {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : (legacy h).ReductionDataOn R H μ a P) :
    D.HasTopRectangularOn ↔ D.toLegacy.HasTopRectangularOn := by
  constructor
  · intro hd
    exact ⟨fun S hS => (TopRectangularOn.legacy_iff (D.top S hS)).mp (hd.top_rect S hS)⟩
  · intro hd
    exact ⟨fun S hS => (TopRectangularOn.legacy_iff (D.top S hS)).mpr (hd.top_rect S hS)⟩

/-- Exact legacy specialization of the full bottom certificate, including its witness. -/
theorem hasBottomGuarantees_legacy_iff {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (D : (legacy h).ReductionDataOn R H μ a P) :
    D.HasBottomGuarantees 0.00025 1.5e-9 0.5678 0.56797 ↔ D.toLegacy.HasBottomGuarantees := by
  constructor
  · intro hd
    exact ⟨fun S hS hcyc => PolygonBottomGuarantees.legacy_iff.mp (hd.bottom_guar S hS hcyc)⟩
  · intro hd
    exact ⟨fun S hS hcyc => PolygonBottomGuarantees.legacy_iff.mpr (hd.bottom_guar S hS hcyc)⟩

end ReductionDataOn
end TSPGap.BundleGoodnessPolicy

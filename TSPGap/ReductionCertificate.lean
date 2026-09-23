/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaSevenThreeConsumer

/-!
# The partition-free reduction certificate

Everything the payment layer consumes of the reduction events is **linear in
the densities**, except the uniformity of the top thinnings — which only
Lemma 7.3 and Claims 7.4/7.5 use, and which does not survive the projection
from pieces to base trees.  This file isolates the consumed content as a
certificate on base trees, with **no degree partition, no thinning event and
no uniformity**:

* `TopDensities H μ S ε₂ p` — at a degree cut `S`, pair-indexed densities
  `ρ_{u,u'}` with `0 ≤ ρ ≤ 1`, zero on bad pairs and on odd endpoint cuts (in
  either orientation), exact expectation `E[ρ] = p` on good pairs, and case
  (iii) coherence in its pushed form: at an atom in neither case 1 nor the
  recorded case 2, two half bundles with the *same* density at the atom, each
  supported on the 2-2-2 happy event.

  ⚠️ **Scope.**  This certificate is the interface of the Lemma 7.2/7.3 payment
  endpoint (`Lemma76.lean`, `SlackVector.lean` … `MainPaymentCore.lean`), and
  nothing more.  `caseTwo` is a bare predicate with **no specification** — it
  records which atoms the construction treated as case 2 of Theorem 5.28, a
  partition-bound fact the certificate cannot express — so `coherent` is
  *not* a case-(iii) obligation the certificate enforces: the instance with
  `caseTwo := fun _ => True` discharges it trivially (audit round 25).  The
  wrong-side masses of case 3 (`x_{e(B)}, x_{f(A)} ≤ ε₂`) are likewise stated
  against the degree partition and stay with it.  §7.2 (Lemmas 7.8–7.11) does
  **not** consume this certificate's case data: it keeps the piece reduction
  data `ReductionDataOn` in hand and reads the case split, the wrong-side
  masses and the polygon happiness from a provenance sidecar built directly
  from the piece top thinnings, through the compatibility of the piece degree
  partition with the polygon partition.  Only its conclusion — the bottom
  estimate `E[I_S] ≤ βp − c` — crosses to this certificate.
* `ReductionCertificate H μ ε₂ p` — top densities at every degree cut, base
  bottom thinnings at every near-cycle cut; the reduction vector by the same
  summation formulas, with `0 ≤ r_g ≤ τ x_g` (top) and `≤ β x_g`, the exact
  expectations, and the odd-parity reduction mass `oddReductionMass` with its
  inactive/bottom/good-top bounds.
* `HasBottomGuarantees` (unchanged) and `HasOddMassBounds` — Lemma 7.3's
  odd-mass estimate at the parameters `β, τ`, carried as a certificate.
* `ReductionData.toCertificate` — the base data are a certificate, with the
  reduction vector unchanged and `HasOddMassBounds` from `lemma_7_3`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### The averaged top densities at a degree cut -/

/-- **The pair-indexed top densities at the cut `S`**, partition-free. -/
structure TopDensities (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n))
    (ε₂ p : ℝ) where
  /-- `ρ_{e,u}`: the density of the ordered pair `(u, u')` on the tree `T`. -/
  rho : Finset (Fin n) → Finset (Fin n) → Finset (Sym2 (Fin n)) → ℝ
  rho_nonneg : ∀ u u' T, 0 ≤ rho u u' T
  rho_le_one : ∀ u u' T, rho u u' T ≤ 1
  /-- Outside the good ordered pairs of atoms the density is zero. -/
  rho_eq_zero_of_not_good : ∀ u u',
    ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u') →
    ∀ T, rho u u' T = 0
  /-- `E[ρ_{e,u}] = p` on a good ordered pair. -/
  expect_rho : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → IsGoodBundle μ ε₂ u u' →
    μ.expect (rho u u') = p
  /-- No reduction at an odd atom, at the reducing endpoint. -/
  rho_eq_zero_of_odd : ∀ u u' T, Odd (T ∩ cutEdges u).card → rho u u' T = 0
  /-- Nor at the other endpoint. -/
  rho_eq_zero_of_odd' : ∀ u u' T, Odd (T ∩ cutEdges u).card → rho u' u T = 0
  /-- The atoms the construction treated as case 2 of Theorem 5.28.  ⚠️ A bare
  predicate, unspecified: the case is partition-bound and the certificate is
  partition-free.  Consumers needing the case split use the piece data. -/
  caseTwo : Finset (Fin n) → Prop
  /-- **Case (iii) coherence**, pushed: at an atom in neither case 1 nor the
  recorded case 2, two half bundles `e ≠ f` whose densities at `u` coincide and
  are supported on the 2-2-2 happy event.  ⚠️ Gated on the unspecified
  `caseTwo`, hence not an obligation this certificate enforces (see the module
  docstring); carried as provenance, consumed by no theorem. -/
  coherent : ∀ u ∈ H.children S, ¬ BadCase H μ ε₂ S u → ¬ caseTwo u →
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f
      ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
      ∧ (∀ T, rho u e T ≠ 0 → TwoTwoTwoHappy e u f T)
      ∧ (∀ T, rho u f T ≠ 0 → TwoTwoTwoHappy e u f T)
      ∧ rho u f = rho u e

namespace TopDensities

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ p : ℝ}
  (Θ : TopDensities H μ S ε₂ p)

/-- **The reduction of the edge `g` at the cut `S`**:
`(τ x_g / 2)(ρ_{f,u} + ρ_{f,u'})` for `g ∈ f = (u, u')`, as an ordered-pair sum. -/
noncomputable def reduction (τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : ℝ :=
  ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
    if g ∈ betweenEdges u u' then τ * x g / 2 * Θ.rho u u' T else 0

/-- The two-orientation formula on an edge of the bundle `E(a,b)`. -/
theorem reduction_eq {a b : Finset (Fin n)} (ha : a ∈ H.children S) (hb : b ∈ H.children S)
    (hab : a ≠ b) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges a b) (τ : ℝ)
    (T : Finset (Sym2 (Fin n))) :
    Θ.reduction τ T g = τ * x g / 2 * (Θ.rho a b T + Θ.rho b a T) := by
  unfold reduction
  rw [H.sum_ordered_pairs_eq ha hb hab hg (fun u u' => τ * x g / 2 * Θ.rho u u' T)]
  ring

/-- An edge in no bundle of `S` is not reduced at `S`. -/
theorem reduction_eq_zero_of_not {g : Sym2 (Fin n)}
    (h : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → g ∉ betweenEdges a b) (τ : ℝ)
    (T : Finset (Sym2 (Fin n))) : Θ.reduction τ T g = 0 := by
  unfold reduction
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun u' hu' => ?_
  rw [if_neg (h u hu u' (Finset.mem_of_mem_erase hu') (Ne.symm (Finset.ne_of_mem_erase hu')))]

theorem reduction_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (T : Finset (Sym2 (Fin n))) : 0 ≤ Θ.reduction τ T g := by
  unfold reduction
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => ?_
  split_ifs
  · have := Θ.rho_nonneg u u' T
    positivity
  · exact le_rfl

/-- `r_g ≤ τ x_g`. -/
theorem reduction_le {τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (T : Finset (Sym2 (Fin n))) : Θ.reduction τ T g ≤ τ * x g := by
  by_cases h : ∃ a ∈ H.children S, ∃ b ∈ H.children S, a ≠ b ∧ g ∈ betweenEdges a b
  · obtain ⟨a, ha, b, hb, hab, hg⟩ := h
    rw [Θ.reduction_eq ha hb hab hg]
    have h1 := Θ.rho_le_one a b T
    have h2 := Θ.rho_le_one b a T
    have h0 := Θ.rho_nonneg a b T
    have h0' := Θ.rho_nonneg b a T
    nlinarith [mul_nonneg hτ hxg]
  · rw [Θ.reduction_eq_zero_of_not]
    · positivity
    · intro a ha b hb hab hg
      exact h ⟨a, ha, b, hb, hab, hg⟩

/-- **No reduction on `δ(u)` at an odd atom `u`.** -/
theorem reduction_eq_zero_of_odd {u : Finset (Fin n)} (hu : u ∈ H.children S)
    {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges u).card) {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges u) (τ : ℝ) : Θ.reduction τ T g = 0 := by
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
      rw [Θ.rho_eq_zero_of_odd _ _ _ hodd, mul_zero]
    · have hbu : b = u := H.eq_of_mem_children_of_mem hbmem hu hq hp'
      subst hbu
      rw [Θ.rho_eq_zero_of_odd' _ _ _ hodd, mul_zero]
  · rfl

/-- **The top reduction vanishes on a bad bundle**, pointwise. -/
theorem reduction_eq_zero_of_bad_bundle {U w : Finset (Fin n)}
    (hU : U ∈ H.children S) (hw : w ∈ H.children S) (hne : U ≠ w)
    (hbad : ¬ IsGoodBundle μ ε₂ U w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges U w) (τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    Θ.reduction τ T g = 0 := by
  have hbad' : ¬ IsGoodBundle μ ε₂ w U := fun h => hbad (isGoodBundle_comm.mp h)
  rw [Θ.reduction_eq hU hw hne hg τ T,
    Θ.rho_eq_zero_of_not_good _ _ (fun h => hbad h.2.2.2) T,
    Θ.rho_eq_zero_of_not_good _ _ (fun h => hbad' h.2.2.2) T]
  ring

/-- The same, summed over the fiber. -/
theorem sum_reduction_bad_fiber {U w u : Finset (Fin n)}
    (hU : U ∈ H.children S) (hw : w ∈ H.children S) (hne : U ≠ w)
    (hbad : ¬ IsGoodBundle μ ε₂ U w) (τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    ∑ g ∈ betweenEdges U w ∩ cutEdges u, Θ.reduction τ T g = 0 :=
  Finset.sum_eq_zero fun _ hg =>
    Θ.reduction_eq_zero_of_bad_bundle hU hw hne hbad (Finset.mem_inter.mp hg).1 τ T

end TopDensities

/-! ### The base thinnings are densities -/

namespace TopThinnings

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ p ε₁ : ℝ}
  {P : DegreePartitions H ε₁} (Θ : TopThinnings H μ S ε₂ p ε₁ P)

/-- A nonzero density comes from a nonzero thinning. -/
theorem thin_ne_zero_of_rho_ne_zero {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : Θ.rho u u' T ≠ 0) : Θ.thin u u' T ≠ 0 := by
  intro h0
  apply h
  unfold TopThinnings.rho density
  split_ifs with hw
  · rfl
  · rw [h0, zero_div]

/-- **The base top thinnings, read as densities.**  `caseTwo` is Theorem 5.28's
case 2 at the degree partition, and the coherence is `TopThinnings.coherent`
with the thinning event forgotten. -/
noncomputable def toDensities : TopDensities H μ S ε₂ p where
  rho := Θ.rho
  rho_nonneg := Θ.rho_nonneg
  rho_le_one := Θ.rho_le_one
  rho_eq_zero_of_not_good := fun u u' h T => Θ.rho_eq_zero_of_not_good h T
  expect_rho := fun u hu u' hu' huu' hg => Θ.expect_rho hu hu' huu' hg
  rho_eq_zero_of_odd := fun _ _ _ hodd => Θ.rho_eq_zero_of_odd hodd
  rho_eq_zero_of_odd' := fun _ _ _ hodd => Θ.rho_eq_zero_of_odd' hodd
  caseTwo := fun u => ∃ hu : u ∈ H.children S,
    TwoOneOneCase H μ ε₂ S u p (P.get u (H.mem_cuts_of_mem_children hu))
  coherent := by
    intro u hu hnb hn2
    obtain ⟨e, he, f, hf, hne, hhe, hhf, -, -, hiffe, hifff, hthin⟩ :=
      Θ.coherent u hu hnb (fun h => hn2 ⟨hu, h⟩)
    refine ⟨e, he, f, hf, hne, hhe, hhf, fun T hT => ?_, fun T hT => ?_, ?_⟩
    · have h1 := Θ.thin_ne_zero_of_rho_ne_zero hT
      have hgp := Θ.goodPair_of_thin_ne_zero h1
      exact (hiffe T).mp ((Θ.uniform u hgp.1 e hgp.2.1 hgp.2.2.1 hgp.2.2.2).support T h1)
    · have h1 := Θ.thin_ne_zero_of_rho_ne_zero hT
      have hgp := Θ.goodPair_of_thin_ne_zero h1
      exact (hifff T).mp ((Θ.uniform u hgp.1 f hgp.2.1 hgp.2.2.1 hgp.2.2.2).support T h1)
    · funext T
      unfold TopThinnings.rho
      rw [hthin]

@[simp] theorem toDensities_rho : Θ.toDensities.rho = Θ.rho := rfl

theorem toDensities_reduction (τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    Θ.toDensities.reduction τ T g = Θ.reduction τ T g := rfl

end TopThinnings

/-! ### The certificate -/

/-- **The partition-free reduction certificate**: top densities at every degree
cut, bottom thinnings (on the base law) at every near-cycle cut. -/
structure ReductionCertificate (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p : ℝ) where
  top : ∀ S, DegreeCutData H S → TopDensities H μ S ε₂ p
  bottom : ∀ S, S ∈ H.cuts → H.IsNearCycleCut S → BottomThinning H μ S p

namespace ReductionCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  (C : ReductionCertificate H μ ε₂ p)

/-- The reduction of the edge `g` at the cut `S`, if `S` is its edge parent. -/
noncomputable def reductionAt (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  if hS : H.IsEdgeParent g S then
    (if hcyc : H.IsNearCycleCut S then β * x g * (C.bottom S hS.1 hcyc).rho T
      else if hdeg : DegreeCutData H S then (C.top S hdeg).reduction τ T g else 0)
  else 0

/-- **The reduction vector `r`**, summed over the cuts of the hierarchy. -/
noncomputable def reduction (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : ℝ :=
  ∑ S ∈ H.cuts, C.reductionAt β τ T g S

theorem reductionAt_of_not {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent g S) : C.reductionAt β τ T g S = 0 := by
  unfold reductionAt
  rw [dif_neg h]

/-- The reduction is the term at the edge parent. -/
theorem reduction_eq_of_isEdgeParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) :
    C.reduction β τ T g = C.reductionAt β τ T g S := by
  unfold reduction
  refine Finset.sum_eq_single_of_mem S hS.1 fun S' _ hne => ?_
  exact C.reductionAt_of_not fun h => hne (Hierarchy.IsEdgeParent.unique H h hS)

/-- **Bottom edges**: `r_g = β x_g ρ_S` when `p(g) = S` is a near-cycle cut. -/
theorem reduction_bottom {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    C.reduction β τ T g = β * x g * (C.bottom S hS.1 hcyc).rho T := by
  rw [C.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_pos hcyc]

/-- **Top edges**: `r_g` is the reduction at the degree cut `p(g) = S`. -/
theorem reduction_top {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hdeg : DegreeCutData H S) :
    C.reduction β τ T g = (C.top S hdeg).reduction τ T g := by
  rw [C.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hdeg.notNearCycle, dif_pos hdeg]

/-- `E[r_e] = β·p·x_e` on a bottom edge. -/
theorem expect_reduction_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => C.reduction β τ T e) = β * p * x e := by
  have hpt : (fun T => C.reduction β τ T e)
      = fun T => β * x e * (C.bottom S hS.1 hcyc).rho T := by
    funext T
    rw [C.reduction_bottom hS hcyc]
  rw [hpt, μ.expect_mul_left, (C.bottom S hS.1 hcyc).expect_rho]
  ring

/-- `E[r_e] = τ·p·x_e` on a good top bundle. -/
theorem expect_reduction_top {β τ : ℝ} {S a b : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b)
    (hgood : IsGoodBundle μ ε₂ a b) {e : Sym2 (Fin n)} (he : e ∈ betweenEdges a b) :
    μ.expect (fun T => C.reduction β τ T e) = τ * p * x e := by
  have hSe : H.IsEdgeParent e S :=
    H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb) hab he
  have hpt : (fun T => C.reduction β τ T e)
      = fun T => τ * x e / 2 * (C.top S hdeg).rho a b T
          + τ * x e / 2 * (C.top S hdeg).rho b a T := by
    funext T
    rw [C.reduction_top hSe hdeg, (C.top S hdeg).reduction_eq ha hb hab he]
    ring
  rw [hpt, μ.expect_add, μ.expect_mul_left, μ.expect_mul_left,
    (C.top S hdeg).expect_rho a ha b hb hab hgood,
    (C.top S hdeg).expect_rho b hb a ha (Ne.symm hab) (isGoodBundle_comm.mp hgood)]
  ring

/-- An edge whose parent is neither a near-cycle cut nor a degree cut is not
reduced. -/
theorem reduction_eq_zero_of_neither {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : C.reduction β τ T g = 0 := by
  rw [C.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hcyc, dif_neg hdeg]

/-- An edge with no edge parent is not reduced. -/
theorem reduction_eq_zero_of_noParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent g S) : C.reduction β τ T g = 0 := by
  unfold reduction
  exact Finset.sum_eq_zero fun S _ => C.reductionAt_of_not (h S)

theorem reductionAt_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) :
    0 ≤ C.reductionAt β τ T g S := by
  unfold reductionAt
  split_ifs with hS hcyc hdeg
  · have := (C.bottom S hS.1 hcyc).rho_nonneg T
    positivity
  · exact (C.top S hdeg).reduction_nonneg hτ hxg T
  · exact le_rfl
  · exact le_rfl

theorem reduction_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) : 0 ≤ C.reduction β τ T g :=
  Finset.sum_nonneg fun S _ => C.reductionAt_nonneg hβ hτ hxg T S

/-- **`r_g ≤ β x_g`** for `τ ≤ β`. -/
theorem reduction_le {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) : C.reduction β τ T g ≤ β * x g := by
  have hβ : 0 ≤ β := hτ.trans hτβ
  by_cases h : ∃ S, H.IsEdgeParent g S
  · obtain ⟨S, hS⟩ := h
    rw [C.reduction_eq_of_isEdgeParent hS]
    unfold reductionAt
    rw [dif_pos hS]
    split_ifs with hcyc hdeg
    · have h1 := (C.bottom S hS.1 hcyc).rho_le_one T
      have h0 := (C.bottom S hS.1 hcyc).rho_nonneg T
      nlinarith [mul_nonneg hβ hxg]
    · calc (C.top S hdeg).reduction τ T g ≤ τ * x g := (C.top S hdeg).reduction_le hτ hxg T
        _ ≤ β * x g := mul_le_mul_of_nonneg_right hτβ hxg
    · positivity
  · rw [C.reduction_eq_zero_of_noParent fun S hS => h ⟨S, hS⟩]
    positivity

/-- **No reduction on `δ(u)` at an odd atom `u` of a degree cut**, for the
edges whose parent is that cut. -/
theorem reduction_eq_zero_of_odd {β τ : ℝ} {S u : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges u).card)
    {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u) (hS : H.IsEdgeParent g S) :
    C.reduction β τ T g = 0 := by
  rw [C.reduction_top hS hdeg]
  exact (C.top S hdeg).reduction_eq_zero_of_odd hu hodd hg τ

/-! #### The bottom certificate -/

/-- **The bottom certificate**, unchanged from `ReductionData`. -/
structure HasBottomGuarantees : Prop where
  bottom_guar : ∀ S, ∀ hS : S ∈ H.cuts, ∀ hcyc : H.IsNearCycleCut S,
    BottomGuarantees H μ S p (C.bottom S hS hcyc)

variable {C}

theorem bottomGuar (h : C.HasBottomGuarantees) (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) : BottomGuarantees H μ S p (C.bottom S hS hcyc) :=
  h.bottom_guar S hS hcyc

theorem bottomPolygonWitness (h : C.HasBottomGuarantees) (S : Finset (Fin n))
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    Nonempty (BottomPolygonWitness H μ S p (C.bottom S hS hcyc)) :=
  (h.bottom_guar S hS hcyc).polygonWitness

/-- The bottom odd-parity bound, in the expectation form Lemma 7.3 sums. -/
theorem expect_rho_bottom_odd_le (h : C.HasBottomGuarantees) {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) :
    μ.expect (fun T => (C.bottom S hS hcyc).rho T
        * if Odd (T ∩ cutEdges u).card then 1 else 0) ≤ 0.5678 * p := by
  have h1 := (C.bottom S hS hcyc).expect_rho_le ((h.bottom_guar S hS hcyc).odd_le u hu hlt)
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => (C.bottom S hS hcyc).rho T * z)
    (ite_instance_congr _ _ _ (1 : ℝ) 0)

variable (C)

/-! #### The odd-parity reduction mass -/

/-- `R(E) = ∑_{g ∈ E} E[r_g · 1_{δ(u) odd}]`, at the certificate. -/
noncomputable def oddReductionMass (β τ : ℝ) (u : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ g ∈ E, μ.expect fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0

/-- `R` splits along the three-way partition of the tail. -/
theorem oddReductionMass_split (β τ : ℝ) (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    C.oddReductionMass β τ u (goodTopPart H μ ε₂ E)
        + C.oddReductionMass β τ u (inactivePart H μ ε₂ E)
        + C.oddReductionMass β τ u (bottomPart H E)
      = C.oddReductionMass β τ u E :=
  sum_split_three H μ ε₂ E _

/-- An edge of the root tail has zero reduction: it has no edge parent. -/
theorem reduction_eq_zero_of_mem_root_tail {u : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hg : g ∈ tail u e₀.rootCut) (β τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    C.reduction β τ T g = 0 :=
  Finset.sum_eq_zero fun S _ =>
    C.reductionAt_of_not (not_isEdgeParent_of_mem_root_tail H hg S)

/-- **An inactive tail edge has zero reduction.** -/
theorem reduction_eq_zero_of_inactive {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    {g : Sym2 (Fin n)} (hgu : g ∈ cutEdges u)
    (hnb : ¬ IsBottomEdge H g) (hng : ¬ IsGoodTopEdge H μ ε₂ g)
    (β τ : ℝ) (T : Finset (Sym2 (Fin n))) : C.reduction β τ T g = 0 := by
  by_cases hp : ∃ V, H.IsEdgeParent g V
  · obtain ⟨V, hV⟩ := hp
    rw [C.reduction_eq_of_isEdgeParent hV]
    unfold reductionAt
    rw [dif_pos hV]
    by_cases hcyc : H.IsNearCycleCut V
    · exact absurd ⟨V, hV, hcyc⟩ hnb
    · rw [dif_neg hcyc]
      by_cases hdeg : DegreeCutData H V
      · rw [dif_pos hdeg]
        obtain ⟨U, hUV, -, w, hw, hgw⟩ := exists_bundle_of_isEdgeParent H hu hgu hV
        exact (C.top V hdeg).reduction_eq_zero_of_bad_bundle
          (H.mem_children.mpr hUV) (H.mem_children.mpr (H.mem_siblings.mp hw).2)
          (Ne.symm (H.mem_siblings.mp hw).1)
          (fun hgood => hng (isGoodTopEdge_of_mem_good_fiber H hUV hdeg hw hgood hgw)) hgw τ T
      · rw [dif_neg hdeg]
  · exact Finset.sum_eq_zero fun S _ => C.reductionAt_of_not fun h => hp ⟨S, h⟩

/-- **`R(inactive) = 0`.** -/
theorem oddReductionMass_inactive_eq_zero {u : Finset (Fin n)} (hu : u ∈ H.cuts) (β τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    C.oddReductionMass β τ u (inactivePart H μ ε₂ E) = 0 := by
  refine Finset.sum_eq_zero fun g hg => ?_
  obtain ⟨hgE, hnb, hng⟩ := Finset.mem_filter.mp hg
  unfold TreeDist.expect
  refine Finset.sum_eq_zero fun T _ => ?_
  simp [C.reduction_eq_zero_of_inactive hu (hE hgE) hnb hng β τ T]

/-- **`R(bottom) ≤ 0.5678·β·p·bottom`**. -/
theorem oddReductionMass_bottom_le (hx : IsRestrictedLP e₀ x) (hbg : C.HasBottomGuarantees)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β : ℝ} (hβ : 0 ≤ β) (τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    C.oddReductionMass β τ u (bottomPart H E)
      ≤ 0.5678 * β * p * ∑ g ∈ bottomPart H E, x g := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨hgE, V, hV, hcyc⟩ := Finset.mem_filter.mp hg
  have hxg : 0 ≤ x g := hx.nonneg g
  have hpt : (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      = fun T => β * x g * ((C.bottom V hV.1 hcyc).rho T
          * if Odd (T ∩ cutEdges u).card then 1 else 0) := by
    funext T
    rw [C.reduction_bottom hV hcyc]
    ring
  rw [hpt, μ.expect_mul_left]
  have hb := expect_rho_bottom_odd_le hbg hV.1 hcyc hu
    (ssubset_of_isEdgeParent H hu (hE hgE) hV)
  nlinarith [mul_nonneg hβ hxg, hb]

/-- **`R(E) ≤ τ·p·x(E)` on any set of good top edges.** -/
theorem oddReductionMass_le_of_goodTop (hx : IsRestrictedLP e₀ x) (u : Finset (Fin n))
    {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ g ∈ E, IsGoodTopEdge H μ ε₂ g) :
    C.oddReductionMass β τ u E ≤ τ * p * ∑ g ∈ E, x g := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨S, hdeg, a, ha, b, hb, hab, hgab, hgood⟩ := hE g hg
  have hxg : 0 ≤ x g := hx.nonneg g
  have hfull := C.expect_reduction_top (β := β) (τ := τ) hdeg ha hb hab hgood hgab
  refine le_trans ?_ (le_of_eq hfull)
  unfold TreeDist.expect
  refine Finset.sum_le_sum fun T _ => ?_
  have hr : 0 ≤ C.reduction β τ T g := C.reduction_nonneg hβ hτ hxg T
  have hprob : 0 ≤ μ.prob T := μ.prob_nonneg T
  change μ.prob T * (C.reduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      ≤ μ.prob T * C.reduction β τ T g
  by_cases hodd : Odd (T ∩ cutEdges u).card
  · rw [if_pos hodd, mul_one]
  · rw [if_neg hodd, mul_zero, mul_zero]
    exact mul_nonneg hprob hr

/-- **`R(good) ≤ τ·p·good`.** -/
theorem oddReductionMass_goodTop_le (hx : IsRestrictedLP e₀ x) (u : Finset (Fin n))
    {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (E : Finset (Sym2 (Fin n))) :
    C.oddReductionMass β τ u (goodTopPart H μ ε₂ E)
      ≤ τ * p * ∑ g ∈ goodTopPart H μ ε₂ E, x g :=
  C.oddReductionMass_le_of_goodTop hx u hβ hτ _ fun g hg => (Finset.mem_filter.mp hg).2.2

/-- **`R(δ↑(u)) ≤ τ·p·x(δ↑(u))`**, the trivial bound on a whole tail. -/
theorem oddReductionMass_tail_le (hx : IsRestrictedLP e₀ x) (hBG : C.HasBottomGuarantees)
    {u Pu : Finset (Fin n)} (hu : u ∈ H.cuts) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hp : 0 ≤ p) (hβτ : 0.5678 * β ≤ τ) :
    C.oddReductionMass β τ u (tail u Pu) ≤ τ * p * upSum x Pu u := by
  have hE : tail u Pu ⊆ cutEdges u := Finset.inter_subset_right
  have hsplit := C.oddReductionMass_split β τ u (tail u Pu)
  have hinact := C.oddReductionMass_inactive_eq_zero hu β τ hE
  have hgood := C.oddReductionMass_goodTop_le hx u hβ hτ (tail u Pu)
  have hbot := C.oddReductionMass_bottom_le hx hBG hu hβ τ hE
  have hmass := sum_split_three H μ ε₂ (tail u Pu) x
  have hq : upSum x Pu u = ∑ g ∈ tail u Pu, x g := rfl
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hin0 : 0 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hexp : τ * p * (∑ g ∈ tail u Pu, x g)
      = τ * p * (∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g)
        + τ * p * (∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g)
        + τ * p * ∑ g ∈ bottomPart H (tail u Pu), x g := by
    rw [← hmass]; ring
  have hslack : 0 ≤ τ * p * ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g :=
    mul_nonneg (mul_nonneg hτ hp) hin0
  have hbot' : 0.5678 * β * p * (∑ g ∈ bottomPart H (tail u Pu), x g)
      ≤ τ * p * ∑ g ∈ bottomPart H (tail u Pu), x g := by
    nlinarith [mul_nonneg hp hbot0]
  rw [hq]
  linarith

/-! #### Lemma 7.3's odd-mass bounds, as a certificate -/

/-- **Lemma 7.3's estimate at the parameters `β, τ`**: at every atom `u` with
parent `p(u)` and `x(δ↑(u)) ≥ 1/10`, the odd-parity reduction mass of the
tail is at most `τ·p·(1 − ε₁/5)·F_u·x(δ↑(u))`. -/
structure HasOddMassBounds (ε₁ β τ : ℝ) : Prop where
  odd_mass_le : ∀ {u Pu : Finset (Fin n)}, IsChildOf H.cuts u Pu → u.Nonempty →
    u ≠ Finset.univ → cutSum x u ≤ 2 + εη → 1 / 10 ≤ upSum x Pu u →
    C.oddReductionMass β τ u (tail u Pu)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x Pu (21 * ε₂) u) * upSum x Pu u

end ReductionCertificate

/-! ### The base reduction data are a certificate -/

namespace ReductionData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ : ℝ}
  {P : DegreePartitions H ε₁} (D : ReductionData H μ ε₂ p ε₁ P)

/-- **The certificate of the base reduction data**: the densities of its top
thinnings, its bottom thinnings unchanged. -/
noncomputable def toCertificate : ReductionCertificate H μ ε₂ p where
  top := fun S hS => (D.top S hS).toDensities
  bottom := D.bottom

theorem toCertificate_reductionAt (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n))
    (S : Finset (Fin n)) : D.toCertificate.reductionAt β τ T g S = D.reductionAt β τ T g S :=
  rfl

/-- The reduction vector is unchanged. -/
theorem toCertificate_reduction (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    D.toCertificate.reduction β τ T g = D.reduction β τ T g :=
  rfl

theorem toCertificate_oddReductionMass (β τ : ℝ) (u : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) :
    D.toCertificate.oddReductionMass β τ u E = oddReductionMass D β τ u E :=
  rfl

theorem toCertificate_hasBottomGuarantees (h : D.HasBottomGuarantees) :
    D.toCertificate.HasBottomGuarantees :=
  ⟨h.bottom_guar⟩

/-- **Lemma 7.3 at the base data**, as the certificate's odd-mass bounds. -/
theorem toCertificate_hasOddMassBounds (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100) (hεηsq : εη ≤ ε₂ ^ 2)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangular)
    (hctrl : P.ControlsDescendants)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂) :
    D.toCertificate.HasOddMassBounds ε₁ β τ :=
  ⟨fun hPu hune huniv hucut hq =>
    lemma_7_3 hx hμ hεη hεηcap hεη₁ hεηsq hH D hBG hTR hctrl hPu hune huniv hucut hβ hτeq hp
      hple hε₁0 hε₁ hε₂ hε₂0 hq⟩

end ReductionData

end TSPGap

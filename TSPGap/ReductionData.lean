/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HappyEvents

/-!
# KKO21 §7: the reduction events and the reduction vector `r`

**Top bundles.**  At a degree cut `S`, every *ordered* pair `(u, u')` of
distinct atoms with a good bundle carries a uniform thinning `R_{e,u}` at mass
`p` of an event `E_{e,u} ⊆ H_{e,u}` (`TopThinnings`): the event is the one the
thinning is uniform over, and it implies KKO's `H_{e,u}` (`HappyWrt`).  Bad
pairs carry the zero thinning.  ⚠️ **Case (iii) coherence**: at an atom `u`
in case 3 of Theorem 5.28 and not in cases 1 or 2, the two chosen half bundles
`e, f` use the **same** thinning of `H_{e,u} ∩ H_{f,u}` — the 2-2-2 happy
event — so `ρ_{e,u} = ρ_{f,u}` pointwise (`coherent`); independent endpoint
thinnings would not do for Lemma 7.8.

**Bottom bundles.**  At a near-cycle (polygon) cut `S`, KKO subsample the
max-flow event `E_S` of Definition 5.8.  In this development that "event" is
Proposition 5.6's *selected subweight*, so the data (`BottomThinning`) are a
near-cycle presenting `S`, a base subweight supported on happy trees, and its
rescaling `R_S` to mass `p` (`IsRescaling`).

**The reduction vector** (KKO, after the reduction events):
`r_g = β x_g R_S` if `p(g) = S` is a polygon cut, and
`r_g = (τ x_g / 2)(R_{f,u} + R_{f,u'})` if `g ∈ f = (u, u')` is a top edge of
the degree cut `p(g)`.  Both are defined **by summation, never by choice**:
over the ordered pairs of atoms of `p(g)` (`TopThinnings.reduction`, exactly
two nonzero terms by `Hierarchy.sum_ordered_pairs_eq`) and over the cuts of
the hierarchy (`ReductionData.reduction`, at most one nonzero term since the
edge parent is unique).  Edges with no edge parent, or whose parent is neither
a near-cycle cut nor a `DegreeCutData` cut, are not reduced.

Pointwise: `0 ≤ r_g ≤ τ x_g` (top) or `≤ β x_g` (bottom), `r_g = 0` on a bad
bundle, and **`r_g = 0` on every edge of `δ(u)` when `δ(u)_T` is odd**
(`TopThinnings.reduction_eq_zero_of_odd`) — the fact Theorem 4.33 (iv) uses.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### Top thinnings at one cut -/

/-- **The thinning data of the top bundles at the cut `S`** (see the module
docstring). `P.get u hu` is the degree partition of `δ(u)`, read at the
cut `u`; see `DegreePartitions` for why the family is not a total function. -/
structure TopThinnings (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n))
    (ε₂ p ε₁ : ℝ) (P : DegreePartitions H ε₁) where
  /-- The event `E_{e,u}` the thinning of the ordered pair `(u, u')` is uniform over. -/
  event : Finset (Fin n) → Finset (Fin n) → Finset (Sym2 (Fin n)) → Prop
  /-- The thinning `R_{e,u}` of the ordered pair `(u, u')`. -/
  thin : Finset (Fin n) → Finset (Fin n) → Finset (Sym2 (Fin n)) → ℝ
  /-- A good ordered pair carries a uniform thinning at mass `p`. -/
  uniform : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → IsGoodBundle μ ε₂ u u' →
    IsUniformThinning μ.prob (thin u u') (event u u') p
  /-- The event lies in KKO's `H_{e,u}`. -/
  event_happy : ∀ u, ∀ hu : u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    ∀ T, event u u' T → HappyWrt μ ε₂ p u u' (P.get u (H.mem_cuts_of_mem_children hu)) T
  /-- Outside the good ordered pairs of atoms the thinning is zero. -/
  thin_eq_zero : ∀ u u',
    ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u') → thin u u' = 0
  /-- **Case (iii) coherence**: an atom in case 3 but not in cases 1, 2 of
  Theorem 5.28 has two half bundles `e ≠ f` as in case 3 whose thinnings at
  `u` coincide and are uniform over the 2-2-2 happy event. -/
  coherent : ∀ u, ∀ hu : u ∈ H.children S, ¬ BadCase H μ ε₂ S u →
    ¬ TwoOneOneCase H μ ε₂ S u p (P.get u (H.mem_cuts_of_mem_children hu)) →
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f
      ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
      ∧ ∑ g ∈ betweenEdges u e ∩ (P.get u (H.mem_cuts_of_mem_children hu)).B, x g ≤ ε₂
      ∧ ∑ g ∈ betweenEdges u f ∩ (P.get u (H.mem_cuts_of_mem_children hu)).A, x g ≤ ε₂
      ∧ (∀ T, event u e T ↔ TwoTwoTwoHappy e u f T)
      ∧ (∀ T, event u f T ↔ TwoTwoTwoHappy e u f T)
      ∧ thin u f = thin u e

namespace TopThinnings

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ p ε₁ : ℝ}
  {P : DegreePartitions H ε₁}
  (Θ : TopThinnings H μ S ε₂ p ε₁ P)

theorem thin_nonneg (u u' : Finset (Fin n)) : WeightNonneg (Θ.thin u u') := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2).nonneg
  · intro T
    rw [Θ.thin_eq_zero u u' h]
    exact le_rfl

theorem thin_le (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    Θ.thin u u' T ≤ μ.prob T := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2).le T
  · rw [Θ.thin_eq_zero u u' h]
    exact μ.prob_nonneg T

/-- A nonzero thinning forces the ordered pair to be a good pair of children;
in particular `u` is a hierarchy cut, so `P` can be read there. -/
theorem goodPair_of_thin_ne_zero {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : Θ.thin u u' T ≠ 0) :
    u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u' := by
  by_contra hg
  exact absurd (congrFun (Θ.thin_eq_zero u u' hg) T) h

/-- The thinning is supported on its event, and its event lies in `H_{e,u}`. -/
theorem happy_of_thin_ne_zero {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : Θ.thin u u' T ≠ 0) :
    HappyWrt μ ε₂ p u u'
      (P.get u (H.mem_cuts_of_mem_children (Θ.goodPair_of_thin_ne_zero h).1)) T :=
  Θ.event_happy u (Θ.goodPair_of_thin_ne_zero h).1 u' (Θ.goodPair_of_thin_ne_zero h).2.1
    (Θ.goodPair_of_thin_ne_zero h).2.2.1 T
    ((Θ.uniform u (Θ.goodPair_of_thin_ne_zero h).1 u' (Θ.goodPair_of_thin_ne_zero h).2.1
      (Θ.goodPair_of_thin_ne_zero h).2.2.1 (Θ.goodPair_of_thin_ne_zero h).2.2.2).support T h)

/-- **`ρ_{e,u}`**: the density of the thinning of the ordered pair `(u, u')`. -/
noncomputable def rho (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : ℝ :=
  density μ.prob (Θ.thin u u') T

theorem rho_nonneg (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : 0 ≤ Θ.rho u u' T :=
  density_nonneg μ.weightNonneg (Θ.thin_nonneg u u') T

theorem rho_le_one (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Θ.rho u u' T ≤ 1 :=
  density_le_one μ.weightNonneg (Θ.thin_le u u') T

/-- `E[ρ_{e,u}] = p` on a good ordered pair. -/
theorem expect_rho {u u' : Finset (Fin n)} (hu : u ∈ H.children S) (hu' : u' ∈ H.children S)
    (huu' : u ≠ u') (hg : IsGoodBundle μ ε₂ u u') : μ.expect (Θ.rho u u') = p :=
  μ.expect_density (Θ.uniform u hu u' hu' huu' hg).toIsThinning

/-- **No reduction at an odd atom**: `ρ_{e,u} = 0` when `δ(u)_T` is odd. -/
theorem rho_eq_zero_of_odd {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (T ∩ cutEdges u).card) : Θ.rho u u' T = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · have : Θ.thin u u' T = 0 := by
      by_contra h
      exact (Θ.happy_of_thin_ne_zero h).not_odd hodd
    rw [this, zero_div]

/-- Nor at the other endpoint: `ρ_{e,u'} = 0` when `δ(u)_T` is odd. -/
theorem rho_eq_zero_of_odd' {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (T ∩ cutEdges u).card) : Θ.rho u' u T = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · have : Θ.thin u' u T = 0 := by
      by_contra h
      have := (Θ.happy_of_thin_ne_zero h).card_eq_two'
      rw [this] at hodd
      exact absurd hodd (by decide)
    rw [this, zero_div]

/-- `E[ρ 1_Q] = ∑_{T ∈ Q} R_{e,u}(T)`. -/
theorem expect_rho_indicator (u u' : Finset (Fin n)) (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.expect (fun T => Θ.rho u u' T * if Q T then 1 else 0) = weightMass (Θ.thin u u') Q :=
  μ.expect_density_indicator (Θ.thin_le u u') (Θ.thin_nonneg u u') Q

/-- **The uniformity identity at a good pair**:
`P[E_{e,u}] · E[ρ_{e,u} 1_Q] = p · P[E_{e,u} ∧ Q]`. -/
theorem probEvent_mul_expect_rho {u u' : Finset (Fin n)} (hu : u ∈ H.children S)
    (hu' : u' ∈ H.children S) (huu' : u ≠ u') (hg : IsGoodBundle μ ε₂ u u')
    (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.probEvent (Θ.event u u') * μ.expect (fun T => Θ.rho u u' T * if Q T then 1 else 0)
      = p * μ.probEvent (fun T => Θ.event u u' T ∧ Q T) :=
  μ.probEvent_mul_expect_density_indicator (Θ.uniform u hu u' hu' huu' hg) Q

/-- A conditional bound `P[Q | E_{e,u}] ≤ c` (cross-multiplied) gives
`E[ρ_{e,u} 1_Q] ≤ p c`; on a bad pair the left side is `0`. -/
theorem expect_rho_indicator_le {u u' : Finset (Fin n)} {Q : Finset (Sym2 (Fin n)) → Prop}
    {c : ℝ} (hpc : 0 ≤ p * c)
    (hQ : u ∈ H.children S → u' ∈ H.children S → u ≠ u' → IsGoodBundle μ ε₂ u u' →
      μ.probEvent (fun T => Θ.event u u' T ∧ Q T) ≤ c * μ.probEvent (Θ.event u u')) :
    μ.expect (fun T => Θ.rho u u' T * if Q T then 1 else 0) ≤ p * c := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact μ.expect_density_indicator_le (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2)
      (hQ h.1 h.2.1 h.2.2.1 h.2.2.2)
  · rw [Θ.expect_rho_indicator]
    have : weightMass (Θ.thin u u') Q = 0 := by
      unfold weightMass
      exact Finset.sum_eq_zero fun T _ => by rw [Θ.thin_eq_zero u u' h]; simp
    rw [this]
    exact hpc

/-! #### The reduction at the cut -/

/-- **The reduction of the edge `g` at the cut `S`**:
`(τ x_g / 2)(ρ_{f,u} + ρ_{f,u'})` for `g ∈ f = (u, u')`, as a sum over the
ordered pairs of atoms — exactly two nonzero terms. -/
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
  · -- the edge meets `u`, so `u` is one of the two atoms
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_betweenEdges_iff.mp hab
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

end TopThinnings

/-! ### Bottom thinnings at one near-cycle cut -/

/-- **The thinning data of a near-cycle (polygon) cut `S`**: a near-cycle
presenting it, the base subweight (KKO's max-flow event `E_S`) supported on
happy trees, and its rescaling `R_S` to mass `p`. -/
structure BottomThinning (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n))
    (p : ℝ) where
  /-- The near-cycle presenting `S`: it fixes the polygon partition `A, B, C`. -/
  cycle : NearCycle x εη
  presents : H.Presents cycle S
  /-- The base subweight (the max-flow "event"). -/
  base : Finset (Sym2 (Fin n)) → ℝ
  base_nonneg : WeightNonneg base
  base_le : ∀ T, base T ≤ μ.prob T
  /-- The base is supported on happy trees. -/
  base_happy : ∀ T, base T ≠ 0 → cycle.Happy T
  /-- The rescaling `R_S`. -/
  thin : Finset (Sym2 (Fin n)) → ℝ
  rescaling : IsRescaling base thin p
  p_le : p ≤ totalMass base

namespace BottomThinning

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {p : ℝ}
  (Ξ : BottomThinning H μ S p)

include Ξ in
theorem p_nonneg : 0 ≤ p :=
  Ξ.rescaling.total ▸ totalMass_nonneg Ξ.rescaling.nonneg

theorem thin_nonneg : WeightNonneg Ξ.thin := Ξ.rescaling.nonneg

theorem thin_le_base (T : Finset (Sym2 (Fin n))) : Ξ.thin T ≤ Ξ.base T :=
  Ξ.rescaling.le Ξ.base_nonneg Ξ.p_nonneg Ξ.p_le T

theorem thin_le (T : Finset (Sym2 (Fin n))) : Ξ.thin T ≤ μ.prob T :=
  (Ξ.thin_le_base T).trans (Ξ.base_le T)

/-- The rescaling is supported on happy trees. -/
theorem happy_of_thin_ne_zero {T : Finset (Sym2 (Fin n))} (h : Ξ.thin T ≠ 0) :
    Ξ.cycle.Happy T := by
  refine Ξ.base_happy T fun hb => h ?_
  exact le_antisymm (by rw [← hb]; exact Ξ.thin_le_base T) (Ξ.thin_nonneg T)

/-- **`ρ_S`**: the density of `R_S`. -/
noncomputable def rho (T : Finset (Sym2 (Fin n))) : ℝ := density μ.prob Ξ.thin T

theorem rho_nonneg (T : Finset (Sym2 (Fin n))) : 0 ≤ Ξ.rho T :=
  density_nonneg μ.weightNonneg Ξ.thin_nonneg T

theorem rho_le_one (T : Finset (Sym2 (Fin n))) : Ξ.rho T ≤ 1 :=
  density_le_one μ.weightNonneg Ξ.thin_le T

/-- `E[ρ_S] = p`. -/
theorem expect_rho : μ.expect Ξ.rho = p := by
  have := μ.expect_density_mul Ξ.thin_le Ξ.thin_nonneg (fun _ => 1)
  simp only [mul_one] at this
  exact this.trans Ξ.rescaling.total

/-- `ρ_S = 0` on unhappy trees. -/
theorem rho_eq_zero_of_not_happy {T : Finset (Sym2 (Fin n))} (h : ¬ Ξ.cycle.Happy T) :
    Ξ.rho T = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · have : Ξ.thin T = 0 := by
      by_contra hne
      exact h (Ξ.happy_of_thin_ne_zero hne)
    rw [this, zero_div]

theorem expect_rho_indicator (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.expect (fun T => Ξ.rho T * if Q T then 1 else 0) = weightMass Ξ.thin Q :=
  μ.expect_density_indicator Ξ.thin_le Ξ.thin_nonneg Q

/-- **The uniformity identity**: `(∑ base) · E[ρ_S 1_Q] = p · W_base(Q)`, i.e.
`E[ρ_S 1_Q] = p · P[Q | E_S]`. -/
theorem totalMass_mul_expect_rho (Q : Finset (Sym2 (Fin n)) → Prop) :
    totalMass Ξ.base * μ.expect (fun T => Ξ.rho T * if Q T then 1 else 0)
      = p * weightMass Ξ.base Q := by
  rw [Ξ.expect_rho_indicator, Ξ.rescaling.weightMass_mul]

end BottomThinning

/-! ### The global reduction data and the reduction vector -/

/-- **The reduction data of the hierarchy**: top thinnings at every degree
cut, bottom thinnings at every near-cycle cut. -/
structure ReductionData (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p ε₁ : ℝ)
    (P : DegreePartitions H ε₁) where
  top : ∀ S, DegreeCutData H S → TopThinnings H μ S ε₂ p ε₁ P
  bottom : ∀ S, S ∈ H.cuts → H.IsNearCycleCut S → BottomThinning H μ S p

namespace ReductionData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ : ℝ}
  {P : DegreePartitions H ε₁} (D : ReductionData H μ ε₂ p ε₁ P)

/-- The reduction of the edge `g` at the cut `S`, if `S` is its edge parent. -/
noncomputable def reductionAt (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  if hS : H.IsEdgeParent g S then
    (if hcyc : H.IsNearCycleCut S then β * x g * (D.bottom S hS.1 hcyc).rho T
      else if hdeg : DegreeCutData H S then (D.top S hdeg).reduction τ T g else 0)
  else 0

/-- **KKO's reduction vector `r`**: summed over the cuts of the hierarchy — at
most one term is nonzero, the one at the edge parent. -/
noncomputable def reduction (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : ℝ :=
  ∑ S ∈ H.cuts, D.reductionAt β τ T g S

theorem reductionAt_of_not {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent g S) : D.reductionAt β τ T g S = 0 := by
  unfold reductionAt
  rw [dif_neg h]

/-- The reduction is the term at the edge parent. -/
theorem reduction_eq_of_isEdgeParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) :
    D.reduction β τ T g = D.reductionAt β τ T g S := by
  unfold reduction
  refine Finset.sum_eq_single_of_mem S hS.1 fun S' _ hne => ?_
  exact D.reductionAt_of_not fun h => hne (Hierarchy.IsEdgeParent.unique H h hS)

/-- **Bottom edges**: `r_g = β x_g ρ_S` when `p(g) = S` is a near-cycle cut. -/
theorem reduction_bottom {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    D.reduction β τ T g = β * x g * (D.bottom S hS.1 hcyc).rho T := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_pos hcyc]

/-- **Top edges**: `r_g` is the reduction at the degree cut `p(g) = S`. -/
theorem reduction_top {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hdeg : DegreeCutData H S) :
    D.reduction β τ T g = (D.top S hdeg).reduction τ T g := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hdeg.notNearCycle, dif_pos hdeg]

/-- `E[r_e] = β·p·x_e` on a bottom edge.  ⚠️ Stated here, at the *reduction*
data: Lemma 7.3 has a `ReductionData` and not a `PaymentData`.  The
`PaymentData` form is a wrapper. -/
theorem expect_reduction_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => D.reduction β τ T e) = β * p * x e := by
  have hpt : (fun T => D.reduction β τ T e)
      = fun T => β * x e * (D.bottom S hS.1 hcyc).rho T := by
    funext T
    rw [D.reduction_bottom hS hcyc]
  rw [hpt, μ.expect_mul_left, (D.bottom S hS.1 hcyc).expect_rho]
  ring

/-- `E[r_e] = τ·p·x_e` on a good top bundle, at the *reduction* data. -/
theorem expect_reduction_top {β τ : ℝ} {S a b : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b)
    (hgood : IsGoodBundle μ ε₂ a b) {e : Sym2 (Fin n)} (he : e ∈ betweenEdges a b) :
    μ.expect (fun T => D.reduction β τ T e) = τ * p * x e := by
  have hSe : H.IsEdgeParent e S :=
    H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb) hab he
  have hpt : (fun T => D.reduction β τ T e)
      = fun T => τ * x e / 2 * (D.top S hdeg).rho a b T
          + τ * x e / 2 * (D.top S hdeg).rho b a T := by
    funext T
    rw [D.reduction_top hSe hdeg, (D.top S hdeg).reduction_eq ha hb hab he]
    ring
  rw [hpt, μ.expect_add, μ.expect_mul_left, μ.expect_mul_left,
    (D.top S hdeg).expect_rho ha hb hab hgood,
    (D.top S hdeg).expect_rho hb ha (Ne.symm hab) (isGoodBundle_comm.mp hgood)]
  ring

/-- An edge whose parent is neither a near-cycle cut nor a degree cut is not
reduced. -/
theorem reduction_eq_zero_of_neither {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : D.reduction β τ T g = 0 := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hcyc, dif_neg hdeg]

/-- An edge with no edge parent is not reduced. -/
theorem reduction_eq_zero_of_noParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent g S) : D.reduction β τ T g = 0 := by
  unfold reduction
  exact Finset.sum_eq_zero fun S _ => D.reductionAt_of_not (h S)

theorem reductionAt_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) :
    0 ≤ D.reductionAt β τ T g S := by
  unfold reductionAt
  split_ifs with hS hcyc hdeg
  · have := (D.bottom S hS.1 hcyc).rho_nonneg T
    positivity
  · exact (D.top S hdeg).reduction_nonneg hτ hxg T
  · exact le_rfl
  · exact le_rfl

theorem reduction_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) : 0 ≤ D.reduction β τ T g :=
  Finset.sum_nonneg fun S _ => D.reductionAt_nonneg hβ hτ hxg T S

/-- **`r_g ≤ β x_g`** for `τ ≤ β`. -/
theorem reduction_le {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) : D.reduction β τ T g ≤ β * x g := by
  have hβ : 0 ≤ β := hτ.trans hτβ
  by_cases h : ∃ S, H.IsEdgeParent g S
  · obtain ⟨S, hS⟩ := h
    rw [D.reduction_eq_of_isEdgeParent hS]
    unfold reductionAt
    rw [dif_pos hS]
    split_ifs with hcyc hdeg
    · have h1 := (D.bottom S hS.1 hcyc).rho_le_one T
      have h0 := (D.bottom S hS.1 hcyc).rho_nonneg T
      nlinarith [mul_nonneg hβ hxg]
    · calc (D.top S hdeg).reduction τ T g ≤ τ * x g := (D.top S hdeg).reduction_le hτ hxg T
        _ ≤ β * x g := mul_le_mul_of_nonneg_right hτβ hxg
    · positivity
  · rw [D.reduction_eq_zero_of_noParent fun S hS => h ⟨S, hS⟩]
    positivity

/-- **No reduction on `δ(u)` at an odd atom `u` of a degree cut**, for the
edges whose parent is that cut. -/
theorem reduction_eq_zero_of_odd {β τ : ℝ} {S u : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges u).card)
    {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u) (hS : H.IsEdgeParent g S) :
    D.reduction β τ T g = 0 := by
  rw [D.reduction_top hS hdeg]
  exact (D.top S hdeg).reduction_eq_zero_of_odd hu hodd hg τ

end ReductionData

end TSPGap

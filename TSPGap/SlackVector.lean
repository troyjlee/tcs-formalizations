/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TopIncreaseSetup
import TSPGap.ReductionCertificate

/-!
# KKO21 §7: the bottom increase (32) and the slack vector (34)

**Eq. (32).**  At a near-cycle (polygon) cut `S` with polygon partition
`A, B, C` (fixed by the presenting near-cycle of its `BottomThinning`),
`I_S = (1 + ε_η)(max{r(A) 1{S not left happy}, r(B) 1{S not right happy}}
+ r(C) 1{S not happy})` (`BottomThinning.increase`).

**The payment certificate** is a partition-free reduction certificate
(`ReductionCertificate`) together with a matching (`MatchingData`) at every
degree cut; the increase and the slack are defined and studied there, and the
**payment data** (`ReductionData` plus matchings) are a certificate through
`PaymentData.toCertificate`, every one of their declarations being a wrapper.  The per-edge increase is again a sum
over the cuts of the hierarchy and, at a degree cut, over the ordered pairs of
atoms: for `e ∈ f = (u, u')`, `x_e / x_f · (I_{f,u} + I_{f,u'})`
(`PaymentData.topIncreaseAt`); for `p(e) = S` a near-cycle cut, `I_S x_e`.
The quotient `x_e / x_f` is zero-safe by Lean's convention, and correctly so:
`x_f = 0` forces every `x_e = 0` on the bundle.

**Eq. (34).**  `s_e = −r_e + I_e` on the genuine edges (`PaymentData.slack`).
Two of Theorem 4.33's properties are pointwise and are proved here:
`−βx_e ≤ s_e` (`slack_lower`, from `r_e ≤ βx_e` and `I_e ≥ 0`), and `s_e = 0`
off the good edges (`slack_eq_zero_of_not_mem_goodEdges`: a genuine edge
inside the root that is neither bottom nor in a good top bundle has zero
thinnings and zero allocation).  Properties (iii)–(v) are the content of
Lemmas 7.2–7.11 and Theorem 7.1, and (i) is Theorem 5.14 + Lemma 2.7.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### Eq. (32) -/

namespace BottomThinning

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {p : ℝ}
  (Ξ : BottomThinning H μ S p)

/-- **Eq. (32)**: the increase `I_S` of the polygon cut `S` on the tree `T`,
for the reduction vector `r`. -/
noncomputable def increase (r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    (T : Finset (Sym2 (Fin n))) : ℝ :=
  (1 + εη) * (max ((∑ f ∈ Ξ.cycle.partA, r T f) * (if Ξ.cycle.LeftHappy T then 0 else 1))
      ((∑ f ∈ Ξ.cycle.partB, r T f) * (if Ξ.cycle.RightHappy T then 0 else 1))
    + (∑ f ∈ Ξ.cycle.partC, r T f) * (if Ξ.cycle.Happy T then 0 else 1))

theorem increase_nonneg (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (hr : ∀ g, 0 ≤ r T g) : 0 ≤ Ξ.increase r T := by
  unfold increase
  have hA : 0 ≤ (∑ f ∈ Ξ.cycle.partA, r T f) * (if Ξ.cycle.LeftHappy T then 0 else 1) := by
    have hs := Finset.sum_nonneg fun f (_ : f ∈ Ξ.cycle.partA) => hr f
    split_ifs
    · simp
    · rw [mul_one]; exact hs
  have hC : 0 ≤ (∑ f ∈ Ξ.cycle.partC, r T f) * (if Ξ.cycle.Happy T then 0 else 1) := by
    have hs := Finset.sum_nonneg fun f (_ : f ∈ Ξ.cycle.partC) => hr f
    split_ifs
    · simp
    · rw [mul_one]; exact hs
  have hmax : 0 ≤ max ((∑ f ∈ Ξ.cycle.partA, r T f) * (if Ξ.cycle.LeftHappy T then 0 else 1))
      ((∑ f ∈ Ξ.cycle.partB, r T f) * (if Ξ.cycle.RightHappy T then 0 else 1)) :=
    le_trans hA (le_max_left _ _)
  exact mul_nonneg (by linarith) (add_nonneg hmax hC)

/-- A happy tree gets no bottom increase. -/
theorem increase_eq_zero_of_happy {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (h : Ξ.cycle.Happy T) : Ξ.increase r T = 0 := by
  unfold increase
  have hL : Ξ.cycle.LeftHappy T := ⟨h.1, h.2.2⟩
  have hR : Ξ.cycle.RightHappy T := ⟨h.2.1, h.2.2⟩
  rw [if_pos hL, if_pos hR, if_pos h]
  simp

/-- The increase is at least the `A`-term: `(1 + ε_η)(r(A) + r(C))` when `S`
is not left happy. -/
theorem increase_ge_left (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (h : ¬ Ξ.cycle.LeftHappy T) :
    (1 + εη) * ((∑ f ∈ Ξ.cycle.partA, r T f) + ∑ f ∈ Ξ.cycle.partC, r T f) ≤ Ξ.increase r T := by
  unfold increase
  have hH : ¬ Ξ.cycle.Happy T := fun hh => h ⟨hh.1, hh.2.2⟩
  rw [if_neg h, if_neg hH]
  have := le_max_left ((∑ f ∈ Ξ.cycle.partA, r T f) * 1)
    ((∑ f ∈ Ξ.cycle.partB, r T f) * (if Ξ.cycle.RightHappy T then 0 else 1))
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The mirror: at least `(1 + ε_η)(r(B) + r(C))` when `S` is not right happy. -/
theorem increase_ge_right (hεη : 0 ≤ εη) {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    {T : Finset (Sym2 (Fin n))} (h : ¬ Ξ.cycle.RightHappy T) :
    (1 + εη) * ((∑ f ∈ Ξ.cycle.partB, r T f) + ∑ f ∈ Ξ.cycle.partC, r T f) ≤ Ξ.increase r T := by
  unfold increase
  have hH : ¬ Ξ.cycle.Happy T := fun hh => h ⟨hh.2.1, hh.2.2⟩
  rw [if_neg h, if_neg hH]
  have := le_max_right ((∑ f ∈ Ξ.cycle.partA, r T f) * (if Ξ.cycle.LeftHappy T then 0 else 1))
    ((∑ f ∈ Ξ.cycle.partB, r T f) * 1)
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

end BottomThinning

/-! ### The payment certificate -/

/-- **The payment certificate**: a reduction certificate and a matching at
every degree cut. -/
structure PaymentCertificate (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p εB α : ℝ)
    extends ReductionCertificate H μ ε₂ p where
  matching : ∀ S, DegreeCutData H S → MatchingData H μ S ε₂ εB α

namespace PaymentCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p εB α : ℝ}
  (Δ : PaymentCertificate H μ ε₂ p εB α)

/-- The increase share of the edge `e` at the degree cut `S`:
`x_e / x_f · (I_{f,u} + I_{f,u'})` for `e ∈ f = (u, u')`, as an ordered-pair
sum. -/
noncomputable def topIncreaseAt (β τ : ℝ) (S : Finset (Fin n)) (hS : DegreeCutData H S)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
    if e ∈ betweenEdges u u' then
      x e / pairSum x u u' * (Δ.matching S hS).increase (Δ.reduction β τ) u u' T
    else 0

/-- The increase share of the edge `e` at the cut `S`, if `S` is its edge parent. -/
noncomputable def increaseAt (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  if hS : H.IsEdgeParent e S then
    (if hcyc : H.IsNearCycleCut S then
        (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T * x e
      else if hdeg : DegreeCutData H S then Δ.topIncreaseAt β τ S hdeg T e else 0)
  else 0

/-- **The increase `I_e`** of the edge `e`, summed over the cuts of the
hierarchy — at most one nonzero term, at the edge parent. -/
noncomputable def increase (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  ∑ S ∈ H.cuts, Δ.increaseAt β τ T e S

/-- **Eq. (34)**: the slack vector `s_e = −r_e + I_e`, on the genuine edges. -/
noncomputable def slack (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  if e ∈ edgeFinset n then - Δ.reduction β τ T e + Δ.increase β τ T e else 0

/-! #### Basic bookkeeping -/

theorem topIncreaseAt_eq {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b) {e : Sym2 (Fin n)}
    (he : e ∈ betweenEdges a b) (T : Finset (Sym2 (Fin n))) :
    Δ.topIncreaseAt β τ S hS T e
      = x e / pairSum x a b * (Δ.matching S hS).increase (Δ.reduction β τ) a b T
        + x e / pairSum x b a * (Δ.matching S hS).increase (Δ.reduction β τ) b a T := by
  unfold topIncreaseAt
  exact H.sum_ordered_pairs_eq ha hb hab he
    (fun u u' => x e / pairSum x u u' * (Δ.matching S hS).increase (Δ.reduction β τ) u u' T)

theorem topIncreaseAt_eq_zero_of_not {β τ : ℝ} {S : Finset (Fin n)} (hS : DegreeCutData H S)
    {e : Sym2 (Fin n)}
    (h : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → e ∉ betweenEdges a b)
    (T : Finset (Sym2 (Fin n))) : Δ.topIncreaseAt β τ S hS T e = 0 := by
  unfold topIncreaseAt
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun u' hu' => ?_
  rw [if_neg (h u hu u' (Finset.mem_of_mem_erase hu') (Ne.symm (Finset.ne_of_mem_erase hu')))]

theorem topIncreaseAt_nonneg (hx : IsRestrictedLP e₀ x) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {S : Finset (Fin n)} (hS : DegreeCutData H S) (T : Finset (Sym2 (Fin n)))
    (e : Sym2 (Fin n)) : 0 ≤ Δ.topIncreaseAt β τ S hS T e := by
  unfold topIncreaseAt
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => ?_
  split_ifs
  · have h1 := (Δ.matching S hS).increase_nonneg hx
      (fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T) u u'
    have h2 : 0 ≤ x e / pairSum x u u' := div_nonneg (hx.nonneg e) (pairSum_nonneg hx.nonneg u u')
    exact mul_nonneg h2 h1
  · exact le_rfl

theorem increaseAt_of_not {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent e S) : Δ.increaseAt β τ T e S = 0 := by
  unfold increaseAt
  rw [dif_neg h]

theorem increaseAt_nonneg (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (S : Finset (Fin n)) :
    0 ≤ Δ.increaseAt β τ T e S := by
  unfold increaseAt
  split_ifs with hS hcyc hdeg
  · have h1 := (Δ.bottom S hS.1 hcyc).increase_nonneg hεη
      (fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T)
    exact mul_nonneg h1 (hx.nonneg e)
  · exact Δ.topIncreaseAt_nonneg hx hβ hτ hdeg T e
  · exact le_rfl
  · exact le_rfl

theorem increase_nonneg (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : 0 ≤ Δ.increase β τ T e :=
  Finset.sum_nonneg fun S _ => Δ.increaseAt_nonneg hx hεη hβ hτ T e S

/-- The increase is the term at the edge parent. -/
theorem increase_eq_of_isEdgeParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) :
    Δ.increase β τ T e = Δ.increaseAt β τ T e S := by
  unfold increase
  refine Finset.sum_eq_single_of_mem S hS.1 fun S' _ hne => ?_
  exact Δ.increaseAt_of_not fun h => hne (Hierarchy.IsEdgeParent.unique H h hS)

/-- **Bottom edges**: `I_e = I_S x_e` when `p(e) = S` is a near-cycle cut. -/
theorem increase_bottom {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    Δ.increase β τ T e = (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T * x e := by
  rw [Δ.increase_eq_of_isEdgeParent hS]
  unfold increaseAt
  rw [dif_pos hS, dif_pos hcyc]

/-- **Top edges**: `I_e` is the share at the degree cut `p(e) = S`. -/
theorem increase_top {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hdeg : DegreeCutData H S) :
    Δ.increase β τ T e = Δ.topIncreaseAt β τ S hdeg T e := by
  rw [Δ.increase_eq_of_isEdgeParent hS]
  unfold increaseAt
  rw [dif_pos hS, dif_neg hdeg.notNearCycle, dif_pos hdeg]

theorem increase_eq_zero_of_neither {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : Δ.increase β τ T e = 0 := by
  rw [Δ.increase_eq_of_isEdgeParent hS]
  unfold increaseAt
  rw [dif_pos hS, dif_neg hcyc, dif_neg hdeg]

theorem increase_eq_zero_of_noParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent e S) : Δ.increase β τ T e = 0 := by
  unfold increase
  exact Finset.sum_eq_zero fun S _ => Δ.increaseAt_of_not (h S)

/-! #### Theorem 4.33 (ii): the pointwise properties of the slack -/

/-- **`s_e ≥ −βx_e`.** -/
theorem slack_lower (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : -(β * x e) ≤ Δ.slack β τ T e := by
  unfold slack
  have hβ : 0 ≤ β := hτ.trans hτβ
  split_ifs
  · have h1 := Δ.reduction_le hτ hτβ (hx.nonneg e) T
    have h2 := Δ.increase_nonneg hx hεη hβ hτ T e
    linarith
  · have := hx.nonneg e
    nlinarith

/-- A bad bundle is neither reduced nor increased at its cut. -/
theorem topIncreaseAt_eq_zero_of_bad {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b) {e : Sym2 (Fin n)}
    (he : e ∈ betweenEdges a b) (hbad : ¬ IsGoodBundle μ ε₂ a b) (T : Finset (Sym2 (Fin n))) :
    Δ.topIncreaseAt β τ S hS T e = 0 := by
  rw [Δ.topIncreaseAt_eq hS ha hb hab he]
  have hbad' : ¬ IsGoodBundle μ ε₂ b a := fun h => hbad (isGoodBundle_comm.mp h)
  rw [(Δ.matching S hS).increase_eq_zero_of_not (u := a) (u' := b) (fun h => hbad h.2.2.2) T,
    (Δ.matching S hS).increase_eq_zero_of_not (u := b) (u' := a) (fun h => hbad' h.2.2.2) T]
  ring

theorem reduction_eq_zero_of_bad {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    {e : Sym2 (Fin n)} (hSe : H.IsEdgeParent e S) (ha : a ∈ H.children S)
    (hb : b ∈ H.children S) (hab : a ≠ b)
    (he : e ∈ betweenEdges a b) (hbad : ¬ IsGoodBundle μ ε₂ a b) (T : Finset (Sym2 (Fin n))) :
    Δ.reduction β τ T e = 0 := by
  rw [Δ.reduction_top hSe hS, (Δ.top S hS).reduction_eq ha hb hab he]
  have hbad' : ¬ IsGoodBundle μ ε₂ b a := fun h => hbad (isGoodBundle_comm.mp h)
  rw [(Δ.top S hS).rho_eq_zero_of_not_good a b (fun h => hbad h.2.2.2) T,
    (Δ.top S hS).rho_eq_zero_of_not_good b a (fun h => hbad' h.2.2.2) T]
  ring

/-- **`s` is supported on the good edges `E_g`.** -/
theorem slack_eq_zero_of_not_mem_goodEdges {β τ : ℝ} (T : Finset (Sym2 (Fin n)))
    {e : Sym2 (Fin n)} (he : e ∉ goodEdges H μ ε₂) : Δ.slack β τ T e = 0 := by
  unfold slack
  split_ifs with hgen
  · rw [mem_goodEdges] at he
    push_neg at he
    by_cases hin : EdgeInside e e₀.rootCut
    · have hne := he hgen hin
      obtain ⟨S, hS⟩ := H.exists_isEdgeParent hin
      have hcyc : ¬ H.IsNearCycleCut S := fun h => hne.1 ⟨S, hS, h⟩
      by_cases hdeg : DegreeCutData H S
      · have hdiag : ¬ e.IsDiag := (Finset.mem_filter.mp hgen).2
        rcases H.exists_between_children_of_isEdgeParent hS hdiag with
          ⟨a, ha, b, hb, hab, hab'⟩ | hnone
        · have hbad : ¬ IsGoodBundle μ ε₂ a b :=
            fun hg => hne.2 ⟨S, hdeg, a, ha, b, hb, hab, hab', hg⟩
          rw [Δ.reduction_eq_zero_of_bad hdeg hS ha hb hab hab' hbad,
            Δ.increase_top hS hdeg, Δ.topIncreaseAt_eq_zero_of_bad hdeg ha hb hab hab' hbad]
          ring
        · have hnob : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → e ∉ betweenEdges a b :=
            fun a ha _ _ _ _ => hnone a (H.mem_children.mp ha)
          rw [Δ.reduction_top hS hdeg, (Δ.top S hdeg).reduction_eq_zero_of_not hnob,
            Δ.increase_top hS hdeg, Δ.topIncreaseAt_eq_zero_of_not hdeg hnob]
          ring
      · rw [Δ.reduction_eq_zero_of_neither hS hcyc hdeg,
          Δ.increase_eq_zero_of_neither hS hcyc hdeg]
        ring
    · have hno : ∀ S, ¬ H.IsEdgeParent e S := fun S hS =>
        hin (fun v hv => H.subset_rootCut hS.1 (hS.2.1 v hv))
      rw [Δ.reduction_eq_zero_of_noParent hno, Δ.increase_eq_zero_of_noParent hno]
      ring
  · rfl

end PaymentCertificate

/-! ### The payment data, as wrappers around the certificate -/

/-- **The payment data**: reduction data and a matching at every degree cut. -/
structure PaymentData (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p ε₁ εB α : ℝ)
    (P : DegreePartitions H ε₁)
    extends ReductionData H μ ε₂ p ε₁ P where
  matching : ∀ S, DegreeCutData H S → MatchingData H μ S ε₂ εB α

namespace PaymentData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ εB α : ℝ}
  {P : DegreePartitions H ε₁}
  (Δ : PaymentData H μ ε₂ p ε₁ εB α P)

/-- **The payment data are a payment certificate**: the reduction certificate of
the reduction data, with the same matchings. -/
noncomputable def toCertificate : PaymentCertificate H μ ε₂ p εB α :=
  ⟨Δ.toReductionData.toCertificate, Δ.matching⟩

@[simp] theorem toCertificate_matching : Δ.toCertificate.matching = Δ.matching := rfl

theorem toCertificate_reduction (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    Δ.toCertificate.reduction β τ T g = Δ.reduction β τ T g := rfl

theorem toCertificate_bottom (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    Δ.toCertificate.bottom S hS hcyc = Δ.bottom S hS hcyc := rfl

/-- The increase share of the edge `e` at the degree cut `S`:
`x_e / x_f · (I_{f,u} + I_{f,u'})` for `e ∈ f = (u, u')`, as an ordered-pair
sum. -/
noncomputable def topIncreaseAt (β τ : ℝ) (S : Finset (Fin n)) (hS : DegreeCutData H S)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  Δ.toCertificate.topIncreaseAt β τ S hS T e

/-- The increase share of the edge `e` at the cut `S`, if `S` is its edge parent. -/
noncomputable def increaseAt (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  Δ.toCertificate.increaseAt β τ T e S

/-- **The increase `I_e`** of the edge `e`, summed over the cuts of the
hierarchy — at most one nonzero term, at the edge parent. -/
noncomputable def increase (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  Δ.toCertificate.increase β τ T e

/-- **Eq. (34)**: the slack vector `s_e = −r_e + I_e`, on the genuine edges. -/
noncomputable def slack (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  Δ.toCertificate.slack β τ T e

/-! #### Basic bookkeeping -/

theorem topIncreaseAt_eq {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b) {e : Sym2 (Fin n)}
    (he : e ∈ betweenEdges a b) (T : Finset (Sym2 (Fin n))) :
    Δ.topIncreaseAt β τ S hS T e
      = x e / pairSum x a b * (Δ.matching S hS).increase (Δ.reduction β τ) a b T
        + x e / pairSum x b a * (Δ.matching S hS).increase (Δ.reduction β τ) b a T :=
  Δ.toCertificate.topIncreaseAt_eq hS ha hb hab he T

theorem topIncreaseAt_eq_zero_of_not {β τ : ℝ} {S : Finset (Fin n)} (hS : DegreeCutData H S)
    {e : Sym2 (Fin n)}
    (h : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → e ∉ betweenEdges a b)
    (T : Finset (Sym2 (Fin n))) : Δ.topIncreaseAt β τ S hS T e = 0 :=
  Δ.toCertificate.topIncreaseAt_eq_zero_of_not hS h T

theorem topIncreaseAt_nonneg (hx : IsRestrictedLP e₀ x) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {S : Finset (Fin n)} (hS : DegreeCutData H S) (T : Finset (Sym2 (Fin n)))
    (e : Sym2 (Fin n)) : 0 ≤ Δ.topIncreaseAt β τ S hS T e :=
  Δ.toCertificate.topIncreaseAt_nonneg hx hβ hτ hS T e

theorem increaseAt_of_not {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent e S) : Δ.increaseAt β τ T e S = 0 :=
  Δ.toCertificate.increaseAt_of_not h

theorem increaseAt_nonneg (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (S : Finset (Fin n)) :
    0 ≤ Δ.increaseAt β τ T e S :=
  Δ.toCertificate.increaseAt_nonneg hx hεη hβ hτ T e S

theorem increase_nonneg (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : 0 ≤ Δ.increase β τ T e :=
  Δ.toCertificate.increase_nonneg hx hεη hβ hτ T e

/-- The increase is the term at the edge parent. -/
theorem increase_eq_of_isEdgeParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) :
    Δ.increase β τ T e = Δ.increaseAt β τ T e S :=
  Δ.toCertificate.increase_eq_of_isEdgeParent hS

/-- **Bottom edges**: `I_e = I_S x_e` when `p(e) = S` is a near-cycle cut. -/
theorem increase_bottom {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    Δ.increase β τ T e = (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T * x e :=
  Δ.toCertificate.increase_bottom hS hcyc

/-- **Top edges**: `I_e` is the share at the degree cut `p(e) = S`. -/
theorem increase_top {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hdeg : DegreeCutData H S) :
    Δ.increase β τ T e = Δ.topIncreaseAt β τ S hdeg T e :=
  Δ.toCertificate.increase_top hS hdeg

theorem increase_eq_zero_of_neither {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : Δ.increase β τ T e = 0 :=
  Δ.toCertificate.increase_eq_zero_of_neither hS hcyc hdeg

theorem increase_eq_zero_of_noParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent e S) : Δ.increase β τ T e = 0 :=
  Δ.toCertificate.increase_eq_zero_of_noParent h

/-! #### Theorem 4.33 (ii): the pointwise properties of the slack -/

/-- **`s_e ≥ −βx_e`.** -/
theorem slack_lower (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : -(β * x e) ≤ Δ.slack β τ T e :=
  Δ.toCertificate.slack_lower hx hεη hτ hτβ T e

/-- A bad bundle is neither reduced nor increased at its cut. -/
theorem topIncreaseAt_eq_zero_of_bad {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b) {e : Sym2 (Fin n)}
    (he : e ∈ betweenEdges a b) (hbad : ¬ IsGoodBundle μ ε₂ a b) (T : Finset (Sym2 (Fin n))) :
    Δ.topIncreaseAt β τ S hS T e = 0 :=
  Δ.toCertificate.topIncreaseAt_eq_zero_of_bad hS ha hb hab he hbad T

theorem reduction_eq_zero_of_bad {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    {e : Sym2 (Fin n)} (hSe : H.IsEdgeParent e S) (ha : a ∈ H.children S)
    (hb : b ∈ H.children S) (hab : a ≠ b)
    (he : e ∈ betweenEdges a b) (hbad : ¬ IsGoodBundle μ ε₂ a b) (T : Finset (Sym2 (Fin n))) :
    Δ.reduction β τ T e = 0 :=
  Δ.toCertificate.reduction_eq_zero_of_bad hS hSe ha hb hab he hbad T

/-- **`s` is supported on the good edges `E_g`.** -/
theorem slack_eq_zero_of_not_mem_goodEdges {β τ : ℝ} (T : Finset (Sym2 (Fin n)))
    {e : Sym2 (Fin n)} (he : e ∉ goodEdges H μ ε₂) : Δ.slack β τ T e = 0 :=
  Δ.toCertificate.slack_eq_zero_of_not_mem_goodEdges T he

end PaymentData

end TSPGap

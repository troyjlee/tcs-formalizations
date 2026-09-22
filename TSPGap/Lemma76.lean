/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaSevenThreeConsumer
import TSPGap.ReductionCertificate

/-!
# Lemma 7.6: the small-tail endpoint

KKO Lemma 7.6 bounds `E[I_{e,u}] + E[I_{e,v}]` for a good bundle `e = (u,v)` at a
degree cut whose endpoint `u` has a *small* tail, `x(δ↑(u)) < ε_F = 1/10` — the
regime Lemma 7.3 does not cover.

This file carries the interface: the ends of `F`'s and `Z`'s ranges, the
zero-safe coefficient identity with `Z` kept, the per-endpoint form of Eqs. (44)
and (45), and the trivial reduction bound on a whole tail.

⚠️ **A paper-level repair.**  KKO's proof passes from
`m_{e,v} ≥ x_e − ε_F − 4ε_B` to `m_{e,v} ≥ 0.88·x_e`.  That implication is
**false** at the bottom of `x_e`'s range: at `ε_B = 21ε₂ = 0.0042` and
`x_e = 0.9`, the left side is `0.7832` while `0.88·0.9 = 0.792`.  The correct
constant is `0.87` — at `x_e ≥ 1 − ε_F − ε_η` the requirement is
`x_e ≥ (0.1 + 4ε_B)/0.13 = 0.89846…`, which `0.9 − ε_η` meets.  The change
propagates to the final step, which then needs `ε_η ≤ ε₁/400` rather than KKO's
`ε₁/100`; the concrete specialization supplies it from `ε₁ = ε₂/12`,
`ε_η ≤ ε₂²` and `ε₂ ≤ 1/5000`.

Every statement involving the reduction data is proved at the partition-free
`ReductionCertificate` (Lemma 7.3's estimate entering as `HasOddMassBounds`),
and the `ReductionData` forms are wrappers through `ReductionData.toCertificate`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}

/-! ### `F` and `Z` at the ends of their ranges -/

/-- `1 − ε_B ≤ F_u` always.  ⚠️ `fFactor_le_one` and `fFactor_pos` are already in
`MatchingDefs`; this is the lower bound Eq. (47) needs. -/
theorem one_sub_le_fFactor {S u : Finset (Fin n)} {εB : ℝ} (hεB : 0 ≤ εB) :
    1 - εB ≤ fFactor x S εB u := by
  unfold fFactor
  split_ifs <;> linarith

/-- `0 ≤ F_u` for `ε_B ≤ 1`. -/
theorem fFactor_nonneg' {S u : Finset (Fin n)} {εB : ℝ} (hεB : εB ≤ 1) :
    0 ≤ fFactor x S εB u := by
  unfold fFactor
  split_ifs <;> linarith

/-- **`Z_u = 1` at a cut with fewer than four atoms** — KKO's Case 1. -/
theorem zFactor_eq_one_of_card_lt {S u : Finset (Fin n)} {k : ℕ} (hk : k < 4) :
    zFactor x S k u = 1 := by
  unfold zFactor
  exact if_neg fun h => absurd h.1 (by omega)

/-- **`Z_u = 2` at a small tail of a cut with at least four atoms** — KKO's
Case 2.  ⚠️ `IsFractional` and `zFactor`'s test disagree at `q = 1/10`: `Z` uses
`q ≤ 1/10`, so the boundary point carries `Z = 2`. -/
theorem zFactor_eq_two_of {S u : Finset (Fin n)} {k : ℕ} (hk : 4 ≤ k)
    (hq : upSum x S u ≤ 1 / 10) : zFactor x S k u = 2 := by
  unfold zFactor
  exact if_pos ⟨hk, hq⟩

/-- `0 ≤ Z_u`. -/
theorem zFactor_nonneg (S : Finset (Fin n)) (k : ℕ) (u : Finset (Fin n)) :
    (0 : ℝ) ≤ zFactor x S k u :=
  le_trans zero_le_one (one_le_zFactor S k u)

namespace MatchingData

variable {S : Finset (Fin n)} {εB α : ℝ} (M : MatchingData H μ S ε₂ εB α)

/-- **The zero-safe coefficient identity, with `Z` kept**:
`c_{e,u}·x(δ↑(u))·Z_u ≤ m_{e,u}`, with equality unless the tail is massless.
⚠️ `coeff_mul_upSum_le` drops `Z`, which is exactly the factor Lemma 7.6's
Case 2 spends. -/
theorem coeff_mul_upSum_mul_zFactor_le (u u' : Finset (Fin n)) :
    M.coeff u u' * (upSum x S u * zFactor x S (H.children S).card u) ≤ M.m u u' := by
  by_cases h : upSum x S u = 0
  · rw [h, zero_mul, mul_zero]
    exact M.nonneg u u'
  · exact le_of_eq (M.coeff_mul_upSum_mul_zFactor h u')

/-- 🔑 **Eqs. (44) and (45) at one endpoint.**  A reduction bound
`∑_{g∈δ↑(u)} E[r_g·1_odd] ≤ κ·(c·x(δ↑(u)))` gives
`E[I_{e,u}]·Z_u ≤ κ·(c·m_{e,u})`.

Both of KKO's endpoint bounds are this statement: (44) at `κ = τp`, `c = F_u = 1`
(the small tail is not fractional), and (45) at `κ = τp(1 − ε₁/5)`, `c = F_v`.
⚠️ `Z_u` is kept on the **left**, so no division is needed; the consumer rewrites
it to `1` or `2` from the atom count. -/
theorem expect_increase_zFactor_le (hx : IsRestrictedLP e₀ x)
    {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ} {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (u u' : Finset (Fin n))
    (hK : ∑ g ∈ upEdges S u,
      μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      ≤ κ * (c * upSum x S u)) :
    μ.expect (fun T => M.increase r u u' T) * zFactor x S (H.children S).card u
      ≤ κ * (c * M.m u u') := by
  have h1 := M.expect_increase_le hx u u' hK
  have h2 := M.coeff_mul_upSum_mul_zFactor_le u u'
  have hZ0 := zFactor_nonneg (x := x) S (H.children S).card u
  nlinarith [mul_le_mul_of_nonneg_right h1 hZ0,
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hκ hc)]

end MatchingData

/-! ### The trivial reduction bound on a whole tail -/

/-- **`R(δ↑(u)) ≤ τ·p·x(δ↑(u))`**, the bound Eq. (44) feeds on.  Good top edges
pay `τ·p·x_g` outright, bottom edges pay `0.5678·β·p·x_g ≤ τ·p·x_g` by
Corollary 5.10, and the inactive part contributes nothing.
🔑 `0.5678β ≤ τ` is exactly KKO's `0.5678β ≤ τ = 0.571β`. -/
theorem oddReductionMass_tail_le (hx : IsRestrictedLP e₀ x)
    (D : ReductionData H μ ε₂ p ε₁ P) (hBG : D.HasBottomGuarantees)
    {u Pu : Finset (Fin n)} (hu : u ∈ H.cuts) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hp : 0 ≤ p) (hβτ : 0.5678 * β ≤ τ) :
    oddReductionMass D β τ u (tail u Pu) ≤ τ * p * upSum x Pu u :=
  D.toCertificate.oddReductionMass_tail_le hx (D.toCertificate_hasBottomGuarantees hBG) hu hβ hτ hp hβτ

/-! ### Case 1: the three-atom geometry -/

/-- **The row-sum identities at a three-atom cut.**  An atom's cut is its two
bundles plus its tail; the tails sum to `x(δ(S))`; and twice the bundle mass is
`∑_a x(δ(a)) − x(δ(S))`. -/
theorem threeAtom_identities (H : Hierarchy x e₀ εη) {S u v w : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hch : H.children S = {u, v, w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    cutSum x u = pairSum x u v + pairSum x u w + upSum x S u
      ∧ upSum x S u + upSum x S v + upSum x S w = cutSum x S
      ∧ 2 * (pairSum x u v + pairSum x u w + pairSum x v w)
          = cutSum x u + cutSum x v + cutSum x w - cutSum x S := by
  classical
  obtain ⟨hsu, hsv, hsw⟩ := H.siblings_of_three hch huv (Ne.symm huw) (Ne.symm hvw)
  have hu : u ∈ H.children S := by rw [hch]; simp
  have hv : v ∈ H.children S := by rw [hch]; simp
  have hw : w ∈ H.children S := by rw [hch]; simp
  have ha1 := H.arrowSum_eq_sum (x := x) (H.mem_children.mp hu)
  have ha2 := H.arrowSum_eq_sum (x := x) (H.mem_children.mp hv)
  have ha3 := H.arrowSum_eq_sum (x := x) (H.mem_children.mp hw)
  rw [hsu, Finset.sum_pair hvw] at ha1
  rw [hsv, Finset.sum_pair huw] at ha2
  rw [hsw, Finset.sum_pair huv] at ha3
  have hnotmem : u ∉ ({v, w} : Finset (Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, huw⟩
  have hup := H.sum_upSum_children x hS ⟨u, hu⟩
  rw [hch, Finset.sum_insert hnotmem, Finset.sum_pair hvw] at hup
  have e1 : arrowSum x S u = cutSum x u - upSum x S u := rfl
  have e2 : arrowSum x S v = cutSum x v - upSum x S v := rfl
  have e3 : arrowSum x S w = cutSum x w - upSum x S w := rfl
  have c1 := pairSum_comm x v u
  have c2 := pairSum_comm x w u
  have c3 := pairSum_comm x w v
  refine ⟨by linarith, by linarith, by linarith⟩

/-- 🔑 **KKO's Eq. (46).**  At a three-atom cut whose atom `u` has a small tail,
both the bundle `e = (u,v)` and the tail at `v` carry at least `1 − ε_F − ε_η`:
`x_e + x_f ≥ 2 − ε_F` while `x_f ≤ 1 + ε_η`, and symmetrically for the tails. -/
theorem threeAtom_heavy (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts) (hch : H.children S = {u, v, w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hεη : 0 ≤ εη)
    (hsmall : upSum x S u ≤ 1 / 10) :
    1 - 1 / 10 - εη ≤ pairSum x u v ∧ 1 - 1 / 10 - εη ≤ upSum x S v := by
  classical
  obtain ⟨hid1, hid2, -⟩ := threeAtom_identities H hS hch huv huw hvw
  have hu : u ∈ H.children S := by rw [hch]; simp
  have hv : v ∈ H.children S := by rw [hch]; simp
  have hw : w ∈ H.children S := by rw [hch]; simp
  have hucut := H.child_two_le_cutSum hx (H.mem_children.mp hu)
  have hScut := H.two_le_cutSum hx hS
  -- `x_f ≤ 1 + ε_η`, the bundle form of Lemma 2.7
  have hdisj : Disjoint u w :=
    H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hw) huw
  have hsub : u ∪ w ⊆ S := Finset.union_subset (H.children_subset hu) (H.children_subset hw)
  have hne : (u ∪ w).Nonempty :=
    ((H.child_nearMin (H.mem_children.mp hu)).nonempty).mono Finset.subset_union_left
  have hnu : u ∪ w ≠ Finset.univ := fun hc => (H.nearMin S hS).ne_univ
    (Finset.univ_subset_iff.mp (hc ▸ hsub))
  have hf := hx.triangle_pairSum_le hdisj (H.child_nearMin (H.mem_children.mp hu)).cut_le
    (H.child_nearMin (H.mem_children.mp hw)).cut_le hne hnu ((H.avoids S hS).mono hsub)
  -- `x(δ↑(w)) ≤ 1 + ε_η`
  have hwup := upSum_le_one_add hx (H.avoids S hS) (H.mem_children.mp hw).2.2.1
    (H.child_nearMin (H.mem_children.mp hw)).nonempty (H.nearMin S hS).cut_le
    (H.child_nearMin (H.mem_children.mp hw)).cut_le
  exact ⟨by linarith, by linarith⟩

/-! ### Case 1: the row `m_{e,v}` -/

set_option maxHeartbeats 400000 in
-- the two row sums, (26) at the two other bundles, and the bundle ceiling
/-- 🔑 **Case 1's `m_{e,v}` bound**, with KKO's arithmetic repaired.

KKO pass from `m_{e,v} ≥ x_e − ε_F − 4ε_B` to `m_{e,v} ≥ 0.88·x_e`; that step is
**false** at the bottom of `x_e`'s range — at `ε_B = 0.0042` and `x_e = 0.9` the
left side is `0.7832` against `0.792`.  The correct constant is `0.87`.

The chain here keeps `1 − ε_B` multiplied through rather than dividing, which is
both division-free and sharper: what it needs is
`0.13·x_e ≥ 0.1 + 1.9ε_B + 1.5ε_η + α(2 + 1.5ε_η − x_e)`, and Eq. (46)'s
`x_e ≥ 0.9 − ε_η` clears it with about `0.009` to spare. -/
theorem threeAtom_m_ge (hx : IsRestrictedLP e₀ x) {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts)
    {εB α : ℝ} (M : MatchingData H μ S ε₂ εB α) (hch : H.children S = {u, v, w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hα0 : 0 ≤ α) (hα : α ≤ 1e-9) (hεB0 : 0 ≤ εB) (hεB : εB ≤ 0.0042)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hsmall : upSum x S u ≤ 1 / 10) :
    0.87 * pairSum x u v ≤ M.m v u := by
  classical
  obtain ⟨-, hid2, hid3⟩ := threeAtom_identities H hS hch huv huw hvw
  obtain ⟨hxe, -⟩ := threeAtom_heavy hx H hS hch huv huw hvw hεη hsmall
  have hu : u ∈ H.children S := by rw [hch]; simp
  have hv : v ∈ H.children S := by rw [hch]; simp
  have hw : w ∈ H.children S := by rw [hch]; simp
  have hnotmem : u ∉ ({v, w} : Finset (Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, huw⟩
  have hcard : (H.children S).card = 3 := by
    rw [hch, Finset.card_insert_of_notMem hnotmem, Finset.card_pair hvw]
  have hZ : ∀ a : Finset (Fin n), zFactor x S (H.children S).card a = 1 := fun a =>
    zFactor_eq_one_of_card_lt (by omega)
  -- the two row sums, at `Z = 1`
  have hrv := M.sum v hv
  have hrw := M.sum w hw
  rw [hZ v, mul_one] at hrv
  rw [hZ w, mul_one] at hrw
  have hev : (H.children S).erase v = {u, w} := by
    rw [hch]
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact Or.inl h2
      · exact absurd h2 h1
      · exact Or.inr h2
    · rintro (h2 | h2)
      · exact ⟨by rw [h2]; exact huv, Or.inl h2⟩
      · exact ⟨by rw [h2]; exact Ne.symm hvw, Or.inr (Or.inr h2)⟩
  have hew : (H.children S).erase w = {u, v} := by
    rw [hch]
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact Or.inl h2
      · exact Or.inr h2
      · exact absurd h2 h1
    · rintro (h2 | h2)
      · exact ⟨by rw [h2]; exact huw, Or.inl h2⟩
      · exact ⟨by rw [h2]; exact hvw, Or.inr (Or.inl h2)⟩
  rw [hev, Finset.sum_pair huw] at hrv
  rw [hew, Finset.sum_pair huv] at hrw
  -- (26) at the bundles `(v,w)` and `(u,w)`
  have h26vw := M.bound v hv w hw hvw
  have h26uw := M.bound u hu w hw huw
  have hFv := one_sub_le_fFactor (x := x) (S := S) (u := v) hεB0
  have hFw := one_sub_le_fFactor (x := x) (S := S) (u := w) hεB0
  have hFu0 : 0 ≤ fFactor x S εB u := fFactor_nonneg' (by linarith)
  have hmvw := M.nonneg v w
  have hmwv := M.nonneg w v
  have hmwu := M.nonneg w u
  have hmuw := M.nonneg u w
  have hmvu := M.nonneg v u
  have hbvw : (1 - εB) * (M.m v w + M.m w v) ≤ (1 + α) * pairSum x v w := by nlinarith
  have hbuw : (1 - εB) * M.m w u ≤ (1 + α) * pairSum x u w := by nlinarith
  -- the bundle ceiling
  have hcu := (H.child_nearMin (H.mem_children.mp hu)).cut_le
  have hcv := (H.child_nearMin (H.mem_children.mp hv)).cut_le
  have hcw := (H.child_nearMin (H.mem_children.mp hw)).cut_le
  have hScut := H.two_le_cutSum hx hS
  have hceil : pairSum x u w + pairSum x v w ≤ 2 + 3 * εη / 2 - pairSum x u v := by
    linarith
  -- the tails at `v` and `w`
  have htails : 2 - 1 / 10 ≤ upSum x S v + upSum x S w := by linarith
  -- assemble, keeping `1 − ε_B` multiplied through
  have hprod : α * (pairSum x u w + pairSum x v w) ≤ 1.2 * α := by nlinarith
  nlinarith [hbvw, hbuw, hceil, htails, hprod, mul_nonneg hεB0 hmvu]

/-! ### Lemma 7.6's closing arithmetic -/

/-- **The three-atom close.**  `1 + 2ε_η − (ε₁/5)·0.87·(1 − 21ε₂) ≤ 1 − ε₁/6`.

🔑 This is where the repaired `0.87` costs something: it needs
`2ε_η ≤ ε₁[0.87(1 − 21ε₂)/5 − 1/6] ≈ 0.0066·ε₁`, i.e. `ε_η ≤ ε₁/303`.  KKO's
stated `ε_η ≤ ε₁/100` is **not** enough — not even at their `0.88`, which needs
`ε₁/233` — so the hypothesis carried here is `ε_η ≤ ε₁/400`, which the concrete
specialization supplies from `ε₁ = ε₂/12`, `ε_η ≤ ε₂²` and `ε₂ ≤ 1/5000`.

The range hypothesis is the paper's `ε₁ ≤ ε₂/10`; it enters only through
`0 ≤ ε₂`.  (The development's global `ε₁ = ε₂/12` is a specialization, needed by
Lemma 7.3 and imposed by Lemma 7.2, not by this lemma.) -/
theorem lemma76_arith_three {ε₁ ε₂ εη : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10)
    (hε₂ : ε₂ ≤ 0.0002) (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁ / 400) :
    1 + 2 * εη - ε₁ / 5 * (0.87 * (1 - 21 * ε₂)) ≤ 1 - ε₁ / 6 := by
  nlinarith [mul_nonneg hε₁0 (by linarith : (0:ℝ) ≤ ε₂)]

/-- **The `ε_η ≤ ε₁/400` hypothesis, discharged concretely.**  At `ε₁ = ε₂/12`,
`ε_η ≤ ε₂²` and `ε₂ ≤ 1/5000` one has `ε_η ≤ ε₂²  ≤ ε₂/4800 = ε₁/400`. -/
theorem epsEta_le_eps1_div_400 {ε₁ ε₂ εη : ℝ} (hε₁eq : ε₁ = ε₂ / 12) (hε₂0 : 0 ≤ ε₂)
    (hε₂ : ε₂ ≤ 1 / 5000) (hεηsq : εη ≤ ε₂ ^ 2) : εη ≤ ε₁ / 400 := by
  rw [hε₁eq]
  nlinarith

/-- **The card-`≥ 4` close, both tails small.**  Halving both endpoints leaves
`(1 + 2ε_η)/2`, far below `1 − ε₁/6`. -/
theorem lemma76_arith_low {ε₁ εη : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ 1)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) :
    (1 + 2 * εη) / 2 ≤ 1 - ε₁ / 6 := by linarith

/-- **The card-`≥ 4` close, one tail large.**  The large endpoint pays
`1 − ε₁/5` and the small one is halved, so `(1 − ε₁/5)(1 + 2ε_η) ≤ 1 − ε₁/6`
already at `ε_η ≤ ε₁/60`. -/
theorem lemma76_arith_high {ε₁ εη : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ 1)
    (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁ / 400) :
    (1 - ε₁ / 5) * (1 + 2 * εη) ≤ 1 - ε₁ / 6 := by nlinarith

/-! ### The third atom -/

/-- At a three-atom cut, two distinct atoms determine the third. -/
theorem exists_third_atom (H : Hierarchy x e₀ εη) {S u v : Finset (Fin n)}
    (hcard : (H.children S).card = 3) (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) :
    ∃ w ∈ H.children S, u ≠ w ∧ v ≠ w ∧ H.children S = {u, v, w} := by
  classical
  obtain ⟨w, hw, hwu, hwv⟩ : ∃ w ∈ H.children S, w ≠ u ∧ w ≠ v := by
    by_contra hcon
    push_neg at hcon
    have hsub : H.children S ⊆ {u, v} := fun y hy => by
      by_cases h : y = u
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [hcon y hy h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  have hnotmem : u ∉ ({v, w} : Finset (Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, Ne.symm hwu⟩
  refine ⟨w, hw, Ne.symm hwu, Ne.symm hwv, ?_⟩
  symm
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  · rw [hcard, Finset.card_insert_of_notMem hnotmem, Finset.card_pair (Ne.symm hwv)]

/-! ### Lemma 7.6 -/

set_option maxHeartbeats 800000 in
-- (44) at the small endpoint, (45) at the large one, (26), and the `m_{e,v}` bound
/-- ⭐ **Lemma 7.6, Case 1** (`|A(S)| = 3`).  Here `Z_u = 1`, so the small
endpoint pays its full `τ·p·F_u·m_{e,u}` and (26) alone would only give
`τ·p·(1 + 2ε_η)·x_e`.  The saving comes from the *other* endpoint: `v`'s tail is
heavy by Eq. (46), so Lemma 7.3 applies there at rate `1 − ε₁/5`, and
`threeAtom_m_ge` shows `v`'s row keeps `0.87·x_e` of the bundle. -/
theorem ReductionCertificate.lemma76_three (hx : IsRestrictedLP e₀ x)
    (C : ReductionCertificate H μ ε₂ p) (hBG : C.HasBottomGuarantees)
    {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hch : H.children S = {u, v, w}) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hsmall : upSum x S u < 1 / 10)
    (h45 : ∑ g ∈ upEdges S v,
        μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) v) * upSum x S v) :
    μ.expect (fun T => M.increase (C.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  classical
  have hε₂0 : (0:ℝ) ≤ ε₂ := by linarith
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hu : u ∈ H.children S := by rw [hch]; simp
  have hv : v ∈ H.children S := by rw [hch]; simp
  have hnotmem : u ∉ ({v, w} : Finset (Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, huw⟩
  have hcard : (H.children S).card = 3 := by
    rw [hch, Finset.card_insert_of_notMem hnotmem, Finset.card_pair hvw]
  have hZ : ∀ a : Finset (Fin n), zFactor x S (H.children S).card a = 1 := fun a =>
    zFactor_eq_one_of_card_lt (by omega)
  have hxe0 : 0 ≤ pairSum x u v := pairSum_nonneg (fun e => hx.nonneg e) u v
  have hFu : fFactor x S (21 * ε₂) u = 1 := fFactor_eq_one_of_lt hsmall
  have hFv0 : 0 ≤ fFactor x S (21 * ε₂) v := fFactor_nonneg' (by linarith)
  have hFv := one_sub_le_fFactor (x := x) (S := S) (u := v) (εB := 21 * ε₂) (by linarith)
  -- (44) at the small endpoint
  have h44 : ∑ g ∈ upEdges S u,
      μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      ≤ τ * p * (fFactor x S (21 * ε₂) u * upSum x S u) := by
    rw [hFu, one_mul]
    exact C.oddReductionMass_tail_le hx hBG (H.mem_cuts_of_mem_children hu) hβ hτ hp
      (by rw [hτeq]; linarith)
  have hUb := M.expect_increase_zFactor_le hx (r := C.reduction β τ) hτp
    (fFactor_nonneg' (x := x) (S := S) (u := u) (εB := 21 * ε₂) (by linarith)) u v h44
  rw [hZ u, mul_one] at hUb
  -- (45) at the heavy endpoint
  have h45' : ∑ g ∈ upEdges S v,
      μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ (τ * p * (1 - ε₁ / 5)) * (fFactor x S (21 * ε₂) v * upSum x S v) :=
    le_of_le_of_eq h45 (by ring)
  have hVb := M.expect_increase_zFactor_le hx (r := C.reduction β τ)
    (by nlinarith : (0:ℝ) ≤ τ * p * (1 - ε₁ / 5)) hFv0 v u h45'
  rw [hZ v, mul_one] at hVb
  -- (26) and the row bound
  have h26 := M.bound u hu v hv huv
  have hm := threeAtom_m_ge hx hS M hch huv huw hvw (by linarith) (by linarith)
    (by linarith) (by linarith) hεη hεηcap (le_of_lt hsmall)
  have hmvu0 : 0 ≤ M.m v u := M.nonneg v u
  have hsave : (1 - 21 * ε₂) * (0.87 * pairSum x u v)
      ≤ fFactor x S (21 * ε₂) v * M.m v u := by
    have t1 : (1 - 21 * ε₂) * M.m v u ≤ fFactor x S (21 * ε₂) v * M.m v u :=
      mul_le_mul_of_nonneg_right hFv hmvu0
    have t2 : (1 - 21 * ε₂) * (0.87 * pairSum x u v) ≤ (1 - 21 * ε₂) * M.m v u :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    linarith
  have s4 : τ * p * (ε₁ / 5) * ((1 - 21 * ε₂) * (0.87 * pairSum x u v))
      ≤ τ * p * (ε₁ / 5) * (fFactor x S (21 * ε₂) v * M.m v u) :=
    mul_le_mul_of_nonneg_left hsave (by positivity)
  have s5 : τ * p * (M.m u v * fFactor x S (21 * ε₂) u
        + M.m v u * fFactor x S (21 * ε₂) v)
      ≤ τ * p * ((1 + 2 * εη) * pairSum x u v) :=
    mul_le_mul_of_nonneg_left h26 hτp
  have s6 : τ * p * pairSum x u v * (1 + 2 * εη - ε₁ / 5 * (0.87 * (1 - 21 * ε₂)))
      ≤ τ * p * pairSum x u v * (1 - ε₁ / 6) :=
    mul_le_mul_of_nonneg_left (lemma76_arith_three hε₁0 hε₁ hε₂ hεη hεη₁)
      (mul_nonneg hτp hxe0)
  linarith [hUb, hVb, s4, s5, s6]

/-! ### Lemma 7.6 -/

/-- ⭐ **Lemma 7.6, Case 1** (`|A(S)| = 3`).  Here `Z_u = 1`, so the small
endpoint pays its full `τ·p·F_u·m_{e,u}` and (26) alone would only give
`τ·p·(1 + 2ε_η)·x_e`.  The saving comes from the *other* endpoint: `v`'s tail is
heavy by Eq. (46), so Lemma 7.3 applies there at rate `1 − ε₁/5`, and
`threeAtom_m_ge` shows `v`'s row keeps `0.87·x_e` of the bundle. -/
theorem lemma76_three (hx : IsRestrictedLP e₀ x)
    (D : ReductionData H μ ε₂ p ε₁ P) (hBG : D.HasBottomGuarantees)
    {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hch : H.children S = {u, v, w}) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hsmall : upSum x S u < 1 / 10)
    (h45 : ∑ g ∈ upEdges S v,
        μ.expect (fun T => D.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) v) * upSum x S v) :
    μ.expect (fun T => M.increase (D.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma76_three hx D.toCertificate (D.toCertificate_hasBottomGuarantees hBG) hS M hch huv huw hvw hβ hτeq hp hε₁0 hε₁ hε₂ hεη hεηcap hεη₁ hsmall h45

set_option maxHeartbeats 400000 in
-- both tails small: `Z = 2` at both endpoints halves (26)
/-- ⭐ **Lemma 7.6, Case 2, both tails small** (`|A(S)| ≥ 4`).  Here `Z = 2` at
both endpoints, so (26) is halved outright and no saving is needed. -/
theorem ReductionCertificate.lemma76_four_low (hx : IsRestrictedLP e₀ x)
    (C : ReductionCertificate H μ ε₂ p) (hBG : C.HasBottomGuarantees)
    {S u v : Finset (Fin n)}
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hcard : 4 ≤ (H.children S).card)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ 1) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (hsu : upSum x S u < 1 / 10) (hsv : upSum x S v < 1 / 10) :
    μ.expect (fun T => M.increase (C.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hxe0 : 0 ≤ pairSum x u v := pairSum_nonneg (fun e => hx.nonneg e) u v
  have hFu : fFactor x S (21 * ε₂) u = 1 := fFactor_eq_one_of_lt hsu
  have hFv : fFactor x S (21 * ε₂) v = 1 := fFactor_eq_one_of_lt hsv
  have hZu : zFactor x S (H.children S).card u = 2 :=
    zFactor_eq_two_of hcard (le_of_lt hsu)
  have hZv : zFactor x S (H.children S).card v = 2 :=
    zFactor_eq_two_of hcard (le_of_lt hsv)
  have hFu0 : (0:ℝ) ≤ fFactor x S (21 * ε₂) u := by rw [hFu]; norm_num
  have hFv0 : (0:ℝ) ≤ fFactor x S (21 * ε₂) v := by rw [hFv]; norm_num
  have h44u : ∑ g ∈ upEdges S u,
      μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      ≤ τ * p * (fFactor x S (21 * ε₂) u * upSum x S u) := by
    rw [hFu, one_mul]
    exact C.oddReductionMass_tail_le hx hBG (H.mem_cuts_of_mem_children hu) hβ hτ hp
      (by rw [hτeq]; linarith)
  have h44v : ∑ g ∈ upEdges S v,
      μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ τ * p * (fFactor x S (21 * ε₂) v * upSum x S v) := by
    rw [hFv, one_mul]
    exact C.oddReductionMass_tail_le hx hBG (H.mem_cuts_of_mem_children hv) hβ hτ hp
      (by rw [hτeq]; linarith)
  have hUb := M.expect_increase_zFactor_le hx (r := C.reduction β τ) hτp hFu0 u v h44u
  have hVb := M.expect_increase_zFactor_le hx (r := C.reduction β τ) hτp hFv0 v u h44v
  rw [hZu] at hUb
  rw [hZv] at hVb
  have h26 := M.bound u hu v hv huv
  have s5 : τ * p * (M.m u v * fFactor x S (21 * ε₂) u
        + M.m v u * fFactor x S (21 * ε₂) v)
      ≤ τ * p * ((1 + 2 * εη) * pairSum x u v) :=
    mul_le_mul_of_nonneg_left h26 hτp
  have s6 : τ * p * pairSum x u v * ((1 + 2 * εη) / 2)
      ≤ τ * p * pairSum x u v * (1 - ε₁ / 6) :=
    mul_le_mul_of_nonneg_left (lemma76_arith_low hε₁0 hε₁ hεη hεηcap)
      (mul_nonneg hτp hxe0)
  linarith [hUb, hVb, s5, s6]

-- `Z = 2` halves the small endpoint; the heavy one pays Lemma 7.3's rate

/-- ⭐ **Lemma 7.6, Case 2, both tails small** (`|A(S)| ≥ 4`).  Here `Z = 2` at
both endpoints, so (26) is halved outright and no saving is needed. -/
theorem lemma76_four_low (hx : IsRestrictedLP e₀ x)
    (D : ReductionData H μ ε₂ p ε₁ P) (hBG : D.HasBottomGuarantees)
    {S u v : Finset (Fin n)}
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hcard : 4 ≤ (H.children S).card)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ 1) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (hsu : upSum x S u < 1 / 10) (hsv : upSum x S v < 1 / 10) :
    μ.expect (fun T => M.increase (D.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma76_four_low hx D.toCertificate (D.toCertificate_hasBottomGuarantees hBG) M hcard hu hv huv hβ hτeq hp hε₁0 hε₁ hεη hεηcap hsu hsv

/-- ⭐ **Lemma 7.6, Case 2, one tail large** (`|A(S)| ≥ 4`).  The small endpoint
is halved by `Z_u = 2` and the heavy one pays `1 − ε₁/5`, so (26) closes at
`(1 − ε₁/5)(1 + 2ε_η) ≤ 1 − ε₁/6`. -/
theorem ReductionCertificate.lemma76_four_high (hx : IsRestrictedLP e₀ x)
    (C : ReductionCertificate H μ ε₂ p) (hBG : C.HasBottomGuarantees)
    {S u v : Finset (Fin n)}
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hcard : 4 ≤ (H.children S).card)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁ / 400)
    (hsu : upSum x S u < 1 / 10)
    (h45 : ∑ g ∈ upEdges S v,
        μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) v) * upSum x S v) :
    μ.expect (fun T => M.increase (C.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  classical
  have hε₂0 : (0:ℝ) ≤ ε₂ := by linarith
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hxe0 : 0 ≤ pairSum x u v := pairSum_nonneg (fun e => hx.nonneg e) u v
  have hFu : fFactor x S (21 * ε₂) u = 1 := fFactor_eq_one_of_lt hsu
  have hFu0 : (0:ℝ) ≤ fFactor x S (21 * ε₂) u := by rw [hFu]; norm_num
  have hFv0 : 0 ≤ fFactor x S (21 * ε₂) v := fFactor_nonneg' (by linarith)
  have hZu : zFactor x S (H.children S).card u = 2 :=
    zFactor_eq_two_of hcard (le_of_lt hsu)
  -- the small endpoint, halved
  have h44u : ∑ g ∈ upEdges S u,
      μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      ≤ τ * p * (fFactor x S (21 * ε₂) u * upSum x S u) := by
    rw [hFu, one_mul]
    exact C.oddReductionMass_tail_le hx hBG (H.mem_cuts_of_mem_children hu) hβ hτ hp
      (by rw [hτeq]; linarith)
  have hUb := M.expect_increase_zFactor_le hx (r := C.reduction β τ) hτp hFu0 u v h44u
  rw [hZu] at hUb
  -- the heavy endpoint
  have h45' : ∑ g ∈ upEdges S v,
      μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ (τ * p * (1 - ε₁ / 5)) * (fFactor x S (21 * ε₂) v * upSum x S v) :=
    le_of_le_of_eq h45 (by ring)
  have hVb := M.expect_increase_zFactor_le hx (r := C.reduction β τ)
    (by nlinarith : (0:ℝ) ≤ τ * p * (1 - ε₁ / 5)) hFv0 v u h45'
  have hEv0 : 0 ≤ μ.expect (fun T => M.increase (C.reduction β τ) v u T) := by
    unfold TreeDist.expect
    refine Finset.sum_nonneg fun T _ => mul_nonneg (μ.prob_nonneg T) ?_
    exact M.increase_nonneg hx (fun g => C.reduction_nonneg hβ hτ (hx.nonneg g) T) v u
  have hZv1 : (1:ℝ) ≤ zFactor x S (H.children S).card v :=
    one_le_zFactor (x := x) S (H.children S).card v
  have hVb' : μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ (τ * p * (1 - ε₁ / 5)) * (fFactor x S (21 * ε₂) v * M.m v u) := by
    nlinarith [hVb, hEv0, hZv1]
  -- (26) and the closing arithmetic
  have h26 := M.bound u hu v hv huv
  have hA0 : 0 ≤ M.m u v * fFactor x S (21 * ε₂) u := mul_nonneg (M.nonneg u v) hFu0
  have hB0 : 0 ≤ M.m v u * fFactor x S (21 * ε₂) v := mul_nonneg (M.nonneg v u) hFv0
  have hmain : M.m u v * fFactor x S (21 * ε₂) u / 2
      + (1 - ε₁ / 5) * (M.m v u * fFactor x S (21 * ε₂) v)
      ≤ (1 - ε₁ / 6) * pairSum x u v := by
    nlinarith [mul_le_mul_of_nonneg_left h26 (show (0:ℝ) ≤ 1 - ε₁ / 5 by nlinarith),
      mul_le_mul_of_nonneg_right (lemma76_arith_high hε₁0 (by nlinarith) hεη hεη₁) hxe0,
      hA0, hB0]
  have hscaled := mul_le_mul_of_nonneg_left hmain hτp
  nlinarith [hUb, hVb', hscaled]

/-- ⭐ **Lemma 7.6, Case 2, one tail large** (`|A(S)| ≥ 4`).  The small endpoint
is halved by `Z_u = 2` and the heavy one pays `1 − ε₁/5`, so (26) closes at
`(1 − ε₁/5)(1 + 2ε_η) ≤ 1 − ε₁/6`. -/
theorem lemma76_four_high (hx : IsRestrictedLP e₀ x)
    (D : ReductionData H μ ε₂ p ε₁ P) (hBG : D.HasBottomGuarantees)
    {S u v : Finset (Fin n)}
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hcard : 4 ≤ (H.children S).card)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁ / 400)
    (hsu : upSum x S u < 1 / 10)
    (h45 : ∑ g ∈ upEdges S v,
        μ.expect (fun T => D.reduction β τ T g * if Odd (T ∩ cutEdges v).card then 1 else 0)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) v) * upSum x S v) :
    μ.expect (fun T => M.increase (D.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma76_four_high hx D.toCertificate (D.toCertificate_hasBottomGuarantees hBG) M hcard hu hv huv hβ hτeq hp hε₁0 hε₁ hε₂ hεη hεη₁ hsu h45

set_option maxHeartbeats 800000 in
-- three atoms, or four-plus with the second tail small or large
/-- ⭐⭐ **KKO Lemma 7.6**: at a bundle `e = (u,v)` of a degree cut whose endpoint
`u` has a *small* tail, `E[I_{e,u}] + E[I_{e,v}] ≤ τ·p·(1 − ε₁/6)·x_e`.

🔑 **No goodness hypothesis is needed**, though KKO state one: `m` vanishes off
the good ordered pairs (`MatchingData.support`), hence so do `coeff` and
`increase`, so at a bad pair the statement holds with both terms zero.  The
range hypotheses are the paper's (`ε₁ ≤ ε₂/10`, `ε₂ ≤ 0.0002`), except that the
repaired arithmetic needs `ε_η ≤ ε₁/400` where KKO state `ε₁/100`
(`lemma76_arith_three`); Lemma 7.2 below is where the development's global
`ε₁ ≤ ε₂/12` (Lemma 7.3's range) is imposed.

`h73` is Lemma 7.3, assumed at every atom whose tail is large enough for it —
the form Lemma 7.2 supplies.

The three branches are KKO's: exactly three atoms (where `Z = 1` forces the
`m_{e,v} ≥ 0.87·x_e` route, and Eq. (46) guarantees `v`'s tail is heavy enough
for Lemma 7.3); four or more with both tails small (`Z = 2` at both ends); and
four or more with `v`'s tail large. -/

theorem ReductionCertificate.lemma_7_6 (hx : IsRestrictedLP e₀ x)
    (C : ReductionCertificate H μ ε₂ p) (hBG : C.HasBottomGuarantees)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hsmall : upSum x S u < 1 / 10)
    (h73 : ∀ a ∈ H.children S, 1 / 10 ≤ upSum x S a →
      ∑ g ∈ upEdges S a,
        μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges a).card then 1 else 0)
        ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) a) * upSum x S a) :
    μ.expect (fun T => M.increase (C.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  classical
  have hε₂0 : (0:ℝ) ≤ ε₂ := by linarith
  rcases eq_or_lt_of_le hSdeg.three with h3 | h4
  · -- exactly three atoms
    obtain ⟨w, hw, huw, hvw, hch⟩ := exists_third_atom H h3.symm hu hv huv
    have hheavy :=
      (threeAtom_heavy hx H hSdeg.mem hch huv huw hvw hεη (le_of_lt hsmall)).2
    exact ReductionCertificate.lemma76_three hx C hBG hSdeg.mem M hch huv huw hvw hβ hτeq hp hε₁0 hε₁ hε₂ hεη
      hεηcap hεη₁ hsmall (h73 v hv (by linarith))
  · -- four atoms or more
    have hcard : 4 ≤ (H.children S).card := by omega
    by_cases hsv : upSum x S v < 1 / 10
    · exact ReductionCertificate.lemma76_four_low hx C hBG M hcard hu hv huv hβ hτeq hp hε₁0 (by nlinarith)
        hεη hεηcap hsmall hsv
    · push_neg at hsv
      exact ReductionCertificate.lemma76_four_high hx C hBG M hcard hu hv huv hβ hτeq hp hε₁0 hε₁ hε₂
        hεη hεη₁ hsmall (h73 v hv hsv)

theorem lemma_7_6 (hx : IsRestrictedLP e₀ x)
    (D : ReductionData H μ ε₂ p ε₁ P) (hBG : D.HasBottomGuarantees)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 10) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hsmall : upSum x S u < 1 / 10)
    (h73 : ∀ a ∈ H.children S, 1 / 10 ≤ upSum x S a →
      ∑ g ∈ upEdges S a,
        μ.expect (fun T => D.reduction β τ T g * if Odd (T ∩ cutEdges a).card then 1 else 0)
        ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) a) * upSum x S a) :
    μ.expect (fun T => M.increase (D.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma_7_6 hx D.toCertificate (D.toCertificate_hasBottomGuarantees hBG) hSdeg M hu hv huv hβ hτeq hp hε₁0 hε₁ hε₂ hεη hεηcap hεη₁ hsmall h73

/-! ### Lemma 7.2 -/

set_option maxHeartbeats 800000 in
-- either endpoint small (Lemma 7.6, in either orientation), or both large (Eq. (39))
/-- ⭐⭐ **KKO Lemma 7.2**: for *every* bundle `e = (u,v)` of a degree cut,
`E[I_{e,u}] + E[I_{e,v}] ≤ τ·p·(1 − ε₁/6)·x_e`.

🔑 As in Lemma 7.6, goodness is not assumed: the increase vanishes at a bad
ordered pair, so the bound is trivial there.  KKO restrict the statement to good
top bundles because that is where it is used.

If either tail is small, Lemma 7.6 applies — in the orientation that puts the
small tail first, the sum being symmetric.  If both are large, Lemma 7.3 applies
at both ends and the symmetric Eq. (39) wrapper closes it:
`(1 − ε₁/5)(1 + 2ε_η) ≤ 1 − ε₁/6`.

⚠️ This is the **conditional** form: the per-atom Lemma 7.3 estimate arrives as
the hypothesis `h73`, which KKO's Lemma 7.2 does not have — they prove 7.3 in the
same section and use it directly.  `lemma_7_2` below is the paper-facing
statement, and discharges `h73` from the proved `lemma_7_3`. -/
theorem ReductionCertificate.lemma_7_2_of_lemma_7_3 (hx : IsRestrictedLP e₀ x)
    (C : ReductionCertificate H μ ε₂ p) (hBG : C.HasBottomGuarantees)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (h73 : ∀ a ∈ H.children S, 1 / 10 ≤ upSum x S a →
      ∑ g ∈ upEdges S a,
        μ.expect (fun T => C.reduction β τ T g * if Odd (T ∩ cutEdges a).card then 1 else 0)
        ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) a) * upSum x S a) :
    μ.expect (fun T => M.increase (C.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hxe0 : 0 ≤ pairSum x u v := pairSum_nonneg (fun e => hx.nonneg e) u v
  by_cases hsu : upSum x S u < 1 / 10
  · exact ReductionCertificate.lemma_7_6 hx C hBG hSdeg M hu hv huv hβ hτeq hp hε₁0
      (by linarith) hε₂ hεη hεηcap hεη₁ hsu h73
  · by_cases hsv : upSum x S v < 1 / 10
    · -- the small tail is `v`'s; run Lemma 7.6 in the other orientation
      have hswap := ReductionCertificate.lemma_7_6 hx C hBG hSdeg M hv hu (Ne.symm huv) hβ hτeq hp hε₁0
        (by linarith) hε₂ hεη hεηcap hεη₁ hsv h73
      rw [pairSum_comm x v u] at hswap
      linarith
    · -- both tails are large: Lemma 7.3 at both ends
      push_neg at hsu hsv
      have hκ : (0:ℝ) ≤ τ * p * (1 - ε₁ / 5) := by nlinarith
      have hKu : ∑ g ∈ upEdges S u,
          μ.expect (fun T => C.reduction β τ T g *
            if Odd (T ∩ cutEdges u).card then 1 else 0)
          ≤ τ * p * (1 - ε₁ / 5) * upSum x S u * fFactor x S (21 * ε₂) u :=
        le_of_le_of_eq (h73 u hu hsu) (by ring)
      have hKv : ∑ g ∈ upEdges S v,
          μ.expect (fun T => C.reduction β τ T g *
            if Odd (T ∩ cutEdges v).card then 1 else 0)
          ≤ τ * p * (1 - ε₁ / 5) * upSum x S v * fFactor x S (21 * ε₂) v :=
        le_of_le_of_eq (h73 v hv hsv) (by ring)
      have h39 := M.expect_increase_add_le hx (by linarith) hκ hu hv huv hKu hKv
      have harith := mul_le_mul_of_nonneg_left
        (lemma76_arith_high hε₁0 (by nlinarith) hεη hεη₁) (mul_nonneg hτp hxe0)
      nlinarith [h39, harith]

/-! ### Lemma 7.2 -/

/-- ⭐⭐ **KKO Lemma 7.2**: for *every* bundle `e = (u,v)` of a degree cut,
`E[I_{e,u}] + E[I_{e,v}] ≤ τ·p·(1 − ε₁/6)·x_e`.

🔑 As in Lemma 7.6, goodness is not assumed: the increase vanishes at a bad
ordered pair, so the bound is trivial there.  KKO restrict the statement to good
top bundles because that is where it is used.

If either tail is small, Lemma 7.6 applies — in the orientation that puts the
small tail first, the sum being symmetric.  If both are large, Lemma 7.3 applies
at both ends and the symmetric Eq. (39) wrapper closes it:
`(1 − ε₁/5)(1 + 2ε_η) ≤ 1 − ε₁/6`.

⚠️ This is the **conditional** form: the per-atom Lemma 7.3 estimate arrives as
the hypothesis `h73`, which KKO's Lemma 7.2 does not have — they prove 7.3 in the
same section and use it directly.  `lemma_7_2` below is the paper-facing
statement, and discharges `h73` from the proved `lemma_7_3`. -/
theorem lemma_7_2_of_lemma_7_3 (hx : IsRestrictedLP e₀ x)
    (D : ReductionData H μ ε₂ p ε₁ P) (hBG : D.HasBottomGuarantees)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (h73 : ∀ a ∈ H.children S, 1 / 10 ≤ upSum x S a →
      ∑ g ∈ upEdges S a,
        μ.expect (fun T => D.reduction β τ T g * if Odd (T ∩ cutEdges a).card then 1 else 0)
        ≤ τ * p * ((1 - ε₁ / 5) * fFactor x S (21 * ε₂) a) * upSum x S a) :
    μ.expect (fun T => M.increase (D.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma_7_2_of_lemma_7_3 hx D.toCertificate (D.toCertificate_hasBottomGuarantees hBG) hSdeg M hu hv huv hβ hτeq hp hε₁0 hε₁ hε₂ hεη hεηcap hεη₁ h73

/-- **KKO21 Lemma 7.2 (Top Edge Increase)**, at the certificate: Lemma 7.3's
estimate enters as `HasOddMassBounds`, discharged at each atom through
`Hierarchy.child_nearMin`. -/
theorem ReductionCertificate.lemma_7_2 (hx : IsRestrictedLP e₀ x)
    (C : ReductionCertificate H μ ε₂ p) (hBG : C.HasBottomGuarantees)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hodd : C.HasOddMassBounds ε₁ β τ) :
    μ.expect (fun T => M.increase (C.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (C.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  refine ReductionCertificate.lemma_7_2_of_lemma_7_3 hx C hBG hSdeg M hu hv huv hβ hτeq hp hε₁0
    hε₁ hε₂ hεη hεηcap hεη₁ ?_
  intro a ha hq
  have haNM : IsNearMinCut x εη a := H.child_nearMin (H.mem_children.mp ha)
  simpa [ReductionCertificate.oddReductionMass, tail] using
    hodd.odd_mass_le (H.mem_children.mp ha) haNM.nonempty haNM.ne_univ haNM.cut_le hq

/-- **KKO21 Lemma 7.2 (Top Edge Increase).**  For a degree cut `S` and a good
edge bundle `e = (u,v)` with `p(e) = S`, if `ε₂ ≤ 0.0002`, `ε₁ ≤ ε₂/12` and
`ε_η ≤ ε₁/400`, then

`E[I_{e,u}] + E[I_{e,v}] ≤ p τ x_e (1 − ε₁/6)`.

This is the paper's statement: no Lemma 7.3 estimate is assumed.  The proof runs
`lemma_7_2_of_lemma_7_3` and discharges its `h73` at each atom from the proved
`lemma_7_3`, whose own inputs — the max-entropy limit, the degree rule, the top
rectangular and descendant-control certificates, and the `p ≤ 0.005ε₂²`,
`ε_η ≤ ε₂²` budgets — appear here as binders.

The three side conditions `lemma_7_3` asks of each atom — nonempty, not all of
`V`, and `x(δ(a)) ≤ 2 + ε_η` — are exactly the three fields of `IsNearMinCut`,
and a child of a cut is a cut, so `Hierarchy.child_nearMin` supplies all three
at once.  ⚠️ KKO's `ε_η ≤ ε₁/100` is sharpened
to `ε_η ≤ ε₁/400`, which is what `lemma_7_2_of_lemma_7_3`'s Eq. (39) step needs;
it implies the `/100` form that `lemma_7_3` asks for. -/
theorem lemma_7_2 (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hHdeg : H.DegreeRule) (D : ReductionData H μ ε₂ p ε₁ P)
    (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangular)
    (hctrl : P.ControlsDescendants)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hεηsq : εη ≤ ε₂ ^ 2) :
    μ.expect (fun T => M.increase (D.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma_7_2 hx D.toCertificate (D.toCertificate_hasBottomGuarantees hBG)
    hSdeg M hu hv huv hβ hτeq hp hε₁0 hε₁ hε₂ hεη hεηcap hεη₁
    (D.toCertificate_hasOddMassBounds hx hμ hεη hεηcap (by linarith) hεηsq hHdeg hBG hTR hctrl
      hβ hτeq hp hple hε₁0 hε₁ hε₂ hε₂0)

end TSPGap

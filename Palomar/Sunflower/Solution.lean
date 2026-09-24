/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Sunflower

/-!
# Sunflower bounds: Palomar proof adapter

Finite families contain no repeated sets. All constants below are explicit
and independent of the ambient type. `lg` follows ALWZ arXiv v3 (base 1.9).
Definitions are repeated to keep the Challenge independent of this proof library. See `Palomar/README.md` for the source map.
-/

namespace PalomarSunflower

open Finset
variable {α : Type*} [DecidableEq α]

/-- Distinct petals intersect in the same core. -/
def IsSunflowerWith (𝒮 : Finset (Finset α)) (K : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒮 → ∀ ⦃T⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = K

/-- A sunflower with exactly `r` distinct petals. -/
def IsSunflower (r : ℕ) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧ ∃ K, IsSunflowerWith 𝒮 K

/-- The family contains an `r`-petal sunflower. -/
def HasSunflower (r : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∃ 𝒮 ⊆ 𝓕, IsSunflower r 𝒮

/-- Every member has exactly `w` elements. -/
def IsUniform (w : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝓕 → S.card = w

/-- Every member has at most `w` elements. -/
def IsBounded (w : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝓕 → S.card ≤ w

/-- Base 1.9, so the iterated logarithm is positive already at width two. -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 1.9 x

/-- An explicit absolute constant for both ALWZ proof routes. -/
noncomputable def alwzConstant : ℝ := max (2 ^ 41) (1 / lg (lg 2))

/-- The ALWZ cardinality threshold. -/
noncomputable def alwzBound (C : ℝ) (r w : ℕ) : ℝ :=
  (C * r ^ 3 * lg w * lg (lg w)) ^ w

/-- The link on `Z`, with `Z` removed from every member containing it. -/
def link (𝓕 : Finset (Finset α)) (Z : Finset α) : Finset (Finset α) :=
  (𝓕.filter fun S => Z ⊆ S).image fun S => S \ Z

/-- Rao's absolute spread condition. -/
def IsRaoSpread (R : ℝ) (w : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ Z : Finset α, Z.Nonempty → ((link 𝓕 Z).card : ℝ) ≤ R ^ (w - Z.card)

/-- The probability of `P` for independent inclusion with probability `p`. -/
noncomputable def pBiased (X : Finset α) (p : ℝ) (P : Finset α → Prop) : ℝ :=
  open scoped Classical in
  ∑ R ∈ X.powerset, if P R then p ^ R.card * (1 - p) ^ (X.card - R.card) else 0

/-- A random `a`-subset contains a family member with probability greater than `1-b`. -/
def IsSatisfying (a b : ℝ) (X : Finset α) (𝓕 : Finset (Finset α)) : Prop :=
  1 - b < pBiased X a (fun R => ∃ S ∈ 𝓕, S ⊆ R)

/-- The common intersection; the empty family's kernel is empty. -/
noncomputable def kernel (𝓕 : Finset (Finset α)) : Finset α :=
  if h : 𝓕.Nonempty then 𝓕.inf' h id else ∅

/-- ALWZ's robust sunflower: a satisfying link whose empty petal is excluded. -/
def IsRobustSunflower (a b : ℝ) (X : Finset α) (𝓕 : Finset (Finset α)) : Prop :=
  kernel 𝓕 ∉ 𝓕 ∧ IsSatisfying a b (X \ kernel 𝓕) (link 𝓕 (kernel 𝓕))

/-- Explicit ALWZ-shaped robust threshold, of order `lg w * lg lg w` for fixed `a,b`. -/
noncomputable def kappaZeroPad (w : ℕ) (a b : ℝ) : ℝ :=
  (2 ^ 20 / a) * (lg (1 / a) + lg (16 / b) + lg (lg w) + 40) * (lg w + lg (16 / b))

/-- Erdős–Rado's bounded-width sunflower theorem. -/
theorem erdos_rado_bounded (w r : ℕ) {𝓕 : Finset (Finset α)}
    (hb : IsBounded w 𝓕) (hcard : (r - 1) ^ w * Nat.factorial w < 𝓕.card) :
    HasSunflower r 𝓕 := by
  exact Sunflower.erdos_rado_bounded w r hb hcard

/-- ALWZ Theorem 1.4, with an explicit constant (second-moment route). -/
theorem alwz_bounded (r w : ℕ) (hr : 3 ≤ r) (hw : 2 ≤ w)
    {𝓕 : Finset (Finset α)} (hb : IsBounded w 𝓕)
    (hcard : alwzBound alwzConstant r w ≤ (𝓕.card : ℝ)) : HasSunflower r 𝓕 := by
  exact Sunflower.hasSunflower_of_bounded
    (P := fun n => Sunflower.alwzBound alwzConstant r w ≤ (n : ℝ))
    (fun hu hc => Sunflower.alwz_uniform_of_spread_lemma
      (C₀ := (2 : ℝ) ^ 41) (by norm_num)
      (fun r w w' hr hw hw' hw'w _ hu hne hsp =>
        Sunflower.SpreadCore.spread_core_main r w w' hr hw hw' hw'w hu hne hsp)
      r w hr hw hu hc) hb hcard

/-- The same ALWZ bound through the Janson route. -/
theorem alwz_bounded_janson (r w : ℕ) (hr : 3 ≤ r) (hw : 2 ≤ w)
    {𝓕 : Finset (Finset α)} (hb : IsBounded w 𝓕)
    (hcard : alwzBound alwzConstant r w ≤ (𝓕.card : ℝ)) : HasSunflower r 𝓕 := by
  exact Sunflower.hasSunflower_of_bounded
    (P := fun n => Sunflower.alwzBound alwzConstant r w ≤ (n : ℝ))
    (fun hu hc => Sunflower.alwz_uniform_of_spread_lemma
      (C₀ := (2 : ℝ) ^ 41) (by norm_num)
      (fun r w w' hr hw hw' hw'w _ hu hne hsp =>
        Sunflower.spread_core_janson r w w' hr hw hw' hw'w hu hne hsp)
      r w hr hw hu hc) hb hcard

/-- BCW Theorem 1 via Rao's coding route, with the explicit constant `2^60`. -/
theorem rao_bcw_bounded (r w : ℕ) (hr : 2 ≤ r) (hw : 2 ≤ w)
    {𝓕 : Finset (Finset α)} (hb : IsBounded w 𝓕)
    (hcard : ((2 : ℝ) ^ 60 * r * lg w) ^ w ≤ (𝓕.card : ℝ)) : HasSunflower r 𝓕 := by
  exact Sunflower.hasSunflower_of_bounded
    (P := fun n => Sunflower.raoBound (2 ^ 60) r w ≤ (n : ℝ))
    (fun hu hc => Sunflower.rao_bcw_uniform hr hw hu hc) hb hcard

/-- ALWZ Theorem 1.9 with an explicit threshold of the stated asymptotic shape. -/
theorem exists_isRobustSunflower_pad {𝓕 : Finset (Finset α)} {X : Finset α}
    {w : ℕ} {a b : ℝ} (hw : 2 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hu : IsUniform w 𝓕) (hsub : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : kappaZeroPad w a b ^ w ≤ (𝓕.card : ℝ)) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  exact Sunflower.exists_isRobustSunflower_pad hw ha ha1 hb0 hb1 hu hsub hcard

/-- The robust-sunflower bound obtained from Rao's logarithmic spread threshold. -/
theorem exists_isRobustSunflower_rao {𝓕 : Finset (Finset α)} {X : Finset α}
    {w : ℕ} {a b : ℝ} (hw : 2 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hu : IsUniform w 𝓕) (hsub : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : ((2 : ℝ) ^ 60 / a * lg ((w : ℝ) / b)) ^ w ≤ (𝓕.card : ℝ)) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  exact Sunflower.exists_isRobustSunflower_rao hw ha ha1 hb0 hb1 hu hsub hcard

/-- ALWZ's robust-sunflower lower-bound shape, with an explicit finite construction. -/
theorem exists_no_robustSunflower (w : ℕ) (hw : 4 ≤ w) :
    ∃ 𝓕 : Finset (Finset (Fin w × Fin (Nat.log 2 w / 2))),
      IsUniform w 𝓕 ∧ ((Nat.log 2 w : ℝ) / 16) ^ (w - Nat.sqrt w) ≤ (𝓕.card : ℝ) ∧
      ∀ 𝒢 ⊆ 𝓕, ¬IsRobustSunflower (1 / 2) (1 / 2)
        (Finset.univ : Finset (Fin w × Fin (Nat.log 2 w / 2))) 𝒢 := by
  exact Sunflower.LowerBound.exists_no_robustSunflower w hw

/-- BCW Lemma 2, with explicit spread constant. -/
theorem exists_pairwiseDisjoint_of_raoSpread {w r : ℕ} {R : ℝ} {X : Finset α}
    {𝓕 : Finset (Finset α)} (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : IsUniform w 𝓕)
    (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : R ^ w ≤ (𝓕.card : ℝ))
    (hR : 2 ^ 56 * (r : ℝ) * (Real.log (2 * (w : ℝ)) + 1) ≤ R) :
    ∃ 𝒟 ⊆ 𝓕, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  exact Sunflower.exists_pairwiseDisjoint_of_raoSpread hr hw hu hsp hSX hcard hR

/-- BCW Theorem 3 with the explicit absolute constant `2^56`. -/
theorem bcw_theorem3 (w : ℕ) (R δ ε : ℝ) (X : Finset α) (𝓕 : Finset (Finset α))
    (hw : 2 ≤ w) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hR : 2 ^ 56 * δ⁻¹ * Real.log ((w : ℝ) / ε) ≤ R) (hcard : R ^ w ≤ (𝓕.card : ℝ)) :
    IsSatisfying δ ε X 𝓕 := by
  exact Sunflower.bcw_theorem3_explicit w R δ ε X 𝓕 hw hδ0 hδ1 hε0 hε1
    hu hsp hSX hR hcard

/-- BCW Lemma 4: a spread family whose containment probability is below `1-ε`. -/
theorem bcw_lemma4 {k r : ℕ} {δ ε : ℝ} (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hrb : (r : ℝ) ≤ 4⁻¹ * δ⁻¹ * Real.log ((k : ℝ) / ε)) :
    ∃ 𝓢 : Finset (Finset (Fin k × Fin r)),
      IsUniform k 𝓢 ∧ IsRaoSpread (r : ℝ) k 𝓢 ∧ 𝓢.card = r ^ k ∧
      pBiased Finset.univ δ (fun R => ∃ S ∈ 𝓢, S ⊆ R) < 1 - ε := by
  exact Sunflower.bcw_lemma4 hk hr hδ0 hδ1 hε0 hε1 hrb

end PalomarSunflower

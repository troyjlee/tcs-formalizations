/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lemma 7.3's numerical core

Three real inequalities, isolated from every hierarchy, thinning and
probability notion, so that the case assembly is pure bookkeeping.

* `eq40_absorb_bottom` — Eq. (40).  ⚠️ The decimals are **exact**.  At
  `ε₁ = ε₂/12`, `ε_B = 21ε₂`, `ε₂ = 0.0002` the two sides are `0.5685994·β`
  against `0.568599904660…·β`: a margin of `5.0466·10⁻⁷·β`.  Nothing here may
  be rounded.
* `eq41_of_mass_slack` — Eq. (41), stated as the **exact algebraic reduction**
  of the target to a slack premise, plus two floor certificates that discharge
  that premise.  ⚠️ The floor certificates carry an explicit ceiling `G` on
  `good`: whether a given floor suffices depends on it, and it is the case
  analysis — not this file — that knows the ceiling.
* `eq42_of_weighted_saving` — Eq. (42).  Pure algebra: **no** numerical bound,
  positivity or sign condition.  Adding the two premises cancels `saving` and
  `inactive` outright.
-/

namespace TSPGap

/-! ### Eq. (40) -/

/-- **Eq. (40): a bottom edge absorbs its own Corollary 5.10 loss.**

`0.5678β + 0.0014τ ≤ τ(1 − ε₁/5)(1 − ε_B)` at `τ = 0.571β`.

⚠️ Tight.  Reduced, the claim is
`0.1142·βε₁ + 0.571·βε_B ≤ 0.0024006·β + 0.1142·βε₁ε_B`, and the left side is at
most `12.00051667·βε₂ ≤ 0.00240010·β`.  The slack is about `5·10⁻⁷·β`, so
`0.571`, `0.5678` and `0.0014` must be preserved exactly. -/
theorem eq40_absorb_bottom {β τ ε₁ ε₂ εB : ℝ} (hβ : 0 ≤ β) (hτ : τ = 0.571 * β)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hεB0 : 0 ≤ εB) (hεB : εB ≤ 21 * ε₂) :
    0.5678 * β + 0.0014 * τ ≤ τ * (1 - ε₁ / 5) * (1 - εB) := by
  subst hτ
  nlinarith [mul_nonneg (mul_nonneg hβ hε₁0) hεB0,
    mul_nonneg hβ (sub_nonneg.mpr hε₂),
    mul_nonneg hβ (sub_nonneg.mpr hε₁),
    mul_nonneg hβ (sub_nonneg.mpr hεB)]

/-- Non-vacuity, at the extreme parameters: `0.5685994 ≤ 0.568599904660…`, a
margin of `5.0466·10⁻⁷`.  If any of the three decimals were rounded, this would
fail. -/
example : (0.5678 : ℝ) * 1 + 0.0014 * (0.571 * 1)
    ≤ 0.571 * 1 * (1 - (0.0002 / 12) / 5) * (1 - 21 * 0.0002) := by norm_num

/-! ### Eq. (41) -/

/-- **Eq. (41), the exact reduction.**  The target
`good ≤ cF(good + inactive) + 0.0014·bottom` is *equivalent* to the slack
premise, so nothing is lost here; the content is in discharging it. -/
theorem eq41_of_mass_slack {good inactive bottom c F : ℝ}
    (h : good * (1 - c * F) ≤ c * F * inactive + 0.0014 * bottom) :
    good ≤ c * F * (good + inactive) + 0.0014 * bottom := by
  nlinarith [h]

/-- **The slack premise from a floor on the bottom mass.**  This is the shape of
the first certificate (`F = 1`, `bottom ≥ 0.003`) and of the third
(`F = 1 − 21ε₂`, `bottom ≥ 4q/5`).

⚠️ `hnum` is where the case analysis pays: whether a floor suffices depends on
the ceiling `G` on `good`, which this file cannot know.  For the third
certificate `bottom ≥ 4q/5` out of a total `q` forces `G = q/5`, and
`(q/5)(1 − cF) ≤ 0.0014·(4q/5)` then holds with room. -/
theorem eq41_slack_of_bottom_floor {good inactive bottom c F G bfloor : ℝ}
    (hgoodG : good ≤ G) (hcF : c * F ≤ 1) (hinactive : 0 ≤ c * F * inactive)
    (hfloor : bfloor ≤ bottom) (hnum : G * (1 - c * F) ≤ 0.0014 * bfloor) :
    good * (1 - c * F) ≤ c * F * inactive + 0.0014 * bottom := by
  nlinarith [mul_le_mul_of_nonneg_right hgoodG (sub_nonneg.mpr hcF)]

/-- **The slack premise from a floor on the inactive mass.**  This is the shape
of the second certificate (`F ≥ 1 − 21ε₂`, `inactive ≥ 0.006`).  ⚠️ It admits
`F = 1`; restricting it to the fractional `F = 1 − 21ε₂` would omit a consumer
case. -/
theorem eq41_slack_of_inactive_floor {good inactive bottom c F G ifloor : ℝ}
    (hgoodG : good ≤ G) (hcF : c * F ≤ 1) (hcF0 : 0 ≤ c * F)
    (hfloor : ifloor ≤ inactive) (hbottom : 0 ≤ bottom)
    (hnum : G * (1 - c * F) ≤ c * F * ifloor) :
    good * (1 - c * F) ≤ c * F * inactive + 0.0014 * bottom := by
  nlinarith [mul_le_mul_of_nonneg_right hgoodG (sub_nonneg.mpr hcF),
    mul_le_mul_of_nonneg_left hfloor hcF0]

/-! ### The three numeric certificates, at the ceiling `G = 1.001` -/

/-- 🔑 The ceiling is `x(δ↑(u)) ≤ 1 + ε_η` — **KKO Lemma 2.7**, in the repository
as `upSum_le_one_add` — not `2 + ε_η`.  ⚠️ The larger ceiling genuinely **fails**
both floor certificates, so it must not be used: at `2.001` the bottom floor
would need `2.001·ε₂/60 ≤ 4.2·10⁻⁶`, i.e. `6.67·10⁻⁶ ≤ 4.2·10⁻⁶`. -/
theorem eq41_ceiling {εη q : ℝ} (hεη : εη ≤ 0.001) (hq : q ≤ 1 + εη) : q ≤ 1.001 := by
  linarith

/-- **First certificate**: `F = 1` and `bottom ≥ 0.003`.  At `c = 1 − ε₂/60` with
`ε₂ ≤ 0.0002`, `1.001·(1 − c) ≤ 1.001/300000 = 3.337·10⁻⁶ ≤ 4.2·10⁻⁶`. -/
theorem eq41_bottom_num {c : ℝ} (hc : 1 - (1 : ℝ) / 300000 ≤ c) :
    (1.001 : ℝ) * (1 - c * 1) ≤ 0.0014 * 0.003 := by
  norm_num
  linarith

/-- The lower anchor `m₀ = (1 − 1/300000)(1 − 21/5000)` for `c·F`: the value at
`ε₂ = 0.0002` in both factors. -/
theorem eq41_anchor : ((1493695021 : ℝ) / 1500000000)
    = (1 - 1 / 300000) * (1 - 21 / 5000) := by
  norm_num

/-- **Second certificate**: `F ≥ 1 − 21ε₂` and `inactive ≥ 0.006`.  Linear in
`cF`: the claim is `1.001 ≤ 1.007·cF`, and `m₀ ≥ 1.001/1.007`.  ⚠️ `F = 1` is
admitted — the anchor only bounds `cF` from below. -/
theorem eq41_inactive_num {cF : ℝ} (hlo : (1493695021 : ℝ) / 1500000000 ≤ cF) :
    (1.001 : ℝ) * (1 - cF) ≤ cF * 0.006 := by
  norm_num at hlo ⊢
  linarith

/-- **Third certificate**: `F = 1 − 21ε₂` and `bottom ≥ 4q/5`.  Self-certifying:
a total of `q` with `bottom ≥ 4q/5` forces the ceiling `G = q/5`, and then
`(q/5)(1 − cF) ≤ 0.00084067·q ≤ 0.00112·q`. -/
theorem eq41_bottom_frac_num {q cF : ℝ} (hq : 0 ≤ q)
    (hlo : (1493695021 : ℝ) / 1500000000 ≤ cF) :
    q / 5 * (1 - cF) ≤ 0.0014 * (4 * q / 5) := by
  nlinarith [hq, hlo]

/-! ### Eq. (42) -/

/-- **Eq. (42): a saving on a good subset converts to the target.**

From `paid + saving ≤ good` and `(1 − cF)(good + inactive) ≤ inactive + saving`,
conclude `paid ≤ cF(good + inactive)`.

⚠️ Pure algebra.  No numerical bound, no positivity, no sign condition on any of
`paid`, `saving`, `good`, `inactive`, `c`, `F`: the second premise rearranges to
`good − cF(good + inactive) ≤ saving`, and adding the first cancels `saving` and
`inactive` outright. -/
theorem eq42_of_weighted_saving {paid saving good inactive c F : ℝ}
    (hpaid : paid + saving ≤ good)
    (hsav : (1 - c * F) * (good + inactive) ≤ inactive + saving) :
    paid ≤ c * F * (good + inactive) := by
  nlinarith [hpaid, hsav]

/-! ### Case 2, step 5: window saving, Eq. (42), and the assembly -/

/-- **The window and its complement.**  The window is charged at the Claim 7.5
rate `c`, the complement trivially at `1`; the net saving is `(1 − c)·winMass`.
⚠️ Scaled by `τ·p` throughout, never normalized. -/
theorem good_bound_of_window {Rwin Rcomp goodMass winMass compMass τ p c : ℝ}
    (hwin : Rwin ≤ τ * p * c * winMass) (hcomp : Rcomp ≤ τ * p * compMass)
    (hmass : goodMass = winMass + compMass) :
    Rwin + Rcomp ≤ τ * p * (goodMass - (1 - c) * winMass) := by
  subst hmass
  nlinarith [hwin, hcomp]

/-- **The window saving.**  A window of mass at least `0.24` charged at rate
`c ≤ 1 − 49ε₁/50` saves `0.2352·ε₁`, which already covers the `0.2002·ε₁` that
Eq. (42) needs.
🔑 `0.24` is Case 1b's window, the *tight* consumer; Case 2's window carries
`4/5` and saves `0.784·ε₁`, with far more room. -/
theorem case2_saving_ge {winMass c ε₁ : ℝ} (hwin : 0.24 ≤ winMass)
    (hc : c ≤ 1 - 49 * ε₁ / 50) (hε₁ : 0 ≤ ε₁) :
    0.2002 * ε₁ ≤ (1 - c) * winMass := by
  nlinarith

/-- **Case 2's Eq. (42) step.**  A saving of at least `0.2002·ε₁` covers the
target factor `1 − ε₁/5`.
🔑 `0.2002 = 1.001/5`: the ceiling on `good + inactive` enters *here*.  ⚠️ With
the `2 + ε_η` ceiling the requirement would be `0.4002·ε₁` — still under the
`0.784·ε₁` available, but the correct ceiling is `1 + ε_η` (KKO Lemma 2.7) and
Eq. (41)'s floors genuinely need it. -/
theorem case2_eq42 {paid saving good inactive ε₁ : ℝ}
    (hgi : good + inactive ≤ 1.001) (hinactive : 0 ≤ inactive) (hε₁ : 0 ≤ ε₁)
    (hsaving : 0.2002 * ε₁ ≤ saving) (hpaid : paid + saving ≤ good) :
    paid ≤ (1 - ε₁ / 5) * (good + inactive) := by
  have hslack : (1 - (1 - ε₁ / 5) * 1) * (good + inactive) ≤ inactive + saving := by
    nlinarith [mul_nonneg hε₁ (sub_nonneg.mpr hgi)]
  refine le_trans (eq42_of_weighted_saving hpaid hslack) (le_of_eq ?_)
  ring

/-- **Case 2's assembly.**  Inactive contributes nothing, the good part is within
the target factor by Eq. (42), and Eq. (40) absorbs the bottom part — with
`0.0014·τ` to spare, which is exactly the slack Eq. (41) uses. -/
theorem case2_assemble {Rtotal Rgood Rbottom good inactive bottom saving
    q τ p β ε₁ εB : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * (good - saving))
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (heq40 : 0.5678 * β + 0.0014 * τ ≤ τ * (1 - ε₁ / 5) * (1 - εB))
    (heq42 : good - saving ≤ (1 - ε₁ / 5) * (good + inactive))
    (hq : q = good + inactive + bottom)
    (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hεB : 0 ≤ εB) (hbot : 0 ≤ bottom) (hε₁ : ε₁ ≤ 5) :
    Rtotal ≤ τ * p * (1 - ε₁ / 5) * q := by
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hfac : 0 ≤ 1 - ε₁ / 5 := by linarith
  have hprod : 0 ≤ τ * (1 - ε₁ / 5) * εB := mul_nonneg (mul_nonneg hτ hfac) hεB
  -- the good half
  have hg : Rgood ≤ τ * p * ((1 - ε₁ / 5) * (good + inactive)) :=
    le_trans hRgood (mul_le_mul_of_nonneg_left heq42 hτp)
  -- the bottom half, through Eq. (40), keeping `0.0014·τ` in reserve
  have hb40 : 0.5678 * β ≤ τ * (1 - ε₁ / 5) - 0.0014 * τ := by nlinarith
  have hpb : 0 ≤ p * bottom := mul_nonneg hp hbot
  have hb : Rbottom ≤ τ * p * ((1 - ε₁ / 5) * bottom) := by
    have hmul := mul_le_mul_of_nonneg_right hb40 hpb
    nlinarith [mul_nonneg (mul_nonneg hτ hp) hbot]
  rw [hsplit, hq]
  nlinarith [hg, hb]

/-! ### Step 6: `ε_B` is pinned, not free -/

/-- 🔑 **`ε_B` must be `21ε₂` exactly.**  The matching lemma (`lemma_6_2`, via
`Hierarchy.hall_inequality`) requires `21ε₂ ≤ ε_B`, while Eq. (40) requires
`ε_B ≤ 21ε₂`.  The two point in **opposite** directions, so the only consistent
choice is equality: `ε_B` is *not* a free parameter of Lemma 7.3, and a
specialization that leaves it generic cannot satisfy both sides. -/
theorem epsB_eq_of_both {ε₂ εB : ℝ} (hmatching : 21 * ε₂ ≤ εB) (heq40 : εB ≤ 21 * ε₂) :
    εB = 21 * ε₂ :=
  le_antisymm heq40 hmatching

/-- At `ε_B = 21ε₂` the matching lemma's upper side condition holds:
`21 · 0.0002 = 0.0042 ≤ 1/100`. -/
theorem epsB_le_one_hundredth {ε₂ : ℝ} (hε₂ : ε₂ ≤ 0.0002) : 21 * ε₂ ≤ 1 / 100 := by
  linarith

/-- **Eq. (40) at the pinned `ε_B = 21ε₂`.**  Both of the generic version's
`ε_B` hypotheses are discharged, the upper one by `le_rfl`.  ⚠️ No separate
`0 ≤ ε₂` is needed: `0 ≤ ε₁ ≤ ε₂/12` already supplies it. -/
theorem eq40_absorb_bottom_specialized {β τ ε₁ ε₂ : ℝ} (hβ : 0 ≤ β) (hτ : τ = 0.571 * β)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) :
    0.5678 * β + 0.0014 * τ ≤ τ * (1 - ε₁ / 5) * (1 - 21 * ε₂) :=
  eq40_absorb_bottom hβ hτ hε₁0 hε₁ hε₂ (by linarith) le_rfl

/-- **Case 2's assembly at the pinned `ε_B`.**  Eq. (40)'s hypothesis and the
sign conditions are all discharged from `β`, `ε₁` and `ε₂`, so the caller
supplies only the three reduction bounds, Eq. (42) and the mass identity. -/
theorem case2_assemble_specialized {Rtotal Rgood Rbottom good inactive bottom saving
    q τ p β ε₁ ε₂ : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * (good - saving))
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (heq42 : good - saving ≤ (1 - ε₁ / 5) * (good + inactive))
    (hq : q = good + inactive + bottom)
    (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) (hp : 0 ≤ p) (hbot : 0 ≤ bottom) :
    Rtotal ≤ τ * p * (1 - ε₁ / 5) * q := by
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hε₁5 : ε₁ ≤ 5 := by linarith
  exact case2_assemble hsplit hRgood hRbottom
    (eq40_absorb_bottom_specialized hβ hτeq hε₁0 hε₁ hε₂) heq42 hq hτ hp
    (by linarith) hbot hε₁5

/-! ### The Eq. (41) branch's assembler -/

/-- **Case 2's assembly on the Eq. (41) branch.**

⚠️ `case2_assemble` cannot serve here: Eq. (41)'s conclusion carries a
`+ 0.0014·bottom` term, and there is no `good − saving` to feed it.

🔑 The `0.0014·τ·p·bottom` that term contributes is **exactly** what Eq. (40)
leaves in reserve, so the two cancel identically.  That is why Eq. (40)'s
`0.0014` and Eq. (41)'s `0.0014` are the same constant and neither may be
rounded independently. -/
theorem case2_assemble_eq41_specialized {Rtotal Rgood Rbottom good inactive bottom
    q τ p β ε₁ ε₂ : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * good)
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (heq41 : good ≤ (1 - ε₁ / 5) * (good + inactive) + 0.0014 * bottom)
    (hq : q = good + inactive + bottom)
    (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) (hp : 0 ≤ p) (hbot : 0 ≤ bottom) :
    Rtotal ≤ τ * p * (1 - ε₁ / 5) * q := by
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hfac : 0 ≤ 1 - ε₁ / 5 := by linarith
  have h40 := eq40_absorb_bottom_specialized hβ hτeq hε₁0 hε₁ hε₂
  have hprod : 0 ≤ τ * (1 - ε₁ / 5) * (21 * ε₂) :=
    mul_nonneg (mul_nonneg hτ hfac) (by linarith)
  have hg : Rgood ≤ τ * p * ((1 - ε₁ / 5) * (good + inactive) + 0.0014 * bottom) :=
    le_trans hRgood (mul_le_mul_of_nonneg_left heq41 hτp)
  have hb40 : 0.5678 * β ≤ τ * (1 - ε₁ / 5) - 0.0014 * τ := by nlinarith
  have hpb : 0 ≤ p * bottom := mul_nonneg hp hbot
  have hb : Rbottom ≤ τ * p * ((1 - ε₁ / 5) * bottom) - 0.0014 * (τ * p * bottom) := by
    have hmul := mul_le_mul_of_nonneg_right hb40 hpb
    nlinarith
  rw [hsplit, hq]
  nlinarith [hg, hb]

/-- **Case 2's two branches, unified.**  Either floor is large and Eq. (41)
closes the branch, or both are small and the window saving closes it through
Eq. (42).  Both land on the same target `τ·p·(1 − ε₁/5)·q`. -/
theorem case2_target_of_branches {Rtotal Rgood Rbottom good inactive bottom saving
    q τ p β ε₁ ε₂ : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (hq : q = good + inactive + bottom)
    (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) (hp : 0 ≤ p) (hbot : 0 ≤ bottom)
    (hbranch :
      (Rgood ≤ τ * p * good
          ∧ good ≤ (1 - ε₁ / 5) * (good + inactive) + 0.0014 * bottom)
        ∨ (Rgood ≤ τ * p * (good - saving)
          ∧ good - saving ≤ (1 - ε₁ / 5) * (good + inactive))) :
    Rtotal ≤ τ * p * (1 - ε₁ / 5) * q := by
  rcases hbranch with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact case2_assemble_eq41_specialized hsplit h1 hRbottom h2 hq hβ hτeq hε₁0 hε₁
      hε₂ hp hbot
  · exact case2_assemble_specialized hsplit h1 hRbottom h2 hq hβ hτeq hε₁0 hε₁ hε₂ hp hbot

/-- `1 − ε₁/5 = 1 − ε₂/60` at `ε₁ = ε₂/12`.

⚠️ **For the concrete specialization only.**  `case2_eq41_of_large_part` is
generic in `c`; it does *not* itself produce `1 − ε₂/60`.  The generic
structural theorem assumes only `ε₁ ≤ ε₂/12`, so it must instantiate that lemma
directly at `c := 1 − ε₁/5` and discharge the lower bound with
`case2_eq41_factor_lower` — never with this equality. -/
theorem case2_eq41_factor {ε₁ ε₂ : ℝ} (hε₁eq : ε₁ = ε₂ / 12) :
    1 - ε₁ / 5 = 1 - ε₂ / 60 := by
  rw [hε₁eq]; ring

/-- `case2_eq41_of_large_part`'s lower bound at `c := 1 − ε₁/5`, from the generic
`ε₁ ≤ ε₂/12` alone.  ⚠️ It reduces to `ε₁ ≤ 1/60000`, which `ε₂ ≤ 0.0002` meets
with **no slack** — equality at the cap. -/
theorem case2_eq41_factor_lower {ε₁ ε₂ : ℝ} (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) :
    1 - (1 : ℝ) / 300000 ≤ 1 - ε₁ / 5 := by
  linarith

/-! ### Step 7: the small-floor branch's closer -/

/-- **The window closer.**  Every window branch — Case 2's root and parent
windows, and Case 1b's `tail u p(S_j) ∖ tail u p(S_ℓ)` — arrives at exactly this
shape: the good reduction is charged at the Claim 7.5 rate on a window of mass at
least `0.24`, netting the saving `(1 − c)·winMass`.

🔑 At the `0.24` this closer assumes, the saving is `(1 − c)·winMass ≥ 0.2352·ε₁`
(`case2_saving_ge`), against Eq. (42)'s `0.2002·ε₁ = 1.001·ε₁/5`.  Case 2's
windows carry `4/5` and so save `0.784·ε₁`, with far more room; Case 1b's `0.24`
is the tight one.  The branch then lands on the **right** disjunct of
`case2_target_of_branches`. -/
theorem case2_close_of_window {Rtotal Rgood Rbottom good inactive bottom winMass
    q τ p β ε₁ ε₂ c : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * (good - (1 - c) * winMass))
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (hq : q = good + inactive + bottom)
    (hgi : good + inactive ≤ 1.001) (hin0 : 0 ≤ inactive)
    (hwin : 0.24 ≤ winMass) (hc : c ≤ 1 - 49 * ε₁ / 50)
    (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) (hp : 0 ≤ p) (hbot0 : 0 ≤ bottom) :
    Rtotal ≤ τ * p * (1 - ε₁ / 5) * q := by
  have hsav : 0.2002 * ε₁ ≤ (1 - c) * winMass := case2_saving_ge hwin hc hε₁0
  have h42 : good - (1 - c) * winMass ≤ (1 - ε₁ / 5) * (good + inactive) :=
    case2_eq42 hgi hin0 hε₁0 hsav (by linarith)
  exact case2_target_of_branches hsplit hRbottom hq hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
    (Or.inr ⟨hRgood, h42⟩)

/-! ### The assembly, generic in the target factor `cF` -/

/-- **The assembly, in terms of the single factor `cF`.**  Case 2 runs at
`F = 1`, Case 3 at `F = 1 − ε_B`; nothing else in the assembly depends on which,
so both are this one statement with `cF := c·F`.
🔑 Eq. (40) is consumed in the form `0.5678β + 0.0014τ ≤ τ·cF`: the bottom part
is paid at the target rate with `0.0014·τ` left in reserve. -/
theorem assemble_of_eq40 {Rtotal Rgood Rbottom good inactive bottom saving
    q τ p β cF : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * (good - saving))
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (heq40 : 0.5678 * β + 0.0014 * τ ≤ τ * cF)
    (heq42 : good - saving ≤ cF * (good + inactive))
    (hq : q = good + inactive + bottom)
    (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hbot : 0 ≤ bottom) :
    Rtotal ≤ τ * p * cF * q := by
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hg : Rgood ≤ τ * p * (cF * (good + inactive)) :=
    le_trans hRgood (mul_le_mul_of_nonneg_left heq42 hτp)
  have hb40 : 0.5678 * β ≤ τ * cF - 0.0014 * τ := by linarith
  have hpb : 0 ≤ p * bottom := mul_nonneg hp hbot
  have hb : Rbottom ≤ τ * p * (cF * bottom) := by
    have hmul := mul_le_mul_of_nonneg_right hb40 hpb
    nlinarith [mul_nonneg (mul_nonneg hτ hp) hbot]
  rw [hsplit, hq]
  nlinarith [hg, hb]

/-- **The Eq. (41) assembly, generic in `cF`.**  The `0.0014·bottom` that
Eq. (41) carries is exactly Eq. (40)'s reserve, so the two cancel identically —
at `F = 1 − ε_B` no less than at `F = 1`. -/
theorem assemble_eq41_of_eq40 {Rtotal Rgood Rbottom good inactive bottom
    q τ p β cF : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * good)
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (heq40 : 0.5678 * β + 0.0014 * τ ≤ τ * cF)
    (heq41 : good ≤ cF * (good + inactive) + 0.0014 * bottom)
    (hq : q = good + inactive + bottom)
    (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hbot : 0 ≤ bottom) :
    Rtotal ≤ τ * p * cF * q := by
  have hτp : 0 ≤ τ * p := mul_nonneg hτ hp
  have hg : Rgood ≤ τ * p * (cF * (good + inactive) + 0.0014 * bottom) :=
    le_trans hRgood (mul_le_mul_of_nonneg_left heq41 hτp)
  have hb40 : 0.5678 * β ≤ τ * cF - 0.0014 * τ := by linarith
  have hpb : 0 ≤ p * bottom := mul_nonneg hp hbot
  have hb : Rbottom ≤ τ * p * (cF * bottom) - 0.0014 * (τ * p * bottom) := by
    have hmul := mul_le_mul_of_nonneg_right hb40 hpb
    nlinarith
  rw [hsplit, hq]
  nlinarith [hg, hb]

/-! ### Case 3: the fractional window at `ε_F = 1/10` -/

/-- **Case 3's target factor is bounded below by the Eq. (41) anchor.**  Both
factors are decreasing in their parameter, so the anchor
`(1 − 1/300000)(1 − 21/5000)` — the value at `ε₂ = 0.0002` in both — is a lower
bound throughout the admissible range. -/
theorem case3_cF_lower {ε₁ ε₂ : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) :
    (1493695021 : ℝ) / 1500000000 ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) := by
  have hε₂0 : 0 ≤ ε₂ := by linarith
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 300000 - ε₁ / 5 by linarith)
    (show (0 : ℝ) ≤ 1 - 21 * ε₂ by linarith), mul_nonneg hε₁0 hε₂0]

/-- **Case 3's rate.**  At `ε_F = 1/10` the nested Claim 7.5 gives
`1 − ε_F + max(2ε_η, ε_F²) + ε_η/2 = 0.91 + ε_η/2`; the `ε_η/2` is what `p(u)`
failing to be a tree costs. -/
theorem case3_rate_le {εη : ℝ} (hεηcap : εη ≤ 1e-10) :
    1 - (1 : ℝ) / 10 + max (2 * εη) (((1 : ℝ) / 10) ^ 2) + εη / 2 ≤ 0.911 := by
  have h : max (2 * εη) (((1 : ℝ) / 10) ^ 2) ≤ 0.01 :=
    max_le (by linarith) (by norm_num)
  linarith

/-- **Case 3's Eq. (42).**  🔑 The ceiling here is `good + inactive ≤ q`, *not*
`1.001`: Case 3's saving is proportional to `q`, and the deficit `1 − cF` is
charged against `q` as well, so the two scale together.

At `q ≥ 1/10` the saving `0.089·(q/5 − 0.006) = 0.0178q − 0.000534` beats the
deficit `(ε₁/5 + 21ε₂)·q ≤ 0.00421q` from `q ≥ 0.0393` on — the paper's
`(ε_F − 2ε_F²)/5 ≥ ε_{1/1}/5 + ε_B`, with the `0.006` inactive floor subtracted
from the good set, which the printed proof omits. -/
theorem case3_eq42 {paid saving good inactive bottom q ε₁ ε₂ c₃ : ℝ}
    (hq : q = good + inactive + bottom) (hbot0 : 0 ≤ bottom) (hin0 : 0 ≤ inactive)
    (hgood0 : 0 ≤ good) (hqlo : 1 / 10 ≤ q) (hgood : q / 5 - 0.006 ≤ good)
    (hc₃ : c₃ ≤ 0.911) (hsaving : (1 - c₃) * good ≤ saving)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hpaid : paid + saving ≤ good) :
    paid ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) * (good + inactive) := by
  refine eq42_of_weighted_saving hpaid ?_
  have hε₂0 : 0 ≤ ε₂ := by linarith
  have hgi0 : 0 ≤ good + inactive := by linarith
  have hgiq : good + inactive ≤ q := by linarith
  have hcF : 1 - (1 - ε₁ / 5) * (1 - 21 * ε₂) ≤ 0.00421 := by
    nlinarith [mul_nonneg hε₁0 hε₂0]
  have h1 : (1 - (1 - ε₁ / 5) * (1 - 21 * ε₂)) * (good + inactive) ≤ 0.00421 * q := by
    nlinarith [mul_le_mul_of_nonneg_right hcF hgi0]
  have hsav : 0.089 * good ≤ saving := by
    nlinarith [mul_le_mul_of_nonneg_right (show (0.089 : ℝ) ≤ 1 - c₃ by linarith) hgood0]
  linarith

/-- **Case 3's Eq. (41) from the bottom floor `4q/5`.**  🔑 The floor supplies
its own ceiling: a total of `q` with `bottom ≥ 4q/5` forces `good ≤ q/5`, and the
third certificate is exactly calibrated to that pair. -/
theorem case3_eq41_of_bottom_floor {good inactive bottom q ε₁ ε₂ : ℝ}
    (hq : q = good + inactive + bottom) (hin0 : 0 ≤ inactive) (hq0 : 0 ≤ q)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hfloor : 4 * q / 5 ≤ bottom) :
    good ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) * (good + inactive) + 0.0014 * bottom := by
  have hε₂0 : 0 ≤ ε₂ := by linarith
  have hcF0 : (0 : ℝ) ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) :=
    mul_nonneg (by linarith) (by linarith)
  have hcF1 : (1 - ε₁ / 5) * (1 - 21 * ε₂) ≤ 1 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 21 * ε₂ by linarith)
      (show (0 : ℝ) ≤ 1 - ε₁ / 5 by linarith)]
  refine eq41_of_mass_slack (c := 1 - ε₁ / 5) (F := 1 - 21 * ε₂)
    (eq41_slack_of_bottom_floor (G := q / 5) (bfloor := 4 * q / 5)
      (by linarith) hcF1 (mul_nonneg hcF0 hin0) hfloor
      (eq41_bottom_frac_num hq0 (case3_cF_lower hε₁0 hε₁ hε₂)))

/-- **Case 3's Eq. (41) from the inactive floor `0.006`**, at the ceiling
`1.001` — KKO Lemma 2.7, exactly as in Case 2. -/
theorem case3_eq41_of_inactive_floor {good inactive bottom ε₁ ε₂ : ℝ}
    (hceil : good + inactive ≤ 1.001) (hbot0 : 0 ≤ bottom)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hfloor : 0.006 ≤ inactive) :
    good ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) * (good + inactive) + 0.0014 * bottom := by
  have hε₂0 : 0 ≤ ε₂ := by linarith
  have hcF0 : (0 : ℝ) ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) :=
    mul_nonneg (by linarith) (by linarith)
  have hcF1 : (1 - ε₁ / 5) * (1 - 21 * ε₂) ≤ 1 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 21 * ε₂ by linarith)
      (show (0 : ℝ) ≤ 1 - ε₁ / 5 by linarith)]
  refine eq41_of_mass_slack (c := 1 - ε₁ / 5) (F := 1 - 21 * ε₂)
    (eq41_slack_of_inactive_floor (G := 1.001) (ifloor := 0.006)
      (by linarith) hcF1 hcF0 hfloor hbot0
      (eq41_inactive_num (case3_cF_lower hε₁0 hε₁ hε₂)))

/-! ### Case 3's two closers -/

/-- **Case 3's closer on the window branch.**  The good part is charged at the
nested rate `c₃` on *all* of it — Case 3 has no window selection — and Eq. (42)
converts the saving `(1 − c₃)·good` into the target factor `cF = (1 − ε₁/5)(1 − ε_B)`. -/
theorem case3_close_of_good {Rtotal Rgood Rbottom good inactive bottom q τ p β ε₁ ε₂ c₃ : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * c₃ * good)
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (hq : q = good + inactive + bottom)
    (hbot0 : 0 ≤ bottom) (hin0 : 0 ≤ inactive) (hgood0 : 0 ≤ good)
    (hqlo : 1 / 10 ≤ q) (hgood : q / 5 - 0.006 ≤ good) (hc₃ : c₃ ≤ 0.911)
    (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) (hp : 0 ≤ p) :
    Rtotal ≤ τ * p * ((1 - ε₁ / 5) * (1 - 21 * ε₂)) * q := by
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have h40 : 0.5678 * β + 0.0014 * τ ≤ τ * ((1 - ε₁ / 5) * (1 - 21 * ε₂)) := by
    have h := eq40_absorb_bottom_specialized hβ hτeq hε₁0 hε₁ hε₂
    rw [mul_assoc] at h
    exact h
  refine assemble_of_eq40 (saving := (1 - c₃) * good) hsplit
    (le_trans hRgood (le_of_eq (by ring))) hRbottom h40 ?_ hq hτ hp hbot0
  exact case3_eq42 hq hbot0 hin0 hgood0 hqlo hgood hc₃ le_rfl hε₁0 hε₁ hε₂ (by linarith)

/-- **Case 3's closer on either Eq. (41) branch.**  The good part takes only its
trivial `τ·p` bound; Eq. (40)'s `0.0014·τ` reserve absorbs Eq. (41)'s term at
`F = 1 − ε_B` exactly as it does at `F = 1`. -/
theorem case3_close_of_eq41 {Rtotal Rgood Rbottom good inactive bottom q τ p β ε₁ ε₂ : ℝ}
    (hsplit : Rtotal = Rgood + Rbottom)
    (hRgood : Rgood ≤ τ * p * good)
    (hRbottom : Rbottom ≤ 0.5678 * β * p * bottom)
    (hq : q = good + inactive + bottom)
    (heq41 : good ≤ (1 - ε₁ / 5) * (1 - 21 * ε₂) * (good + inactive) + 0.0014 * bottom)
    (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂ : ε₂ ≤ 0.0002) (hp : 0 ≤ p) (hbot0 : 0 ≤ bottom) :
    Rtotal ≤ τ * p * ((1 - ε₁ / 5) * (1 - 21 * ε₂)) * q := by
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have h40 : 0.5678 * β + 0.0014 * τ ≤ τ * ((1 - ε₁ / 5) * (1 - 21 * ε₂)) := by
    have h := eq40_absorb_bottom_specialized hβ hτeq hε₁0 hε₁ hε₂
    rw [mul_assoc] at h
    exact h
  exact assemble_eq41_of_eq40 hsplit hRgood hRbottom h40 heq41 hq hτ hp hbot0

end TSPGap

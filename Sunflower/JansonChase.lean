/-
# The constant chase for the Janson route

`JansonIterate.iterate_le_janson` runs the width-schedule iteration on the Janson bottom, with
the bottom κ-conditions `hJ1`–`hJ4`. The remaining work was to choose `L, s, m_bot, p, κ`
making them hold at the `spread_lemma` instantiation. This file does that chase, and its first
result is that **the chase cannot close in that form** — not for want of constants.

## Superseded, and why it is kept

**Everything in this file analyses one specific choice: applying Janson to the *support*, one
event per distinct member.** That choice is what forces the count-vs-mass step, and this file
follows it to the end — the budget is infeasible, support-spreadness is false, and the repair
costs `log₂` of the largest multiplicity.

`Sunflower.JansonMass` makes the other choice, which is ALWZ's: one event per *copy*. There the
count-vs-mass step never arises, the bottom needs only `WLinkBounded`, and the spread lemma
comes out unconditionally (`JansonAssemble.spread_core_janson`). So the results below are no
longer on the path to the theorem. They are kept because they are what the wrong indexing costs,
and the counterexample (`suppSpread_not_of_wLinkBounded`) is the reason one cannot simply repair
it: support-spreadness is not a property these systems have.

## The obstruction (`janson_mass_budget_infeasible`)

At the instantiation both the mass floor and the spread bound are the family size,
`A₀ = M = |𝓖|`, so the budget `hJ3` reads

  `log(2/εbot) ≤ |𝓖|·κ²·p / (64·|𝓖|²·L²) = κ²·p / (64·|𝓖|·L²)`.

Spreadness forces `|𝓖| ≥ κ^{w'}` (`pow_le_card_of_isSpread`), so for `w' ≥ 2` the right-hand
side is at most `1/1024`, while the left-hand side exceeds `1` for any `εbot ≤ 1/2`. No choice
of `p ≤ 1`, `L ≥ 4` or `κ ≥ 1` repairs this: the failure is by a factor `|𝓖|/κ² ≥ κ^{w'-2}`.

## The diagnosis for the support-indexed formulation

The `|𝓖|` in the denominator is not an artefact of the budget's shape. It enters at
`card_supp_superset_le`, which bounds a *count* of support members by a *mass*:

  `#{T ∈ supp : U ⊆ T} ≤ wLink X σ U ≤ M / κ^{|U|}`.

For an honest family (`M = |supp|`) that is sharp; for a multiset it is off by the
multiplicity. This support-indexed formulation sees only the support — its covering event does
not know multiplicities — so the estimate it needs is *support*-spreadness,
`#{T ∈ supp : U ⊆ T}·κ^{|U|} ≤ |supp|`,
i.e. `IsSpread κ (supp X σ)`. The iteration's `reduce` genuinely creates multiplicities (many
`S` share a reduced image), and its invariant is mass-based: `WLinkBounded X σ M κ` with a
*fixed* `M` and `wTotal ≥ A`. The only lower bound on `|supp|` available from that invariant is
`card_supp_ge` (`|supp| ≥ A·κ^v/M`), which is exactly the lossy step above.

This is the price of the development's deliberate departure from ALWZ: they carry set families
and their cardinalities, which is *support*-spreadness maintained through the rounds; the
formalization carries weighted multisets and masses, which is what makes the second moment
(Chebyshev needs only mass) work without ever lower-bounding a deduplicated family.

## The repair, and the chase for it

`failCount_le_of_janson_isSpread` is the bottom step under support-spreadness. Its exponent is
`κ·p/(8v²)` — no `M/|supp|` ratio anywhere — and `iterate_le_janson_supp` runs the iteration on
it, taking support-spreadness of the residual systems as an explicit hypothesis (`hinv`).

`janson_supp_conditions` is then the constant chase for the repaired conditions, at the actual
`SpreadAssemble` parameters: `κ = 2^41·r³·lg w·lg lg w`, `p = 1/(8r)`, `εbot = 1/(4r)`,
`m = n/r`, `m_bot = m - m/2`, and any `L` with `4 ≤ L ≤ 88 + 4·lg r + 3·lg lg w` (the bound
`SpreadAssemble` proves for its `L`). All three conditions hold with room to spare — the
`log(1/εbot)` budget costs `r·log r` where the second moment costs `r²`.

## `hinv` is false, and what replaces it

Support-spreadness of the iteration's systems cannot be proved: it is **false**
(`suppSpread_not_of_wLinkBounded`). Mass-spreadness constrains *weights*, and a multiset can
park an arbitrarily large *count* in a star — `t` pairs `{0,i}` of weight `1` — while a little
heavy ballast spread over `≈ 2κ²` singletons pays for the star's link. The support is then only
`(1 + k/t)`-spread as a family, with `t` free.

What does survive is the device this development already uses twice, applied to *weight*: split
the support into dyadic weight classes `𝓗_j = {T ∈ supp : 2^j ≤ σ T < 2^{j+1}}`. Inside a class
count and mass agree up to a factor `2`, so mass-spreadness *is* count-spreadness there, and the
heaviest class carries a `1/(J+1)` fraction of the mass when `2^J` bounds the weights:

  `isSpread_weightClass` : the heaviest class is `κ·A/(2(J+1)M)`-spread **as a family**.

Since a subfamily of the support only fails more often, that suffices for the bottom step:
`failCount_le_of_janson_massSpread` is the Janson bottom from `WLinkBounded` **alone**, and
`iterate_le_janson_mass` runs the whole iteration with no side hypothesis. `hinv` is gone.

The price is `J + 1 ≈ log₂(largest multiplicity)` in the budget, and `janson_mass_conditions`
does that chase: everything follows from `hJ : 8192·r²·L²·(J+1) ≤ κ`. What `hJ` costs is
`width_le_of_multiplicity_budget`: since `M = |𝓖| ≥ κ^{w'}` forces `J ≥ w'`, the route needs

  `w' + 1 ≤ κ/(8192·r²·L²)`,

an enormous but finite width ceiling that grows only like `r·lg w·lg lg w`. So the Janson route
delivers the spread lemma for every width below that ceiling, and the multiset formulation —
not the estimate — is what stops it from delivering all of them. For an honest family `J = 0`
and there is no price at all, which is why ALWZ, who carry families, never meet this.
-/
import Sunflower.JansonIterate
import Sunflower.SpreadAssemble

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## The obstruction: the mass-routed budget is infeasible -/

/-- **The Janson budget of `iterate_le_janson` cannot be met** at the instantiation
`spread_core_main` uses, where the mass floor and the spread bound are both the family size:
with `A₀ = M = G` and `κ^{w'} ≤ G` (which spreadness forces), `hJ3` fails for `w' ≥ 2`, by a
factor `G/κ² ≥ κ^{w'-2}`. -/
theorem janson_mass_budget_infeasible {κ p εbot G : ℝ} {L w' : ℕ}
    (hκ : 1 ≤ κ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hL : 4 ≤ L) (hw' : 2 ≤ w')
    (hG : κ ^ w' ≤ G) (hεb : 0 < εbot) (hεb2 : εbot ≤ 1 / 2) :
    G * κ ^ 2 * p / (64 * G ^ 2 * (L : ℝ) ^ 2) < Real.log (2 / εbot) := by
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκ2G : κ ^ 2 ≤ G := le_trans (pow_le_pow_right₀ hκ hw') hG
  have hκ2pos : (0 : ℝ) < κ ^ 2 := by positivity
  have hGpos : (0 : ℝ) < G := lt_of_lt_of_le hκ2pos hκ2G
  have hLR : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  -- the left side is at most `1/1024`
  have hleft : G * κ ^ 2 * p / (64 * G ^ 2 * (L : ℝ) ^ 2) ≤ 1 / 1024 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : G * κ ^ 2 * p ≤ G * G * 1 := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hκ2G hGpos.le) hp1 hp0.le (by positivity)
    have h2 : G * G * 1 ≤ 1 / 1024 * (64 * G ^ 2 * (L : ℝ) ^ 2) := by
      have h3 : (16 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg G, hGpos]
    linarith
  -- the right side exceeds `1`
  have hlog : (1 : ℝ) < Real.log (2 / εbot) := by
    have h4 : (4 : ℝ) ≤ 2 / εbot := by
      rw [le_div_iff₀ hεb]
      linarith
    have hlog4 : Real.log 4 ≤ Real.log (2 / εbot) :=
      Real.log_le_log (by norm_num) h4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have := Real.log_two_gt_d9
    linarith
  linarith

/-- The same statement at the level of the family: for a `w'`-uniform `κ`-spread family with
`w' ≥ 2`, the Janson budget of `iterate_le_janson` — instantiated as `spread_core_main` does,
with `A₀ = M = |𝓖|` — is false. -/
theorem janson_budget_infeasible_of_isSpread {𝓖 : Finset (Finset α)} {κ p εbot : ℝ}
    {L w' : ℕ} (hκ : 1 ≤ κ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hL : 4 ≤ L) (hw' : 2 ≤ w')
    (hne : 𝓖.Nonempty) (hu : IsUniform w' 𝓖) (hsp : IsSpread κ 𝓖)
    (hεb : 0 < εbot) (hεb2 : εbot ≤ 1 / 2) :
    ¬ (Real.log (2 / εbot)
        ≤ (𝓖.card : ℝ) * κ ^ 2 * p / (64 * (𝓖.card : ℝ) ^ 2 * (L : ℝ) ^ 2)) := by
  have hG : κ ^ w' ≤ (𝓖.card : ℝ) :=
    pow_le_card_of_isSpread (le_trans zero_le_one hκ) hne hu hsp
  exact not_le_of_gt (janson_mass_budget_infeasible hκ hp0 hp1 hL hw' hG hεb hεb2)

/-! ## The repair: the bottom step under support-spreadness

Everything below is unconditional. `IsSpread κ (supp X σ)` says the *support*, as a family, is
`κ`-spread — the hypothesis ALWZ carry and the one Janson actually consumes. -/

/-- Covering does not see multiplicities: the system and the indicator of its support have the
same covered sets. -/
lemma wCovered_indW_supp {X : Finset α} {σ : Finset α → ℕ} {v : ℕ} (hb : WBounded X v σ)
    (W : Finset α) : WCovered (indW (supp X σ)) W ↔ WCovered σ W := by
  constructor
  · rintro ⟨S, hS, hSW⟩
    rw [indW_ne_zero] at hS
    exact ⟨S, (mem_supp.mp hS).2, hSW⟩
  · rintro ⟨S, hS, hSW⟩
    exact ⟨S, indW_ne_zero.mpr (mem_supp.mpr ⟨(hb S hS).1, hS⟩), hSW⟩

/-- Hence the failure counts agree: **deduplication is free** for the Janson estimate. -/
lemma failCount_indW_supp {X : Finset α} {σ : Finset α → ℕ} {v m : ℕ} (hb : WBounded X v σ) :
    failCount X (indW (supp X σ)) m = failCount X σ m := by
  classical
  simp only [failCount]
  refine congrArg Finset.card (Finset.filter_congr fun W _ => ?_)
  constructor
  · intro h hc
    exact h ((wCovered_indW_supp hb W).mpr hc)
  · intro h hc
    exact h ((wCovered_indW_supp hb W).mp hc)

omit [DecidableEq α] in
/-- For a `0`/`1`-valued system, mass is support size. -/
lemma wTotal_eq_card_supp {X : Finset α} {σ : Finset α → ℕ} (h : ∀ S, σ S ≤ 1) :
    wTotal X σ = (supp X σ).card := by
  classical
  rw [wTotal, supp, Finset.card_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  have := h S
  by_cases hs : σ S = 0
  · simp [hs]
  · rw [if_pos hs]
    omega

/-- **The Janson bottom step under support-spreadness.** For a `≤ v`-bounded system whose
support is `κ`-spread *as a family*, the failure fraction is below `εbot` once

`log(2/εbot) ≤ κ·p/(8v²)`.

Compare `JansonBottom.failCount_le_of_janson_bounded`, whose budget carries the ratio
`A/M²`: here there is no such ratio, because `card_supp_superset_le` is applied to the
indicator of the support, where count and mass coincide. The `v²` is the heaviest-class
reduction: a factor `v` because the class may sit at any width `u ≤ v`, and another because
the class carries only a `1/v` fraction of the support. -/
theorem failCount_le_of_janson_isSpread {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {κ p εbot : ℝ}
    (hb : WBounded X v σ) (hsp : IsSpread κ (supp X σ))
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hv : 1 ≤ v)
    (hN : 0 < (supp X σ).card)
    (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hεb : 0 < εbot)
    (hbudget : Real.log (2 / εbot) ≤ κ * p / (8 * (v : ℝ) ^ 2))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
  classical
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκp : (0 : ℝ) < κ * p := mul_pos hκ0 hp
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hv1R : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  -- `hvt` says `κp ≥ 2v ≥ 2`
  have hκp2 : 2 * (v : ℝ) ≤ κ * p := by
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp] at hvt
    linarith
  have hκp1 : (1 : ℝ) ≤ κ * p := by linarith
  by_cases hE : σ ∅ ≠ 0
  · rw [failCount_eq_zero_of_empty_mem X σ m₀ hE, Nat.cast_zero]
    exact mul_nonneg hεb.le (Nat.cast_nonneg _)
  rw [not_not] at hE
  set 𝓖 := supp X σ with h𝓖
  have h𝓖X : ∀ S ∈ 𝓖, S ⊆ X := fun _ hS => subset_of_mem_supp hS
  set τ₀ := indW 𝓖 with hτ₀
  have hsupp₀ : supp X τ₀ = 𝓖 := supp_indW h𝓖X
  have hb₀ : WBounded X v τ₀ := by
    intro S hS
    rw [hτ₀, indW_ne_zero] at hS
    exact ⟨h𝓖X S hS, (hb S (mem_supp.mp hS).2).2⟩
  have hl₀ : WLinkBounded X τ₀ (𝓖.card : ℝ) κ := wLinkBounded_indW h𝓖X hsp
  have hτ₀1 : ∀ S, τ₀ S ≤ 1 := by
    intro S
    rw [hτ₀, indW]
    split <;> norm_num
  have hE₀ : τ₀ ∅ = 0 := by
    have : (∅ : Finset α) ∉ 𝓖 := by
      rw [h𝓖]
      intro hmem
      exact (mem_supp.mp hmem).2 hE
    rw [hτ₀, indW, if_neg this]
  have hNpos : 0 < 𝓖.card := hN
  -- the heaviest size class of the deduplicated system
  obtain ⟨u, huIcc, hheavy⟩ := exists_heavy_sizeClass hb₀ hE₀ hv
  rw [Finset.mem_Icc] at huIcc
  obtain ⟨hu1, huv⟩ := huIcc
  set τ := sizeClass τ₀ u with hτ
  have hτ1 : ∀ S, τ S ≤ 1 := fun S => le_trans (sizeClass_le τ₀ u S) (hτ₀1 S)
  have hNu : wTotal X τ = (supp X τ).card := wTotal_eq_card_supp hτ1
  have hN₀ : wTotal X τ₀ = 𝓖.card := by
    rw [wTotal_eq_card_supp hτ₀1, hsupp₀]
  -- `N ≤ v·N_u`
  have hheavy' : 𝓖.card ≤ v * (supp X τ).card := by rw [← hNu, ← hN₀]; exact hheavy
  have hNupos : 0 < (supp X τ).card := by
    by_contra hcon
    push Not at hcon
    have h0 : (supp X τ).card = 0 := Nat.le_zero.mp hcon
    rw [h0, Nat.mul_zero] at hheavy'
    omega
  have hNuR : (0 : ℝ) < ((supp X τ).card : ℝ) := by exact_mod_cast hNupos
  have hNR : (0 : ℝ) < (𝓖.card : ℝ) := by exact_mod_cast hNpos
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu1
  have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  -- the class is `u`-uniform, still `κ`-spread against the *global* support size
  have hbu : WBounded X u τ := wBounded_sizeClass hb₀ u
  have hlu : WLinkBounded X τ (𝓖.card : ℝ) κ := wLinkBounded_sizeClass hκ0.le hl₀ u
  have huu : SuppUniform X τ u := suppUniform_sizeClass X τ₀ u
  -- `κ^u ≤ N`, from spreadness at a member of the class
  have hκuN : κ ^ u ≤ (𝓖.card : ℝ) := by
    obtain ⟨T₀, hT₀⟩ := Finset.card_pos.mp hNupos
    have hT₀𝓖 : T₀ ∈ 𝓖 := by
      have := (mem_supp.mp hT₀).2
      have h1 : τ₀ T₀ ≠ 0 := fun h0 => this (by rw [hτ, sizeClass, h0]; simp)
      rw [hτ₀, indW_ne_zero] at h1
      exact h1
    have hcard : T₀.card = u := huu T₀ hT₀
    have hlink : 1 ≤ (link 𝓖 T₀).card := by
      rw [card_link]
      exact Finset.card_pos.mpr ⟨T₀, Finset.mem_filter.mpr ⟨hT₀𝓖, Finset.Subset.rfl⟩⟩
    have h := hsp T₀
    rw [hcard] at h
    calc κ ^ u = 1 * κ ^ u := (one_mul _).symm
      _ ≤ ((link 𝓖 T₀).card : ℝ) * κ ^ u := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hlink
      _ ≤ (𝓖.card : ℝ) := h
  -- the `q ≤ 1` check
  have hμD : ((supp X τ).card : ℝ) * p ^ u
      ≤ 2 * (((supp X τ).card : ℝ)
          * ((𝓖.card : ℝ) * p ^ (2 * u) * (2 * (u : ℝ) * (κ * p)⁻¹))) := by
    have hkey : κ * p ≤ 4 * (u : ℝ) * (𝓖.card : ℝ) * p ^ u := by
      have h1 : (κ * p) ^ 1 ≤ (κ * p) ^ u := pow_le_pow_right₀ hκp1 hu1
      rw [pow_one] at h1
      have h2 : (κ * p) ^ u = κ ^ u * p ^ u := mul_pow κ p u
      have h3 : κ ^ u * p ^ u ≤ (𝓖.card : ℝ) * p ^ u :=
        mul_le_mul_of_nonneg_right hκuN (by positivity)
      have h4 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      nlinarith [h1, h3, mul_nonneg (Nat.cast_nonneg (𝓖.card)) (pow_nonneg hp.le u)]
    have hrw : 2 * (((supp X τ).card : ℝ)
          * ((𝓖.card : ℝ) * p ^ (2 * u) * (2 * (u : ℝ) * (κ * p)⁻¹)))
        = (((supp X τ).card : ℝ) * p ^ u)
            * ((4 * (u : ℝ) * (𝓖.card : ℝ) * p ^ u) / (κ * p)) := by
      rw [two_mul u, pow_add]
      field_simp
      ring
    rw [hrw]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [le_div_iff₀ hκp, one_mul]
    exact hkey
  -- Janson for the class, with `M = N`: the exponent is `N_u·κ·p/(8·N·u)`
  have hjan := failCount_le_janson_budget (X := X) (v := u) (σ := τ) (M := (𝓖.card : ℝ))
    (κ := κ) (p := p) hbu hlu huu hκ0 hp hp1 hNR hu1 hNupos
    (le_trans (mul_le_mul_of_nonneg_right huvR (by positivity)) hvt) hμD hm₀ hm₀n hsmall
  -- `N_u·κ·p/(8·N·u) ≥ κ·p/(8v²)`, since `N ≤ v·N_u` and `u ≤ v`
  have hexp : κ * p / (8 * (v : ℝ) ^ 2)
      ≤ ((supp X τ).card : ℝ) * κ * p / (8 * (𝓖.card : ℝ) * (u : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hNv : (𝓖.card : ℝ) ≤ (v : ℝ) * ((supp X τ).card : ℝ) := by exact_mod_cast hheavy'
    have hkey : (𝓖.card : ℝ) * (u : ℝ) ≤ ((supp X τ).card : ℝ) * (v : ℝ) ^ 2 := by
      nlinarith [hNv, huvR, hNuR, hvR, huR]
    calc κ * p * (8 * (𝓖.card : ℝ) * (u : ℝ))
        = (8 * (κ * p)) * ((𝓖.card : ℝ) * (u : ℝ)) := by ring
      _ ≤ (8 * (κ * p)) * (((supp X τ).card : ℝ) * (v : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = ((supp X τ).card : ℝ) * κ * p * (8 * (v : ℝ) ^ 2) := by ring
  -- convert the exponential bound into the failure fraction
  have hexpb : Real.exp (- (((supp X τ).card : ℝ) * κ * p / (8 * (𝓖.card : ℝ) * (u : ℝ))))
      ≤ εbot / 2 := by
    have hpos : (0 : ℝ) < 2 / εbot := by positivity
    refine le_trans (Real.exp_le_exp.mpr (neg_le_neg (le_trans hbudget hexp))) ?_
    rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  have hfinal : (failCount X τ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
    calc (failCount X τ m₀ : ℝ)
        ≤ 2 * (Real.exp (- (((supp X τ).card : ℝ) * κ * p / (8 * (𝓖.card : ℝ) * (u : ℝ))))
            * (X.card.choose m₀ : ℝ)) := hjan
      _ ≤ 2 * ((εbot / 2) * (X.card.choose m₀ : ℝ)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hexpb hchoose) (by norm_num)
      _ = εbot * (X.card.choose m₀ : ℝ) := by ring
  refine le_trans ?_ hfinal
  have h1 : failCount X σ m₀ = failCount X τ₀ m₀ := (failCount_indW_supp hb).symm
  rw [h1]
  exact_mod_cast failCount_le_sizeClass X τ₀ u m₀

/-! ## Support-spreadness itself is not available — but a weight class of it is

`hinv` below asks for `IsSpread κs (supp X σ)`. That is **false** for systems satisfying the
iteration's invariants (`suppSpread_not_of_wLinkBounded` at the end of this file): mass-spread
constrains *weights*, and a multiset can park a large *count* in a star while keeping the mass
spread — the star members carry weight `1` each, and a little heavy ballast elsewhere pays for
their link.

What survives is the same device used twice already, now applied to weight: split the support
into **dyadic weight classes** `𝓗_j = {T ∈ supp : 2^j ≤ σ T < 2^{j+1}}`. Inside one class,
count and mass agree up to a factor `2`, so mass-spreadness *is* count-spreadness there. The
heaviest class carries a `1/(J+1)` fraction of the mass, where `2^J` bounds the weights, so:

  the heaviest class is `κ·A/(2(J+1)M)`-spread **as a family**.

Since a subfamily of the support only has *more* failures, that is enough for the bottom step,
and the Janson route becomes unconditional — at the price of `J + 1 ≈ log₂(max multiplicity)`
in the budget. For an honest family (`J = 0`) there is no price at all, which is why ALWZ,
who carry families, never meet this. -/

/-- The `j`-th **dyadic weight class** of the support. -/
def weightClass (X : Finset α) (σ : Finset α → ℕ) (j : ℕ) : Finset (Finset α) :=
  (supp X σ).filter fun T => Nat.log 2 (σ T) = j

omit [DecidableEq α] in
lemma weightClass_subset (X : Finset α) (σ : Finset α → ℕ) (j : ℕ) :
    weightClass X σ j ⊆ supp X σ := Finset.filter_subset _ _

omit [DecidableEq α] in
lemma pow_le_of_mem_weightClass {X : Finset α} {σ : Finset α → ℕ} {j : ℕ} {T : Finset α}
    (h : T ∈ weightClass X σ j) : 2 ^ j ≤ σ T := by
  rw [weightClass, Finset.mem_filter] at h
  obtain ⟨hT, hlog⟩ := h
  calc 2 ^ j = 2 ^ Nat.log 2 (σ T) := by rw [hlog]
    _ ≤ σ T := Nat.pow_log_le_self 2 (mem_supp.mp hT).2

omit [DecidableEq α] in
lemma lt_pow_of_mem_weightClass {X : Finset α} {σ : Finset α → ℕ} {j : ℕ} {T : Finset α}
    (h : T ∈ weightClass X σ j) : σ T < 2 ^ (j + 1) := by
  rw [weightClass, Finset.mem_filter] at h
  obtain ⟨-, hlog⟩ := h
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (σ T)
  rwa [hlog] at this

omit [DecidableEq α] in
/-- The mass of a system lives on its support. -/
lemma wTotal_eq_sum_supp (X : Finset α) (σ : Finset α → ℕ) :
    (wTotal X σ : ℝ) = ∑ T ∈ supp X σ, (σ T : ℝ) := by
  classical
  rw [wTotal]
  push_cast
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro T hT hTn
  have hz : σ T = 0 := by
    by_contra hc
    exact hTn (mem_supp.mpr ⟨Finset.mem_powerset.mp hT, hc⟩)
  rw [hz]
  exact Nat.cast_zero

/-- Under `WLinkBounded`, no member weighs more than `M`. -/
lemma weight_le_of_wLinkBounded {X : Finset α} {σ : Finset α → ℕ} {M κ : ℝ}
    (hκ : 1 ≤ κ) (hl : WLinkBounded X σ M κ) (hE : σ ∅ = 0) {T : Finset α}
    (hT : T ∈ supp X σ) : (σ T : ℝ) ≤ M := by
  have hne : T.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T with rfl | h
    · exact absurd hE (mem_supp.mp hT).2
    · exact h
  have hsub : (σ T : ℝ) ≤ (wLink X σ T : ℝ) := by
    have : σ T ≤ wLink X σ T := by
      rw [wLink]
      refine Finset.single_le_sum (f := σ) (fun _ _ => Nat.zero_le _) ?_
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (subset_of_mem_supp hT), Finset.Subset.rfl⟩
    exact_mod_cast this
  have hpow : (1 : ℝ) ≤ κ ^ T.card := one_le_pow₀ hκ
  have h := hl T hne
  nlinarith [Nat.cast_nonneg (α := ℝ) (wLink X σ T)]

/-- **Pigeonhole on weight classes.** With all weights below `2^J`, some class carries a
`1/(J+1)` fraction of the mass. -/
lemma exists_heavy_weightClass {X : Finset α} {σ : Finset α → ℕ} {M κ A : ℝ} {J : ℕ}
    (hκ : 1 ≤ κ) (hl : WLinkBounded X σ M κ) (hE : σ ∅ = 0) (hMJ : M ≤ 2 ^ J)
    (hA : A ≤ (wTotal X σ : ℝ)) :
    ∃ j ≤ J, A / ((J : ℝ) + 1) ≤ ∑ T ∈ weightClass X σ j, (σ T : ℝ) := by
  classical
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hmaps : ∀ T ∈ supp X σ, Nat.log 2 (σ T) ∈ Finset.range (J + 1) := by
    intro T hT
    rw [Finset.mem_range]
    have h1 : (σ T : ℝ) ≤ 2 ^ J := le_trans (weight_le_of_wLinkBounded hκ hl hE hT) hMJ
    have h2 : σ T ≤ 2 ^ J := by exact_mod_cast h1
    have : Nat.log 2 (σ T) ≤ J := by
      calc Nat.log 2 (σ T) ≤ Nat.log 2 (2 ^ J) := Nat.log_mono_right h2
        _ = J := Nat.log_pow (by norm_num : 1 < 2) J
    omega
  have hsplit : ∑ j ∈ Finset.range (J + 1), ∑ T ∈ weightClass X σ j, (σ T : ℝ)
      = ∑ T ∈ supp X σ, (σ T : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  by_contra hcon
  push Not at hcon
  have hlt : ∑ j ∈ Finset.range (J + 1), ∑ T ∈ weightClass X σ j, (σ T : ℝ)
      < ∑ _j ∈ Finset.range (J + 1), A / ((J : ℝ) + 1) := by
    refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (by omega)⟩ fun j hj => ?_
    exact hcon j (by rw [Finset.mem_range] at hj; omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
  rw [hcast, mul_div_cancel₀ A (ne_of_gt hJ1)] at hlt
  rw [hsplit, ← wTotal_eq_sum_supp] at hlt
  linarith

/-- **The heaviest weight class is spread as a family.** Inside a dyadic class, count and mass
agree up to a factor `2`, so the mass-spread hypothesis becomes count-spread — with the
`A/M` ratio and the `1/(J+1)` pigeonhole loss. This is what replaces the false hypothesis
`IsSpread κs (supp X σ)`. -/
theorem isSpread_weightClass {X : Finset α} {σ : Finset α → ℕ} {M κ A : ℝ} {J j : ℕ}
    (hκ : 1 ≤ κ) (hl : WLinkBounded X σ M κ) (hM : 0 < M) (hA0 : 0 < A) (hAM : A ≤ 2 * M)
    (hheavy : A / ((J : ℝ) + 1) ≤ ∑ T ∈ weightClass X σ j, (σ T : ℝ)) :
    IsSpread (κ * (A / (2 * ((J : ℝ) + 1) * M))) (weightClass X σ j) := by
  classical
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  set 𝓗 := weightClass X σ j with h𝓗
  set c : ℝ := A / (2 * ((J : ℝ) + 1) * M) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    nlinarith [hM, hJ1]
  have hP : (0 : ℝ) < 2 ^ j := by positivity
  -- the class's mass is at most `|𝓗|·2^{j+1}`
  have hmass : ∑ T ∈ 𝓗, (σ T : ℝ) ≤ (𝓗.card : ℝ) * (2 * 2 ^ j) := by
    calc ∑ T ∈ 𝓗, (σ T : ℝ) ≤ ∑ _T ∈ 𝓗, (2 : ℝ) ^ (j + 1) := by
          refine Finset.sum_le_sum fun T hT => ?_
          have := lt_pow_of_mem_weightClass (h𝓗 ▸ hT)
          have : (σ T : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast this.le
          exact this
      _ = (𝓗.card : ℝ) * (2 * 2 ^ j) := by
          rw [Finset.sum_const, nsmul_eq_mul, pow_succ]
          ring
  have hcard : A / (((J : ℝ) + 1) * (2 * 2 ^ j)) ≤ (𝓗.card : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : A / ((J : ℝ) + 1) ≤ (𝓗.card : ℝ) * (2 * 2 ^ j) := le_trans hheavy hmass
    rw [div_le_iff₀ hJ1] at h1
    calc A ≤ (𝓗.card : ℝ) * (2 * 2 ^ j) * ((J : ℝ) + 1) := h1
      _ = (𝓗.card : ℝ) * (((J : ℝ) + 1) * (2 * 2 ^ j)) := by ring
  intro Z
  rcases Finset.eq_empty_or_nonempty Z with rfl | hZ
  · rw [card_link, Finset.filter_true_of_mem fun x _ => Finset.empty_subset x,
      Finset.card_empty, pow_zero, mul_one]
  · have hZ1 : 1 ≤ Z.card := Finset.card_pos.mpr hZ
    set cnt : ℝ := ((𝓗.filter fun T => Z ⊆ T).card : ℝ) with hcnt
    have hcnt0 : 0 ≤ cnt := Nat.cast_nonneg _
    -- count times the class floor is at most the link mass
    have h1 : cnt * (2 : ℝ) ^ j ≤ (wLink X σ Z : ℝ) := by
      have hnat : (𝓗.filter fun T => Z ⊆ T).card * 2 ^ j ≤ wLink X σ Z := by
        calc (𝓗.filter fun T => Z ⊆ T).card * 2 ^ j
            = ∑ _T ∈ 𝓗.filter fun T => Z ⊆ T, 2 ^ j := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ T ∈ 𝓗.filter fun T => Z ⊆ T, σ T := by
              refine Finset.sum_le_sum fun T hT => ?_
              exact pow_le_of_mem_weightClass (h𝓗 ▸ (Finset.mem_filter.mp hT).1)
          _ ≤ ∑ S ∈ X.powerset.filter fun S => Z ⊆ S, σ S := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
              intro T hT
              rw [Finset.mem_filter] at hT ⊢
              exact ⟨Finset.mem_powerset.mpr
                (subset_of_mem_supp (weightClass_subset X σ j (h𝓗 ▸ hT.1))), hT.2⟩
          _ = wLink X σ Z := rfl
      calc cnt * (2 : ℝ) ^ j
          = (((𝓗.filter fun T => Z ⊆ T).card * 2 ^ j : ℕ) : ℝ) := by rw [hcnt]; push_cast; ring
        _ ≤ (wLink X σ Z : ℝ) := by exact_mod_cast hnat
    have h2 : (wLink X σ Z : ℝ) * κ ^ Z.card ≤ M := hl Z hZ
    have hK : (0 : ℝ) < κ ^ Z.card := by positivity
    -- `cnt·κ^{|Z|} ≤ M/2^j`
    have h3 : cnt * κ ^ Z.card * 2 ^ j ≤ M := by
      calc cnt * κ ^ Z.card * 2 ^ j = (cnt * 2 ^ j) * κ ^ Z.card := by ring
        _ ≤ (wLink X σ Z : ℝ) * κ ^ Z.card := mul_le_mul_of_nonneg_right h1 hK.le
        _ ≤ M := h2
    -- `c^{|Z|} ≤ c`
    have h4 : c ^ Z.card ≤ c := by
      calc c ^ Z.card ≤ c ^ 1 := pow_le_pow_of_le_one hc0.le hc1 hZ1
        _ = c := pow_one c
    rw [card_link, ← hcnt, mul_pow]
    calc cnt * (κ ^ Z.card * c ^ Z.card) ≤ cnt * (κ ^ Z.card * c) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hK.le) hcnt0
      _ = (cnt * κ ^ Z.card) * c := by ring
      _ ≤ (M / 2 ^ j) * c := by
          refine mul_le_mul_of_nonneg_right ?_ hc0.le
          rw [le_div_iff₀ hP]
          exact h3
      _ = A / (((J : ℝ) + 1) * (2 * 2 ^ j)) := by
          rw [hc]
          field_simp
      _ ≤ (𝓗.card : ℝ) := hcard

/-- A subfamily of the support only has more failures. -/
lemma failCount_le_indW_subfamily {X : Finset α} {σ : Finset α → ℕ}
    {𝓗 : Finset (Finset α)} (h : 𝓗 ⊆ supp X σ) (m : ℕ) :
    failCount X σ m ≤ failCount X (indW 𝓗) m := by
  classical
  simp only [failCount]
  refine Finset.card_le_card fun W hW => ?_
  rw [Finset.mem_filter] at hW ⊢
  refine ⟨hW.1, fun hcov => hW.2 ?_⟩
  obtain ⟨S, hS, hSW⟩ := hcov
  rw [indW_ne_zero] at hS
  exact ⟨S, (mem_supp.mp (h hS)).2, hSW⟩

/-- **The Janson bottom step from mass-spreadness alone** — no support hypothesis. Passing to
the heaviest dyadic weight class turns `WLinkBounded X σ M κ` into genuine family
spreadness, at the cost of `2(J+1)M/A` in the constant, where `2^J` bounds the weights.

This is what makes the Janson route unconditional: `hinv` disappears. What it costs is the
`J + 1` — the number of weight scales, i.e. `log₂` of the largest multiplicity. -/
theorem failCount_le_of_janson_massSpread {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {M κ κs p A εbot : ℝ} {J : ℕ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hv : 1 ≤ v) (hM : 0 < M) (hMJ : M ≤ 2 ^ J)
    (hA0 : 0 < A) (hAM : A ≤ 2 * M) (hA : A ≤ (wTotal X σ : ℝ))
    (hκs1 : 1 ≤ κs) (hκs : κs ≤ κ * (A / (2 * ((J : ℝ) + 1) * M)))
    (hvt : (v : ℝ) * (κs * p)⁻¹ ≤ 1 / 2)
    (hεb : 0 < εbot)
    (hbudget : Real.log (2 / εbot) ≤ κs * p / (8 * (v : ℝ) ^ 2))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
  classical
  by_cases hE : σ ∅ ≠ 0
  · rw [failCount_eq_zero_of_empty_mem X σ m₀ hE, Nat.cast_zero]
    exact mul_nonneg hεb.le (Nat.cast_nonneg _)
  rw [not_not] at hE
  obtain ⟨j, -, hheavy⟩ := exists_heavy_weightClass hκ hl hE hMJ hA
  set 𝓗 := weightClass X σ j with h𝓗
  have h𝓗sub : 𝓗 ⊆ supp X σ := weightClass_subset X σ j
  have h𝓗X : ∀ S ∈ 𝓗, S ⊆ X := fun S hS => subset_of_mem_supp (h𝓗sub hS)
  -- the class is spread as a family, hence so is it at the weaker constant `κs`
  have hspread : IsSpread κs 𝓗 :=
    (isSpread_weightClass hκ hl hM hA0 hAM hheavy).mono (by linarith) hκs
  -- the class is nonempty: it carries positive mass
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hne : 0 < 𝓗.card := by
    rcases Finset.eq_empty_or_nonempty 𝓗 with hem | h
    · exfalso
      rw [hem, Finset.sum_empty] at hheavy
      have : (0 : ℝ) < A / ((J : ℝ) + 1) := by positivity
      linarith
    · exact Finset.card_pos.mpr h
  -- run the support-spread bottom on the indicator of the class
  set τ := indW 𝓗 with hτ
  have hsupp : supp X τ = 𝓗 := supp_indW h𝓗X
  have hbτ : WBounded X v τ := by
    intro S hS
    rw [hτ, indW_ne_zero] at hS
    exact ⟨h𝓗X S hS, (hb S (mem_supp.mp (h𝓗sub hS)).2).2⟩
  have hmain := failCount_le_of_janson_isSpread (X := X) (v := v) (σ := τ) (κ := κs) (p := p)
    (εbot := εbot) hbτ (by rw [hsupp]; exact hspread) hκs1 hp hp1 hv (by rw [hsupp]; exact hne)
    hvt hεb hbudget hm₀ hm₀n hsmall
  refine le_trans ?_ hmain
  exact_mod_cast failCount_le_indW_subfamily h𝓗sub m₀

/-! ## The iteration on the support-spread bottom

The bottom conditions shrink to three, uniform in `v ≤ 2L`, `m ≥ m_bot`, `|X| ≤ n₀`:

* `hS1 : 4L ≤ κs·p`                        — the linearisation condition;
* `hS2 : log(2/εbot) ≤ κs·p/(32L²)`        — the budget, in `log(1/εbot)` form;
* `hS3 : 2p·n₀ ≤ m_bot`                    — the `p`-biased/fixed-size bridge.

The `q ≤ 1` check of `hJ2` is gone: support-spreadness gives `κs^u ≤ |supp|` at a member of
the class, which discharges it from `κs·p ≥ 1` alone. -/

/-- The bottom regime under support-spreadness, in the shape `iterate_le_of_bottom` consumes.
Note that the mass-spread hypothesis `WLinkBounded X σ M κ` is not used: this route runs
entirely on `IsSpread κs (supp X σ)`. -/
theorem janson_bottom_supp {L m_bot n₀ : ℕ} {A₀ κs p εbot : ℝ} {X : Finset α}
    {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ}
    (hL : 2 ≤ L) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hκs : 1 ≤ κs) (hp : 0 < p) (hp1 : p ≤ 1) (hεb : 0 < εbot)
    (hS1 : 4 * (L : ℝ) ≤ κs * p)
    (hS2 : Real.log (2 / εbot) ≤ κs * p / (32 * (L : ℝ) ^ 2))
    (hS3 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ))
    (hinv : IsSpread κs (supp X σ))
    (hb : WBounded X v σ)
    (htot : A ≤ (wTotal X σ : ℝ)) (hAinv : A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A)
    (hv : 1 ≤ v) (hvL : v ≤ 2 * L) (hmm : m_bot ≤ m) (hmn : m ≤ X.card)
    (hn₀ : X.card ≤ n₀) :
    (failCount X σ m : ℝ) ≤ εbot * (X.card.choose m : ℝ) := by
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hvL' : (v : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hvL
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hκs0 : (0 : ℝ) < κs := lt_of_lt_of_le zero_lt_one hκs
  have hκp : (0 : ℝ) < κs * p := mul_pos hκs0 hp
  -- the mass never drops below `A₀/2`, so the support is nonempty
  have hhalf : (1 / 2 : ℝ) ^ (v + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (v + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hA2 : A₀ / 2 ≤ A := by
    calc A₀ / 2 = A₀ * (1 - 1 / 2) := by ring
      _ ≤ A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) := mul_le_mul_of_nonneg_left (by linarith) hA₀.le
      _ ≤ A := hAinv
  have hwpos : 0 < wTotal X σ := by
    by_contra hcon
    push Not at hcon
    have hz : wTotal X σ = 0 := Nat.le_zero.mp hcon
    rw [hz, Nat.cast_zero] at htot
    linarith [hA₀]
  have hN : 0 < (supp X σ).card := card_supp_pos hwpos
  -- `hS1` gives the linearisation condition at every width `v ≤ 2L`
  have hvt : (v : ℝ) * (κs * p)⁻¹ ≤ 1 / 2 := by
    have h1 : (v : ℝ) * (κs * p)⁻¹ ≤ 2 * (L : ℝ) * (κs * p)⁻¹ :=
      mul_le_mul_of_nonneg_right hvL' (by positivity)
    have h2 : 2 * (L : ℝ) * (κs * p)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp]
      linarith
    linarith
  -- `hS2` gives the budget at every width `v ≤ 2L`
  have hbudget : Real.log (2 / εbot) ≤ κs * p / (8 * (v : ℝ) ^ 2) := by
    refine le_trans hS2 ?_
    refine div_le_div_of_nonneg_left hκp.le (by positivity) ?_
    nlinarith [hvR, hvL', hLR]
  -- `hS3` gives the bridge condition
  have hsmall : 2 * (p * (X.card : ℝ)) ≤ (m : ℝ) := by
    have h1 : (X.card : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h2 : (m_bot : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmm
    have h3 : p * (X.card : ℝ) ≤ p * (n₀ : ℝ) := mul_le_mul_of_nonneg_left h1 hp.le
    linarith
  exact failCount_le_of_janson_isSpread hb hinv hκs hp hp1 hv hN hvt hεb hbudget
    (by omega) hmn hsmall

/-- **The width-schedule iteration on the support-spread Janson bottom.** `iterate_le`'s
conclusion verbatim, with `hK2`, `hK3` replaced by `hS1`–`hS3` — and by `hinv`, which asks for
support-spreadness of the systems the iteration hands its bottom step.

`hinv` is not supplied by the iteration, and cannot be: it is false
(`suppSpread_not_of_wLinkBounded`). Use `iterate_le_janson_mass` instead, which manufactures
what it needs from `WLinkBounded` by passing to a dyadic weight class. This version is kept
because it is the statement with the *clean* constant — `κs` with no `1/(J+1)` — and shows
exactly what the loss buys. -/
theorem iterate_le_janson_supp {L s m_bot n₀ : ℕ} {A₀ M κ κs p ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 ≤ M) (hκ : 1 ≤ κ) (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hκs : 1 ≤ κs) (hp : 0 < p) (hp1 : p ≤ 1)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hS1 : 4 * (L : ℝ) ≤ κs * p)
    (hS2 : Real.log (2 / εbot) ≤ κs * p / (32 * (L : ℝ) ^ 2))
    (hS3 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ))
    (hinv : ∀ {X : Finset α} {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ},
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      1 ≤ v → v ≤ 2 * L → m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      IsSpread κs (supp X σ)) :
    ∀ (t : ℕ) (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) (A : ℝ) (m : ℕ),
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      (v : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t →
      1 ≤ v → s * t + m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤
        (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) :=
  iterate_le_of_bottom hL hs hmb hA₀ hM hκ hε hεb.le hK1
    (fun {_X _σ _v _m _A} hb hl htot hAinv hv hvL hmm hmn hn₀ =>
      janson_bottom_supp hL hmb hA₀ hκs hp hp1 hεb hS1 hS2 hS3
        (hinv hb hl htot hAinv hv hvL hmm hmn hn₀) hb htot hAinv hv hvL hmm hmn hn₀)

/-! ## The iteration with no side hypothesis at all

`janson_bottom_mass` is `janson_bottom_supp` with the support hypothesis replaced by the weight
class, so `iterate_le_janson_mass` needs no `hinv`. The price is in the constant: the bottom
runs at `κs ≤ κ·A₀/(4(J+1)M)`, where `2^J` bounds the weights. -/

/-- The bottom regime from mass-spreadness alone, in the shape `iterate_le_of_bottom` consumes. -/
theorem janson_bottom_mass {L m_bot n₀ J : ℕ} {A₀ M κ κs p εbot : ℝ} {X : Finset α}
    {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ}
    (hL : 2 ≤ L) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hMJ : M ≤ 2 ^ J) (hA₀M : A₀ ≤ 4 * M)
    (hκ : 1 ≤ κ) (hκs1 : 1 ≤ κs) (hκs : κs ≤ κ * (A₀ / (4 * ((J : ℝ) + 1) * M)))
    (hp : 0 < p) (hp1 : p ≤ 1) (hεb : 0 < εbot)
    (hS1 : 4 * (L : ℝ) ≤ κs * p)
    (hS2 : Real.log (2 / εbot) ≤ κs * p / (32 * (L : ℝ) ^ 2))
    (hS3 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ))
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (htot : A ≤ (wTotal X σ : ℝ)) (hAinv : A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A)
    (hv : 1 ≤ v) (hvL : v ≤ 2 * L) (hmm : m_bot ≤ m) (hmn : m ≤ X.card)
    (hn₀ : X.card ≤ n₀) :
    (failCount X σ m : ℝ) ≤ εbot * (X.card.choose m : ℝ) := by
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hvL' : (v : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hvL
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hκs0 : (0 : ℝ) < κs := lt_of_lt_of_le zero_lt_one hκs1
  have hκp : (0 : ℝ) < κs * p := mul_pos hκs0 hp
  -- the mass floor `A₀/2`
  have hhalf : (1 / 2 : ℝ) ^ (v + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (v + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hA2 : A₀ / 2 ≤ A := by
    calc A₀ / 2 = A₀ * (1 - 1 / 2) := by ring
      _ ≤ A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) := mul_le_mul_of_nonneg_left (by linarith) hA₀.le
      _ ≤ A := hAinv
  have hvt : (v : ℝ) * (κs * p)⁻¹ ≤ 1 / 2 := by
    have h1 : (v : ℝ) * (κs * p)⁻¹ ≤ 2 * (L : ℝ) * (κs * p)⁻¹ :=
      mul_le_mul_of_nonneg_right hvL' (by positivity)
    have h2 : 2 * (L : ℝ) * (κs * p)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp]
      linarith
    linarith
  have hbudget : Real.log (2 / εbot) ≤ κs * p / (8 * (v : ℝ) ^ 2) := by
    refine le_trans hS2 ?_
    refine div_le_div_of_nonneg_left hκp.le (by positivity) ?_
    nlinarith [hvR, hvL', hLR]
  have hsmall : 2 * (p * (X.card : ℝ)) ≤ (m : ℝ) := by
    have h1 : (X.card : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h2 : (m_bot : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmm
    have h3 : p * (X.card : ℝ) ≤ p * (n₀ : ℝ) := mul_le_mul_of_nonneg_left h1 hp.le
    linarith
  refine failCount_le_of_janson_massSpread (A := A₀ / 2) (J := J) hb hl hκ hp hp1 hv hM hMJ
    (by linarith) (by linarith) (le_trans hA2 htot) hκs1 ?_ hvt hεb hbudget (by omega) hmn hsmall
  refine le_trans hκs (le_of_eq ?_)
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  field_simp
  ring

/-- **The width-schedule iteration on the Janson bottom, unconditionally.** No `hinv`: the
support-spreadness the bottom needs is manufactured from `WLinkBounded` by passing to the
heaviest dyadic weight class. `hMJ : M ≤ 2^J` is the only new input — a bound on how many
weight scales the systems can have, which `M ≤ 2^J` supplies since no member outweighs `M`. -/
theorem iterate_le_janson_mass {L s m_bot n₀ J : ℕ} {A₀ M κ κs p ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hMJ : M ≤ 2 ^ J) (hA₀M : A₀ ≤ 4 * M)
    (hκ : 1 ≤ κ) (hκs1 : 1 ≤ κs) (hκs : κs ≤ κ * (A₀ / (4 * ((J : ℝ) + 1) * M)))
    (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hS1 : 4 * (L : ℝ) ≤ κs * p)
    (hS2 : Real.log (2 / εbot) ≤ κs * p / (32 * (L : ℝ) ^ 2))
    (hS3 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ)) :
    ∀ (t : ℕ) (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) (A : ℝ) (m : ℕ),
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      (v : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t →
      1 ≤ v → s * t + m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤
        (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) :=
  iterate_le_of_bottom hL hs hmb hA₀ hM.le hκ hε hεb.le hK1
    (fun {_X _σ _v _m _A} hb hl htot hAinv hv hvL hmm hmn hn₀ =>
      janson_bottom_mass hL hmb hA₀ hM hMJ hA₀M hκ hκs1 hκs hp hp1 hεb hS1 hS2 hS3
        hb hl htot hAinv hv hvL hmm hmn hn₀)

/-! ## The chase

At `spread_core_main`'s own parameters — `κ = 2^41·r³·lg w·lg lg w`, `n ≥ κ` (`kappa_le_ground`),
`m = n/r`, `m_bot = m - m/2`, and `L` any width parameter with `4 ≤ L ≤ 88 + 4·lg r + 3·lg lg w`
(what `SpreadAssemble` proves of its `L := Nat.log 2 ⌈κ⌉₊ + Nat.log 2 r + 4`) — the three
support-spread conditions hold at

  `p := 1/(8r)`,   `εbot := 1/(4r)`,   `κs := κ`.

The budget is the interesting one: it needs `256·r·L²·log(8r) ≤ κ`, and `L² ≤ 23232 + 768r +
432·lg w` (the same estimate `SpreadAssemble` uses for `hK2`), so `2048·r²·L² ≤ κ` suffices —
against the second moment's `hK2`, which needs `576·r²·L² ≤ κ` *after* paying `1/εbot = 4r`
rather than `log(2/εbot) = log(8r)`. That is the `log(1/β)`-for-`1/β` trade, in the concrete
arithmetic. -/

/-- **The constant chase for the support-spread bottom.** All three conditions of
`iterate_le_janson_supp` hold at the `spread_core_main` parameters, with `p = 1/(8r)` and
`εbot = 1/(4r)` (the fourth conjunct, `1 ≤ κ`, is the standing hypothesis they are used
under). Only `Real.log` estimates are used, and only through `log x ≤ x - 1`. -/
theorem janson_supp_conditions {r w L n m m_bot : ℕ} (hr : 3 ≤ r) (hw : 2 ≤ w)
    (hL4 : 4 ≤ L) (hLub : (L : ℝ) ≤ 88 + 4 * lg r + 3 * lg (lg w))
    (hκn : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w) ≤ (n : ℝ))
    (hm : m = n / r) (hmbot : m_bot = m - m / 2) :
    (1 : ℝ) ≤ (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)
    ∧ 4 * (L : ℝ) ≤ ((2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)) * (1 / (8 * (r : ℝ)))
    ∧ Real.log (2 / (1 / (4 * (r : ℝ))))
        ≤ ((2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)) * (1 / (8 * (r : ℝ)))
            / (32 * (L : ℝ) ^ 2)
    ∧ 2 * ((1 / (8 * (r : ℝ))) * (n : ℝ)) ≤ (m_bot : ℝ) := by
  set κ : ℝ := (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w) with hκdef
  -- the `lg` facts, as in `spread_core_main`
  have hw2 : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hlgw : (1 : ℝ) < lg w := one_lt_lg hw2
  have hlgw0 : (0 : ℝ) < lg w := lt_trans one_pos hlgw
  have hlglg20 : (1 / 20 : ℝ) ≤ lg (lg w) := le_trans lg_lg_two_ge (lg_lg_le_lg_lg hw2)
  have hlglgpos : (0 : ℝ) < lg (lg w) := lt_of_lt_of_le (by norm_num) hlglg20
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr9 : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hr3r : 9 * (r : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith
  have hr32 : 3 * (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := by nlinarith [sq_nonneg (r : ℝ)]
  have hlgr2 : lg r ≤ 2 * (r : ℝ) := lg_le_double hrpos
  have hlgrsq : (lg r) ^ 2 ≤ 16 * (r : ℝ) := lg_sq_le (by exact_mod_cast (by omega : 1 ≤ r))
  have hlglgsq : (lg (lg w)) ^ 2 ≤ 16 * (lg w) := lg_sq_le hlgw.le
  have hκpos : (0 : ℝ) < κ := by
    rw [hκdef]
    exact mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) hlgw0) hlglgpos
  -- the three lower bounds on `κ`
  have hκlb1 : (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 ≤ κ := by
    rw [hκdef]
    have h1 : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * 1 * (1 / 20)
        ≤ 2 ^ 41 * (r : ℝ) ^ 3 * lg w * lg (lg w) := by
      refine mul_le_mul (mul_le_mul le_rfl hlgw.le (by norm_num) (by positivity))
        hlglg20 (by norm_num) ?_
      exact mul_nonneg (by positivity) hlgw0.le
    calc (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 = 2 ^ 41 * (r : ℝ) ^ 3 * 1 * (1 / 20) := by ring
      _ ≤ _ := h1
  have hκlb2 : (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 * lg w ≤ κ := by
    rw [hκdef]
    have h1 : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * (1 / 20)
        ≤ 2 ^ 41 * (r : ℝ) ^ 3 * lg w * lg (lg w) :=
      mul_le_mul_of_nonneg_left hlglg20 (mul_nonneg (by positivity) hlgw0.le)
    calc (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 * lg w
        = 2 ^ 41 * (r : ℝ) ^ 3 * lg w * (1 / 20) := by ring
      _ ≤ _ := h1
  have hκlb3 : (2 ^ 41 * 9 : ℝ) * (r : ℝ) * lg w * lg (lg w) ≤ κ := by
    rw [hκdef]
    have h1 : (2 ^ 41 : ℝ) * (9 * (r : ℝ)) ≤ 2 ^ 41 * (r : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hr3r (by positivity)
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hlgw0.le) hlglgpos.le
    calc (2 ^ 41 * 9 : ℝ) * (r : ℝ) * lg w * lg (lg w)
        = (2 ^ 41 : ℝ) * (9 * (r : ℝ)) * lg w * lg (lg w) := by ring
      _ ≤ _ := h3
  have hL4R : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  -- `L² ≤ 23232 + 768r + 432·lg w`, exactly as in `SpreadAssemble`
  have hLsq : (L : ℝ) ^ 2 ≤ 23232 + 768 * (r : ℝ) + 432 * (lg w) := by
    have h1 : (L : ℝ) ^ 2 ≤ (88 + 4 * lg r + 3 * lg (lg w)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hLub 2
    have h2 : (88 + 4 * lg r + 3 * lg (lg w)) ^ 2
        ≤ 3 * (88 ^ 2 + (4 * lg r) ^ 2 + (3 * lg (lg w)) ^ 2) := by
      nlinarith [sq_nonneg (88 - 4 * lg r), sq_nonneg (88 - 3 * lg (lg w)),
        sq_nonneg (4 * lg r - 3 * lg (lg w))]
    calc (L : ℝ) ^ 2 ≤ 3 * (88 ^ 2 + (4 * lg r) ^ 2 + (3 * lg (lg w)) ^ 2) := le_trans h1 h2
      _ = 23232 + 48 * (lg r) ^ 2 + 27 * (lg (lg w)) ^ 2 := by ring
      _ ≤ 23232 + 48 * (16 * (r : ℝ)) + 27 * (16 * (lg w)) := by
          have := mul_le_mul_of_nonneg_left hlgrsq (by norm_num : (0 : ℝ) ≤ 48)
          have := mul_le_mul_of_nonneg_left hlglgsq (by norm_num : (0 : ℝ) ≤ 27)
          linarith
      _ = 23232 + 768 * (r : ℝ) + 432 * (lg w) := by ring
  refine ⟨by nlinarith [hκlb1, hr3, hrpos], ?_, ?_, ?_⟩
  -- (1) the linearisation condition `4L ≤ κ·p`, i.e. `32·r·L ≤ κ`
  · rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ))]
    have hrlgr : (r : ℝ) * lg r ≤ 2 * (r : ℝ) ^ 2 := by nlinarith [hlgr2, hrpos]
    have hprod : (r : ℝ) * lg (lg w) ≤ (r : ℝ) * lg w * lg (lg w) := by
      nlinarith [mul_nonneg (mul_nonneg hrpos.le hlglgpos.le) (sub_nonneg.mpr hlgw.le)]
    have hp1 : 2816 * (r : ℝ) ≤ κ / 3 := by linarith
    have hp2 : 128 * (r : ℝ) * lg r ≤ κ / 3 := by linarith
    have hp3 : 96 * (r : ℝ) * lg (lg w) ≤ κ / 3 := by linarith
    calc 4 * (L : ℝ) * (8 * (r : ℝ)) = 32 * (r : ℝ) * (L : ℝ) := by ring
      _ ≤ 32 * (r : ℝ) * (88 + 4 * lg r + 3 * lg (lg w)) :=
          mul_le_mul_of_nonneg_left hLub (by positivity)
      _ = 2816 * (r : ℝ) + 128 * (r : ℝ) * lg r + 96 * (r : ℝ) * lg (lg w) := by ring
      _ ≤ κ / 3 + κ / 3 + κ / 3 := by linarith
      _ = κ := by ring
  -- (2) the budget `log(8r) ≤ κ·p/(32L²)`, i.e. `2048·r²·L² ≤ κ` after `log x ≤ x`
  · have h8r : (2 : ℝ) / (1 / (4 * (r : ℝ))) = 8 * (r : ℝ) := by
      field_simp
      norm_num
    rw [h8r, mul_one_div, div_div, le_div_iff₀ (by positivity)]
    have hlog : Real.log (8 * (r : ℝ)) ≤ 8 * (r : ℝ) :=
      le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
    have hq1 : 2048 * 23232 * (r : ℝ) ^ 2 ≤ κ / 3 := by linarith
    have hq2 : 2048 * 768 * (r : ℝ) ^ 3 ≤ κ / 3 := by linarith
    have hq3 : 2048 * 432 * (r : ℝ) ^ 2 * lg w ≤ κ / 3 := by
      have h1 : 3 * (r : ℝ) ^ 2 * lg w ≤ (r : ℝ) ^ 3 * lg w :=
        mul_le_mul_of_nonneg_right hr32 hlgw0.le
      linarith
    have hfin : 8 * (r : ℝ) * (8 * (r : ℝ) * (32 * (L : ℝ) ^ 2)) ≤ κ := by
      have h1 : 2048 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2
          ≤ 2048 * (r : ℝ) ^ 2 * (23232 + 768 * (r : ℝ) + 432 * (lg w)) :=
        mul_le_mul_of_nonneg_left hLsq (by positivity)
      calc 8 * (r : ℝ) * (8 * (r : ℝ) * (32 * (L : ℝ) ^ 2))
          = 2048 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 := by ring
        _ ≤ 2048 * (r : ℝ) ^ 2 * (23232 + 768 * (r : ℝ) + 432 * (lg w)) := h1
        _ = 2048 * 23232 * (r : ℝ) ^ 2 + 2048 * 768 * (r : ℝ) ^ 3
              + 2048 * 432 * (r : ℝ) ^ 2 * lg w := by ring
        _ ≤ κ / 3 + κ / 3 + κ / 3 := by linarith
        _ = κ := by ring
    calc Real.log (8 * (r : ℝ)) * (8 * (r : ℝ) * (32 * (L : ℝ) ^ 2))
        ≤ 8 * (r : ℝ) * (8 * (r : ℝ) * (32 * (L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
      _ ≤ κ := hfin
  -- (3) the bridge condition `2p·n ≤ m_bot`, i.e. `n ≤ 4r·m_bot`
  · have hn4r : 4 * (r : ℝ) ≤ (n : ℝ) := by linarith
    have hnrN : r ≤ n := by
      have : (r : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hm1 : 1 ≤ m := by
      rw [hm, Nat.one_le_div_iff (by omega : 0 < r)]
      exact hnrN
    have hmbot1 : 1 ≤ m_bot := by rw [hmbot]; omega
    have hmdiv : r * m + n % r = n := by rw [hm]; exact Nat.div_add_mod n r
    have hmod : n % r < r := Nat.mod_lt _ (by omega)
    have hnlt : n < r * m + r := by omega
    have hnR : (n : ℝ) < (r : ℝ) * (m : ℝ) + (r : ℝ) := by exact_mod_cast hnlt
    have h2mbot : m ≤ 2 * m_bot := by rw [hmbot]; omega
    have h2mbotR : (m : ℝ) ≤ 2 * (m_bot : ℝ) := by exact_mod_cast h2mbot
    have hmb1R : (1 : ℝ) ≤ (m_bot : ℝ) := by exact_mod_cast hmbot1
    have hrm : (r : ℝ) * (m : ℝ) ≤ (r : ℝ) * (2 * (m_bot : ℝ)) :=
      mul_le_mul_of_nonneg_left h2mbotR hrpos.le
    have hrmb : (r : ℝ) ≤ (r : ℝ) * (m_bot : ℝ) := le_mul_of_one_le_right hrpos.le hmb1R
    rw [show 2 * ((1 / (8 * (r : ℝ))) * (n : ℝ)) = (n : ℝ) / (4 * (r : ℝ)) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (r : ℝ))]
    nlinarith [hnR, hrm, hrmb, mul_nonneg hrpos.le (Nat.cast_nonneg (α := ℝ) m_bot)]

/-! ### The chase for the unconditional route

With the weight-class bottom the chase gets *simpler*, because a single hypothesis carries it:

  `hJ : 8192·r²·L²·(J+1) ≤ κ`.

`hS1` and `hS2` both follow from it (the second through `log(8r) ≤ 8r` again), and `hS3` is
unchanged. Note it no longer needs the `lg`-structure of `κ` at all — any `κ` clearing `hJ`
works. What `hJ` *costs* is `width_le_of_multiplicity_budget` below. -/

/-- **The chase for `iterate_le_janson_mass`.** At `p = 1/(8r)`, `εbot = 1/(4r)` and
`κs = κ/(4(J+1))`, the multiplicity budget `hJ` gives all four conditions. -/
theorem janson_mass_conditions {r L n m m_bot J : ℕ} {κ : ℝ} (hr : 3 ≤ r) (hL4 : 4 ≤ L)
    (hκn : κ ≤ (n : ℝ)) (hm : m = n / r) (hmbot : m_bot = m - m / 2)
    (hJ : 8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((J : ℝ) + 1) ≤ κ) :
    (1 : ℝ) ≤ κ / (4 * ((J : ℝ) + 1))
    ∧ 4 * (L : ℝ) ≤ (κ / (4 * ((J : ℝ) + 1))) * (1 / (8 * (r : ℝ)))
    ∧ Real.log (2 / (1 / (4 * (r : ℝ))))
        ≤ (κ / (4 * ((J : ℝ) + 1))) * (1 / (8 * (r : ℝ))) / (32 * (L : ℝ) ^ 2)
    ∧ 2 * ((1 / (8 * (r : ℝ))) * (n : ℝ)) ≤ (m_bot : ℝ) := by
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hL4R : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  -- `hJ` dwarfs everything: `8192·r²·L² ≥ 8192·9·16`
  have hr9 : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hL16 : (16 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hcoef : (1179648 : ℝ) ≤ 8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hr9 hL16 (by norm_num : (0:ℝ) ≤ 16) (by positivity : (0:ℝ) ≤ (r:ℝ)^2)]
  have hbig : 1179648 * ((J : ℝ) + 1) ≤ κ :=
    le_trans (mul_le_mul_of_nonneg_right hcoef hJ1.le) hJ
  have hκpos : (0 : ℝ) < κ := by nlinarith [hbig, hJ1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    linarith
  · rw [mul_one_div, div_div, le_div_iff₀ (by positivity)]
    -- `4L·(4(J+1)·8r) = 128·r·L·(J+1) ≤ κ`
    have h1 : 4 * (L : ℝ) * (4 * ((J : ℝ) + 1) * (8 * (r : ℝ)))
        = 128 * (r : ℝ) * (L : ℝ) * ((J : ℝ) + 1) := by ring
    rw [h1]
    nlinarith [hJ, hJ1, hr3, hL4R]
  · have h8r : (2 : ℝ) / (1 / (4 * (r : ℝ))) = 8 * (r : ℝ) := by
      field_simp
      norm_num
    rw [h8r, mul_one_div, div_div, div_div, le_div_iff₀ (by positivity)]
    have hlog : Real.log (8 * (r : ℝ)) ≤ 8 * (r : ℝ) :=
      le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
    have h1 : Real.log (8 * (r : ℝ)) * (4 * ((J : ℝ) + 1) * (8 * (r : ℝ)) * (32 * (L : ℝ) ^ 2))
        ≤ 8 * (r : ℝ) * (4 * ((J : ℝ) + 1) * (8 * (r : ℝ)) * (32 * (L : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    have h2 : 8 * (r : ℝ) * (4 * ((J : ℝ) + 1) * (8 * (r : ℝ)) * (32 * (L : ℝ) ^ 2))
        = 8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((J : ℝ) + 1) := by ring
    linarith [hJ, h1, h2 ▸ h1]
  · -- the bridge condition, exactly as before
    have hn4r : 4 * (r : ℝ) ≤ (n : ℝ) := by
      have hstep : 131072 * (r : ℝ) ^ 2 ≤ 8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((J : ℝ) + 1) := by
        have h2 : 131072 * (r : ℝ) ^ 2 = 8192 * (r : ℝ) ^ 2 * 16 * 1 := by ring
        rw [h2]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hL16 (by positivity)) (by linarith)
          (by norm_num) (by positivity)
      nlinarith [hstep, hr3, hJ, hκn]
    have hnrN : r ≤ n := by
      have : (r : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hm1 : 1 ≤ m := by
      rw [hm, Nat.one_le_div_iff (by omega : 0 < r)]
      exact hnrN
    have hmbot1 : 1 ≤ m_bot := by rw [hmbot]; omega
    have hmdiv : r * m + n % r = n := by rw [hm]; exact Nat.div_add_mod n r
    have hmod : n % r < r := Nat.mod_lt _ (by omega)
    have hnlt : n < r * m + r := by omega
    have hnR : (n : ℝ) < (r : ℝ) * (m : ℝ) + (r : ℝ) := by exact_mod_cast hnlt
    have h2mbot : m ≤ 2 * m_bot := by rw [hmbot]; omega
    have h2mbotR : (m : ℝ) ≤ 2 * (m_bot : ℝ) := by exact_mod_cast h2mbot
    have hmb1R : (1 : ℝ) ≤ (m_bot : ℝ) := by exact_mod_cast hmbot1
    have hrm : (r : ℝ) * (m : ℝ) ≤ (r : ℝ) * (2 * (m_bot : ℝ)) :=
      mul_le_mul_of_nonneg_left h2mbotR hrpos.le
    have hrmb : (r : ℝ) ≤ (r : ℝ) * (m_bot : ℝ) := le_mul_of_one_le_right hrpos.le hmb1R
    rw [show 2 * ((1 / (8 * (r : ℝ))) * (n : ℝ)) = (n : ℝ) / (4 * (r : ℝ)) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (r : ℝ))]
    nlinarith [hnR, hrm, hrmb, mul_nonneg hrpos.le (Nat.cast_nonneg (α := ℝ) m_bot)]

/-- **What the multiplicity budget costs.** `hJ` must be met with `2^J ≥ M`, and at the
instantiation `M = |𝓖| ≥ κ^{w'}`, so `J ≥ w'` already for `κ ≥ 2`: the budget caps the
*width*,

  `w' + 1 ≤ κ/(8192·r²·L²)`.

With `κ = 2^41·r³·lg w·lg lg w` and `L ≥ 4` that is a real but enormous ceiling
(`w' ≲ 10³·r·lg w·lg lg w`), so the route delivers the spread lemma for all widths below it —
and, since the cap grows only like `lg w·lg lg w`, not for arbitrary `w`. That is the residue
of the multiset formulation: the second moment pays nothing for multiplicities, Janson pays
`log₂` of them. -/
theorem width_le_of_multiplicity_budget {r L J w' : ℕ} {κ M : ℝ}
    (hκ2 : 2 ≤ κ) (hMw : κ ^ w' ≤ M) (hMJ : M ≤ 2 ^ J)
    (hJ : 8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((J : ℝ) + 1) ≤ κ)
    (hr : 3 ≤ r) (hL4 : 4 ≤ L) :
    (w' : ℝ) + 1 ≤ κ / (8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hL4R : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hpow : (2 : ℝ) ^ w' ≤ 2 ^ J := by
    calc (2 : ℝ) ^ w' ≤ κ ^ w' := pow_le_pow_left₀ (by norm_num) hκ2 w'
      _ ≤ M := hMw
      _ ≤ 2 ^ J := hMJ
  have hwJ : w' ≤ J := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) ^ J < 2 ^ w' := by
      exact pow_lt_pow_right₀ (by norm_num) hcon
    linarith
  have hwJR : (w' : ℝ) ≤ (J : ℝ) := by exact_mod_cast hwJ
  rw [le_div_iff₀ (by positivity)]
  calc ((w' : ℝ) + 1) * (8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2)
      ≤ ((J : ℝ) + 1) * (8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 8192 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((J : ℝ) + 1) := by ring
    _ ≤ κ := hJ

/-- **The chase, plugged in.** The three conditions really do discharge the bottom step at the
`spread_core_main` parameters: a `≤ v`-bounded system of width `v ≤ 2L` and mass above the
invariant, whose *support* is `κ`-spread, fails at budget `m ≥ m_bot` with fraction at most
`εbot = 1/(4r)` — the allowance `SpreadAssemble` runs the iteration with.

This is `iterate_le_janson_supp`'s bottom hypothesis at the real parameters, so what separates
this from a `log(1/β)` spread lemma is only `hinv`, the support-spreadness of the iteration's
residual systems. -/
theorem janson_bottom_at_params {r w L n m m_bot mb v : ℕ} {A₀ A : ℝ} {X : Finset α}
    {σ : Finset α → ℕ}
    (hr : 3 ≤ r) (hw : 2 ≤ w) (hL4 : 4 ≤ L)
    (hLub : (L : ℝ) ≤ 88 + 4 * lg r + 3 * lg (lg w))
    (hκn : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w) ≤ (n : ℝ))
    (hm : m = n / r) (hmbot : m_bot = m - m / 2) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀)
    (hinv : IsSpread ((2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)) (supp X σ))
    (hb : WBounded X v σ) (htot : A ≤ (wTotal X σ : ℝ))
    (hAinv : A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A)
    (hv : 1 ≤ v) (hvL : v ≤ 2 * L) (hmm : m_bot ≤ mb) (hmn : mb ≤ X.card)
    (hn₀ : X.card ≤ n) :
    (failCount X σ mb : ℝ) ≤ (1 / (4 * (r : ℝ))) * (X.card.choose mb : ℝ) := by
  obtain ⟨hκ1, hS1, hS2, hS3⟩ := janson_supp_conditions hr hw hL4 hLub hκn hm hmbot
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hr1 : (1 : ℝ) ≤ 8 * (r : ℝ) := by
    have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  exact janson_bottom_supp (L := L) (m_bot := m_bot) (n₀ := n) (by omega) hmb hA₀ hκ1
    (by positivity) (by rw [div_le_one (by positivity)]; exact hr1) (by positivity)
    hS1 hS2 hS3 hinv hb htot hAinv hv hvL hmm hmn hn₀

/-! ## Why the weight class is necessary: support-spreadness is false

The system below satisfies everything the iteration propagates — `≤ 2`-bounded, `κ`-spread in
the mass sense against `M = wTotal` — yet its support is a near-star. It is
`t` pairs `{0, i}` of weight `1` together with `k` singletons `{z}` of weight `t`:

* the *mass* is spread, because the star members weigh `1` each and the heavy ballast is
  spread over `k ≈ 2κ²` distinct singletons, so no link carries more than `M/κ^{|T|}`;
* the *count* is not: `t` of the `t + k` support members contain `0`, so the support is only
  `(1 + k/t)`-spread as a family, and `t` may be taken as large as one likes.

That is exactly the gap between mass and count that `weightClass` repairs: here the two weight
scales are `1` and `t`, the heaviest class is the ballast, and the ballast *is* spread. -/

section Counterexample

open Finset

/-- `t` pairs `{0, i}` — the star. -/
private def starFam (t : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 t).image fun i => ({0, i} : Finset ℕ)

/-- `k` singletons `{z}`, disjoint from the star's elements — the ballast. -/
private def ballastFam (t k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc (t + 1) (t + k)).image fun z => ({z} : Finset ℕ)

private def starGround (t k : ℕ) : Finset ℕ := insert 0 (Finset.Icc 1 (t + k))

/-- Star members weigh `1`, ballast members weigh `N`. -/
private noncomputable def starW (t k N : ℕ) : Finset ℕ → ℕ :=
  fun S => indW (starFam t) S + N * indW (ballastFam t k) S

private lemma card_starFam (t : ℕ) : (starFam t).card = t := by
  classical
  rw [starFam, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_Icc] at hi hj
    have heq : ({0, i} : Finset ℕ) = {0, j} := hij
    have h : i ∈ ({0, j} : Finset ℕ) := by rw [← heq]; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    omega

private lemma card_ballastFam (t k : ℕ) : (ballastFam t k).card = k := by
  classical
  rw [ballastFam, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i _ j _ hij
    have heq : ({i} : Finset ℕ) = {j} := hij
    have : i ∈ ({j} : Finset ℕ) := by rw [← heq]; simp
    simpa using this

private lemma starFam_card_two {t : ℕ} {S : Finset ℕ} (h : S ∈ starFam t) : S.card = 2 := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
  rw [Finset.mem_Icc] at hi
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

private lemma ballastFam_card_one {t k : ℕ} {S : Finset ℕ} (h : S ∈ ballastFam t k) :
    S.card = 1 := by
  classical
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp h
  exact Finset.card_singleton z

private lemma starFam_sub {t k : ℕ} : ∀ S ∈ starFam t, S ⊆ starGround t k := by
  classical
  intro S hS
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
  rw [Finset.mem_Icc] at hi
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [starGround, Finset.mem_insert, Finset.mem_Icc]
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨hi.1, by omega⟩

private lemma ballastFam_sub {t k : ℕ} : ∀ S ∈ ballastFam t k, S ⊆ starGround t k := by
  classical
  intro S hS
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hS
  rw [Finset.mem_Icc] at hz
  intro x hx
  rw [Finset.mem_singleton] at hx
  rw [starGround, Finset.mem_insert, Finset.mem_Icc]
  exact Or.inr ⟨by omega, by omega⟩

/-- The link mass of the star/ballast system, as a count plus `N` times a count. -/
private lemma wLink_starW (t k N : ℕ) (T : Finset ℕ) :
    wLink (starGround t k) (starW t k N) T
      = ((starFam t).filter fun S => T ⊆ S).card
        + N * ((ballastFam t k).filter fun S => T ⊆ S).card := by
  classical
  have h1 : wLink (starGround t k) (starW t k N) T
      = wLink (starGround t k) (indW (starFam t)) T
        + N * wLink (starGround t k) (indW (ballastFam t k)) T := by
    simp only [wLink, starW, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, wLink_indW starFam_sub, wLink_indW ballastFam_sub, card_link, card_link]

private lemma starW_ne_zero {t k N : ℕ} {S : Finset ℕ} (h : starW t k N S ≠ 0) :
    S ∈ starFam t ∨ S ∈ ballastFam t k := by
  classical
  by_contra hcon
  push Not at hcon
  rw [starW, indW, indW, if_neg hcon.1, if_neg hcon.2] at h
  simp at h

/-- **Mass-spreadness does not imply support-spreadness.** For every `κ ≥ 1` and every
`κs > 1` there is a `≤ 2`-bounded system, `κ`-spread against its own mass, whose support is
not `κs`-spread. Consequently the hypothesis `hinv` of `iterate_le_janson_supp` cannot be
derived from the iteration's invariants — the weight-class detour of
`failCount_le_of_janson_massSpread` is not an artefact of the proof. -/
theorem suppSpread_not_of_wLinkBounded (κ κs : ℝ) (hκ : 1 ≤ κ) (hκs : 1 < κs) :
    ∃ (X : Finset ℕ) (σ : Finset ℕ → ℕ),
      WBounded X 2 σ ∧ WLinkBounded X σ (wTotal X σ : ℝ) κ ∧ 0 < wTotal X σ ∧
      ¬ IsSpread κs (supp X σ) := by
  classical
  -- parameters: `k ≈ 2κ²` ballast singletons, `t` star pairs, ballast weight `N = t`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * κ ^ 2 ≤ (k : ℝ) := ⟨⌈2 * κ ^ 2⌉₊, Nat.le_ceil _⟩
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, 1 ≤ t ∧ (k : ℝ) < (t : ℝ) * (κs - 1) := by
    obtain ⟨t₀, ht₀⟩ := exists_nat_gt ((k : ℝ) / (κs - 1))
    refine ⟨t₀ + 1, by omega, ?_⟩
    have hpos : (0 : ℝ) < κs - 1 := by linarith
    rw [div_lt_iff₀ hpos] at ht₀
    have : (t₀ : ℝ) ≤ ((t₀ + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [this, hpos]
  refine ⟨starGround t k, starW t k t, ?_, ?_, ?_, ?_⟩
  · -- `≤ 2`-bounded
    intro S hS
    rcases starW_ne_zero hS with h | h
    · exact ⟨starFam_sub S h, le_of_eq (starFam_card_two h)⟩
    · exact ⟨ballastFam_sub S h, by rw [ballastFam_card_one h]; omega⟩
  · -- `κ`-spread in the mass sense, against `M = wTotal`
    intro T hT
    have hmass : (wTotal (starGround t k) (starW t k t) : ℝ) = (t : ℝ) + (k : ℝ) * (t : ℝ) := by
      have h := wLink_starW t k t (∅ : Finset ℕ)
      rw [wLink_empty] at h
      rw [h]
      push_cast
      rw [Finset.filter_true_of_mem fun _ _ => Finset.empty_subset _,
        Finset.filter_true_of_mem fun _ _ => Finset.empty_subset _, card_starFam,
        card_ballastFam]
      ring
    by_cases hz : wLink (starGround t k) (starW t k t) T = 0
    · rw [hz, Nat.cast_zero, zero_mul, hmass]
      positivity
    · -- a nonzero link forces `|T| ≤ 2`, so `κ^{|T|} ≤ κ²`
      have hTle : T.card ≤ 2 := by
        have hex : ∃ S ∈ (starGround t k).powerset.filter fun S => T ⊆ S,
            starW t k t S ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hz (Finset.sum_eq_zero hcon)
        obtain ⟨S, hS, hne⟩ := hex
        rw [Finset.mem_filter] at hS
        have hcard : S.card ≤ 2 := by
          rcases starW_ne_zero hne with h | h
          · exact le_of_eq (starFam_card_two h)
          · rw [ballastFam_card_one h]; omega
        exact le_trans (Finset.card_le_card hS.2) hcard
      have hpow : κ ^ T.card ≤ κ ^ 2 := pow_le_pow_right₀ hκ hTle
      -- the link is at most `t + t`: at most `t` star sets, at most one ballast singleton
      have hlink : (wLink (starGround t k) (starW t k t) T : ℝ) ≤ (t : ℝ) + (t : ℝ) := by
        rw [wLink_starW]
        have hs : ((starFam t).filter fun S => T ⊆ S).card ≤ t := by
          calc ((starFam t).filter fun S => T ⊆ S).card ≤ (starFam t).card :=
                Finset.card_filter_le _ _
            _ = t := card_starFam t
        have hb : ((ballastFam t k).filter fun S => T ⊆ S).card ≤ 1 := by
          refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_singleton T))
          intro S hS
          rw [Finset.mem_filter] at hS
          obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hS.1
          rw [Finset.mem_singleton]
          refine (Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hT, ?_⟩).symm
          intro x hx
          exact Finset.mem_singleton.mp (hS.2 hx)
        push_cast
        have : (((starFam t).filter fun S => T ⊆ S).card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hs
        have : ((((ballastFam t k).filter fun S => T ⊆ S).card : ℝ)) ≤ 1 := by exact_mod_cast hb
        nlinarith [Nat.cast_nonneg (α := ℝ) t]
      have hκ0 : (0 : ℝ) ≤ κ ^ T.card := by positivity
      have htR : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      have hlinkpos : (0 : ℝ) ≤ (wLink (starGround t k) (starW t k t) T : ℝ) :=
        Nat.cast_nonneg _
      calc (wLink (starGround t k) (starW t k t) T : ℝ) * κ ^ T.card
          ≤ ((t : ℝ) + (t : ℝ)) * κ ^ 2 := by
            refine mul_le_mul hlink hpow hκ0 (by linarith)
        _ ≤ (t : ℝ) + (k : ℝ) * (t : ℝ) := by nlinarith [hk, htR]
        _ = (wTotal (starGround t k) (starW t k t) : ℝ) := hmass.symm
  · -- positive mass: the star member `{0,1}` weighs `1`
    have hmem : ({0, 1} : Finset ℕ) ∈ starFam t := by
      refine Finset.mem_image.mpr ⟨1, ?_, rfl⟩
      rw [Finset.mem_Icc]
      omega
    have hnb : ({0, 1} : Finset ℕ) ∉ ballastFam t k := by
      intro hb
      have h1 := starFam_card_two hmem
      have h2 := ballastFam_card_one hb
      omega
    have hσ : starW t k t ({0, 1} : Finset ℕ) = 1 := by
      rw [starW, indW, indW, if_pos hmem, if_neg hnb]
      omega
    have hle : starW t k t ({0, 1} : Finset ℕ) ≤ wTotal (starGround t k) (starW t k t) :=
      Finset.single_le_sum (f := starW t k t) (fun _ _ => Nat.zero_le _)
        (Finset.mem_powerset.mpr (starFam_sub _ hmem))
    omega
  · -- the support is a near-star at `0`, so it is not `κs`-spread
    intro hsp
    have hsub : starFam t ⊆ supp (starGround t k) (starW t k t) := by
      intro S hS
      refine mem_supp.mpr ⟨starFam_sub S hS, ?_⟩
      have hnb : S ∉ ballastFam t k := by
        intro hb
        have h1 := starFam_card_two hS
        have h2 := ballastFam_card_one hb
        omega
      rw [starW, indW, indW, if_pos hS, if_neg hnb]
      omega
    have hsupsub : supp (starGround t k) (starW t k t) ⊆ starFam t ∪ ballastFam t k := by
      intro S hS
      rcases starW_ne_zero (mem_supp.mp hS).2 with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
    -- the star sits inside the link at `{0}`
    have hstar : starFam t ⊆
        (supp (starGround t k) (starW t k t)).filter fun S => ({0} : Finset ℕ) ⊆ S := by
      intro S hS
      rw [Finset.mem_filter]
      refine ⟨hsub hS, ?_⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      simp
    have hcount : (t : ℝ)
        ≤ (((supp (starGround t k) (starW t k t)).filter
            fun S => ({0} : Finset ℕ) ⊆ S).card : ℝ) := by
      have : t ≤ ((supp (starGround t k) (starW t k t)).filter
          fun S => ({0} : Finset ℕ) ⊆ S).card := by
        calc t = (starFam t).card := (card_starFam t).symm
          _ ≤ _ := Finset.card_le_card hstar
      exact_mod_cast this
    have hsize : ((supp (starGround t k) (starW t k t)).card : ℝ) ≤ (t : ℝ) + (k : ℝ) := by
      have : (supp (starGround t k) (starW t k t)).card ≤ t + k := by
        calc (supp (starGround t k) (starW t k t)).card ≤ (starFam t ∪ ballastFam t k).card :=
              Finset.card_le_card hsupsub
          _ ≤ (starFam t).card + (ballastFam t k).card := Finset.card_union_le _ _
          _ = t + k := by rw [card_starFam, card_ballastFam]
      exact_mod_cast this
    have h := hsp {0}
    rw [card_link, Finset.card_singleton, pow_one] at h
    have hκs0 : (0 : ℝ) < κs := by linarith
    nlinarith [hcount, hsize, h, ht2]

end Counterexample

end Sunflower

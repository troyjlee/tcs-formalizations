/-
# From the iteration's output to Definition 1.5, and the assembly at free `(a, b)`

The width-schedule iteration bounds `failCount X σ m₀` — a count of `m₀`-element subsets.
Definition 1.5 (`IsSatisfying`) asks about a `p`-biased set. `Sunflower.BridgeBack` supplies the
transfer and the lower tail; this file connects the two ends and then re-runs the assembly with
the sunflower parameters `a = b = 1/r` replaced by free `(a, b)`.

* `isSatisfying_of_failCount_tail` — a fixed-size failure bound plus *any* tail bound gives
  Definition 1.5. Instantiated at Chebyshev (`isSatisfying_of_failCount`) and at Chernoff
  (`isSatisfying_of_failCount_exp`); Theorem 1.9 uses the latter, which needs only
  `p·|X| ≳ log(1/b)` — supplied by `κ ≤ |X|` — and so removes the ground-set enlargement from
  the path.
* `pBiased_uncovered_ground_eq` / `isSatisfying_ground_iff` — the ground set is irrelevant:
  elements outside every member change no probability. (Kept: it is what moves the link's
  satisfying property onto `X \ Z` at the end, and it is what would make the Chebyshev route
  work if one preferred it.)
* `isSatisfying_of_isSpread_iterated` — **ALWZ's Theorem 2.5 in schedule form**: a `κ`-spread
  `w'`-uniform family, iterated on the Janson bottom with a schedule meeting the conditions, is
  `(a, b)`-satisfying.
* `exists_isRobustSunflower_of_satisfying` — **the paper's Lemma 2.4**: Theorem 2.5 for all
  widths up to `w` gives Theorem 1.9.

What is left for Theorem 1.9 is exactly one thing: choosing the schedule
(`L`, `s`, `t₀`, `m_bot`, `m`) in closed form as a function of `(w, a, b)`, the analogue of
`SpreadAssemble`'s chase.
-/
import Sunflower.JansonMass
import Sunflower.BridgeBack

open Finset

set_option maxHeartbeats 800000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-- **The iteration's output is Definition 1.5.** A fixed-size failure bound at budget `m₀`,
plus *any* bound `τ` on the lower tail, gives the satisfying property once `ε + τ < b`. -/
theorem isSatisfying_of_failCount_tail {X : Finset α} {σ : Finset α → ℕ} {v : ℕ}
    (hbd : WBounded X v σ) {p b ε τ : ℝ} {m₀ : ℕ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hm₀n : m₀ ≤ X.card)
    (hfail : (failCount X σ m₀ : ℝ) ≤ ε * (X.card.choose m₀ : ℝ))
    (htail : pBiased X p (fun R => R.card < m₀) ≤ τ)
    (hb : ε + τ < b) :
    IsSatisfying p b X (supp X σ) := by
  classical
  refine isSatisfying_of_uncovered_lt ?_
  have hCpos : (0 : ℝ) < (X.card.choose m₀ : ℝ) := by
    have : 0 < X.card.choose m₀ := Nat.choose_pos hm₀n
    exact_mod_cast this
  have hbridge := pBiased_le_fixedCount_add_tail (X := X)
    (P := fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) (decreasing_uncovered X σ) hp0.le hp1 hm₀n
  have hfc : fixedCount X (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) m₀ = failCount X σ m₀ :=
    (failCount_eq_fixedCount hbd m₀).symm
  rw [hfc] at hbridge
  have htail' := mul_le_mul_of_nonneg_right htail hCpos.le
  refine lt_of_mul_lt_mul_right ?_ hCpos.le
  calc pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) * (X.card.choose m₀ : ℝ)
      ≤ (failCount X σ m₀ : ℝ)
        + pBiased X p (fun R => R.card < m₀) * (X.card.choose m₀ : ℝ) := hbridge
    _ ≤ ε * (X.card.choose m₀ : ℝ) + τ * (X.card.choose m₀ : ℝ) := by linarith
    _ = (ε + τ) * (X.card.choose m₀ : ℝ) := by ring
    _ < b * (X.card.choose m₀ : ℝ) := mul_lt_mul_of_pos_right hb hCpos

/-- The Chebyshev instance: `τ = 4/(p·|X|)`, needing `2m₀ ≤ p·|X|`. -/
theorem isSatisfying_of_failCount {X : Finset α} {σ : Finset α → ℕ} {v : ℕ}
    (hbd : WBounded X v σ) {p b ε : ℝ} {m₀ : ℕ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hX : 0 < X.card) (hm₀n : m₀ ≤ X.card)
    (hm₀ : 2 * (m₀ : ℝ) ≤ p * X.card)
    (hfail : (failCount X σ m₀ : ℝ) ≤ ε * (X.card.choose m₀ : ℝ))
    (hb : ε + 4 / (p * (X.card : ℝ)) < b) :
    IsSatisfying p b X (supp X σ) :=
  isSatisfying_of_failCount_tail hbd hp0 hp1 hm₀n hfail
    (pBiased_card_lt_le_four_div X hp0 hp1 hm₀ hX) hb

/-- The Chernoff instance: `τ = exp(m₀·log 2 − p·|X|/2)`, needing nothing extra. This is the
one Theorem 1.9 uses — the tail is below `β` as soon as `p·|X| ≳ log(1/β)`, which spreadness
already supplies through `κ ≤ |X|`, so no ground-set enlargement is needed. -/
theorem isSatisfying_of_failCount_exp {X : Finset α} {σ : Finset α → ℕ} {v : ℕ}
    (hbd : WBounded X v σ) {p b ε : ℝ} {m₀ : ℕ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hm₀n : m₀ ≤ X.card)
    (hfail : (failCount X σ m₀ : ℝ) ≤ ε * (X.card.choose m₀ : ℝ))
    (hb : ε + Real.exp ((m₀ : ℝ) * Real.log 2 - p * (X.card : ℝ) / 2) < b) :
    IsSatisfying p b X (supp X σ) :=
  isSatisfying_of_failCount_tail hbd hp0 hp1 hm₀n hfail
    (pBiased_card_lt_le_exp X hp0.le hp1 m₀) hb

/-- **The ground set is irrelevant.** Elements outside every member of `𝓖` change no
probability: the uncovered event depends on `R` only through `R ∩ X`. This is what makes the
Chebyshev tail `4/(p|X|)` free — enlarge `X` until it is below `β`, then transfer back. -/
theorem pBiased_uncovered_ground_eq {X X' : Finset α} (hXX : X ⊆ X')
    {𝓖 : Finset (Finset α)} (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) (p : ℝ) :
    pBiased X' p (fun R => ∃ S ∈ 𝓖, S ⊆ R) = pBiased X p (fun R => ∃ S ∈ 𝓖, S ⊆ R) := by
  classical
  have hsub : X' \ X ⊆ X' := Finset.sdiff_subset
  have hQ : ∀ R : Finset α, (∃ S ∈ 𝓖, S ⊆ R) ↔ (∃ S ∈ 𝓖, S ⊆ R \ (X' \ X)) := by
    intro R
    constructor
    · rintro ⟨S, hS, hSR⟩
      refine ⟨S, hS, fun x hx => ?_⟩
      rw [Finset.mem_sdiff]
      refine ⟨hSR hx, ?_⟩
      rw [Finset.mem_sdiff]
      intro hcon
      exact hcon.2 (h𝓖 S hS hx)
    · rintro ⟨S, hS, hSR⟩
      exact ⟨S, hS, fun x hx => (Finset.mem_sdiff.mp (hSR hx)).1⟩
  have hmarg := pBiased_marginal_sdiff (X := X') (Y := X' \ X) hsub (p := p)
    (Q := fun R => ∃ S ∈ 𝓖, S ⊆ R) hQ
  rw [hmarg, Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hXX]

/-- Definition 1.5 does not see the ground set either. -/
theorem isSatisfying_ground_iff {X X' : Finset α} (hXX : X ⊆ X')
    {𝓖 : Finset (Finset α)} (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) {a b : ℝ} :
    IsSatisfying a b X' 𝓖 ↔ IsSatisfying a b X 𝓖 := by
  rw [IsSatisfying, IsSatisfying, pBiased_uncovered_ground_eq hXX h𝓖]

/-! ## The assembly with `(a, b)` free — ALWZ's Theorem 2.5

`SpreadAssemble`/`JansonAssemble` run the iteration at the sunflower parameters
`a = b = 1/r`, and stop at a failure count because that is what the disjointness extraction
consumes. Theorem 1.9 needs the *satisfying* property at free `(a, b)`, so the assembly is run
again here: same schedule, same round condition, same Janson bottom, but the conclusion is
converted through `isSatisfying_of_failCount_exp` instead of fed to `coveredTuples`.

Two parameters that coincided at `a = b = 1/r` must now be kept apart: the **inner** sampling
parameter `p` of the Janson bottom, which must satisfy `2p·n ≤ m` (the forward bridge), and the
**outer** parameter `a` of Definition 1.5, whose tail wants `m` small compared with `a·n`. Any
`p ≤ a/8`, `m ≈ a·n/4` separates them.

The schedule itself (`L`, `s`, `t₀`, `m_bot`, `m`) is left as a parameter with its conditions
explicit: choosing it in closed form for given `(w, a, b)` is the numeric chase, the analogue
of `SpreadAssemble`'s, and is the only thing between this and Theorem 1.9. -/

/-- **ALWZ Theorem 2.5, schedule form.** A `κ`-spread `w'`-uniform family, run through the
width-schedule iteration on the Janson bottom with a schedule meeting the conditions, is
`(a, b)`-satisfying.

`hK1` is the round condition, `hS1`–`hS3` the Janson bottom's, `hfuel` and `hbud` the
schedule's; `hb` is the final accounting `(εbot + ε) + tail < b`. -/
theorem isSatisfying_of_isSpread_iterated {𝓖 : Finset (Finset α)} {w' : ℕ}
    {κ a p b ε εbot : ℝ} {L s m_bot t₀ m : ℕ}
    (hu : IsUniform w' 𝓖) (hne : 𝓖.Nonempty) (hsp : IsSpread κ 𝓖) (hw' : 1 ≤ w')
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * ((𝓖.biUnion id).card : ℝ) / s) ^ v * (𝓖.card : ℝ) * 2 ^ (v + 1) * 2 ^ v
        ≤ ε * (𝓖.card : ℝ) * κ ^ (v - v / L))
    (hS1 : 4 * (L : ℝ) ≤ κ * p)
    (hS2 : Real.log (2 / εbot) ≤ κ * p / (64 * (L : ℝ) ^ 2))
    (hS3 : 2 * (p * ((𝓖.biUnion id).card : ℝ)) ≤ (m_bot : ℝ))
    (hfuel : (w' : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t₀)
    (hbud : s * t₀ + m_bot ≤ m) (hmn : m ≤ (𝓖.biUnion id).card)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : (εbot + ε)
        + Real.exp ((m : ℝ) * Real.log 2 - a * (((𝓖.biUnion id).card : ℕ) : ℝ) / 2) < b) :
    IsSatisfying a b (𝓖.biUnion id) 𝓖 := by
  classical
  set X := 𝓖.biUnion id with hX
  set σ := toWeight 𝓖 with hσ
  have h𝓖X : ∀ S ∈ 𝓖, S ⊆ X := fun S hS => Finset.subset_biUnion_of_mem id hS
  have hNpos : (0 : ℝ) < (𝓖.card : ℝ) := by
    have := Finset.card_pos.mpr hne
    exact_mod_cast this
  -- the support of the indicator system is the family itself
  have hsupp : supp X σ = 𝓖 := by
    have hind : σ = indW 𝓖 := rfl
    rw [hind]
    exact supp_indW h𝓖X
  -- the iteration, on the Janson bottom
  have hbd : WBounded X w' σ := by rw [hX, hσ]; exact toWeight_bounded hu
  have hlk : WLinkBounded X σ (𝓖.card : ℝ) κ := by rw [hX, hσ]; exact toWeight_linkBounded hsp
  have htot : (𝓖.card : ℝ) ≤ (wTotal X σ : ℝ) := by
    have heq : wTotal X σ = 𝓖.card := by rw [hX, hσ]; exact toWeight_total 𝓖
    rw [heq]
  have hAinv : (𝓖.card : ℝ) * (1 - (1 / 2 : ℝ) ^ (w' + 1)) ≤ (𝓖.card : ℝ) := by
    have h1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w' + 1) := by positivity
    nlinarith [hNpos]
  have hS2' : Real.log (2 / εbot)
      ≤ (𝓖.card : ℝ) * κ * p / (64 * (𝓖.card : ℝ) * (L : ℝ) ^ 2) := by
    refine le_trans hS2 (le_of_eq ?_)
    have hNne : (𝓖.card : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
  have hfail := iterate_le_janson_alwz (L := L) (s := s) (m_bot := m_bot) (n₀ := X.card)
    (A₀ := (𝓖.card : ℝ)) (M := (𝓖.card : ℝ)) (κ := κ) (p := p) (ε := ε) (εbot := εbot)
    hL hs hmb hNpos hNpos hκ hp hp1 hε hεb hK1 hS1 hS2' hS3
    t₀ X σ w' (𝓖.card : ℝ) m hbd hlk htot hAinv hfuel hw' hbud hmn (le_refl _)
  -- the failure fraction is at most `εbot + ε`
  have hfail' : (failCount X σ m : ℝ) ≤ (εbot + ε) * (X.card.choose m : ℝ) := by
    refine le_trans hfail (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    have h1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w' := by positivity
    nlinarith [hε]
  -- and Definition 1.5 follows
  have hres := isSatisfying_of_failCount_exp (X := X) (σ := σ) (v := w') (p := a) (b := b)
    (ε := εbot + ε) hbd ha ha1 hmn hfail' hb
  rwa [hsupp] at hres

/-! ## Theorem 1.9 from Theorem 2.5 — the paper's Lemma 2.4 -/

/-- **ALWZ Lemma 2.4 / Theorem 1.9, modulo Theorem 2.5.** If every `κ`-spread uniform family of
width at most `w` is `(a,b)`-satisfying, then every `w`-uniform family of size at least `κ^w`
contains an `(a,b)`-robust sunflower.

The dichotomy is `exists_spread_link`: either the family is spread — in which case it is
satisfying, hence robust — or it has a popular core `Z`, and the link there is spread with
strictly smaller width. `isRobustSunflower_above_spread_core` packages the link's satisfying
property as a robust sunflower `{S ∈ 𝓕 : Z ⊆ S}` sitting inside `𝓕`, and
`isSatisfying_ground_iff` moves the ground set from the link's own union to `X \ Z`.

With this, the only thing between the development and Theorem 1.9 is `hsat` in closed form:
`isSatisfying_of_isSpread_iterated` supplies it for any schedule meeting its conditions, so what
remains is choosing that schedule as an explicit function of `(w, a, b)`. -/
theorem exists_isRobustSunflower_of_satisfying {a b κ : ℝ} {w : ℕ} {X : Finset α}
    {𝓕 : Finset (Finset α)} (hκ : 1 < κ) (hw : 1 ≤ w) (hu : IsUniform w 𝓕)
    (hsub : ∀ S ∈ 𝓕, S ⊆ X) (hcard : κ ^ w ≤ (𝓕.card : ℝ))
    (hsat : ∀ {𝓖 : Finset (Finset α)} {w' : ℕ}, IsUniform w' 𝓖 → 𝓖.Nonempty → IsSpread κ 𝓖 →
      1 ≤ w' → w' ≤ w → IsSatisfying a b (𝓖.biUnion id) 𝓖) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  classical
  have hκ0 : (0 : ℝ) < κ := lt_trans one_pos hκ
  obtain ⟨Z, hZlt, hZsp, hZsize⟩ := exists_spread_link hκ.le hw hu hcard
  -- the link is nonempty
  have hlinkne : (link 𝓕 Z).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h
    have h0 : (link 𝓕 Z).card = 0 := by omega
    rw [h0] at hZsize
    simp only [Nat.cast_zero, zero_mul] at hZsize
    exact absurd hZsize (not_le.mpr (pow_pos hκ0 w))
  -- `Z` itself is not a member: it is too small
  have hZnot : Z ∉ 𝓕 := by
    intro h
    have := hu h
    omega
  -- the link is `(w − |Z|)`-uniform, of width at least `1`
  have hlu : IsUniform (w - Z.card) (link 𝓕 Z) := hu.link Z
  have hw' : 1 ≤ w - Z.card := by omega
  -- Theorem 2.5 on the link, then move the ground set to `X \ Z`
  have hsatlink := hsat hlu hlinkne hZsp hw' (by omega)
  have hground : (link 𝓕 Z).biUnion id ⊆ X \ Z := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨P, hP, hxP⟩ := hx
    rw [mem_link] at hP
    obtain ⟨S, hS, hZS, rfl⟩ := hP
    simp only [id] at hxP
    rw [Finset.mem_sdiff] at hxP ⊢
    exact ⟨hsub S hS hxP.1, hxP.2⟩
  have hmem : ∀ S ∈ link 𝓕 Z, S ⊆ (link 𝓕 Z).biUnion id :=
    fun S hS => Finset.subset_biUnion_of_mem id hS
  have hsat' : IsSatisfying a b (X \ Z) (link 𝓕 Z) :=
    (isSatisfying_ground_iff hground hmem).mpr hsatlink
  exact ⟨𝓕.filter fun S => Z ⊆ S, Finset.filter_subset _ _,
    isRobustSunflower_above_spread_core hκ hZnot hlinkne hZsp hsat'⟩

end Sunflower

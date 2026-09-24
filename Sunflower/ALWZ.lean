/-
# The Alweiss–Lovett–Wu–Zhang bound

The improved sunflower bound: for `r ≥ 3`, any `w`-uniform family of size at least
`(C r³ log w log log w)^w` contains an `r`-sunflower.

**On the base of the logarithm.** Under a literal base-2 reading of the pre-v3 statement,
`log log 2 = 0`, so the required size at `w = 2` is `0` and the theorem asserts that every
nonempty family of 2-element sets contains an `r`-sunflower. ArXiv v3 (31 Aug 2021) adds:

> "We will implicitly assume throughout the paper that `log log w > 0`. Formally, to handle
> the case of `w = 2`, we interpret `log` as logarithm in base `1.9`."

We adopt that convention as `Sunflower.lg`, and *prove* below that it gives the required
positivity (`lg_lg_two_pos`) while the base-2 nested logarithm is zero
(`logb_two_logb_two_two`). The later divisions and inequalities explicitly consume the
corresponding positivity or nonzeroness facts.

See `docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md`.
-/
import Sunflower.Spread
import Sunflower.Padding
import Sunflower.Lg
import Sunflower.SpreadAssemble
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- The ALWZ size bound `(C · r³ · lg w · lg (lg w))^w`. -/
noncomputable def alwzBound (C : ℝ) (r w : ℕ) : ℝ :=
  (C * r ^ 3 * lg w * lg (lg w)) ^ w

/-- **The spread lemma** — the probabilistic core of ALWZ (their §2, refined by Rao's
"Coding for sunflowers" encoding argument): a `(C r³ lg w lg lg w)`-spread family of
nonempty sets of size at most `w` contains `r` pairwise disjoint members.

**Fully proved**, with the explicit constant `C = 2^41`, by
`Sunflower.SpreadCore.spread_core_main` — the encoding argument, the reduction
rounds, the heaviest-class second moment, the width-schedule iteration, and the
disjointness extraction, assembled in `Sunflower.SpreadAssemble`. The nonemptiness hypothesis is necessary: `𝓖 = ∅` is
`R`-spread for every `R` and contains nothing. Uniformity at some `w' ≥ 1` keeps `∅`
out of `𝓖` (a family containing `∅` is never `R`-spread for `R > 1` unless it is
`{∅}`, which again contains no `r ≥ 2` disjoint distinct members). -/
theorem spread_lemma : ∃ C : ℝ, 0 < C ∧ ∀ (r w w' : ℕ), 3 ≤ r → 2 ≤ w → 1 ≤ w' →
    w' ≤ w → ∀ {𝓖 : Finset (Finset α)}, IsUniform w' 𝓖 → 𝓖.Nonempty →
    IsSpread (C * r ^ 3 * lg w * lg (lg w)) 𝓖 →
    ∃ 𝒟 ⊆ 𝓖, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  refine ⟨2^41, by norm_num, ?_⟩
  intro r w w' hr hw hw' hw'w 𝓖 hu hne hsp
  exact SpreadCore.spread_core_main r w w' hr hw hw' hw'w hu hne hsp

/-- **The reduction from the spread lemma to the sunflower bound**, abstracted over the spread
lemma it consumes. Pick a core `Z` (`|Z| < w`) whose link is `κ`-spread for
`κ = C r³ lg w lg lg w` (`Sunflower.exists_spread_link`), extract `r` pairwise disjoint petals
there, and reattach `Z`.

Stating it this way lets the *same* reduction serve both routes to the spread lemma: the
second-moment one (`SpreadCore.spread_core_main`, giving `alwz` below) and the Janson one
(`spread_core_janson`, giving `JansonALWZ.alwz_janson`). -/
theorem alwz_of_spread_lemma {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hspread : ∀ (r w w' : ℕ), 3 ≤ r → 2 ≤ w → 1 ≤ w' → w' ≤ w →
      ∀ {𝓖 : Finset (Finset α)}, IsUniform w' 𝓖 → 𝓖.Nonempty →
        IsSpread (C₀ * (r : ℝ) ^ 3 * lg w * lg (lg w)) 𝓖 →
        ∃ 𝒟 ⊆ 𝓖, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsUniform w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) →
    HasSunflower r 𝓕 := by
  refine ⟨max C₀ (1 / lg (lg 2)), lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro r w hr hw 𝓕 hu hcard
  set C : ℝ := max C₀ (1 / lg (lg 2)) with hCdef
  -- positivity and monotonicity facts about the factors of `κ`
  have hw2 : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have ha : (0 : ℝ) < lg (lg 2) := lg_lg_two_pos
  have hCa : 1 / lg (lg 2) ≤ C := le_max_right _ _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by positivity) hCa
  have hlgw : (1 : ℝ) < lg w := one_lt_lg hw2
  have hlglgw : lg (lg 2) ≤ lg (lg w) := lg_lg_le_lg_lg hw2
  have hlglgw0 : (0 : ℝ) < lg (lg w) := lt_of_lt_of_le ha hlglgw
  have hr3 : (27 : ℝ) ≤ (r : ℝ) ^ 3 := by
    have h3r : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h9 : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    nlinarith
  set κ : ℝ := C * (r : ℝ) ^ 3 * lg w * lg (lg w) with hκdef
  -- `κ ≥ 1`, thanks to `C ≥ 1 / lg (lg 2)`
  have hκ1 : 1 ≤ κ := by
    have h1 : 1 ≤ C * lg (lg 2) := by
      have h := mul_le_mul_of_nonneg_right hCa ha.le
      rwa [one_div_mul_cancel ha.ne'] at h
    have h2 : 1 ≤ C * lg (lg w) :=
      h1.trans (mul_le_mul_of_nonneg_left hlglgw hCpos.le)
    have h3 : 1 ≤ (r : ℝ) ^ 3 * lg w := by nlinarith
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (C * lg (lg w)) * ((r : ℝ) ^ 3 * lg w) :=
          mul_le_mul h2 h3 one_pos.le (le_trans one_pos.le h2)
      _ = κ := by rw [hκdef]; ring
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le one_pos hκ1
  -- the hypothesis is exactly `κ^w ≤ |𝓕|`
  have hbound : κ ^ w ≤ (𝓕.card : ℝ) := by
    have hunf : alwzBound C r w = κ ^ w := by unfold alwzBound; rw [hκdef]
    rwa [hunf] at hcard
  -- the reduction: a `κ`-spread link on a core of size `< w`
  obtain ⟨Z, hZlt, hZspread, hZsize⟩ :=
    exists_spread_link hκ1 (by omega : 1 ≤ w) hu hbound
  have hlinkne : (link 𝓕 Z).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h
    have h0 : (link 𝓕 Z).card = 0 := by omega
    rw [h0] at hZsize
    simp only [Nat.cast_zero, zero_mul] at hZsize
    exact absurd hZsize (not_le.mpr (pow_pos hκ0 w))
  -- weaken `κ`-spreadness to the exact form the spread lemma consumes
  have hκ₀κ : C₀ * (r : ℝ) ^ 3 * lg w * lg (lg w) ≤ κ := by
    rw [hκdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      (le_of_lt (lt_trans one_pos hlgw))) hlglgw0.le
  have hspread₀ : IsSpread (C₀ * (r : ℝ) ^ 3 * lg w * lg (lg w)) (link 𝓕 Z) :=
    hZspread.mono
      (mul_nonneg (mul_nonneg (mul_nonneg hC₀.le (by positivity))
        (le_of_lt (lt_trans one_pos hlgw))) hlglgw0.le) hκ₀κ
  -- extract `r` disjoint petals and reattach the core
  obtain ⟨𝒟, h𝒟sub, h𝒟card, h𝒟pd⟩ :=
    hspread r w (w - Z.card) hr hw (by omega) (Nat.sub_le _ _) (hu.link Z)
      hlinkne hspread₀
  exact hasSunflower_of_pairwiseDisjoint_link h𝒟sub h𝒟card h𝒟pd

/-- **Alweiss–Lovett–Wu–Zhang** (STOC 2020; *Annals of Mathematics* 194 (2021) 795–815).

For some absolute constant `C`, every `w`-uniform family of size at least
`(C r³ lg w · lg lg w)^w` contains an `r`-sunflower.

Stated with `Sunflower.lg` (base 1.9) per the paper's own v3 convention, so that it is true
at `w = 2` as well; see the module docstring.

Proved from `spread_lemma` via the reduction `Sunflower.exists_spread_link`: pick a core
`Z` (`|Z| < w`) whose link is `κ`-spread for `κ = C r³ lg w lg lg w`, extract `r` pairwise
disjoint petals there, and reattach `Z`. The constant is `max C₀ (1 / lg (lg 2))` where
`C₀` is the spread lemma's constant — the second argument guarantees `κ ≥ 1`, and it is
finite precisely because `lg (lg 2) > 0` (`lg_lg_two_pos`), i.e. precisely because of the
base-1.9 convention. -/
theorem alwz : ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsUniform w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) →
    HasSunflower r 𝓕 := by
  obtain ⟨C₀, hC₀, hspread⟩ := spread_lemma (α := α)
  exact alwz_of_spread_lemma hC₀ hspread

/-- **Alweiss–Lovett–Wu–Zhang, Theorem 1.4 as stated in the paper.**

For some absolute constant `C`, every **`w`-set system** — every member of cardinality *at
most* `w`, not necessarily exactly `w` — of size at least `(C r³ lg w · lg lg w)^w` contains
an `r`-sunflower.

This is the published hypothesis, unchanged across arXiv v1–v3: "we call `F` a `w`-set
system if each set in `F` has size at most `w`". Uniformity is a device internal to the
proof — it is the *robust*-sunflower theorem (their 1.9) that v2 restated for `w`-uniform
systems — and the paper bridges the two in §1 by padding each short set with `w - |S|`
dummies, "so that no dummy element appears in more than one set".

`alwz` above proves the uniform version, which is what §2 actually establishes. This wrapper
restores the paper's statement by carrying out that padding (`Sunflower.pad`,
`Sunflower.hasSunflower_of_bounded`): apply `alwz` in the enlarged universe `Padded α`, then
pull the sunflower back along `Sunflower.unpad`.

The reduction is free and exact: `card_padFamily` says padding changes the number of members
not at all, so the constant `C` and the bound `alwzBound C r w` are the *same* as in the
uniform statement — nothing is lost by stating the theorem in the paper's generality.
Privacy of the dummies makes the correspondence faithful in both directions
(`hasSunflower_padFamily_iff`).

This §1 padding is not the weighted padding discussed in formalization note A3
(`docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md`). This particular proof chain handles the
weighted uniformity step via the heaviest size class (`SpreadBottom.bottom_le`); the
robust-sunflower endpoint later formalizes the source's weighted padding in `DummyPad` and
`PadBottom`. -/
theorem alwz_bounded_of_alwz {C : ℝ} (hC : 0 < C)
    (halwz : ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w → ∀ {𝓕 : Finset (Finset (Padded α))},
      IsUniform w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) → HasSunflower r 𝓕) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsBounded w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) →
    HasSunflower r 𝓕 := by
  refine ⟨C, hC, ?_⟩
  intro r w hr hw 𝓕 hb hcard
  exact hasSunflower_of_bounded (P := fun n => alwzBound C r w ≤ (n : ℝ))
    (fun hu hc => halwz r w hr hw hu hc) hb hcard

/-- The paper's `w`-set-system statement, from the uniform one. -/
theorem alwz_bounded : ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsBounded w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) →
    HasSunflower r 𝓕 := by
  obtain ⟨C, hC, halwz⟩ := alwz (α := Padded α)
  exact alwz_bounded_of_alwz hC halwz

end Sunflower

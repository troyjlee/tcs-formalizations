/-
# The width-schedule iteration with the Janson bottom

`SpreadIterate.iterate_le_of_bottom` is the width-schedule iteration abstracted over its bottom
step: it consumes the bottom only through the conclusion

  `failCount X σ m ≤ εbot · C(|X|, m)`   for `≤ v`-bounded systems with `v ≤ 2L`.

`SpreadIterate.iterate_le` instantiates it with the second-moment bottom (`iterate_bottom`,
whose κ-conditions are `hK2`, `hK3`). This file instantiates the *same* theorem with the Janson
bottom `JansonBottom.failCount_le_of_janson_bounded`, whose κ-conditions are `hJ1`–`hJ4` below.

The two routes differ only in what the bottom allowance `εbot` costs:

* second moment (`hK2`): `εbot` enters as `1/εbot`, i.e. `κ ≳ L²·n₀·M/(εbot·A₀·m_bot)`;
* Janson (`hJ3`):        `εbot` enters as `log(1/εbot)`, i.e. `κ² ≳ L²·M²·log(2/εbot)/(A₀·p)`.

That is the whole point of the Janson route (formalization note B1), and it is why `Real.log` appears
here where `SpreadAssemble` uses only `Nat.log`.

## The parameter `p`

The Janson bottom is a statement about a `p`-biased random set, transported to a uniform
`m`-subset by `JansonCover`'s bridge, so it carries a sampling parameter `p` that the
second-moment bottom does not have. It is fixed once for the whole iteration, and the bridge
costs the condition `2p·n₀ ≤ m_bot` (`hJ4`): the biased set must be smaller than the budget.

## What remains — and a warning

The constant chase (choosing `L`, `s`, `m_bot`, `p`, `κ` so that `hK1` and `hJ1`–`hJ4` hold at
the `spread_lemma` instantiation) is `Sunflower.JansonChase`, and its first result is that
**`hJ3` is unsatisfiable there**: with `A₀ = M = |𝓖|` it asks for `|𝓖| ≲ κ²p/L²`, against
`|𝓖| ≥ κ^{w'}` (`janson_mass_budget_infeasible`). So this file's `iterate_le_janson` is
correct but not usable at the intended instantiation; the usable form is
`JansonChase.iterate_le_janson_supp`, which runs on support-spreadness instead of mass-
spreadness. The two files are kept apart deliberately: this one records that the iteration
accepts a Janson bottom at all — what the uniformity obstacle (formalization note A3) previously
blocked — and that one records what the bottom must be *about*.
-/
import Sunflower.SpreadIterate
import Sunflower.JansonBottom

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-- **The Janson bottom regime.** The analogue of `SpreadCore.iterate_bottom`: at width
`v ≤ 2L` the Janson bottom `failCount_le_of_janson_bounded` applies with the class-reduced
budget, and the four κ-conditions

* `hJ1 : 4L ≤ κ·p`                       — the linearisation condition `v/(κp) ≤ 1/2`;
* `hJ2 : κ·p ≤ 4M·p^{2L}`                — the `q ≤ 1` check of the Janson optimisation;
* `hJ3 : log(2/εbot) ≤ A₀κ²p/(64M²L²)`   — the κ-budget, in `log(1/εbot)` form;
* `hJ4 : 2p·n₀ ≤ m_bot`                  — the `p`-biased/fixed-size bridge condition

are exactly what it takes to make them uniform in `v ∈ [1, 2L]`, `m ≥ m_bot` and
`|X| ≤ n₀`. -/
theorem janson_bottom {L m_bot n₀ : ℕ} {A₀ M κ p εbot : ℝ} {X : Finset α}
    {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ}
    (hL : 2 ≤ L) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hεb : 0 < εbot)
    (hJ1 : 4 * (L : ℝ) ≤ κ * p)
    (hJ2 : κ * p ≤ 4 * M * p ^ (2 * L))
    (hJ3 : Real.log (2 / εbot) ≤ A₀ * κ ^ 2 * p / (64 * M ^ 2 * (L : ℝ) ^ 2))
    (hJ4 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ))
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (htot : A ≤ (wTotal X σ : ℝ)) (hAinv : A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A)
    (hv : 1 ≤ v) (hvL : v ≤ 2 * L) (hmm : m_bot ≤ m) (hmn : m ≤ X.card)
    (hn₀ : X.card ≤ n₀) :
    (failCount X σ m : ℝ) ≤ εbot * (X.card.choose m : ℝ) := by
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le one_pos hκ
  have hκp : (0 : ℝ) < κ * p := mul_pos hκ0 hp
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hvL' : (v : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hvL
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  -- the mass never drops below `A₀/2` (as in `iterate_bottom`)
  have hhalf : (1 / 2 : ℝ) ^ (v + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (v + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hA2 : A₀ / 2 ≤ A := by
    calc A₀ / 2 = A₀ * (1 - 1 / 2) := by ring
      _ ≤ A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) := mul_le_mul_of_nonneg_left (by linarith) hA₀.le
      _ ≤ A := hAinv
  have hA : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) hA2
  -- `hJ1` gives the linearisation condition at every width `v ≤ 2L`
  have hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2 := by
    have h1 : (v : ℝ) * (κ * p)⁻¹ ≤ 2 * (L : ℝ) * (κ * p)⁻¹ :=
      mul_le_mul_of_nonneg_right hvL' (by positivity)
    have h2 : 2 * (L : ℝ) * (κ * p)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp]
      linarith
    linarith
  -- `hJ2` gives the `q ≤ 1` check at every width `v ≤ 2L`, since `p ≤ 1`
  have hq : κ * p ≤ 4 * M * p ^ v := by
    refine le_trans hJ2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_of_le_one hp.le hp1 hvL
  -- `hJ3` gives the budget at every width `v ≤ 2L`, since `A ≥ A₀/2`
  have hbudget : Real.log (2 / εbot) ≤ A * κ ^ 2 * p / (8 * M ^ 2 * (v : ℝ) ^ 2) := by
    refine le_trans hJ3 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : A₀ ≤ 2 * A := by linarith
    have h2 : (v : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith [hvR, hvL']
    calc A₀ * κ ^ 2 * p * (8 * M ^ 2 * (v : ℝ) ^ 2)
        = (κ ^ 2 * p * (8 * M ^ 2)) * (A₀ * (v : ℝ) ^ 2) := by ring
      _ ≤ (κ ^ 2 * p * (8 * M ^ 2)) * ((2 * A) * (4 * (L : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
      _ = A * κ ^ 2 * p * (64 * M ^ 2 * (L : ℝ) ^ 2) := by ring
  -- `hJ4` gives the bridge condition, since `|X| ≤ n₀ ≤ m_bot/(2p)` and `m ≥ m_bot`
  have hsmall : 2 * (p * (X.card : ℝ)) ≤ (m : ℝ) := by
    have h1 : (X.card : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h2 : (m_bot : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmm
    have h3 : p * (X.card : ℝ) ≤ p * (n₀ : ℝ) := mul_le_mul_of_nonneg_left h1 hp.le
    linarith
  exact failCount_le_of_janson_bounded hb hl hκ hp hp1 hM hv hvt hq hA htot hεb hbudget
    (by omega) hmn hsmall

/-- **The width-schedule iteration with the Janson bottom.** `SpreadIterate.iterate_le` with
`hK2`, `hK3` replaced by `hJ1`–`hJ4`: identical conclusion, but the bottom allowance `εbot`
now costs `log(1/εbot)` in the κ-budget instead of `1/εbot`.

The conclusion is verbatim `iterate_le`'s, and the remaining differences in the hypotheses are
the sampling parameter `p` and the strictness upgrades `0 < M`, `0 < εbot` that Janson needs.
That the iteration itself is untouched is the point of `iterate_le_of_bottom`. -/
theorem iterate_le_janson {L s m_bot n₀ : ℕ} {A₀ M κ p ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hJ1 : 4 * (L : ℝ) ≤ κ * p)
    (hJ2 : κ * p ≤ 4 * M * p ^ (2 * L))
    (hJ3 : Real.log (2 / εbot) ≤ A₀ * κ ^ 2 * p / (64 * M ^ 2 * (L : ℝ) ^ 2))
    (hJ4 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ)) :
    ∀ (t : ℕ) (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) (A : ℝ) (m : ℕ),
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      (v : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t →
      1 ≤ v → s * t + m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤
        (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) :=
  iterate_le_of_bottom hL hs hmb hA₀ hM.le hκ hε hεb.le hK1
    (fun {_X _σ _v _m _A} hb hl htot hAinv hv hvL hmm hmn hn₀ =>
      janson_bottom hL hmb hA₀ hM hκ hp hp1 hεb hJ1 hJ2 hJ3 hJ4
        hb hl htot hAinv hv hvL hmm hmn hn₀)

end Sunflower

/-
# Field widths, and Rao's constant chase

Two things remain between `RaoJoin.contraction_of_lengths` and the contraction itself.

**The widths.** Every "index into a set of known size" field is `⌈log₂ N⌉` bits, where `N` is
whatever the counting lemmas bound that set by. `card_le_two_pow_ceil_logb` says that width
suffices, and `ceil_logb_le` says it costs at most `log₂ N + 1` — Rao's "+1"s.

**The constants.** Adding up the fields, the two branches cost

  case 1:  `log₂(R^w·C) + a·(log₂ρ + 3) − b·log₂κ + 3`
  case 2:  `log₂(R^w·C) + a·(3 − log₂ρ) + 2`

where `a = |χ(S,U)|`, `b = |χ(S,W)|`, `C = C(n−u,v)` and `κ = R·v/(n−u)`. Rao closes by
choosing `ρ` and `κ` so that both fit the common shape `log₂N + A·a − B·b` with `A/B ≤ 2/3`:

> Set `ρ` to be large enough so that `(log ρ + c)/(2 log ρ + c − c′) ≤ 2/3`, and `κ` large
> enough so that `log(κ/2) ≥ 2 log ρ + c − c′`.

`branch1_fits`/`branch2_fits`/`ratio_ok` below are that, with the constants made explicit:
`A = log₂ρ + 7`, `B = log₂κ`, and `log₂ρ = 21`, `log₂κ = 42` do it — `A/B = 28/42 = 2/3`
exactly. Case 2 has no `−b` term of its own, so it is brought into the common shape using
`b ≤ a` (`RaoChi.chi_card_mono`), exactly as Rao does by "adding
`(2 log ρ + c − c′)(|χ(X,U)| − |χ(X,W)|)`, which is non-negative".

The `+3` and `+2` are absorbed into `a·(…)` using `a ≥ 1`, which is where the `a = 0`
dichotomy of `RaoJoin.chi_pos_or_all_covered` is needed.
-/
import Sunflower.RaoJoin

open Finset

namespace Sunflower

namespace Rao

/-! ## Widths from counting bounds -/

/-- A set of size at most `N` is indexed by `⌈log₂ N⌉` bits. -/
theorem card_le_two_pow_ceil_logb {n : ℕ} {N : ℝ} (hN : 0 < N) (h : (n : ℝ) ≤ N) :
    n ≤ 2 ^ ⌈Real.logb 2 N⌉₊ := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have h1 : N = (2 : ℝ) ^ (Real.logb 2 N) := (Real.rpow_logb (by norm_num) (by norm_num) hN).symm
  have h2 : (2 : ℝ) ^ (Real.logb 2 N) ≤ (2 : ℝ) ^ ((⌈Real.logb 2 N⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_left_iff hb |>.mpr (Nat.le_ceil _)
  have h3 : (2 : ℝ) ^ ((⌈Real.logb 2 N⌉₊ : ℕ) : ℝ) = ((2 ^ ⌈Real.logb 2 N⌉₊ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  have h4 : (n : ℝ) ≤ ((2 ^ ⌈Real.logb 2 N⌉₊ : ℕ) : ℝ) := by
    rw [← h3]
    exact le_trans h (le_trans (le_of_eq h1) h2)
  exact_mod_cast h4

/-- …and that width costs at most `log₂ N + 1` bits: Rao's "+1". -/
theorem ceil_logb_le {N : ℝ} (hN : 1 ≤ N) :
    ((⌈Real.logb 2 N⌉₊ : ℕ) : ℝ) ≤ Real.logb 2 N + 1 := by
  have h0 : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN
  exact le_of_lt (Nat.ceil_lt_add_one h0)

/-! ## The constant chase

Everything below is arithmetic in the logarithms: `LN = log₂(R^w·C)`, `Lρ = log₂ρ`,
`Lκ = log₂κ`. -/

/-- **Case 1 fits the common shape.** Its cost `LN + a(Lρ+3) − b·Lκ + 3`, plus the tag bit, is
at most `LN + a(Lρ+7) − b·Lκ` once `a ≥ 1`. -/
theorem branch1_fits {LN Lρ Lκ len : ℝ} {a b : ℕ} (ha : 1 ≤ a)
    (h : len ≤ 1 + (LN + (a : ℝ) * (Lρ + 3) - (b : ℝ) * Lκ + 3)) :
    len ≤ LN + (a : ℝ) * (Lρ + 7) - (b : ℝ) * Lκ := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  nlinarith [h, ha1]

/-- **Case 2 fits the common shape.** It has no `−b` term of its own; `b ≤ a` supplies one, and
`Lκ ≤ 2Lρ` is what makes the exchange affordable. This is Rao's "adding
`(2 log ρ + c − c′)(|χ(X,U)| − |χ(X,W)|)`, which is non-negative for `ρ` chosen large enough". -/
theorem branch2_fits {LN Lρ Lκ len : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ a)
    (hκ0 : 0 ≤ Lκ) (hκ2ρ : Lκ ≤ 2 * Lρ)
    (h : len ≤ 1 + (LN + (a : ℝ) * (3 - Lρ) + 2)) :
    len ≤ LN + (a : ℝ) * (Lρ + 7) - (b : ℝ) * Lκ := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hba : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hb
  -- `−b·Lκ ≥ −a·Lκ`, and then the inequality is linear in `a`
  have hswap : -((b : ℝ) * Lκ) ≥ -((a : ℝ) * Lκ) := by nlinarith [hba, hκ0]
  nlinarith [h, ha1, hswap, hκ2ρ, hκ0]

/-- **The ratio is `2/3`.** At `Lρ = 21` and `Lκ = 42` the common shape has
`A = 28`, `B = 42`, so `3A ≤ 2B` — which is what `sum_le_of_code` turns into
`E|χ(S,W)| ≤ (2/3)·E|χ(S,U)|`. -/
theorem ratio_ok {Lρ Lκ : ℝ} (hρ : 21 ≤ Lρ) (hκ : Lκ = 2 * Lρ) :
    3 * (Lρ + 7) ≤ 2 * Lκ := by
  rw [hκ]; linarith

/-- The two constraints on `κ` are compatible: `Lκ = 2Lρ` satisfies both `Lκ ≤ 2Lρ` (needed by
case 2) and `3(Lρ+7) ≤ 2Lκ` (the `2/3` ratio), as soon as `Lρ ≥ 21`. Rao's `ρ` and `κ`
"large enough" are this pair of inequalities. -/
theorem constants_exist : ∃ Lρ Lκ : ℝ, 0 ≤ Lκ ∧ Lκ ≤ 2 * Lρ ∧ 3 * (Lρ + 7) ≤ 2 * Lκ :=
  ⟨21, 42, by norm_num, by norm_num, by norm_num⟩

/-! ### The constants after trimming

`RaoRobust.isSatisfying_of_trimmed` reduces to a family at the threshold, but trimming lands at
`⌈R^w⌉`, so the bound comes back as `|𝓕| ≤ R^w + 1` rather than `R^w`. That unit of slack
enters in exactly two places — the empty-trace fiber bound and case 2's `k_𝓕` width — costing a
factor `2` in the first (so `(4/ρ)^a` becomes `(8/ρ)^a`) and one bit in the second. Case 2's
cost is then `LN + a·(4 − log₂ρ) + 3`.

The chase still closes, with `log₂κ ≤ 2log₂ρ − 1` in place of `≤ 2log₂ρ`, at `log₂ρ = 23` and
`log₂κ = 45` — where both that and the `2/3` ratio hold with equality. -/

/-- Case 2 fits the common shape after trimming: cost `LN + a(4 − Lρ) + 3` plus the tag. -/
theorem branch2_fits_trimmed {LN Lρ Lκ len : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ a)
    (hκ0 : 0 ≤ Lκ) (hκ2ρ : Lκ ≤ 2 * Lρ - 1)
    (h : len ≤ 1 + (LN + (a : ℝ) * (4 - Lρ) + 3)) :
    len ≤ LN + (a : ℝ) * (Lρ + 7) - (b : ℝ) * Lκ := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hba : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hb
  have hswap : -((b : ℝ) * Lκ) ≥ -((a : ℝ) * Lκ) := by nlinarith [hba, hκ0]
  nlinarith [h, ha1, hswap, hκ2ρ, hκ0]

/-- And the two constraints remain compatible: `log₂ρ = 23`, `log₂κ = 45`. -/
theorem constants_exist_trimmed :
    ∃ Lρ Lκ : ℝ, 0 ≤ Lκ ∧ Lκ ≤ 2 * Lρ - 1 ∧ 3 * (Lρ + 7) ≤ 2 * Lκ :=
  ⟨23, 45, by norm_num, by norm_num, by norm_num⟩

/-- The `2/3` ratio with the trimmed constants: `Lκ = 2Lρ − 1` and `Lρ ≥ 23`. -/
theorem ratio_ok_trimmed {Lρ Lκ : ℝ} (hρ : 23 ≤ Lρ) (hκ : Lκ = 2 * Lρ - 1) :
    3 * (Lρ + 7) ≤ 2 * Lκ := by
  rw [hκ]; linarith

/-- **The contraction, from the two branch bounds.** Given a code whose case-1 pairs cost
`LN + a(Lρ+3) − b·Lκ + 3` and whose case-2 pairs cost `LN + a(4 − Lρ) + 3` (each plus
the tag bit), with `a ≥ 1` throughout and the trimmed constants — the case-2 costs and the
`Lκ = 2Lρ − 1` relation carry the slack of a family known only up to `|𝓕| ≤ R^w + 1` — the
summed residual contracts by `2/3`. -/
theorem contraction_of_branch_bounds {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)}
    {X U : Finset α} {v : ℕ}
    (C : Coding.Code {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v})
    {N Lρ Lκ : ℝ} (hN : 0 < N) (hne : (pairs 𝓕 X U v).Nonempty)
    (hcard : N ≤ ((pairs 𝓕 X U v).card : ℝ))
    (hnil : ∀ p, C.enc p ≠ [])
    (ha : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}, 1 ≤ (chi 𝓕 p.1.2 U).card)
    (hb : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      (chi 𝓕 p.1.2 (U ∪ p.1.1)).card ≤ (chi 𝓕 p.1.2 U).card)
    (hκ0 : 0 ≤ Lκ) (hκ2ρ : Lκ ≤ 2 * Lρ - 1) (hρ : 23 ≤ Lρ) (hLκ : Lκ = 2 * Lρ - 1)
    (hlen : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      ((C.enc p).length : ℝ)
        ≤ 1 + (Real.logb 2 N + ((chi 𝓕 p.1.2 U).card : ℝ) * (Lρ + 3)
            - ((chi 𝓕 p.1.2 (U ∪ p.1.1)).card : ℝ) * Lκ + 3)
      ∨ ((C.enc p).length : ℝ)
        ≤ 1 + (Real.logb 2 N + ((chi 𝓕 p.1.2 U).card : ℝ) * (4 - Lρ) + 3)) :
    3 * ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 (U ∪ p.1)).card : ℝ)
      ≤ 2 * ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 U).card : ℝ) := by
  -- every pair fits the common shape
  have hcommon : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      ((C.enc p).length : ℝ)
        ≤ Real.logb 2 N + (Lρ + 7) * ((chi 𝓕 p.1.2 U).card : ℝ)
            - Lκ * ((chi 𝓕 p.1.2 (U ∪ p.1.1)).card : ℝ) := by
    intro p
    have hmul : ∀ y z : ℝ, y * z = z * y := fun y z => mul_comm y z
    rcases hlen p with h | h
    · have := branch1_fits (a := (chi 𝓕 p.1.2 U).card)
        (b := (chi 𝓕 p.1.2 (U ∪ p.1.1)).card) (ha p) h
      linarith [this]
    · have := branch2_fits_trimmed (a := (chi 𝓕 p.1.2 U).card)
        (b := (chi 𝓕 p.1.2 (U ∪ p.1.1)).card) (ha p) (hb p) hκ0 hκ2ρ h
      linarith [this]
  have hsum := contraction_of_lengths C (A := Lρ + 7) (B := Lκ) hN hne hcard hnil hcommon
  -- and `3(Lρ+7) ≤ 2Lκ` turns that into the `2/3` contraction
  have hratio : 3 * (Lρ + 7) ≤ 2 * Lκ := ratio_ok_trimmed hρ hLκ
  have hnn : 0 ≤ ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 (U ∪ p.1)).card : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hnn' : 0 ≤ ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 U).card : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  nlinarith [hsum, hratio, hnn, hnn']

end Rao

end Sunflower

/-
# The width-schedule iteration (paper §2.3)

This file chains the reduction round (`round_le`, paper Lemma 2.6) down from the
starting width to the bottom regime and finishes with the second-moment step
(`bottom_le`, replacing paper Lemma 2.10). This is where the theorem's
`log log w` is earned: the width shrinks by a `1/L` fraction each round
(`v' = v - v/L`, with `L ≈ log₂ log₂ w` at the eventual instantiation), so the
number of rounds is `O(L log w)` — and the per-round κ-cost
`(8n/s)^{v/v'} = (8n/s)^{1+O(1/L)}` stays within a constant factor of `8n/s`.

Design choices that keep the bookkeeping finite:

* **Fuel induction.** The induction variable is a fuel `t` with the invariant
  `v ≤ 2L·Q^t`, `Q = 2L/(2L-1)`; each round divides the width bound by `Q`
  (since `v/L ≥ v/(2L)` in ℕ for `v > 2L`), and fuel `0` forces the bottom
  regime `v ≤ 2L`. No explicit round-count function is needed.
* **Geometric budgets.** The round at width `v` receives failure allowance
  `ε·(1/2)^v` and bad-mass allowance `θ(v) = A₀·(1/2)^{v+1}`. Because widths
  strictly decrease along the schedule, the totals telescope against the
  invariants `fail ≤ (εbot + ε(1-(1/2)^v))·C(n,m)` and
  `A ≥ A₀(1-(1/2)^{v+1})` — both recurse exactly using only `v' + 1 ≤ v`.
  In particular the round count never appears in the accumulated failure.
* **Per-round budget `s`.** Every round consumes exactly `s` elements of ground
  set and `s` of the random budget; the budget hypothesis `s·t + m_bot ≤ m`
  threads through, and the bottom keeps at least `m_bot`.

The κ-requirements are isolated as hypotheses:
* `hK1` (rounds): `(8n₀/s)^v·M·2^{2v+1} ≤ ε·A₀·κ^{v-v/L}` for all `v > 2L`;
* `hK2` (bottom Chebyshev): `16L²·n₀·M ≤ εbot·A₀·κ·(m_bot-2L)`;
* `hK3` (bottom geometric-sum condition): `4L·n₀ ≤ κ·(m_bot-2L)`.
They are verified for `κ = C·r³·lg w·lg lg w` at the `spread_lemma`
instantiation.
-/
import Sunflower.SpreadBottom

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace SpreadCore

open scoped Classical

variable {α : Type*} [DecidableEq α]

/-- The bottom regime `v ≤ 2L` of the iteration: apply `bottom_le` and absorb
the constants into `εbot` via `hK2`/`hK3`. -/
lemma iterate_bottom {L m_bot n₀ : ℕ} {A₀ M κ εbot : ℝ} {X : Finset α}
    {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ}
    (hL : 2 ≤ L) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 ≤ M) (hκ : 1 ≤ κ) (hεb : 0 ≤ εbot)
    (hK2 : 16 * (L : ℝ) ^ 2 * n₀ * M ≤ εbot * A₀ * κ * ((m_bot - 2 * L : ℕ) : ℝ))
    (hK3 : 4 * (L : ℝ) * n₀ ≤ κ * ((m_bot - 2 * L : ℕ) : ℝ))
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (htot : A ≤ (wTotal X σ : ℝ)) (hAinv : A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A)
    (hv : 1 ≤ v) (hvL : v ≤ 2 * L) (hmm : m_bot ≤ m) (hmn : m ≤ X.card)
    (hn₀ : X.card ≤ n₀) :
    (failCount X σ m : ℝ) ≤ εbot * (X.card.choose m : ℝ) := by
  have hκ0 : (0:ℝ) < κ := lt_of_lt_of_le one_pos hκ
  -- the mass never drops below `A₀/2`
  have hhalf : (1 / 2 : ℝ) ^ (v + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (v + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hA2 : A₀ / 2 ≤ A := by
    calc A₀ / 2 = A₀ * (1 - 1 / 2) := by ring
      _ ≤ A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) := by
          refine mul_le_mul_of_nonneg_left (by linarith) hA₀.le
      _ ≤ A := hAinv
  have hA : (0:ℝ) < A := lt_of_lt_of_le (by positivity) hA2
  -- denominators
  have hq0 : (0:ℝ) < ((m_bot - 2 * L : ℕ) : ℝ) := by
    have : 0 < m_bot - 2 * L := by omega
    exact_mod_cast this
  have hmv : m_bot - 2 * L ≤ m - v := by omega
  have hq0' : (0:ℝ) < ((m - v : ℕ) : ℝ) := by
    have : 0 < m - v := by omega
    exact_mod_cast this
  have hqle : ((m_bot - 2 * L : ℕ) : ℝ) ≤ ((m - v : ℕ) : ℝ) := by
    exact_mod_cast hmv
  -- the ratio `R = n/(m-v)` is dominated by `R₀ = n₀/(m_bot-2L)`
  have hRle : (X.card : ℝ) / ((m - v : ℕ) : ℝ) ≤
      (n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ) :=
    div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast hn₀) hq0 hqle
  have hR0 : (0:ℝ) ≤ (X.card : ℝ) / ((m - v : ℕ) : ℝ) := by positivity
  have hvL' : (v : ℝ) ≤ 2 * L := by exact_mod_cast hvL
  -- geometric-sum condition of `bottom_le`
  have hgeo : (v : ℝ) * ((X.card : ℝ) / ((m - v : ℕ) : ℝ) / κ) ≤ 1 / 2 := by
    have h1 : (v : ℝ) * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) ≤
        2 * L * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) :=
      mul_le_mul hvL' hRle hR0 (by positivity)
    have h2 : 2 * (L : ℝ) * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) ≤ κ / 2 := by
      rw [show 2 * (L : ℝ) * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) =
        2 * (L : ℝ) * (n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ) from by ring]
      rw [div_le_iff₀ hq0]
      calc 2 * (L : ℝ) * (n₀ : ℝ) ≤ κ * ((m_bot - 2 * L : ℕ) : ℝ) / 2 := by
            linarith [hK3]
        _ = κ / 2 * ((m_bot - 2 * L : ℕ) : ℝ) := by ring
    rw [show (v : ℝ) * ((X.card : ℝ) / ((m - v : ℕ) : ℝ) / κ) =
      (v : ℝ) * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) / κ from by ring]
    rw [div_le_iff₀ hκ0]
    calc (v : ℝ) * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) ≤
        2 * L * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) := h1
      _ ≤ κ / 2 := h2
      _ = 1 / 2 * κ := by ring
  -- apply the second-moment step
  have happ := bottom_le (v := v) (m := m) hκ0 hM hA hb hl htot hv
    (by omega) hmn hgeo
  -- absorb constants: `2v²R·M ≤ εbot·A·κ`
  have hcoef : 2 * (v : ℝ) ^ 2 * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) * M ≤
      εbot * A * κ := by
    have hv2 : (v : ℝ) ^ 2 ≤ (2 * L) ^ 2 := by
      have := sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) v]) hvL'
      simpa [sq] using this
    have h1 : 2 * (v : ℝ) ^ 2 * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) * M ≤
        2 * (2 * L) ^ 2 * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) * M := by
      refine mul_le_mul_of_nonneg_right ?_ hM
      refine mul_le_mul ?_ hRle hR0 (by positivity)
      exact mul_le_mul_of_nonneg_left hv2 (by norm_num)
    have h2 : 2 * (2 * (L:ℝ)) ^ 2 * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) * M ≤
        εbot * (A₀ / 2) * κ := by
      rw [show 2 * (2 * (L:ℝ)) ^ 2 * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) * M =
        8 * (L:ℝ) ^ 2 * (n₀ : ℝ) * M / ((m_bot - 2 * L : ℕ) : ℝ) from by ring]
      rw [div_le_iff₀ hq0]
      have hexp : εbot * (A₀ / 2) * κ * ((m_bot - 2 * L : ℕ) : ℝ) =
          εbot * A₀ * κ * ((m_bot - 2 * L : ℕ) : ℝ) / 2 := by ring
      rw [hexp]
      linarith [hK2]
    calc 2 * (v : ℝ) ^ 2 * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) * M ≤
        2 * (2 * (L:ℝ)) ^ 2 * ((n₀ : ℝ) / ((m_bot - 2 * L : ℕ) : ℝ)) * M := h1
      _ ≤ εbot * (A₀ / 2) * κ := h2
      _ ≤ εbot * A * κ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA2 hεb) hκ0.le
  -- conclude
  have hAκ : (0:ℝ) < A * κ := mul_pos hA hκ0
  refine le_of_mul_le_mul_right ?_ hAκ
  calc (failCount X σ m : ℝ) * (A * κ)
      = (failCount X σ m : ℝ) * A * κ := by ring
    _ ≤ 2 * (v : ℝ) ^ 2 * ((X.card : ℝ) / ((m - v : ℕ) : ℝ)) * M *
        (X.card.choose m : ℝ) := happ
    _ ≤ εbot * A * κ * (X.card.choose m : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ = εbot * (X.card.choose m : ℝ) * (A * κ) := by ring

/-- **The width-schedule iteration, abstracted over its bottom step.**

The iteration uses the bottom estimate only through its *conclusion*
`failCount X σ m ≤ εbot·C(|X|,m)`, at two points (the `t = 0` case and the `v ≤ 2L` branch of
the successor case). Taking that conclusion as a hypothesis rather than deriving it from
`hK2`/`hK3` decouples the iteration from *how* the bottom is established: the second-moment
route (`iterate_bottom`, giving `iterate_le` below) and the Janson route
(`JansonBottom.failCount_le_of_janson_budget`, whose conclusion has exactly this shape) both
instantiate this one theorem.

Under the κ-conditions `hK1`–`hK3`, a
`v`-bounded link-bounded system with mass `≥ A ≥ A₀(1-(1/2)^{v+1})`, width bound
within fuel (`v ≤ 2L·Q^t`), and budget `m ≥ s·t + m_bot` fails with fraction at
most `εbot + ε(1-(1/2)^v)`. -/
theorem iterate_le_of_bottom {L s m_bot n₀ : ℕ} {A₀ M κ ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 ≤ M) (hκ : 1 ≤ κ) (hε : 0 ≤ ε) (hεb : 0 ≤ εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hbot : ∀ {X : Finset α} {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ},
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      1 ≤ v → v ≤ 2 * L → m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤ εbot * (X.card.choose m : ℝ)) :
    ∀ (t : ℕ) (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) (A : ℝ) (m : ℕ),
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      (v : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t →
      1 ≤ v → s * t + m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤
        (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) := by
  have hLR : (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
  have hεbot_le : ∀ v : ℕ, ∀ X : Finset α, ∀ m : ℕ,
      εbot * (X.card.choose m : ℝ) ≤
      (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) := by
    intro v X m
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have hp1 : (1/2:ℝ) ^ v ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have := mul_nonneg hε (by linarith : (0:ℝ) ≤ 1 - (1/2:ℝ)^v)
    linarith
  intro t
  induction t with
  | zero =>
    intro X σ v A m hb hl htot hAinv hfuel hv hbud hmn hn₀
    have hvL : v ≤ 2 * L := by
      have h : (v : ℝ) ≤ 2 * L := by
        have h0 := hfuel
        rw [pow_zero, mul_one] at h0
        exact h0
      exact_mod_cast h
    have hbot' := hbot hb hl htot hAinv hv hvL (by omega) hmn hn₀
    exact hbot'.trans (hεbot_le v X m)
  | succ t ih =>
    intro X σ v A m hb hl htot hAinv hfuel hv hbud hmn hn₀
    have hbud' : m_bot ≤ m := by
      have hdist : s * (t + 1) = s * t + s := by ring
      omega
    by_cases hvL : v ≤ 2 * L
    · have hbot' := hbot hb hl htot hAinv hv hvL hbud' hmn hn₀
      exact hbot'.trans (hεbot_le v X m)
    · rw [not_le] at hvL
      -- ℕ-division facts about the width decrement
      set d := v / L with hd
      have hd1 : 1 ≤ d := by
        rw [hd, Nat.one_le_div_iff (by omega : 0 < L)]
        omega
      have hdle : d ≤ v / 2 := by
        rw [hd]
        exact Nat.div_le_div_left hL (by omega)
      have hv22 : v / 2 * 2 ≤ v := Nat.div_mul_le_self v 2
      have hv21 : 1 ≤ v / 2 := by
        rw [Nat.one_le_div_iff (by omega : 0 < 2)]
        omega
      have h2d : v < 2 * (L * d) := by
        have hmod := Nat.div_add_mod v L
        have hmodlt : v % L < L := Nat.mod_lt v (by omega)
        rw [← hd] at hmod
        have hLd : L ≤ L * d := Nat.le_mul_of_pos_right L (by omega)
        omega
      set v' := v - d with hv'
      have hdv : d ≤ v := by omega
      have hv'1 : 1 ≤ v' := by omega
      have hv'v : v' + 1 ≤ v := by omega
      -- fuel decay
      have h2L0 : (2 * (L:ℝ)) ≠ 0 := by positivity
      have h2L1 : (2 * (L:ℝ) - 1) ≠ 0 := by
        have : (1:ℝ) ≤ 2 * (L:ℝ) - 1 := by linarith
        linarith
      have hfuel' : (v' : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t := by
        have hcast : (v' : ℝ) = (v : ℝ) - (d : ℝ) := by
          rw [hv']
          push_cast [hdv]
          ring
        have hdge : (v : ℝ) / (2 * L) ≤ (d : ℝ) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (L:ℝ))]
          have hcast2 : (v:ℝ) < 2 * ((L * d : ℕ) : ℝ) := by exact_mod_cast h2d
          push_cast at hcast2
          linarith
        have hstep : (v' : ℝ) ≤ (v : ℝ) * ((2 * L - 1) / (2 * L)) := by
          rw [hcast]
          have hexp : (v : ℝ) * ((2 * L - 1) / (2 * L)) =
              v - v / (2 * L) := by
            field_simp
          rw [hexp]
          linarith
        calc (v' : ℝ) ≤ (v : ℝ) * ((2 * L - 1) / (2 * L)) := hstep
          _ ≤ (2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ (t + 1)) *
              ((2 * L - 1) / (2 * L)) := by
              refine mul_le_mul_of_nonneg_right hfuel ?_
              refine div_nonneg (by linarith) (by positivity)
          _ = 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t := by
              rw [pow_succ]
              field_simp
      -- mass facts
      have hhalfp : (1 / 2 : ℝ) ^ (v + 1) ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ (v + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 2 := pow_one _
      have hA2 : A₀ / 2 ≤ A := by
        calc A₀ / 2 = A₀ * (1 - 1 / 2) := by ring
          _ ≤ A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) := by
              refine mul_le_mul_of_nonneg_left (by linarith) hA₀.le
          _ ≤ A := hAinv
      have hA : (0:ℝ) < A := lt_of_lt_of_le (by positivity) hA2
      set θ := A₀ * (1 / 2 : ℝ) ^ (v + 1) with hθ
      have hθ0 : (0:ℝ) < θ := by rw [hθ]; positivity
      set δ := θ / A with hδdef
      have hδ0 : 0 < δ := div_pos hθ0 hA
      have hδA : δ * A = θ := div_mul_cancel₀ θ hA.ne'
      set β' := εbot + ε * (1 - (1 / 2 : ℝ) ^ v') with hβ'
      have hβ'0 : 0 ≤ β' := by
        rw [hβ']
        have hp1 : (1/2:ℝ) ^ v' ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have := mul_nonneg hε (by linarith : (0:ℝ) ≤ 1 - (1/2:ℝ)^v')
        linarith
      have hsm : s ≤ m := by
        have hdist : s * (t + 1) = s * t + s := by ring
        omega
      -- the reduced systems satisfy the induction hypothesis
      have hIH : ∀ W ∈ X.powersetCard s, (badWeight X σ v' W : ℝ) ≤ δ * A →
          (failCount (X \ W) (reduce X σ v' W) (m - s) : ℝ) ≤
            β' * ((X.card - s).choose (m - s) : ℝ) := by
        intro W hW hbad
        rw [hδA] at hbad
        rw [Finset.mem_powersetCard] at hW
        obtain ⟨hWX, hWcard⟩ := hW
        have hcard' : (X \ W).card = X.card - s := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hWX, hWcard]
        have htot' : A - θ ≤ (wTotal (X \ W) (reduce X σ v' W) : ℝ) := by
          have hrt := reduce_total (v' := v') (W := W) hb
          have heq : (wTotal (X \ W) (reduce X σ v' W) : ℝ) =
              (wTotal X σ : ℝ) - (badWeight X σ v' W : ℝ) := by
            rw [hrt]
            push_cast
            ring
          rw [heq]
          linarith
        have hAinv' : A₀ * (1 - (1 / 2 : ℝ) ^ (v' + 1)) ≤ A - θ := by
          have h1 : (1/2:ℝ) ^ v ≤ (1/2:ℝ) ^ (v' + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hv'v
          have h2 : A₀ * (1 - (1/2:ℝ) ^ v) ≤ A - θ := by
            rw [hθ]
            have hexp : A₀ * (1 - (1/2:ℝ)^v) =
                A₀ * (1 - (1/2:ℝ)^(v+1)) - A₀ * (1/2:ℝ)^(v+1) := by
              rw [show ((1:ℝ)/2)^(v+1) = (1/2) * (1/2:ℝ)^v from by
                rw [pow_succ]; ring]
              ring
            rw [hexp]
            linarith [hAinv]
          calc A₀ * (1 - (1/2:ℝ)^(v'+1)) ≤ A₀ * (1 - (1/2:ℝ)^v) := by
                refine mul_le_mul_of_nonneg_left (by linarith) hA₀.le
            _ ≤ A - θ := h2
        have hb2 : s * t + m_bot ≤ m - s := by
          have hdist : s * (t + 1) = s * t + s := by ring
          omega
        have happ := ih (X \ W) (reduce X σ v' W) v' (A - θ) (m - s)
          (reduce_bounded hb)
          (reduce_linkBounded (le_trans zero_le_one hκ) hl)
          htot' hAinv' hfuel' hv'1 hb2
          (by rw [hcard']; omega) (by rw [hcard']; omega)
        rw [hcard'] at happ
        exact happ
      -- the round
      have hround := round_le (v := v) (v' := v') (m₁ := s) (m₂ := m - s)
        (M := M) (κ := κ) (A := A) (δ := δ) (β' := β')
        hκ hM hA hδ0 hβ'0 hb hl hv hs (by omega) hIH
      have hms : s + (m - s) = m := by omega
      rw [hms] at hround
      -- the Markov coefficient is within the geometric allowance
      have hκ0 : (0:ℝ) < κ := lt_of_lt_of_le one_pos hκ
      have hκv' : (0:ℝ) < κ ^ v' := pow_pos hκ0 _
      have hγ : (8 * (X.card:ℝ) / s) ^ v * M / (κ ^ v' * δ * A) ≤
          ε * (1/2:ℝ) ^ v := by
        have hden : κ ^ v' * δ * A = κ ^ v' * θ := by
          rw [mul_assoc, hδA]
        rw [hden]
        have hbase : 8 * (X.card:ℝ) / (s:ℝ) ≤ 8 * (n₀:ℝ) / (s:ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_
            (inv_nonneg.mpr (Nat.cast_nonneg _))
          have : (X.card:ℝ) ≤ n₀ := by exact_mod_cast hn₀
          linarith
        have hpow : (8 * (X.card:ℝ) / s) ^ v ≤ (8 * (n₀:ℝ) / s) ^ v :=
          pow_le_pow_left₀ (by positivity) hbase v
        have hK := hK1 v hvL
        rw [show v - v / L = v' from by rw [hv', hd]] at hK
        have h2 : (8 * (n₀:ℝ) / s) ^ v * M ≤
            ε * (1/2:ℝ) ^ v * (κ ^ v' * θ) := by
          have hmul : (0:ℝ) < (2:ℝ) ^ (v + 1) * (2:ℝ) ^ v := by positivity
          refine le_of_mul_le_mul_right ?_ hmul
          have hpow2 : ((1/2:ℝ) ^ (v+1)) * ((2:ℝ) ^ (v+1)) = 1 := by
            rw [← mul_pow]
            norm_num
          have hpow3 : ((1/2:ℝ) ^ v) * ((2:ℝ) ^ v) = 1 := by
            rw [← mul_pow]
            norm_num
          calc (8 * (n₀:ℝ) / s) ^ v * M * ((2:ℝ) ^ (v+1) * (2:ℝ) ^ v)
              = (8 * (n₀:ℝ) / s) ^ v * M * 2 ^ (v+1) * 2 ^ v := by ring
            _ ≤ ε * A₀ * κ ^ v' := hK
            _ = ε * (1/2:ℝ)^v * (κ ^ v' * (A₀ * (1/2:ℝ)^(v+1))) *
                ((2:ℝ) ^ (v+1) * (2:ℝ) ^ v) := by
                rw [show ε * (1/2:ℝ)^v * (κ ^ v' * (A₀ * (1/2:ℝ)^(v+1))) *
                    ((2:ℝ) ^ (v+1) * (2:ℝ) ^ v) =
                  ε * A₀ * κ ^ v' * (((1/2:ℝ)^(v+1)) * ((2:ℝ)^(v+1))) *
                    (((1/2:ℝ)^v) * ((2:ℝ)^v)) from by ring]
                rw [hpow2, hpow3, mul_one, mul_one]
            _ = ε * (1/2:ℝ)^v * (κ ^ v' * θ) * ((2:ℝ) ^ (v+1) * (2:ℝ) ^ v) := by
                rw [hθ]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < κ ^ v' * θ)]
        calc (8 * (X.card:ℝ) / s) ^ v * M ≤ (8 * (n₀:ℝ) / s) ^ v * M :=
              mul_le_mul_of_nonneg_right hpow hM
          _ ≤ ε * (1/2:ℝ) ^ v * (κ ^ v' * θ) := h2
      -- combine the allowances
      have hcomb : (8 * (X.card:ℝ) / s) ^ v * M / (κ ^ v' * δ * A) + β' ≤
          εbot + ε * (1 - (1/2:ℝ) ^ v) := by
        have hps : (1/2:ℝ) ^ v = (1/2:ℝ) ^ (v-1) * (1/2) := by
          conv_lhs => rw [show v = (v - 1) + 1 from by omega]
          rw [pow_succ]
        have hp : (1/2:ℝ) ^ (v-1) ≤ (1/2:ℝ) ^ v' :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have h2v : 2 * (1/2:ℝ) ^ v ≤ (1/2:ℝ) ^ v' := by
          calc 2 * (1/2:ℝ) ^ v = (1/2:ℝ) ^ (v-1) := by
                rw [hps]; ring
            _ ≤ (1/2:ℝ) ^ v' := hp
        have hkey : (1/2:ℝ)^v + (1 - (1/2:ℝ)^v') ≤ 1 - (1/2:ℝ)^v := by
          linarith
        calc (8 * (X.card:ℝ) / s) ^ v * M / (κ ^ v' * δ * A) + β'
            ≤ ε * (1/2:ℝ) ^ v + β' := add_le_add hγ le_rfl
          _ = εbot + ε * ((1/2:ℝ)^v + (1 - (1/2:ℝ)^v')) := by
              rw [hβ']
              ring
          _ ≤ εbot + ε * (1 - (1/2:ℝ)^v) := by
              have := mul_le_mul_of_nonneg_left hkey hε
              linarith
      calc (failCount X σ m : ℝ)
          ≤ ((8 * (X.card:ℝ) / s) ^ v * M / (κ ^ v' * δ * A) + β') *
            (X.card.choose m : ℝ) := hround
        _ ≤ (εbot + ε * (1 - (1/2:ℝ) ^ v)) * (X.card.choose m : ℝ) :=
            mul_le_mul_of_nonneg_right hcomb (Nat.cast_nonneg _)

/-- **The width-schedule iteration** in its original form: the second-moment bottom step
(`iterate_bottom`) instantiating `iterate_le_of_bottom`. Statement unchanged, so
`SpreadAssemble` and `alwz` are unaffected. -/
theorem iterate_le {L s m_bot n₀ : ℕ} {A₀ M κ ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 ≤ M) (hκ : 1 ≤ κ) (hε : 0 ≤ ε) (hεb : 0 ≤ εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hK2 : 16 * (L : ℝ) ^ 2 * n₀ * M ≤ εbot * A₀ * κ * ((m_bot - 2 * L : ℕ) : ℝ))
    (hK3 : 4 * (L : ℝ) * n₀ ≤ κ * ((m_bot - 2 * L : ℕ) : ℝ)) :
    ∀ (t : ℕ) (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) (A : ℝ) (m : ℕ),
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      (v : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t →
      1 ≤ v → s * t + m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤
        (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) :=
  iterate_le_of_bottom hL hs hmb hA₀ hM hκ hε hεb hK1
    fun hb hl htot hAinv hv hvL hmm hmn hn₀ =>
      iterate_bottom hL hmb hA₀ hM hκ hεb hK2 hK3 hb hl htot hAinv hv hvL hmm hmn hn₀

end SpreadCore

end Sunflower

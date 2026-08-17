/-
# Assembling the spread lemma

The arithmetic instantiation of the width-schedule iteration, discharging
`Sunflower.spread_lemma` with the explicit constant `C := 2^41`.

Parameters (for a given `r ≥ 3`, `2 ≤ w`, `1 ≤ w' ≤ w`, and
`κ = 2^41·r³·lg w·lg lg w`):

* `L := Nat.log 2 ⌈κ⌉₊ + Nat.log 2 r + 4` — chosen so that `κ ≤ 2^L` and
  `8r ≤ 2^{2L}` hold by construction (`Nat.log`-based, no real exponentials),
  while `L = O(lg r + lg lg w)` keeps the budget.
* `k₀ := Nat.log 2 w + 1`, `t₀ := (2L-1)·k₀` — the fuel; `Q^{2L-1} ≥ 2` by
  Bernoulli, so `2L·Q^{t₀} ≥ 2^{k₀} > w`.
* `m := n/r`, `m_bot := m - m/2`, `s := (m/2)/t₀` — the budget split.

The two master inequalities, verified with `C = 2^41` and the numeric bounds
`lg 2 ≥ 21/20` (⟺ `2^20 ≥ 1.9^21`, rational arithmetic) and
`lg lg 2 ≥ 1/20` (⟺ `1.05^20 ≥ 1.9`):

* (M1) `1024·r·t₀ ≤ κ` — feeds the round condition `hK1` (via `κ ≥ 16·(8n/s)`
  and `2^{v-1} ≥ 4r`) and the budget facts;
* (M2) `512·r²·L² ≤ κ` — feeds the bottom conditions `hK2`, `hK3`.

Both use only `lg y ≤ 2y` and `(lg y)² ≤ 16y` on `y ∈ {r, lg w}` plus numeric
leaves — no `rpow` anywhere.
-/
import Sunflower.SpreadIterate
import Sunflower.Lg
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset

set_option maxHeartbeats 3200000

namespace Sunflower

namespace SpreadCore

open scoped Classical

variable {α : Type*} [DecidableEq α]

/-! ## Toolkit stubs (proved in scratch files, integrated on completion) -/

/-- The natural log of the base: `log 1.9 ≥ 1/2`. -/
lemma half_le_log_base : (1/2 : ℝ) ≤ Real.log 1.9 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1.9)]
  have h1 : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp (1/2 : ℝ) := Real.exp_pos _
  nlinarith [h1, h2, h3, sq_nonneg (Real.exp (1/2 : ℝ) - 1.9)]

/-- `lg y ≤ 2·y` for positive `y`. -/
lemma lg_le_double {y : ℝ} (hy : 0 < y) : lg y ≤ 2 * y := by
  have hB : (0:ℝ) < Real.log 1.9 := lt_of_lt_of_le (by norm_num) half_le_log_base
  have hlog : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy
  unfold lg
  rw [← Real.log_div_log, div_le_iff₀ hB]
  nlinarith [mul_nonneg hy.le (sub_nonneg.mpr half_le_log_base)]

/-- `(lg y)² ≤ 16·y` for `y ≥ 1`. -/
lemma lg_sq_le {y : ℝ} (hy : 1 ≤ y) : (lg y) ^ 2 ≤ 16 * y := by
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hB : (0:ℝ) < Real.log 1.9 := lt_of_lt_of_le (by norm_num) half_le_log_base
  have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy
  have h0 : 0 ≤ lg y := by
    unfold lg
    rw [← Real.log_div_log]
    exact div_nonneg hlog_nonneg hB.le
  have hlogsqrt : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hlogy : Real.log y ≤ 2 * Real.sqrt y := by
    have hhalf : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
    linarith
  have hub : lg y ≤ 4 * Real.sqrt y := by
    unfold lg
    rw [← Real.log_div_log, div_le_iff₀ hB]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr half_le_log_base)]
  calc (lg y) ^ 2 ≤ (4 * Real.sqrt y) ^ 2 := pow_le_pow_left₀ h0 hub 2
    _ = 16 * (Real.sqrt y ^ 2) := by ring
    _ = 16 * y := by rw [Real.sq_sqrt hy0.le]

/-- `lg 2 ≤ 2`. -/
lemma lg_two_le : lg 2 ≤ 2 := by
  have h2 : lg ((1.9:ℝ) ^ (2:ℕ)) = 2 := by
    unfold lg
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_base]
    norm_num
  calc lg 2 ≤ lg ((1.9:ℝ) ^ (2:ℕ)) := lg_mono two_pos (by norm_num)
    _ = 2 := h2

/-- `Nat.log 2` is dominated by `lg` for positive naturals. -/
lemma natlog_le_lg {x : ℕ} (hx : 1 ≤ x) : (Nat.log 2 x : ℝ) ≤ lg x := by
  set k := Nat.log 2 x with hk
  have hpow : 2 ^ k ≤ x := Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2:ℝ) ^ k ≤ (x:ℝ) := by exact_mod_cast hpow
  have hposR : (0:ℝ) < 2 ^ k := by positivity
  have h1 : lg ((2:ℝ) ^ k) ≤ lg x := lg_mono hposR hpowR
  have h2 : lg ((2:ℝ) ^ k) = k * lg 2 := by
    unfold lg
    rw [Real.logb_pow]
  have h3 : (k:ℝ) ≤ (k:ℝ) * lg 2 :=
    le_mul_of_one_le_right (Nat.cast_nonneg k) one_lt_lg_two.le
  calc (k:ℝ) ≤ (k:ℝ) * lg 2 := h3
    _ = lg ((2:ℝ) ^ k) := h2.symm
    _ ≤ lg x := h1

def toWeight (𝓖 : Finset (Finset α)) : Finset α → ℕ := fun S => if S ∈ 𝓖 then 1 else 0

lemma toWeight_bounded {𝓖 : Finset (Finset α)} {w' : ℕ} (hu : IsUniform w' 𝓖) :
    WBounded (𝓖.biUnion id) w' (toWeight 𝓖) := by
  intro S hS
  by_cases h : S ∈ 𝓖
  · exact ⟨Finset.subset_biUnion_of_mem id h, le_of_eq (hu h)⟩
  · simp [toWeight, h] at hS

lemma toWeight_total (𝓖 : Finset (Finset α)) :
    wTotal (𝓖.biUnion id) (toWeight 𝓖) = 𝓖.card := by
  simp only [wTotal, toWeight]
  rw [← Finset.card_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨Finset.subset_biUnion_of_mem id h, h⟩

lemma toWeight_link (𝓖 : Finset (Finset α)) (T : Finset α) :
    wLink (𝓖.biUnion id) (toWeight 𝓖) T = (𝓖.filter (fun S => T ⊆ S)).card := by
  simp only [wLink, toWeight]
  rw [← Finset.card_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨-, hT⟩, hS⟩; exact ⟨hS, hT⟩
  · rintro ⟨hS, hT⟩; exact ⟨⟨Finset.subset_biUnion_of_mem id hS, hT⟩, hS⟩

lemma toWeight_linkBounded {𝓖 : Finset (Finset α)} {κ : ℝ}
    (hsp : IsSpread κ 𝓖) :
    WLinkBounded (𝓖.biUnion id) (toWeight 𝓖) (𝓖.card : ℝ) κ := by
  intro T hT
  rw [toWeight_link, ← card_link 𝓖 T]
  exact hsp T

/-- Any member of the family witnesses `κ^{w'} ≤ |𝓖|` under spreadness. -/
lemma pow_le_card_of_isSpread {𝓖 : Finset (Finset α)} {κ : ℝ} {w' : ℕ}
    (hκ : 0 ≤ κ) (hne : 𝓖.Nonempty) (hu : IsUniform w' 𝓖) (hsp : IsSpread κ 𝓖) :
    κ ^ w' ≤ (𝓖.card : ℝ) := by
  obtain ⟨S₀, hS₀⟩ := hne
  have hmem : S₀ ∈ 𝓖.filter (fun S => S₀ ⊆ S) :=
    Finset.mem_filter.mpr ⟨hS₀, subset_rfl⟩
  have hpos : 1 ≤ (𝓖.filter (fun S => S₀ ⊆ S)).card :=
    Finset.card_pos.mpr ⟨S₀, hmem⟩
  have hlink : 1 ≤ (link 𝓖 S₀).card := by
    rw [card_link]; exact hpos
  have h := hsp S₀
  have hcard : S₀.card = w' := hu hS₀
  rw [hcard] at h
  calc κ ^ w' = 1 * κ ^ w' := (one_mul _).symm
    _ ≤ ((link 𝓖 S₀).card : ℝ) * κ ^ w' := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hκ w')
        exact_mod_cast hlink
    _ ≤ (𝓖.card : ℝ) := h

lemma card_le_pow_ground {𝓖 : Finset (Finset α)} {w' : ℕ} (hu : IsUniform w' 𝓖) :
    𝓖.card ≤ (𝓖.biUnion id).card ^ w' := by
  have hsub : 𝓖 ⊆ (𝓖.biUnion id).powersetCard w' := by
    intro S hS
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_biUnion_of_mem id hS, hu hS⟩
  calc 𝓖.card ≤ ((𝓖.biUnion id).powersetCard w').card := Finset.card_le_card hsub
    _ = (𝓖.biUnion id).card.choose w' := Finset.card_powersetCard _ _
    _ ≤ (𝓖.biUnion id).card ^ w' := Nat.choose_le_pow _ _

/-- The ground set is at least `κ` under spreadness (for `w' ≥ 1`). -/
lemma kappa_le_ground {𝓖 : Finset (Finset α)} {κ : ℝ} {w' : ℕ}
    (hκ : 0 ≤ κ) (hne : 𝓖.Nonempty) (hw' : 1 ≤ w') (hu : IsUniform w' 𝓖)
    (hsp : IsSpread κ 𝓖) : κ ≤ ((𝓖.biUnion id).card : ℝ) := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : κ ^ w' ≤ (𝓖.card : ℝ) := pow_le_card_of_isSpread hκ hne hu hsp
  have h2 : (𝓖.card : ℝ) ≤ ((𝓖.biUnion id).card : ℝ) ^ w' := by
    exact_mod_cast card_le_pow_ground hu
  have h3 : ((𝓖.biUnion id).card : ℝ) ^ w' < κ ^ w' :=
    pow_lt_pow_left₀ hlt (Nat.cast_nonneg _) (by omega)
  linarith

/-! ## Numeric bounds on `lg` at small arguments

Both reduce to comparisons of *rational* powers — no `rpow`. -/

/-- `lg 2 ≥ 21/20`, because `2^20 = 1048576 ≥ 1.9^21`. -/
lemma lg_two_ge : (21/20 : ℝ) ≤ lg 2 := by
  have h20 : (21 : ℝ) * 1 ≤ 20 * lg 2 := by
    have hkey : ((1.9:ℝ)) ^ (21:ℕ) ≤ (2:ℝ) ^ (20:ℕ) := by norm_num
    have h1 : lg ((1.9:ℝ) ^ (21:ℕ)) ≤ lg ((2:ℝ) ^ (20:ℕ)) :=
      lg_mono (by positivity) hkey
    rw [lg, lg, Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one one_lt_base] at h1
    rw [lg]
    push_cast at h1 ⊢
    linarith
  linarith [h20]

/-- `lg (lg 2) ≥ 1/20`, because `lg 2 ≥ 21/20` and `(21/20)^20 ≥ 1.9`. -/
lemma lg_lg_two_ge : (1/20 : ℝ) ≤ lg (lg 2) := by
  have h1 : lg (21/20 : ℝ) ≤ lg (lg 2) := lg_mono (by norm_num) lg_two_ge
  have h2 : (1/20 : ℝ) ≤ lg (21/20 : ℝ) := by
    have hkey : ((1.9:ℝ)) ^ (1:ℕ) ≤ ((21/20 : ℝ)) ^ (20:ℕ) := by norm_num
    have h3 : lg ((1.9:ℝ) ^ (1:ℕ)) ≤ lg (((21/20):ℝ) ^ (20:ℕ)) :=
      lg_mono (by positivity) hkey
    rw [lg, lg, Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one one_lt_base] at h3
    rw [lg]
    push_cast at h3 ⊢
    linarith
  linarith

/-! ## The instantiation -/

/-- **The spread lemma with the explicit constant `2^41`**: an
`(2^41·r³·lg w·lg lg w)`-spread `w'`-uniform nonempty family contains `r`
pairwise disjoint members. -/
theorem spread_core_main (r w w' : ℕ) (hr : 3 ≤ r) (hw : 2 ≤ w) (hw' : 1 ≤ w')
    (hw'w : w' ≤ w) {𝓖 : Finset (Finset α)} (hu : IsUniform w' 𝓖)
    (hne : 𝓖.Nonempty)
    (hsp : IsSpread ((2^41 : ℝ) * r ^ 3 * lg w * lg (lg w)) 𝓖) :
    ∃ 𝒟 ⊆ 𝓖, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  classical
  set κ : ℝ := (2^41 : ℝ) * r ^ 3 * lg w * lg (lg w) with hκdef
  -- basic facts about the factors
  have hw2 : (2:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw
  have hlgw : (1:ℝ) < lg w := one_lt_lg hw2
  have hlgw0 : (0:ℝ) < lg w := lt_trans one_pos hlgw
  have hlglg20 : (1/20 : ℝ) ≤ lg (lg w) := le_trans lg_lg_two_ge (lg_lg_le_lg_lg hw2)
  have hlglgpos : (0:ℝ) < lg (lg w) := lt_of_lt_of_le (by norm_num) hlglg20
  have hr3 : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hr9 : (9:ℝ) ≤ (r:ℝ)^2 := by nlinarith
  have hr27 : (27:ℝ) ≤ (r:ℝ)^3 := by nlinarith
  have hr3r : 9*(r:ℝ) ≤ (r:ℝ)^3 := by nlinarith
  have hlgr : (1:ℝ) < lg r := one_lt_lg (by exact_mod_cast (by omega : 2 ≤ r))
  have hlgr2 : lg r ≤ 2*(r:ℝ) := lg_le_double hrpos
  have hlgrsq : (lg r)^2 ≤ 16*(r:ℝ) := lg_sq_le (by exact_mod_cast (by omega : 1 ≤ r))
  have hlglgsq : (lg (lg w))^2 ≤ 16*(lg w) := lg_sq_le hlgw.le
  -- κ positivity and κ ≥ 1
  have hκpos : (0:ℝ) < κ := by
    rw [hκdef]
    exact mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) hlgw0) hlglgpos
  -- three lower bounds on κ used throughout
  have hκlb1 : (2^41/20 : ℝ) * (r:ℝ)^3 ≤ κ := by
    rw [hκdef]
    have h1 : (2^41 : ℝ) * (r:ℝ)^3 * 1 * (1/20) ≤ 2^41 * (r:ℝ)^3 * lg w * lg (lg w) := by
      refine mul_le_mul (mul_le_mul le_rfl hlgw.le (by norm_num) (by positivity))
        hlglg20 (by norm_num) ?_
      have : (0:ℝ) ≤ (2^41 : ℝ) * (r:ℝ)^3 := by positivity
      exact mul_nonneg this hlgw0.le
    calc (2^41/20 : ℝ) * (r:ℝ)^3 = 2^41 * (r:ℝ)^3 * 1 * (1/20) := by ring
      _ ≤ _ := h1
  have hκlb2 : (2^41/20 : ℝ) * (r:ℝ)^3 * lg w ≤ κ := by
    rw [hκdef]
    have h1 : (2^41 : ℝ) * (r:ℝ)^3 * lg w * (1/20) ≤
        2^41 * (r:ℝ)^3 * lg w * lg (lg w) := by
      refine mul_le_mul_of_nonneg_left hlglg20 ?_
      have : (0:ℝ) ≤ (2^41 : ℝ) * (r:ℝ)^3 := by positivity
      exact mul_nonneg this hlgw0.le
    calc (2^41/20 : ℝ) * (r:ℝ)^3 * lg w = 2^41 * (r:ℝ)^3 * lg w * (1/20) := by ring
      _ ≤ _ := h1
  have hκlb3 : (2^41*9 : ℝ) * (r:ℝ) * lg w * lg (lg w) ≤ κ := by
    rw [hκdef]
    have h1 : (2^41 : ℝ) * (9*(r:ℝ)) ≤ 2^41 * (r:ℝ)^3 :=
      mul_le_mul_of_nonneg_left hr3r (by positivity)
    have h2 : (2^41 : ℝ) * (9*(r:ℝ)) * lg w ≤ 2^41 * (r:ℝ)^3 * lg w :=
      mul_le_mul_of_nonneg_right h1 hlgw0.le
    have h3 := mul_le_mul_of_nonneg_right h2 hlglgpos.le
    calc (2^41*9 : ℝ) * (r:ℝ) * lg w * lg (lg w)
        = (2^41 : ℝ) * (9*(r:ℝ)) * lg w * lg (lg w) := by ring
      _ ≤ _ := h3
  have hκ1 : (1:ℝ) ≤ κ := by
    have : (1:ℝ) ≤ (2^41/20 : ℝ) * 27 := by norm_num
    nlinarith [hκlb1, hr27]
  -- the weighted system
  set X := 𝓖.biUnion id with hX
  set σ := toWeight 𝓖 with hσdef
  set n := X.card with hn
  set Ncard := 𝓖.card with hNcard
  have hA₀pos : (0:ℝ) < (Ncard:ℝ) := by
    have := Finset.card_pos.mpr hne
    exact_mod_cast this
  have hκn : κ ≤ (n:ℝ) := kappa_le_ground hκpos.le hne hw' hu hsp
  -- schedule parameters
  set L := Nat.log 2 ⌈κ⌉₊ + Nat.log 2 r + 4 with hLdef
  set k₀ := Nat.log 2 w + 1 with hk₀def
  set t₀ := (2*L - 1) * k₀ with ht₀def
  set m := n / r with hmdef
  set m_bot := m - m / 2 with hmbotdef
  set s := (m / 2) / t₀ with hsdef
  have hL4 : 4 ≤ L := by omega
  -- κ ≤ 2^L and 8r ≤ 2^{2L}, by construction of L
  have hceil1 : 1 ≤ ⌈κ⌉₊ := Nat.one_le_ceil_iff.mpr hκpos
  have hκ2L : κ ≤ (2:ℝ)^L := by
    have h1 : κ ≤ (⌈κ⌉₊ : ℝ) := Nat.le_ceil κ
    have h2 : ⌈κ⌉₊ < 2^(Nat.log 2 ⌈κ⌉₊ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : (2:ℕ)^(Nat.log 2 ⌈κ⌉₊ + 1) ≤ 2^L :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc κ ≤ (⌈κ⌉₊ : ℝ) := h1
      _ ≤ ((2^(Nat.log 2 ⌈κ⌉₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2.le
      _ ≤ ((2^L : ℕ) : ℝ) := by exact_mod_cast h3
      _ = (2:ℝ)^L := by push_cast; rfl
  have h8r2L : 8*(r:ℝ) ≤ (2:ℝ)^(2*L) := by
    have h1 : r < 2^(Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
    have h2 : (8:ℕ)*r ≤ 2^(Nat.log 2 r + 4) := by
      calc (8:ℕ)*r ≤ 8 * 2^(Nat.log 2 r + 1) := Nat.mul_le_mul_left 8 h1.le
        _ = 2^(Nat.log 2 r + 4) := by rw [pow_add, pow_add]; ring
    have h3 : (2:ℕ)^(Nat.log 2 r + 4) ≤ 2^(2*L) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 8*(r:ℝ) = ((8*r : ℕ):ℝ) := by push_cast; ring
      _ ≤ ((2^(2*L) : ℕ):ℝ) := by exact_mod_cast le_trans h2 h3
      _ = (2:ℝ)^(2*L) := by push_cast; rfl
  -- upper bound on L
  have hlgκub : lg κ ≤ 82 + 3*lg r + 3*lg (lg w) := by
    have hfac : lg κ = lg ((2:ℝ)^41) + lg ((r:ℝ)^3) + lg (lg w) + lg (lg (lg w)) := by
      have hne1 : ((2:ℝ)^41 : ℝ) ≠ 0 := by positivity
      have hne2 : ((r:ℝ)^3 : ℝ) ≠ 0 := by positivity
      have hne3 : lg (w:ℝ) ≠ 0 := ne_of_gt hlgw0
      have hne4 : lg (lg (w:ℝ)) ≠ 0 := ne_of_gt hlglgpos
      have hne5 : (r:ℝ)^3 * (lg (w:ℝ) * lg (lg (w:ℝ))) ≠ 0 :=
        mul_ne_zero hne2 (mul_ne_zero hne3 hne4)
      have hassoc : κ = (2:ℝ)^41 * ((r:ℝ)^3 * (lg (w:ℝ) * lg (lg (w:ℝ)))) := by
        rw [hκdef]; ring
      rw [hassoc]
      simp only [lg]
      simp only [lg] at hne3 hne4 hne5
      rw [Real.logb_mul hne1 hne5,
        Real.logb_mul hne2 (mul_ne_zero hne3 hne4),
        Real.logb_mul hne3 hne4]
      ring
    have h41 : lg ((2:ℝ)^41) ≤ 82 := by
      rw [lg, Real.logb_pow]
      have := lg_two_le
      rw [lg] at this
      push_cast
      linarith
    have hr3lg : lg ((r:ℝ)^3) = 3 * lg r := by
      rw [lg, Real.logb_pow, lg]
      push_cast
      ring
    have hlast : lg (lg (lg w)) ≤ 2 * lg (lg w) := lg_le_double hlglgpos
    rw [hfac, hr3lg]
    linarith
  have hLub : (L:ℝ) ≤ 88 + 4*lg r + 3*lg (lg w) := by
    have h1 : (Nat.log 2 ⌈κ⌉₊ : ℝ) ≤ lg κ + 2 := by
      have h2 := natlog_le_lg hceil1
      have h3 : (⌈κ⌉₊ : ℝ) ≤ 2*κ := by
        have h4 := Nat.ceil_lt_add_one hκpos.le
        linarith [hκ1]
      have h5 : lg (⌈κ⌉₊:ℝ) ≤ lg (2*κ) := by
        refine lg_mono ?_ h3
        exact_mod_cast hceil1
      have h6 : lg (2*κ) = lg 2 + lg κ := by
        rw [lg, lg, lg, Real.logb_mul (by norm_num) (ne_of_gt hκpos)]
      linarith [lg_two_le]
    have h7 : (Nat.log 2 r : ℝ) ≤ lg r := natlog_le_lg (by omega)
    have h8 : (L:ℝ) = (Nat.log 2 ⌈κ⌉₊ : ℝ) + (Nat.log 2 r : ℝ) + 4 := by
      rw [hLdef]
      push_cast
      ring
    rw [h8]
    linarith [hlgκub]
  -- master inequality (M2): `1024 r² L² ≤ κ`
  have hL0 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg _
  have hM2 : 1024*(r:ℝ)^2*(L:ℝ)^2 ≤ κ := by
    have hLsq : (L:ℝ)^2 ≤ 23232 + 768*(r:ℝ) + 432*(lg w) := by
      have h1 : (L:ℝ)^2 ≤ (88 + 4*lg r + 3*lg (lg w))^2 := by
        refine pow_le_pow_left₀ hL0 hLub 2
      have h2 : (88 + 4*lg r + 3*lg (lg w))^2 ≤
          3*(88^2 + (4*lg r)^2 + (3*lg (lg w))^2) := by
        nlinarith [sq_nonneg (88 - 4*lg r), sq_nonneg (88 - 3*lg (lg w)),
          sq_nonneg (4*lg r - 3*lg (lg w))]
      have h3 : (4*lg r)^2 = 16*(lg r)^2 := by ring
      have h4 : (3*lg (lg w))^2 = 9*(lg (lg w))^2 := by ring
      calc (L:ℝ)^2 ≤ 3*(88^2 + (4*lg r)^2 + (3*lg (lg w))^2) := le_trans h1 h2
        _ = 23232 + 48*(lg r)^2 + 27*(lg (lg w))^2 := by rw [h3, h4]; ring
        _ ≤ 23232 + 48*(16*(r:ℝ)) + 27*(16*(lg w)) := by
            have := mul_le_mul_of_nonneg_left hlgrsq (by norm_num : (0:ℝ) ≤ 48)
            have := mul_le_mul_of_nonneg_left hlglgsq (by norm_num : (0:ℝ) ≤ 27)
            linarith
        _ = 23232 + 768*(r:ℝ) + 432*(lg w) := by ring
    have hmul : 1024*(r:ℝ)^2*(L:ℝ)^2 ≤
        1024*(r:ℝ)^2*(23232 + 768*(r:ℝ) + 432*(lg w)) := by
      refine mul_le_mul_of_nonneg_left hLsq (by positivity)
    have hpiece1 : 1024*23232*(r:ℝ)^2 ≤ κ/3 := by
      have h1 : 3*(1024*23232)*(r:ℝ)^2 ≤ (2^41/20)*(r:ℝ)^3 := by
        nlinarith [hr3, sq_nonneg (r:ℝ)]
      linarith [hκlb1]
    have hpiece2 : 1024*768*(r:ℝ)^3 ≤ κ/3 := by
      have h1 : 3*(1024*768)*(r:ℝ)^3 ≤ (2^41/20)*(r:ℝ)^3 := by
        nlinarith [hr27, pow_pos hrpos 3]
      linarith [hκlb1]
    have hpiece3 : 1024*432*(r:ℝ)^2*lg w ≤ κ/3 := by
      have h1 : 3*(1024*432)*(r:ℝ)^2*lg w ≤ (2^41/20)*(r:ℝ)^3*lg w := by
        have h2 : 3*(1024*432)*(r:ℝ)^2 ≤ (2^41/20)*(r:ℝ)^3 := by
          nlinarith [hr3, sq_nonneg (r:ℝ)]
        exact mul_le_mul_of_nonneg_right h2 hlgw0.le
      linarith [hκlb2]
    calc 1024*(r:ℝ)^2*(L:ℝ)^2
        ≤ 1024*(r:ℝ)^2*(23232 + 768*(r:ℝ) + 432*(lg w)) := hmul
      _ = 1024*23232*(r:ℝ)^2 + 1024*768*(r:ℝ)^3 + 1024*432*(r:ℝ)^2*lg w := by ring
      _ ≤ κ/3 + κ/3 + κ/3 := by linarith
      _ = κ := by ring
  -- master inequality (M1): `1024 r t₀ ≤ κ`
  have hk₀R : (k₀:ℝ) ≤ 2*lg w := by
    have h1 : (Nat.log 2 w : ℝ) ≤ lg w := natlog_le_lg (by omega)
    have h2 : (k₀:ℝ) = (Nat.log 2 w : ℝ) + 1 := by
      rw [hk₀def]; push_cast; ring
    rw [h2]
    linarith
  have ht₀R : (t₀:ℝ) ≤ 4*(L:ℝ)*lg w := by
    have h1 : t₀ ≤ 2*L*k₀ := by
      rw [ht₀def]
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : (t₀:ℝ) ≤ 2*(L:ℝ)*(k₀:ℝ) := by exact_mod_cast h1
    have h3 : 2*(L:ℝ)*(k₀:ℝ) ≤ 2*(L:ℝ)*(2*lg w) :=
      mul_le_mul_of_nonneg_left hk₀R (by positivity)
    calc (t₀:ℝ) ≤ 2*(L:ℝ)*(2*lg w) := le_trans h2 h3
      _ = 4*(L:ℝ)*lg w := by ring
  have hM1 : 1024*(r:ℝ)*(t₀:ℝ) ≤ κ := by
    have h1 : 1024*(r:ℝ)*(t₀:ℝ) ≤ 4096*(r:ℝ)*(L:ℝ)*lg w := by
      have := mul_le_mul_of_nonneg_left ht₀R
        (by positivity : (0:ℝ) ≤ 1024*(r:ℝ))
      calc 1024*(r:ℝ)*(t₀:ℝ) = 1024*(r:ℝ)*((t₀:ℝ)) := by ring
        _ ≤ 1024*(r:ℝ)*(4*(L:ℝ)*lg w) := this
        _ = 4096*(r:ℝ)*(L:ℝ)*lg w := by ring
    have h2 : 4096*(r:ℝ)*(L:ℝ)*lg w ≤
        4096*(r:ℝ)*lg w*(88 + 4*lg r + 3*lg (lg w)) := by
      have h3 := mul_le_mul_of_nonneg_left hLub
        (by positivity : (0:ℝ) ≤ 4096*(r:ℝ))
      have h4 : 4096*(r:ℝ)*(L:ℝ) ≤ 4096*(r:ℝ)*(88 + 4*lg r + 3*lg (lg w)) := h3
      calc 4096*(r:ℝ)*(L:ℝ)*lg w ≤
          4096*(r:ℝ)*(88 + 4*lg r + 3*lg (lg w))*lg w :=
            mul_le_mul_of_nonneg_right h4 hlgw0.le
        _ = 4096*(r:ℝ)*lg w*(88 + 4*lg r + 3*lg (lg w)) := by ring
    have hpa : 4096*88*(r:ℝ)*lg w ≤ κ/3 := by
      have h5 : 3*(4096*88)*(r:ℝ)*lg w ≤ (2^41/20)*(r:ℝ)^3*lg w := by
        have h6 : 3*(4096*88)*(r:ℝ) ≤ (2^41/20)*(r:ℝ)^3 := by
          nlinarith [hr3r, hrpos]
        exact mul_le_mul_of_nonneg_right h6 hlgw0.le
      linarith [hκlb2]
    have hpb : 4096*4*(r:ℝ)*lg w*lg r ≤ κ/3 := by
      have h5 : 4096*4*(r:ℝ)*lg w*lg r ≤ 4096*8*(r:ℝ)^2*lg w := by
        have h6 := mul_le_mul_of_nonneg_left hlgr2
          (by positivity : (0:ℝ) ≤ 4096*4*(r:ℝ)*lg w)
        calc 4096*4*(r:ℝ)*lg w*lg r = 4096*4*(r:ℝ)*lg w*(lg r) := by ring
          _ ≤ 4096*4*(r:ℝ)*lg w*(2*(r:ℝ)) := h6
          _ = 4096*8*(r:ℝ)^2*lg w := by ring
      have h7 : 3*(4096*8)*(r:ℝ)^2*lg w ≤ (2^41/20)*(r:ℝ)^3*lg w := by
        have h8 : 3*(4096*8)*(r:ℝ)^2 ≤ (2^41/20)*(r:ℝ)^3 := by
          nlinarith [hr3, sq_nonneg (r:ℝ)]
        exact mul_le_mul_of_nonneg_right h8 hlgw0.le
      linarith [hκlb2]
    have hpc : 4096*3*(r:ℝ)*lg w*lg (lg w) ≤ κ/3 := by
      have h5 : 3*(4096*3)*(r:ℝ)*lg w*lg (lg w) ≤ (2^41*9)*(r:ℝ)*lg w*lg (lg w) := by
        have h6 : (3*(4096*3) : ℝ) ≤ 2^41*9 := by norm_num
        have h7 : (0:ℝ) ≤ (r:ℝ)*lg w*lg (lg w) :=
          mul_nonneg (mul_nonneg hrpos.le hlgw0.le) hlglgpos.le
        nlinarith [h7]
      linarith [hκlb3]
    calc 1024*(r:ℝ)*(t₀:ℝ)
        ≤ 4096*(r:ℝ)*lg w*(88 + 4*lg r + 3*lg (lg w)) := le_trans h1 h2
      _ = 4096*88*(r:ℝ)*lg w + 4096*4*(r:ℝ)*lg w*lg r +
          4096*3*(r:ℝ)*lg w*lg (lg w) := by ring
      _ ≤ κ/3 + κ/3 + κ/3 := by linarith
      _ = κ := by ring
  -- ℕ-side facts about the schedule
  have ht₀pos : 0 < t₀ := by
    rw [ht₀def]
    exact Nat.mul_pos (by omega) (by omega)
  have hn512 : 512*r*t₀ ≤ n := by
    have hcast : ((512*r*t₀ : ℕ):ℝ) ≤ (n:ℝ) := by
      push_cast
      have h1 : (0:ℝ) ≤ (r:ℝ)*(t₀:ℝ) :=
        mul_nonneg hrpos.le (Nat.cast_nonneg _)
      nlinarith [hM1, hκn]
    exact_mod_cast hcast
  have hmpos512 : 512*t₀ ≤ m := by
    rw [hmdef, Nat.le_div_iff_mul_le (by omega : 0 < r)]
    calc 512*t₀*r = 512*r*t₀ := by ring
      _ ≤ n := hn512
  have hm2' : 256*t₀ ≤ m/2 := by omega
  have hs256 : 256 ≤ s := by
    rw [hsdef]
    calc 256 = 256*t₀/t₀ := by rw [Nat.mul_div_cancel _ ht₀pos]
      _ ≤ (m/2)/t₀ := Nat.div_le_div_right hm2'
  have hs1 : 1 ≤ s := by omega
  have hst : s*t₀ ≤ m/2 := by
    rw [hsdef]
    exact Nat.div_mul_le_self _ _
  have hbudget : s*t₀ + m_bot ≤ m := by
    rw [hmbotdef]
    omega
  have ht₀2L : 2*L - 1 ≤ t₀ := by
    rw [ht₀def]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have h2Lm4 : 2*L ≤ m/4 := by
    have h1 : 128*t₀ ≤ m/4 := by omega
    omega
  have hmb2L : 2*L < m_bot := by
    rw [hmbotdef]
    omega
  have hmbot4 : m/4 ≤ m_bot - 2*L := by
    rw [hmbotdef]
    omega
  -- real-side rate bounds
  have hm1R : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hnmR : (n:ℝ) ≤ 2*(r:ℝ)*(m:ℝ) := by
    have hdm := Nat.div_add_mod n r
    have hmod : n % r < r := Nat.mod_lt _ (by omega)
    have h2 : r*m + n%r = n := by
      rw [hmdef]
      exact hdm
    have h3 : n < r*m + r := by omega
    have h4 : (n:ℝ) < (r:ℝ)*(m:ℝ) + r := by exact_mod_cast h3
    have h5 : (r:ℝ) ≤ (r:ℝ)*(m:ℝ) := le_mul_of_one_le_right hrpos.le hm1R
    linarith
  have hsRpos : (0:ℝ) < (s:ℝ) := by exact_mod_cast (by omega : 0 < s)
  have ht₀Rpos : (0:ℝ) < (t₀:ℝ) := by exact_mod_cast ht₀pos
  have hm4t : (m:ℝ) ≤ 4*(t₀:ℝ)*(s:ℝ) := by
    have hdm := Nat.div_add_mod (m/2) t₀
    have hmod : (m/2) % t₀ < t₀ := Nat.mod_lt _ ht₀pos
    have h1 : t₀*s + (m/2)%t₀ = m/2 := by
      rw [hsdef]
      exact hdm
    have h3 : m ≤ 2*(t₀*s) + 2*t₀ + 1 := by omega
    have h4 : (m:ℝ) ≤ 2*((t₀:ℝ)*(s:ℝ)) + 2*(t₀:ℝ) + 1 := by exact_mod_cast h3
    have h6 : (256:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs256
    nlinarith [ht₀Rpos]
  have hnst : 8*(n:ℝ)/(s:ℝ) ≤ 64*(r:ℝ)*(t₀:ℝ) := by
    rw [div_le_iff₀ hsRpos]
    have hhint := mul_le_mul_of_nonneg_left hm4t
      (by positivity : (0:ℝ) ≤ 2*(r:ℝ))
    nlinarith [hnmR]
  -- the round condition hK1
  have hK1 : ∀ v : ℕ, 2*L < v →
      (8*(n:ℝ)/(s:ℝ))^v * (Ncard:ℝ) * 2^(v+1) * 2^v ≤
        (1/(4*(r:ℝ))) * (Ncard:ℝ) * κ^(v - v/L) := by
    intro v hv
    have hF0 : (0:ℝ) ≤ 8*(n:ℝ)/(s:ℝ) := by positivity
    have h16F : 16*(8*(n:ℝ)/(s:ℝ)) ≤ κ := by nlinarith [hM1, hnst]
    have hsplit : κ^(v - v/L) * κ^(v/L) = κ^v := by
      rw [← pow_add]
      congr 1
      have := Nat.div_le_self v L
      omega
    have hκvL : κ^(v/L) ≤ (2:ℝ)^v := by
      calc κ^(v/L) ≤ ((2:ℝ)^L)^(v/L) := pow_le_pow_left₀ hκpos.le hκ2L _
        _ = (2:ℝ)^(L*(v/L)) := by rw [← pow_mul]
        _ ≤ (2:ℝ)^v := by
            refine pow_le_pow_right₀ one_le_two ?_
            calc L*(v/L) = (v/L)*L := by ring
              _ ≤ v := Nat.div_mul_le_self _ _
    have hmain : 4*(r:ℝ)*((8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1)) * 2^v ≤ κ^v := by
      have hκF : (16*(8*(n:ℝ)/(s:ℝ)))^v ≤ κ^v :=
        pow_le_pow_left₀ (by positivity) h16F v
      have hexp : (16*(8*(n:ℝ)/(s:ℝ)))^v = (8*(n:ℝ)/(s:ℝ))^v * 2^(4*v) := by
        rw [mul_pow]
        rw [show (16:ℝ) = 2^(4:ℕ) from by norm_num, ← pow_mul]
        ring
      have h2L : (2:ℝ)^(2*L) ≤ 2^(v-1) :=
        pow_le_pow_right₀ one_le_two (by omega)
      have hcalc : 4*(r:ℝ)*(2:ℝ)^(2*v+1)*2^v ≤ 2^(4*v) := by
        have h8r : 8*(r:ℝ) ≤ (2:ℝ)^(v-1) := le_trans h8r2L h2L
        have hpowid : (2:ℝ)^(v-1) * 2^(2*v+1) * 2^v = 2^(4*v) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        have hp : (0:ℝ) ≤ (2:ℝ)^(2*v+1)*2^v := by positivity
        have h9 := mul_le_mul_of_nonneg_right h8r hp
        calc 4*(r:ℝ)*(2:ℝ)^(2*v+1)*2^v
            = (8*(r:ℝ))*((2:ℝ)^(2*v+1)*2^v)/2 := by ring
          _ ≤ ((2:ℝ)^(v-1))*((2:ℝ)^(2*v+1)*2^v)/2 := by linarith
          _ = 2^(4*v)/2 := by
              rw [show (2:ℝ)^(v-1)*((2:ℝ)^(2*v+1)*2^v) =
                2^(v-1) * 2^(2*v+1) * 2^v from by ring, hpowid]
          _ ≤ 2^(4*v) := by
              have hq : (0:ℝ) ≤ (2:ℝ)^(4*v) := by positivity
              linarith
      calc 4*(r:ℝ)*((8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1)) * 2^v
          = (8*(n:ℝ)/(s:ℝ))^v * (4*(r:ℝ)*(2:ℝ)^(2*v+1)*2^v) := by ring
        _ ≤ (8*(n:ℝ)/(s:ℝ))^v * 2^(4*v) :=
            mul_le_mul_of_nonneg_left hcalc (by positivity)
        _ = (16*(8*(n:ℝ)/(s:ℝ)))^v := hexp.symm
        _ ≤ κ^v := hκF
    have hdiv : 4*(r:ℝ)*((8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1)) ≤ κ^(v - v/L) := by
      have h2v : (0:ℝ) < (2:ℝ)^v := by positivity
      refine le_of_mul_le_mul_right ?_ h2v
      calc 4*(r:ℝ)*((8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1)) * 2^v ≤ κ^v := hmain
        _ = κ^(v-v/L) * κ^(v/L) := hsplit.symm
        _ ≤ κ^(v-v/L) * 2^v :=
            mul_le_mul_of_nonneg_left hκvL (pow_nonneg hκpos.le _)
    have h4r : (0:ℝ) < 4*(r:ℝ) := by positivity
    rw [show (1/(4*(r:ℝ))) * (Ncard:ℝ) * κ^(v - v/L) =
      (Ncard:ℝ) * (κ^(v - v/L)/(4*(r:ℝ))) from by ring,
      show (8*(n:ℝ)/(s:ℝ))^v * (Ncard:ℝ) * 2^(v+1) * 2^v =
      (Ncard:ℝ) * ((8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1)) from by
        rw [show (2:ℝ)^(2*v+1) = 2^(v+1)*2^v from by
          rw [← pow_add]; congr 1; omega]
        ring]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [le_div_iff₀ h4r]
    calc (8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1) * (4*(r:ℝ))
        = 4*(r:ℝ)*((8*(n:ℝ)/(s:ℝ))^v * 2^(2*v+1)) := by ring
      _ ≤ κ^(v-v/L) := hdiv
  -- the bottom conditions hK2, hK3
  have hq4pos : (0:ℝ) < ((m_bot - 2*L : ℕ):ℝ) := by
    have : 0 < m_bot - 2*L := by omega
    exact_mod_cast this
  have hm4R : ((m/4 : ℕ):ℝ) ≤ ((m_bot - 2*L : ℕ):ℝ) := by exact_mod_cast hmbot4
  have hm4pos : (0:ℝ) < ((m/4 : ℕ):ℝ) := by
    have : 0 < m/4 := by omega
    exact_mod_cast this
  have hnm4 : (n:ℝ) ≤ 9*(r:ℝ)*((m/4:ℕ):ℝ) := by
    have h1 : m ≤ 4*(m/4) + 3 := by omega
    have h2 : (m:ℝ) ≤ 4*((m/4:ℕ):ℝ) + 3 := by exact_mod_cast h1
    have h3 : (6:ℝ) ≤ ((m/4:ℕ):ℝ) := by
      exact_mod_cast (by omega : 6 ≤ m/4)
    have h4 : (m:ℝ) ≤ (9/2)*((m/4:ℕ):ℝ) := by linarith
    nlinarith [hnmR, hrpos, hm4pos]
  have hrL12 : (12:ℝ) ≤ (r:ℝ)*(L:ℝ) := by
    have hL4R : (4:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL4
    nlinarith
  have hK3 : 4*(L:ℝ)*(n:ℝ) ≤ κ*((m_bot - 2*L : ℕ):ℝ) := by
    have hκ36 : 36*(r:ℝ)*(L:ℝ) ≤ κ := by
      have h1 : (0:ℝ) ≤ (r:ℝ)*(L:ℝ) := by positivity
      nlinarith [hM2, hrL12, mul_nonneg (sub_nonneg.mpr hrL12) h1]
    have h1 : 4*(L:ℝ)*(n:ℝ) ≤ 36*(r:ℝ)*(L:ℝ)*((m/4:ℕ):ℝ) := by
      have h2 := mul_le_mul_of_nonneg_left hnm4
        (by positivity : (0:ℝ) ≤ 4*(L:ℝ))
      calc 4*(L:ℝ)*(n:ℝ) ≤ 4*(L:ℝ)*(9*(r:ℝ)*((m/4:ℕ):ℝ)) := h2
        _ = 36*(r:ℝ)*(L:ℝ)*((m/4:ℕ):ℝ) := by ring
    calc 4*(L:ℝ)*(n:ℝ) ≤ 36*(r:ℝ)*(L:ℝ)*((m/4:ℕ):ℝ) := h1
      _ ≤ κ*((m/4:ℕ):ℝ) := mul_le_mul_of_nonneg_right hκ36 hm4pos.le
      _ ≤ κ*((m_bot-2*L:ℕ):ℝ) := mul_le_mul_of_nonneg_left hm4R hκpos.le
  have hK2 : 16*(L:ℝ)^2*(n:ℝ)*(Ncard:ℝ) ≤
      (1/(4*(r:ℝ)))*(Ncard:ℝ)*κ*((m_bot-2*L:ℕ):ℝ) := by
    have h2 : 64*(r:ℝ)*((L:ℝ)^2*(n:ℝ)) ≤ 576*(r:ℝ)^2*(L:ℝ)^2*((m/4:ℕ):ℝ) := by
      have h2a := mul_le_mul_of_nonneg_left hnm4
        (by positivity : (0:ℝ) ≤ 64*(r:ℝ)*(L:ℝ)^2)
      calc 64*(r:ℝ)*((L:ℝ)^2*(n:ℝ)) = 64*(r:ℝ)*(L:ℝ)^2*(n:ℝ) := by ring
        _ ≤ 64*(r:ℝ)*(L:ℝ)^2*(9*(r:ℝ)*((m/4:ℕ):ℝ)) := h2a
        _ = 576*(r:ℝ)^2*(L:ℝ)^2*((m/4:ℕ):ℝ) := by ring
    have h3 : 576*(r:ℝ)^2*(L:ℝ)^2 ≤ κ := by
      have h3a : (0:ℝ) ≤ (r:ℝ)^2*(L:ℝ)^2 := by positivity
      nlinarith [hM2]
    have h1 : 64*(r:ℝ)*((L:ℝ)^2*(n:ℝ)) ≤ κ*((m/4:ℕ):ℝ) := by
      calc 64*(r:ℝ)*((L:ℝ)^2*(n:ℝ)) ≤ 576*(r:ℝ)^2*(L:ℝ)^2*((m/4:ℕ):ℝ) := h2
        _ ≤ κ*((m/4:ℕ):ℝ) := mul_le_mul_of_nonneg_right h3 hm4pos.le
    have h4r : (0:ℝ) < 4*(r:ℝ) := by positivity
    rw [show (1/(4*(r:ℝ)))*(Ncard:ℝ)*κ*((m_bot-2*L:ℕ):ℝ) =
      (Ncard:ℝ)*(κ*((m_bot-2*L:ℕ):ℝ)/(4*(r:ℝ))) from by ring,
      show 16*(L:ℝ)^2*(n:ℝ)*(Ncard:ℝ) = (Ncard:ℝ)*(16*(L:ℝ)^2*(n:ℝ)) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [le_div_iff₀ h4r]
    calc 16*(L:ℝ)^2*(n:ℝ)*(4*(r:ℝ)) = 64*(r:ℝ)*((L:ℝ)^2*(n:ℝ)) := by ring
      _ ≤ κ*((m/4:ℕ):ℝ) := h1
      _ ≤ κ*((m_bot-2*L:ℕ):ℝ) := mul_le_mul_of_nonneg_left hm4R hκpos.le
  -- the fuel bound
  have hL1R : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have h2L1 : (0:ℝ) < 2*(L:ℝ) - 1 := by linarith
  have hfuel : (w':ℝ) ≤ 2*(L:ℝ)*((2*(L:ℝ))/(2*(L:ℝ)-1))^t₀ := by
    have hQ0 : (0:ℝ) ≤ (2*(L:ℝ))/(2*(L:ℝ)-1) :=
      div_nonneg (by positivity) h2L1.le
    have hQ2 : (2:ℝ) ≤ ((2*(L:ℝ))/(2*(L:ℝ)-1))^(2*L-1) := by
      have hx : (-2:ℝ) ≤ 1/(2*(L:ℝ)-1) := by
        have : (0:ℝ) ≤ 1/(2*(L:ℝ)-1) := by positivity
        linarith
      have hb := one_add_mul_le_pow hx (2*L-1)
      have hcast : ((2*L-1 : ℕ):ℝ) = 2*(L:ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*L)]
        push_cast
        ring
      rw [hcast] at hb
      have hone : (2*(L:ℝ)-1)*(1/(2*(L:ℝ)-1)) = 1 := by
        field_simp
      have hQeq : (1:ℝ) + 1/(2*(L:ℝ)-1) = (2*(L:ℝ))/(2*(L:ℝ)-1) := by
        field_simp
        ring
      rw [hQeq] at hb
      linarith
    have hpw : ((2*(L:ℝ))/(2*(L:ℝ)-1))^t₀ =
        (((2*(L:ℝ))/(2*(L:ℝ)-1))^(2*L-1))^k₀ := by
      rw [← pow_mul, ht₀def]
    have h2k : (w:ℝ) < (2:ℝ)^k₀ := by
      have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) w
      have hcast : ((2^(Nat.log 2 w + 1) : ℕ):ℝ) = (2:ℝ)^k₀ := by
        rw [hk₀def]
        push_cast
        rfl
      calc (w:ℝ) < ((2^(Nat.log 2 w + 1) : ℕ):ℝ) := by exact_mod_cast h1
        _ = (2:ℝ)^k₀ := hcast
    have h2kQ : (2:ℝ)^k₀ ≤ (((2*(L:ℝ))/(2*(L:ℝ)-1))^(2*L-1))^k₀ :=
      pow_le_pow_left₀ (by norm_num) hQ2 k₀
    have hw'R : (w':ℝ) ≤ (w:ℝ) := by exact_mod_cast hw'w
    have hQt0 : (0:ℝ) ≤ ((2*(L:ℝ))/(2*(L:ℝ)-1))^t₀ := pow_nonneg hQ0 _
    calc (w':ℝ) ≤ (w:ℝ) := hw'R
      _ ≤ (2:ℝ)^k₀ := h2k.le
      _ ≤ (((2*(L:ℝ))/(2*(L:ℝ)-1))^(2*L-1))^k₀ := h2kQ
      _ = ((2*(L:ℝ))/(2*(L:ℝ)-1))^t₀ := hpw.symm
      _ ≤ 2*(L:ℝ)*((2*(L:ℝ))/(2*(L:ℝ)-1))^t₀ :=
          le_mul_of_one_le_left hQt0 (by linarith)
  -- run the iteration (opaquify the schedule parameters for fast unification)
  clear_value κ X n Ncard L k₀ t₀ m m_bot s
  have hquarter : (0:ℝ) ≤ 1/(4*(r:ℝ)) := by positivity
  have htotX : (Ncard:ℝ) ≤ (wTotal X σ : ℝ) := by
    have heq : wTotal X σ = Ncard := by
      rw [hX, hσdef, hNcard]
      exact toWeight_total 𝓖
    rw [heq]
  have hAinv0 : (Ncard:ℝ)*(1 - (1/2:ℝ)^(w'+1)) ≤ (Ncard:ℝ) := by
    have h1 : (0:ℝ) ≤ (1/2:ℝ)^(w'+1) := by positivity
    nlinarith [hA₀pos]
  have hmn' : m ≤ X.card := by
    rw [← hn, hmdef]
    exact Nat.div_le_self _ _
  have hfailB := iterate_le (L := L) (s := s) (m_bot := m_bot) (n₀ := n)
    (A₀ := (Ncard:ℝ)) (M := (Ncard:ℝ)) (κ := κ)
    (ε := 1/(4*(r:ℝ))) (εbot := 1/(4*(r:ℝ)))
    (by omega) hs1 hmb2L hA₀pos hA₀pos.le hκ1 hquarter hquarter
    hK1 hK2 hK3 t₀ X σ w' (Ncard:ℝ) m
    (by rw [hX, hσdef]; exact toWeight_bounded hu)
    (by
      have h := toWeight_linkBounded (κ := κ) hsp
      rw [hX, hσdef, hNcard]
      exact h)
    htotX hAinv0 hfuel hw' hbudget hmn' (le_of_eq hn.symm)
  -- the failure fraction is below `1/(2r)`
  have hCpos : (0:ℝ) < ((n.choose m : ℕ):ℝ) := by
    have h1 : m ≤ n := by rw [hmdef]; exact Nat.div_le_self _ _
    have : 0 < n.choose m := Nat.choose_pos h1
    exact_mod_cast this
  have hfail2 : (failCount X σ m : ℝ) * (r:ℝ) < ((n.choose m):ℝ) := by
    have h1 : (failCount X σ m : ℝ) ≤ (1/(2*(r:ℝ)))*((n.choose m):ℝ) := by
      refine le_trans hfailB ?_
      have hCX : ((X.card.choose m : ℕ):ℝ) = ((n.choose m):ℝ) := by rw [← hn]
      rw [hCX]
      refine mul_le_mul_of_nonneg_right ?_ hCpos.le
      have h2 : (0:ℝ) ≤ (1/2:ℝ)^w' := by positivity
      have h3 : (1/(4*(r:ℝ)))*(1-(1/2:ℝ)^w') ≤ 1/(4*(r:ℝ)) := by
        nlinarith [hquarter]
      have h4 : 1/(4*(r:ℝ)) + 1/(4*(r:ℝ)) = 1/(2*(r:ℝ)) := by
        field_simp
        ring
      linarith
    have h4 : (failCount X σ m : ℝ)*(r:ℝ) ≤ (1/2)*((n.choose m):ℝ) := by
      have h5 := mul_le_mul_of_nonneg_right h1 hrpos.le
      calc (failCount X σ m:ℝ)*(r:ℝ)
          ≤ (1/(2*(r:ℝ)))*((n.choose m):ℝ)*(r:ℝ) := h5
        _ = (1/2)*((n.choose m):ℝ) := by
            field_simp
    linarith [hCpos]
  -- extract `r` pairwise disjoint members
  have hrm : r*m ≤ X.card := by
    rw [← hn, hmdef, mul_comm]
    exact Nat.div_mul_le_self n r
  have hlow := coveredTuples_lower σ m r X hrm
  have hprodpos : (0:ℝ) < ((∏ i ∈ range r, (X.card - i*m).choose m : ℕ):ℝ) := by
    have hp : 0 < ∏ i ∈ range r, (X.card - i*m).choose m := by
      refine Finset.prod_pos fun i hi => ?_
      rw [Finset.mem_range] at hi
      refine Nat.choose_pos ?_
      have h1 : (i+1)*m ≤ r*m := Nat.mul_le_mul_right m (by omega)
      have h2 : (i+1)*m = i*m + m := by ring
      omega
    exact_mod_cast hp
  have h1r : (0:ℝ) < 1 - (r:ℝ)*(failCount X σ m : ℝ)/((X.card.choose m):ℝ) := by
    have hCX : (0:ℝ) < ((X.card.choose m):ℝ) := by rw [← hn]; exact hCpos
    rw [sub_pos, div_lt_one hCX]
    calc (r:ℝ)*(failCount X σ m:ℝ) = (failCount X σ m:ℝ)*(r:ℝ) := by ring
      _ < ((n.choose m):ℝ) := hfail2
      _ = ((X.card.choose m):ℝ) := by rw [← hn]
  have hct : 0 < coveredTuples σ m X r := by
    by_contra hcon
    have h0 : coveredTuples σ m X r = 0 := by omega
    have h2 := hlow
    rw [h0] at h2
    have h3 := mul_pos hprodpos h1r
    rw [Nat.cast_zero] at h2
    linarith
  have hσne : ∀ S, σ S ≠ 0 → S.Nonempty := by
    intro S hS
    rw [hσdef] at hS
    simp only [toWeight] at hS
    by_cases h : S ∈ 𝓖
    · have hcard := hu h
      exact Finset.card_pos.mp (by omega)
    · rw [if_neg h] at hS
      exact absurd rfl hS
  obtain ⟨𝒟, h𝒟card, h𝒟mem, h𝒟pd⟩ :=
    exists_disjoint_of_coveredTuples_pos σ m hσne r X hct
  refine ⟨𝒟, ?_, h𝒟card, h𝒟pd⟩
  intro S hS
  have h1 := (h𝒟mem S hS).1
  rw [hσdef] at h1
  simp only [toWeight] at h1
  by_cases h : S ∈ 𝓖
  · exact h
  · rw [if_neg h] at h1
    exact absurd rfl h1

end SpreadCore

end Sunflower

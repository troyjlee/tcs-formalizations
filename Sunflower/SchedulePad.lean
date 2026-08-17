/-
# The schedule chase, re-run on the padded bottom

`PadBottom.iterate_le_janson_pad` improves the bottom condition by one factor `L`:
`log(2/εbot) ≤ A₀·κ·p/(32·M·L)` where the size-class route needs `A₀·κ·p/(64·M·L²)`. This file
re-runs the assembly and the schedule chase on it. Everything else — the schedule itself, the
round condition, the fuel, the budget split, the two bridges — is unchanged, so the three
conditions become

  `128·L ≤ κa`,     **`1024·L·log(8/b) ≤ κa`**,     `4096·L·(log₂w + 1) ≤ κa`,

with the middle one linear in `L` where it used to be quadratic. `KappaZeroPad.lean` exploits
this improvement to prove an explicit constant with fixed-`a,b` shape
`O(log w·log log w)`; the third condition has size `L·log₂w`.
-/
import Sunflower.PadBottom
import Sunflower.Schedule

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-- **ALWZ Theorem 2.5, schedule form, on the padded bottom.** A `κ`-spread `w'`-uniform family, run through the
width-schedule iteration on the Janson bottom with a schedule meeting the conditions, is
`(a, b)`-satisfying.

Identical to `Satisfying.isSatisfying_of_isSpread_iterated` except for `hS2`, which is one
factor `L` cheaper because the bottom is `PadBottom.iterate_le_janson_pad`. -/
theorem isSatisfying_of_isSpread_iterated_pad {𝓖 : Finset (Finset α)} {w' : ℕ}
    {κ a p b ε εbot : ℝ} {L s m_bot t₀ m : ℕ}
    (hu : IsUniform w' 𝓖) (hne : 𝓖.Nonempty) (hsp : IsSpread κ 𝓖) (hw' : 1 ≤ w')
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * ((𝓖.biUnion id).card : ℝ) / s) ^ v * (𝓖.card : ℝ) * 2 ^ (v + 1) * 2 ^ v
        ≤ ε * (𝓖.card : ℝ) * κ ^ (v - v / L))
    (hS1 : 4 * (L : ℝ) ≤ κ * p)
    (hS2 : Real.log (2 / εbot) ≤ κ * p / (32 * (L : ℝ)))
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
      ≤ (𝓖.card : ℝ) * κ * p / (32 * (𝓖.card : ℝ) * (L : ℝ)) := by
    refine le_trans hS2 (le_of_eq ?_)
    have hNne : (𝓖.card : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
  have hfail := iterate_le_janson_pad (L := L) (s := s) (m_bot := m_bot) (n₀ := X.card)
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


/-- **Theorem 2.5 with the schedule picked, on the padded bottom.** A `κ`-spread `w'`-uniform family is
`(a,b)`-satisfying, provided `κ` clears the three size conditions.

Everything else — the schedule, the round condition, the fuel, the budget split, the two
bridges — is discharged here. -/
theorem isSatisfying_of_isSpread_of_kappa_pad {𝓖 : Finset (Finset α)} {w w' : ℕ} {κ a b : ℝ}
    (hu : IsUniform w' 𝓖) (hne : 𝓖.Nonempty) (hsp : IsSpread κ 𝓖)
    (hw' : 1 ≤ w') (hw'w : w' ≤ w) (_hw2 : 2 ≤ w)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hH1 : 128 * (schedL κ b : ℝ) ≤ κ * a)
    (hH2 : 1024 * (schedL κ b : ℝ) * Real.log (8 / b) ≤ κ * a)
    (hH3 : 4096 * (schedL κ b : ℝ) * ((Nat.log 2 w : ℝ) + 1) ≤ κ * a) :
    IsSatisfying a b (𝓖.biUnion id) 𝓖 := by
  classical
  set L := schedL κ b with hLdef
  have hL4 : 4 ≤ L := four_le_schedL κ b
  have hLR : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hκ512 : 512 ≤ κ := by nlinarith [hH1, hLR, ha1, ha]
  have hκ1 : (1 : ℝ) ≤ κ := by linarith
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hκ2L : κ ≤ (2 : ℝ) ^ L := hLdef ▸ le_two_pow_schedL hκ0
  have h16b : 16 / b ≤ (2 : ℝ) ^ L := hLdef ▸ le_two_pow_schedL' hb0
  -- the ground set
  set X := 𝓖.biUnion id with hX
  set n := X.card with hn
  have hκn : κ ≤ (n : ℝ) := kappa_le_ground hκ0.le hne hw' hu hsp
  have hnR : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hκ0 hκn
  have han : κ * a ≤ a * (n : ℝ) := by nlinarith [hκn, ha]
  -- the schedule
  set k₀ := Nat.log 2 w + 1 with hk₀
  set P := L * k₀ with hP
  set t₀ := (2 * L - 1) * k₀ with ht₀
  set m := ⌊a * (n : ℝ) / 4⌋₊ with hm
  set m_bot := m - m / 2 with hmbot
  set s := (m / 2) / t₀ with hs
  have hk₀1 : 1 ≤ k₀ := by rw [hk₀]; omega
  have hLP : L ≤ P := by rw [hP]; exact Nat.le_mul_of_pos_right _ (by omega)
  have ht₀P : t₀ ≤ 2 * P := by
    rw [ht₀, hP, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)
  have ht₀pos : 0 < t₀ := by rw [ht₀]; exact Nat.mul_pos (by omega) (by omega)
  have ht₀R : (0 : ℝ) < (t₀ : ℝ) := by exact_mod_cast ht₀pos
  have ht₀1 : (1 : ℝ) ≤ (t₀ : ℝ) := by exact_mod_cast ht₀pos
  have hPR : ((P : ℕ) : ℝ) = (L : ℝ) * (k₀ : ℝ) := by rw [hP]; push_cast; ring
  have hk₀R : ((k₀ : ℕ) : ℝ) = (Nat.log 2 w : ℝ) + 1 := by rw [hk₀]; push_cast; ring
  have hPκ : 4096 * ((P : ℕ) : ℝ) ≤ κ * a := by
    rw [hPR]
    have : 4096 * (L : ℝ) * ((k₀ : ℕ) : ℝ) ≤ κ * a := by rw [hk₀R]; exact hH3
    linarith [this]
  have hPpos : (1 : ℝ) ≤ ((P : ℕ) : ℝ) := by
    have : 1 ≤ P := le_trans (by omega) hLP
    exact_mod_cast this
  -- the budget `m`
  have hmR : (m : ℝ) ≤ a * (n : ℝ) / 4 := Nat.floor_le (by positivity)
  have hmR' : a * (n : ℝ) / 4 - 1 ≤ (m : ℝ) := by
    have := Nat.sub_one_lt_floor (a * (n : ℝ) / 4)
    linarith
  have hmP : 512 * P ≤ m := by
    have h1 : 4096 * ((P : ℕ) : ℝ) ≤ a * (n : ℝ) := le_trans hPκ han
    have h2 : (512 : ℝ) * ((P : ℕ) : ℝ) ≤ (m : ℝ) := by linarith [hmR', hPpos]
    exact_mod_cast h2
  -- the ℕ-side schedule facts
  have hs1 : 1 ≤ s := by
    rw [hs, Nat.one_le_div_iff ht₀pos]
    omega
  have hmb2L : 2 * L < m_bot := by rw [hmbot]; omega
  have hbud : s * t₀ + m_bot ≤ m := by
    have hst : s * t₀ ≤ m / 2 := by rw [hs]; exact Nat.div_mul_le_self _ _
    rw [hmbot]; omega
  have hmn : m ≤ n := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by nlinarith [hmR, ha1, hnR, ha.le]
    exact_mod_cast h1
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  -- the inner sampling parameter
  have hp0 : (0 : ℝ) < a / 32 := by positivity
  have hp1 : a / 32 ≤ 1 := by linarith
  -- `hS3` : `2·p·n ≤ m_bot`
  have hmbotR : (m : ℝ) / 2 - 1 ≤ (m_bot : ℝ) := by
    have h1 : (m : ℝ) ≤ 2 * ((m_bot : ℕ) : ℝ) := by
      have h2 : m ≤ 2 * m_bot := by rw [hmbot]; omega
      exact_mod_cast h2
    linarith
  have hS3 : 2 * ((a / 32) * (n : ℝ)) ≤ (m_bot : ℝ) := by
    have h2 : (8 : ℝ) ≤ a * (n : ℝ) := by linarith [hPκ, han, hPpos]
    have h3 : 2 * ((a / 32) * (n : ℝ)) = a * (n : ℝ) / 16 := by ring
    rw [h3]
    linarith [hmR', hmbotR]
  -- `hS1`, `hS2`
  have hS1 : 4 * (L : ℝ) ≤ κ * (a / 32) := by
    have h1 : κ * (a / 32) = κ * a / 32 := by ring
    rw [h1]; linarith
  have hlogb : 0 < Real.log (8 / b) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hb0]; linarith
  have hS2 : Real.log (2 / (b / 4)) ≤ κ * (a / 32) / (32 * (L : ℝ)) := by
    have hrw : (2 : ℝ) / (b / 4) = 8 / b := by
      rw [div_div_eq_mul_div]
      norm_num
    rw [hrw, le_div_iff₀ (by positivity)]
    have hexp : κ * (a / 32) = κ * a / 32 := by ring
    rw [hexp]
    nlinarith [hH2, hLR]
  -- the round condition's ratio bound `16·(8n/s) ≤ κ`
  have hF : 16 * (8 * (n : ℝ) / (s : ℝ)) ≤ κ := by
    have hdm : t₀ * s + (m / 2) % t₀ = m / 2 := by rw [hs]; exact Nat.div_add_mod (m / 2) t₀
    have hmod : (m / 2) % t₀ < t₀ := Nat.mod_lt _ ht₀pos
    have h2 : m ≤ 2 * (t₀ * s) + 2 * t₀ + 1 := by omega
    have h3 : (m : ℝ) ≤ 2 * ((t₀ : ℝ) * (s : ℝ)) + 2 * (t₀ : ℝ) + 1 := by exact_mod_cast h2
    have hsge : a * (n : ℝ) ≤ 8 * (t₀ : ℝ) * ((s : ℝ) + 2) := by
      nlinarith [h3, hmR', ht₀1]
    have ht₀PR : (t₀ : ℝ) ≤ 2 * ((P : ℕ) : ℝ) := by exact_mod_cast ht₀P
    have hκa : 2048 * (t₀ : ℝ) ≤ κ * a := by nlinarith [hPκ, ht₀PR]
    have h5 : 2048 * (t₀ : ℝ) * (n : ℝ) ≤ κ * a * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hκa hnR.le
    have hmul : κ * (a * (n : ℝ)) ≤ κ * (8 * (t₀ : ℝ) * ((s : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hsge hκ0.le
    have h6 : (t₀ : ℝ) * (2048 * (n : ℝ)) ≤ (t₀ : ℝ) * (8 * κ * (s : ℝ) + 16 * κ) := by
      nlinarith [h5, hmul]
    have h7 : 2048 * (n : ℝ) ≤ 8 * κ * (s : ℝ) + 16 * κ := le_of_mul_le_mul_left h6 ht₀R
    have hgoal : 16 * (8 * (n : ℝ) / (s : ℝ)) = 128 * (n : ℝ) / (s : ℝ) := by ring
    rw [hgoal, div_le_iff₀ hsR]
    nlinarith [h7, hκn, hnR]
  -- the round condition
  have hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * (n : ℝ) / (s : ℝ)) ^ v * (𝓖.card : ℝ) * 2 ^ (v + 1) * 2 ^ v
        ≤ (b / 4) * (𝓖.card : ℝ) * κ ^ (v - v / L) := by
    intro v hv
    have hsplit : κ ^ (v - v / L) * κ ^ (v / L) = κ ^ v := by
      rw [← pow_add]
      congr 1
      have := Nat.div_le_self v L
      omega
    have hκvL : κ ^ (v / L) ≤ (2 : ℝ) ^ v := by
      calc κ ^ (v / L) ≤ ((2 : ℝ) ^ L) ^ (v / L) := pow_le_pow_left₀ hκ0.le hκ2L _
        _ = (2 : ℝ) ^ (L * (v / L)) := by rw [← pow_mul]
        _ ≤ (2 : ℝ) ^ v := by
            refine pow_le_pow_right₀ one_le_two ?_
            calc L * (v / L) = (v / L) * L := by ring
              _ ≤ v := Nat.div_mul_le_self _ _
    have h8b : 8 / b ≤ (2 : ℝ) ^ (v - 1) := by
      have hLv : (2 : ℝ) ^ L ≤ 2 ^ (v - 1) := pow_le_pow_right₀ one_le_two (by omega)
      have h16 : 8 / b ≤ 16 / b := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith [h16b, hLv]
    have hmain : (4 / b) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)) * 2 ^ v
        ≤ κ ^ v := by
      have hκF : (16 * (8 * (n : ℝ) / (s : ℝ))) ^ v ≤ κ ^ v :=
        pow_le_pow_left₀ (by positivity) hF v
      have hexp : (16 * (8 * (n : ℝ) / (s : ℝ))) ^ v
          = (8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (4 * v) := by
        rw [mul_pow, show (16 : ℝ) = 2 ^ (4 : ℕ) from by norm_num, ← pow_mul]
        ring
      have hcalc : (4 / b) * (2 : ℝ) ^ (2 * v + 1) * 2 ^ v ≤ 2 ^ (4 * v) := by
        have hpowid : (2 : ℝ) ^ (v - 1) * 2 ^ (2 * v + 1) * 2 ^ v = 2 ^ (4 * v) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        have hpp : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * v + 1) * 2 ^ v := by positivity
        have h9 := mul_le_mul_of_nonneg_right h8b hpp
        calc (4 / b) * (2 : ℝ) ^ (2 * v + 1) * 2 ^ v
            = (8 / b) * ((2 : ℝ) ^ (2 * v + 1) * 2 ^ v) / 2 := by ring
          _ ≤ ((2 : ℝ) ^ (v - 1)) * ((2 : ℝ) ^ (2 * v + 1) * 2 ^ v) / 2 := by linarith
          _ = 2 ^ (4 * v) / 2 := by
              rw [show (2 : ℝ) ^ (v - 1) * ((2 : ℝ) ^ (2 * v + 1) * 2 ^ v) =
                2 ^ (v - 1) * 2 ^ (2 * v + 1) * 2 ^ v from by ring, hpowid]
          _ ≤ 2 ^ (4 * v) := by
              have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (4 * v) := by positivity
              linarith
      calc (4 / b) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)) * 2 ^ v
          = (8 * (n : ℝ) / (s : ℝ)) ^ v * ((4 / b) * (2 : ℝ) ^ (2 * v + 1) * 2 ^ v) := by ring
        _ ≤ (8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (4 * v) :=
            mul_le_mul_of_nonneg_left hcalc (by positivity)
        _ = (16 * (8 * (n : ℝ) / (s : ℝ))) ^ v := hexp.symm
        _ ≤ κ ^ v := hκF
    have hdiv : (4 / b) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1))
        ≤ κ ^ (v - v / L) := by
      have h2v : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
      refine le_of_mul_le_mul_right ?_ h2v
      calc (4 / b) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)) * 2 ^ v ≤ κ ^ v := hmain
        _ = κ ^ (v - v / L) * κ ^ (v / L) := hsplit.symm
        _ ≤ κ ^ (v - v / L) * 2 ^ v :=
            mul_le_mul_of_nonneg_left hκvL (pow_nonneg hκ0.le _)
    have hfinal : (8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)
        ≤ (b / 4) * κ ^ (v - v / L) := by
      have hbne : b ≠ 0 := ne_of_gt hb0
      have heq : (b / 4) * ((4 / b) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)))
          = (8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1) := by field_simp
      calc (8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)
          = (b / 4) * ((4 / b) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1))) := heq.symm
        _ ≤ (b / 4) * κ ^ (v - v / L) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
    calc (8 * (n : ℝ) / (s : ℝ)) ^ v * (𝓖.card : ℝ) * 2 ^ (v + 1) * 2 ^ v
        = (𝓖.card : ℝ) * ((8 * (n : ℝ) / (s : ℝ)) ^ v * 2 ^ (2 * v + 1)) := by
          rw [show (2 : ℝ) ^ (2 * v + 1) = 2 ^ (v + 1) * 2 ^ v from by
            rw [← pow_add]; congr 1; omega]
          ring
      _ ≤ (𝓖.card : ℝ) * ((b / 4) * κ ^ (v - v / L)) :=
          mul_le_mul_of_nonneg_left hfinal (Nat.cast_nonneg _)
      _ = (b / 4) * (𝓖.card : ℝ) * κ ^ (v - v / L) := by ring
  -- the fuel bound
  have h2L1 : (0 : ℝ) < 2 * (L : ℝ) - 1 := by linarith
  have hfuel : (w' : ℝ) ≤ 2 * (L : ℝ) * ((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ t₀ := by
    have hQ0 : (0 : ℝ) ≤ (2 * (L : ℝ)) / (2 * (L : ℝ) - 1) := div_nonneg (by positivity) h2L1.le
    have hQ2 : (2 : ℝ) ≤ ((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ (2 * L - 1) := by
      have hx : (-2 : ℝ) ≤ 1 / (2 * (L : ℝ) - 1) := by
        have : (0 : ℝ) ≤ 1 / (2 * (L : ℝ) - 1) := by positivity
        linarith
      have hbn := one_add_mul_le_pow hx (2 * L - 1)
      have hcast : ((2 * L - 1 : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * L)]
        push_cast
        ring
      rw [hcast] at hbn
      have hone : (2 * (L : ℝ) - 1) * (1 / (2 * (L : ℝ) - 1)) = 1 := by
        field_simp
      have hQeq : (1 : ℝ) + 1 / (2 * (L : ℝ) - 1) = (2 * (L : ℝ)) / (2 * (L : ℝ) - 1) := by
        field_simp
        try ring
      rw [hQeq] at hbn
      linarith
    have hpw : ((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ t₀
        = (((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ (2 * L - 1)) ^ k₀ := by
      rw [← pow_mul, ht₀]
    have h2k : (w : ℝ) < (2 : ℝ) ^ k₀ := by
      have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) w
      have hcast : ((2 ^ (Nat.log 2 w + 1) : ℕ) : ℝ) = (2 : ℝ) ^ k₀ := by
        rw [hk₀]; push_cast; rfl
      calc (w : ℝ) < ((2 ^ (Nat.log 2 w + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2 : ℝ) ^ k₀ := hcast
    have h2kQ : (2 : ℝ) ^ k₀ ≤ (((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ (2 * L - 1)) ^ k₀ :=
      pow_le_pow_left₀ (by norm_num) hQ2 k₀
    have hw'R : (w' : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw'w
    have hQt0 : (0 : ℝ) ≤ ((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ t₀ := pow_nonneg hQ0 _
    calc (w' : ℝ) ≤ (w : ℝ) := hw'R
      _ ≤ (2 : ℝ) ^ k₀ := h2k.le
      _ ≤ (((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ (2 * L - 1)) ^ k₀ := h2kQ
      _ = ((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ t₀ := hpw.symm
      _ ≤ 2 * (L : ℝ) * ((2 * (L : ℝ)) / (2 * (L : ℝ) - 1)) ^ t₀ :=
          le_mul_of_one_le_left hQt0 (by linarith)
  -- the final accounting
  have hfin : (b / 4 + b / 4)
      + Real.exp ((m : ℝ) * Real.log 2 - a * ((n : ℕ) : ℝ) / 2) < b := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hmlog : (m : ℝ) * Real.log 2 - a * (n : ℝ) / 2 ≤ - (a * (n : ℝ) / 4) := by
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      nlinarith [hmR, hlog2, hlog2nn, h2]
    have h2 : 4096 * Real.log (8 / b) ≤ κ * a := by nlinarith [hH2, hLR, hlogb.le]
    have h3 : Real.log (2 / b) < Real.log (8 / b) := by
      refine Real.log_lt_log (by positivity) ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    have hstrict : Real.log (2 / b) < a * (n : ℝ) / 4 := by linarith [han, h2, hlogb, h3]
    have hexp : Real.exp ((m : ℝ) * Real.log 2 - a * (n : ℝ) / 2) < b / 2 := by
      have h4 : Real.exp ((m : ℝ) * Real.log 2 - a * (n : ℝ) / 2)
          ≤ Real.exp (- (a * (n : ℝ) / 4)) := Real.exp_le_exp.mpr hmlog
      have h5 : Real.exp (- (a * (n : ℝ) / 4)) < Real.exp (- Real.log (2 / b)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h6 : Real.exp (- Real.log (2 / b)) = b / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      linarith
    linarith
  -- run the assembly
  exact isSatisfying_of_isSpread_iterated_pad (κ := κ) (a := a) (p := a / 32) (b := b)
    (ε := b / 4) (εbot := b / 4) (L := L) (s := s) (m_bot := m_bot) (t₀ := t₀) (m := m)
    hu hne hsp hw' (by omega) hs1 hmb2L hκ1 hp0 hp1 (by positivity) (by positivity)
    hK1 hS1 hS2 hS3 hfuel hbud hmn ha ha1 hfin


/-- **ALWZ Theorem 1.9 on the padded bottom.** Same as
`Schedule.exists_isRobustSunflower_of_kappa`, with the middle condition linear in `L`. -/
theorem exists_isRobustSunflower_of_kappa_pad {𝓕 : Finset (Finset α)} {X : Finset α} {w : ℕ}
    {κ a b : ℝ} (hκ1 : 1 < κ) (hw2 : 2 ≤ w) (hu : IsUniform w 𝓕)
    (hsub : ∀ S ∈ 𝓕, S ⊆ X) (hcard : κ ^ w ≤ (𝓕.card : ℝ))
    (ha : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hH1 : 128 * (schedL κ b : ℝ) ≤ κ * a)
    (hH2 : 1024 * (schedL κ b : ℝ) * Real.log (8 / b) ≤ κ * a)
    (hH3 : 4096 * (schedL κ b : ℝ) * ((Nat.log 2 w : ℝ) + 1) ≤ κ * a) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 :=
  exists_isRobustSunflower_of_satisfying hκ1 (by omega) hu hsub hcard
    (fun {_𝓖} {_w'} hu' hne' hsp' hw'1 hw'w =>
      isSatisfying_of_isSpread_of_kappa_pad hu' hne' hsp' hw'1 hw'w hw2 ha ha1 hb0 hb1
        hH1 hH2 hH3)

end Sunflower

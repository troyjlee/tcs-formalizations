/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma57

/-!
# The cut-oriented repair for Proposition 5.6

In KKO's min-cut analysis the residual case supplies `γ > ζ/2.1` with
`x(S_A) + x(S̄_B) ≥ 1 − η + γ`, and the argument then invokes Lemma 5.7 at
`α = γ − η`.  ⚠️ **That application is not justified as written**: Lemma 5.7
requires `α < 0.001`, and the proof establishes only the *lower* bound
`γ − η > ζ/2.1 − η > 100η`.  Nothing prevents `γ` from being large — it is
a difference of `x`-masses inside `A`, so `γ` ranges up to `1 + η`.

The repair is to *cap*.  Two observations close the gap.

* Lemma 5.7's ceiling is not really `0.001`: every numeric step in it has
  room up to `1/50`, which is where `Lemma57.lean` now states it.
* The target is bounded two ways, and each covers one regime:
  `cut_target_le_cube` gives `≤ 0.017γ³` for *all* `ζ` — the maximum over
  `ζ` is at `ζ = 1.4γ`, worth `0.016077γ³` — while `cut_target_le_const`
  gives `≤ 3·10⁻⁷` once `ζ < 0.003` and `γ ≤ 1.001`.

So for `γ − η ≤ 1/50` apply Lemma 5.7 at `α = γ − η` and compare cubes; for
`γ − η > 1/50` apply it at `α = 1/50`, where the hypothesis is *weaker* than
what is given, and compare against the constant: `0.11·(1/50)³ = 8.8·10⁻⁷`
clears `3·10⁻⁷` with a factor of nearly three to spare.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Two bounds on the cut target -/

omit [Fintype ι] [DecidableEq ι] in
/-- The target never exceeds `0.017 γ³`, whatever `ζ` is: the maximum over
`ζ` sits at `ζ = 1.4γ` and is worth `0.016077…γ³`.  The certificate is the
factorization `ζ³ − 2.1γζ² + 1.372γ³ = (ζ − 1.4γ)²(ζ + 0.7γ)`. -/
theorem cut_target_le_cube {γ ζ : ℝ} (hγ : 0 ≤ γ) (hζ : 0 ≤ ζ) :
    0.11 * (0.473 * ζ) ^ 2 * (γ - ζ / 2.1) ≤ 0.017 * γ ^ 3 := by
  have key : 0 ≤ (ζ - 1.4 * γ) ^ 2 * (ζ + 0.7 * γ) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hγ3 : 0 ≤ γ ^ 3 := pow_nonneg hγ 3
  have hid : 0.017 * γ ^ 3 - 0.11 * (0.473 * ζ) ^ 2 * (γ - ζ / 2.1)
      = (2461019 / 210000000 : ℝ) * ((ζ - 1.4 * γ) ^ 2 * (ζ + 0.7 * γ))
        + (193481932 / 210000000000 : ℝ) * γ ^ 3 := by ring
  linarith [key, hγ3, hid]

omit [Fintype ι] [DecidableEq ι] in
/-- Once `ζ` is genuinely small the target is bounded by a constant. -/
theorem cut_target_le_const {γ ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ 0.003)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1.001) :
    0.11 * (0.473 * ζ) ^ 2 * (γ - ζ / 2.1) ≤ 0.0000003 := by
  have hζsq : ζ ^ 2 ≤ 0.000009 := by nlinarith
  have hprod : ζ ^ 2 * γ ≤ 0.000009 * 1.001 :=
    mul_le_mul hζsq hγ hγ0 (by norm_num)
  have hcube : (0:ℝ) ≤ ζ ^ 3 := by positivity
  have hid : 0.11 * (0.473 * ζ) ^ 2 * (γ - ζ / 2.1)
      = (2461019 / 100000000 : ℝ) * (ζ ^ 2 * γ)
        - (2461019 / 210000000 : ℝ) * ζ ^ 3 := by ring
  rw [hid]
  linarith [hprod, hcube]

/-! ### The repair -/

/-- **The cut-oriented form of Lemma 5.7**, valid for every `γ` the min-cut
argument can produce — including the large `γ` the paper's application does
not cover. -/
theorem cut_repair {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B X Y : Finset ι} (hAB : Disjoint A B) (hXA : X ⊆ A)
    {η γ ζ : ℝ} (hη0 : 0 ≤ η) (hζη : 330 * η < ζ) (hζ : ζ < 0.003)
    (hγζ : ζ / 2.1 < γ) (hγ1 : γ ≤ 1 + η)
    (hEA : expCard w A ≤ 1 + η) (hEB : expCard w B ≤ 1 + η)
    (hunion : 1 - η + γ ≤ expCard w (X ∪ (B \ Y))) :
    0.11 * (0.473 * ζ) ^ 2 * (γ - ζ / 2.1)
      ≤ weightMass w (fun T => (T ∩ X).card = 1 ∧ (T ∩ (B \ Y)).card = 1
          ∧ (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) := by
  have hζ0 : 0 < ζ := by linarith
  -- clear the division: `linarith` treats `ζ / 2.1` as an opaque atom
  have hγζ' : ζ < 2.1 * γ := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2.1)] at hγζ
    linarith
  have hγ0 : 0 < γ := by linarith
  -- `γ` dominates `η` by the two-step chain `330η < ζ < 2.1γ`
  have hηγ : 100 * η < γ - η := by linarith
  have hBY : B \ Y ⊆ B := Finset.sdiff_subset
  rcases le_or_gt (γ - η) (1 / 50) with hsmall | hbig
  · -- moderate `γ`: Lemma 5.7 applies at `α = γ − η`
    have h57 := lemma_5_7 hst hr hnn htot hAB hXA hBY hη0 hηγ hsmall hEA hEB
      (by linarith)
    have hcube := cut_target_le_cube (γ := γ) (ζ := ζ) hγ0.le hζ0.le
    have hstep : 0.99 * γ ≤ γ - η := by linarith
    have hpow : (0.99 * γ) ^ 3 ≤ (γ - η) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hstep 3
    nlinarith [h57, hcube, hpow, pow_nonneg hγ0.le 3]
  · -- large `γ`: apply Lemma 5.7 at the cap, where the hypothesis is weaker
    have h57 := lemma_5_7 hst hr hnn htot hAB hXA hBY hη0
      (show 100 * η < 1 / 50 by linarith) (le_refl (1 / 50 : ℝ)) hEA hEB
      (by linarith)
    have hconst := cut_target_le_const (γ := γ) (ζ := ζ) hζ0.le hζ.le hγ0.le
      (by linarith)
    norm_num at h57
    linarith [h57, hconst]

end TSPGap

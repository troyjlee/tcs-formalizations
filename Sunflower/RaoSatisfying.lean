/-
# From fixed-size coverage to the `p`-biased model

`RaoCover.rao_fixed_cover` bounds the uncovered *slices*: `< ε·C(n,m)` of the `m`-subsets miss
every member. Theorem 1.9 and the BCW note both want the `p`-biased statement — Definition 1.5,
`IsSatisfying δ ε X 𝓕` — so the two models have to be bridged.

This is the interface of formalization note **F7**, and the bridge already exists: it was built for
the ALWZ route in `Bridge`/`BridgeBack`, where the direction `p`-biased ⟸ fixed-size was found
to need a *lower tail* for `|R|`. Nothing new is required here; the existing lemmas are stated
for weighted systems (`supp X σ`), so this file supplies the plain-family versions and composes
them with the covering estimate.

The tail is `Pr[|R| < m] ≤ exp(m·log 2 − δ·n/2)` (`BridgeBack.pBiased_card_lt_le_exp`, the
Chernoff bound off the exact MGF). Keeping it as a named hypothesis rather than inlining the
arithmetic keeps the schedule chase in one place.
-/
import Sunflower.RaoCover
import Sunflower.BridgeBack

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α]

/-! ## The plain-family versions of the bridge -/

omit [DecidableEq α] in
/-- "No member of `𝓕` fits inside `R`" is a decreasing event. -/
lemma decreasing_uncovered_family (𝓕 : Finset (Finset α)) :
    Decreasing (fun R => ¬ ∃ T ∈ 𝓕, T ⊆ R) := by
  intro a b hab h hex
  obtain ⟨T, hT, hTa⟩ := hex
  exact h ⟨T, hT, hTa.trans hab⟩

/-- Definition 1.5, from a bound on the uncovered probability. -/
lemma isSatisfying_of_uncovered_lt_family {X : Finset α} {𝓕 : Finset (Finset α)} {p b : ℝ}
    (h : pBiased X p (fun R => ¬ ∃ T ∈ 𝓕, T ⊆ R) < b) :
    IsSatisfying p b X 𝓕 := by
  have hsum := pBiased_add_not X p (fun R => ∃ S ∈ 𝓕, S ⊆ R)
  rw [IsSatisfying]
  linarith [hsum, h]

/-- **The transfer.** A fixed-size covering bound plus a lower tail for `|R|` gives Definition
1.5. This is `Satisfying.isSatisfying_of_failCount_tail` for a plain family. -/
theorem isSatisfying_of_fixedCount_tail {X : Finset α} {𝓕 : Finset (Finset α)}
    {p b ε τ : ℝ} {m₀ : ℕ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hm₀n : m₀ ≤ X.card)
    (hfail : ((fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) m₀ : ℕ) : ℝ)
      ≤ ε * ((X.card.choose m₀ : ℕ) : ℝ))
    (htail : pBiased X p (fun R => R.card < m₀) ≤ τ)
    (hb : ε + τ < b) :
    IsSatisfying p b X 𝓕 := by
  classical
  refine isSatisfying_of_uncovered_lt_family ?_
  have hCpos : (0 : ℝ) < ((X.card.choose m₀ : ℕ) : ℝ) := by
    have : 0 < X.card.choose m₀ := Nat.choose_pos hm₀n
    exact_mod_cast this
  have hbridge := pBiased_le_fixedCount_add_tail (X := X)
    (P := fun R => ¬ ∃ T ∈ 𝓕, T ⊆ R) (decreasing_uncovered_family 𝓕) hp0.le hp1 hm₀n
  have htail' := mul_le_mul_of_nonneg_right htail hCpos.le
  refine lt_of_mul_lt_mul_right ?_ hCpos.le
  calc pBiased X p (fun R => ¬ ∃ T ∈ 𝓕, T ⊆ R) * ((X.card.choose m₀ : ℕ) : ℝ)
      ≤ ((fixedCount X (fun R => ¬ ∃ T ∈ 𝓕, T ⊆ R) m₀ : ℕ) : ℝ)
          + pBiased X p (fun R => R.card < m₀) * ((X.card.choose m₀ : ℕ) : ℝ) := hbridge
    _ ≤ ε * ((X.card.choose m₀ : ℕ) : ℝ) + τ * ((X.card.choose m₀ : ℕ) : ℝ) :=
        add_le_add hfail htail'
    _ = (ε + τ) * ((X.card.choose m₀ : ℕ) : ℝ) := by ring
    _ < b * ((X.card.choose m₀ : ℕ) : ℝ) := by
        exact mul_lt_mul_of_pos_right hb hCpos

/-! ## Rao's technical estimate, `p`-biased

BCW's Theorem 3: an `R`-spread `w`-uniform family with `|𝓕| ≥ R^w` is `(δ, ε)`-satisfying. -/

/-- **BCW's Theorem 3** (Rao's Lemma 4 in the `p`-biased model), with the schedule and the tail
supplied. Splitting `ε` between the two sources of failure — uncovered slices and a short `R` —
is the `2ε² ≤ ε` step of the plan, here `ε/4 + ε/2 < ε`. -/
theorem rao_isSatisfying {X : Finset α} {𝓕 : Finset (Finset α)} {v w j : ℕ} {R δ ε : ℝ}
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hFle : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hFge : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 1 ≤ R) (hne𝓕 : 𝓕.Nonempty) (hw1 : 1 ≤ w)
    (hv1 : 1 ≤ v) (hwv : w ≤ v)
    (hjv : j * v + v ≤ X.card) (hw3 : 3 * w ≤ 2 * (X.card - j * v))
    (hwn : w < X.card - j * v)
    (hRv : 1 ≤ R * ((v : ℝ) / (((X.card : ℕ)) : ℝ)))
    (hκ : 45 ≤ Real.logb 2 R + Real.logb 2 ((v : ℝ) / (((X.card : ℕ)) : ℝ)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (hj : 3 * Real.log ((w : ℝ) / (ε / 4)) < (j : ℝ))
    (htail : Real.exp (((j * v : ℕ) : ℝ) * Real.log 2 - δ * ((X.card : ℕ) : ℝ) / 2) ≤ ε / 2) :
    IsSatisfying δ ε X 𝓕 := by
  refine isSatisfying_of_fixedCount_tail (m₀ := j * v) (ε := ε / 4) (τ := ε / 2)
    hδ0 hδ1 (by omega) ?_ ?_ (by linarith)
  · exact le_of_lt (rao_fixed_cover hu hsp hSX hFle hFge hR hne𝓕 hw1 hv1 hwv hjv hw3 hwn
      hRv hκ (by linarith) hj)
  · exact le_trans (pBiased_card_lt_le_exp X hδ0.le hδ1 (j * v)) htail

end Rao

end Sunflower

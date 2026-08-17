/-
# The sunflower theorem at `(C·r·log w)^w`

Rao's induction, with the note's `2r`-colour disjointness lemma at its base. Fix `r` and the
spread parameter `R`. For a `w`-uniform family with at least `R^w` members:

* if the family is absolutely `R`-spread, `SunflowerNote.exists_pairwiseDisjoint_of_raoSpread`
  produces `r` pairwise disjoint members — a sunflower with empty core;
* otherwise some nonempty core `Z` violates the spread condition, so its link has **more**
  than `R^{w−|Z|}` members. The link is `(w−|Z|)`-uniform of strictly smaller width, the
  `κ`-condition on `R` is monotone in the width, and a sunflower in the link reattaches `Z`.

This is the induction as Rao runs it (Coding for Sunflowers, proof of the theorem), and it is
where the *absolute* spread condition earns its keep: a violating core hands the induction a
link that is large in absolute terms, with the same `R`.

The endpoint: `rao_bcw` — every `w`-uniform family of size at least `(2⁶⁰·r·lg w)^w`
contains an `r`-sunflower — and `rao_bcw_bounded`, the same threshold for `w`-set systems via
the private-dummy padding, exactly as `alwz_bounded`. Against `alwz`'s
`(C·r³·lg w·lg lg w)^w`, this removes both the `r³` (Rao's coding argument needs no `log r`
rounds, and the note's `b = 1/2` removes the union bound's `1/r` budget) and the `lg lg w`
(the coding estimate replaces the ALWZ iteration). `rao_bcw_original` re-exports Rao's own
`(C·r·log(rw))^w` shape as a regression check.
-/
import Sunflower.SunflowerNote
import Sunflower.Padding

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- **Lifting a sunflower out of a link.** A sunflower in `𝓕_Z` with core `K` reattaches to
a sunflower in `𝓕` with core `K ∪ Z`: members of the link are disjoint from `Z`, so
`P ↦ P ∪ Z` is injective on it and `(P ∪ Z) ∩ (Q ∪ Z) = (P ∩ Q) ∪ Z`. -/
theorem hasSunflower_of_hasSunflower_link {𝓕 : Finset (Finset α)} {Z : Finset α} {r : ℕ}
    (h : HasSunflower r (link 𝓕 Z)) : HasSunflower r 𝓕 := by
  classical
  obtain ⟨𝒮, hsub, hcard, K, hK⟩ := h
  have hdisjZ : ∀ ⦃P⦄, P ∈ 𝒮 → Disjoint P Z := fun P hP =>
    disjoint_of_mem_link (hsub hP)
  have hcancel : ∀ ⦃P⦄, P ∈ 𝒮 → (P ∪ Z) \ Z = P := by
    intro P hP
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1 h2
    · intro hx
      exact ⟨Or.inl hx, fun hxZ => Finset.disjoint_left.mp (hdisjZ hP) hx hxZ⟩
  have hinj : Set.InjOn (fun P => P ∪ Z) (𝒮 : Set (Finset α)) := by
    intro A hA B hB hAB
    calc A = (A ∪ Z) \ Z := (hcancel hA).symm
      _ = (B ∪ Z) \ Z := by rw [show A ∪ Z = B ∪ Z from hAB]
      _ = B := hcancel hB
  refine ⟨𝒮.image (fun P => P ∪ Z), ?_, ?_, K ∪ Z, ?_⟩
  · intro S hS
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hS
    exact union_mem_of_mem_link (hsub hP)
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · intro S hS T hT hne
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hT
    have hPQ : P ≠ Q := fun hpq => hne (by rw [hpq])
    have hcore := hK hP hQ hPQ
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, ← hcore]
    tauto

/-- **Rao's induction.** For fixed `r` and `R`: every `w`-uniform family with at least `R^w`
members contains an `r`-sunflower, provided `R` clears the disjointness lemma's condition at
width `w` (the condition is monotone in the width, so it clears it at every smaller width
too). Spread families give the empty-core sunflower directly; a violating core hands the
induction a strictly narrower link with the same `R`. -/
theorem hasSunflower_of_raoKappa {r : ℕ} {R : ℝ} (hr : 1 ≤ r) :
    ∀ w : ℕ, 1 ≤ w → 2 ^ 56 * (r : ℝ) * (Real.log (2 * (w : ℝ)) + 1) ≤ R →
      ∀ 𝓕 : Finset (Finset α), IsUniform w 𝓕 → R ^ w ≤ ((𝓕.card : ℕ) : ℝ) →
      HasSunflower r 𝓕 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw1 hκ 𝓕 hu hcard
    by_cases hsp : IsRaoSpread R w 𝓕
    · -- spread: the `2r`-colour lemma gives `r` disjoint members, an empty-core sunflower
      obtain ⟨𝒟, h𝒟sub, h𝒟card, h𝒟pd⟩ := exists_pairwiseDisjoint_of_raoSpread hr hw1 hu hsp
        (fun S hS => Finset.subset_biUnion_of_mem id hS) hcard hκ
      refine hasSunflower_of_pairwiseDisjoint_link (Z := ∅) ?_ h𝒟card h𝒟pd
      rw [link_empty]
      exact h𝒟sub
    · -- a violating core: its link is large in absolute terms
      obtain ⟨Z, hZne, hZbig⟩ : ∃ Z : Finset α, Z.Nonempty
          ∧ R ^ (w - Z.card) < (((link 𝓕 Z).card : ℕ) : ℝ) := by
        by_contra hcon
        push Not at hcon
        exact hsp fun Z hZ => hcon Z hZ
      have hZpos : 0 < Z.card := Finset.card_pos.mpr hZne
      -- a full-size core has a link of at most one member, below `R^0 = 1`
      have hZlt : Z.card < w := by
        by_contra hge
        push Not at hge
        have h1 : (link 𝓕 Z).card ≤ 1 := card_link_le_one hu hge
        have h2 : (((link 𝓕 Z).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
        have h3 : w - Z.card = 0 := by omega
        rw [h3, pow_zero] at hZbig
        linarith
      have hw'1 : 1 ≤ w - Z.card := by omega
      -- the `κ` condition is monotone in the width
      have hκ' : 2 ^ 56 * (r : ℝ) * (Real.log (2 * ((w - Z.card : ℕ) : ℝ)) + 1) ≤ R := by
        have hle : ((w - Z.card : ℕ) : ℝ) ≤ (w : ℝ) := by
          exact_mod_cast Nat.sub_le w Z.card
        have hpos : (0 : ℝ) < 2 * ((w - Z.card : ℕ) : ℝ) := by
          have h1 : (1 : ℝ) ≤ ((w - Z.card : ℕ) : ℝ) := by exact_mod_cast hw'1
          linarith
        have hlogle : Real.log (2 * ((w - Z.card : ℕ) : ℝ)) ≤ Real.log (2 * (w : ℝ)) :=
          Real.log_le_log hpos (by linarith)
        calc 2 ^ 56 * (r : ℝ) * (Real.log (2 * ((w - Z.card : ℕ) : ℝ)) + 1)
            ≤ 2 ^ 56 * (r : ℝ) * (Real.log (2 * (w : ℝ)) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ R := hκ
      exact hasSunflower_of_hasSunflower_link
        (ih (w - Z.card) (by omega) hw'1 hκ' (link 𝓕 Z) (hu.link Z) (le_of_lt hZbig))

/-! ## The explicit threshold -/

/-- The Rao–BCW sunflower threshold, `(C·r·lg w)^w`. -/
noncomputable def raoBound (C : ℝ) (r w : ℕ) : ℝ := (C * (r : ℝ) * lg (w : ℝ)) ^ w

/-- The `κ`-condition of the disjointness lemma clears at `R = 2⁶⁰·r·lg w` for `w ≥ 2`:
`log(2w) + 1 ≤ 4·log w ≤ 4·lg w`, and `2⁵⁶·4 = 2⁵⁸ ≤ 2⁶⁰`. -/
theorem kappa_cond_of_lg {r w : ℕ} (hr : 1 ≤ r) (hw : 2 ≤ w) :
    2 ^ 56 * (r : ℝ) * (Real.log (2 * (w : ℝ)) + 1) ≤ 2 ^ 60 * (r : ℝ) * lg (w : ℝ) := by
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlogw : (0.693 : ℝ) ≤ Real.log (w : ℝ) := by
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hw2R
    nlinarith [Real.log_two_gt_d9]
  have hlog2w : Real.log (2 * (w : ℝ)) = Real.log 2 + Real.log (w : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt (by linarith : (0 : ℝ) < (w : ℝ)))
  have hlg : Real.log (w : ℝ) ≤ lg (w : ℝ) := by
    have h0 : (0 : ℝ) ≤ Real.log (w : ℝ) := by linarith
    have hlog19_pos : (0 : ℝ) < Real.log 1.9 := Real.log_pos (by norm_num)
    have hlog19_lt1 : Real.log 1.9 < 1 := by
      have h1 : (1.9 : ℝ) < Real.exp 1 :=
        lt_of_lt_of_le (by norm_num) (le_of_lt Real.exp_one_gt_d9)
      have h2 := Real.log_lt_log (by norm_num : (0 : ℝ) < 1.9) h1
      rwa [Real.log_exp] at h2
    simp only [lg, Real.logb]
    rw [le_div_iff₀ hlog19_pos]
    nlinarith
  have hkey : Real.log (2 * (w : ℝ)) + 1 ≤ 4 * lg (w : ℝ) := by
    rw [hlog2w]
    nlinarith [Real.log_two_lt_d9]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by linarith
  have hlg0 : (0 : ℝ) ≤ lg (w : ℝ) := by linarith
  have h1 : (r : ℝ) * (Real.log (2 * (w : ℝ)) + 1) ≤ (r : ℝ) * (4 * lg (w : ℝ)) :=
    mul_le_mul_of_nonneg_left hkey hr0
  nlinarith [h1, mul_nonneg hr0 hlg0]

/-- **The uniform sunflower theorem at `(2⁶⁰·r·lg w)^w`.** -/
theorem rao_bcw_uniform {r w : ℕ} (hr : 2 ≤ r) (hw : 2 ≤ w)
    {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕)
    (hcard : raoBound (2 ^ 60) r w ≤ ((𝓕.card : ℕ) : ℝ)) : HasSunflower r 𝓕 := by
  rw [raoBound] at hcard
  exact hasSunflower_of_raoKappa (by omega) w (by omega)
    (kappa_cond_of_lg (by omega) hw) 𝓕 hu hcard

/-- **The sunflower theorem on the Rao route**: for some absolute `C`, every `w`-uniform
family of size at least `(C·r·lg w)^w` contains an `r`-sunflower (`r, w ≥ 2`). Compare
`alwz`: the `r³` and the `lg lg w` are both gone. -/
theorem rao_bcw : ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 2 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsUniform w 𝓕 → raoBound C r w ≤ ((𝓕.card : ℕ) : ℝ) →
    HasSunflower r 𝓕 :=
  ⟨2 ^ 60, by norm_num, fun _ _ hr hw _ hu hcard => rao_bcw_uniform hr hw hu hcard⟩

/-- **The `w`-set-system version** — ALWZ Theorem 1.4 with the improved threshold. The
private-dummy padding changes neither the width nor the number of members, so the constant
and the bound are the same as in the uniform statement. -/
theorem rao_bcw_bounded : ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 2 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsBounded w 𝓕 → raoBound C r w ≤ ((𝓕.card : ℕ) : ℝ) →
    HasSunflower r 𝓕 := by
  refine ⟨2 ^ 60, by norm_num, ?_⟩
  intro r w hr hw 𝓕 hb hcard
  exact hasSunflower_of_bounded (P := fun n => raoBound (2 ^ 60) r w ≤ (n : ℝ))
    (fun hu hc => rao_bcw_uniform hr hw hu hc) hb hcard

/-! ## Rao's original shape, as a regression check -/

/-- Rao's own threshold, `(C·r·log(rw))^w`. -/
noncomputable def raoBoundOrig (C : ℝ) (r w : ℕ) : ℝ :=
  (C * (r : ℝ) * lg ((r : ℝ) * (w : ℝ))) ^ w

/-- **Rao's theorem in its original shape** (Coding for Sunflowers, Theorem 1): the
`(C·r·log(rw))^w` bound. This is a *statement*-level regression check only — the proof
simply weakens the improved bound by `lg w ≤ lg(rw)`. The proof-route regression — Rao's
own union-bound disjointness argument at `δ = ε = 1/r`, kept independent of the note's
`2r`-colour improvement — is `SunflowerNote.rao_disjoint_original`. -/
theorem rao_bcw_original {r w : ℕ} (hr : 2 ≤ r) (hw : 2 ≤ w)
    {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕)
    (hcard : raoBoundOrig (2 ^ 60) r w ≤ ((𝓕.card : ℕ) : ℝ)) : HasSunflower r 𝓕 := by
  refine rao_bcw_uniform hr hw hu (le_trans ?_ hcard)
  rw [raoBound, raoBoundOrig]
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hw0 : (0 : ℝ) < (w : ℝ) := by linarith
  have hlg_le : lg (w : ℝ) ≤ lg ((r : ℝ) * (w : ℝ)) := lg_mono hw0 (by nlinarith)
  have hlg0 : (0 : ℝ) ≤ lg (w : ℝ) := by
    have h1 := one_lt_lg hw2R
    linarith
  refine pow_le_pow_left₀ (by positivity) ?_ w
  exact mul_le_mul_of_nonneg_left hlg_le (by positivity)

end Sunflower

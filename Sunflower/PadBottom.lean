/-
# Cashing in the padding: the bottom step without the `v²`

`DummyPad.exists_padding` turns a `≤v`-bounded `(M,κ)`-spread system into a `v`-**uniform**
`(qM, κ)`-spread one of mass `q·wTotal`, on a larger *type*. To use it in the bottom step the
`p`-biased measure has to travel with it, which is what this file does:

* `pBiased_map_inl` — the measure is carried along `Sum.inl`: the covering probability of `𝓖`
  on `X` equals that of the image family on `X.map inl`. A bijection of powersets, with
  cardinalities and the subset relation preserved.
* `pBiased_uncovered_ground_eq'` — and then the dummies are invisible, since the event depends
  only on the original coordinates (`Satisfying.pBiased_uncovered_ground_eq`, transported to
  the uncovered form).
* `pBiased_uncovered_le_exp_mass` — the `p`-biased core of `JansonMass`: for a `v`-uniform
  system, `Pr[uncovered] ≤ exp(−A·κ·p/(8Mv))`.
* `pBiased_uncovered_le_exp_pad` and `failCount_le_of_janson_padded` — the payoff: the same
  bound for a merely `≤v`-bounded system, with **no `v²`**. Compare
  `JansonMass.failCount_le_of_janson_uniformMass`, which pays `v²` for the heaviest-size-class
  detour: one factor `v` for the mass split, one for the class width.

The saved factor is exactly the `log log w` by which `KappaZero.kappaZero` exceeds ALWZ's
constant; re-running the schedule chase on this bottom is what would remove it.
-/
import Sunflower.DummyPad
import Sunflower.Satisfying

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## Carrying the measure along `Sum.inl` -/

/-- The `p`-biased covering probability is carried by an injection: sampling `X` and sampling
its image are the same experiment. -/
lemma pBiased_map_inl (X : Finset α) (p : ℝ) (𝓖 : Finset (Finset α)) :
    pBiased (X.map ⟨Sum.inl, Sum.inl_injective⟩) p
        (fun R => ∃ S ∈ 𝓖, S.map ⟨Sum.inl, (Sum.inl_injective : Function.Injective
          (Sum.inl : α → Padded α))⟩ ⊆ R)
      = pBiased X p (fun R => ∃ S ∈ 𝓖, S ⊆ R) := by
  classical
  set e : α ↪ Padded α := ⟨Sum.inl, Sum.inl_injective⟩ with he
  rw [pBiased, pBiased]
  refine (Finset.sum_nbij' (i := fun R => R.map e) (j := fun R' => R'.preimage e
    (Set.injOn_of_injective e.injective)) ?_ ?_ ?_ ?_ ?_).symm
  · intro R hR
    rw [Finset.mem_powerset] at hR ⊢
    exact Finset.map_subset_map.mpr hR
  · intro R' hR'
    rw [Finset.mem_powerset] at hR' ⊢
    intro x hx
    rw [Finset.mem_preimage] at hx
    have := hR' hx
    rw [Finset.mem_map] at this
    obtain ⟨y, hy, hxy⟩ := this
    have : y = x := e.injective hxy
    exact this ▸ hy
  · intro R _
    ext x
    rw [Finset.mem_preimage, Finset.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (e.injective hxy) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro R' hR'
    rw [Finset.mem_powerset] at hR'
    ext x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Finset.mem_preimage] at hy
      exact hy
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp (hR' hx)
      exact ⟨y, Finset.mem_preimage.mpr hx, rfl⟩
  · intro R _
    have hcardR : (R.map e).card = R.card := Finset.card_map e
    have hcardX : (X.map e).card = X.card := Finset.card_map e
    have hevent : (∃ S ∈ 𝓖, S.map e ⊆ R.map e) ↔ (∃ S ∈ 𝓖, S ⊆ R) := by
      constructor
      · rintro ⟨S, hS, hSR⟩
        exact ⟨S, hS, Finset.map_subset_map.mp hSR⟩
      · rintro ⟨S, hS, hSR⟩
        exact ⟨S, hS, Finset.map_subset_map.mpr hSR⟩
    by_cases hc : ∃ S ∈ 𝓖, S ⊆ R
    · rw [if_pos hc, if_pos (hevent.mpr hc), hcardR, hcardX]
    · rw [if_neg hc, if_neg (fun h => hc (hevent.mp h))]

/-- The uncovered form of `Satisfying.pBiased_uncovered_ground_eq`. -/
lemma pBiased_uncovered_ground_eq' {X X' : Finset α} (hXX : X ⊆ X')
    {𝓖 : Finset (Finset α)} (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) (p : ℝ) :
    pBiased X' p (fun R => ∀ S ∈ 𝓖, ¬ (S ⊆ R)) = pBiased X p (fun R => ∀ S ∈ 𝓖, ¬ (S ⊆ R)) := by
  classical
  have hcov := pBiased_uncovered_ground_eq hXX h𝓖 p
  have hX' := pBiased_add_not X' p (fun R => ∃ S ∈ 𝓖, S ⊆ R)
  have hX := pBiased_add_not X p (fun R => ∃ S ∈ 𝓖, S ⊆ R)
  have hcg : ∀ Y : Finset α, pBiased Y p (fun R => ¬ ∃ S ∈ 𝓖, S ⊆ R)
      = pBiased Y p (fun R => ∀ S ∈ 𝓖, ¬ (S ⊆ R)) := by
    intro Y
    refine pBiased_congr Y p fun R => ?_
    exact ⟨fun hh T hT hTR => hh ⟨T, hT, hTR⟩, fun hh hex => by
      obtain ⟨T, hT, hTR⟩ := hex; exact hh T hT hTR⟩
  rw [hcg] at hX' hX
  linarith

/-- `p`-biased probability is monotone in the event. -/
lemma pBiased_mono_event (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ R, P R → Q R) :
    pBiased X p P ≤ pBiased X p Q := by
  classical
  rw [pBiased_eq_sum_wt, pBiased_eq_sum_wt]
  refine Finset.sum_le_sum fun R _ => ?_
  by_cases hP : P R
  · rw [if_pos hP, if_pos (h R hP)]
  · rw [if_neg hP, mul_zero]
    by_cases hQ : Q R
    · rw [if_pos hQ, mul_one]
      exact wt_nonneg hp0 hp1 R
    · rw [if_neg hQ, mul_zero]

/-! ## The `p`-biased core of the mass-Janson bound -/

/-- **ALWZ's Lemma 2.10 at the `p`-biased level**: for a `v`-uniform `κ`-spread system,
`Pr[no member is contained in R] ≤ exp(−A·κ·p/(8·M·v))`. -/
theorem pBiased_uncovered_le_exp_mass {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hA : 0 < wTotal X σ) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : (wTotal X σ : ℝ) * p ^ v
      ≤ 2 * ((wTotal X σ : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)))) :
    pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- ((wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ)))) := by
  classical
  have hAR : (0 : ℝ) < (wTotal X σ : ℝ) := by exact_mod_cast hA
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  set μ : ℝ := ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card with hμdef
  set Δ : ℝ := ∑ T ∈ supp X σ, (σ T : ℝ)
    * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T), (σ T' : ℝ) * p ^ (T ∪ T').card
    with hΔdef
  set D : ℝ := (wTotal X σ : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hΔD : Δ ≤ D := by rw [hΔdef, hDdef]; exact delta_mass_linear hl hu hκ hp hM.le hvt
  have hμA : μ = (wTotal X σ : ℝ) * p ^ v := by rw [hμdef]; exact mu_mass_eq hu
  have hμ0 : 0 ≤ μ := by
    rw [hμdef]
    exact Finset.sum_nonneg fun T _ => by positivity
  set q : ℝ := μ / (2 * D) with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one (by linarith)]
    rw [hμA, hDdef]
    exact hμD
  have hjan : pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- (q * μ) + q ^ 2 * Δ) := by
    rw [hμdef, hΔdef]
    exact janson_mult_q X σ hp.le hp1 hq0 hq1
  refine le_trans hjan (Real.exp_le_exp.mpr ?_)
  have h1 : q ^ 2 * Δ ≤ q ^ 2 * D := mul_le_mul_of_nonneg_left hΔD (sq_nonneg q)
  have h2 : - (q * μ) + q ^ 2 * D = - (μ ^ 2 / (4 * D)) := by
    rw [hqdef]; field_simp; ring
  have hMne : M ≠ 0 := ne_of_gt hM
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  have hpne : p ≠ 0 := ne_of_gt hp
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hAne : (wTotal X σ : ℝ) ≠ 0 := ne_of_gt hAR
  have h3 : μ ^ 2 / (4 * D) = (wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ)) := by
    rw [hμA, hDdef, two_mul v, pow_add]
    field_simp
    ring
  linarith [h1, h2, h3]

/-! ## The payoff: the bottom step for `≤v`-bounded systems, with no `v²` -/

private lemma map_inl_eq_image (S : Finset α) :
    S.map ⟨Sum.inl, (Sum.inl_injective : Function.Injective (Sum.inl : α → Padded α))⟩
      = S.image Sum.inl := Finset.map_eq_image _ _

/-- **The Janson bottom for a `≤v`-bounded system, through the padding.** The exponent is
`A·κ·p/(8·M·v)` — the uniform one, with no loss at all. Compare
`JansonMass.failCount_le_of_janson_uniformMass`, whose heaviest-size-class route pays `v²`. -/
theorem pBiased_uncovered_le_exp_pad {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hA : 0 < wTotal X σ) (hE : σ ∅ = 0) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2) :
    pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- ((wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ)))) := by
  classical
  set e : α ↪ Padded α := ⟨Sum.inl, Sum.inl_injective⟩ with he
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκp : (0 : ℝ) < κ * p := mul_pos hκ0 hp
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hv1R : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hκp1 : (1 : ℝ) ≤ κ * p := by
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp] at hvt
    linarith
  -- the padding, with `q = ⌈κ^v⌉`
  set q : ℕ := ⌈κ ^ v⌉₊ with hqdef
  have hqR : κ ^ v ≤ (q : ℝ) := Nat.le_ceil _
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ (q : ℝ) := le_trans (one_le_pow₀ hκ) hqR
    exact_mod_cast this
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  obtain ⟨hb', hu', hl', htot', hcov'⟩ := exists_padding q hb hl hκ hM.le hE hqR
  set X' := padGround X σ v q with hX'
  set σ' := padWeight X σ v q with hσ'
  have hA' : 0 < wTotal X' σ' := by rw [htot']; exact Nat.mul_pos (by omega) hA
  have hM' : (0 : ℝ) < (q : ℝ) * M := by positivity
  -- the `q ≤ 1` check for the padded system, from `κ^v ≤ q·M`
  have hκvM : κ ^ v ≤ (q : ℝ) * M := by
    have h1 : (1 : ℝ) ≤ M := by
      -- `M ≥ κ^{|S|}·σ S ≥ 1` at any member
      obtain ⟨S, hS⟩ := Finset.card_pos.mp (card_supp_pos hA)
      have hne : S.Nonempty := by
        rcases Finset.eq_empty_or_nonempty S with rfl | h
        · exact absurd hE (mem_supp.mp hS).2
        · exact h
      have h2 : (1 : ℝ) ≤ (wLink X σ S : ℝ) := by
        have : 1 ≤ wLink X σ S := by
          rw [wLink]
          refine le_trans (Nat.one_le_iff_ne_zero.mpr (mem_supp.mp hS).2)
            (Finset.single_le_sum (f := σ) (fun _ _ => Nat.zero_le _) ?_)
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_powerset.mpr (subset_of_mem_supp hS), Finset.Subset.rfl⟩
        exact_mod_cast this
      have h3 := hl S hne
      have h4 : (1 : ℝ) ≤ κ ^ S.card := one_le_pow₀ hκ
      nlinarith [h2, h3, h4]
    nlinarith [hqR, h1, hM.le, pow_pos hκ0 v]
  have hμD' : (wTotal X' σ' : ℝ) * p ^ v
      ≤ 2 * ((wTotal X' σ' : ℝ) * (((q : ℝ) * M) * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))) := by
    have hkey : κ * p ≤ 4 * (v : ℝ) * ((q : ℝ) * M) * p ^ v := by
      have h1 : (κ * p) ^ 1 ≤ (κ * p) ^ v := pow_le_pow_right₀ hκp1 hv
      rw [pow_one] at h1
      have h2 : (κ * p) ^ v = κ ^ v * p ^ v := mul_pow κ p v
      have h3 : κ ^ v * p ^ v ≤ ((q : ℝ) * M) * p ^ v :=
        mul_le_mul_of_nonneg_right hκvM (by positivity)
      nlinarith [h1, h3, mul_nonneg hM'.le (pow_nonneg hp.le v), hv1R]
    have hrw : 2 * ((wTotal X' σ' : ℝ) * (((q : ℝ) * M) * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)))
        = ((wTotal X' σ' : ℝ) * p ^ v) * ((4 * (v : ℝ) * ((q : ℝ) * M) * p ^ v) / (κ * p)) := by
      rw [two_mul v, pow_add]
      field_simp
      ring
    rw [hrw]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [le_div_iff₀ hκp, one_mul]
    exact hkey
  -- the uniform bound on the padded system
  have hpad := pBiased_uncovered_le_exp_mass hl' hu' hκ0 hp hp1 hM' hv hA' hvt hμD'
  have hexp : ((wTotal X' σ' : ℝ)) * κ * p / (8 * ((q : ℝ) * M) * (v : ℝ))
      = (wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ)) := by
    have hcast : ((wTotal X' σ' : ℕ) : ℝ) = (q : ℝ) * (wTotal X σ : ℝ) := by
      rw [htot']; push_cast; ring
    rw [hcast]
    exact janson_exponent_padding hqRpos (ne_of_gt hM) (ne_of_gt hvR)
  rw [hexp] at hpad
  refine le_trans ?_ hpad
  -- carry the measure: `X → X.map e → X'`
  have hsubX : X.map e ⊆ X' := by
    rw [hX', padGround, he, map_inl_eq_image]
    exact Finset.subset_union_left
  have hmem : ∀ S ∈ (supp X σ).image (fun S => S.map e), S ⊆ X.map e := by
    intro P hP
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.map_subset_map.mpr (subset_of_mem_supp hS)
  have hstep1 : pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      = pBiased (X.map e) p (fun R => ∀ P ∈ (supp X σ).image (fun S => S.map e), ¬ (P ⊆ R)) := by
    have hcov := pBiased_map_inl X p (supp X σ)
    have h1 := pBiased_add_not X p (fun R => ∃ S ∈ supp X σ, S ⊆ R)
    have h2 := pBiased_add_not (X.map e) p
      (fun R => ∃ P ∈ (supp X σ).image (fun S => S.map e), P ⊆ R)
    have hcg1 : pBiased X p (fun R => ¬ ∃ S ∈ supp X σ, S ⊆ R)
        = pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) :=
      pBiased_congr X p fun R => ⟨fun hh T hT hTR => hh ⟨T, hT, hTR⟩, fun hh hex => by
        obtain ⟨T, hT, hTR⟩ := hex; exact hh T hT hTR⟩
    have hcg2 : pBiased (X.map e) p
          (fun R => ¬ ∃ P ∈ (supp X σ).image (fun S => S.map e), P ⊆ R)
        = pBiased (X.map e) p
          (fun R => ∀ P ∈ (supp X σ).image (fun S => S.map e), ¬ (P ⊆ R)) :=
      pBiased_congr _ p fun R => ⟨fun hh T hT hTR => hh ⟨T, hT, hTR⟩, fun hh hex => by
        obtain ⟨T, hT, hTR⟩ := hex; exact hh T hT hTR⟩
    have hcov' : pBiased (X.map e) p
        (fun R => ∃ P ∈ (supp X σ).image (fun S => S.map e), P ⊆ R)
        = pBiased X p (fun R => ∃ S ∈ supp X σ, S ⊆ R) := by
      refine Eq.trans (pBiased_congr _ p fun R => ?_) hcov
      constructor
      · rintro ⟨P, hP, hPR⟩
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hP
        exact ⟨S, hS, hPR⟩
      · rintro ⟨S, hS, hSR⟩
        exact ⟨S.map e, Finset.mem_image_of_mem _ hS, hSR⟩
    rw [hcg1] at h1
    rw [hcg2] at h2
    rw [hcov'] at h2
    linarith
  have hstep2 : pBiased (X.map e) p
        (fun R => ∀ P ∈ (supp X σ).image (fun S => S.map e), ¬ (P ⊆ R))
      = pBiased X' p (fun R => ∀ P ∈ (supp X σ).image (fun S => S.map e), ¬ (P ⊆ R)) :=
    (pBiased_uncovered_ground_eq' hsubX hmem p).symm
  have hstep3 : pBiased X' p (fun R => ∀ P ∈ (supp X σ).image (fun S => S.map e), ¬ (P ⊆ R))
      ≤ pBiased X' p (fun R => ∀ P ∈ supp X' σ', ¬ (P ⊆ R)) := by
    refine pBiased_mono_event X' hp.le hp1 fun R hR P hP hPR => ?_
    obtain ⟨S, hS, hSP⟩ := hcov' P hP
    refine hR (S.map e) (Finset.mem_image_of_mem _ hS) ?_
    rw [he, map_inl_eq_image]
    exact le_trans hSP hPR
  rw [hstep1, hstep2]
  exact hstep3

/-- **The bottom step for the iteration, padded.** `log(2/εbot) ≤ A·κ·p/(8·M·v)` — where
`JansonMass.failCount_le_of_janson_uniformMass` needs `A·κ·p/(8·M·v²)`. -/
theorem failCount_le_of_janson_padded {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {M κ p A εbot : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 1 ≤ v)
    (hA0 : 0 < A) (hA : A ≤ (wTotal X σ : ℝ))
    (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hεb : 0 < εbot)
    (hbudget : Real.log (2 / εbot) ≤ A * κ * p / (8 * M * (v : ℝ)))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
  classical
  by_cases hE : σ ∅ ≠ 0
  · rw [failCount_eq_zero_of_empty_mem X σ m₀ hE, Nat.cast_zero]
    exact mul_nonneg hεb.le (Nat.cast_nonneg _)
  rw [not_not] at hE
  have hApos : 0 < wTotal X σ := by
    by_contra hcon
    push Not at hcon
    have hz : wTotal X σ = 0 := Nat.le_zero.mp hcon
    rw [hz, Nat.cast_zero] at hA
    linarith
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  -- the padded `p`-biased bound, then the bridge
  have hpb := pBiased_uncovered_le_exp_pad hb hl hκ hp hp1 hM (by omega) hApos hE hvt
  have hmono : Real.exp (- ((wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ))))
      ≤ Real.exp (- (A * κ * p / (8 * M * (v : ℝ)))) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (by positivity)) hp.le
  have hexp : Real.exp (- (A * κ * p / (8 * M * (v : ℝ)))) ≤ εbot / 2 := by
    have hpos : (0 : ℝ) < 2 / εbot := by positivity
    refine le_trans (Real.exp_le_exp.mpr (neg_le_neg hbudget)) ?_
    rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  rw [failCount_eq_fixedCount hb m₀]
  calc (fixedCount X (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) m₀ : ℝ)
      ≤ 2 * (pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) * (X.card.choose m₀ : ℝ)) :=
        fixedCount_le_two_mul_pBiased (decreasing_uncovered X σ) hp.le hp1 hm₀ hm₀n hsmall
    _ ≤ 2 * ((εbot / 2) * (X.card.choose m₀ : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hchoose) (by norm_num)
        exact le_trans (le_trans hpb hmono) hexp
    _ = εbot * (X.card.choose m₀ : ℝ) := by ring

/-! ## The iteration on the padded bottom

The bottom condition improves by one factor `L`: where `JansonMass.iterate_le_janson_alwz`
needs `log(2/εbot) ≤ A₀·κ·p/(64·M·L²)`, this needs `A₀·κ·p/(32·M·L)`. -/

/-- The bottom regime on the padded Janson step, in the shape `iterate_le_of_bottom` consumes. -/
theorem janson_bottom_pad {L m_bot n₀ : ℕ} {A₀ M κ p εbot : ℝ} {X : Finset α}
    {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ}
    (hL : 2 ≤ L) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hεb : 0 < εbot)
    (hS1 : 4 * (L : ℝ) ≤ κ * p)
    (hS2 : Real.log (2 / εbot) ≤ A₀ * κ * p / (32 * M * (L : ℝ)))
    (hS3 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ))
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (htot : A ≤ (wTotal X σ : ℝ)) (hAinv : A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A)
    (hv : 1 ≤ v) (hvL : v ≤ 2 * L) (hmm : m_bot ≤ m) (hmn : m ≤ X.card)
    (hn₀ : X.card ≤ n₀) :
    (failCount X σ m : ℝ) ≤ εbot * (X.card.choose m : ℝ) := by
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hvL' : (v : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hvL
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκp : (0 : ℝ) < κ * p := mul_pos hκ0 hp
  have hhalf : (1 / 2 : ℝ) ^ (v + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (v + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hA2 : A₀ / 2 ≤ A := by
    calc A₀ / 2 = A₀ * (1 - 1 / 2) := by ring
      _ ≤ A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) := mul_le_mul_of_nonneg_left (by linarith) hA₀.le
      _ ≤ A := hAinv
  have hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2 := by
    have h1 : (v : ℝ) * (κ * p)⁻¹ ≤ 2 * (L : ℝ) * (κ * p)⁻¹ :=
      mul_le_mul_of_nonneg_right hvL' (by positivity)
    have h2 : 2 * (L : ℝ) * (κ * p)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp]
      linarith
    linarith
  -- the budget at width `v ≤ 2L`, with mass floor `A₀/2` — only *one* factor `L` now
  have hbudget : Real.log (2 / εbot) ≤ (A₀ / 2) * κ * p / (8 * M * (v : ℝ)) := by
    refine le_trans hS2 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc A₀ * κ * p * (8 * M * (v : ℝ))
        = (8 * M * (κ * p)) * (A₀ * (v : ℝ)) := by ring
      _ ≤ (8 * M * (κ * p)) * (A₀ * (2 * (L : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvL' hA₀.le)
            (by positivity)
      _ = A₀ / 2 * κ * p * (32 * M * (L : ℝ)) := by ring
  have hsmall : 2 * (p * (X.card : ℝ)) ≤ (m : ℝ) := by
    have h1 : (X.card : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h2 : (m_bot : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmm
    have h3 : p * (X.card : ℝ) ≤ p * (n₀ : ℝ) := mul_le_mul_of_nonneg_left h1 hp.le
    linarith
  exact failCount_le_of_janson_padded (A := A₀ / 2) hb hl hκ hp hp1 hM hv (by linarith)
    (le_trans hA2 htot) hvt hεb hbudget (by omega) hmn hsmall

/-- **The width-schedule iteration on the padded Janson bottom.** `iterate_le`'s conclusion
verbatim; the bottom budget is now `A₀·κ·p/(32·M·L)`, one factor `L` better than
`JansonMass.iterate_le_janson_alwz`, because the padding replaces the heaviest-size-class
detour. -/
theorem iterate_le_janson_pad {L s m_bot n₀ : ℕ} {A₀ M κ p ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hS1 : 4 * (L : ℝ) ≤ κ * p)
    (hS2 : Real.log (2 / εbot) ≤ A₀ * κ * p / (32 * M * (L : ℝ)))
    (hS3 : 2 * (p * (n₀ : ℝ)) ≤ (m_bot : ℝ)) :
    ∀ (t : ℕ) (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) (A : ℝ) (m : ℕ),
      WBounded X v σ → WLinkBounded X σ M κ → A ≤ (wTotal X σ : ℝ) →
      A₀ * (1 - (1 / 2 : ℝ) ^ (v + 1)) ≤ A →
      (v : ℝ) ≤ 2 * L * ((2 * L : ℝ) / (2 * L - 1)) ^ t →
      1 ≤ v → s * t + m_bot ≤ m → m ≤ X.card → X.card ≤ n₀ →
      (failCount X σ m : ℝ) ≤
        (εbot + ε * (1 - (1 / 2 : ℝ) ^ v)) * (X.card.choose m : ℝ) :=
  iterate_le_of_bottom hL hs hmb hA₀ hM.le hκ hε hεb.le hK1
    (fun {_X _σ _v _m _A} hb hl htot hAinv hv hvL hmm hmn hn₀ =>
      janson_bottom_pad hL hmb hA₀ hM hκ hp hp1 hεb hS1 hS2 hS3
        hb hl htot hAinv hv hvL hmm hmn hn₀)

end Sunflower

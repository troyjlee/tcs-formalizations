/-
# The final step with Janson: the two spread estimates

`SpreadBottom.bottom_le` is the formalization's replacement for ALWZ's Lemma 2.10: it uses a
bare second moment where the paper uses Janson, at the cost of `1/β` instead of `log(1/β)`
(formalization note B1). With `Sunflower.JansonCover` supplying

  `failCount X σ m₀ ≤ 2 · exp(−μ + Δ) · C(|X|, m₀)`,   `μ = ∑_{T ∈ supp} p^{|T|}`,
  `Δ ≤ ∑_{T ∈ supp} ∑_{T' ∈ supp, T' ∩ T ≠ ∅} p^{|T ∪ T'|}`,

what remains is to bound `μ` below and `Δ` above **from the spread hypothesis**. That is the
computation ALWZ perform inside Lemma 2.10, and it is what this file does.

Both estimates rest on one counting consequence of `WLinkBounded`: since every member of the
support carries weight at least `1`,

  `#{T' ∈ supp : U ⊆ T'} · κ^{|U|} ≤ M`   for nonempty `U`   (`card_supp_superset_le`).

From it:

* **`mu_ge`** — for a `v`-uniform system, `|supp| ≥ wTotal·κ^v/M`, hence
  `μ ≥ (wTotal/M)·(κp)^v`. The support cannot be small, because the spread condition caps how
  much weight any single set may carry.
* **`delta_inner_le`** — for each `T`, grouping the `T'` meeting `T` by the *exact*
  intersection `U = T ∩ T'` (not by subsets of it — the exponent bookkeeping only works for
  the exact intersection),
  `∑_{T' : T∩T' ≠ ∅} p^{|T ∪ T'|} ≤ M·p^{2v}·∑_{u=1}^{v} C(v,u)·(κp)^{-u}`.

The remaining arithmetic — summing `delta_inner_le` over `T`, choosing `p`, checking
`Δ ≤ μ/2`, and threading the result through `SpreadIterate` — is the analogue of
`SpreadAssemble` for the Janson route and is *not* done here.
-/
import Sunflower.JansonCover

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## The counting consequence of spreadness -/

/-- Every member of the support carries weight at least `1`, so counting members of the
support above `U` is dominated by the link mass at `U`. -/
lemma card_supp_superset_le_wLink (X : Finset α) (σ : Finset α → ℕ) (U : Finset α) :
    ((supp X σ).filter fun T => U ⊆ T).card ≤ wLink X σ U := by
  classical
  rw [wLink]
  calc ((supp X σ).filter fun T => U ⊆ T).card
      = ∑ _T ∈ (supp X σ).filter fun T => U ⊆ T, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ T ∈ (supp X σ).filter fun T => U ⊆ T, σ T := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [Finset.mem_filter] at hT
        exact Nat.one_le_iff_ne_zero.mpr (mem_supp.mp hT.1).2
    _ ≤ ∑ T ∈ X.powerset.filter fun T => U ⊆ T, σ T := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
        intro T hT
        rw [Finset.mem_filter] at hT ⊢
        exact ⟨Finset.mem_powerset.mpr (subset_of_mem_supp hT.1), hT.2⟩

/-- **The counting form of spreadness.** For nonempty `U`, at most `M/κ^{|U|}` members of the
support lie above `U`. -/
lemma card_supp_superset_le {X : Finset α} {σ : Finset α → ℕ} {M κ : ℝ}
    (hl : WLinkBounded X σ M κ) (hκ : 0 ≤ κ) {U : Finset α} (hU : U.Nonempty) :
    (((supp X σ).filter fun T => U ⊆ T).card : ℝ) * κ ^ U.card ≤ M := by
  refine le_trans ?_ (hl U hU)
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_supp_superset_le_wLink X σ U) (by positivity)

/-! ## The support of a uniform system is large -/

/-- `v`-uniformity of the support. -/
def SuppUniform (X : Finset α) (σ : Finset α → ℕ) (v : ℕ) : Prop :=
  ∀ T ∈ supp X σ, T.card = v

/-- For a `v`-uniform system with `v ≥ 1`, spreadness caps the weight of a single member,
hence forces the support to be large: `|supp| · M ≥ wTotal · κ^v`. -/
lemma card_supp_ge {X : Finset α} {σ : Finset α → ℕ} {M κ : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hv : 1 ≤ v) (hκ : 0 < κ) :
    (wTotal X σ : ℝ) * κ ^ v ≤ ((supp X σ).card : ℝ) * M := by
  classical
  -- each member of the support has weight at most `M / κ^v`
  have hone : ∀ T ∈ supp X σ, (σ T : ℝ) * κ ^ v ≤ M := by
    intro T hT
    have hTne : T.Nonempty := by
      rw [← Finset.card_pos, hu T hT]; omega
    refine le_trans ?_ (hl T hTne)
    have hsub : (σ T : ℝ) ≤ (wLink X σ T : ℝ) := by
      have : σ T ≤ wLink X σ T := by
        rw [wLink]
        refine Finset.single_le_sum (f := σ) (fun _ _ => Nat.zero_le _) ?_
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr (subset_of_mem_supp hT), Finset.Subset.rfl⟩
      exact_mod_cast this
    rw [hu T hT]
    exact mul_le_mul_of_nonneg_right hsub (by positivity)
  -- the total mass lives on the support
  have htot : (wTotal X σ : ℝ) = ∑ T ∈ supp X σ, (σ T : ℝ) := by
    rw [wTotal]
    push_cast
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro T hT hTn
    have hTX : T ⊆ X := Finset.mem_powerset.mp hT
    have hz : σ T = 0 := by
      by_contra hc
      exact hTn (mem_supp.mpr ⟨hTX, hc⟩)
    rw [hz]
    exact Nat.cast_zero
  calc (wTotal X σ : ℝ) * κ ^ v = ∑ T ∈ supp X σ, (σ T : ℝ) * κ ^ v := by
        rw [htot, Finset.sum_mul]
    _ ≤ ∑ _T ∈ supp X σ, M := Finset.sum_le_sum hone
    _ = ((supp X σ).card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The `μ` lower bound.** For a `v`-uniform system, `μ = |supp|·p^v ≥ (wTotal/M)·(κp)^v`,
stated multiplied out. -/
lemma mu_ge {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hv : 1 ≤ v) (hκ : 0 < κ)
    (hp0 : 0 ≤ p) :
    (wTotal X σ : ℝ) * (κ * p) ^ v ≤ (∑ T ∈ supp X σ, p ^ T.card) * M := by
  have huni : ∑ T ∈ supp X σ, p ^ T.card = ((supp X σ).card : ℝ) * p ^ v := by
    rw [Finset.sum_congr rfl fun T hT => by rw [hu T hT], Finset.sum_const, nsmul_eq_mul]
  rw [huni, mul_pow]
  calc (wTotal X σ : ℝ) * (κ ^ v * p ^ v) = ((wTotal X σ : ℝ) * κ ^ v) * p ^ v := by ring
    _ ≤ (((supp X σ).card : ℝ) * M) * p ^ v :=
        mul_le_mul_of_nonneg_right (card_supp_ge hl hu hv hκ) (by positivity)
    _ = ((supp X σ).card : ℝ) * p ^ v * M := by ring

/-! ## The `Δ` upper bound -/

/-- **The inner `Δ` estimate.** Fix `T` in the support of a `v`-uniform system. Grouping the
members `T'` that meet `T` by the *exact* intersection `U = T ∩ T'`,

`∑_{T' : T ∩ T' ≠ ∅} p^{|T ∪ T'|} ≤ ∑_{∅ ≠ U ⊆ T} (M/κ^{|U|}) · p^{2v − |U|}`,

stated without division as a sum over the nonempty subsets of `T`.

Grouping by the exact intersection is essential: for `U ⊊ T ∩ T'` the exponent
`2v − |U|` would *exceed* `|T ∪ T'|`, and with `p ≤ 1` the inequality would run the wrong
way. -/
lemma delta_inner_le {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (_hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (_hκ : 0 < κ)
    (hp0 : 0 ≤ p) {T : Finset α} (hT : T ∈ supp X σ) :
    ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T), p ^ (T ∪ T').card
      ≤ ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
          (((supp X σ).filter fun T'' => U ⊆ T'').card : ℝ) * p ^ (2 * v - U.card) := by
  classical
  -- partition the meeting members by their exact intersection with `T`
  have hfib : ∀ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
      T ∩ T' ∈ T.powerset.filter (fun U => U.Nonempty) := by
    intro T' hT'
    rw [Finset.mem_filter] at hT'
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.inter_subset_left, ?_⟩
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    refine hT'.2 (Finset.disjoint_iff_inter_eq_empty.mpr ?_)
    rw [Finset.inter_comm]
    exact hempty
  rw [← Finset.sum_fiberwise_of_maps_to hfib fun T' => p ^ (T ∪ T').card]
  refine Finset.sum_le_sum fun U hU => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hU
  -- on the fibre the exponent is exactly `2v - |U|`
  have hexp : ∀ T' ∈ ((supp X σ).filter (fun T' => ¬ Disjoint T' T)).filter
      (fun T' => T ∩ T' = U), p ^ (T ∪ T').card = p ^ (2 * v - U.card) := by
    intro T' hT'
    rw [Finset.mem_filter, Finset.mem_filter] at hT'
    have hT'supp : T' ∈ supp X σ := hT'.1.1
    have hcards : (T ∪ T').card + (T ∩ T').card = T.card + T'.card :=
      Finset.card_union_add_card_inter T T'
    have hTv : T.card = v := hu T hT
    have hT'v : T'.card = v := hu T' hT'supp
    have : (T ∪ T').card = 2 * v - U.card := by
      rw [hT'.2] at hcards
      omega
    rw [this]
  rw [Finset.sum_congr rfl hexp, Finset.sum_const, nsmul_eq_mul]
  -- the fibre is contained in the members above `U`
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro T' hT'
  rw [Finset.mem_filter, Finset.mem_filter] at hT'
  rw [Finset.mem_filter]
  exact ⟨hT'.1.1, hT'.2 ▸ Finset.inter_subset_right⟩

/-- **The `Δ` upper bound.** Summing `delta_inner_le` over `T` and applying the counting form
of spreadness to each fibre count gives an explicit bound on the Janson quadratic term:

`Δ ≤ ∑_{T ∈ supp} ∑_{∅ ≠ U ⊆ T} M·κ^{−|U|}·p^{2v−|U|}`.

Since the inner sum depends on `T` only through `|T| = v`, this is `|supp|` times a binomial
sum in `u = |U|`; that regrouping is the only step left before the `κ`-budget arithmetic. -/
theorem delta_le {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hκ : 0 < κ) (hp0 : 0 ≤ p) :
    ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
        p ^ (T ∪ T').card
      ≤ ∑ T ∈ supp X σ, ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
          M * (κ ^ U.card)⁻¹ * p ^ (2 * v - U.card) := by
  refine Finset.sum_le_sum fun T hT => ?_
  refine le_trans (delta_inner_le hl hu hκ hp0 hT) (Finset.sum_le_sum fun U hU => ?_)
  rw [Finset.mem_filter, Finset.mem_powerset] at hU
  -- `#{T' ⊇ U} ≤ M / κ^{|U|}`, from `card_supp_superset_le`
  have hcount := card_supp_superset_le hl hκ.le hU.2
  have hκpow : (0 : ℝ) < κ ^ U.card := by positivity
  have hcard : (((supp X σ).filter fun T'' => U ⊆ T'').card : ℝ) ≤ M * (κ ^ U.card)⁻¹ := by
    rw [le_mul_inv_iff₀ hκpow]
    exact hcount
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Regrouping a sum over the **nonempty** subsets of `T` by cardinality. The `u = 0` term
must be excluded, not merely dropped as a nonnegative extra: including it would replace
`(1+κp)^v − (κp)^v` by `(1+κp)^v`, which for `κp ≫ 1` is larger by a factor `≈ κp/v` — exactly
the factor the final bound lives on. -/
lemma sum_nonempty_subsets_eq (T : Finset α) (g : ℕ → ℝ) :
    ∑ U ∈ T.powerset.filter (fun U => U.Nonempty), g U.card
      = ∑ u ∈ Finset.Icc 1 T.card, (T.card.choose u : ℝ) * g u := by
  classical
  rw [Finset.sum_filter, Finset.powerset_card_biUnion,
    Finset.sum_biUnion (T.pairwise_disjoint_powersetCard.set_pairwise _)]
  have hlayer : ∀ u ∈ Finset.range (T.card + 1),
      (∑ U ∈ Finset.powersetCard u T, if U.Nonempty then g U.card else 0)
        = if u ≠ 0 then (T.card.choose u : ℝ) * g u else 0 := by
    intro u _
    by_cases hu : u = 0
    · subst hu
      rw [Finset.powersetCard_zero]
      simp
    · rw [if_pos hu]
      have hterm : ∀ U ∈ Finset.powersetCard u T,
          (if U.Nonempty then g U.card else 0) = g u := by
        intro U hU
        obtain ⟨-, hUc⟩ := Finset.mem_powersetCard.mp hU
        rw [if_pos (by rw [← Finset.card_pos, hUc]; omega), hUc]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
        Finset.card_powersetCard]
  rw [Finset.sum_congr rfl hlayer, ← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- **The `Δ` upper bound, regrouped.** For a `v`-uniform system the inner sum depends on `T`
only through `|T| = v`, so the whole quadratic term is `|supp|` times a binomial sum:

`Δ ≤ |supp| · ∑_{u=1}^{v} C(v,u) · M · κ^{−u} · p^{2v−u}`.

(Multiplying by `κ^v` and substituting `j = v − u` turns the sum into
`M · p^v · ((1+κp)^v − (κp)^v)`.) -/
theorem delta_le_binom {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hκ : 0 < κ) (hp0 : 0 ≤ p) :
    ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
        p ^ (T ∪ T').card
      ≤ ((supp X σ).card : ℝ)
          * ∑ u ∈ Finset.Icc 1 v, (v.choose u : ℝ) * (M * (κ ^ u)⁻¹ * p ^ (2 * v - u)) := by
  refine le_trans (delta_le hl hu hκ hp0) ?_
  have hper : ∀ T ∈ supp X σ,
      ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
          M * (κ ^ U.card)⁻¹ * p ^ (2 * v - U.card)
        = ∑ u ∈ Finset.Icc 1 v, (v.choose u : ℝ) * (M * (κ ^ u)⁻¹ * p ^ (2 * v - u)) := by
    intro T hT
    have h := sum_nonempty_subsets_eq T fun u => M * (κ ^ u)⁻¹ * p ^ (2 * v - u)
    rwa [hu T hT] at h
  rw [Finset.sum_congr rfl hper, Finset.sum_const, nsmul_eq_mul]

/-- The binomial tail in closed form: `∑_{u=1}^{v} C(v,u)·x^u = (1+x)^v − 1`. -/
lemma sum_Icc_choose (v : ℕ) (x : ℝ) :
    ∑ u ∈ Finset.Icc 1 v, (v.choose u : ℝ) * x ^ u = (1 + x) ^ v - 1 := by
  have hb : (1 + x) ^ v = ∑ u ∈ Finset.range (v + 1), (v.choose u : ℝ) * x ^ u := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [one_pow, mul_one]
    ring
  have hins : Finset.range (v + 1) = insert 0 (Finset.Icc 1 v) := by
    ext u
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 v := by simp
  rw [hins, Finset.sum_insert h0] at hb
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at hb
  linarith

/-- **The `Δ` bound in closed form.** For `p > 0`,

`Δ ≤ |supp| · M · p^{2v} · ((1 + 1/(κp))^v − 1)`.

This is the quotable form: with `t = 1/(κp)`, the bracket is `≈ v·t` once `v·t ≤ 1`, so the
Janson exponent `μ²/(4Δ)` is `≈ |supp|·κ·p/(8·M·v)` — see the closing note. -/
theorem delta_le_closed {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hκ : 0 < κ) (hp : 0 < p) :
    ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
        p ^ (T ∪ T').card
      ≤ ((supp X σ).card : ℝ) * (M * p ^ (2 * v) * ((1 + (κ * p)⁻¹) ^ v - 1)) := by
  refine le_trans (delta_le_binom hl hu hκ hp.le) ?_
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  have hterm : ∀ u ∈ Finset.Icc 1 v,
      (v.choose u : ℝ) * (M * (κ ^ u)⁻¹ * p ^ (2 * v - u))
        = M * p ^ (2 * v) * ((v.choose u : ℝ) * ((κ * p)⁻¹) ^ u) := by
    intro u hu'
    rw [Finset.mem_Icc] at hu'
    have hple : u ≤ 2 * v := by omega
    have hpow : p ^ (2 * v - u) = p ^ (2 * v) * (p ^ u)⁻¹ := by
      rw [← div_eq_mul_inv, eq_div_iff (by positivity), ← pow_add]
      congr 1
      omega
    rw [hpow, mul_inv, mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_Icc_choose]

/-! ### The geometric-series step -/

/-- `∑_{i<v} r^i ≤ 2` for `0 ≤ r ≤ 1/2`, from `(∑ r^i)·(r−1) = r^v − 1`. -/
lemma geom_sum_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (v : ℕ) :
    ∑ i ∈ Finset.range v, r ^ i ≤ 2 := by
  have hmul := geom_sum_mul r v
  have hrv : (0 : ℝ) ≤ r ^ v := by positivity
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range v, r ^ i :=
    Finset.sum_nonneg fun i _ => pow_nonneg hr0 i
  nlinarith [hmul, hrv, hnn]

/-- **The linearisation of the Janson bracket**: `(1+t)^v − 1 ≤ 2·v·t` once `v·t ≤ 1/2`.

Proved termwise from the binomial expansion using `C(v,u) ≤ v^u`, then summed as a geometric
series — no exponential or logarithm is needed. -/
lemma one_add_pow_sub_one_le {t : ℝ} (ht0 : 0 ≤ t) {v : ℕ} (hvt : (v : ℝ) * t ≤ 1 / 2) :
    (1 + t) ^ v - 1 ≤ 2 * (v : ℝ) * t := by
  rw [← sum_Icc_choose v t]
  have hstep : ∀ u ∈ Finset.Icc 1 v, (v.choose u : ℝ) * t ^ u ≤ ((v : ℝ) * t) ^ u := by
    intro u _
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ht0 u)
    exact_mod_cast Nat.choose_le_pow v u
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hIcc : Finset.Icc 1 v = Finset.Ico 1 (v + 1) := by
    ext u; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have hre : ∀ i ∈ Finset.range v,
      ((v : ℝ) * t) ^ (1 + i) = ((v : ℝ) * t) * ((v : ℝ) * t) ^ i := by
    intro i _
    rw [pow_add, pow_one]
  rw [Finset.sum_congr rfl hre, ← Finset.mul_sum]
  have hrt0 : (0 : ℝ) ≤ (v : ℝ) * t := by positivity
  calc ((v : ℝ) * t) * ∑ i ∈ Finset.range v, ((v : ℝ) * t) ^ i
      ≤ ((v : ℝ) * t) * 2 := mul_le_mul_of_nonneg_left (geom_sum_le_two hrt0 hvt v) hrt0
    _ = 2 * (v : ℝ) * t := by ring

/-- **The `Δ` bound, linearised.** Once `v/(κp) ≤ 1/2`,

`Δ ≤ |supp| · M · p^{2v} · 2v/(κp)`.

Together with `μ = |supp|·p^v` this gives the Janson exponent
`μ²/(4Δ) ≥ |supp|·κ·p/(8·M·v)`, which is the budget. -/
theorem delta_le_linear {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hκ : 0 < κ) (hp : 0 < p)
    (hM : 0 ≤ M) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2) :
    ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
        p ^ (T ∪ T').card
      ≤ ((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) := by
  refine le_trans (delta_le_closed hl hu hκ hp) ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (Nat.cast_nonneg _)
  exact one_add_pow_sub_one_le (by positivity) hvt

omit [DecidableEq α] in
/-- The `μ` of a `v`-uniform system in closed form. -/
lemma mu_eq {X : Finset α} {σ : Finset α → ℕ} {p : ℝ} {v : ℕ} (hu : SuppUniform X σ v) :
    ∑ T ∈ supp X σ, p ^ T.card = ((supp X σ).card : ℝ) * p ^ v := by
  rw [Finset.sum_congr rfl fun T hT => by rw [hu T hT], Finset.sum_const, nsmul_eq_mul]

/-- **The Janson bottom bound**, with an abstract upper bound `D` for the quadratic term.
Chaining `janson_supp_q` through the `p`-biased ↔ fixed-size bridge: for every `q ∈ [0,1]`,

`failCount X σ m₀ ≤ 2 · exp(−q·μ + q²·D) · C(|X|, m₀)`.

This is the exponential replacement for the second-moment estimate of
`SpreadBottom.bottom_le`. -/
theorem failCount_le_janson_gen {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    (hb : WBounded X v σ) {p q D : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hD : ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
        p ^ (T ∪ T').card ≤ D)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- (q * ∑ T ∈ supp X σ, p ^ T.card) + q ^ 2 * D)
        * (X.card.choose m₀ : ℝ)) := by
  classical
  rw [failCount_eq_fixedCount hb m₀]
  refine le_trans (fixedCount_le_two_mul_pBiased (decreasing_uncovered X σ) hp0 hp1 hm₀
    hm₀n hsmall) ?_
  have hjan := janson_supp_q X σ hp0 hp1 hq0 hq1
  have hmono : Real.exp (- (q * ∑ T ∈ supp X σ, p ^ T.card)
      + q ^ 2 * ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
          p ^ (T ∪ T').card)
      ≤ Real.exp (- (q * ∑ T ∈ supp X σ, p ^ T.card) + q ^ 2 * D) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hD (sq_nonneg q)
    linarith
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  have hstep := mul_le_mul_of_nonneg_right (le_trans hjan hmono) hchoose
  linarith

/-- **The optimised Janson bottom bound.** Instantiating `failCount_le_janson_gen` at
`q = μ/(2D)` — admissible exactly when `μ ≤ 2D`, which is the `q ≤ 1` check — turns the
`q`-form into

`failCount X σ m₀ ≤ 2 · exp(−μ²/(4D)) · C(|X|, m₀)`. -/
theorem failCount_le_janson_opt {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    (hb : WBounded X v σ) {p D : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hDpos : 0 < D)
    (hμD : (∑ T ∈ supp X σ, p ^ T.card) ≤ 2 * D)
    (hD : ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
        p ^ (T ∪ T').card ≤ D)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- ((∑ T ∈ supp X σ, p ^ T.card) ^ 2 / (4 * D)))
        * (X.card.choose m₀ : ℝ)) := by
  have hμ0 : (0 : ℝ) ≤ ∑ T ∈ supp X σ, p ^ T.card :=
    Finset.sum_nonneg fun T _ => pow_nonneg hp0 _
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hq0 : 0 ≤ (∑ T ∈ supp X σ, p ^ T.card) / (2 * D) := by positivity
  have hq1 : (∑ T ∈ supp X σ, p ^ T.card) / (2 * D) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hμD
  have hexp : - ((∑ T ∈ supp X σ, p ^ T.card) / (2 * D) * ∑ T ∈ supp X σ, p ^ T.card)
      + ((∑ T ∈ supp X σ, p ^ T.card) / (2 * D)) ^ 2 * D
      = - ((∑ T ∈ supp X σ, p ^ T.card) ^ 2 / (4 * D)) := by
    field_simp
    ring
  have hgen := failCount_le_janson_gen hb hp0 hp1 hq0 hq1 hD hm₀ hm₀n hsmall
  rwa [hexp] at hgen

/-- **The `κ`-budget, explicitly.** Feeding `delta_le_linear` into `failCount_le_janson_opt`
and evaluating `μ²/(4D)` with `μ = |supp|·p^v` gives

`failCount X σ m₀ ≤ 2 · exp(−|supp|·κ·p/(8·M·v)) · C(|X|, m₀)`.

So `failure ≤ β` requires `κ ≳ 8·v·(M/|supp|)·log(1/β)/p` — with `p ≈ α` and weights near `1`
(so `M ≈ |supp|`) this is the paper's `κ ≈ w·log(1/β)/α`, against `w/(αβ)` for the
second-moment route. -/
theorem failCount_le_janson_budget {X : Finset α} {v : ℕ} {σ : Finset α → ℕ} {M κ p : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hN : 0 < (supp X σ).card) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : ((supp X σ).card : ℝ) * p ^ v
      ≤ 2 * (((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- (((supp X σ).card : ℝ) * κ * p / (8 * M * (v : ℝ))))
        * (X.card.choose m₀ : ℝ)) := by
  have hNR : (0 : ℝ) < ((supp X σ).card : ℝ) := by exact_mod_cast hN
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  set D : ℝ := ((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hmu := mu_eq (X := X) (σ := σ) (p := p) hu
  have hopt := failCount_le_janson_opt hb hp.le hp1 hDpos (by rwa [hmu]) 
    (delta_le_linear hl hu hκ hp hM.le hvt) hm₀ hm₀n hsmall
  rw [hmu] at hopt
  -- `μ²/(4D) = N·κ·p/(8·M·v)`
  have hNne : ((supp X σ).card : ℝ) ≠ 0 := ne_of_gt hNR
  have hMne : M ≠ 0 := ne_of_gt hM
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  have hpne : p ≠ 0 := ne_of_gt hp
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have harith : (((supp X σ).card : ℝ) * p ^ v) ^ 2 / (4 * D)
      = ((supp X σ).card : ℝ) * κ * p / (8 * M * (v : ℝ)) := by
    rw [hDdef]
    rw [two_mul, pow_add]
    field_simp
    ring
  rwa [harith] at hopt

/-- **The bottom bound in the iteration's own parameters.** `failCount_le_janson_budget` is
stated in terms of `|supp|`, which is *not* one of `SpreadIterate.iterate_le`'s abstract
parameters — those are `A` (mass lower bound), `M` (link bound) and `κ`. Routing `|supp|`
through `card_supp_ge` (`wTotal·κ^v ≤ |supp|·M`) eliminates it:

`failCount X σ m₀ ≤ 2 · exp(−A·κ^{v+1}·p / (8·M²·v)) · C(|X|, m₀)`.

Note the shape: the exponent carries `κ^{v+1}`, not `κ`. This is the spread hypothesis doing
the work, and it is why the budget is affordable — but it also means the bottom hypothesis
has a *different functional form in `κ`* from `SpreadIterate`'s `hK2`, so plugging Janson in
changes the statement of `iterate_le`, not merely its hypotheses. -/
theorem failCount_le_janson_mass {X : Finset α} {v : ℕ} {σ : Finset α → ℕ} {M κ p A : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hN : 0 < (supp X σ).card) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : ((supp X σ).card : ℝ) * p ^ v
      ≤ 2 * (((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))))
    (_hA0 : 0 ≤ A) (hA : A ≤ (wTotal X σ : ℝ))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- (A * κ ^ (v + 1) * p / (8 * M ^ 2 * (v : ℝ))))
        * (X.card.choose m₀ : ℝ)) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hNR : (0 : ℝ) < ((supp X σ).card : ℝ) := by exact_mod_cast hN
  -- `A·κ^v ≤ |supp|·M`, from `card_supp_ge`
  have hAN : A * κ ^ v ≤ ((supp X σ).card : ℝ) * M :=
    le_trans (mul_le_mul_of_nonneg_right hA (by positivity)) (card_supp_ge hl hu hv hκ)
  refine le_trans (failCount_le_janson_budget hb hl hu hκ hp hp1 hM hv hN hvt hμD
    hm₀ hm₀n hsmall) ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (Nat.cast_nonneg _)) (by norm_num)
  rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hAN
    (show (0 : ℝ) ≤ κ * p * (8 * M * (v : ℝ)) by positivity), hM, hvR, hκ, hp]

/-- **The optimised Janson bound at the `pBiased` level.** Instantiating `janson_supp_q` at
`q = μ/(2D)` with `D` the linearised `Δ` bound, and collapsing `μ²/(4D)` using `μ = |supp|·p^v`:

`Pr[no member of supp is contained in R] ≤ exp(−|supp|·κ·p/(8·M·v))`.

Everything downstream — the `failCount` chain and the satisfying property — reads off this. -/
theorem pBiased_uncovered_le_exp {X : Finset α} {v : ℕ} {σ : Finset α → ℕ} {M κ p : ℝ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hN : 0 < (supp X σ).card) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : ((supp X σ).card : ℝ) * p ^ v
      ≤ 2 * (((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)))) :
    pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- (((supp X σ).card : ℝ) * κ * p / (8 * M * (v : ℝ)))) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hNR : (0 : ℝ) < ((supp X σ).card : ℝ) := by exact_mod_cast hN
  set N : ℝ := ((supp X σ).card : ℝ) with hNdef
  set μ : ℝ := ∑ T ∈ supp X σ, p ^ T.card with hμdef
  set Δ : ℝ := ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
    p ^ (T ∪ T').card with hΔdef
  set D : ℝ := N * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) with hDdef
  have hDpos : 0 < D := by rw [hDdef, hNdef]; positivity
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hΔD : Δ ≤ D := by
    rw [hΔdef, hDdef, hNdef]; exact delta_le_linear hl hu hκ hp hM.le hvt
  have hμN : μ = N * p ^ v := by rw [hμdef, hNdef]; exact mu_eq hu
  have hμ0 : 0 ≤ μ := by rw [hμdef]; exact Finset.sum_nonneg fun T _ => pow_nonneg hp.le _
  set q : ℝ := μ / (2 * D) with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one (by linarith)]
    rw [hμN]
    rw [hDdef]
    exact hμD
  have hjan : pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- (q * μ) + q ^ 2 * Δ) := by
    rw [hμdef, hΔdef]; exact janson_supp_q X σ hp.le hp1 hq0 hq1
  refine le_trans hjan (Real.exp_le_exp.mpr ?_)
  have h1 : q ^ 2 * Δ ≤ q ^ 2 * D := mul_le_mul_of_nonneg_left hΔD (sq_nonneg q)
  have h2 : - (q * μ) + q ^ 2 * D = - (μ ^ 2 / (4 * D)) := by
    rw [hqdef]; field_simp; ring
  have hMne : M ≠ 0 := ne_of_gt hM
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  have hpne : p ≠ 0 := ne_of_gt hp
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hNne : N ≠ 0 := by rw [hNdef]; exact ne_of_gt hNR
  have h3 : μ ^ 2 / (4 * D) = N * κ * p / (8 * M * (v : ℝ)) := by
    rw [hμN, hDdef, two_mul, pow_add]
    field_simp; ring
  linarith [h1, h2, h3]

/-! ### The bottom step in the form the iteration consumes -/

/-- **The Janson bottom step.** `SpreadIterate` consumes the bottom estimate as a bound on
the failure *fraction* by an allowance `εbot`. Converting the exponential bound into that
form is where `Real.log` enters:

if `log(2/εbot) ≤ A·κ^{v+1}·p/(8·M²·v)` then `failCount X σ m₀ ≤ εbot · C(|X|, m₀)`.

Read the other way, this is the κ-budget: the bottom allowance `εbot` costs
`log(1/εbot)` in `κ`, not `1/εbot`. That is exactly the improvement Janson buys over the
second moment, and it is the reason `Real.log` cannot be avoided here — the present
`SpreadAssemble` does its whole constant chase in `Nat.log` precisely because the
second-moment shape let it. -/
theorem failCount_le_of_janson_budget {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {M κ p A εbot : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hN : 0 < (supp X σ).card) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : ((supp X σ).card : ℝ) * p ^ v
      ≤ 2 * (((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))))
    (hA0 : 0 ≤ A) (hA : A ≤ (wTotal X σ : ℝ))
    (hεb : 0 < εbot)
    (hbudget : Real.log (2 / εbot) ≤ A * κ ^ (v + 1) * p / (8 * M ^ 2 * (v : ℝ)))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
  have hmass := failCount_le_janson_mass hb hl hu hκ hp hp1 hM hv hN hvt hμD hA0 hA
    hm₀ hm₀n hsmall
  -- `exp(−E) ≤ exp(−log(2/εbot)) = εbot/2`
  have hpos : (0 : ℝ) < 2 / εbot := by positivity
  have hexp : Real.exp (- (A * κ ^ (v + 1) * p / (8 * M ^ 2 * (v : ℝ)))) ≤ εbot / 2 := by
    refine le_trans (Real.exp_le_exp.mpr (neg_le_neg hbudget)) ?_
    rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  calc (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- (A * κ ^ (v + 1) * p / (8 * M ^ 2 * (v : ℝ))))
          * (X.card.choose m₀ : ℝ)) := hmass
    _ ≤ 2 * ((εbot / 2) * (X.card.choose m₀ : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hchoose) (by norm_num)
    _ = εbot * (X.card.choose m₀ : ℝ) := by ring

/-! ### The heaviest-class reduction: from uniform to bounded systems

`failCount_le_of_janson_budget` requires `SuppUniform X σ v` — members of size *exactly* `v` —
whereas the iteration hands its bottom step a merely `≤ v`-bounded system (`WBounded X v σ`),
whose residual systems are genuinely mixed-size. `SpreadBottom.bottom_le` meets the same
obstacle and resolves it by restricting to the **heaviest size class**, which is uniform by
construction and carries a `1/v` fraction of the mass. This section does the same for the
Janson bottom.

The restriction costs a factor `v` in the mass and, because the heaviest class may sit at any
width `u ∈ [1, v]`, forces the exponent to be taken at its worst case over `u`: the budget
`A·κ^{v+1}·p/(8M²v)` of `failCount_le_janson_mass` degrades to `A·κ²·p/(8M²v²)`, using
`κ^{u+1}/u ≥ κ²/v` for `1 ≤ u ≤ v` and `κ ≥ 1`. Only the coefficient in the exponent is lost;
the `log(1/εbot)` dependence — the whole point of the Janson route — survives untouched. -/

/-- The `u`-th **size class** of a weighted system: the members of size exactly `u`, carrying
their original weights, everything else zeroed out. -/
def sizeClass (σ : Finset α → ℕ) (u : ℕ) : Finset α → ℕ :=
  fun S => if S.card = u then σ S else 0

omit [DecidableEq α] in
lemma sizeClass_le (σ : Finset α → ℕ) (u : ℕ) (S : Finset α) : sizeClass σ u S ≤ σ S := by
  show (if S.card = u then σ S else 0) ≤ σ S
  split
  · exact le_rfl
  · exact Nat.zero_le _

omit [DecidableEq α] in
lemma sizeClass_ne_zero {σ : Finset α → ℕ} {u : ℕ} {S : Finset α}
    (h : sizeClass σ u S ≠ 0) : S.card = u ∧ σ S ≠ 0 := by
  by_cases hc : S.card = u
  · refine ⟨hc, fun h0 => h ?_⟩
    show (if S.card = u then σ S else 0) = 0
    rw [if_pos hc, h0]
  · exact absurd (show (if S.card = u then σ S else 0) = 0 from if_neg hc) h

omit [DecidableEq α] in
/-- A size class is `u`-bounded (indeed `u`-uniform). -/
lemma wBounded_sizeClass {X : Finset α} {σ : Finset α → ℕ} {v : ℕ} (hb : WBounded X v σ)
    (u : ℕ) : WBounded X u (sizeClass σ u) := by
  intro S hS
  obtain ⟨hc, hσ⟩ := sizeClass_ne_zero hS
  exact ⟨(hb S hσ).1, hc.le⟩

omit [DecidableEq α] in
/-- The support of a size class is uniform: this is what the Janson estimates need and what
the iteration's systems fail to provide. -/
lemma suppUniform_sizeClass (X : Finset α) (σ : Finset α → ℕ) (u : ℕ) :
    SuppUniform X (sizeClass σ u) u := fun _ hT => (sizeClass_ne_zero (mem_supp.mp hT).2).1

lemma wLink_sizeClass_le (X : Finset α) (σ : Finset α → ℕ) (u : ℕ) (T : Finset α) :
    wLink X (sizeClass σ u) T ≤ wLink X σ T :=
  Finset.sum_le_sum fun S _ => sizeClass_le σ u S

/-- Spreadness is inherited by size classes: zeroing weights only shrinks links. -/
lemma wLinkBounded_sizeClass {X : Finset α} {σ : Finset α → ℕ} {M κ : ℝ} (hκ : 0 ≤ κ)
    (hl : WLinkBounded X σ M κ) (u : ℕ) : WLinkBounded X (sizeClass σ u) M κ := by
  intro T hT
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) (hl T hT)
  exact_mod_cast wLink_sizeClass_le X σ u T

omit [DecidableEq α] in
/-- Failures of the whole system are failures of each class: a set covered by the class is
covered by the system. -/
lemma failCount_le_sizeClass (X : Finset α) (σ : Finset α → ℕ) (u m : ℕ) :
    failCount X σ m ≤ failCount X (sizeClass σ u) m := by
  classical
  simp only [failCount]
  refine Finset.card_le_card fun W hW => ?_
  rw [Finset.mem_filter] at hW ⊢
  refine ⟨hW.1, fun hcov => hW.2 ?_⟩
  obtain ⟨S, hS0, hSW⟩ := hcov
  exact ⟨S, (sizeClass_ne_zero hS0).2, hSW⟩

omit [DecidableEq α] in
/-- The mass of a `≤ v`-bounded system with no empty member splits over its `v` size classes. -/
lemma wTotal_eq_sum_sizeClass {X : Finset α} {σ : Finset α → ℕ} {v : ℕ}
    (hb : WBounded X v σ) (hE : σ ∅ = 0) :
    wTotal X σ = ∑ u ∈ Finset.Icc 1 v, wTotal X (sizeClass σ u) := by
  classical
  have hcl : ∀ u : ℕ, wTotal X (sizeClass σ u)
      = ∑ S ∈ X.powerset, (if S.card = u then σ S else 0) := fun _ => rfl
  rw [Finset.sum_congr rfl fun u _ => hcl u, Finset.sum_comm, wTotal]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hσS : σ S = 0
  · simp [hσS]
  · have h1 : 1 ≤ S.card := by
      rcases Finset.eq_empty_or_nonempty S with rfl | hne
      · exact absurd hE hσS
      · exact Finset.card_pos.mpr hne
    have h2 : S.card ≤ v := (hb S hσS).2
    rw [Finset.sum_ite_eq (Finset.Icc 1 v) S.card (fun _ => σ S),
      if_pos (Finset.mem_Icc.mpr ⟨h1, h2⟩)]

omit [DecidableEq α] in
/-- **Pigeonhole on size classes.** Some class `u ∈ [1, v]` carries at least a `1/v` fraction
of the mass. (Compare the same step inside `SpreadBottom.bottom_le`.) -/
lemma exists_heavy_sizeClass {X : Finset α} {σ : Finset α → ℕ} {v : ℕ}
    (hb : WBounded X v σ) (hE : σ ∅ = 0) (hv : 1 ≤ v) :
    ∃ u ∈ Finset.Icc 1 v, wTotal X σ ≤ v * wTotal X (sizeClass σ u) := by
  classical
  rcases Nat.eq_zero_or_pos (wTotal X σ) with h0 | hpos
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hv⟩, by omega⟩
  by_contra hcon
  push Not at hcon
  have hsplit := wTotal_eq_sum_sizeClass hb hE
  have hle : ∀ u ∈ Finset.Icc 1 v, v * wTotal X (sizeClass σ u) ≤ wTotal X σ - 1 := by
    intro u hu
    have := hcon u hu
    omega
  have hsum : v * wTotal X σ ≤ v * (wTotal X σ - 1) := by
    calc v * wTotal X σ = ∑ u ∈ Finset.Icc 1 v, v * wTotal X (sizeClass σ u) := by
          rw [hsplit, Finset.mul_sum]
      _ ≤ ∑ _u ∈ Finset.Icc 1 v, (wTotal X σ - 1) := Finset.sum_le_sum hle
      _ = v * (wTotal X σ - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  have := Nat.le_of_mul_le_mul_left hsum (by omega : 0 < v)
  omega

omit [DecidableEq α] in
/-- A system with positive mass has nonempty support. -/
lemma card_supp_pos {X : Finset α} {σ : Finset α → ℕ} (h : 0 < wTotal X σ) :
    0 < (supp X σ).card := by
  classical
  rw [Finset.card_pos]
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  have hzero : wTotal X σ = 0 := by
    rw [wTotal]
    refine Finset.sum_eq_zero fun S hS => ?_
    by_contra hσ
    have hmem : S ∈ supp X σ := mem_supp.mpr ⟨Finset.mem_powerset.mp hS, hσ⟩
    rw [hcon] at hmem
    exact absurd hmem (Finset.notMem_empty S)
  omega

/-- **The Janson bottom step for bounded systems.** The uniformity hypothesis of
`failCount_le_of_janson_budget` is discharged by passing to the heaviest size class:

if `log(2/εbot) ≤ A·κ²·p/(8·M²·v²)` then `failCount X σ m₀ ≤ εbot · C(|X|, m₀)`,

for any `≤ v`-bounded `κ`-spread system of mass at least `A`. This is the form
`SpreadIterate.iterate_le_of_bottom` consumes — `WBounded` in, failure fraction out — so it is
the Janson replacement for `SpreadBottom.bottom_le`, with the bottom allowance `εbot` costing
`log(1/εbot)` in `κ` rather than `1/εbot`.

The side condition `κ·p ≤ 4·M·p^v` is the `q ≤ 1` check of the Janson optimisation
(`μ ≤ 2Δ`-bound), transported to every class at once. -/
theorem failCount_le_of_janson_bounded {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {M κ p A εbot : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 1 ≤ v)
    (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hq : κ * p ≤ 4 * M * p ^ v)
    (hA0 : 0 < A) (hA : A ≤ (wTotal X σ : ℝ))
    (hεb : 0 < εbot)
    (hbudget : Real.log (2 / εbot) ≤ A * κ ^ 2 * p / (8 * M ^ 2 * (v : ℝ) ^ 2))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
  classical
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκp : (0 : ℝ) < κ * p := mul_pos hκ0 hp
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  by_cases hE : σ ∅ ≠ 0
  · rw [failCount_eq_zero_of_empty_mem X σ m₀ hE, Nat.cast_zero]
    exact mul_nonneg hεb.le (Nat.cast_nonneg _)
  rw [not_not] at hE
  -- the heaviest class: uniform, still spread, and it inherits every failure
  obtain ⟨u, huIcc, hheavy⟩ := exists_heavy_sizeClass hb hE hv
  rw [Finset.mem_Icc] at huIcc
  obtain ⟨hu1, huv⟩ := huIcc
  set τ : Finset α → ℕ := sizeClass σ u with hτ
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu1
  have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have hAu : A / (v : ℝ) ≤ (wTotal X τ : ℝ) := by
    rw [div_le_iff₀ hvR]
    have hcast : (wTotal X σ : ℝ) ≤ (v : ℝ) * (wTotal X τ : ℝ) := by exact_mod_cast hheavy
    nlinarith [hA, hcast]
  have hAvpos : (0 : ℝ) < A / (v : ℝ) := div_pos hA0 hvR
  have hwpos : 0 < wTotal X τ := by
    by_contra hcon
    push Not at hcon
    have hz : wTotal X τ = 0 := Nat.le_zero.mp hcon
    rw [hz, Nat.cast_zero] at hAu
    linarith
  have hN : 0 < (supp X τ).card := card_supp_pos hwpos
  -- the `q ≤ 1` check for the class, from the width-`v` form
  have hμD : ((supp X τ).card : ℝ) * p ^ u
      ≤ 2 * (((supp X τ).card : ℝ) * (M * p ^ (2 * u) * (2 * (u : ℝ) * (κ * p)⁻¹))) := by
    have hkey : κ * p ≤ 4 * (u : ℝ) * M * p ^ u := by
      have hpu : p ^ v ≤ p ^ u := pow_le_pow_of_le_one hp.le hp1 huv
      have h1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      calc κ * p ≤ 4 * M * p ^ v := hq
        _ ≤ 4 * M * p ^ u := mul_le_mul_of_nonneg_left hpu (by positivity)
        _ ≤ 4 * (u : ℝ) * M * p ^ u := by
            have hge : 0 ≤ M * p ^ u * ((u : ℝ) - 1) :=
              mul_nonneg (mul_nonneg hM.le (pow_nonneg hp.le u)) (by linarith)
            nlinarith [hge]
    have hrw : 2 * (((supp X τ).card : ℝ) * (M * p ^ (2 * u) * (2 * (u : ℝ) * (κ * p)⁻¹)))
        = (((supp X τ).card : ℝ) * p ^ u) * ((4 * (u : ℝ) * M * p ^ u) / (κ * p)) := by
      rw [two_mul u, pow_add]
      field_simp
      ring
    rw [hrw]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [le_div_iff₀ hκp, one_mul]
    exact hkey
  -- the budget, taken at its worst case over the class width `u ∈ [1, v]`
  have hbudget' : Real.log (2 / εbot)
      ≤ A / (v : ℝ) * κ ^ (u + 1) * p / (8 * M ^ 2 * (u : ℝ)) := by
    refine le_trans hbudget ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hκ2 : κ ^ 2 ≤ κ ^ (u + 1) := pow_le_pow_right₀ hκ (by omega)
    have hlhs : A * κ ^ 2 * p * (8 * M ^ 2 * (u : ℝ))
        = (A * p * (8 * M ^ 2)) * (κ ^ 2 * (u : ℝ)) := by ring
    have hrhs : A / (v : ℝ) * κ ^ (u + 1) * p * (8 * M ^ 2 * (v : ℝ) ^ 2)
        = (A * p * (8 * M ^ 2)) * (κ ^ (u + 1) * (v : ℝ)) := by
      field_simp
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hκ2 huvR huR.le (by positivity))
      (by positivity)
  have hmain := failCount_le_of_janson_budget (X := X) (v := u) (σ := τ) (M := M) (κ := κ)
    (p := p) (A := A / (v : ℝ)) (εbot := εbot)
    (wBounded_sizeClass hb u) (wLinkBounded_sizeClass hκ0.le hl u)
    (suppUniform_sizeClass X σ u) hκ0 hp hp1 hM hu1 hN
    (le_trans (mul_le_mul_of_nonneg_right huvR (by positivity)) hvt) hμD
    hAvpos.le hAu hεb hbudget' hm₀ hm₀n hsmall
  refine le_trans ?_ hmain
  exact_mod_cast failCount_le_sizeClass X σ u m₀

/-! ### Towards Theorem 1.9: from Janson to Definition 1.5

Theorem 1.9 concludes that a system is an `(a,b)`-*robust sunflower* — via Definition 1.7,
that its link at the kernel is `(a,b)`-*satisfying* (Definition 1.5). Definition 1.5 is a
statement about the `p`-biased probability that a random set *contains* a member, which is
the complement of the event Janson bounds. -/

/-- **Janson gives Definition 1.5.** If the uncovered probability is below `b`, the support is
`(p, b)`-satisfying. -/
theorem isSatisfying_of_uncovered_lt {X : Finset α} {σ : Finset α → ℕ} {p b : ℝ}
    (h : pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) < b) :
    IsSatisfying p b X (supp X σ) := by
  classical
  have hsum := pBiased_add_not X p (fun R => ∃ S ∈ supp X σ, S ⊆ R)
  have hcg : pBiased X p (fun R => ¬ ∃ S ∈ supp X σ, S ⊆ R)
      = pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) :=
    pBiased_congr X p fun R =>
      ⟨fun hh T hT hTR => hh ⟨T, hT, hTR⟩, fun hh hex => by
        obtain ⟨T, hT, hTR⟩ := hex; exact hh T hT hTR⟩
  rw [hcg] at hsum
  rw [IsSatisfying]
  linarith

/-- **The satisfying property from the `κ`-budget** — ALWZ's Theorem 2.5 shape, with the
`log(1/b)` dependence Janson provides: a `v`-uniform `κ`-spread system whose Janson exponent
exceeds `log(1/b)` is `(p, b)`-satisfying, i.e. satisfies Definition 1.5. -/
theorem isSatisfying_of_janson {X : Finset α} {v : ℕ} {σ : Finset α → ℕ} {M κ p b : ℝ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hN : 0 < (supp X σ).card) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : ((supp X σ).card : ℝ) * p ^ v
      ≤ 2 * (((supp X σ).card : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))))
    (hb : 0 < b)
    (hbudget : Real.log (1 / b)
      < ((supp X σ).card : ℝ) * κ * p / (8 * M * (v : ℝ))) :
    IsSatisfying p b X (supp X σ) := by
  refine isSatisfying_of_uncovered_lt (lt_of_le_of_lt
    (pBiased_uncovered_le_exp hl hu hκ hp hp1 hM hv hN hvt hμD) ?_)
  have hbne : (0 : ℝ) < 1 / b := by positivity
  calc Real.exp (- (((supp X σ).card : ℝ) * κ * p / (8 * M * (v : ℝ))))
      < Real.exp (- Real.log (1 / b)) := Real.exp_lt_exp.mpr (by linarith)
    _ = b := by rw [Real.exp_neg, Real.exp_log hbne, one_div, inv_inv]

/-! ### Definition 1.5 ⟹ Definition 1.7 -/

/-- The `p`-biased marginal on `X \ Y`: an event determined by `R \ Y` has the same
probability under `U(X,p)` and under `U(X \ Y, p)`. -/
lemma pBiased_marginal_sdiff {X Y : Finset α} (hY : Y ⊆ X) {p : ℝ} {Q : Finset α → Prop}
    [DecidablePred Q] (hQ : ∀ R, Q R ↔ Q (R \ Y)) :
    pBiased X p Q = pBiased (X \ Y) p Q := by
  classical
  rw [pBiased_eq_sum_wt, pBiased_eq_sum_wt]
  have key : ∀ F₁ F₂ : Finset α → ℝ,
      ∑ R ∈ X.powerset, F₁ (R ∩ Y) * F₂ (R \ Y)
        = (∑ A ∈ Y.powerset, F₁ A) * ∑ B ∈ (X \ Y).powerset, F₂ B := by
    intro F₁ F₂
    rw [sum_powerset_split hY fun A B => F₁ A * F₂ B, Finset.sum_mul_sum]
  have hA1 : ∑ A ∈ Y.powerset, wt Y p A = 1 := sum_wt _ _
  have h := key (fun A => wt Y p A) fun B => wt (X \ Y) p B * (if Q B then (1 : ℝ) else 0)
  rw [hA1, one_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [wt_split hY (Finset.mem_powerset.mp hR)]
  by_cases hQR : Q R
  · have hQ' : Q (R \ Y) := (hQ R).mp hQR
    simp [hQR, hQ']
  · have hQ' : ¬ Q (R \ Y) := fun hh => hQR ((hQ R).mpr hh)
    simp [hQR, hQ']

/-- **ALWZ's remark following Definition 1.7**: an `(a,b)`-satisfying `w`-uniform system with
at least two members is an `(a,b)`-robust sunflower.

Two things to check. The kernel is not a member: it is contained in every member, and all
members have the same cardinality `w`, so a kernel in the family would force every member to
equal it, contradicting `2 ≤ |𝓕|`. And the link at the kernel is satisfying: a random
`R ⊆ X` containing some `S ∈ 𝓕` has `R \ K ⊇ S \ K`, and `R \ K` is distributed as
`U(X \ K, a)` — which is `pBiased_marginal_sdiff`, the step the paper leaves as "clearly". -/
theorem isRobustSunflower_of_isSatisfying {a b : ℝ} {w : ℕ} {X : Finset α}
    {𝓕 : Finset (Finset α)} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hsub : ∀ S ∈ 𝓕, S ⊆ X)
    (hu : IsUniform w 𝓕) (h2 : 2 ≤ 𝓕.card) (hsat : IsSatisfying a b X 𝓕) :
    IsRobustSunflower a b X 𝓕 := by
  classical
  obtain ⟨S₀, hS₀, S₁, hS₁, hne⟩ := Finset.one_lt_card.mp h2
  have hne𝓕 : 𝓕.Nonempty := ⟨S₀, hS₀⟩
  have hKX : kernel 𝓕 ⊆ X := (kernel_subset hS₀).trans (hsub S₀ hS₀)
  -- (i) the kernel is not a member
  have hKnot : kernel 𝓕 ∉ 𝓕 := by
    intro hK
    have hall : ∀ S ∈ 𝓕, S = kernel 𝓕 := by
      intro S hS
      exact (Finset.eq_of_subset_of_card_le (kernel_subset hS)
        (by rw [hu hS, hu hK])).symm
    exact hne ((hall S₀ hS₀).trans (hall S₁ hS₁).symm)
  refine ⟨hKnot, ?_⟩
  -- (ii) the link at the kernel is satisfying
  set K : Finset α := kernel 𝓕 with hKdef
  set Q : Finset α → Prop := fun R => ∃ P ∈ link 𝓕 K, P ⊆ R with hQdef
  have hQmarg : ∀ R : Finset α, Q R ↔ Q (R \ K) := by
    intro R
    constructor
    · rintro ⟨P, hP, hPR⟩
      refine ⟨P, hP, fun x hx => ?_⟩
      rw [Finset.mem_sdiff]
      exact ⟨hPR hx, fun hxK => (Finset.disjoint_left.mp (disjoint_of_mem_link hP)) hx hxK⟩
    · rintro ⟨P, hP, hPR⟩
      exact ⟨P, hP, hPR.trans Finset.sdiff_subset⟩
  have hmarg : pBiased X a Q = pBiased (X \ K) a Q := pBiased_marginal_sdiff hKX hQmarg
  -- containing a member of `𝓕` implies containing a member of the link
  have himp : ∀ R : Finset α, (∃ S ∈ 𝓕, S ⊆ R) → Q R := by
    rintro R ⟨S, hS, hSR⟩
    refine ⟨S \ K, ?_, (Finset.sdiff_subset).trans hSR⟩
    rw [mem_link]
    exact ⟨S, hS, kernel_subset hS, rfl⟩
  have hmono : pBiased X a (fun R => ∃ S ∈ 𝓕, S ⊆ R) ≤ pBiased X a Q :=
    pBiased_mono ha0 ha1 X himp
  have hsat' : 1 - b < pBiased X a (fun R => ∃ S ∈ 𝓕, S ⊆ R) := hsat
  rw [IsSatisfying, ← hmarg]
  linarith

/-! ### The spread/link dichotomy

`kernel_eq_empty_of_isSpread` and `isRobustSunflower_above_spread_core` — the assembly of a
spread, satisfying link into a robust sunflower — live in `Sunflower.Robust`, shared with the
Rao route. -/

/-! ### The quantitative side: spread families as weighted systems

The Janson chain is stated for a weighted system `σ`. The top-level theorem applies it to an
unweighted family `𝓖` — the link produced by `exists_spread_link` — via the indicator weight.

The point of this translation is that for the indicator weight `M = wTotal = |supp| = |𝓖|`,
so the ratio `M/|supp|` in the budget is **exactly `1`**: the exponent `N·κ·p/(8·M·v)`
collapses to `κ·p/(8·v)`, and the budget is the paper's `κ ≳ v·log(1/b)/p` with nothing lost.
(The ratio is what *weights* cost; unweighted systems pay nothing.) -/

/-- The indicator weight of a family. -/
def indW (𝓖 : Finset (Finset α)) : Finset α → ℕ := fun S => if S ∈ 𝓖 then 1 else 0

@[simp] lemma indW_ne_zero {𝓖 : Finset (Finset α)} {S : Finset α} :
    indW 𝓖 S ≠ 0 ↔ S ∈ 𝓖 := by
  rw [indW]; split <;> simp_all

lemma supp_indW {X : Finset α} {𝓖 : Finset (Finset α)} (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) :
    supp X (indW 𝓖) = 𝓖 := by
  ext S
  rw [mem_supp, indW_ne_zero]
  exact ⟨fun h => h.2, fun h => ⟨h𝓖 S h, h⟩⟩

lemma wLink_indW {X : Finset α} {𝓖 : Finset (Finset α)} (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X)
    (T : Finset α) : wLink X (indW 𝓖) T = (link 𝓖 T).card := by
  classical
  rw [wLink, card_link]
  simp only [indW]
  rw [Finset.sum_boole, Nat.cast_id]
  refine congrArg Finset.card ?_
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h𝓖 S h.1, h.2⟩, h.1⟩⟩

lemma wTotal_indW {X : Finset α} {𝓖 : Finset (Finset α)} (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) :
    wTotal X (indW 𝓖) = 𝓖.card := by
  have h := wLink_indW h𝓖 (∅ : Finset α)
  rw [wLink_empty] at h
  rw [h, card_link, Finset.filter_true_of_mem fun S _ => Finset.empty_subset S]

lemma wBounded_indW {X : Finset α} {𝓖 : Finset (Finset α)} {v : ℕ}
    (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) (hu : IsUniform v 𝓖) : WBounded X v (indW 𝓖) := by
  intro S hS
  rw [indW_ne_zero] at hS
  exact ⟨h𝓖 S hS, (hu hS).le⟩

lemma suppUniform_indW {X : Finset α} {𝓖 : Finset (Finset α)} {v : ℕ}
    (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) (hu : IsUniform v 𝓖) : SuppUniform X (indW 𝓖) v := by
  intro T hT
  rw [supp_indW h𝓖] at hT
  exact hu hT

/-- Spreadness of `𝓖` is exactly `WLinkBounded` for its indicator weight, with `M = |𝓖|`. -/
lemma wLinkBounded_indW {X : Finset α} {𝓖 : Finset (Finset α)} {κ : ℝ}
    (h𝓖 : ∀ S ∈ 𝓖, S ⊆ X) (hsp : IsSpread κ 𝓖) :
    WLinkBounded X (indW 𝓖) (𝓖.card : ℝ) κ := by
  intro T _
  rw [wLink_indW h𝓖 T]
  exact hsp T

/-- **ALWZ's Theorem 2.5, unweighted form.** A `v`-uniform `κ`-spread family whose Janson
exponent `κ·p/(8·v)` exceeds `log(1/b)` is `(p, b)`-satisfying.

The `M/|supp|` ratio that the weighted statement carries is `1` here, since the indicator
weight has `M = wTotal = |supp| = |𝓖|`. So the budget is exactly

`κ ≳ 8·v·log(1/b)/p`,

the paper's `κ ≈ w·log(1/β)/α`, with no loss — against `w/(αβ)` for the second-moment
route. -/
theorem isSatisfying_of_isSpread {X : Finset α} {𝓖 : Finset (Finset α)} {v : ℕ} {κ p b : ℝ}
    (h𝓖X : ∀ S ∈ 𝓖, S ⊆ X) (hu : IsUniform v 𝓖) (hne : 𝓖.Nonempty) (hsp : IsSpread κ 𝓖)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hv : 0 < v)
    (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : (𝓖.card : ℝ) * p ^ v
      ≤ 2 * ((𝓖.card : ℝ) * ((𝓖.card : ℝ) * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))))
    (hb : 0 < b) (hbudget : Real.log (1 / b) < κ * p / (8 * (v : ℝ))) :
    IsSatisfying p b X 𝓖 := by
  classical
  have hsupp : supp X (indW 𝓖) = 𝓖 := supp_indW h𝓖X
  have hNpos : 0 < (supp X (indW 𝓖)).card := by rw [hsupp]; exact Finset.card_pos.mpr hne
  have hMpos : (0 : ℝ) < (𝓖.card : ℝ) := by
    have : 0 < 𝓖.card := Finset.card_pos.mpr hne
    exact_mod_cast this
  have hres := isSatisfying_of_janson (X := X) (v := v) (σ := indW 𝓖) (M := (𝓖.card : ℝ))
    (κ := κ) (p := p) (b := b)
    (wLinkBounded_indW h𝓖X hsp) (suppUniform_indW h𝓖X hu) hκ hp hp1 hMpos hv hNpos
    hvt (by rwa [hsupp]) hb ?_
  · rwa [hsupp] at hres
  · -- the exponent collapses: `N·κ·p/(8·M·v) = κ·p/(8·v)` because `M = N = |𝓖|`
    rw [hsupp]
    have hcollapse : (𝓖.card : ℝ) * κ * p / (8 * (𝓖.card : ℝ) * (v : ℝ))
        = κ * p / (8 * (v : ℝ)) := by
      field_simp
    rwa [hcollapse]

/-!
## What remains

`mu_ge` and `delta_le` are the two estimates ALWZ's Lemma 2.10 needs, and together with
`Sunflower.JansonCover.failCount_le_two_mul_exp` they give an *exponentially* small failure
bound where `SpreadBottom.bottom_le` gives a polynomial one. Three things are still missing
before this can replace `bottom_le` in `SpreadIterate`:

1. **The binomial regrouping** — done (`delta_le_binom`).

2. **The `q`-interface** — done (`JansonCover.janson_supp_q`), the form with no side
   conditions on `μ` and `Δ`, so `delta_le_binom` substitutes directly.

3. **The `κ`-budget.** With `delta_le_closed` the picture is explicit. Writing `N = |supp|`
   and `t = 1/(κp)`, and using `μ = N·p^v`,

     `μ²/(4Δ) ≥ (N p^v)² / (4·N·M·p^{2v}·((1+t)^v − 1)) = N / (4·M·((1+t)^v − 1))`.

   Once `v·t ≤ 1/2` one has `(1+t)^v − 1 = ∑_{u≥1} C(v,u)t^u ≤ ∑_{u≥1}(vt)^u ≤ 2vt`
   (using `C(v,u) ≤ v^u` and a geometric series), so the exponent is at least

     `N·κ·p / (8·M·v)`,

   and `failure ≤ β` requires **`κ ≳ 8·v·(M/N)·log(1/β)/p`**. With `p ≈ α` and weights near
   `1` (so `M ≈ N`) this is the paper's `κ ≈ w·log(1/β)/α`, against `w/(αβ)` for the
   second-moment route — the whole point of the exercise. Note the ratio `M/N` is what the
   weights cost: `card_supp_ge` gives `N ≥ A·κ^v/M`, and it is genuinely needed, because the
   covering event depends only on the *support* while the hypotheses constrain *mass*.

   All of this is now proved: `one_add_pow_sub_one_le` (geometric step), `delta_le_linear`
   (linearised `Δ`), `failCount_le_janson_opt` (the `q = μ/(2D)` choice with its `q ≤ 1`
   check), and `failCount_le_janson_budget` (the explicit exponent `N·κ·p/(8·M·v)`).

   `failCount_le_janson_mass` puts the bound in `iterate_le`'s own parameters `(A, M, κ)`, and
   `failCount_le_of_janson_budget` puts it in the form the iteration consumes — a failure
   fraction bounded by an allowance `εbot`, at the cost `log(1/εbot)` in `κ`.

   `pBiased_uncovered_le_exp` is the optimised bound at the `pBiased` level, and
   `isSatisfying_of_janson` reads Definition 1.5 off it: a `v`-uniform `κ`-spread system
   whose Janson exponent exceeds `log(1/b)` is `(p,b)`-satisfying. That is ALWZ's Theorem 2.5
   shape, with the `log(1/b)` dependence in place of the second moment's `1/b`.

   `isRobustSunflower_of_isSatisfying` closes Definition 1.5 ⟹ Definition 1.7, so the
   conclusion side of Theorem 1.9 is complete: spread ⟹ satisfying ⟹ robust sunflower.

   `isRobustSunflower_above_spread_core` closes the structural side: `exists_spread_link`
   produces a core `Z` with `|Z| < w` whose link is `κ`-spread, the Janson chain makes that
   link `(a,b)`-satisfying, and this lemma packages `{S ∈ 𝓕 : Z ⊆ S}` as an `(a,b)`-robust
   sunflower inside `𝓕`. The kernel of that subfamily is exactly `Z`, which is
   `kernel_eq_empty_of_isSpread` — spreadness with `κ > 1` leaves no element common to every
   member of the link.

   On the quantitative side, `isSatisfying_of_isSpread` is ALWZ's Theorem 2.5 in its
   unweighted form, with the budget `κ ≳ 8·v·log(1/b)/p` and **no `M/|supp|` loss** — the
   indicator weight has `M = wTotal = |supp| = |𝓖|`, so the ratio is `1`. The ratio is what
   *weights* cost, and the top-level theorem is unweighted.

   What is left is the iteration. Two observations should shape how it is attempted.

### The iteration is load-bearing, not just a better constant

`isSatisfying_of_isSpread` is ALWZ's Lemma 2.10, and they apply it at the **bottom of the
width schedule**, where `v = O(log log w)` — not at full width. Chaining
`exists_spread_link → isSatisfying_of_isSpread → isRobustSunflower_above_spread_core`
directly is sound, but needs `2w ≤ κa` and `log(1/b) < κa/(8w)`, giving a size hypothesis of
the form `(C·w·log(1/b)/a)^w`: **linear in `w` where the paper has `log w·log log w`**. No
amount of constant-chasing at the top level recovers that; only the width schedule does.
(The `log(1/b)` dependence *is* already the paper's — that part Janson delivers.)

### The swap point is `iterate_bottom`, and the shape already matches

`SpreadIterate.iterate_le` does not call `SpreadBottom.bottom_le` directly. It calls the
helper `iterate_bottom`, in exactly two places (the `t = 0` case and the `v ≤ 2L` branch of
the successor case), and consumes its conclusion as

  `failCount X σ m ≤ εbot * (X.card.choose m : ℝ)`

— which is precisely the shape of `failCount_le_of_janson_budget` above. So the two routes
differ only in how that one estimate is *established*, not in what it says.

The right refactor is therefore **not** to rewrite `iterate_le`: it is to abstract it over its
bottom step, replacing the hypotheses `hK2`, `hK3` (which exist only to feed `iterate_bottom`)
by the bottom estimate itself as a hypothesis. Both the second-moment route and the Janson
route then instantiate the same `iterate_le`, and `SpreadAssemble`'s constant chase is redone
only for the new instantiation — with `Real.log`, per the note above. That is a far smaller
change than a rewrite of the iteration, and it leaves the existing sorry-free `alwz` chain
intact by construction. **Done**: `SpreadIterate.iterate_le_of_bottom`, with `iterate_le`
re-derived from it, statement unchanged.

### The uniformity obstacle, and its resolution

Wiring `failCount_le_of_janson_budget` into `iterate_le_of_bottom` was **not** just a matter of
choosing `L`, `s`, `m_bot`, `p`. The bottom hypothesis of `iterate_le_of_bottom` supplies

  `WBounded X v σ`   — members of size *at most* `v`,

whereas `failCount_le_of_janson_budget` requires

  `SuppUniform X σ v` — members of size *exactly* `v`,

and the iteration's residual systems are genuinely mixed-size (formalization note A3). The second-moment
route meets the same obstacle, which is exactly why `SpreadBottom` restricts to the **heaviest
size class** before applying `bottom_le`.

`failCount_le_of_janson_bounded` above does the same for the Janson bottom, and
`JansonIterate.iterate_le_janson` runs the iteration on it. Two remarks on the cost.

* **A factor `v` in the mass, and a second one in the exponent.** The heaviest class carries
  a `1/v` fraction of the mass; and since it may sit at *any* width `u ∈ [1, v]`, the budget
  must be taken at the worst case of `κ^{u+1}/u` over that range, which is `u = 1`. So
  `A·κ^{v+1}·p/(8M²v)` becomes `A·κ²·p/(8M²v²)`. The `κ^{v+1}` was never robust: it came from
  routing `|supp|` through `card_supp_ge`, which is a *uniformity* statement.
* **The `log(1/εbot)` dependence is untouched**, which is the entire point of the Janson route
  (formalization note B1). Both losses are polynomial factors inside the exponent's coefficient.

The alternative — generalising the Janson estimates to bounded systems — remains inadvisable:
`mu_eq` and `delta_le_closed` both use `|T| = v` essentially (the exponent bookkeeping rests on
`|T ∪ T'| = 2v − |T ∩ T'|`), and the analysis shows that mixed sizes degrade this badly.

## The chase, and what it found

`iterate_le_janson` has the same statement as `SpreadIterate.iterate_le`, with the bottom
κ-conditions `hK2`, `hK3` replaced by `hJ1`–`hJ4`, so the remaining work looked like
`SpreadAssemble`'s: choose `L`, `s`, `m_bot`, `p`, `κ` making `hK1` and `hJ1`–`hJ4` hold at the
`spread_lemma` instantiation, this time with `Real.log` (the present chase is deliberately
`Nat.log`-only, which is what the `1/β` failure shape bought) and with the new sampling
parameter `p`.

It does not close, and `Sunflower.JansonChase` proves why. At the instantiation the mass floor
and the spread bound are both the family size, `A₀ = M = |𝓖|`, so `hJ3` reads
`log(2/εbot) ≤ κ²p/(64·|𝓖|·L²)`; spreadness forces `|𝓖| ≥ κ^{w'}`, so it fails by a factor
`κ^{w'-2}` (`janson_mass_budget_infeasible`). The culprit is `card_supp_superset_le`, which
bounds a *count* of support members by a *mass*: sharp for a family, off by the multiplicity
for a multiset. This support-indexed formulation sees only the support, so what it needs is
**support**-spreadness,
`IsSpread κ (supp X σ)` — and `card_supp_ge` is the only lower bound on `|supp|` the mass
invariant affords.

`JansonChase.failCount_le_of_janson_isSpread` is the support-spread bottom (exponent `κp/(8v²)`, no
mass/support ratio), `iterate_le_janson_supp` the iteration on it, and
`janson_supp_conditions` the completed chase for its conditions. What remains is the invariant
itself: `reduce` creates multiplicities, and recovering support-spreadness through the rounds
is ALWZ's own bookkeeping — families and their cardinalities, the departure this development
made deliberately in order to avoid ever lower-bounding a deduplicated family.
-/

end Sunflower

/-
# Janson on the multiset — ALWZ's own Lemma 2.10

`JansonBottom` applies Janson to the **support**: one event per *distinct* member. That forces
the `Δ` estimate to bound a *count* of members above `U` by the mass bound `M/κ^{|U|}`, which
is off by the multiplicity for a weighted system — and `JansonChase` shows the resulting
hypothesis (support-spreadness) is false, so that route must pass to a dyadic weight class and
pay `log₂` of the largest multiplicity.

ALWZ do it differently, and better. Their Lemma 2.10 scales the weights to integers and forms

  "the multi-set system where each `S ∈ F` is repeated `N_S` times",

then applies Janson with **one event per copy**. Repeated events are harmless — Janson is
stated for an indexed family, and duplicating an event multiplies `μ` by the multiplicity and
`Δ` by its square, so `μ²/Δ` is unchanged. What it buys is that every quantity in sight is now
a *mass*: the number of copies above `U` is exactly `wLink X σ U`, which is what
`WLinkBounded` bounds. No count-vs-mass gap, no support-spreadness, no weight classes.

This file redoes the chain on that indexing:

* `janson_mult_q` — Janson for the multiset: `μ = ∑_T σ(T)·p^{|T|}`,
  `Δ = ∑_T σ(T)·∑_{T' meets T} σ(T')·p^{|T ∪ T'|}`;
* `mu_mass_eq`, `delta_mass_linear` — the two spread estimates in mass form, the second
  resting on `WLinkBounded` directly;
* `failCount_le_janson_mass_budget` — the bottom bound with exponent **`A·κ·p/(8·M·v)`**,
  which is ALWZ's `κ ≳ w·log(1/β)/α` with no `M/|supp|` ratio and no multiplicity loss;
* `failCount_le_of_janson_uniformMass` — the same in the iteration's shape, after the
  heaviest-size-class reduction (`A → A/v`, so the exponent becomes `A·κ·p/(8·M·v²)`).

The `Fin k` indexing of `Sunflower.janson_ext_q` already allows repeats, so nothing about
Janson itself needs changing: only the enumeration does.
-/
import Sunflower.JansonChase

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## The multiset enumeration -/

/-- **The multiset enumeration.** Each member of the support is listed `σ T` times, so the
linear term becomes the mass-weighted `∑_T σ(T)·p^{|T|}` and the quadratic term the
mass-weighted double sum. Compare `janson_supp_aux`, which lists each member once. -/
lemma janson_mult_aux (X : Finset α) (σ : Finset α → ℕ) {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    ∃ (k : ℕ) (S : Fin k → Finset α), (∀ i, S i ⊆ X)
      ∧ pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
          = pBiased X p (fun R => ∀ i : Fin k, ¬ (S i ⊆ R))
      ∧ (∑ i : Fin k, pBiased X p (fun R => S i ⊆ R))
          = ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card
      ∧ (∑ i : Fin k, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
            pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R))
          ≤ ∑ T ∈ supp X σ, (σ T : ℝ)
              * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
                  (σ T' : ℝ) * p ^ (T ∪ T').card := by
  classical
  set s : Finset (Finset α) := supp X σ with hs
  -- the index type: a member together with a copy number
  set k : ℕ := Fintype.card ((T : {x // x ∈ s}) × Fin (σ (T : Finset α))) with hk
  set e : Fin k ≃ ((T : {x // x ∈ s}) × Fin (σ (T : Finset α))) :=
    (Fintype.equivFin _).symm with he
  set S : Fin k → Finset α := fun i => ((e i).1 : Finset α) with hSdef
  have hSmem : ∀ i, S i ∈ s := fun i => (e i).1.2
  have hSX : ∀ i, S i ⊆ X := fun i => subset_of_mem_supp (hs ▸ hSmem i)
  -- re-indexing: summing over copies weights by `σ`
  have hreindex : ∀ g : Finset α → ℝ, ∑ i : Fin k, g (S i) = ∑ T ∈ s, (σ T : ℝ) * g T := by
    intro g
    have h1 : ∑ i : Fin k, g (S i)
        = ∑ x : ((T : {x // x ∈ s}) × Fin (σ (T : Finset α))), g ((x.1 : Finset α)) :=
      Fintype.sum_equiv e _ _ fun i => rfl
    rw [h1, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    have h2 : ∀ T : {x // x ∈ s},
        ∑ _j : Fin (σ (T : Finset α)), g ((T : Finset α)) = (σ (T : Finset α) : ℝ) * g T := by
      intro T
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun T _ => h2 T]
    exact Finset.sum_coe_sort s fun T => (σ T : ℝ) * g T
  -- the event is unchanged: the copies cover exactly the support
  have hevent : ∀ R : Finset α, (∀ T ∈ s, ¬ (T ⊆ R)) ↔ ∀ i : Fin k, ¬ (S i ⊆ R) := by
    intro R
    constructor
    · exact fun h i => h (S i) (hSmem i)
    · intro h T hT
      have hσT : 0 < σ T := Nat.pos_of_ne_zero (mem_supp.mp (hs ▸ hT)).2
      have hthis := h (e.symm ⟨⟨T, hT⟩, ⟨0, hσT⟩⟩)
      simp only [hSdef, Equiv.apply_symm_apply] at hthis
      exact hthis
  -- the linear term is exact
  have hmu : ∑ i : Fin k, pBiased X p (fun R => S i ⊆ R)
      = ∑ T ∈ s, (σ T : ℝ) * p ^ T.card := by
    rw [← hreindex fun T => p ^ T.card]
    exact Finset.sum_congr rfl fun i _ => pBiased_superset (hSX i) p
  -- the quadratic term is dominated by the mass-weighted double sum
  have hpair : ∀ i j : Fin k,
      pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R) = p ^ (S i ∪ S j).card := by
    intro i j
    have hcg : pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
        = pBiased X p (fun R => S i ∪ S j ⊆ R) :=
      pBiased_congr X p fun R => (Finset.union_subset_iff).symm
    rw [hcg]
    exact pBiased_superset (Finset.union_subset (hSX i) (hSX j)) p
  have hdelta : ∑ i : Fin k, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
        pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
      ≤ ∑ T ∈ s, (σ T : ℝ) * ∑ T' ∈ s.filter (fun T' => ¬ Disjoint T' T),
          (σ T' : ℝ) * p ^ (T ∪ T').card := by
    have hinner : ∀ i : Fin k,
        ∑ j ∈ depBelow S Finset.univ (i : ℕ) i, pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
          ≤ ∑ T' ∈ s.filter (fun T' => ¬ Disjoint T' (S i)),
              (σ T' : ℝ) * p ^ (S i ∪ T').card := by
      intro i
      have hsub : depBelow S Finset.univ (i : ℕ) i
          ⊆ Finset.univ.filter fun j => ¬ Disjoint (S j) (S i) := by
        intro j hj
        simp only [depBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.2
      calc ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
            pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
          = ∑ j ∈ depBelow S Finset.univ (i : ℕ) i, p ^ (S i ∪ S j).card :=
            Finset.sum_congr rfl fun j _ => hpair i j
        _ ≤ ∑ j ∈ Finset.univ.filter fun j => ¬ Disjoint (S j) (S i),
              p ^ (S i ∪ S j).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity
        _ = ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' (S i), (σ T' : ℝ) * p ^ (S i ∪ T').card := by
            rw [Finset.sum_filter, Finset.sum_filter]
            have := hreindex fun T' => if ¬ Disjoint T' (S i) then p ^ (S i ∪ T').card else 0
            rw [this]
            refine Finset.sum_congr rfl fun T' _ => ?_
            by_cases hd : Disjoint T' (S i) <;> simp [hd]
    calc ∑ i : Fin k, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
          pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
        ≤ ∑ i : Fin k, ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' (S i),
            (σ T' : ℝ) * p ^ (S i ∪ T').card := Finset.sum_le_sum fun i _ => hinner i
      _ = ∑ T ∈ s, (σ T : ℝ) * ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' T,
            (σ T' : ℝ) * p ^ (T ∪ T').card :=
          hreindex fun T => ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' T,
            (σ T' : ℝ) * p ^ (T ∪ T').card
  exact ⟨k, S, hSX, pBiased_congr X p hevent, hmu, hdelta⟩

/-- **Janson for the multiset**, `q`-form: for every `q ∈ [0,1]`,

`Pr[no member is contained in R] ≤ exp(−q·μ + q²·Δ)`,  `μ = ∑_T σ(T)p^{|T|}`,
`Δ = ∑_T σ(T)∑_{T' meets T} σ(T')p^{|T∪T'|}`.

Duplicating an event multiplies `μ` by the multiplicity and `Δ` by its square, so nothing is
lost — and every quantity is now a mass, which is what the spread hypothesis controls. -/
theorem janson_mult_q (X : Finset α) (σ : Finset α → ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- (q * ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card)
          + q ^ 2 * ∑ T ∈ supp X σ, (σ T : ℝ)
              * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
                  (σ T' : ℝ) * p ^ (T ∪ T').card) := by
  obtain ⟨k, S, hSX, hev, hmu, hdelta⟩ := janson_mult_aux X σ hp0 hp1
  rw [hev]
  refine le_trans (janson_ext_q hp0 hp1 hSX hq0 hq1) (Real.exp_le_exp.mpr ?_)
  rw [hmu]
  have hq2 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have := mul_le_mul_of_nonneg_left hdelta hq2
  linarith

/-! ## The two spread estimates, in mass form

Both are the `JansonBottom` estimates with counts replaced by masses. `mu_mass_eq` is exact;
`delta_mass_le` is where the difference bites: the fibre above `U` is bounded by
`wLink X σ U`, which is *literally* what `WLinkBounded` constrains — no count-vs-mass step. -/

omit [DecidableEq α] in
/-- **The `μ` of a `v`-uniform system, in mass form**: `μ = wTotal·p^v`. -/
lemma mu_mass_eq {X : Finset α} {σ : Finset α → ℕ} {p : ℝ} {v : ℕ} (hu : SuppUniform X σ v) :
    ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card = (wTotal X σ : ℝ) * p ^ v := by
  have h1 : ∀ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card = (σ T : ℝ) * p ^ v := by
    intro T hT
    rw [hu T hT]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← wTotal_eq_sum_supp]

/-- **The inner `Δ` estimate, in mass form.** Grouping the members meeting `T` by their exact
intersection `U`, the fibre mass is at most `wLink X σ U`. -/
lemma delta_inner_mass_le {X : Finset α} {σ : Finset α → ℕ} {p : ℝ} {v : ℕ}
    (hu : SuppUniform X σ v) (hp0 : 0 ≤ p) {T : Finset α} (hT : T ∈ supp X σ) :
    ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T), (σ T' : ℝ) * p ^ (T ∪ T').card
      ≤ ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
          (wLink X σ U : ℝ) * p ^ (2 * v - U.card) := by
  classical
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
  rw [← Finset.sum_fiberwise_of_maps_to hfib fun T' => (σ T' : ℝ) * p ^ (T ∪ T').card]
  refine Finset.sum_le_sum fun U hU => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hU
  have hexp : ∀ T' ∈ ((supp X σ).filter (fun T' => ¬ Disjoint T' T)).filter
      (fun T' => T ∩ T' = U),
      (σ T' : ℝ) * p ^ (T ∪ T').card = (σ T' : ℝ) * p ^ (2 * v - U.card) := by
    intro T' hT'
    rw [Finset.mem_filter, Finset.mem_filter] at hT'
    have hT'supp : T' ∈ supp X σ := hT'.1.1
    have hcards : (T ∪ T').card + (T ∩ T').card = T.card + T'.card :=
      Finset.card_union_add_card_inter T T'
    have hTv : T.card = v := hu T hT
    have hT'v : T'.card = v := hu T' hT'supp
    have hcard : (T ∪ T').card = 2 * v - U.card := by
      rw [hT'.2] at hcards
      omega
    rw [hcard]
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  -- the fibre mass is at most the link mass at `U`
  have hnat : ∑ T' ∈ ((supp X σ).filter (fun T' => ¬ Disjoint T' T)).filter
      (fun T' => T ∩ T' = U), σ T' ≤ wLink X σ U := by
    rw [wLink]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
    intro T' hT'
    rw [Finset.mem_filter, Finset.mem_filter] at hT'
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_of_mem_supp hT'.1.1, hT'.2 ▸ Finset.inter_subset_right⟩
  exact_mod_cast hnat

/-- The binomial tail in closed form (no set system involved). -/
lemma binom_tail_eq {M κ p : ℝ} {v : ℕ} (hp : 0 < p) :
    ∑ u ∈ Finset.Icc 1 v, (v.choose u : ℝ) * (M * (κ ^ u)⁻¹ * p ^ (2 * v - u))
      = M * p ^ (2 * v) * ((1 + (κ * p)⁻¹) ^ v - 1) := by
  have hterm : ∀ u ∈ Finset.Icc 1 v,
      (v.choose u : ℝ) * (M * (κ ^ u)⁻¹ * p ^ (2 * v - u))
        = M * p ^ (2 * v) * ((v.choose u : ℝ) * ((κ * p)⁻¹) ^ u) := by
    intro u hu'
    rw [Finset.mem_Icc] at hu'
    have hpow : p ^ (2 * v - u) = p ^ (2 * v) * (p ^ u)⁻¹ := by
      rw [← div_eq_mul_inv, eq_div_iff (by positivity), ← pow_add]
      congr 1
      omega
    rw [hpow, mul_inv, mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_Icc_choose]

/-- **The `Δ` bound, in mass form and linearised.** Once `v/(κp) ≤ 1/2`,

`Δ ≤ wTotal · M · p^{2v} · 2v/(κp)`.

With `μ = wTotal·p^v` this gives the Janson exponent `μ²/(4Δ) ≥ wTotal·κ·p/(8·M·v)` — ALWZ's
budget, with no `M/|supp|` ratio: the mass appears on both sides and cancels. -/
theorem delta_mass_linear {X : Finset α} {σ : Finset α → ℕ} {M κ p : ℝ} {v : ℕ}
    (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v) (hκ : 0 < κ) (hp : 0 < p)
    (hM : 0 ≤ M) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2) :
    ∑ T ∈ supp X σ, (σ T : ℝ)
        * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T), (σ T' : ℝ) * p ^ (T ∪ T').card
      ≤ (wTotal X σ : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) := by
  classical
  -- per member `T`, the inner sum is at most the binomial tail
  have hper : ∀ T ∈ supp X σ,
      ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T), (σ T' : ℝ) * p ^ (T ∪ T').card
        ≤ M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹) := by
    intro T hT
    refine le_trans (delta_inner_mass_le hu hp.le hT) ?_
    have h1 : ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
          (wLink X σ U : ℝ) * p ^ (2 * v - U.card)
        ≤ ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
            M * (κ ^ U.card)⁻¹ * p ^ (2 * v - U.card) := by
      refine Finset.sum_le_sum fun U hU => ?_
      rw [Finset.mem_filter, Finset.mem_powerset] at hU
      have hκpow : (0 : ℝ) < κ ^ U.card := by positivity
      have hmass : (wLink X σ U : ℝ) ≤ M * (κ ^ U.card)⁻¹ := by
        rw [le_mul_inv_iff₀ hκpow]
        exact hl U hU.2
      exact mul_le_mul_of_nonneg_right hmass (by positivity)
    refine le_trans h1 ?_
    have heq : ∑ U ∈ T.powerset.filter (fun U => U.Nonempty),
          M * (κ ^ U.card)⁻¹ * p ^ (2 * v - U.card)
        = M * p ^ (2 * v) * ((1 + (κ * p)⁻¹) ^ v - 1) := by
      have h := sum_nonempty_subsets_eq T fun u => M * (κ ^ u)⁻¹ * p ^ (2 * v - u)
      rw [hu T hT] at h
      rw [h, binom_tail_eq hp]
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact one_add_pow_sub_one_le (by positivity) hvt
  calc ∑ T ∈ supp X σ, (σ T : ℝ)
        * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T), (σ T' : ℝ) * p ^ (T ∪ T').card
      ≤ ∑ T ∈ supp X σ, (σ T : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) :=
        Finset.sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (hper T hT) (by positivity)
    _ = (wTotal X σ : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) := by
        rw [← Finset.sum_mul, ← wTotal_eq_sum_supp]

/-! ## The bottom step: ALWZ's Lemma 2.10 -/

/-- Janson at the fixed-size level, mass form, `q`-parameterised. -/
theorem failCount_le_janson_mass_q {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    (hb : WBounded X v σ) {p q D : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hD : ∑ T ∈ supp X σ, (σ T : ℝ)
        * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
            (σ T' : ℝ) * p ^ (T ∪ T').card ≤ D)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- (q * ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) + q ^ 2 * D)
        * (X.card.choose m₀ : ℝ)) := by
  classical
  rw [failCount_eq_fixedCount hb m₀]
  refine le_trans (fixedCount_le_two_mul_pBiased (decreasing_uncovered X σ) hp0 hp1 hm₀
    hm₀n hsmall) ?_
  have hjan := janson_mult_q X σ hp0 hp1 hq0 hq1
  have hmono : Real.exp (- (q * ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card)
      + q ^ 2 * ∑ T ∈ supp X σ, (σ T : ℝ)
          * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
              (σ T' : ℝ) * p ^ (T ∪ T').card)
      ≤ Real.exp (- (q * ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) + q ^ 2 * D) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hD (sq_nonneg q)
    linarith
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  have hstep := mul_le_mul_of_nonneg_right (le_trans hjan hmono) hchoose
  linarith

/-- The optimised form, at `q = μ/(2D)`. -/
theorem failCount_le_janson_mass_opt {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    (hb : WBounded X v σ) {p D : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hDpos : 0 < D)
    (hμD : (∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) ≤ 2 * D)
    (hD : ∑ T ∈ supp X σ, (σ T : ℝ)
        * ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
            (σ T' : ℝ) * p ^ (T ∪ T').card ≤ D)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- ((∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) ^ 2 / (4 * D)))
        * (X.card.choose m₀ : ℝ)) := by
  have hμ0 : (0 : ℝ) ≤ ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card :=
    Finset.sum_nonneg fun T _ => by positivity
  have hq0 : 0 ≤ (∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) / (2 * D) := by positivity
  have hq1 : (∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) / (2 * D) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hμD
  have hexp : - ((∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) / (2 * D)
        * ∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card)
      + ((∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) / (2 * D)) ^ 2 * D
      = - ((∑ T ∈ supp X σ, (σ T : ℝ) * p ^ T.card) ^ 2 / (4 * D)) := by
    field_simp
    ring
  have hgen := failCount_le_janson_mass_q hb hp0 hp1 hq0 hq1 hD hm₀ hm₀n hsmall
  rwa [hexp] at hgen

/-- **ALWZ's Lemma 2.10.** For a `v`-uniform `κ`-spread weighted system of mass `A`,

`failCount X σ m₀ ≤ 2·exp(−A·κ·p/(8·M·v))·C(|X|, m₀)`.

The mass appears in both `μ` and `Δ` and cancels down to the ratio `A/M`, which is `1` in the
iteration's regime. There is no `|supp|` anywhere: this is the whole point of indexing Janson
by copies rather than by distinct members. -/
theorem failCount_le_janson_mass_budget {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {M κ p : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ) (hu : SuppUniform X σ v)
    (hκ : 0 < κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 0 < v)
    (hA : 0 < wTotal X σ) (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hμD : (wTotal X σ : ℝ) * p ^ v
      ≤ 2 * ((wTotal X σ : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹))))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- ((wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ))))
        * (X.card.choose m₀ : ℝ)) := by
  have hAR : (0 : ℝ) < (wTotal X σ : ℝ) := by exact_mod_cast hA
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  set D : ℝ := (wTotal X σ : ℝ) * (M * p ^ (2 * v) * (2 * (v : ℝ) * (κ * p)⁻¹)) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hmu := mu_mass_eq (X := X) (σ := σ) (p := p) hu
  have hopt := failCount_le_janson_mass_opt hb hp.le hp1 hDpos (by rwa [hmu])
    (delta_mass_linear hl hu hκ hp hM.le hvt) hm₀ hm₀n hsmall
  rw [hmu] at hopt
  have hAne : (wTotal X σ : ℝ) ≠ 0 := ne_of_gt hAR
  have hMne : M ≠ 0 := ne_of_gt hM
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  have hpne : p ≠ 0 := ne_of_gt hp
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have harith : ((wTotal X σ : ℝ) * p ^ v) ^ 2 / (4 * D)
      = (wTotal X σ : ℝ) * κ * p / (8 * M * (v : ℝ)) := by
    rw [hDdef, two_mul v, pow_add]
    field_simp
    ring
  rwa [harith] at hopt

/-- **The bottom step for bounded systems**, after the heaviest-size-class reduction: for a
`≤ v`-bounded `κ`-spread system of mass at least `A`,

if `log(2/εbot) ≤ A·κ·p/(8·M·v²)` then `failCount X σ m₀ ≤ εbot·C(|X|, m₀)`.

The class costs one factor `v` in the mass and one in the width, hence `v²` — the same price
`SpreadBottom` pays. Nothing else is lost: no support size, no multiplicity, no extra
hypothesis. -/
theorem failCount_le_of_janson_uniformMass {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    {M κ p A εbot : ℝ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 < M) (hv : 1 ≤ v)
    (hA0 : 0 < A) (hA : A ≤ (wTotal X σ : ℝ))
    (hvt : (v : ℝ) * (κ * p)⁻¹ ≤ 1 / 2)
    (hεb : 0 < εbot)
    (hbudget : Real.log (2 / εbot) ≤ A * κ * p / (8 * M * (v : ℝ) ^ 2))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
  classical
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκp : (0 : ℝ) < κ * p := mul_pos hκ0 hp
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hv1R : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hκp2 : 2 * (v : ℝ) ≤ κ * p := by
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hκp] at hvt
    linarith
  have hκp1 : (1 : ℝ) ≤ κ * p := by linarith
  by_cases hE : σ ∅ ≠ 0
  · rw [failCount_eq_zero_of_empty_mem X σ m₀ hE, Nat.cast_zero]
    exact mul_nonneg hεb.le (Nat.cast_nonneg _)
  rw [not_not] at hE
  -- the heaviest size class
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
  have hNu : 0 < (supp X τ).card := card_supp_pos hwpos
  have hbu : WBounded X u τ := wBounded_sizeClass hb u
  have hlu : WLinkBounded X τ M κ := wLinkBounded_sizeClass hκ0.le hl u
  have huu : SuppUniform X τ u := suppUniform_sizeClass X σ u
  -- `κ^u ≤ M`, from spreadness at a member of the class
  have hκuM : κ ^ u ≤ M := by
    obtain ⟨T₀, hT₀⟩ := Finset.card_pos.mp hNu
    have hne : T₀.Nonempty := by
      rw [← Finset.card_pos, huu T₀ hT₀]
      omega
    have hone : (1 : ℝ) ≤ (wLink X τ T₀ : ℝ) := by
      have : 1 ≤ wLink X τ T₀ := by
        rw [wLink]
        refine le_trans (Nat.one_le_iff_ne_zero.mpr (mem_supp.mp hT₀).2)
          (Finset.single_le_sum (f := τ) (fun _ _ => Nat.zero_le _) ?_)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr (subset_of_mem_supp hT₀), Finset.Subset.rfl⟩
      exact_mod_cast this
    have h := hlu T₀ hne
    rw [huu T₀ hT₀] at h
    nlinarith [pow_pos hκ0 u]
  -- the `q ≤ 1` check
  have hμD : (wTotal X τ : ℝ) * p ^ u
      ≤ 2 * ((wTotal X τ : ℝ) * (M * p ^ (2 * u) * (2 * (u : ℝ) * (κ * p)⁻¹))) := by
    have hkey : κ * p ≤ 4 * (u : ℝ) * M * p ^ u := by
      have h1 : (κ * p) ^ 1 ≤ (κ * p) ^ u := pow_le_pow_right₀ hκp1 hu1
      rw [pow_one] at h1
      have h2 : (κ * p) ^ u = κ ^ u * p ^ u := mul_pow κ p u
      have h3 : κ ^ u * p ^ u ≤ M * p ^ u := mul_le_mul_of_nonneg_right hκuM (by positivity)
      have h4 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      nlinarith [h1, h3, mul_nonneg hM.le (pow_nonneg hp.le u)]
    have hrw : 2 * ((wTotal X τ : ℝ) * (M * p ^ (2 * u) * (2 * (u : ℝ) * (κ * p)⁻¹)))
        = ((wTotal X τ : ℝ) * p ^ u) * ((4 * (u : ℝ) * M * p ^ u) / (κ * p)) := by
      rw [two_mul u, pow_add]
      field_simp
      ring
    rw [hrw]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [le_div_iff₀ hκp, one_mul]
    exact hkey
  have hjan := failCount_le_janson_mass_budget (X := X) (v := u) (σ := τ) (M := M) (κ := κ)
    (p := p) hbu hlu huu hκ0 hp hp1 hM hu1 hwpos
    (le_trans (mul_le_mul_of_nonneg_right huvR (by positivity)) hvt) hμD hm₀ hm₀n hsmall
  -- the exponent is at least `A·κ·p/(8·M·v²)`
  have hexp : A * κ * p / (8 * M * (v : ℝ) ^ 2)
      ≤ (wTotal X τ : ℝ) * κ * p / (8 * M * (u : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hAuv : A ≤ (v : ℝ) * (wTotal X τ : ℝ) := by
      rw [div_le_iff₀ hvR] at hAu
      linarith
    have hkey : A * (u : ℝ) ≤ (wTotal X τ : ℝ) * (v : ℝ) ^ 2 := by
      nlinarith [hAuv, huvR, hvR, huR, Nat.cast_nonneg (α := ℝ) (wTotal X τ)]
    calc A * κ * p * (8 * M * (u : ℝ)) = (8 * M * (κ * p)) * (A * (u : ℝ)) := by ring
      _ ≤ (8 * M * (κ * p)) * ((wTotal X τ : ℝ) * (v : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (wTotal X τ : ℝ) * κ * p * (8 * M * (v : ℝ) ^ 2) := by ring
  have hexpb : Real.exp (- ((wTotal X τ : ℝ) * κ * p / (8 * M * (u : ℝ)))) ≤ εbot / 2 := by
    have hpos : (0 : ℝ) < 2 / εbot := by positivity
    refine le_trans (Real.exp_le_exp.mpr (neg_le_neg (le_trans hbudget hexp))) ?_
    rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  have hfinal : (failCount X τ m₀ : ℝ) ≤ εbot * (X.card.choose m₀ : ℝ) := by
    calc (failCount X τ m₀ : ℝ)
        ≤ 2 * (Real.exp (- ((wTotal X τ : ℝ) * κ * p / (8 * M * (u : ℝ))))
            * (X.card.choose m₀ : ℝ)) := hjan
      _ ≤ 2 * ((εbot / 2) * (X.card.choose m₀ : ℝ)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hexpb hchoose) (by norm_num)
      _ = εbot * (X.card.choose m₀ : ℝ) := by ring
  refine le_trans ?_ hfinal
  exact_mod_cast failCount_le_sizeClass X σ u m₀

/-! ## The iteration, unconditionally

Three conditions, all in the iteration's own parameters — no support hypothesis, no
multiplicity bound, nothing about `|𝓖|`:

* `hS1 : 4L ≤ κ·p`                          — the linearisation condition;
* `hS2 : log(2/εbot) ≤ A₀·κ·p/(64·M·L²)`    — the budget, in `log(1/εbot)` form;
* `hS3 : 2p·n₀ ≤ m_bot`                     — the `p`-biased/fixed-size bridge. -/

/-- The bottom regime on ALWZ's Lemma 2.10, in the shape `iterate_le_of_bottom` consumes. -/
theorem janson_bottom_alwz {L m_bot n₀ : ℕ} {A₀ M κ p εbot : ℝ} {X : Finset α}
    {σ : Finset α → ℕ} {v m : ℕ} {A : ℝ}
    (hL : 2 ≤ L) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) (hεb : 0 < εbot)
    (hS1 : 4 * (L : ℝ) ≤ κ * p)
    (hS2 : Real.log (2 / εbot) ≤ A₀ * κ * p / (64 * M * (L : ℝ) ^ 2))
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
  -- the budget at width `v ≤ 2L`, with mass floor `A₀/2`
  have hbudget : Real.log (2 / εbot) ≤ (A₀ / 2) * κ * p / (8 * M * (v : ℝ) ^ 2) := by
    refine le_trans hS2 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hv2 : (v : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith [hvR, hvL', hLR]
    calc A₀ * κ * p * (8 * M * (v : ℝ) ^ 2)
        = (8 * M * (κ * p)) * (A₀ * (v : ℝ) ^ 2) := by ring
      _ ≤ (8 * M * (κ * p)) * (A₀ * (4 * (L : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv2 hA₀.le)
            (by positivity)
      _ = A₀ / 2 * κ * p * (64 * M * (L : ℝ) ^ 2) := by ring
  have hsmall : 2 * (p * (X.card : ℝ)) ≤ (m : ℝ) := by
    have h1 : (X.card : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h2 : (m_bot : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmm
    have h3 : p * (X.card : ℝ) ≤ p * (n₀ : ℝ) := mul_le_mul_of_nonneg_left h1 hp.le
    linarith
  exact failCount_le_of_janson_uniformMass (A := A₀ / 2) hb hl hκ hp hp1 hM hv (by linarith)
    (le_trans hA2 htot) hvt hεb hbudget (by omega) hmn hsmall

/-- **The width-schedule iteration on ALWZ's bottom step.** `iterate_le`'s conclusion verbatim,
with `hK2`, `hK3` replaced by `hS1`–`hS3` — and nothing else. No support-spreadness, no weight
classes, no bound on multiplicities: indexing Janson by copies makes the mass invariant the
iteration already carries exactly the right hypothesis. -/
theorem iterate_le_janson_alwz {L s m_bot n₀ : ℕ} {A₀ M κ p ε εbot : ℝ}
    (hL : 2 ≤ L) (hs : 1 ≤ s) (hmb : 2 * L < m_bot)
    (hA₀ : 0 < A₀) (hM : 0 < M) (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hεb : 0 < εbot)
    (hK1 : ∀ v : ℕ, 2 * L < v →
      (8 * n₀ / s : ℝ) ^ v * M * 2 ^ (v + 1) * 2 ^ v ≤ ε * A₀ * κ ^ (v - v / L))
    (hS1 : 4 * (L : ℝ) ≤ κ * p)
    (hS2 : Real.log (2 / εbot) ≤ A₀ * κ * p / (64 * M * (L : ℝ) ^ 2))
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
      janson_bottom_alwz hL hmb hA₀ hM hκ hp hp1 hεb hS1 hS2 hS3
        hb hl htot hAinv hv hvL hmm hmn hn₀)

/-! ## The chase

`p = 1/(8r)`, `εbot = 1/(4r)`, and `A₀ = M` at the instantiation, so `hS2` reads
`log(8r) ≤ κ/(512·r·L²)`, i.e. `512·r·L²·log(8r) ≤ κ` — `r·log r`, against the second
moment's `576·r²·L²`. Through `log x ≤ x − 1` it suffices that `4096·r²·L² ≤ κ`, which
`κ = 2^41·r³·lg w·lg lg w` clears by four orders of magnitude. -/

/-- **The chase for `iterate_le_janson_alwz`**, at the `spread_core_main` parameters. Compare
`janson_supp_conditions`: same shape, and now *nothing* is conditional. -/
theorem janson_alwz_conditions {r w L n m m_bot : ℕ} (hr : 3 ≤ r) (hw : 2 ≤ w)
    (hL4 : 4 ≤ L) (hLub : (L : ℝ) ≤ 88 + 4 * lg r + 3 * lg (lg w))
    (hκn : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w) ≤ (n : ℝ))
    (hm : m = n / r) (hmbot : m_bot = m - m / 2) :
    (1 : ℝ) ≤ (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)
    ∧ 4 * (L : ℝ) ≤ ((2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)) * (1 / (8 * (r : ℝ)))
    ∧ Real.log (2 / (1 / (4 * (r : ℝ))))
        ≤ ((2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w)) * (1 / (8 * (r : ℝ)))
            / (64 * (L : ℝ) ^ 2)
    ∧ 2 * ((1 / (8 * (r : ℝ))) * (n : ℝ)) ≤ (m_bot : ℝ) := by
  set κ : ℝ := (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * lg (lg w) with hκdef
  have hw2 : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hlgw : (1 : ℝ) < lg w := one_lt_lg hw2
  have hlgw0 : (0 : ℝ) < lg w := lt_trans one_pos hlgw
  have hlglg20 : (1 / 20 : ℝ) ≤ lg (lg w) := le_trans lg_lg_two_ge (lg_lg_le_lg_lg hw2)
  have hlglgpos : (0 : ℝ) < lg (lg w) := lt_of_lt_of_le (by norm_num) hlglg20
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr9 : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hr27 : (27 : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith
  have hr3r : 9 * (r : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith
  have hr32 : 3 * (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := by nlinarith [sq_nonneg (r : ℝ)]
  have hlgr2 : lg r ≤ 2 * (r : ℝ) := lg_le_double hrpos
  have hlgrsq : (lg r) ^ 2 ≤ 16 * (r : ℝ) := lg_sq_le (by exact_mod_cast (by omega : 1 ≤ r))
  have hlglgsq : (lg (lg w)) ^ 2 ≤ 16 * (lg w) := lg_sq_le hlgw.le
  have hκpos : (0 : ℝ) < κ := by
    rw [hκdef]
    exact mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) hlgw0) hlglgpos
  have hκlb1 : (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 ≤ κ := by
    rw [hκdef]
    have h1 : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * 1 * (1 / 20)
        ≤ 2 ^ 41 * (r : ℝ) ^ 3 * lg w * lg (lg w) := by
      refine mul_le_mul (mul_le_mul le_rfl hlgw.le (by norm_num) (by positivity))
        hlglg20 (by norm_num) ?_
      exact mul_nonneg (by positivity) hlgw0.le
    calc (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 = 2 ^ 41 * (r : ℝ) ^ 3 * 1 * (1 / 20) := by ring
      _ ≤ _ := h1
  have hκlb2 : (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 * lg w ≤ κ := by
    rw [hκdef]
    have h1 : (2 ^ 41 : ℝ) * (r : ℝ) ^ 3 * lg w * (1 / 20)
        ≤ 2 ^ 41 * (r : ℝ) ^ 3 * lg w * lg (lg w) :=
      mul_le_mul_of_nonneg_left hlglg20 (mul_nonneg (by positivity) hlgw0.le)
    calc (2 ^ 41 / 20 : ℝ) * (r : ℝ) ^ 3 * lg w
        = 2 ^ 41 * (r : ℝ) ^ 3 * lg w * (1 / 20) := by ring
      _ ≤ _ := h1
  have hκlb3 : (2 ^ 41 * 9 : ℝ) * (r : ℝ) * lg w * lg (lg w) ≤ κ := by
    rw [hκdef]
    have h1 : (2 ^ 41 : ℝ) * (9 * (r : ℝ)) ≤ 2 ^ 41 * (r : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hr3r (by positivity)
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hlgw0.le) hlglgpos.le
    calc (2 ^ 41 * 9 : ℝ) * (r : ℝ) * lg w * lg (lg w)
        = (2 ^ 41 : ℝ) * (9 * (r : ℝ)) * lg w * lg (lg w) := by ring
      _ ≤ _ := h3
  have hL4R : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hLsq : (L : ℝ) ^ 2 ≤ 23232 + 768 * (r : ℝ) + 432 * (lg w) := by
    have h1 : (L : ℝ) ^ 2 ≤ (88 + 4 * lg r + 3 * lg (lg w)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hLub 2
    have h2 : (88 + 4 * lg r + 3 * lg (lg w)) ^ 2
        ≤ 3 * (88 ^ 2 + (4 * lg r) ^ 2 + (3 * lg (lg w)) ^ 2) := by
      nlinarith [sq_nonneg (88 - 4 * lg r), sq_nonneg (88 - 3 * lg (lg w)),
        sq_nonneg (4 * lg r - 3 * lg (lg w))]
    calc (L : ℝ) ^ 2 ≤ 3 * (88 ^ 2 + (4 * lg r) ^ 2 + (3 * lg (lg w)) ^ 2) := le_trans h1 h2
      _ = 23232 + 48 * (lg r) ^ 2 + 27 * (lg (lg w)) ^ 2 := by ring
      _ ≤ 23232 + 48 * (16 * (r : ℝ)) + 27 * (16 * (lg w)) := by
          have := mul_le_mul_of_nonneg_left hlgrsq (by norm_num : (0 : ℝ) ≤ 48)
          have := mul_le_mul_of_nonneg_left hlglgsq (by norm_num : (0 : ℝ) ≤ 27)
          linarith
      _ = 23232 + 768 * (r : ℝ) + 432 * (lg w) := by ring
  refine ⟨by nlinarith [hκlb1, hr27], ?_, ?_, ?_⟩
  -- (1) `4L ≤ κ/(8r)`, i.e. `32·r·L ≤ κ`
  · rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ))]
    have hrlgr : (r : ℝ) * lg r ≤ 2 * (r : ℝ) ^ 2 := by nlinarith [hlgr2, hrpos]
    have hprod : (r : ℝ) * lg (lg w) ≤ (r : ℝ) * lg w * lg (lg w) := by
      nlinarith [mul_nonneg (mul_nonneg hrpos.le hlglgpos.le) (sub_nonneg.mpr hlgw.le)]
    have hp1 : 2816 * (r : ℝ) ≤ κ / 3 := by linarith
    have hp2 : 128 * (r : ℝ) * lg r ≤ κ / 3 := by linarith
    have hp3 : 96 * (r : ℝ) * lg (lg w) ≤ κ / 3 := by linarith
    calc 4 * (L : ℝ) * (8 * (r : ℝ)) = 32 * (r : ℝ) * (L : ℝ) := by ring
      _ ≤ 32 * (r : ℝ) * (88 + 4 * lg r + 3 * lg (lg w)) :=
          mul_le_mul_of_nonneg_left hLub (by positivity)
      _ = 2816 * (r : ℝ) + 128 * (r : ℝ) * lg r + 96 * (r : ℝ) * lg (lg w) := by ring
      _ ≤ κ / 3 + κ / 3 + κ / 3 := by linarith
      _ = κ := by ring
  -- (2) the budget: `log(8r) ≤ κ/(512·r·L²)`, via `4096·r²·L² ≤ κ`
  · have h8r : (2 : ℝ) / (1 / (4 * (r : ℝ))) = 8 * (r : ℝ) := by
      field_simp
      norm_num
    rw [h8r, mul_one_div, div_div, le_div_iff₀ (by positivity)]
    have hlog : Real.log (8 * (r : ℝ)) ≤ 8 * (r : ℝ) :=
      le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
    have hq1 : 4096 * 23232 * (r : ℝ) ^ 2 ≤ κ / 3 := by linarith
    have hq2 : 4096 * 768 * (r : ℝ) ^ 3 ≤ κ / 3 := by linarith
    have hq3 : 4096 * 432 * (r : ℝ) ^ 2 * lg w ≤ κ / 3 := by
      have h1 : 3 * (r : ℝ) ^ 2 * lg w ≤ (r : ℝ) ^ 3 * lg w :=
        mul_le_mul_of_nonneg_right hr32 hlgw0.le
      linarith
    have hfin : 8 * (r : ℝ) * (8 * (r : ℝ) * (64 * (L : ℝ) ^ 2)) ≤ κ := by
      have h1 : 4096 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2
          ≤ 4096 * (r : ℝ) ^ 2 * (23232 + 768 * (r : ℝ) + 432 * (lg w)) :=
        mul_le_mul_of_nonneg_left hLsq (by positivity)
      calc 8 * (r : ℝ) * (8 * (r : ℝ) * (64 * (L : ℝ) ^ 2))
          = 4096 * (r : ℝ) ^ 2 * (L : ℝ) ^ 2 := by ring
        _ ≤ 4096 * (r : ℝ) ^ 2 * (23232 + 768 * (r : ℝ) + 432 * (lg w)) := h1
        _ = 4096 * 23232 * (r : ℝ) ^ 2 + 4096 * 768 * (r : ℝ) ^ 3
              + 4096 * 432 * (r : ℝ) ^ 2 * lg w := by ring
        _ ≤ κ / 3 + κ / 3 + κ / 3 := by linarith
        _ = κ := by ring
    calc Real.log (8 * (r : ℝ)) * (8 * (r : ℝ) * (64 * (L : ℝ) ^ 2))
        ≤ 8 * (r : ℝ) * (8 * (r : ℝ) * (64 * (L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
      _ ≤ κ := hfin
  -- (3) the bridge condition
  · have hn4r : 4 * (r : ℝ) ≤ (n : ℝ) := by linarith
    have hnrN : r ≤ n := by
      have : (r : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hm1 : 1 ≤ m := by
      rw [hm, Nat.one_le_div_iff (by omega : 0 < r)]
      exact hnrN
    have hmbot1 : 1 ≤ m_bot := by rw [hmbot]; omega
    have hmdiv : r * m + n % r = n := by rw [hm]; exact Nat.div_add_mod n r
    have hmod : n % r < r := Nat.mod_lt _ (by omega)
    have hnlt : n < r * m + r := by omega
    have hnR : (n : ℝ) < (r : ℝ) * (m : ℝ) + (r : ℝ) := by exact_mod_cast hnlt
    have h2mbot : m ≤ 2 * m_bot := by rw [hmbot]; omega
    have h2mbotR : (m : ℝ) ≤ 2 * (m_bot : ℝ) := by exact_mod_cast h2mbot
    have hmb1R : (1 : ℝ) ≤ (m_bot : ℝ) := by exact_mod_cast hmbot1
    have hrm : (r : ℝ) * (m : ℝ) ≤ (r : ℝ) * (2 * (m_bot : ℝ)) :=
      mul_le_mul_of_nonneg_left h2mbotR hrpos.le
    have hrmb : (r : ℝ) ≤ (r : ℝ) * (m_bot : ℝ) := le_mul_of_one_le_right hrpos.le hmb1R
    rw [show 2 * ((1 / (8 * (r : ℝ))) * (n : ℝ)) = (n : ℝ) / (4 * (r : ℝ)) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (r : ℝ))]
    nlinarith [hnR, hrm, hrmb, mul_nonneg hrpos.le (Nat.cast_nonneg (α := ℝ) m_bot)]

end Sunflower

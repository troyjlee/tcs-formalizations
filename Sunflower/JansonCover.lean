/-
# Janson applied to the covering event of a weighted system

`Sunflower.Janson` proves Janson's inequality for an abstract family `S : Fin n → Finset α`.
The systems in `SpreadCore` are weighted, `σ : Finset α → ℕ`, and the event of interest is

  `WCovered σ R = ∃ S, σ S ≠ 0 ∧ S ⊆ R`,

whose negation is the decreasing event Janson bounds. This file connects the two: enumerate
the support of `σ` and specialise.

The payoff is that **both Janson parameters become explicit powers of `p`**, because
`pBiased_superset` computes `Pr[T ⊆ R] = p^{|T|}` exactly:

  `μ = ∑_{T ∈ supp} p^{|T|}`,   `Δ ≤ ∑_{T ∈ supp} ∑_{T' ∈ supp, T' ∩ T ≠ ∅} p^{|T ∪ T'|}`.

That is precisely the shape ALWZ's Lemma 2.10 computes with. (`Δ` is an over-estimate: the
Janson sum runs over *unordered* dependent pairs, and we bound it by the full ordered sum,
which only adds nonnegative terms — including the diagonal.)

Combined with `Sunflower.Bridge`, this yields a fixed-size bound on `failCount`
(`failCount_le_two_mul_exp`), which is what would replace the second-moment estimate in
`SpreadBottom.bottom_le`.
-/
import Sunflower.Janson
import Sunflower.Bridge
import Sunflower.SpreadCore

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## The support of a weighted system -/

/-- The support of `σ` inside `X`: the sets of positive weight that sit inside `X`. -/
def supp (X : Finset α) (σ : Finset α → ℕ) : Finset (Finset α) :=
  X.powerset.filter fun S => σ S ≠ 0

omit [DecidableEq α] in
lemma mem_supp {X : Finset α} {σ : Finset α → ℕ} {T : Finset α} :
    T ∈ supp X σ ↔ T ⊆ X ∧ σ T ≠ 0 := by
  rw [supp, Finset.mem_filter, Finset.mem_powerset]

omit [DecidableEq α] in
lemma subset_of_mem_supp {X : Finset α} {σ : Finset α → ℕ} {T : Finset α}
    (h : T ∈ supp X σ) : T ⊆ X := (mem_supp.mp h).1

omit [DecidableEq α] in
/-- Under `WBounded`, covering by the system is covering by its support. -/
lemma wCovered_iff_supp {X : Finset α} {v : ℕ} {σ : Finset α → ℕ} (hb : WBounded X v σ)
    (R : Finset α) : WCovered σ R ↔ ∃ T ∈ supp X σ, T ⊆ R := by
  constructor
  · rintro ⟨T, hT0, hTR⟩
    exact ⟨T, mem_supp.mpr ⟨(hb T hT0).1, hT0⟩, hTR⟩
  · rintro ⟨T, hT, hTR⟩
    exact ⟨T, (mem_supp.mp hT).2, hTR⟩

/-! ## Janson for the support -/

/-- The enumeration of the support, packaged with the three facts every Janson form needs:
the event translates, the linear term is *exact*, and the quadratic term is dominated by the
support sum. Both `janson_supp` and `janson_supp_q` are read off from this. -/
lemma janson_supp_aux (X : Finset α) (σ : Finset α → ℕ) {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    ∃ (k : ℕ) (S : Fin k → Finset α), (∀ i, S i ⊆ X)
      ∧ pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
          = pBiased X p (fun R => ∀ i : Fin k, ¬ (S i ⊆ R))
      ∧ (∑ i : Fin k, pBiased X p (fun R => S i ⊆ R)) = ∑ T ∈ supp X σ, p ^ T.card
      ∧ (∑ i : Fin k, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
            pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R))
          ≤ ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
              p ^ (T ∪ T').card := by
  classical
  set s : Finset (Finset α) := supp X σ with hs
  set k : ℕ := Fintype.card {x // x ∈ s} with hk
  set e : Fin k ≃ {x // x ∈ s} := (Fintype.equivFin _).symm with he
  set S : Fin k → Finset α := fun i => ((e i : {x // x ∈ s}) : Finset α) with hSdef
  have hSmem : ∀ i, S i ∈ s := fun i => (e i).2
  have hSX : ∀ i, S i ⊆ X := fun i => subset_of_mem_supp (hs ▸ hSmem i)
  -- re-indexing along the enumeration
  have hreindex : ∀ g : Finset α → ℝ, ∑ i : Fin k, g (S i) = ∑ T ∈ s, g T := by
    intro g
    rw [← Finset.sum_coe_sort s g]
    exact Fintype.sum_equiv e _ _ fun i => rfl
  -- the event
  have hevent : ∀ R : Finset α, (∀ T ∈ s, ¬ (T ⊆ R)) ↔ ∀ i : Fin k, ¬ (S i ⊆ R) := by
    intro R
    constructor
    · exact fun h i => h (S i) (hSmem i)
    · intro h T hT
      have hthis := h (e.symm ⟨T, hT⟩)
      simp only [hSdef, Equiv.apply_symm_apply] at hthis
      exact hthis
  -- the linear term is exact
  have hmu : ∑ i : Fin k, pBiased X p (fun R => S i ⊆ R) = ∑ T ∈ s, p ^ T.card := by
    rw [← hreindex fun T => p ^ T.card]
    exact Finset.sum_congr rfl fun i _ => pBiased_superset (hSX i) p
  -- the quadratic term is an over-estimate
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
      ≤ ∑ T ∈ s, ∑ T' ∈ s.filter (fun T' => ¬ Disjoint T' T), p ^ (T ∪ T').card := by
    have hinner : ∀ i : Fin k,
        ∑ j ∈ depBelow S Finset.univ (i : ℕ) i, pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
          ≤ ∑ T' ∈ s.filter (fun T' => ¬ Disjoint T' (S i)), p ^ (S i ∪ T').card := by
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
        _ = ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' (S i), p ^ (S i ∪ T').card := by
            rw [Finset.sum_filter, Finset.sum_filter]
            exact hreindex fun T' => if ¬ Disjoint T' (S i) then p ^ (S i ∪ T').card else 0
    calc ∑ i : Fin k, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
          pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)
        ≤ ∑ i : Fin k, ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' (S i),
            p ^ (S i ∪ T').card := Finset.sum_le_sum fun i _ => hinner i
      _ = ∑ T ∈ s, ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' T, p ^ (T ∪ T').card :=
          hreindex fun T => ∑ T' ∈ s.filter fun T' => ¬ Disjoint T' T, p ^ (T ∪ T').card
  exact ⟨k, S, hSX, pBiased_congr X p hevent, hmu, hdelta⟩

/-- **Janson's inequality for a weighted system.** The probability that a `p`-biased random
set contains no member of the support is at most `exp(−μ + Δ)`, with

`μ = ∑_{T ∈ supp} p^{|T|}` and `Δ = ∑_{T ∈ supp} ∑_{T' ∈ supp, T' ∩ T ≠ ∅} p^{|T ∪ T'|}`.

Both parameters are explicit, by `pBiased_superset`. -/
theorem janson_supp (X : Finset α) (σ : Finset α → ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- (∑ T ∈ supp X σ, p ^ T.card)
          + ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
              p ^ (T ∪ T').card) := by
  obtain ⟨k, S, hSX, hev, hmu, hdelta⟩ := janson_supp_aux X σ hp0 hp1
  rw [hev]
  refine le_trans (janson hp0 hp1 hSX) (Real.exp_le_exp.mpr ?_)
  rw [hmu]
  linarith [hdelta]

/-- **The `q`-form of Janson for a weighted system**: for every `q ∈ [0,1]`,

`Pr[no member of the support is contained in R] ≤ exp(−q·μ + q²·Δ)`.

This is the form the final step needs. Unlike `janson_ext`, it carries **no side conditions**
on `μ` and `Δ` — so an *upper bound* on `Δ` may be substituted directly (which is all
`JansonBottom.delta_le` provides), and `q` optimised afterwards. `janson_ext`'s hypotheses
`0 < Δ`, `μ ≤ 2Δ` constrain the exact Janson quadratic term, which is tied to the enumeration
and is not expressible in support terms. -/
theorem janson_supp_q (X : Finset α) (σ : Finset α → ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pBiased X p (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R))
      ≤ Real.exp (- (q * ∑ T ∈ supp X σ, p ^ T.card)
          + q ^ 2 * ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
              p ^ (T ∪ T').card) := by
  obtain ⟨k, S, hSX, hev, hmu, hdelta⟩ := janson_supp_aux X σ hp0 hp1
  rw [hev]
  refine le_trans (janson_ext_q hp0 hp1 hSX hq0 hq1) (Real.exp_le_exp.mpr ?_)
  rw [hmu]
  have hq2 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have := mul_le_mul_of_nonneg_left hdelta hq2
  linarith

/-! ## The fixed-size consequence -/

/-- The support form of the uncovered count agrees with `SpreadCore.failCount`. -/
lemma failCount_eq_fixedCount {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    (hb : WBounded X v σ) (m : ℕ) :
    failCount X σ m
      = fixedCount X (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) m := by
  classical
  rw [failCount, fixedCount]
  congr 1
  refine Finset.filter_congr fun R _ => ?_
  rw [wCovered_iff_supp hb R]
  constructor
  · exact fun h T hT hTR => h ⟨T, hT, hTR⟩
  · rintro h ⟨T, hT, hTR⟩
    exact h T hT hTR

omit [DecidableEq α] in
/-- The event "no member of the support is contained in `R`" is decreasing. -/
lemma decreasing_uncovered (X : Finset α) (σ : Finset α → ℕ) :
    Decreasing (fun R => ∀ T ∈ supp X σ, ¬ (T ⊆ R)) :=
  fun _ _ hab h T hT hTR => h T hT (hTR.trans hab)

/-- **The combined statement**: a fixed-size bound on the failure count, with the paper's
exponential (Janson) shape rather than a second moment.

`failCount X σ m₀ ≤ 2 · exp(−μ + Δ) · C(|X|, m₀)` whenever `2·p·|X| ≤ m₀`. -/
theorem failCount_le_two_mul_exp {X : Finset α} {v : ℕ} {σ : Finset α → ℕ}
    (hb : WBounded X v σ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (failCount X σ m₀ : ℝ)
      ≤ 2 * (Real.exp (- (∑ T ∈ supp X σ, p ^ T.card)
          + ∑ T ∈ supp X σ, ∑ T' ∈ (supp X σ).filter (fun T' => ¬ Disjoint T' T),
              p ^ (T ∪ T').card) * (X.card.choose m₀ : ℝ)) := by
  classical
  rw [failCount_eq_fixedCount hb m₀]
  refine le_trans (fixedCount_le_two_mul_pBiased (decreasing_uncovered X σ) hp0 hp1 hm₀
    hm₀n hsmall) ?_
  have hjan := janson_supp X σ hp0 hp1
  have hchoose : (0 : ℝ) ≤ (X.card.choose m₀ : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_right hjan hchoose
  linarith

end Sunflower

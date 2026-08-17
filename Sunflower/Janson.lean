/-
# Towards Janson's inequality: correlation for the `p`-biased measure

ALWZ's Lemma 2.10 invokes **Janson's inequality** — `Pr[⋀ᵢ ¬Aᵢ] ≤ exp(−μ²/2Δ̄)` for the
increasing events `Aᵢ = [Sᵢ ⊆ R]` — and it is what produces the `log(1/β)` in their
Theorem 1.9. The retained second-moment chain uses `SpreadBottom.bottom_le`, whose corresponding
dependence is `1/β`. To recover the source-shaped `log(1/β)` bottom estimate, this development
formalizes Janson, which Mathlib did not provide at the pinned revision (formalization note B1).

This file starts that development. The route is the standard one (Alon–Spencer):

1. **Harris/FKG** for the `p`-biased measure — increasing events are positively correlated,
   and an increasing and a decreasing event are negatively correlated. *This file*
   (`pBiased_mul_le_pBiased_and`, `pBiased_and_le_mul`).
2. **Independence on disjoint coordinates** — if `P` depends only on `R ∩ Y` and `Q` only on
   `R \ Y` then `Pr[P ∧ Q] = Pr[P]·Pr[Q]`. *This file* (`pBiased_and_of_indep`).
3. **Basic Janson** `Pr[⋀ ¬Aᵢ] ≤ exp(−μ + Δ)`, by telescoping the events in index order and
   bounding each factor with 1 and 2. *This file* (`janson_step`, `janson_prod`, `janson`),
   indexed by `Fin n` and **division-free**: instead of conditional probabilities the
   induction runs on `Pr[C ∧ ¬Aₖ] ≤ Pr[C]·(1 − Pr[Aₖ] + ∑_dep Pr[Aₖ ∧ Aⱼ])`, which
   degenerates correctly when `Pr[C] = 0`.
4. **Extended Janson** `exp(−μ²/2Δ̄)`, the form Lemma 2.10 uses. *This file*
   (`janson_ext_q`, `janson_ext`), via averaging basic Janson over a random sub-collection —
   which is itself a `p`-biased set, on the index type `Fin n`, so the averaging reuses the
   same `wt` machinery (`pBiased_mem`, `pBiased_mem_pair`).

All four steps are proved; the file is sorry-free.

**What makes step 1 available at all**: mathlib has the Ahlswede–Daykin four functions
theorem (`Finset.four_functions_theorem`). We do not use mathlib's `fkg` corollary, because
that one sums over `univ` of a `Fintype` lattice, whereas our ground set is a `Finset α` for
an arbitrary `α`. Instead we apply the four functions theorem directly with
`𝒜 = ℬ = X.powerset`, which is closed under `∩` and `∪` (`infs_powerset_self`,
`sups_powerset_self`), so the right-hand sums are again over `X.powerset`.

The `p`-biased weight is **log-modular** — `wt a · wt b = wt (a ∩ b) · wt (a ∪ b)`, because
`|a| + |b| = |a ∩ b| + |a ∪ b|` — which is the hypothesis the four functions theorem wants.
-/
import Sunflower.Robust
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Finset.Sups
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset
open scoped FinsetFamily

set_option maxHeartbeats 1000000

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## The `p`-biased weight as a log-modular density

`wt` and its basic facts (`wt_of_subset`, `wt_nonneg`, `sum_wt`) live in `Sunflower.Robust`,
as generic `pBiased` vocabulary shared with the fixed-size bridge; extending by zero off
`X.powerset` is what makes log-supermodularity hold on all of `Finset α` (the truncated
subtraction `|X| - |R|` misbehaves for `R ⊄ X`), which is what the four functions theorem
needs — and that log-supermodularity is proved here. -/

/-- **Log-modularity** of the `p`-biased weight on the powerset, and log-supermodularity in
general: `wt a · wt b ≤ wt (a ⊓ b) · wt (a ⊔ b)`, with equality when `a, b ⊆ X`. This is the
hypothesis of the four functions theorem. -/
lemma wt_mul_le {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : Finset α) :
    wt X p a * wt X p b ≤ wt X p (a ⊓ b) * wt X p (a ⊔ b) := by
  by_cases ha : a ⊆ X
  · by_cases hb : b ⊆ X
    · have hinter : a ⊓ b ⊆ X := by
        rw [Finset.inf_eq_inter]
        exact Finset.inter_subset_left.trans ha
      have hunion : a ⊔ b ⊆ X := by
        rw [Finset.sup_eq_union]
        exact Finset.union_subset ha hb
      rw [wt_of_subset ha, wt_of_subset hb, wt_of_subset hinter, wt_of_subset hunion,
        Finset.inf_eq_inter, Finset.sup_eq_union]
      -- the two exponent pairs agree, by `|a∩b| + |a∪b| = |a| + |b|`
      have hcards : (a ∩ b).card + (a ∪ b).card = a.card + b.card :=
        Finset.card_inter_add_card_union a b
      have hax : a.card ≤ X.card := Finset.card_le_card ha
      have hbx : b.card ≤ X.card := Finset.card_le_card hb
      have hux : (a ∪ b).card ≤ X.card := Finset.card_le_card hunion
      have hix : (a ∩ b).card ≤ X.card := Finset.card_le_card hinter
      have e1 : a.card + b.card = (a ∩ b).card + (a ∪ b).card := hcards.symm
      have e2 : (X.card - a.card) + (X.card - b.card)
          = (X.card - (a ∩ b).card) + (X.card - (a ∪ b).card) := by omega
      refine le_of_eq ?_
      calc p ^ a.card * (1 - p) ^ (X.card - a.card)
              * (p ^ b.card * (1 - p) ^ (X.card - b.card))
          = p ^ (a.card + b.card) * (1 - p) ^ ((X.card - a.card) + (X.card - b.card)) := by
            rw [pow_add, pow_add]; ring
        _ = p ^ ((a ∩ b).card + (a ∪ b).card)
              * (1 - p) ^ ((X.card - (a ∩ b).card) + (X.card - (a ∪ b).card)) := by
            rw [e1, e2]
        _ = p ^ (a ∩ b).card * (1 - p) ^ (X.card - (a ∩ b).card)
              * (p ^ (a ∪ b).card * (1 - p) ^ (X.card - (a ∪ b).card)) := by
            rw [pow_add, pow_add]; ring
    · have hb0 : wt X p b = 0 := by rw [wt, if_neg hb]
      rw [hb0, mul_zero]
      exact mul_nonneg (wt_nonneg hp0 hp1 _) (wt_nonneg hp0 hp1 _)
  · have ha0 : wt X p a = 0 := by rw [wt, if_neg ha]
    rw [ha0, zero_mul]
    exact mul_nonneg (wt_nonneg hp0 hp1 _) (wt_nonneg hp0 hp1 _)

/-! ## `X.powerset` is closed under the lattice operations -/

lemma infs_powerset_self (X : Finset α) : X.powerset ⊼ X.powerset = X.powerset := by
  apply Finset.Subset.antisymm
  · intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_infs.mp hc
    rw [Finset.mem_powerset] at ha hb ⊢
    rw [Finset.inf_eq_inter]
    exact Finset.inter_subset_left.trans ha
  · intro a ha
    exact Finset.mem_infs.mpr ⟨a, ha, a, ha, inf_idem a⟩

lemma sups_powerset_self (X : Finset α) : X.powerset ⊻ X.powerset = X.powerset := by
  apply Finset.Subset.antisymm
  · intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sups.mp hc
    rw [Finset.mem_powerset] at ha hb ⊢
    rw [Finset.sup_eq_union]
    exact Finset.union_subset ha hb
  · intro a ha
    exact Finset.mem_sups.mpr ⟨a, ha, a, ha, sup_idem a⟩

/-! ## Harris / FKG for the `p`-biased measure

`Increasing`, `Decreasing`, and `pBiased_eq_sum_wt` also live in `Sunflower.Robust`. -/

/-! ### Generic facts about `pBiased` -/

lemma pBiased_true (X : Finset α) (p : ℝ) : pBiased X p (fun _ => True) = 1 := by
  rw [pBiased_eq_sum_wt]
  refine Eq.trans (Finset.sum_congr rfl fun R _ => ?_) (sum_wt X p)
  simp

lemma pBiased_le_one {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset α → Prop) [DecidablePred P] : pBiased X p P ≤ 1 := by
  rw [← pBiased_true X p]
  exact pBiased_mono hp0 hp1 X fun _ _ => trivial

omit [DecidableEq α] in
/-- Splitting an event along another. -/
lemma pBiased_split (X : Finset α) (p : ℝ) (P Q : Finset α → Prop)
    [DecidablePred P] [DecidablePred Q] :
    pBiased X p P
      = pBiased X p (fun R => P R ∧ Q R) + pBiased X p (fun R => P R ∧ ¬ Q R) := by
  rw [pBiased, pBiased, pBiased, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases hP : P R <;> by_cases hQ : Q R <;> simp [hP, hQ]

/-- **Union bound**, in the form the Janson step needs. -/
lemma pBiased_and_exists_le_sum {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (U : Finset α → Prop) (f : ι → Finset α → Prop)
    [DecidablePred U] [∀ i, DecidablePred (f i)] :
    pBiased X p (fun R => U R ∧ ∃ i ∈ s, f i R)
      ≤ ∑ i ∈ s, pBiased X p (fun R => U R ∧ f i R) := by
  classical
  have hswap : ∑ i ∈ s, pBiased X p (fun R => U R ∧ f i R)
      = ∑ R ∈ X.powerset, wt X p R
          * ∑ i ∈ s, (if U R ∧ f i R then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ s) => pBiased_eq_sum_wt X p (fun R => U R ∧ f i R),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun R _ => by rw [Finset.mul_sum]
  rw [pBiased_eq_sum_wt, hswap]
  refine Finset.sum_le_sum fun R _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg hp0 hp1 R)
  by_cases hU : U R
  · by_cases hex : ∃ i ∈ s, f i R
    · obtain ⟨i, his, hfi⟩ := hex
      calc (if U R ∧ ∃ i ∈ s, f i R then (1 : ℝ) else 0)
          = (if U R ∧ f i R then (1 : ℝ) else 0) := by
            rw [if_pos ⟨hU, ⟨i, his, hfi⟩⟩, if_pos ⟨hU, hfi⟩]
        _ ≤ ∑ j ∈ s, (if U R ∧ f j R then (1 : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun j => if U R ∧ f j R then (1 : ℝ) else 0)
              (fun j _ => by positivity) his
    · rw [if_neg (fun h => hex h.2)]
      exact Finset.sum_nonneg fun j _ => by split <;> norm_num
  · rw [if_neg (fun h => hU h.1)]
    exact Finset.sum_nonneg fun j _ => by split <;> norm_num

/-- **Harris' inequality (FKG) for the `p`-biased measure**: two increasing events are
positively correlated.

Proved from the Ahlswede–Daykin four functions theorem applied with `𝒜 = ℬ = X.powerset`,
using log-modularity of the weight (`wt_mul_le`) and closure of the powerset under `∩`, `∪`. -/
theorem pBiased_mul_le_pBiased_and {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (hP : Increasing P) (hQ : Increasing Q) :
    pBiased X p P * pBiased X p Q ≤ pBiased X p (fun R => P R ∧ Q R) := by
  classical
  set f₁ : Finset α → ℝ := fun R => wt X p R * (if P R then (1 : ℝ) else 0) with hf₁
  set f₂ : Finset α → ℝ := fun R => wt X p R * (if Q R then (1 : ℝ) else 0) with hf₂
  set f₃ : Finset α → ℝ := fun R => wt X p R with hf₃
  set f₄ : Finset α → ℝ := fun R =>
    wt X p R * ((if P R then (1 : ℝ) else 0) * (if Q R then (1 : ℝ) else 0)) with hf₄
  have hind : ∀ (S : Finset α → Prop) [DecidablePred S] (R : Finset α),
      (0 : ℝ) ≤ (if S R then (1 : ℝ) else 0) := by
    intro S _ R; split <;> norm_num
  have h₁ : 0 ≤ f₁ := fun R => mul_nonneg (wt_nonneg hp0 hp1 R) (hind P R)
  have h₂ : 0 ≤ f₂ := fun R => mul_nonneg (wt_nonneg hp0 hp1 R) (hind Q R)
  have h₃ : 0 ≤ f₃ := fun R => wt_nonneg hp0 hp1 R
  have h₄ : 0 ≤ f₄ := fun R =>
    mul_nonneg (wt_nonneg hp0 hp1 R) (mul_nonneg (hind P R) (hind Q R))
  have hkey : ∀ a b : Finset α, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b) := by
    intro a b
    by_cases hPa : P a
    · by_cases hQb : Q b
      · have hPab : P (a ⊔ b) := hP (by rw [Finset.sup_eq_union]; exact Finset.subset_union_left) hPa
        have hQab : Q (a ⊔ b) := hQ (by rw [Finset.sup_eq_union]; exact Finset.subset_union_right) hQb
        simp only [hf₁, hf₂, hf₃, hf₄, if_pos hPa, if_pos hQb, if_pos hPab, if_pos hQab,
          mul_one]
        exact wt_mul_le hp0 hp1 a b
      · simp only [hf₁, hf₂, if_neg hQb, mul_zero]
        exact mul_nonneg (h₃ _) (h₄ _)
    · simp only [hf₁, if_neg hPa, mul_zero, zero_mul]
      exact mul_nonneg (h₃ _) (h₄ _)
  have hff := four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ hkey X.powerset X.powerset
  rw [infs_powerset_self, sups_powerset_self] at hff
  rw [pBiased_eq_sum_wt, pBiased_eq_sum_wt, pBiased_eq_sum_wt]
  refine le_trans hff (le_of_eq ?_)
  rw [show (∑ R ∈ X.powerset, f₃ R) = 1 from sum_wt X p, one_mul]
  refine Finset.sum_congr rfl fun R _ => ?_
  simp only [hf₄]
  by_cases hPR : P R <;> by_cases hQR : Q R <;> simp [hPR, hQR]

/-- **Harris' inequality, mixed form**: an increasing and a decreasing event are negatively
correlated. This is the form Janson's inequality consumes (`Aᵢ` increasing, `⋂ⱼ ¬Aⱼ`
decreasing). -/
theorem pBiased_and_le_mul {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (hP : Increasing P) (hQ : Decreasing Q) :
    pBiased X p (fun R => P R ∧ Q R) ≤ pBiased X p P * pBiased X p Q := by
  classical
  -- apply the increasing case to `P` and `¬Q`
  have hnQ : Increasing (fun R => ¬ Q R) := fun a b hab hna hQb => hna (hQ hab hQb)
  have hharris := pBiased_mul_le_pBiased_and (X := X) (p := p) hp0 hp1 hP hnQ
  -- `Pr[P] = Pr[P ∧ Q] + Pr[P ∧ ¬Q]` and `Pr[Q] + Pr[¬Q] = 1`
  have hsplitP : pBiased X p P
      = pBiased X p (fun R => P R ∧ Q R) + pBiased X p (fun R => P R ∧ ¬ Q R) := by
    rw [pBiased, pBiased, pBiased, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun R _ => ?_
    by_cases hPR : P R <;> by_cases hQR : Q R <;> simp [hPR, hQR]
  have hQsum := pBiased_add_not X p Q
  have hQle : pBiased X p (fun R => ¬ Q R) = 1 - pBiased X p Q := by linarith
  rw [hQle] at hharris
  nlinarith [hharris, hsplitP, pBiased_nonneg hp0 hp1 X (fun R => P R ∧ ¬ Q R)]

/-! ## Step 2: independence on disjoint coordinates

If `P` is determined by `R ∩ Y` and `Q` by `R \ Y`, then `P` and `Q` are independent under
the `p`-biased measure. The proof is the bijection `R ↦ (R ∩ Y, R \ Y)` from `X.powerset` to
`Y.powerset ×ˢ (X \ Y).powerset`, under which the weight factorises (`wt_split`). -/

/-- **Independence on disjoint coordinates.** If the event `P` is determined by `R ∩ Y` and
`Q` by `R \ Y`, then `Pr[P ∧ Q] = Pr[P]·Pr[Q]`.

This is step 2 of the Janson route: in the telescoping product, `Aᵢ = [Sᵢ ⊆ R]` is
determined by `R ∩ Sᵢ`, and the conjunction of the `¬Aⱼ` for `Sⱼ` disjoint from `Sᵢ` is
determined by `R \ Sᵢ`. -/
theorem pBiased_and_of_indep {X Y : Finset α} (hY : Y ⊆ X) {p : ℝ}
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (hP : ∀ R, P R ↔ P (R ∩ Y)) (hQ : ∀ R, Q R ↔ Q (R \ Y)) :
    pBiased X p (fun R => P R ∧ Q R) = pBiased X p P * pBiased X p Q := by
  classical
  have key : ∀ F₁ F₂ : Finset α → ℝ,
      ∑ R ∈ X.powerset, F₁ (R ∩ Y) * F₂ (R \ Y)
        = (∑ A ∈ Y.powerset, F₁ A) * ∑ B ∈ (X \ Y).powerset, F₂ B := by
    intro F₁ F₂
    rw [sum_powerset_split hY fun A B => F₁ A * F₂ B, Finset.sum_mul_sum]
  have hA1 : ∑ A ∈ Y.powerset, wt Y p A = 1 := sum_wt _ _
  have hB1 : ∑ B ∈ (X \ Y).powerset, wt (X \ Y) p B = 1 := sum_wt _ _
  -- the conjunction factorises
  have e1 : pBiased X p (fun R => P R ∧ Q R)
      = (∑ A ∈ Y.powerset, wt Y p A * (if P A then (1 : ℝ) else 0))
        * ∑ B ∈ (X \ Y).powerset, wt (X \ Y) p B * (if Q B then (1 : ℝ) else 0) := by
    rw [pBiased_eq_sum_wt, ← key (fun A => wt Y p A * (if P A then (1 : ℝ) else 0))
      fun B => wt (X \ Y) p B * (if Q B then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [wt_split hY (Finset.mem_powerset.mp hR)]
    by_cases hPR : P R
    · have hPi : P (R ∩ Y) := (hP R).mp hPR
      by_cases hQR : Q R
      · have hQi : Q (R \ Y) := (hQ R).mp hQR
        simp [hPR, hQR, hPi, hQi]
      · have hQi : ¬ Q (R \ Y) := fun hh => hQR ((hQ R).mpr hh)
        simp [hPR, hQR, hPi, hQi]
    · have hPi : ¬ P (R ∩ Y) := fun hh => hPR ((hP R).mpr hh)
      simp [hPR, hPi]
  -- the two marginals
  have e2 : pBiased X p P
      = ∑ A ∈ Y.powerset, wt Y p A * (if P A then (1 : ℝ) else 0) := by
    have h := key (fun A => wt Y p A * (if P A then (1 : ℝ) else 0)) fun B => wt (X \ Y) p B
    rw [hB1, mul_one] at h
    rw [pBiased_eq_sum_wt, ← h]
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [wt_split hY (Finset.mem_powerset.mp hR)]
    by_cases hPR : P R
    · have hPi : P (R ∩ Y) := (hP R).mp hPR
      simp [hPR, hPi]
    · have hPi : ¬ P (R ∩ Y) := fun hh => hPR ((hP R).mpr hh)
      simp [hPR, hPi]
  have e3 : pBiased X p Q
      = ∑ B ∈ (X \ Y).powerset, wt (X \ Y) p B * (if Q B then (1 : ℝ) else 0) := by
    have h := key (fun A => wt Y p A) fun B => wt (X \ Y) p B * (if Q B then (1 : ℝ) else 0)
    rw [hA1, one_mul] at h
    rw [pBiased_eq_sum_wt, ← h]
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [wt_split hY (Finset.mem_powerset.mp hR)]
    by_cases hQR : Q R
    · have hQi : Q (R \ Y) := (hQ R).mp hQR
      simp [hQR, hQi]
    · have hQi : ¬ Q (R \ Y) := fun hh => hQR ((hQ R).mpr hh)
      simp [hQR, hQi]
  rw [e1, e2, e3]

/-! ## Step 3: basic Janson

The events are `Aᵢ R = [S i ⊆ R]` for `S : Fin n → Finset α`, linearly ordered by the index.
Everything is carried out for an arbitrary sub-collection `T : Finset (Fin n)` — the extended
form in step 4 averages over a random such `T`, so the restricted version is what it needs.

Division-free: instead of conditional probabilities we induct on the multiplicative form
`Pr[C ∧ ¬Aₖ] ≤ Pr[C] · (1 − Pr[Aₖ] + ∑_{j ∈ Depₖ} Pr[Aₖ ∧ Aⱼ])`, which degenerates correctly
when `Pr[C] = 0`. -/

variable {n : ℕ}

/-- The event that no set indexed by `T` below `k` is contained in `R`. -/
def NoneBelow (S : Fin n → Finset α) (T : Finset (Fin n)) (k : ℕ) (R : Finset α) : Prop :=
  ∀ j : Fin n, j ∈ T → (j : ℕ) < k → ¬ (S j ⊆ R)

instance (S : Fin n → Finset α) (T : Finset (Fin n)) (k : ℕ) :
    DecidablePred (NoneBelow S T k) :=
  fun _ => inferInstanceAs (Decidable (∀ _, _))

/-- The indices of `T` below `k` whose set meets `S k'` — the "dependent" predecessors. -/
def depBelow (S : Fin n → Finset α) (T : Finset (Fin n)) (k : ℕ) (k' : Fin n) :
    Finset (Fin n) :=
  T.filter fun j => (j : ℕ) < k ∧ ¬ Disjoint (S j) (S k')

/-- The Janson factor at index `k'`, with predecessors taken from `T` below `k`. -/
noncomputable def jansonFactor (X : Finset α) (p : ℝ) (S : Fin n → Finset α)
    (T : Finset (Fin n)) (k : ℕ) (k' : Fin n) : ℝ :=
  1 - pBiased X p (fun R => S k' ⊆ R)
    + ∑ j ∈ depBelow S T k k', pBiased X p (fun R => S k' ⊆ R ∧ S j ⊆ R)

lemma jansonFactor_nonneg {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Fin n → Finset α) (T : Finset (Fin n)) (k : ℕ) (k' : Fin n) :
    0 ≤ jansonFactor X p S T k k' := by
  have h1 : pBiased X p (fun R => S k' ⊆ R) ≤ 1 := pBiased_le_one hp0 hp1 _
  have h2 : 0 ≤ ∑ j ∈ depBelow S T k k', pBiased X p (fun R => S k' ⊆ R ∧ S j ⊆ R) :=
    Finset.sum_nonneg fun j _ => pBiased_nonneg hp0 hp1 _ _
  rw [jansonFactor]; linarith

/-- **The Janson step.** `Pr[C ∧ ¬Aₖ] ≤ Pr[C] · (1 − Pr[Aₖ] + ∑_{dep} Pr[Aₖ ∧ Aⱼ])`.

Split the predecessors of `k` into those disjoint from `S k` — giving a decreasing event `E`
independent of `Aₖ`, by `pBiased_and_of_indep` — and the rest, bounded by a union bound with
each term controlled by `pBiased_and_le_mul` (`Aₖ ∧ Aⱼ` increasing, `E` decreasing). Then
`Pr[C] ≤ Pr[E]`, and a sign split on the bracket. -/
theorem janson_step {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : Fin n → Finset α} (hS : ∀ i, S i ⊆ X) (T : Finset (Fin n)) (k : ℕ) (k' : Fin n)
    (hk'T : k' ∈ T) (hk : (k' : ℕ) = k) :
    pBiased X p (NoneBelow S T (k + 1))
      ≤ pBiased X p (NoneBelow S T k) * jansonFactor X p S T k k' := by
  classical
  set E : Finset α → Prop :=
    fun R => ∀ j : Fin n, j ∈ T → (j : ℕ) < k → Disjoint (S j) (S k') → ¬ (S j ⊆ R) with hEdef
  set A : Finset α → Prop := fun R => S k' ⊆ R with hAdef
  have hEdec : Decreasing E :=
    fun a b hab hEb j hjT hj hd hsub => hEb j hjT hj hd (hsub.trans hab)
  have hCE : ∀ R, NoneBelow S T k R → E R := fun R hC j hjT hj _ => hC j hjT hj
  have hsucc : ∀ R, NoneBelow S T (k + 1) R ↔ (NoneBelow S T k R ∧ ¬ A R) := by
    intro R
    constructor
    · exact fun h => ⟨fun j hjT hj => h j hjT (by omega), h k' hk'T (by omega)⟩
    · rintro ⟨h1, h2⟩ j hjT hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact h1 j hjT hlt
      · have hjk : j = k' := Fin.ext (by omega)
        rw [hjk]; exact h2
  have hEA : pBiased X p (fun R => A R ∧ E R) = pBiased X p A * pBiased X p E := by
    refine pBiased_and_of_indep (hS k') (fun R => ?_) (fun R => ?_)
    · rw [hAdef]
      exact ⟨fun h => Finset.subset_inter h le_rfl, fun h => h.trans Finset.inter_subset_left⟩
    · rw [hEdef]
      refine ⟨fun h j hjT hj hd hsub => h j hjT hj hd (hsub.trans Finset.sdiff_subset), ?_⟩
      intro h j hjT hj hd hsub
      refine h j hjT hj hd fun x hx => ?_
      rw [Finset.mem_sdiff]
      exact ⟨hsub hx, fun hxk => (Finset.disjoint_left.mp hd) hx hxk⟩
  have hsplitEA := pBiased_split X p (fun R => A R ∧ E R)
    (fun R => ∀ j ∈ depBelow S T k k', ¬ (S j ⊆ R))
  have hub : pBiased X p (fun R => (A R ∧ E R) ∧ ¬ ∀ j ∈ depBelow S T k k', ¬ (S j ⊆ R))
      ≤ ∑ j ∈ depBelow S T k k', pBiased X p (fun R => (A R ∧ E R) ∧ S j ⊆ R) := by
    refine le_trans (le_of_eq (pBiased_congr X p ?_)) (pBiased_and_exists_le_sum hp0 hp1
      (depBelow S T k k') (fun R => A R ∧ E R) fun j R => S j ⊆ R)
    intro R
    constructor
    · rintro ⟨hAE, hne⟩
      refine ⟨hAE, ?_⟩
      by_contra hc
      exact hne fun j hj hsub => hc ⟨j, hj, hsub⟩
    · rintro ⟨hAE, j, hj, hsub⟩
      exact ⟨hAE, fun hall => hall j hj hsub⟩
  have hterm : ∀ j ∈ depBelow S T k k',
      pBiased X p (fun R => (A R ∧ E R) ∧ S j ⊆ R)
        ≤ pBiased X p (fun R => S k' ⊆ R ∧ S j ⊆ R) * pBiased X p E := by
    intro j _
    have hinc : Increasing (fun R => S k' ⊆ R ∧ S j ⊆ R) :=
      fun a b hab h => ⟨h.1.trans hab, h.2.trans hab⟩
    refine le_trans (le_of_eq (pBiased_congr X p fun R => ?_))
      (pBiased_and_le_mul hp0 hp1 hinc hEdec)
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
  have hCA : pBiased X p E * (pBiased X p A
        - ∑ j ∈ depBelow S T k k', pBiased X p (fun R => S k' ⊆ R ∧ S j ⊆ R))
      ≤ pBiased X p (fun R => NoneBelow S T k R ∧ A R) := by
    have hmono : pBiased X p (fun R => (A R ∧ E R) ∧ ∀ j ∈ depBelow S T k k', ¬ (S j ⊆ R))
        ≤ pBiased X p (fun R => NoneBelow S T k R ∧ A R) := by
      refine pBiased_mono hp0 hp1 X fun R hR => ?_
      obtain ⟨⟨hA, hE⟩, hB⟩ := hR
      refine ⟨fun j hjT hj => ?_, hA⟩
      by_cases hd : Disjoint (S j) (S k')
      · exact hE j hjT hj hd
      · exact hB j (Finset.mem_filter.mpr ⟨hjT, hj, hd⟩)
    have hsum : ∑ j ∈ depBelow S T k k', pBiased X p (fun R => (A R ∧ E R) ∧ S j ⊆ R)
        ≤ (∑ j ∈ depBelow S T k k', pBiased X p (fun R => S k' ⊆ R ∧ S j ⊆ R))
            * pBiased X p E := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hterm
    rw [hEA] at hsplitEA
    nlinarith [hsplitEA, hub, hsum, hmono]
  have hCleE : pBiased X p (NoneBelow S T k) ≤ pBiased X p E := pBiased_mono hp0 hp1 X hCE
  have hCnn : 0 ≤ pBiased X p (NoneBelow S T k) := pBiased_nonneg hp0 hp1 _ _
  have hsplitC := pBiased_split X p (NoneBelow S T k) A
  have hgoal : pBiased X p (fun R => NoneBelow S T k R ∧ ¬ A R)
      ≤ pBiased X p (NoneBelow S T k) * jansonFactor X p S T k k' := by
    set Tv : ℝ := pBiased X p A
      - ∑ j ∈ depBelow S T k k', pBiased X p (fun R => S k' ⊆ R ∧ S j ⊆ R) with hTv
    have hfac : jansonFactor X p S T k k' = 1 - Tv := by rw [jansonFactor, hTv, hAdef]; ring
    rcases le_or_gt 0 Tv with hTpos | hTneg
    · have hkey : pBiased X p (NoneBelow S T k) * Tv
          ≤ pBiased X p (fun R => NoneBelow S T k R ∧ A R) :=
        le_trans (mul_le_mul_of_nonneg_right hCleE hTpos) hCA
      rw [hfac]; nlinarith [hsplitC]
    · have hle : pBiased X p (fun R => NoneBelow S T k R ∧ ¬ A R)
          ≤ pBiased X p (NoneBelow S T k) :=
        pBiased_mono hp0 hp1 X fun R hR => hR.1
      rw [hfac]; nlinarith
  exact le_trans (le_of_eq (pBiased_congr X p hsucc)) hgoal

/-- **Janson's inequality, product form**, over an arbitrary sub-collection `T`. -/
theorem janson_prod {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : Fin n → Finset α} (hS : ∀ i, S i ⊆ X) (T : Finset (Fin n)) :
    ∀ k : ℕ, k ≤ n →
      pBiased X p (NoneBelow S T k)
        ≤ ∏ i ∈ T.filter fun i : Fin n => (i : ℕ) < k, jansonFactor X p S T (i : ℕ) i := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : pBiased X p (NoneBelow S T 0) = 1 := by
      have hcg : pBiased X p (NoneBelow S T 0) = pBiased X p (fun _ : Finset α => True) :=
        pBiased_congr X p fun R =>
          ⟨fun _ => trivial, fun _ j _ hj => absurd hj (Nat.not_lt_zero _)⟩
      rw [hcg, pBiased_true]
    rw [h0]
    have hemptyf : (T.filter fun i : Fin n => (i : ℕ) < 0) = ∅ := by ext i; simp
    rw [hemptyf, Finset.prod_empty]
  | succ k ih =>
    intro hkn
    have hk' : k < n := by omega
    set k' : Fin n := ⟨k, hk'⟩ with hk'def
    have hkval : (k' : ℕ) = k := by rw [hk'def]
    by_cases hk'T : k' ∈ T
    · have hstep := janson_step hp0 hp1 hS T k k' hk'T hkval
      have hprod : (T.filter fun i : Fin n => (i : ℕ) < k + 1)
          = insert k' (T.filter fun i : Fin n => (i : ℕ) < k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hiT, hi⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inr ⟨hiT, h⟩
          · exact Or.inl (Fin.ext (by omega))
        · rintro (rfl | ⟨hiT, h⟩)
          · exact ⟨hk'T, by omega⟩
          · exact ⟨hiT, by omega⟩
      have hnotmem : k' ∉ T.filter fun i : Fin n => (i : ℕ) < k := by simp [hkval]
      rw [hprod, Finset.prod_insert hnotmem]
      calc pBiased X p (NoneBelow S T (k + 1))
          ≤ pBiased X p (NoneBelow S T k) * jansonFactor X p S T k k' := hstep
        _ ≤ (∏ i ∈ T.filter fun i : Fin n => (i : ℕ) < k, jansonFactor X p S T (i : ℕ) i)
              * jansonFactor X p S T k k' :=
            mul_le_mul_of_nonneg_right (ih (by omega))
              (jansonFactor_nonneg hp0 hp1 S T k k')
        _ = jansonFactor X p S T (k' : ℕ) k'
              * ∏ i ∈ T.filter fun i : Fin n => (i : ℕ) < k, jansonFactor X p S T (i : ℕ) i := by
            rw [hkval]; ring
    · -- the new index is not in `T`: nothing changes
      have hev : pBiased X p (NoneBelow S T (k + 1)) = pBiased X p (NoneBelow S T k) := by
        refine pBiased_congr X p fun R => ⟨fun h j hjT hj => h j hjT (by omega), ?_⟩
        intro h j hjT hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact h j hjT hlt
        · exact absurd (show j = k' from Fin.ext (by omega)) fun hjk => hk'T (hjk ▸ hjT)
      have hf : (T.filter fun i : Fin n => (i : ℕ) < k + 1)
          = T.filter fun i : Fin n => (i : ℕ) < k := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hiT, hi⟩
          refine ⟨hiT, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h
          · exact absurd (show i = k' from Fin.ext (by omega)) fun hik => hk'T (hik ▸ hiT)
        · rintro ⟨hiT, hi⟩; exact ⟨hiT, by omega⟩
      rw [hev, hf]
      exact ih (by omega)

/-- **Janson's inequality (basic form)**, over a sub-collection `T`:
`Pr[⋀_{i∈T} ¬Aᵢ] ≤ exp(−μ_T + Δ_T)`. -/
theorem janson_on {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : Fin n → Finset α} (hS : ∀ i, S i ⊆ X) (T : Finset (Fin n)) :
    pBiased X p (fun R => ∀ i ∈ T, ¬ (S i ⊆ R))
      ≤ Real.exp (- (∑ i ∈ T, pBiased X p (fun R => S i ⊆ R))
          + ∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i,
              pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)) := by
  classical
  have hfilter : (T.filter fun i : Fin n => (i : ℕ) < n) = T := by
    ext i; simp
  have h1 : pBiased X p (fun R => ∀ i ∈ T, ¬ (S i ⊆ R)) = pBiased X p (NoneBelow S T n) :=
    pBiased_congr X p fun R => ⟨fun h j hjT _ => h j hjT, fun h j hjT => h j hjT j.isLt⟩
  have h2 := janson_prod hp0 hp1 hS T n le_rfl
  rw [hfilter] at h2
  rw [h1]
  refine le_trans h2 ?_
  set a : Fin n → ℝ := fun i => pBiased X p (fun R => S i ⊆ R) with ha
  set b : Fin n → ℝ := fun i => ∑ j ∈ depBelow S T (i : ℕ) i,
    pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R) with hb
  have hstep : ∀ i : Fin n, jansonFactor X p S T (i : ℕ) i ≤ Real.exp (b i - a i) := by
    intro i
    have hfac : jansonFactor X p S T (i : ℕ) i = (b i - a i) + 1 := by
      rw [jansonFactor, ha, hb]; ring
    rw [hfac]
    exact Real.add_one_le_exp _
  calc ∏ i ∈ T, jansonFactor X p S T (i : ℕ) i
      ≤ ∏ i ∈ T, Real.exp (b i - a i) :=
        Finset.prod_le_prod (fun i _ => jansonFactor_nonneg hp0 hp1 S T _ i) fun i _ => hstep i
    _ = Real.exp (∑ i ∈ T, (b i - a i)) := (Real.exp_sum _ _).symm
    _ = Real.exp (- (∑ i ∈ T, a i) + ∑ i ∈ T, b i) := by
        congr 1
        rw [Finset.sum_sub_distrib]
        ring

/-- **Janson's inequality (basic form)**, over the whole family. -/
theorem janson {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : Fin n → Finset α} (hS : ∀ i, S i ⊆ X) :
    pBiased X p (fun R => ∀ i : Fin n, ¬ (S i ⊆ R))
      ≤ Real.exp (- (∑ i : Fin n, pBiased X p (fun R => S i ⊆ R))
          + ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
              pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)) := by
  have h := janson_on hp0 hp1 hS (Finset.univ : Finset (Fin n))
  refine le_trans (le_of_eq (pBiased_congr X p fun R => ?_)) h
  exact ⟨fun hh j _ => hh j, fun hh j => hh j (Finset.mem_univ j)⟩

/-! ## Step 4: extended Janson

The standard route (Alon–Spencer): apply basic Janson to a *random* sub-collection `T`,
including each index independently with probability `q`. Then `E[μ_T] = q·μ` and
`E[Δ_T] = q²·Δ`, so some `T` achieves `−μ_T + Δ_T ≤ −qμ + q²Δ`.

The random sub-collection is itself a `p`-biased set — on the index type `Fin n` — so the
whole averaging reuses `wt`, `pBiased_mem` and `pBiased_mem_pair` with ground set `univ`.

We state the `q`-parameterised bound (`janson_ext_q`), which is division-free, and derive the
optimised `exp(−μ²/(4Δ))` from it. -/

/-- A weighted average is attained from below: some `T` is at least as good as the mean. -/
lemma exists_le_of_wt_avg {ι : Type*} [DecidableEq ι] (V : Finset ι) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Finset ι → ℝ) {M : ℝ}
    (h : ∑ T ∈ V.powerset, wt V q T * f T = M) :
    ∃ T ∈ V.powerset, f T ≤ M := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ T ∈ V.powerset, wt V q T * M < ∑ T ∈ V.powerset, wt V q T * f T := by
    refine Finset.sum_lt_sum (fun T hT => ?_) ?_
    · exact mul_le_mul_of_nonneg_left (hcon T hT).le (wt_nonneg hq0 hq1 T)
    · -- some set carries positive weight, since the weights sum to `1`
      by_contra hall
      push Not at hall
      have : ∑ T ∈ V.powerset, wt V q T * M = ∑ T ∈ V.powerset, wt V q T * f T := by
        refine Finset.sum_congr rfl fun T hT => ?_
        exact le_antisymm (mul_le_mul_of_nonneg_left (hcon T hT).le (wt_nonneg hq0 hq1 T))
          (hall T hT)
      have hpos : (0 : ℝ) < ∑ T ∈ V.powerset, wt V q T * (f T - M) := by
        have hne : ∑ T ∈ V.powerset, wt V q T = 1 := sum_wt V q
        by_contra hle
        push Not at hle
        have : ∑ T ∈ V.powerset, wt V q T * (f T - M) = 0 := by
          refine le_antisymm hle (Finset.sum_nonneg fun T hT => ?_)
          exact mul_nonneg (wt_nonneg hq0 hq1 T) (by linarith [hcon T hT])
        have hzero : ∀ T ∈ V.powerset, wt V q T * (f T - M) = 0 := by
          refine (Finset.sum_eq_zero_iff_of_nonneg fun T hT =>
            mul_nonneg (wt_nonneg hq0 hq1 T) (by linarith [hcon T hT])).mp this
        have : ∀ T ∈ V.powerset, wt V q T = 0 := by
          intro T hT
          rcases mul_eq_zero.mp (hzero T hT) with h1 | h2
          · exact h1
          · exact absurd h2 (by linarith [hcon T hT])
        rw [Finset.sum_congr rfl this, Finset.sum_const_zero] at hne
        exact absurd hne (by norm_num)
      have hrw : ∑ T ∈ V.powerset, wt V q T * (f T - M)
          = (∑ T ∈ V.powerset, wt V q T * f T) - ∑ T ∈ V.powerset, wt V q T * M := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun T _ => by ring
      rw [hrw, ← this] at hpos
      linarith
  rw [← Finset.sum_mul, sum_wt, one_mul, h] at hsum
  exact absurd hsum (lt_irrefl M)

variable {n : ℕ}

/-- **Extended Janson, `q`-form.** For every `q ∈ [0,1]`,
`Pr[⋀ᵢ ¬Aᵢ] ≤ exp(−q·μ + q²·Δ)`. Division-free; the optimised form follows by choosing `q`. -/
theorem janson_ext_q {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : Fin n → Finset α} (hS : ∀ i, S i ⊆ X) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pBiased X p (fun R => ∀ i : Fin n, ¬ (S i ⊆ R))
      ≤ Real.exp (- (q * ∑ i : Fin n, pBiased X p (fun R => S i ⊆ R))
          + q ^ 2 * ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
              pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)) := by
  classical
  set a : Fin n → ℝ := fun i => pBiased X p (fun R => S i ⊆ R) with ha
  set c : Fin n → Fin n → ℝ := fun i j => pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R) with hc
  set μ : ℝ := ∑ i : Fin n, a i with hμ
  set D : ℝ := ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i, c i j with hD
  have hdep : ∀ (T : Finset (Fin n)) (i : Fin n),
      depBelow S T (i : ℕ) i = (depBelow S Finset.univ (i : ℕ) i).filter fun j => j ∈ T := by
    intro T i
    ext j
    simp only [depBelow, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  -- `E[μ_T] = q·μ`
  have hE1 : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      wt Finset.univ q T * ∑ i ∈ T, a i = q * μ := by
    have h1 : ∀ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        wt Finset.univ q T * ∑ i ∈ T, a i
          = ∑ i : Fin n, wt Finset.univ q T * (if i ∈ T then a i else 0) := by
      intro T _
      rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, hμ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm := pBiased_mem (V := (Finset.univ : Finset (Fin n))) (Finset.mem_univ i) q
    rw [pBiased_eq_sum_wt] at hm
    calc ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          wt Finset.univ q T * (if i ∈ T then a i else 0)
        = a i * ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
            wt Finset.univ q T * (if i ∈ T then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases hiT : i ∈ T <;> simp [hiT]; ring
      _ = a i * q := by rw [hm]
      _ = q * a i := by ring
  -- rewriting `Δ_T` with indicators
  have h2 : ∀ T : Finset (Fin n),
      ∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j
        = ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
            (if i ∈ T ∧ j ∈ T then c i j else 0) := by
    intro T
    have houter : ∑ i ∈ T, (∑ j ∈ depBelow S T (i : ℕ) i, c i j)
        = ∑ i : Fin n, (if i ∈ T then ∑ j ∈ depBelow S T (i : ℕ) i, c i j else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [houter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hiT : i ∈ T
    · rw [if_pos hiT, hdep T i, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjT : j ∈ T
      · rw [if_pos hjT, if_pos ⟨hiT, hjT⟩]
      · rw [if_neg hjT, if_neg fun hh => hjT hh.2]
    · rw [if_neg hiT]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg fun hh => hiT hh.1]
  -- `E[Δ_T] = q²·Δ`
  have hE2 : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      wt Finset.univ q T * (∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j) = q ^ 2 * D := by
    have hstep : ∀ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        wt Finset.univ q T * (∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j)
          = ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
              wt Finset.univ q T * (if i ∈ T ∧ j ∈ T then c i j else 0) := by
      intro T _
      rw [h2 T, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm, hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := by
      simp only [depBelow, Finset.mem_filter] at hj
      intro hh; rw [hh] at hj; omega
    have hm := pBiased_mem_pair (V := (Finset.univ : Finset (Fin n)))
      (Finset.mem_univ i) (Finset.mem_univ j) (Ne.symm hji) q
    rw [pBiased_eq_sum_wt] at hm
    calc ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          wt Finset.univ q T * (if i ∈ T ∧ j ∈ T then c i j else 0)
        = c i j * ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
            wt Finset.univ q T * (if i ∈ T ∧ j ∈ T then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases hh : i ∈ T ∧ j ∈ T <;> simp [hh]; ring
      _ = c i j * q ^ 2 := by rw [hm]
      _ = q ^ 2 * c i j := by ring
  -- combine into one average and pick a good `T`
  have havg : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      wt Finset.univ q T * ((- ∑ i ∈ T, a i)
        + ∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j)
      = (- (q * μ)) + q ^ 2 * D := by
    have hsplit : ∀ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        wt Finset.univ q T * ((- ∑ i ∈ T, a i)
            + ∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j)
          = (-1) * (wt Finset.univ q T * ∑ i ∈ T, a i)
            + wt Finset.univ q T * ∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j :=
      fun T _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hE1, hE2]
    ring
  obtain ⟨T, _, hTle⟩ := exists_le_of_wt_avg (Finset.univ : Finset (Fin n)) hq0 hq1
    (fun T => (- ∑ i ∈ T, a i) + ∑ i ∈ T, ∑ j ∈ depBelow S T (i : ℕ) i, c i j) havg
  have hmono : pBiased X p (fun R => ∀ i : Fin n, ¬ (S i ⊆ R))
      ≤ pBiased X p (fun R => ∀ i ∈ T, ¬ (S i ⊆ R)) :=
    pBiased_mono hp0 hp1 X fun R hR i _ => hR i
  exact le_trans hmono (le_trans (janson_on hp0 hp1 hS T) (Real.exp_le_exp.mpr hTle))

/-- **Extended Janson.** If `0 < Δ` and `μ ≤ 2Δ`, then `Pr[⋀ᵢ ¬Aᵢ] ≤ exp(−μ²/(4Δ))`.

This is ALWZ's Lemma 2.10 ingredient (their `exp(−μ²/2Δ̄)`, with `Δ̄` the ordered-pair sum
`2Δ`). Obtained from `janson_ext_q` at the optimal `q = μ/(2Δ)`. -/
theorem janson_ext {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {S : Fin n → Finset α} (hS : ∀ i, S i ⊆ X)
    (hDpos : 0 < ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
        pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R))
    (hle : (∑ i : Fin n, pBiased X p (fun R => S i ⊆ R))
      ≤ 2 * ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
          pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)) :
    pBiased X p (fun R => ∀ i : Fin n, ¬ (S i ⊆ R))
      ≤ Real.exp (- ((∑ i : Fin n, pBiased X p (fun R => S i ⊆ R)) ^ 2
          / (4 * ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
              pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R)))) := by
  classical
  set μ : ℝ := ∑ i : Fin n, pBiased X p (fun R => S i ⊆ R) with hμ
  set D : ℝ := ∑ i : Fin n, ∑ j ∈ depBelow S Finset.univ (i : ℕ) i,
    pBiased X p (fun R => S i ⊆ R ∧ S j ⊆ R) with hD
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun i _ => pBiased_nonneg hp0 hp1 _ _
  set q : ℝ := μ / (2 * D) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one (by linarith)]
    linarith
  refine le_trans (janson_ext_q hp0 hp1 hS hq0 hq1) (Real.exp_le_exp.mpr ?_)
  have hDne : D ≠ 0 := ne_of_gt hDpos
  rw [hq]
  field_simp
  ring_nf
  nlinarith [sq_nonneg μ, hDpos]

end Sunflower

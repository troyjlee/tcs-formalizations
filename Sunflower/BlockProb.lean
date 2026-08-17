/-
# Missing a block: the `p`-biased probability of avoiding, and of hitting every one of a
family of disjoint blocks

`Janson.pBiased_superset` computes `Pr[Y ⊆ R] = p^|Y|`. The lower-bound construction of ALWZ
§3 needs the complementary quantity `Pr[R ∩ Y = ∅] = (1−p)^|Y|`, and then the probability of
hitting *every* block of a pairwise-disjoint family, which factorises by independence on
disjoint coordinates (`Janson.pBiased_and_of_indep`).

Nothing here is specific to the construction; it is the `p`-biased toolkit for block events.
-/
import Sunflower.Janson

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- **Avoiding a block**: `Pr[R ∩ Y = ∅] = (1−p)^{|Y|}`. The mirror image of
`pBiased_superset`, by the same splitting bijection: the `Y`-marginal forces `R ∩ Y = ∅`,
and the `X \ Y` marginal sums to `1`. -/
lemma pBiased_disjoint {X Y : Finset α} (hY : Y ⊆ X) (p : ℝ) :
    pBiased X p (fun R => Disjoint R Y) = (1 - p) ^ Y.card := by
  classical
  rw [pBiased_eq_sum_wt]
  have hiff : ∀ R : Finset α, Disjoint R Y ↔ R ∩ Y = ∅ := fun R => Finset.disjoint_iff_inter_eq_empty
  have h1 : ∑ R ∈ X.powerset, wt X p R * (if Disjoint R Y then (1 : ℝ) else 0)
      = ∑ R ∈ X.powerset, (wt Y p (R ∩ Y) * (if R ∩ Y = ∅ then (1 : ℝ) else 0))
          * wt (X \ Y) p (R \ Y) := by
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [wt_split hY (Finset.mem_powerset.mp hR)]
    by_cases h : Disjoint R Y
    · rw [if_pos h, if_pos ((hiff R).mp h)]; ring
    · rw [if_neg h, if_neg fun hc => h ((hiff R).mpr hc)]; ring
  rw [h1, sum_powerset_split hY fun A B =>
    (wt Y p A * (if A = ∅ then (1 : ℝ) else 0)) * wt (X \ Y) p B]
  have h2 : ∀ A : Finset α,
      (∑ B ∈ (X \ Y).powerset, (wt Y p A * (if A = ∅ then (1 : ℝ) else 0)) * wt (X \ Y) p B)
        = wt Y p A * (if A = ∅ then (1 : ℝ) else 0) := by
    intro A; rw [← Finset.mul_sum, sum_wt, mul_one]
  rw [Finset.sum_congr rfl fun A _ => h2 A]
  rw [Finset.sum_eq_single ∅]
  · rw [if_pos rfl, mul_one, wt_of_subset (Finset.empty_subset Y)]
    simp
  · intro A _ hA; rw [if_neg hA, mul_zero]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.empty_subset Y)) h

/-- **Hitting a block**: `Pr[R ∩ Y ≠ ∅] = 1 − (1−p)^{|Y|}`. -/
lemma pBiased_not_disjoint {X Y : Finset α} (hY : Y ⊆ X) (p : ℝ) :
    pBiased X p (fun R => ¬ Disjoint R Y) = 1 - (1 - p) ^ Y.card := by
  have h := pBiased_add_not X p (fun R => Disjoint R Y)
  rw [pBiased_disjoint hY p] at h
  linarith

/-- **Hitting every block of a pairwise-disjoint family**: the events are independent, so the
probability is the product `∏ (1 − (1−p)^{|Bᵢ|})`. -/
lemma pBiased_forall_not_disjoint {ι : Type*} [DecidableEq ι] {X : Finset α} (p : ℝ)
    (B : ι → Finset α) :
    ∀ I : Finset ι, (∀ i ∈ I, B i ⊆ X) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)) →
      pBiased X p (fun R => ∀ i ∈ I, ¬ Disjoint R (B i))
        = ∏ i ∈ I, (1 - (1 - p) ^ (B i).card) := by
  classical
  intro I
  induction I using Finset.induction_on with
  | empty => intro _ _; simpa using pBiased_true X p
  | insert i I hi ih =>
      intro hsub hdisj
      have hiX : B i ⊆ X := hsub i (Finset.mem_insert_self i I)
      have hsub' : ∀ j ∈ I, B j ⊆ X := fun j hj => hsub j (Finset.mem_insert_of_mem hj)
      have hdisj' : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (B j) (B k) := fun j hj k hk =>
        hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
      -- the event splits as `(hits Bᵢ) ∧ (hits every block of I)`
      have hsplit : pBiased X p (fun R => ∀ j ∈ insert i I, ¬ Disjoint R (B j))
          = pBiased X p (fun R => (¬ Disjoint R (B i)) ∧ (∀ j ∈ I, ¬ Disjoint R (B j))) := by
        refine pBiased_congr X p fun R => ?_
        constructor
        · intro h
          exact ⟨h i (Finset.mem_insert_self i I), fun j hj => h j (Finset.mem_insert_of_mem hj)⟩
        · rintro ⟨h1, h2⟩ j hj
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact h1
          · exact h2 j hj'
      -- the first factor depends only on `R ∩ Bᵢ`, the second only on `R \ Bᵢ`
      have hP : ∀ R : Finset α, (¬ Disjoint R (B i)) ↔ (¬ Disjoint (R ∩ B i) (B i)) := by
        intro R
        constructor
        · intro h hc
          refine h ?_
          rw [Finset.disjoint_iff_inter_eq_empty] at hc ⊢
          rw [Finset.inter_assoc, Finset.inter_self] at hc
          exact hc
        · intro h hc
          refine h ?_
          rw [Finset.disjoint_iff_inter_eq_empty] at hc ⊢
          rw [Finset.inter_assoc, Finset.inter_self]
          exact hc
      have hQ : ∀ R : Finset α, (∀ j ∈ I, ¬ Disjoint R (B j))
          ↔ (∀ j ∈ I, ¬ Disjoint (R \ B i) (B j)) := by
        intro R
        constructor
        · intro h j hj hc
          refine h j hj ?_
          -- `R ∩ B j = (R \ Bᵢ) ∩ B j` since `B j` is disjoint from `Bᵢ`
          have hij : Disjoint (B i) (B j) :=
            hdisj i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
            (by rintro rfl; exact hi hj)
          rw [Finset.disjoint_left] at hc ⊢
          intro x hxR hxj
          refine hc (Finset.mem_sdiff.mpr ⟨hxR, ?_⟩) hxj
          exact fun hxi => (Finset.disjoint_left.mp hij hxi) hxj
        · intro h j hj hc
          refine h j hj ?_
          exact Finset.disjoint_of_subset_left (Finset.sdiff_subset) hc
      rw [hsplit, pBiased_and_of_indep hiX hP hQ, pBiased_not_disjoint hiX p,
        ih hsub' hdisj', Finset.prod_insert hi]

end Sunflower

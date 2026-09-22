/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HappyEvents

/-!
# Definition 5.18's partitions exist when the cut's edges are small

`DegreePartition x ε₁ εη u` (in `TSPGap/HappyEvents.lean`) asks for `δ(u)` to
split into `A ⊎ B ⊎ C` with `x(A), x(B) ∈ [1 − ε₁, 1 + ε_η]` and
`x(C) ≤ 2ε₁ + ε_η`.  KKO obtain it by splitting an edge into parallel copies
"WLOG"; `Sym2 (Fin n)` is a **simple**-edge model with no such splitting, and
that is a real obstruction rather than a bookkeeping one:

> A cut with incident weights `{0.6, 0.6, 0.6, 0.2}` has total exactly `2`, but
> its subset sums are `{0, 0.2, 0.6, 0.8, 1.2, 1.4, 1.8, 2}` — none within
> `[1 − ε₁, 1 + ε_η]` at the intended constants.  Those marginals are LP
> feasible: average Hamilton cycles whose two neighbours of the distinguished
> vertex are `{a,b}, {a,c}, {b,c}, {a,d}` with probabilities
> `0.2, 0.2, 0.4, 0.2`.

So no theorem derives `DegreePartition` from subtour feasibility and
near-minimality alone.  What *does* follow, and is proved here, is that one
explicit hypothesis removes the obstruction at a single cut: **every edge of
`δ(u)` carries at most `ε₁`** (`SmallCutEdges`).  Greedy accumulation then
cannot overshoot, and `exists_degreePartition_of_small` builds the partition.

⚠️ **This does not bridge Definition 5.18, and the price is quantified here.**
`smallCutEdges_two_le_card_mul` shows the hypothesis forces `2 ≤ |δ(S)|·ε₁` at
every cut — at the intended `ε₁ = ε₂/12 = 1/60000` that is **120000 edges in
every cut of the hierarchy**, hence `n ≥ 693` from `|δ(S)| ≤ n²/4` alone.  It is
worse at the mandatory root: `H.root_mem` puts `V ∖ {u₀,v₀}` in `H.cuts`, and
`δ` of it is `δ({u₀,v₀})`, which has at most `2(n-2)` edges while carrying
exactly `2` — so `n ≥ 2 + 1/ε₁ = 60002`, and at `n = 3` the root has two edges
and the hypothesis is outright contradictory.

So `SmallCutEdges` at *every* cut is not a weak side condition awaiting proof;
it is a strong structural restriction the development's instances need not meet.
KKO are explicit that Definition 5.18's existence comes from splitting an edge
into parallel copies (KKO21, 2007.01409v6 lines 3159-3161), **not** from the
original edges being small.  The genuine repair is therefore an indexed
parallel-edge refinement, with `DegreePartition` and this construction
generalized to that edge type; what is proved here is the post-refinement half,
plus an exact statement of what the un-refined model would have to satisfy.

## Main results

* `exists_subset_sum_mem_Icc` — greedy packing: if no weight exceeds `δ` and the
  total reaches the target `t`, some subset has weight in `[t, t + δ]`.
* `exists_degreePartition_of_small` — Definition 5.18's partition at one cut.
* `smallCutEdges_two_le_card_mul` — the price: `2 ≤ |δ(S)|·ε₁` at every cut.
* `exists_degreePartitions_of_small` — the family, over a hierarchy's cuts;
  conditional on a hypothesis the previous item shows to be severe.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Greedy packing -/

/-- **Greedy packing.**  If every weight of `s` is at most `δ` and the total
reaches the target `t ≥ 0`, then some subset has weight in `[t, t + δ]`.

Adding elements one at a time moves the running total up by at most `δ`, so the
first prefix to reach `t` cannot have passed `t + δ`.  This is the whole content
of "no splitting is needed once the pieces are small". -/
theorem exists_subset_sum_mem_Icc {α : Type*} [DecidableEq α] {w : α → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) :
    ∀ s : Finset α, (∀ a ∈ s, 0 ≤ w a) → (∀ a ∈ s, w a ≤ δ) →
      ∀ t : ℝ, 0 ≤ t → t ≤ ∑ a ∈ s, w a →
        ∃ A ⊆ s, t ≤ ∑ a ∈ A, w a ∧ ∑ a ∈ A, w a ≤ t + δ := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ t ht0 hts
      rw [Finset.sum_empty] at hts
      exact ⟨∅, Finset.Subset.refl _, by rw [Finset.sum_empty]; linarith,
        by rw [Finset.sum_empty]; linarith⟩
  | insert a s ha ih =>
      intro hw hδ t ht0 hts
      by_cases hcase : t ≤ w a
      · -- one element already carries the target
        refine ⟨{a}, Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a s), ?_, ?_⟩
        · rw [Finset.sum_singleton]; exact hcase
        · rw [Finset.sum_singleton]
          have := hδ a (Finset.mem_insert_self a s)
          linarith
      · -- otherwise take `a` and pack the rest to the reduced target
        push_neg at hcase
        have hmem : ∀ b ∈ s, b ∈ insert a s := fun b hb => Finset.mem_insert_of_mem hb
        have hsum : t - w a ≤ ∑ b ∈ s, w b := by
          rw [Finset.sum_insert ha] at hts; linarith
        obtain ⟨A, hAs, hA1, hA2⟩ :=
          ih (fun b hb => hw b (hmem b hb)) (fun b hb => hδ b (hmem b hb))
            (t - w a) (by linarith) hsum
        have haA : a ∉ A := fun h => ha (hAs h)
        refine ⟨insert a A, Finset.insert_subset_insert _ hAs, ?_, ?_⟩
        · rw [Finset.sum_insert haA]; linarith
        · rw [Finset.sum_insert haA]; linarith

/-! ### The small-edge hypothesis -/

/-- **Every edge of `δ(u)` carries at most `ε₁`.**

This is the hypothesis that removes Definition 5.18's parallel-copy WLOG.  It is
a genuine restriction — the `{0.6, 0.6, 0.6, 0.2}` cut above violates it, and no
partition exists there — and it is the precise thing a refinement layer would
have to supply. -/
def SmallCutEdges (x : Sym2 (Fin n) → ℝ) (ε₁ : ℝ) (u : Finset (Fin n)) : Prop :=
  ∀ e ∈ cutEdges u, x e ≤ ε₁

/-- **What `SmallCutEdges` costs.**  A cut carrying `x(δ(S)) ≥ 2` out of edges
of size at most `ε₁` must have at least `2/ε₁` of them.

This is the quantitative reason the hypothesis does not extend to a whole
hierarchy: at the intended `ε₁ = 1/60000` it demands `120000` edges in *every*
cut, and `|δ(S)| ≤ n²/4` then forces `n ≥ 693`.  At the hierarchy root it is
sharper still — `δ(V ∖ {u₀,v₀}) = δ({u₀,v₀})` has at most `2(n-2)` edges and
carries exactly `2`, so `n ≥ 2 + 1/ε₁`; for `n = 3` the root has two edges and
the hypothesis is contradictory outright. -/
theorem smallCutEdges_two_le_card_mul (hx : x ∈ subtourLP n) {S : Finset (Fin n)}
    (hSne : S.Nonempty) (hSuniv : S ≠ Finset.univ) {ε₁ : ℝ}
    (h : SmallCutEdges x ε₁ S) :
    2 ≤ ((cutEdges S).card : ℝ) * ε₁ := by
  have hlow : 2 ≤ cutSum x S := hx.2.2 S hSne hSuniv
  have hub : cutSum x S ≤ ((cutEdges S).card : ℝ) * ε₁ := by
    have := Finset.sum_le_sum (f := x) (g := fun _ => ε₁) h
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  linarith

/-! ### Existence at one cut -/

/-- **Definition 5.18's partition exists at a cut with small edges.**

Greedy-pack `A` to `1 − ε₁`; it stops at most `ε₁` past, so `x(A) ≤ 1`.  At least
`1` of the cut is left, so pack `B` the same way.  What remains is
`x(δ(u)) − x(A) − x(B) ≤ (2 + ε_η) − 2(1 − ε₁) = 2ε₁ + ε_η`, which is exactly
the budget `C` is allowed.

The two `x(·) ≤ 1 + ε_η` clauses come out with room to spare: greedy overshoot
is bounded by the largest edge, so the small-edge hypothesis alone caps `A` and
`B` at `1`. -/
theorem exists_degreePartition_of_small {u : Finset (Fin n)} (hx0 : ∀ e, 0 ≤ x e)
    (hlow : 2 ≤ cutSum x u)
    {ε₁ εη : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη)
    (hucut : cutSum x u ≤ 2 + εη) (hsmall : SmallCutEdges x ε₁ u) :
    Nonempty (DegreePartition x ε₁ εη u) := by
  classical
  have hcs : ∑ e ∈ cutEdges u, x e = cutSum x u := rfl
  -- `A`: greedy to `1 − ε₁`, so `1 − ε₁ ≤ x(A) ≤ 1`
  obtain ⟨A, hAsub, hA1, hA2⟩ :=
    exists_subset_sum_mem_Icc (w := x) (δ := ε₁) hε₁0 (cutEdges u)
      (fun e _ => hx0 e) (fun e he => hsmall e he) (1 - ε₁) (by linarith)
      (by rw [hcs]; linarith)
  have hA2' : ∑ e ∈ A, x e ≤ 1 := by linarith
  -- what `A` leaves still carries at least `1`
  have hsplitA : ∑ e ∈ cutEdges u \ A, x e = cutSum x u - ∑ e ∈ A, x e := by
    have h := Finset.sum_sdiff (f := x) hAsub
    rw [hcs] at h; linarith
  have hrest : 1 ≤ ∑ e ∈ cutEdges u \ A, x e := by rw [hsplitA]; linarith
  -- `B`: greedy to `1 − ε₁` inside the remainder
  obtain ⟨B, hBsub, hB1, hB2⟩ :=
    exists_subset_sum_mem_Icc (w := x) (δ := ε₁) hε₁0 (cutEdges u \ A)
      (fun e _ => hx0 e) (fun e he => hsmall e (Finset.mem_sdiff.mp he).1)
      (1 - ε₁) (by linarith) (by linarith)
  have hB2' : ∑ e ∈ B, x e ≤ 1 := by linarith
  -- `C` is what is left, and its budget is what the two overshoots cost
  have hsplitB : ∑ e ∈ (cutEdges u \ A) \ B, x e
      = (∑ e ∈ cutEdges u \ A, x e) - ∑ e ∈ B, x e := by
    have h := Finset.sum_sdiff (f := x) hBsub; linarith
  refine ⟨{ A := A, B := B, C := (cutEdges u \ A) \ B, part := ?_,
            disjAB := ?_, disjAC := ?_, disjBC := ?_,
            xA1 := hA1, xA2 := by linarith, xB1 := hB1, xB2 := by linarith,
            xC := ?_ }⟩
  · -- `A ∪ B ∪ C = δ(u)`
    have hBu : B ⊆ cutEdges u := hBsub.trans (Finset.sdiff_subset)
    apply Finset.Subset.antisymm
    · intro e he
      by_cases hA : e ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hA)
      · by_cases hB : e ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hB)
        · exact Finset.mem_union_right _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨he, hA⟩, hB⟩)
    · intro e he
      rcases Finset.mem_union.mp he with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact hAsub h
        · exact hBu h
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
  · exact Finset.disjoint_left.mpr fun e heA heB =>
      (Finset.mem_sdiff.mp (hBsub heB)).2 heA
  · exact Finset.disjoint_left.mpr fun e heA heC =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heC).1).2 heA
  · exact Finset.disjoint_left.mpr fun e heB heC =>
      (Finset.mem_sdiff.mp heC).2 heB
  · rw [hsplitB, hsplitA]; linarith

/-! ### The family over a hierarchy -/

/-- **The family of Definition 5.18 partitions**, when every cut of the
hierarchy has small edges.

`DegreePartitions` is indexed by `H.cuts`, and each cut is a near-minimum cut of
`x`, so `Nonempty`, `≠ univ` and `x(δ(·)) ≤ 2 + ε_η` all come from `H.nearMin`.

⚠️ **The hypothesis is severe, and at small `n` it is contradictory.**  By
`smallCutEdges_two_le_card_mul` it forces `2 ≤ |δ(U)|·ε₁` at every cut of `H`,
so at the intended `ε₁ = 1/60000` every cut needs `120000` edges.  `H.root_mem`
makes `V ∖ {u₀,v₀}` a cut, and `δ` of it has at most `2(n-2)` edges carrying
exactly `2`, so the premise entails `n ≥ 2 + 1/ε₁ = 60002`; at `n = 3` the root
has two edges and no `x` satisfies it at all.

This theorem is therefore **not** a route to Definition 5.18 in the simple-edge
model — do not read it as one lemma away from discharging
`DegreePartitions`.  It is the post-refinement half: once an indexed
parallel-edge layer exists, its pieces *are* small by construction, and this is
what turns that into the family.  KKO21 lines 3159-3161 obtain Definition 5.18
from exactly such splitting, never from the original edges being small. -/
theorem exists_degreePartitions_of_small {e₀ : RootEdge n} {εη ε₁ : ℝ}
    (H : Hierarchy x e₀ εη) (hx : IsRestrictedLP e₀ x)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη)
    (hsmall : ∀ U ∈ H.cuts, SmallCutEdges x ε₁ U) :
    Nonempty (DegreePartitions H ε₁) := by
  classical
  refine ⟨⟨fun U hU => ?_⟩⟩
  have hnm := H.nearMin U hU
  exact (exists_degreePartition_of_small hx.nonneg (H.two_le_cutSum hx hU) hε₁0 hε₁1 hεη0
    hnm.cut_le (hsmall U hU)).some

end TSPGap

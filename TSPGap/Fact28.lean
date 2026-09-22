/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MaxEntropyLimit

/-!
# Fact 2.8 at the max-entropy limit

KKO21 Fact 2.8: conditioned on the edges inside a vertex set `S` forming a
spanning tree of `S`, the induced tree on `S` and the tree on the contracted
graph `G/S` are independent.  This file carries that statement to the
max-entropy limit.

## Why the identity is cross-multiplied

Conditional probabilities are not continuous where the conditioning event has
probability zero, so `P(A ∣ C)` is not something `LimitClosed` can carry.  The
statement transported is therefore

`P(A ∩ B ∩ C) · P(C) = P(A ∩ C) · P(B ∩ C)`,

polynomial in the probability vector and so covered by `limitClosed_eq`.
`condIndep_of_cross` converts it back to the conditional form — under the
separate hypothesis `0 < P(C)`, which is **strict and deliberately not carried
through the limit**.  Positivity has to be re-established afterwards, from the
application's own probability bound, and only then may one divide.

## What travels in the property, and what does not

The refinement of `StableLimit.lean`'s lesson.  An invariant the closure argument
consumes must be in `P`; but `P` must also remain *true* at the boundary faces,
which rules out anything strict.  Closed support conditions may perfectly well
travel in `P` — `FixedRankNormalized` does — they are simply not consumed here.
**Strict positivity is the thing that must stay outside.**  The conditioning event `InducesTreeOn S` is fixed combinatorial data,
independent of the weight vector, and so are the two "determined by the inside /
outside part" side conditions on the events.  What has to travel is the whole
universally quantified identity `∀ S A B, … → CondIndepCross …`; the quantifiers
are **inside** `P`, and `limitClosed_imp` lets the side conditions ride along
without themselves being closed.

## The finite-graph content

Everything reduces to **rectangularity** (`InducesTreeOn.glue`): if two spanning
trees each induce a tree on `S`, then gluing the inside part of one to the
outside part of the other is again a spanning tree inducing a tree on `S`.  The
map `(T₁, T₂) ↦ (in₁ ∪ out₂, in₂ ∪ out₁)` is then an involution of pairs that
exchanges the two index sets of the identity, and λ-weights, being products over
edges, are preserved because the two glued trees carry the same edges as the two
original ones.

Original edge labels are kept throughout, which is what avoids having to
formalize the contracted multigraph `G/S`.

## Two semantic seams

**`TreeCondIndep` formalizes the conditional-independence *content* of Fact 2.8,
not a typed equality with separately constructed distributions on `G[S]` and
`G/S`.**  That is deliberate, and it is precisely the content needed at the
boundary: the paper's factorization statement presupposes two well-defined
conditional laws, which is exactly what fails when `P(C) = 0`.

**"No side hypotheses" on `IsMaxEntropyLimit.treeCondIndep` means no positivity
and no restriction on `S`.**  Applications still have to supply
`InsideDetermined` and `OutsideDetermined` for their own events; those are
combinatorial obligations, not probabilistic ones.

A convenience lemma identifying `InducesTreeOn S` with the paper's usual
internal-edge-count event on supported spanning trees is still wanted: it would
connect the existing probability bounds to the positivity hypothesis of
`condIndep_of_cross` without restating connectivity.

## Main results

* `CondIndepCross`, `limitClosed_condIndepCross` — the identity and its closure.
* `condIndep_of_cross` — the bridge to the conditional form, given `0 < P(C)`.
* `InducesTreeOn.glue` — rectangularity.
* `treeCondIndep_of_lambdaUniform` — Fact 2.8 for λ-uniform distributions.
* `IsMaxEntropyLimit.treeCondIndep` — the export, with no side hypotheses.

This adapter depends on neither the BBL criterion nor the weighted matrix-tree
development.
-/

namespace TSPGap

open Finset

variable {n : ℕ}

/-! ### Raw event masses -/

open Classical in
/-- The mass a weight vector puts on a set of trees.  Deliberately **raw**: no
normalization and no division, so that it is a polynomial — indeed linear — in
the weight vector, hence continuous. -/
noncomputable def eventMass (f : Finset (Sym2 (Fin n)) → ℝ)
    (Q : Finset (Sym2 (Fin n)) → Prop) : ℝ :=
  ∑ T ∈ Finset.univ.filter Q, f T

theorem probEvent_eq_eventMass {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)
    (Q : Finset (Sym2 (Fin n)) → Prop) : μ.probEvent Q = eventMass μ.prob Q := rfl

theorem continuous_eventMass (Q : Finset (Sym2 (Fin n)) → Prop) :
    Continuous fun f : Finset (Sym2 (Fin n)) → ℝ => eventMass f Q :=
  continuous_probEventSum Q

/-- A product of two event masses, as a single sum over pairs.  This is the
shape the involution acts on. -/
theorem eventMass_mul_eventMass (f : Finset (Sym2 (Fin n)) → ℝ)
    (P Q : Finset (Sym2 (Fin n)) → Prop) [DecidablePred P] [DecidablePred Q] :
    eventMass f P * eventMass f Q
      = ∑ p ∈ (Finset.univ.filter P) ×ˢ (Finset.univ.filter Q), f p.1 * f p.2 := by
  classical
  rw [eventMass, eventMass, Finset.sum_mul_sum, Finset.sum_product]
  exact Finset.sum_congr (by congr 1) fun _ _ => Finset.sum_congr (by congr 1) fun _ _ => rfl

/-! ### The cross-multiplied identity -/

/-- **Conditional independence, cross-multiplied.**

`P(A ∩ B ∩ C) · P(C) = P(A ∩ C) · P(B ∩ C)` — equivalent to
`P(A ∩ B ∣ C) = P(A ∣ C) · P(B ∣ C)` when `P(C) > 0`, and unlike it, a
polynomial identity in the weight vector. -/
def CondIndepCross (f : Finset (Sym2 (Fin n)) → ℝ)
    (A B C : Finset (Sym2 (Fin n)) → Prop) : Prop :=
  eventMass f (fun T => A T ∧ B T ∧ C T) * eventMass f C
    = eventMass f (fun T => A T ∧ C T) * eventMass f (fun T => B T ∧ C T)

theorem limitClosed_condIndepCross (A B C : Finset (Sym2 (Fin n)) → Prop) :
    LimitClosed fun f => CondIndepCross f A B C :=
  limitClosed_eq ((continuous_eventMass _).mul (continuous_eventMass _))
    ((continuous_eventMass _).mul (continuous_eventMass _))

/-- **The bridge back to ordinary conditional independence.**

⚠️ The hypothesis `0 < eventMass f C` is strict, hence *not* limit-closed, and
is deliberately not part of anything transported above.  It has to be supplied
after the limit, from the application's own lower bound on `P(C)`. -/
theorem condIndep_of_cross {f : Finset (Sym2 (Fin n)) → ℝ}
    {A B C : Finset (Sym2 (Fin n)) → Prop} (h : CondIndepCross f A B C)
    (hC : 0 < eventMass f C) :
    eventMass f (fun T => A T ∧ B T ∧ C T) / eventMass f C
      = eventMass f (fun T => A T ∧ C T) / eventMass f C
        * (eventMass f (fun T => B T ∧ C T) / eventMass f C) := by
  have hne : eventMass f C ≠ 0 := ne_of_gt hC
  unfold CondIndepCross at h
  field_simp
  linarith

/-! ### Inside and outside parts

Original edge labels are kept: the "outside" part is literally the rest of the
edge set, not a multigraph on contracted vertices. -/

open Classical in
/-- The edges of `T` with both endpoints in `S`. -/
noncomputable def insidePart (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) := T.filter fun e => ∀ v ∈ e, v ∈ S

open Classical in
/-- The edges of `T` with an endpoint outside `S`. -/
noncomputable def outsidePart (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) := T.filter fun e => ¬ ∀ v ∈ e, v ∈ S

variable {S : Finset (Fin n)} {T T₁ T₂ : Finset (Sym2 (Fin n))}

theorem mem_insidePart {e : Sym2 (Fin n)} :
    e ∈ insidePart S T ↔ e ∈ T ∧ ∀ v ∈ e, v ∈ S := by
  classical simp [insidePart]

theorem mem_outsidePart {e : Sym2 (Fin n)} :
    e ∈ outsidePart S T ↔ e ∈ T ∧ ¬ ∀ v ∈ e, v ∈ S := by
  classical simp [outsidePart]

theorem insidePart_subset (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    insidePart S T ⊆ T := fun _ he => (mem_insidePart.mp he).1

theorem outsidePart_subset (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    outsidePart S T ⊆ T := fun _ he => (mem_outsidePart.mp he).1

/-- Inside parts and outside parts are disjoint **even across different
trees** — the two are cut out by complementary conditions on the edge alone.
This is what makes the glued sets behave like a rectangle. -/
theorem disjoint_inside_outside (S : Finset (Fin n)) (T₁ T₂ : Finset (Sym2 (Fin n))) :
    Disjoint (insidePart S T₁) (outsidePart S T₂) := by
  rw [Finset.disjoint_left]
  exact fun e h1 h2 => (mem_outsidePart.mp h2).2 (mem_insidePart.mp h1).2

theorem union_parts (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    insidePart S T ∪ outsidePart S T = T := by
  ext e
  simp only [Finset.mem_union, mem_insidePart, mem_outsidePart]
  tauto

theorem insidePart_glue (S : Finset (Fin n)) (T₁ T₂ : Finset (Sym2 (Fin n))) :
    insidePart S (insidePart S T₁ ∪ outsidePart S T₂) = insidePart S T₁ := by
  ext e
  simp only [mem_insidePart, mem_outsidePart, Finset.mem_union]
  tauto

theorem outsidePart_glue (S : Finset (Fin n)) (T₁ T₂ : Finset (Sym2 (Fin n))) :
    outsidePart S (insidePart S T₁ ∪ outsidePart S T₂) = outsidePart S T₂ := by
  ext e
  simp only [mem_insidePart, mem_outsidePart, Finset.mem_union]
  tauto

/-- Gluing is an **involution on pairs**: applying it twice returns the pair,
because the inside part of the first glued tree is the first tree's inside part
and the outside part of the second glued tree is the first tree's outside
part. -/
theorem glue_involutive (S : Finset (Fin n)) (T₁ T₂ : Finset (Sym2 (Fin n))) :
    insidePart S (insidePart S T₁ ∪ outsidePart S T₂)
        ∪ outsidePart S (insidePart S T₂ ∪ outsidePart S T₁) = T₁ := by
  rw [insidePart_glue, outsidePart_glue, union_parts]

/-! ### Inducing a tree on `S` -/

/-- `T` **induces a tree on `S`**: its edges inside `S` connect `S` and number
`|S| − 1`.

Stated as `card + 1 = S.card` rather than `card = S.card - 1` to keep truncated
subtraction out of it.  A side effect is that `InducesTree ∅ T` is false; that
is harmless, since the identity below then reads `0 = 0`. -/
def InducesTree (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  (insidePart S T).card + 1 = S.card ∧
    ∀ u ∈ S, ∀ v ∈ S,
      (SimpleGraph.fromEdgeSet (↑(insidePart S T) : Set (Sym2 (Fin n)))).Reachable u v

/-- The conditioning event of Fact 2.8: a spanning tree whose edges inside `S`
form a spanning tree of `S`. -/
def InducesTreeOn (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  IsSpanningTree n T ∧ InducesTree S T

/-- **Rectangularity** — the finite-graph content of Fact 2.8.

If `T₁` and `T₂` are spanning trees each inducing a tree on `S`, then
`in₁ ∪ out₂` is again one.

*Cardinality* is free: the two inside parts have the same size, `|S| − 1`, so
`|in₁| + |out₂| = |in₂| + |out₂| = |T₂|`, with no subtraction anywhere.

*Connectivity* is the real step.  Every edge of `T₂` is joined in `in₁ ∪ out₂`:
an outside edge is there outright, and an inside edge has both endpoints in `S`,
which `in₁` connects.  Walk induction promotes that from edges to reachability,
and `T₂` is connected. -/
theorem InducesTreeOn.glue (h₁ : InducesTreeOn S T₁) (h₂ : InducesTreeOn S T₂) :
    InducesTreeOn S (insidePart S T₁ ∪ outsidePart S T₂) := by
  obtain ⟨⟨hd₁, _, _⟩, hcard₁, hreach₁⟩ := h₁
  obtain ⟨⟨hd₂, hc₂, hcon₂⟩, hcard₂, _⟩ := h₂
  have hin : insidePart S (insidePart S T₁ ∪ outsidePart S T₂) = insidePart S T₁ :=
    insidePart_glue S T₁ T₂
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- no loops
    intro e he
    rw [Finset.mem_union] at he
    rcases he with h | h
    · exact hd₁ e (insidePart_subset _ _ h)
    · exact hd₂ e (outsidePart_subset _ _ h)
  · -- `n − 1` edges
    rw [Finset.card_union_of_disjoint (disjoint_inside_outside S T₁ T₂)]
    have hii : (insidePart S T₁).card = (insidePart S T₂).card := by omega
    rw [hii, ← Finset.card_union_of_disjoint (disjoint_inside_outside S T₂ T₂),
      union_parts]
    exact hc₂
  · -- connected
    have hmono : SimpleGraph.fromEdgeSet (↑(insidePart S T₁) : Set (Sym2 (Fin n))) ≤
        SimpleGraph.fromEdgeSet
          (↑(insidePart S T₁ ∪ outsidePart S T₂) : Set (Sym2 (Fin n))) := by
      refine SimpleGraph.fromEdgeSet_mono ?_
      exact_mod_cast (Finset.subset_union_left :
        insidePart S T₁ ⊆ insidePart S T₁ ∪ outsidePart S T₂)
    have hstep : ∀ u v, (SimpleGraph.fromEdgeSet (↑T₂ : Set (Sym2 (Fin n)))).Adj u v →
        (SimpleGraph.fromEdgeSet
          (↑(insidePart S T₁ ∪ outsidePart S T₂) : Set (Sym2 (Fin n)))).Reachable u v := by
      intro u v hadj
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      obtain ⟨hmem, hne⟩ := hadj
      rw [Finset.mem_coe] at hmem
      by_cases hpred : ∀ w ∈ (s(u, v) : Sym2 (Fin n)), w ∈ S
      · -- an inside edge: route through the tree `T₁` induces on `S`
        exact (hreach₁ u (hpred u (by simp)) v (hpred v (by simp))).mono hmono
      · -- an outside edge: it is in the glued set outright
        refine SimpleGraph.Adj.reachable ?_
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, hne⟩
        rw [Finset.mem_coe, Finset.mem_union]
        exact Or.inr (mem_outsidePart.mpr ⟨hmem, hpred⟩)
    have hwalk : ∀ u v, ∀ _ : (SimpleGraph.fromEdgeSet (↑T₂ : Set (Sym2 (Fin n)))).Walk u v,
        (SimpleGraph.fromEdgeSet
          (↑(insidePart S T₁ ∪ outsidePart S T₂) : Set (Sym2 (Fin n)))).Reachable u v := by
      intro u v w
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih => exact (hstep _ _ hadj).trans ih
    haveI : Nonempty (Fin n) := hcon₂.nonempty
    exact ⟨fun u v => (hcon₂.preconnected u v).elim (hwalk u v)⟩
  · rw [hin]; exact hcard₁
  · rw [hin]; exact hreach₁

/-! ### The property that travels -/

/-- An event **determined by the edges inside `S`**. -/
def InsideDetermined (S : Finset (Fin n)) (A : Finset (Sym2 (Fin n)) → Prop) : Prop :=
  ∀ T T', insidePart S T = insidePart S T' → (A T ↔ A T')

/-- An event **determined by the edges outside `S`** — the events of the
contracted graph, without contracting anything. -/
def OutsideDetermined (S : Finset (Fin n)) (B : Finset (Sym2 (Fin n)) → Prop) : Prop :=
  ∀ T T', outsidePart S T = outsidePart S T' → (B T ↔ B T')

/-- **Fact 2.8 as a closed property of the weight vector.**

The quantifiers over `S`, `A`, `B` and the two side conditions are *inside* the
property: they are fixed combinatorial data, and only the identity itself has to
survive the limit. -/
def TreeCondIndep (f : Finset (Sym2 (Fin n)) → ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (A B : Finset (Sym2 (Fin n)) → Prop),
    InsideDetermined S A → OutsideDetermined S B →
      CondIndepCross f A B (InducesTreeOn S)

theorem limitClosed_treeCondIndep : LimitClosed (TreeCondIndep (n := n)) := by
  show LimitClosed fun f => ∀ S A B, InsideDetermined S A → OutsideDetermined S B →
    CondIndepCross f A B (InducesTreeOn S)
  refine limitClosed_forall fun S => limitClosed_forall fun A =>
    limitClosed_forall fun B => ?_
  exact limitClosed_imp (limitClosed_imp (limitClosed_condIndepCross A B (InducesTreeOn S)))

/-! ### Fact 2.8 for λ-uniform distributions -/

/-- **Fact 2.8, λ-uniform case.**

The involution `(T₁, T₂) ↦ (in₁ ∪ out₂, in₂ ∪ out₁)` carries the pairs indexing
the left-hand side onto those indexing the right: rectangularity keeps both
components in the conditioning event, `A` sees only the inside part and `B` only
the outside part, and the λ-weight is preserved because the glued pair uses
exactly the edges of the original pair. -/
theorem treeCondIndep_of_lambdaUniform {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y)
    (hν : IsLambdaUniform ν) : TreeCondIndep ν.prob := by
  classical
  obtain ⟨lam, _, Z, _, hprob⟩ := hν
  intro S A B hA hB
  show eventMass ν.prob _ * eventMass ν.prob _ = eventMass ν.prob _ * eventMass ν.prob _
  rw [eventMass_mul_eventMass, eventMass_mul_eventMass]
  refine Finset.sum_nbij'
    (fun p => (insidePart S p.1 ∪ outsidePart S p.2, insidePart S p.2 ∪ outsidePart S p.1))
    (fun p => (insidePart S p.1 ∪ outsidePart S p.2, insidePart S p.2 ∪ outsidePart S p.1))
    ?_ ?_ ?_ ?_ ?_
  · -- forward: `(A ∧ B ∧ C, C) → (A ∧ C, B ∧ C)`
    rintro ⟨T₁, T₂⟩ hmem
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    obtain ⟨⟨hA₁, hB₁, hC₁⟩, hC₂⟩ := hmem
    exact ⟨⟨(hA T₁ _ (insidePart_glue S T₁ T₂).symm).mp hA₁, hC₁.glue hC₂⟩,
      (hB T₁ _ (outsidePart_glue S T₂ T₁).symm).mp hB₁, hC₂.glue hC₁⟩
  · -- backward: `(A ∧ C, B ∧ C) → (A ∧ B ∧ C, C)`
    rintro ⟨U₁, U₂⟩ hmem
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    obtain ⟨⟨hA₁, hC₁⟩, hB₂, hC₂⟩ := hmem
    exact ⟨⟨(hA U₁ _ (insidePart_glue S U₁ U₂).symm).mp hA₁,
      (hB U₂ _ (outsidePart_glue S U₁ U₂).symm).mp hB₂, hC₁.glue hC₂⟩, hC₂.glue hC₁⟩
  · rintro ⟨T₁, T₂⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨glue_involutive S T₁ T₂, glue_involutive S T₂ T₁⟩
  · rintro ⟨T₁, T₂⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨glue_involutive S T₁ T₂, glue_involutive S T₂ T₁⟩
  · -- the λ-weight is preserved: the glued pair carries the same edges
    rintro ⟨T₁, T₂⟩ hmem
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨⟨_, _, hC₁⟩, hC₂⟩ := hmem
    have hp : ∀ T : Finset (Sym2 (Fin n)),
        ∏ e ∈ T, lam e
          = (∏ e ∈ insidePart S T, lam e) * ∏ e ∈ outsidePart S T, lam e := by
      intro T
      rw [← Finset.prod_union (disjoint_inside_outside S T T), union_parts]
    have hg : ∀ V₁ V₂ : Finset (Sym2 (Fin n)),
        ∏ e ∈ insidePart S V₁ ∪ outsidePart S V₂, lam e
          = (∏ e ∈ insidePart S V₁, lam e) * ∏ e ∈ outsidePart S V₂, lam e :=
      fun V₁ V₂ => Finset.prod_union (disjoint_inside_outside S V₁ V₂)
    rw [hprob _ hC₁.1, hprob _ hC₂.1, hprob _ (hC₁.glue hC₂).1, hprob _ (hC₂.glue hC₁).1,
      hp T₁, hp T₂, hg, hg]
    ring

/-- **The export.**  Fact 2.8 holds at the max-entropy limit, with no side
hypotheses: the λ-uniform case is proved outright and the identity is closed. -/
theorem IsMaxEntropyLimit.treeCondIndep {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) : TreeCondIndep μ.prob :=
  h.holds limitClosed_treeCondIndep fun ν hν => treeCondIndep_of_lambdaUniform ν hν

/-- Fact 2.8 in conditional form at the limit, once positivity of the
conditioning event is available.  ⚠️ `hC` is an input, not something inherited
from the limit. -/
theorem IsMaxEntropyLimit.condIndep {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) (S : Finset (Fin n)) (A B : Finset (Sym2 (Fin n)) → Prop)
    (hA : InsideDetermined S A) (hB : OutsideDetermined S B)
    (hC : 0 < μ.probEvent (InducesTreeOn S)) :
    μ.probEvent (fun T => A T ∧ B T ∧ InducesTreeOn S T) / μ.probEvent (InducesTreeOn S)
      = μ.probEvent (fun T => A T ∧ InducesTreeOn S T) / μ.probEvent (InducesTreeOn S)
        * (μ.probEvent (fun T => B T ∧ InducesTreeOn S T)
            / μ.probEvent (InducesTreeOn S)) :=
  condIndep_of_cross (h.treeCondIndep S A B hA hB) hC

end TSPGap

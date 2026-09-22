import TSPGap.TreeDist
import TSPGap.InsideAtoms
import TSPGap.PolygonFamily

/-!
# KKO22 Theorem 5.2 — the main theorem

> **Theorem 5.2 (Main theorem).**  Let `x₀` be a feasible LP solution of (1)
> with support `E₀ = E ∪ {e₀}` and let `x` be `x₀` restricted to `E`.  For any
> distribution `μ` of spanning trees with marginals `x`, `0 < η ≤ 1/10` and
> `α > 0`, there is a random vector `s* : E → ℝ≥0` (the randomness in `s*`
> depends exclusively on `T ∼ μ`) such that
> * for any `η`-near minimum cut `S` which is crossed on both sides, if
>   `δ(S)_T` is odd then `s*(δ(S)) ≥ α(1 − η)`;
> * for any `e ∈ E`, `E[s*ₑ] ≤ 18αη xₑ`.

This file is the *assembly*: KKO's own "Proof of Theorem 5.2" derives the two
conclusions from three previously-established facts, and that derivation is
what is proved here, in full and axiom-clean.  The slack vector is the
paper's, defined explicitly in `slack`: initialize `s*` to zero, and for every
bad event `B` that occurs, set `s*ₑ = α xₑ` for each `e ∈ E(B)`.

The bad events are carried abstractly, as a finite family `Ebad : Fin k → …`
of edge sets together with an occurrence predicate.  The three inputs then
appear as the hypotheses `hsat`, `hdeg`, `hprob` of `exists_slack_vector`,
and each is exactly one already-formalized statement of §5:

| hypothesis | KKO22 source | status here |
| --- | --- | --- |
| `hsat` — an odd cut has an occurring bad event whose edges lie in `δ(S)` and carry `x`-mass `≥ 1 − η` | Lemma 5.3 (all cuts are satisfied), routed through Lemma 5.1 (`E(B←(p)) ⊆ E←(p) = E←(S)`) and Lemma 5.6 (the edge sets are heavy) | assembled for *concrete* events by `exists_occurring_badEvent_of_polygon` (`BadEvents.lean`), which discharges all six disjointness side conditions from the polygon (Lemma 4.27 at `S`, `L`, `R`, `L`-with-`R`, `R`-with-`L`, and Corollary 5.8).  What it still *takes* is other lemmas' output — `L ∩ R = S` and the two arrow equalities (Lemmas 5.7, 5.1), and Lemma 5.6's per-side data — so it is not yet instantiated at a polygon point |
| `hdeg` — each edge lies in `E(B)` for at most four bad events | Lemma 5.4 plus Fact 4.9 | **Fact 4.9 proved**; **Lemma 5.4 assembled, both directions** (see `NOTES/kko-lemma-5.4.md`), and the `2 + 2` step is `card_badEvents_le_four_of_polygon` (`BadCount.lean`), which discharges `hlocal` once the bad-event index provides at most one event per (anchor point, direction) |
| `hprob` — each bad event has probability `≤ 4.5η` | Lemma 5.5 | proved, in `BadEvents.lean`, modulo KKO22 Cor 2.12 (a hypothesis, as in KKO) |

So the table above records *provenance*, not a finished dependency graph:
`exists_slack_vector` and `exists_slack_vector_of_family` are proved and
axiom-clean, but their bad-event inputs are still hypotheses rather than
constructions.  Closing that is Milestone 2 of `FORMALIZATION_PLAN.md`.

`hdeg` is the one place where KKO's argument leaves a single polygon.  Their
count of four is `2 + 2`: at most two polygon points `p` with `e ∈ E(B→(p))`
and at most two with `e ∈ E(B←(p))` — that part is Lemma 5.4 — times the fact
that there is at most *one polygon* in which `e` can contribute at all, which
is Fact 4.9 and quantifies over the whole family of polygons indexed by the
crossing components.  Fact 4.9 is available (`PolygonFamily.lean`), so
`exists_slack_vector_of_family` at the end of this file states Theorem 5.2
with `hdeg` replaced by the two *per-polygon* facts that produce it.
-/

namespace TSPGap

open Finset

variable {n k : ℕ} {x : Sym2 (Fin n) → ℝ} {α η : ℝ}

open Classical in
/-- **KKO22's slack vector `s*`**, from the proof of Theorem 5.2: start at
zero, and whenever a bad event `b` occurs, raise `s*ₑ` to `α xₑ` on every
edge of `E(b)`.  The randomness enters only through the tree `T`. -/
noncomputable def slack (α : ℝ) (x : Sym2 (Fin n) → ℝ)
    (Ebad : Fin k → Finset (Sym2 (Fin n)))
    (occurs : Fin k → Finset (Sym2 (Fin n)) → Prop)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  if ∃ b, occurs b T ∧ e ∈ Ebad b then α * x e else 0

open Classical in
theorem slack_nonneg {Ebad : Fin k → Finset (Sym2 (Fin n))}
    {occurs : Fin k → Finset (Sym2 (Fin n)) → Prop}
    (hα : 0 ≤ α) (hx : ∀ e, 0 ≤ x e) (T : Finset (Sym2 (Fin n)))
    (e : Sym2 (Fin n)) : 0 ≤ slack α x Ebad occurs T e := by
  rw [slack]
  split
  · exact mul_nonneg hα (hx e)
  · exact le_rfl

open Classical in
/-- **Theorem 5.2, first conclusion.**  If some bad event occurs whose edge
set lies inside `δ(S)` and carries `x`-mass at least `1 − η`, then the slack
vector already pays `α(1 − η)` across that cut.

This is the paper's one-line argument: on `E(b)` the slack is exactly `α xₑ`,
so `s*(δ(S)) ≥ s*(E(b)) = α · x(E(b)) ≥ α(1 − η)`, the first inequality
because slack is nonnegative and `E(b) ⊆ δ(S)`. -/
theorem le_slack_cutSum {Ebad : Fin k → Finset (Sym2 (Fin n))}
    {occurs : Fin k → Finset (Sym2 (Fin n)) → Prop}
    (hα : 0 ≤ α) (hx : ∀ e, 0 ≤ x e)
    {S : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hb : ∃ b, occurs b T ∧ Ebad b ⊆ cutEdges S ∧ 1 - η ≤ ∑ e ∈ Ebad b, x e) :
    α * (1 - η) ≤ ∑ e ∈ cutEdges S, slack α x Ebad occurs T e := by
  obtain ⟨b, hocc, hsub, hmass⟩ := hb
  have key : ∑ e ∈ Ebad b, slack α x Ebad occurs T e = ∑ e ∈ Ebad b, α * x e := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [slack, if_pos ⟨b, hocc, he⟩]
  calc α * (1 - η) ≤ α * ∑ e ∈ Ebad b, x e := mul_le_mul_of_nonneg_left hmass hα
    _ = ∑ e ∈ Ebad b, α * x e := by rw [Finset.mul_sum]
    _ = ∑ e ∈ Ebad b, slack α x Ebad occurs T e := key.symm
    _ ≤ ∑ e ∈ cutEdges S, slack α x Ebad occurs T e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun e _ _ => slack_nonneg hα hx T e)

open Classical in
/-- **Theorem 5.2, second conclusion.**  If each edge is touched by at most
four bad events and each bad event has probability at most `4.5η`, then
`E[s*ₑ] ≤ 18αηxₑ`.

The slack at `e` is the scaled indicator of "some bad event touching `e`
occurs", so its expectation is `α xₑ` times that probability; the union bound
over the at most four relevant events gives `4 · 4.5η = 18η`. -/
theorem expect_slack_le (μ : TreeDist n x) {Ebad : Fin k → Finset (Sym2 (Fin n))}
    {occurs : Fin k → Finset (Sym2 (Fin n)) → Prop}
    (hα : 0 ≤ α) (hη : 0 ≤ η) (hx : ∀ e, 0 ≤ x e) (e : Sym2 (Fin n))
    (hdeg : ((Finset.univ.filter fun b => e ∈ Ebad b).card : ℝ) ≤ 4)
    (hprob : ∀ b, μ.probEvent (occurs b) ≤ 4.5 * η) :
    μ.expect (fun T => slack α x Ebad occurs T e) ≤ 18 * α * η * x e := by
  have hev : (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b)
      = (fun T => ∃ b ∈ Finset.univ.filter fun b => e ∈ Ebad b, occurs b T) := by
    funext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact propext ⟨fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩, fun ⟨b, h2, h1⟩ => ⟨b, h1, h2⟩⟩
  have hexp : μ.expect (fun T => slack α x Ebad occurs T e)
      = (α * x e) * μ.probEvent (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b) := by
    -- proved directly rather than via `expect_indicator`: unfolding `slack`
    -- re-elaborates `∃ b : Fin k` with `Nat.decidableExistsFin`, which will
    -- not unify with that lemma's `Classical.propDecidable`
    rw [TreeDist.expect, TreeDist.probEvent_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : ∃ b, occurs b T ∧ e ∈ Ebad b <;> simp [slack, h, mul_comm]
  have h45 : (0 : ℝ) ≤ 4.5 * η := by linarith
  have hub : μ.probEvent (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b) ≤ 18 * η := by
    rw [hev]
    calc μ.probEvent
          (fun T => ∃ b ∈ Finset.univ.filter fun b => e ∈ Ebad b, occurs b T)
        ≤ ∑ b ∈ Finset.univ.filter fun b => e ∈ Ebad b, μ.probEvent (occurs b) :=
          μ.probEvent_exists_le _ _
      _ ≤ ∑ _b ∈ Finset.univ.filter fun b => e ∈ Ebad b, 4.5 * η :=
          Finset.sum_le_sum fun b _ => hprob b
      _ = ((Finset.univ.filter fun b => e ∈ Ebad b).card : ℝ) * (4.5 * η) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * (4.5 * η) := mul_le_mul_of_nonneg_right hdeg h45
      _ = 18 * η := by ring
  calc μ.expect (fun T => slack α x Ebad occurs T e)
      = (α * x e) * μ.probEvent (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b) := hexp
    _ ≤ (α * x e) * (18 * η) :=
        mul_le_mul_of_nonneg_left hub (mul_nonneg hα (hx e))
    _ = 18 * α * η * x e := by ring

open Classical in
/-- **KKO22 Theorem 5.2 (Main theorem).**

`x₀` is a feasible subtour-LP point, `e₀` the distinguished edge of its
support, and `x = e₀.restrict x₀` is `x₀` restricted to `E` — the paper's
setup, now statable thanks to the `e₀` layer in `Basic.lean`.  Given a
spanning-tree distribution `μ` with marginals `x`, there is a random slack
vector `s*`, depending only on the tree, that is nonnegative, pays `α(1 − η)`
across every odd **rooted** near-minimum cut crossed on both sides, and costs
at most `18αηxₑ` in expectation on each edge.

The cut quantification is over `IsRootedNearMinCut e₀ x₀ η S`: near-minimum
with respect to the *LP point*, oriented away from `e₀`.  That is the form
§4–§5 produce, and on such cuts the restricted vector agrees anyway
(`IsRootedNearMinCut.restrict`); quantifying over near-min cuts of
`e₀.restrict x₀` itself would be the wrong seam, since the restricted
vector — total edge mass `n − 1` — is never a subtour-LP point.

The three hypotheses are §5's lemmas; see the module docstring for the table,
and in particular for why `hdeg` is a hypothesis rather than a proved input. -/
theorem exists_slack_vector {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (crossedBoth : Finset (Fin n) → Prop)
    (Ebad : Fin k → Finset (Sym2 (Fin n)))
    (occurs : Fin k → Finset (Sym2 (Fin n)) → Prop)
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hsat : ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → crossedBoth S →
      Odd (cutEdges S ∩ T).card →
      ∃ b, occurs b T ∧ Ebad b ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ Ebad b, e₀.restrict x₀ e)
    (hdeg : ∀ e : Sym2 (Fin n),
      ((Finset.univ.filter fun b => e ∈ Ebad b).card : ℝ) ≤ 4)
    (hprob : ∀ b, μ.probEvent (occurs b) ≤ 4.5 * η) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → crossedBoth S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 18 * α * η * e₀.restrict x₀ e) := by
  have hx : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  refine ⟨slack α (e₀.restrict x₀) Ebad occurs, fun T e => ?_, fun S T hS hc ho => ?_,
    fun e => ?_⟩
  · exact slack_nonneg hα hx T e
  · exact le_slack_cutSum hα hx (hsat S T hS hc ho)
  · exact expect_slack_le μ hα hη hx e (hdeg e) hprob

open Classical in
/-- **Theorem 5.2 with `hdeg` discharged.**  The abstract "at most four bad
events per edge" hypothesis is replaced by two *per-polygon* facts, using the
polygon family: `hcharge`, that an edge is charged only in a polygon that
separates it, and `hlocal`, Lemma 5.4's `2 + 2` count inside one polygon.
Fact 4.9 (`card_badEvents_le_four`) multiplies them.

The polygon family is taken over the LP point `x₀` — that is where Benczúr's
Theorem 4.5, and hence Fact 4.9, lives — while the tree distribution is over
the restricted `x = e₀.restrict x₀`, as in KKO.  The bridge `cutSum_restrict`
is what makes the two views agree on the cuts that matter. -/
theorem exists_slack_vector_of_family {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (F : PolygonFamily x₀ η e₀)
    (crossedBoth : Finset (Fin n) → Prop)
    (Ebad : Fin k → Finset (Sym2 (Fin n)))
    (occurs : Fin k → Finset (Sym2 (Fin n)) → Prop)
    (poly : Fin k → Fin F.N)
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hsat : ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → crossedBoth S →
      Odd (cutEdges S ∩ T).card →
      ∃ b, occurs b T ∧ Ebad b ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ Ebad b, e₀.restrict x₀ e)
    (hcharge : ∀ (u v : Fin n) (b : Fin k),
      s(u, v) ∈ Ebad b → F.Separates (poly b) u v)
    (hlocal : ∀ (e : Sym2 (Fin n)) (i : Fin F.N),
      (Finset.univ.filter fun b => poly b = i ∧ e ∈ Ebad b).card ≤ 4)
    (hprob : ∀ b, μ.probEvent (occurs b) ≤ 4.5 * η) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → crossedBoth S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 18 * α * η * e₀.restrict x₀ e) := by
  refine exists_slack_vector e₀ hx₀ μ crossedBoth Ebad occurs hα hη hsat ?_ hprob
  intro e
  induction e using Sym2.ind with
  | _ u v =>
      have h4 := F.card_badEvents_le_four poly Ebad (hcharge u v) (hlocal s(u, v))
      exact_mod_cast h4

end TSPGap

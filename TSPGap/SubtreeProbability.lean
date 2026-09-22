/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Leaves
import TSPGap.Uncrossing

/-!
# Subtree probabilities: KKO22 Lemma 2.11 and Corollary 2.12

The count-only route to Corollary 2.12, discharging the black box
`prob_exactlyOne_betweenEdges`.  No connectivity event and no induced-subtree
bridge appear anywhere: the working event is the **cardinality equality**
`|T ∩ E(S)| + 1 = |S|`, and three such equalities — at `A`, `B` and `A ∪ B` —
already force exactly one `A`–`B` tree edge by pure counting.

* `internalEdges S` — KKO's `E(S)`, the off-diagonal edges inside `S`.
* `sum_cutSum_singleton_local` — the localized handshake
  `∑_{v ∈ S} x(δ(v)) = 2·x(E(S)) + x(δ(S))`, for any vector `x`.
* `card_internal_inter_add_one_le` — a spanning tree has at most `|S| − 1`
  internal edges.  ⚠️ Not by forest machinery: the first edges of geodesics
  toward a root `r ∈ S` inject `Sᶜ` into the tree edges leaving `S`, so the
  internal edges number at most `(n − 1) − |Sᶜ| = |S| − 1`.
* `TreeDist.probEvent_card_eq_of_expected` — one-sided Markov for an
  integer count with an almost-sure ceiling: if `|F ∩ T| ≤ m` on the support
  and `E|F ∩ T| ≥ m − δ`, then `P[|F ∩ T| = m] ≥ 1 − δ`.
* `prob_internal_card` — **Lemma 2.11** in counting form: for an `ε`-near
  minimum cut `S` avoiding `e₀`, `P[|T ∩ E(S)| + 1 = |S|] ≥ 1 − ε/2`.
  The ceiling is the tree bound; the mean is the handshake plus the LP
  degrees, which is where `AvoidsRootEdge` earns its keep — the restricted
  marginals agree with `x₀` on every edge touching `S`.
* `prob_exactlyOne_betweenEdges` — **Corollary 2.12**, no longer a box.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Internal edges -/

/-- The off-diagonal edges with both endpoints in `S` — KKO's `E(S)`. -/
def internalEdges (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (edgeFinset n).filter fun e => ∀ v ∈ e, v ∈ S

theorem internalEdges_subset_edgeFinset (S : Finset (Fin n)) :
    internalEdges S ⊆ edgeFinset n := Finset.filter_subset _ _

theorem mem_internalEdges {S : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ internalEdges S ↔ ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ S := by
  rw [internalEdges, Finset.mem_filter, edgeFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Finset.mem_univ _, h.1⟩, h.2⟩⟩

theorem forall_mem_sym2_iff {S : Finset (Fin n)} {a b : Fin n} :
    (∀ v ∈ s(a, b), v ∈ S) ↔ a ∈ S ∧ b ∈ S := by
  constructor
  · intro h
    exact ⟨h a (Sym2.mem_mk_left a b), h b (Sym2.mem_mk_right a b)⟩
  · rintro ⟨ha, hb⟩ v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ha
    · exact hb

theorem mem_internalEdges_pair {S : Finset (Fin n)} {a b : Fin n} :
    s(a, b) ∈ internalEdges S ↔ a ≠ b ∧ a ∈ S ∧ b ∈ S := by
  rw [mem_internalEdges, Sym2.mk_isDiag_iff, forall_mem_sym2_iff]

theorem mem_cutEdges_pair {S : Finset (Fin n)} {a b : Fin n} :
    s(a, b) ∈ cutEdges S ↔ (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S) := by
  simp only [mem_cutEdges_iff'', Finset.mem_compl, Sym2.eq_iff]
  aesop

theorem mem_betweenEdges_pair {A B : Finset (Fin n)} {a b : Fin n} :
    s(a, b) ∈ betweenEdges A B ↔ (a ∈ A ∧ b ∈ B) ∨ (b ∈ A ∧ a ∈ B) := by
  simp only [betweenEdges, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq_iff]
  aesop

theorem rootEdge_notMem_internalEdges {e₀ : RootEdge n} {S : Finset (Fin n)}
    (h : AvoidsRootEdge e₀ S) : e₀.edge ∉ internalEdges S := fun hmem =>
  h.1 ((mem_internalEdges.mp hmem).2 e₀.u₀ (Sym2.mem_mk_left e₀.u₀ e₀.v₀))

/-! ### The localized handshake -/

/-- `Split.cutEdges_singleton_eq`, restated so that this file does not import
the tour development. -/
theorem cutEdges_singleton_eq' (v : Fin n) :
    cutEdges {v} = (edgeFinset n).filter fun e => v ∈ e := by
  ext e
  rw [mem_cutEdges_singleton, Finset.mem_filter, edgeFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨⟨Finset.mem_univ _, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-- Per edge, the endpoint-in-`S` indicator sum sorts the edge into the
internal or the cut bucket, with weight `2` or `1`. -/
theorem sum_ite_mem_sym2 (x : Sym2 (Fin n) → ℝ) {S : Finset (Fin n)}
    {e : Sym2 (Fin n)} (he : ¬ e.IsDiag) :
    (∑ v ∈ S, if v ∈ e then x e else 0)
      = (if e ∈ internalEdges S then 2 * x e else 0)
        + (if e ∈ cutEdges S then x e else 0) := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at he
    have hsplit : ∀ v : Fin n, (if v ∈ s(a, b) then x s(a, b) else 0)
        = (if v = a then x s(a, b) else 0) + (if v = b then x s(a, b) else 0) := by
      intro v
      by_cases hva : v = a
      · subst hva
        rw [if_pos (Sym2.mem_mk_left v b), if_pos rfl, if_neg he]
        ring
      · by_cases hvb : v = b
        · subst hvb
          rw [if_pos (Sym2.mem_mk_right a v), if_neg hva, if_pos rfl]
          ring
        · rw [if_neg (by simp [Sym2.mem_iff, hva, hvb]), if_neg hva, if_neg hvb]
          ring
    rw [Finset.sum_congr rfl fun v _ => hsplit v, Finset.sum_add_distrib,
      Finset.sum_ite_eq' S a fun _ => x s(a, b),
      Finset.sum_ite_eq' S b fun _ => x s(a, b)]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · rw [if_pos ha, if_pos hb, if_pos (mem_internalEdges_pair.mpr ⟨he, ha, hb⟩),
        if_neg (fun hc => by
          rcases mem_cutEdges_pair.mp hc with ⟨-, h⟩ | ⟨-, h⟩
          exacts [h hb, h ha])]
      ring
    · rw [if_pos ha, if_neg hb,
        if_neg (fun hc => hb (mem_internalEdges_pair.mp hc).2.2),
        if_pos (mem_cutEdges_pair.mpr (Or.inl ⟨ha, hb⟩))]
      ring
    · rw [if_neg ha, if_pos hb,
        if_neg (fun hc => ha (mem_internalEdges_pair.mp hc).2.1),
        if_pos (mem_cutEdges_pair.mpr (Or.inr ⟨hb, ha⟩))]
    · rw [if_neg ha, if_neg hb,
        if_neg (fun hc => ha (mem_internalEdges_pair.mp hc).2.1),
        if_neg (fun hc => by
          rcases mem_cutEdges_pair.mp hc with ⟨h, -⟩ | ⟨h, -⟩
          exacts [ha h, hb h])]

/-- **The localized handshake**: `∑_{v ∈ S} x(δ(v)) = 2·x(E(S)) + x(δ(S))`,
for any vector `x`.  Both sides count edge–endpoint incidences inside `S`.
(`Split.sum_cutSum_singleton` is the `S = univ` case, where the cut term
vanishes.) -/
theorem sum_cutSum_singleton_local (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    ∑ v ∈ S, cutSum x {v}
      = 2 * (∑ e ∈ internalEdges S, x e) + cutSum x S := by
  classical
  have hv : ∀ v : Fin n,
      cutSum x {v} = ∑ e ∈ edgeFinset n, if v ∈ e then x e else 0 := by
    intro v
    rw [cutSum, cutEdges_singleton_eq', Finset.sum_filter]
  rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_comm]
  have hsort : (∑ e ∈ edgeFinset n, ∑ v ∈ S, if v ∈ e then x e else 0)
      = ∑ e ∈ edgeFinset n,
          ((if e ∈ internalEdges S then 2 * x e else 0)
            + (if e ∈ cutEdges S then x e else 0)) :=
    Finset.sum_congr rfl fun e he =>
      sum_ite_mem_sym2 x ((Finset.mem_filter.mp he).2)
  rw [hsort, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (internalEdges_subset_edgeFinset S),
    Finset.inter_eq_right.mpr (cutEdges_subset_edgeFinset'' S),
    Finset.mul_sum, cutSum]

/-! ### A spanning tree has at most `|S| − 1` internal edges -/

/-- **The tree bound.**  Root the tree at some `r ∈ S`: each vertex outside
`S` has a strictly-distance-decreasing tree edge, and these first geodesic
edges are distinct and all leave `S`, so at least `|Sᶜ|` of the `n − 1` tree
edges are not internal to `S`. -/
theorem card_internal_inter_add_one_le {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {S : Finset (Fin n)} (hS : S.Nonempty) :
    (internalEdges S ∩ T).card + 1 ≤ S.card := by
  classical
  obtain ⟨hloop, hcard, hconn⟩ := hT
  obtain ⟨r, hr⟩ := hS
  set G := SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n))) with hG
  set touch := T.filter (fun e => ¬ ∀ v ∈ e, v ∈ S) with htouch
  -- the internal edges of `T` and the edges leaving `S` partition `T`
  have hsplit : (internalEdges S ∩ T).card + touch.card = T.card := by
    have h1 : internalEdges S ∩ T = T.filter fun e => ∀ v ∈ e, v ∈ S := by
      ext e
      simp only [Finset.mem_inter, mem_internalEdges, Finset.mem_filter]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hloop e h.1, h.2⟩, h.1⟩⟩
    rw [h1, htouch, Finset.card_filter_add_card_filter_not]
  -- every vertex outside `S` has a tree edge strictly closer to `r`
  have hstep : ∀ w : Fin n, ∃ u : Fin n,
      w ∉ S → (G.Adj w u ∧ G.dist u r < G.dist w r) := by
    intro w
    by_cases hw : w ∈ S
    · exact ⟨r, fun hc => absurd hw hc⟩
    · have hwr : w ≠ r := fun hc => hw (hc ▸ hr)
      have hreach : G.Reachable w r := hconn.preconnected w r
      have hdist : G.dist w r ≠ 0 := fun h =>
        (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h).elim hwr
          fun hc => hc hreach
      obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      cases p with
      | nil => exact absurd rfl hwr
      | cons hadj q =>
          rename_i u
          refine ⟨u, fun _ => ⟨hadj, ?_⟩⟩
          rw [SimpleGraph.Walk.length_cons] at hp
          have hq := SimpleGraph.dist_le q
          omega
  choose f hf using hstep
  -- the first geodesic edges inject `Sᶜ` into the edges leaving `S`
  have hinj : Sᶜ.card ≤ touch.card := by
    refine Finset.card_le_card_of_injOn (fun w => s(w, f w)) ?_ ?_
    · intro w hw
      have hw' : w ∉ S := Finset.mem_compl.mp hw
      obtain ⟨hadj, -⟩ := hf w hw'
      rw [hG, SimpleGraph.fromEdgeSet_adj] at hadj
      exact Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hadj.1,
        fun hall => hw' (hall w (Sym2.mem_mk_left w (f w)))⟩
    · intro w₁ h₁ w₂ h₂ heq
      have hw₁ : w₁ ∉ S := Finset.mem_compl.mp (Finset.mem_coe.mp h₁)
      have hw₂ : w₂ ∉ S := Finset.mem_compl.mp (Finset.mem_coe.mp h₂)
      obtain ⟨-, hd₁⟩ := hf w₁ hw₁
      obtain ⟨-, hd₂⟩ := hf w₂ hw₂
      rcases Sym2.eq_iff.mp heq with ⟨h, -⟩ | ⟨ha, hb⟩
      · exact h
      · rw [hb] at hd₁
        rw [ha] at hd₁
        omega
  have hcompl : S.card + Sᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨r, hr⟩
  omega

/-! ### One-sided Markov for a bounded count -/

namespace TreeDist

variable {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)

open Classical in
/-- Events with the same trees have the same probability. -/
theorem probEvent_congr {Q R : Finset (Sym2 (Fin n)) → Prop}
    (h : ∀ T, Q T ↔ R T) : μ.probEvent Q = μ.probEvent R := by
  unfold probEvent
  congr 1
  exact Finset.filter_congr fun T _ => h T

open Classical in
/-- A weaker event is at least as probable. -/
theorem probEvent_mono {Q R : Finset (Sym2 (Fin n)) → Prop}
    (h : ∀ T, Q T → R T) : μ.probEvent Q ≤ μ.probEvent R := by
  rw [probEvent_eq_sum, probEvent_eq_sum]
  refine Finset.sum_le_sum fun T _ => ?_
  by_cases hq : Q T
  · rw [if_pos hq, if_pos (h T hq)]
  · rw [if_neg hq]
    split_ifs
    · exact μ.prob_nonneg T
    · exact le_rfl

open Classical in
/-- **One-sided Markov at a ceiling.**  An integer count that never exceeds
`m` on the support and has mean at least `m − δ` equals `m` with probability
at least `1 − δ`: the shortfall `m − |F ∩ T|` is a nonnegative integer of
mean at most `δ`, so it is positive with probability at most `δ`. -/
theorem probEvent_card_eq_of_expected {F : Finset (Sym2 (Fin n))} {m : ℕ}
    {δ : ℝ} (hub : ∀ T, μ.prob T ≠ 0 → (F ∩ T).card ≤ m)
    (hexp : (m : ℝ) - δ ≤ μ.expectedCard F) :
    1 - δ ≤ μ.probEvent fun T => (F ∩ T).card = m := by
  have key : μ.probEvent (fun T => ¬ ((F ∩ T).card = m))
      ≤ (m : ℝ) - μ.expectedCard F := by
    rw [probEvent_eq_sum]
    have step2 : (∑ T : Finset (Sym2 (Fin n)),
          μ.prob T * ((m : ℝ) - ((F ∩ T).card : ℝ)))
        = (m : ℝ) - μ.expectedCard F := by
      have hring : ∀ T : Finset (Sym2 (Fin n)),
          μ.prob T * ((m : ℝ) - ((F ∩ T).card : ℝ))
            = (m : ℝ) * μ.prob T - μ.prob T * ((F ∩ T).card : ℝ) :=
        fun T => by ring
      rw [Finset.sum_congr rfl fun T _ => hring T, Finset.sum_sub_distrib,
        ← Finset.mul_sum, μ.total, mul_one, expectedCard]
    refine le_trans (Finset.sum_le_sum fun T _ => ?_) (le_of_eq step2)
    rcases eq_or_ne (μ.prob T) 0 with h0 | h0
    · rw [h0]
      simp
    · have hcard := hub T h0
      have hnn := μ.prob_nonneg T
      by_cases hm : (F ∩ T).card = m
      · rw [if_neg (not_not_intro hm), hm]
        simp
      · rw [if_pos hm]
        have h1 : (F ∩ T).card + 1 ≤ m := by omega
        have h1' : (1 : ℝ) ≤ (m : ℝ) - ((F ∩ T).card : ℝ) := by
          have := (Nat.cast_le (α := ℝ)).mpr h1
          push_cast at this
          linarith
        nlinarith
  have hnot := μ.probEvent_not fun T => (F ∩ T).card = m
  linarith

end TreeDist

/-! ### KKO22 Lemma 2.11, in counting form -/

variable {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}

/-- **KKO22 Lemma 2.11**, as a count: for an `ε`-near minimum cut `S`
avoiding both endpoints of `e₀`, the tree has exactly `|S| − 1` internal
edges with probability at least `1 − ε/2`.

The ceiling is `card_internal_inter_add_one_le`; the mean is the handshake
`2·x₀(E(S)) = 2|S| − x₀(δ(S)) ≥ 2|S| − 2 − ε` — the LP degrees apply because
`AvoidsRootEdge` keeps every edge touching `S` away from `e₀`, where the
restricted marginals agree with `x₀`. -/
theorem prob_internal_card (hx₀ : x₀ ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x₀)) {S : Finset (Fin n)} {ε : ℝ}
    (havoid : AvoidsRootEdge e₀ S) (hS : IsNearMinCut x₀ ε S) :
    1 - ε / 2 ≤ μ.probEvent fun T => (internalEdges S ∩ T).card + 1 = S.card := by
  classical
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr hS.nonempty
  have hmass : (S.card : ℝ) - 1 - ε / 2 ≤ ∑ e ∈ internalEdges S, x₀ e := by
    have hhs := sum_cutSum_singleton_local x₀ S
    have hdeg : ∑ v ∈ S, cutSum x₀ {v} = 2 * S.card := by
      rw [Finset.sum_congr rfl fun v _ => hx₀.2.1 v, Finset.sum_const,
        nsmul_eq_mul, mul_comm]
    have hcut := hS.cut_le
    linarith
  have hexp : (S.card : ℝ) - 1 - ε / 2 ≤ μ.expectedCard (internalEdges S) := by
    rw [μ.expectedCard_eq_sum (internalEdges_subset_edgeFinset S),
      RootEdge.sum_restrict_of_notMem (rootEdge_notMem_internalEdges havoid)]
    exact hmass
  have hkey := μ.probEvent_card_eq_of_expected (F := internalEdges S)
    (m := S.card - 1) (δ := ε / 2)
    (fun T hT => by
      have := card_internal_inter_add_one_le (μ.support_spanningTree T hT)
        hS.nonempty
      omega)
    (by
      rw [Nat.cast_sub hpos, Nat.cast_one]
      linarith)
  calc 1 - ε / 2
      ≤ μ.probEvent fun T => (internalEdges S ∩ T).card = S.card - 1 := hkey
    _ = μ.probEvent fun T => (internalEdges S ∩ T).card + 1 = S.card :=
        μ.probEvent_congr fun T => by omega

/-! ### The three-count argument for Corollary 2.12 -/

/-- For disjoint `A`, `B`, the internal edges of `A ∪ B` are exactly the
internal edges of `A`, those of `B`, and the `A`–`B` edges. -/
theorem internalEdges_union_eq {A B : Finset (Fin n)} (hd : Disjoint A B) :
    internalEdges (A ∪ B)
      = (internalEdges A ∪ internalEdges B) ∪ betweenEdges A B := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    have h1 : a ∈ A → a ∉ B := fun h => Finset.disjoint_left.mp hd h
    have h2 : b ∈ A → b ∉ B := fun h => Finset.disjoint_left.mp hd h
    simp only [Finset.mem_union, mem_internalEdges_pair, mem_betweenEdges_pair]
    constructor
    · rintro ⟨hab, ha, hb⟩
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (Or.inl ⟨hab, ha, hb⟩)
      · exact Or.inr (Or.inl ⟨ha, hb⟩)
      · exact Or.inr (Or.inr ⟨hb, ha⟩)
      · exact Or.inl (Or.inr ⟨hab, ha, hb⟩)
    · rintro ((⟨hab, ha, hb⟩ | ⟨hab, ha, hb⟩) | (⟨ha, hb⟩ | ⟨hb, ha⟩))
      · exact ⟨hab, Or.inl ha, Or.inl hb⟩
      · exact ⟨hab, Or.inr ha, Or.inr hb⟩
      · exact ⟨fun hc => h1 ha (hc ▸ hb), Or.inl ha, Or.inr hb⟩
      · exact ⟨fun hc => h2 hb (hc ▸ ha), Or.inr ha, Or.inl hb⟩

theorem disjoint_internalEdges {A B : Finset (Fin n)} (hd : Disjoint A B) :
    Disjoint (internalEdges A) (internalEdges B) := by
  rw [Finset.disjoint_left]
  intro e he hbe
  revert he hbe
  induction e using Sym2.ind with
  | _ a b =>
    intro he hbe
    exact Finset.disjoint_left.mp hd (mem_internalEdges_pair.mp he).2.1
      (mem_internalEdges_pair.mp hbe).2.1

theorem disjoint_internalEdges_betweenEdges {A B : Finset (Fin n)}
    (hd : Disjoint A B) :
    Disjoint (internalEdges A ∪ internalEdges B) (betweenEdges A B) := by
  rw [Finset.disjoint_left]
  intro e he hbe
  revert he hbe
  induction e using Sym2.ind with
  | _ a b =>
    intro he hbe
    have h1 : a ∈ A → a ∉ B := fun h => Finset.disjoint_left.mp hd h
    have h2 : b ∈ A → b ∉ B := fun h => Finset.disjoint_left.mp hd h
    rw [Finset.mem_union, mem_internalEdges_pair, mem_internalEdges_pair] at he
    rw [mem_betweenEdges_pair] at hbe
    tauto

/-- The three-way count: internal edges of the union split as internal of
`A`, internal of `B`, and between. -/
theorem card_internal_union_inter {A B : Finset (Fin n)} (hd : Disjoint A B)
    (T : Finset (Sym2 (Fin n))) :
    (internalEdges (A ∪ B) ∩ T).card
      = (internalEdges A ∩ T).card + (internalEdges B ∩ T).card
        + (betweenEdges A B ∩ T).card := by
  have houter : Disjoint ((internalEdges A ∩ T) ∪ (internalEdges B ∩ T))
      (betweenEdges A B ∩ T) := by
    refine Disjoint.mono ?_ Finset.inter_subset_left
      (disjoint_internalEdges_betweenEdges hd)
    rw [← Finset.union_inter_distrib_right]
    exact Finset.inter_subset_left
  have hinner : Disjoint (internalEdges A ∩ T) (internalEdges B ∩ T) :=
    Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (disjoint_internalEdges hd)
  rw [internalEdges_union_eq hd, Finset.union_inter_distrib_right,
    Finset.union_inter_distrib_right, Finset.card_union_of_disjoint houter,
    Finset.card_union_of_disjoint hinner]

/-- **Three cardinality equalities force exactly one `A`–`B` edge.**  Pure
counting; neither connectivity nor any spanning-tree property enters. -/
theorem card_between_eq_one_of_counts {A B : Finset (Fin n)}
    (hd : Disjoint A B) {T : Finset (Sym2 (Fin n))}
    (hA : (internalEdges A ∩ T).card + 1 = A.card)
    (hB : (internalEdges B ∩ T).card + 1 = B.card)
    (hU : (internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card) :
    (betweenEdges A B ∩ T).card = 1 := by
  have hsum := card_internal_union_inter hd T
  have hcard : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hd
  omega

/-- **KKO22 Corollary 2.12** — formerly the black box
`prob_exactlyOne_betweenEdges`.  For disjoint near-minimum cuts `A`, `B`
with `A ∪ B` also near minimum, all avoiding `e₀`, the tree puts exactly one
edge between `A` and `B` with probability at least
`1 − (εA + εB + εA∪B)/2`: a union bound over the three counting events of
Lemma 2.11, whose conjunction forces the between-count to be one. -/
theorem prob_exactlyOne_betweenEdges {x₀ : Sym2 (Fin n) → ℝ}
    {e₀ : RootEdge n} (hx₀ : x₀ ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x₀)) {A B : Finset (Fin n)}
    {εA εB εAB : ℝ} (havoid : AvoidsRootEdge e₀ (A ∪ B))
    (hd : Disjoint A B) (hA : IsNearMinCut x₀ εA A)
    (hB : IsNearMinCut x₀ εB B) (hAB : IsNearMinCut x₀ εAB (A ∪ B)) :
    1 - (εA + εB + εAB) / 2
      ≤ μ.probEvent (fun T => (betweenEdges A B ∩ T).card = 1) := by
  classical
  have pA := prob_internal_card hx₀ μ (havoid.mono Finset.subset_union_left) hA
  have pB := prob_internal_card hx₀ μ (havoid.mono Finset.subset_union_right) hB
  have pU := prob_internal_card hx₀ μ havoid hAB
  have hnA : μ.probEvent
      (fun T => ¬ ((internalEdges A ∩ T).card + 1 = A.card)) ≤ εA / 2 := by
    rw [μ.probEvent_not]
    linarith
  have hnB : μ.probEvent
      (fun T => ¬ ((internalEdges B ∩ T).card + 1 = B.card)) ≤ εB / 2 := by
    rw [μ.probEvent_not]
    linarith
  have hnU : μ.probEvent
      (fun T => ¬ ((internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card))
        ≤ εAB / 2 := by
    rw [μ.probEvent_not]
    linarith
  have hor : μ.probEvent (fun T =>
      ¬ ((internalEdges A ∩ T).card + 1 = A.card)
        ∨ (¬ ((internalEdges B ∩ T).card + 1 = B.card)
          ∨ ¬ ((internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card)))
      ≤ εA / 2 + (εB / 2 + εAB / 2) :=
    (μ.probEvent_or_le _ _).trans
      (add_le_add hnA ((μ.probEvent_or_le _ _).trans (add_le_add hnB hnU)))
  have hnot := μ.probEvent_not (fun T =>
    ((internalEdges A ∩ T).card + 1 = A.card)
      ∧ ((internalEdges B ∩ T).card + 1 = B.card)
      ∧ ((internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card))
  have hcongr : μ.probEvent (fun T =>
      ¬ (((internalEdges A ∩ T).card + 1 = A.card)
        ∧ ((internalEdges B ∩ T).card + 1 = B.card)
        ∧ ((internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card)))
      = μ.probEvent (fun T =>
        ¬ ((internalEdges A ∩ T).card + 1 = A.card)
          ∨ (¬ ((internalEdges B ∩ T).card + 1 = B.card)
            ∨ ¬ ((internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card))) :=
    μ.probEvent_congr fun T => by tauto
  have htriple : 1 - (εA + εB + εAB) / 2
      ≤ μ.probEvent (fun T =>
          ((internalEdges A ∩ T).card + 1 = A.card)
            ∧ ((internalEdges B ∩ T).card + 1 = B.card)
            ∧ ((internalEdges (A ∪ B) ∩ T).card + 1 = (A ∪ B).card)) := by
    rw [hcongr] at hnot
    linarith
  refine htriple.trans (μ.probEvent_mono fun T hT => ?_)
  exact card_between_eq_one_of_counts hd hT.1 hT.2.1 hT.2.2

end TSPGap

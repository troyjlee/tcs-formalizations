/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic

/-!
# Parallel-edge refinement

KKO obtain Definition 5.18's partition of `δ(u)` by splitting an edge into
parallel copies "WLOG" (KKO21, 2007.01409v6 lines 3159-3161).  This
development's edges are `Sym2 (Fin n)` — simple, with no multiplicity — and
`DegreePartitionExists.lean` shows the gap is real: the cut `{0.6, 0.6, 0.6, 0.2}`
is LP-feasible and admits no side of mass in `[1 − ε₁, 1 + ε_η]`, while
`smallCutEdges_two_le_card_mul` shows that asking the *original* edges to be
small would need `120000` of them per cut.

This file is the refinement: a finite type of **pieces**, each lying over a base
edge, carrying a share `q` of that edge's `x`.  Only the edges of a chosen
target set `D` are genuinely split — every other edge has exactly one piece —
and on `D` every piece carries at most `ε₁`, which is precisely what the greedy
argument of `exists_degreePartition_of_small` needs.

`TreeDist` knows nothing about pieces, by design: its trees are simple edge
sets, and `IsSpanningTree` goes through `SimpleGraph.fromEdgeSet`, which erases
copies.  The lift of a tree law to pieces, and its projection back, live in
`RefinementLift.lean`; this file is only the combinatorial object and the one
identity everything downstream rests on, `sum_piecesOver`: **the pieces over an
edge set carry exactly its `x`-mass.**

## Main results

* `EdgeRefinement` — the structure.
* `EdgeRefinement.sum_piecesOver` — the bridge to every existing `x(F)` bound.
* `exists_edgeRefinement` — one always exists: equal shares, enough of them.
-/

namespace TSPGap

open Finset

variable {n : ℕ}

/-- Every cut edge is off-diagonal: its endpoints lie on opposite sides. -/
theorem cutEdges_subset_edgeFinset (S : Finset (Fin n)) :
    cutEdges S ⊆ edgeFinset n := by
  intro e he
  rw [cutEdges, Finset.mem_filter] at he
  obtain ⟨-, u, hu, v, hv, rfl⟩ := he
  rw [edgeFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.mk_isDiag_iff]
  rintro rfl
  exact (Finset.mem_compl.mp hv) hu

/-- **A parallel-edge refinement of `x`, splitting the edges of `D` into pieces
of `x`-mass at most `ε₁`.**

Each piece `p` lies over the base edge `base p` and carries the share `q p` of
that edge, the shares over one edge summing to `1`.  Edges outside `D` are not
split: their fiber is a single piece.  The kernel `q` is what makes a tree law
liftable to pieces — a selected base edge picks one of its copies with
probability `q`. -/
structure EdgeRefinement (x : Sym2 (Fin n) → ℝ) (D : Finset (Sym2 (Fin n))) (ε₁ : ℝ) where
  /-- The pieces. -/
  Piece : Type
  [fintype : Fintype Piece]
  [decEq : DecidableEq Piece]
  /-- The edge a piece lies over. -/
  base : Piece → Sym2 (Fin n)
  base_mem : ∀ p, base p ∈ edgeFinset n
  fiber_nonempty : ∀ e ∈ edgeFinset n, ∃ p, base p = e
  /-- The share of its base edge that a piece carries. -/
  q : Piece → ℝ
  q_pos : ∀ p, 0 < q p
  q_fiber_sum : ∀ e ∈ edgeFinset n, ∑ p, (if base p = e then q p else 0) = 1
  /-- On the target set, every piece is small. -/
  weight_small : ∀ p, base p ∈ D → x (base p) * q p ≤ ε₁
  /-- Off the target set, an edge has exactly one piece. -/
  fiber_subsingleton_off : ∀ p p', base p ∉ D → base p = base p' → p = p'

attribute [instance] EdgeRefinement.fintype EdgeRefinement.decEq

namespace EdgeRefinement

variable {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- The `x`-mass a piece carries: its share of its base edge. -/
noncomputable def weight (p : R.Piece) : ℝ := x (R.base p) * R.q p

theorem weight_nonneg (hx : ∀ e, 0 ≤ x e) (p : R.Piece) : 0 ≤ R.weight p :=
  mul_nonneg (hx _) (R.q_pos p).le

theorem weight_le_of_mem {p : R.Piece} (hp : R.base p ∈ D) : R.weight p ≤ ε₁ :=
  R.weight_small p hp

/-- The pieces lying over an edge set. -/
def piecesOver (F : Finset (Sym2 (Fin n))) : Finset R.Piece :=
  Finset.univ.filter fun p => R.base p ∈ F

theorem mem_piecesOver {F : Finset (Sym2 (Fin n))} {p : R.Piece} :
    p ∈ R.piecesOver F ↔ R.base p ∈ F := by
  simp [piecesOver]

/-- The pieces over one edge carry exactly its `x`: the shares sum to `1`. -/
theorem fiber_weight_sum {e : Sym2 (Fin n)} (he : e ∈ edgeFinset n) :
    ∑ p, (if R.base p = e then R.weight p else 0) = x e := by
  have h := R.q_fiber_sum e he
  calc ∑ p, (if R.base p = e then R.weight p else 0)
      = ∑ p, x e * (if R.base p = e then R.q p else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : R.base p = e
        · simp [hp, weight]
        · simp [hp]
    _ = x e * ∑ p, (if R.base p = e then R.q p else 0) := by rw [Finset.mul_sum]
    _ = x e := by rw [h, mul_one]

/-- **The bridge.**  The pieces over an edge set carry exactly its `x`-mass,
so every bound the development states as `x(F) ≤ …` transfers to pieces
verbatim. -/
theorem sum_piecesOver {F : Finset (Sym2 (Fin n))} (hF : F ⊆ edgeFinset n) :
    ∑ p ∈ R.piecesOver F, R.weight p = ∑ e ∈ F, x e := by
  classical
  calc ∑ p ∈ R.piecesOver F, R.weight p
      = ∑ p ∈ R.piecesOver F, ∑ e ∈ F, (if R.base p = e then R.weight p else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_ite_eq, if_pos (R.mem_piecesOver.mp hp)]
    _ = ∑ e ∈ F, ∑ p ∈ R.piecesOver F, (if R.base p = e then R.weight p else 0) :=
        Finset.sum_comm
    _ = ∑ e ∈ F, ∑ p, (if R.base p = e then R.weight p else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [piecesOver, Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : R.base p = e
        · simp [hp, he]
        · simp [hp]
    _ = ∑ e ∈ F, x e := Finset.sum_congr rfl fun e he => R.fiber_weight_sum (hF he)

end EdgeRefinement

/-! ### Existence: equal shares, enough of them -/

/-- How many pieces an edge gets: on `D`, enough that each share of `x e` is at
most `ε₁`; off `D`, one. -/
noncomputable def refinementCopies (x : Sym2 (Fin n) → ℝ) (D : Finset (Sym2 (Fin n)))
    (ε₁ : ℝ) (e : Sym2 (Fin n)) : ℕ :=
  if e ∈ D then max 1 ⌈x e / ε₁⌉₊ else 1

theorem refinementCopies_pos (x : Sym2 (Fin n) → ℝ) (D : Finset (Sym2 (Fin n)))
    (ε₁ : ℝ) (e : Sym2 (Fin n)) : 0 < refinementCopies x D ε₁ e := by
  unfold refinementCopies
  split_ifs
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · exact one_pos

/-- **A refinement always exists.**  Give each target edge `e` equal shares,
`⌈x e / ε₁⌉` of them, so that each carries `x e / ⌈x e / ε₁⌉ ≤ ε₁`; give every
other edge one piece.  The pieces are indexed by `Σ e, Fin (copies e)`. -/
theorem exists_edgeRefinement (x : Sym2 (Fin n) → ℝ) (D : Finset (Sym2 (Fin n)))
    {ε₁ : ℝ} (hε : 0 < ε₁) :
    Nonempty (EdgeRefinement x D ε₁) := by
  classical
  refine ⟨{
    Piece := Σ e : edgeFinset n, Fin (refinementCopies x D ε₁ e)
    base := fun p => p.1
    base_mem := fun p => p.1.2
    fiber_nonempty := fun e he =>
      ⟨⟨⟨e, he⟩, ⟨0, refinementCopies_pos x D ε₁ e⟩⟩, rfl⟩
    q := fun p => 1 / (refinementCopies x D ε₁ p.1 : ℝ)
    q_pos := fun p => one_div_pos.mpr (Nat.cast_pos.mpr (refinementCopies_pos x D ε₁ _))
    q_fiber_sum := ?_
    weight_small := ?_
    fiber_subsingleton_off := ?_ }⟩
  · -- the shares over `e` sum to `copies e · (1 / copies e) = 1`
    intro e he
    rw [Fintype.sum_sigma]
    have hcpos : (0 : ℝ) < refinementCopies x D ε₁ e :=
      Nat.cast_pos.mpr (refinementCopies_pos x D ε₁ e)
    -- only the summand at `a = ⟨e, he⟩` survives
    have key : ∀ a : edgeFinset n,
        (∑ i : Fin (refinementCopies x D ε₁ a),
          (if ((a : Sym2 (Fin n)) = e) then 1 / (refinementCopies x D ε₁ a : ℝ) else 0))
        = if a = ⟨e, he⟩ then 1 else 0 := by
      intro a
      by_cases ha : a = ⟨e, he⟩
      · subst ha
        simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        exact mul_one_div_cancel hcpos.ne'
      · have ha' : (a : Sym2 (Fin n)) ≠ e := fun h => ha (Subtype.ext h)
        simp [ha', ha]
    simp_rw [key]
    rw [Finset.sum_ite_eq']
    simp
  · -- a target piece carries `x e / copies e ≤ ε₁`
    rintro ⟨a, i⟩ ha
    simp only at ha ⊢
    have hc : x a / ε₁ ≤ (refinementCopies x D ε₁ a : ℝ) := by
      unfold refinementCopies
      rw [if_pos ha]
      calc x a / ε₁ ≤ (⌈x a / ε₁⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ ((max 1 ⌈x a / ε₁⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hcpos : (0 : ℝ) < refinementCopies x D ε₁ a :=
      Nat.cast_pos.mpr (refinementCopies_pos x D ε₁ a)
    rw [div_le_iff₀ hε] at hc
    rw [mul_one_div, div_le_iff₀ hcpos]
    linarith
  · -- off `D` there is one copy, so two pieces over the same edge coincide
    rintro ⟨a, i⟩ ⟨a', i'⟩ hD hb
    simp only at hD hb
    obtain rfl : a = a' := Subtype.ext hb
    have h1 : refinementCopies x D ε₁ a = 1 := by
      unfold refinementCopies; rw [if_neg hD]
    congr 1
    apply Fin.ext
    have hi := i.isLt
    have hi' := i'.isLt
    omega

end TSPGap

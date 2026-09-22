/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.EdgeRefinement
import TSPGap.TreeDist

/-!
# Lifting a tree law to pieces

A `TreeDist` is a law on simple edge sets.  On the refined graph a tree is a
**transversal** set of pieces — at most one piece over each base edge — and the
canonical lift of `μ` selects, for each edge of a `μ`-tree, one of its pieces
with the kernel probability `q`:

`liftProb μ Ť = μ.prob (project Ť) · ∏_{p ∈ Ť} q p`  for transversal `Ť`, else `0`.

Everything about the lift reduces to one combinatorial identity.  The
transversals projecting onto a fixed `T` correspond exactly to the choice
functions picking one piece over each edge of `T`, so by "product of sums is
the sum over choice functions of products",

`∑_{Ť ↦ T} ∏_{p ∈ Ť} q p = ∏_{e ∈ T} ∑_{p over e} q p = 1`.

That is `sum_transversals_prod_q`, and `lift_pushforward` — the lifted law
projects back to `μ` — is its immediate consequence.  `TreeDist` itself is
untouched; the lift is a sidecar.

## Main results

* `EdgeRefinement.project`, `EdgeRefinement.IsTransversal`, `EdgeRefinement.liftProb`.
* `EdgeRefinement.sum_transversals_prod` — the identity, for any summand.
* `EdgeRefinement.lift_pushforward` — `∑_{Ť ↦ T} liftProb Ť = μ.prob T`.
* `EdgeRefinement.lift_total` — the lifted law is a probability law.
* `EdgeRefinement.lift_marginal` — a piece's weight is its lifted marginal.
* `EdgeRefinement.lift_probEvent` — events disintegrate over the projected tree.
-/

namespace TSPGap

open Finset
open scoped Classical

variable {n : ℕ}

/-- A `μ`-tree with positive mass is a set of off-diagonal edges. -/
theorem TreeDist.support_subset_edgeFinset {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)
    {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0) : T ⊆ edgeFinset n := by
  intro e he
  rw [edgeFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (μ.support_spanningTree T hT).1 e he⟩

namespace EdgeRefinement

variable {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- The simple edge set a set of pieces lies over. -/
def project (Ť : Finset R.Piece) : Finset (Sym2 (Fin n)) := Ť.image R.base

/-- A set of pieces is a **transversal** when no two of its pieces lie over the
same edge — the refined analogue of "a set of edges", forbidding two parallel
copies at once. -/
def IsTransversal (Ť : Finset R.Piece) : Prop :=
  Set.InjOn R.base (↑Ť : Set R.Piece)

theorem mem_project {Ť : Finset R.Piece} {e : Sym2 (Fin n)} :
    e ∈ R.project Ť ↔ ∃ p ∈ Ť, R.base p = e := by
  simp [project]

/-! ### Choice functions over an edge set -/

/-- The choice functions picking one piece over each edge of `T`. -/
def sections (T : Finset (Sym2 (Fin n))) : Finset (T → R.Piece) :=
  Fintype.piFinset fun e : T => Finset.univ.filter fun p => R.base p = e

theorem mem_sections {T : Finset (Sym2 (Fin n))} {s : T → R.Piece} :
    s ∈ R.sections T ↔ ∀ e : T, R.base (s e) = e := by
  simp [sections, Fintype.mem_piFinset]

/-- A choice function is injective: its values lie over distinct edges. -/
theorem sections_injective {T : Finset (Sym2 (Fin n))} {s : T → R.Piece}
    (hs : s ∈ R.sections T) : Function.Injective s := by
  intro e e' h
  have := congrArg R.base h
  rw [R.mem_sections.mp hs e, R.mem_sections.mp hs e'] at this
  exact Subtype.ext this

/-! ### Transversals over an edge set -/

/-- The image of a choice function is a transversal projecting onto `T`. -/
theorem image_mem_transversals {T : Finset (Sym2 (Fin n))} {s : T → R.Piece}
    (hs : s ∈ R.sections T) :
    R.IsTransversal (Finset.univ.image s) ∧ R.project (Finset.univ.image s) = T := by
  classical
  have hsec := R.mem_sections.mp hs
  refine ⟨?_, ?_⟩
  · intro p hp p' hp' hb
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    obtain ⟨e', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp')
    rw [hsec e, hsec e'] at hb
    rw [Subtype.ext hb]
  · ext f
    rw [project, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hp
      rw [hsec e]; exact e.2
    · intro hf
      exact ⟨s ⟨f, hf⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hsec ⟨f, hf⟩⟩

/-- **Transversals over `T` are the images of choice functions**, for any
summand.  This is the bijection everything rests on; `sum_transversals_prod_q`
below and the evaluation identity in `RefinementStability.lean` are both
instances of it. -/
theorem sum_sections_image {M : Type*} [AddCommMonoid M] {T : Finset (Sym2 (Fin n))}
    (f : Finset R.Piece → M) :
    ∑ s ∈ R.sections T, f (Finset.univ.image s)
      = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T), f Ť := by
  refine Finset.sum_nbij (fun s => Finset.univ.image s) ?_ ?_ ?_ (fun s _ => rfl)
  · -- a choice function's image is a transversal over `T`
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, R.image_mem_transversals hs⟩
  · -- distinct choice functions have distinct images: each is recovered from
    -- its image as the unique piece over each edge
    intro s hs s' hs' h
    have hsec := R.mem_sections.mp (Finset.mem_coe.mp hs)
    have hsec' := R.mem_sections.mp (Finset.mem_coe.mp hs')
    funext e
    have h' : Finset.univ.image s = Finset.univ.image s' := h
    have hmem : s e ∈ Finset.univ.image s' := by
      rw [← h']; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨e', -, he'⟩ := Finset.mem_image.mp hmem
    have : (e' : Sym2 (Fin n)) = e := by
      rw [← hsec' e', he', hsec e]
    rw [← he', Subtype.ext this]
  · -- every transversal over `T` is the image of the choice function
    -- sending each edge to its unique piece
    intro Ť hŤ
    obtain ⟨-, htr, hproj⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hŤ)
    have hpick : ∀ e : T, ∃ p ∈ Ť, R.base p = e := fun e => by
      have : (e : Sym2 (Fin n)) ∈ R.project Ť := hproj ▸ e.2
      exact R.mem_project.mp this
    choose s hsŤ hsb using hpick
    refine ⟨s, Finset.mem_coe.mpr (R.mem_sections.mpr hsb), ?_⟩
    ext p
    rw [Finset.mem_image]
    constructor
    · rintro ⟨e, -, rfl⟩; exact hsŤ e
    · intro hp
      have hpe : R.base p ∈ T := hproj ▸ R.mem_project.mpr ⟨p, hp, rfl⟩
      refine ⟨⟨R.base p, hpe⟩, Finset.mem_univ _, ?_⟩
      exact htr (Finset.mem_coe.mpr (hsŤ _)) (Finset.mem_coe.mpr hp) (hsb _)

/-- A product over a choice function's image is the product over the function. -/
theorem prod_image_sections {M : Type*} [CommMonoid M] {T : Finset (Sym2 (Fin n))}
    {s : T → R.Piece} (hs : s ∈ R.sections T) (g : R.Piece → M) :
    ∏ p ∈ Finset.univ.image s, g p = ∏ e : T, g (s e) :=
  Finset.prod_image fun _ _ _ _ h => R.sections_injective hs h

/-- **Transversals over `T`, for any multiplicative summand.**  The sum over
the transversals projecting onto `T` of a product factors as the product over
`T`'s edges of the fiber sums — "product of sums is the sum over choice
functions of products", carried across the bijection above.  No hypothesis on
`T`: an edge with no piece empties both sides. -/
theorem sum_transversals_prod {M : Type*} [CommSemiring M] (T : Finset (Sym2 (Fin n)))
    (g : R.Piece → M) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T), ∏ p ∈ Ť, g p
      = ∏ e ∈ T, ∑ p, (if R.base p = e then g p else 0) := by
  rw [← R.sum_sections_image (fun Ť => ∏ p ∈ Ť, g p),
    Finset.sum_congr rfl fun s hs => R.prod_image_sections hs g,
    sections, ← Finset.prod_univ_sum, ← Finset.prod_coe_sort T]
  exact Finset.prod_congr rfl fun e _ => Finset.sum_filter _ _

/-- **The `q`-identity.**  Over an edge set of genuine edges, the `q`-products of
the transversals projecting onto it sum to `1`: each fiber's shares sum to `1`. -/
theorem sum_transversals_prod_q {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
      ∏ p ∈ Ť, R.q p = 1 := by
  rw [R.sum_transversals_prod T R.q]
  exact Finset.prod_eq_one fun e he => R.q_fiber_sum e (hT he)

/-! ### The lifted law -/

open Classical in
/-- **The canonical lift of `μ` to pieces**: a transversal gets the mass of the
simple tree it projects to, times the kernel probability of its particular
choice of copies. -/
noncomputable def liftProb (μ : TreeDist n x) (Ť : Finset R.Piece) : ℝ :=
  if R.IsTransversal Ť then μ.prob (R.project Ť) * ∏ p ∈ Ť, R.q p else 0

theorem liftProb_nonneg (μ : TreeDist n x) (Ť : Finset R.Piece) :
    0 ≤ R.liftProb μ Ť := by
  unfold liftProb
  split_ifs
  · exact mul_nonneg (μ.prob_nonneg _) (Finset.prod_nonneg fun p _ => (R.q_pos p).le)
  · exact le_rfl

/-- **The lift projects back to `μ`.**  The lifted mass of the transversals
over `T` is exactly `μ.prob T`. -/
theorem lift_pushforward (μ : TreeDist n x) (T : Finset (Sym2 (Fin n))) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T), R.liftProb μ Ť = μ.prob T := by
  classical
  -- non-transversals contribute nothing, so restrict to transversals over `T`
  have hsplit : ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T), R.liftProb μ Ť
      = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
          μ.prob T * ∏ p ∈ Ť, R.q p := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Ť _ => ?_
    unfold liftProb
    by_cases hp : R.project Ť = T <;> by_cases htr : R.IsTransversal Ť <;> simp [hp, htr]
  rw [hsplit, ← Finset.mul_sum]
  by_cases h0 : μ.prob T = 0
  · rw [h0, zero_mul]
  · rw [R.sum_transversals_prod_q (μ.support_subset_edgeFinset h0), mul_one]

/-- **The lifted law is a probability law**: grouping transversals by the tree
they project to, `lift_pushforward` turns the total into `μ`'s. -/
theorem lift_total (μ : TreeDist n x) :
    ∑ Ť : Finset R.Piece, R.liftProb μ Ť = 1 := by
  classical
  rw [← μ.total]
  rw [← Finset.sum_fiberwise Finset.univ R.project (R.liftProb μ)]
  exact Finset.sum_congr rfl fun T _ => R.lift_pushforward μ T

/-! ### Marginals and events of the lifted law -/

/-- On a transversal over `T ∋ base p`, zeroing every piece over `base p` other
than `p` turns a product into the same product if `p` is present and `0` if it
is not: a transversal holds exactly one piece over `base p`. -/
theorem prod_pin {T : Finset (Sym2 (Fin n))} {p : R.Piece} (hpT : R.base p ∈ T)
    {Ť : Finset R.Piece} (htr : R.IsTransversal Ť) (hproj : R.project Ť = T)
    (g : R.Piece → ℝ) :
    ∏ p' ∈ Ť, (if R.base p' = R.base p then (if p' = p then g p' else 0) else g p')
      = if p ∈ Ť then ∏ p' ∈ Ť, g p' else 0 := by
  by_cases hp : p ∈ Ť
  · rw [if_pos hp]
    refine Finset.prod_congr rfl fun p' hp' => ?_
    by_cases hb : R.base p' = R.base p
    · have : p' = p := htr (Finset.mem_coe.mpr hp') (Finset.mem_coe.mpr hp) hb
      simp [this]
    · simp [hb]
  · rw [if_neg hp]
    obtain ⟨p'', hp''Ť, hb''⟩ := R.mem_project.mp (hproj ▸ hpT)
    have hne : p'' ≠ p := fun h => hp (h ▸ hp''Ť)
    exact Finset.prod_eq_zero hp''Ť (by simp [hb'', hne])

/-- **The lifted marginal of a piece is its weight.**  `weight p = x (base p) · q p`
is not merely a bookkeeping number: it is the probability, under the lifted
law, that the refined tree contains `p`.  Group by projection; over a tree `T`
containing `base p`, exactly the transversals choosing `p` over that edge
survive, contributing `q p` times the other fibers' full sums of `1`; then
`μ.marginals` turns `∑_{T ∋ base p} μ.prob T` into `x (base p)`. -/
theorem lift_marginal (μ : TreeDist n x) (p : R.Piece) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => p ∈ Ť), R.liftProb μ Ť = R.weight p := by
  -- the pinned summand: `q`, except that pieces over `base p` other than `p` get `0`
  set g : R.Piece → ℝ :=
    fun p' => if R.base p' = R.base p then (if p' = p then R.q p' else 0) else R.q p'
    with hgdef
  -- per tree `T`: the transversals over `T` that contain `p`
  have hT : ∀ T : Finset (Sym2 (Fin n)),
      ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T ∧ p ∈ Ť), R.liftProb μ Ť
        = if R.base p ∈ T then μ.prob T * R.q p else 0 := by
    intro T
    by_cases hpT : R.base p ∈ T
    · rw [if_pos hpT]
      -- restrict to transversals and pin `p`
      have h1 : ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T ∧ p ∈ Ť), R.liftProb μ Ť
          = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
              μ.prob T * ∏ p' ∈ Ť, g p' := by
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun Ť _ => ?_
        by_cases hproj : R.project Ť = T
        · by_cases htr : R.IsTransversal Ť
          · rw [hgdef, R.prod_pin hpT htr hproj]
            by_cases hp : p ∈ Ť <;> simp [hproj, htr, hp, liftProb]
          · simp [hproj, htr, liftProb]
        · simp [hproj]
      rw [h1, ← Finset.mul_sum, R.sum_transversals_prod T g]
      by_cases h0 : μ.prob T = 0
      · rw [h0, zero_mul, zero_mul]
      · congr 1
        have hTe : T ⊆ edgeFinset n := μ.support_subset_edgeFinset h0
        -- split off the factor at `base p`
        rw [← Finset.mul_prod_erase T _ hpT]
        -- that factor is `q p` ...
        have hfac : ∑ p', (if R.base p' = R.base p then g p' else 0) = R.q p := by
          have : ∀ p', (if R.base p' = R.base p then g p' else 0)
              = if p' = p then R.q p' else 0 := by
            intro p'
            simp only [hgdef]
            by_cases hb : R.base p' = R.base p
            · simp [hb]
            · have : p' ≠ p := fun h => hb (h ▸ rfl)
              simp [hb, this]
          simp_rw [this]
          exact Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (Finset.mem_univ _))
        -- ... and every other factor is a full fiber sum, `1`
        have hrest : ∏ e ∈ T.erase (R.base p), ∑ p', (if R.base p' = e then g p' else 0) = 1 := by
          refine Finset.prod_eq_one fun e he => ?_
          have hne : e ≠ R.base p := (Finset.mem_erase.mp he).1
          have heT : e ∈ T := (Finset.mem_erase.mp he).2
          rw [← R.q_fiber_sum e (hTe heT)]
          refine Finset.sum_congr rfl fun p' _ => ?_
          by_cases hb : R.base p' = e
          · simp [hgdef, hb, hne]
          · simp [hb]
        rw [hfac, hrest, mul_one]
    · rw [if_neg hpT]
      apply Finset.sum_eq_zero
      intro Ť hŤ
      obtain ⟨-, hproj, hpŤ⟩ := Finset.mem_filter.mp hŤ
      exact absurd (hproj ▸ R.mem_project.mpr ⟨p, hpŤ, rfl⟩) hpT
  -- group the pieces-containing transversals by their projection
  rw [← Finset.sum_fiberwise (Finset.univ.filter (fun Ť => p ∈ Ť)) R.project]
  have hgroup : ∀ T, ∑ Ť ∈ (Finset.univ.filter (fun Ť => p ∈ Ť)).filter (fun Ť => R.project Ť = T),
        R.liftProb μ Ť
      = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T ∧ p ∈ Ť), R.liftProb μ Ť := by
    intro T
    rw [Finset.filter_filter]
    exact Finset.sum_congr (Finset.filter_congr fun _ _ => and_comm) fun _ _ => rfl
  simp_rw [hgroup, hT]
  rw [← Finset.sum_filter, ← Finset.sum_mul, μ.marginals _ (R.base_mem p)]
  rfl

/-- **Disintegration of a lifted event.**  The lifted probability of any event
on piece sets is the `μ`-expectation of its conditional probability given the
projected tree — the transversals over `T` satisfying it, weighted by `q`. -/
theorem lift_probEvent (μ : TreeDist n x) (Q : Finset R.Piece → Prop) :
    ∑ Ť ∈ Finset.univ.filter Q, R.liftProb μ Ť
      = ∑ T : Finset (Sym2 (Fin n)), μ.prob T *
          ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T ∧ Q Ť),
            ∏ p ∈ Ť, R.q p := by
  rw [← Finset.sum_fiberwise (Finset.univ.filter Q) R.project]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases hQ : Q Ť <;> by_cases hproj : R.project Ť = T <;> by_cases htr : R.IsTransversal Ť
    <;> simp [hQ, hproj, htr, liftProb]

end EdgeRefinement

end TSPGap

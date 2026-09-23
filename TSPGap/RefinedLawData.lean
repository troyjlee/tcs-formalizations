/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinementLift
import TSPGap.Conditioning
import TSPGap.FaceStability
import TSPGap.MaxFace

/-!
# The lifted law as a weight: support, rank, and what commutes with lifting

`RefinementLift.lean` lifts `μ.prob`.  The payment argument, however, runs on
*conditioned* laws — faces (`faceWeight`), avoidance (`avoidWeight`), and the
generic `Finset ι → ℝ` weights of `FederMihail.lean` that these produce — and
those are not probability laws.  So the lift is generalized here to any weight,
`liftWeight`, and the facts that let the piece-native top layer reuse the base
machinery are proved once:

* the lifted weight inherits nonnegativity, fixed rank, and support
  (`FixedRankWeight`, `WeightSupportedOn`), so every generic lemma of
  `FederMihail.lean` applies to it unchanged;
* on a transversal, **counts on pieces are counts on the projection** —
  `|Ť ∩ piecesOver F| = |project Ť ∩ F|` — and this is the *only* cardinality
  rewrite allowed, guarded by transversality;
* events, expectations and `expCard` that are read through `project` have the
  same value under the lift as under the base weight;
* face and avoid conditioning **commute with lifting**: conditioning the lifted
  weight on a count over `piecesOver K` is the lift of the base weight
  conditioned on the count over `K` — and, for any cost `c`, conditioning on
  the pulled-back cost `c ∘ base` is the lift of conditioning on `c`.

Graph geometry is always read on `project Ť`; pieces carry only counts.
-/

namespace TSPGap

open Finset

variable {n : ℕ}

namespace EdgeRefinement

variable {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

open scoped Classical

/-! ### The generic lift -/

/-- **The lift of an arbitrary base weight to pieces**: a transversal gets the
weight of its projection times the kernel probability of its copies, and a
non-transversal gets `0`.  `liftProb μ` is the case `w = μ.prob`. -/
noncomputable def liftWeight (w : Finset (Sym2 (Fin n)) → ℝ) (Ť : Finset R.Piece) : ℝ :=
  if R.IsTransversal Ť then w (R.project Ť) * ∏ p ∈ Ť, R.q p else 0

theorem liftProb_eq_liftWeight (μ : TreeDist n x) : R.liftProb μ = R.liftWeight μ.prob := rfl

theorem liftWeight_of_transversal {w : Finset (Sym2 (Fin n)) → ℝ} {Ť : Finset R.Piece}
    (htr : R.IsTransversal Ť) :
    R.liftWeight w Ť = w (R.project Ť) * ∏ p ∈ Ť, R.q p := if_pos htr

theorem liftWeight_of_not_transversal {w : Finset (Sym2 (Fin n)) → ℝ} {Ť : Finset R.Piece}
    (htr : ¬ R.IsTransversal Ť) : R.liftWeight w Ť = 0 := if_neg htr

theorem prod_q_pos (Ť : Finset R.Piece) : 0 < ∏ p ∈ Ť, R.q p :=
  Finset.prod_pos fun p _ => R.q_pos p

/-- Where the lift lives: on transversals whose projection carries weight. -/
theorem liftWeight_ne_zero {w : Finset (Sym2 (Fin n)) → ℝ} {Ť : Finset R.Piece}
    (h : R.liftWeight w Ť ≠ 0) : R.IsTransversal Ť ∧ w (R.project Ť) ≠ 0 := by
  by_cases htr : R.IsTransversal Ť
  · refine ⟨htr, fun hw => h ?_⟩
    rw [R.liftWeight_of_transversal htr, hw, zero_mul]
  · exact absurd (R.liftWeight_of_not_transversal htr) h

/-! ### Inherited structure: nonnegativity, rank, support -/

theorem weightNonneg_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ} (hw : WeightNonneg w) :
    WeightNonneg (R.liftWeight w) := by
  intro Ť
  unfold liftWeight
  split_ifs
  · exact mul_nonneg (hw _) (R.prod_q_pos Ť).le
  · exact le_rfl

/-- A transversal has as many pieces as its projection has edges. -/
theorem card_project_of_transversal {Ť : Finset R.Piece} (htr : R.IsTransversal Ť) :
    (R.project Ť).card = Ť.card :=
  Finset.card_image_of_injOn htr

/-- **Fixed rank lifts.**  If the base weight lives on sets of size `r`, so does
its lift: a transversal in the support projects to a size-`r` set, and has as
many pieces. -/
theorem fixedRankWeight_liftWeight {r : ℕ} {w : Finset (Sym2 (Fin n)) → ℝ}
    (hr : FixedRankWeight r w) : FixedRankWeight r (R.liftWeight w) := by
  intro Ť h
  obtain ⟨htr, hw⟩ := R.liftWeight_ne_zero h
  rw [← R.card_project_of_transversal htr]
  exact hr _ hw

/-- **Support lifts.**  If the base weight is supported inside `K`, its lift is
supported inside the pieces over `K`. -/
theorem weightSupportedOn_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ} {K : Finset (Sym2 (Fin n))}
    (hw : WeightSupportedOn w K) : WeightSupportedOn (R.liftWeight w) (R.piecesOver K) := by
  intro Ť h p hp
  obtain ⟨-, hwT⟩ := R.liftWeight_ne_zero h
  exact R.mem_piecesOver.mpr (hw _ hwT (R.mem_project.mpr ⟨p, hp, rfl⟩))

/-- The lift of a tree law is supported on transversals projecting to spanning
trees, hence on piece sets of size `n − 1`. -/
theorem liftProb_ne_zero (μ : TreeDist n x) {Ť : Finset R.Piece} (h : R.liftProb μ Ť ≠ 0) :
    R.IsTransversal Ť ∧ IsSpanningTree n (R.project Ť) ∧ Ť.card = n - 1 := by
  obtain ⟨htr, hw⟩ := R.liftWeight_ne_zero h
  have hst := μ.support_spanningTree _ hw
  exact ⟨htr, hst, by rw [← R.card_project_of_transversal htr]; exact hst.2.1⟩

/-! ### Pushforward and total mass, for any weight -/

/-- **The generic pushforward.**  Needs only that the base weight lives on
genuine edges, so that every edge of a weighted set has a nonempty fiber. -/
theorem liftWeight_pushforward {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (T : Finset (Sym2 (Fin n))) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T), R.liftWeight w Ť = w T := by
  have hsplit : ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T), R.liftWeight w Ť
      = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
          w T * ∏ p ∈ Ť, R.q p := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Ť _ => ?_
    unfold liftWeight
    by_cases hp : R.project Ť = T <;> by_cases htr : R.IsTransversal Ť <;> simp [hp, htr]
  rw [hsplit, ← Finset.mul_sum]
  by_cases h0 : w T = 0
  · rw [h0, zero_mul]
  · rw [R.sum_transversals_prod_q (hw T h0), mul_one]

theorem totalMass_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) :
    totalMass (R.liftWeight w) = totalMass w := by
  unfold totalMass
  rw [← Finset.sum_fiberwise Finset.univ R.project (R.liftWeight w)]
  exact Finset.sum_congr rfl fun T _ => R.liftWeight_pushforward hw T

/-! ### The guarded cardinality bridge -/

/-- **Counts on pieces are counts on the projection — on a transversal.**
`|Ť ∩ piecesOver F| = |project Ť ∩ F|`: the pieces of `Ť` over `F` map
injectively onto the edges of `project Ť` in `F`.  This is the only
cardinality rewrite the piece-native layer is allowed, and it is guarded by
transversality: without it, two copies of one edge would count twice on
pieces and once on the projection. -/
theorem card_inter_piecesOver_of_transversal {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (F : Finset (Sym2 (Fin n))) :
    (Ť ∩ R.piecesOver F).card = (R.project Ť ∩ F).card := by
  have himg : (Ť ∩ R.piecesOver F).image R.base = R.project Ť ∩ F := by
    ext e
    constructor
    · intro he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hpŤ, hpF⟩ := Finset.mem_inter.mp hp
      exact Finset.mem_inter.mpr ⟨R.mem_project.mpr ⟨p, hpŤ, rfl⟩, R.mem_piecesOver.mp hpF⟩
    · intro he
      obtain ⟨heP, heF⟩ := Finset.mem_inter.mp he
      obtain ⟨p, hp, hb⟩ := R.mem_project.mp heP
      exact Finset.mem_image.mpr
        ⟨p, Finset.mem_inter.mpr ⟨hp, R.mem_piecesOver.mpr (hb ▸ heF)⟩, hb⟩
  rw [← himg, Finset.card_image_of_injOn]
  exact htr.mono (Finset.coe_subset.mpr Finset.inter_subset_left)

/-! ### Reading events and expectations through the projection -/

/-- **A projected event has the same mass under the lift.**  Group the piece
sets by projection and push each fiber forward. -/
theorem weightMass_liftWeight_project {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (A : Finset (Sym2 (Fin n)) → Prop) :
    weightMass (R.liftWeight w) (fun Ť => A (R.project Ť)) = weightMass w A := by
  unfold weightMass
  rw [← Finset.sum_fiberwise Finset.univ R.project]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hA : A T
  · rw [if_pos hA, ← R.liftWeight_pushforward hw T]
    refine Finset.sum_congr rfl fun Ť hŤ => ?_
    simp [(Finset.mem_filter.mp hŤ).2, hA]
  · rw [if_neg hA]
    refine Finset.sum_eq_zero fun Ť hŤ => ?_
    simp [(Finset.mem_filter.mp hŤ).2, hA]

/-- **A projected expectation has the same value under the lift.** -/
theorem sum_liftWeight_mul_project {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (f : Finset (Sym2 (Fin n)) → ℝ) :
    ∑ Ť : Finset R.Piece, R.liftWeight w Ť * f (R.project Ť)
      = ∑ T : Finset (Sym2 (Fin n)), w T * f T := by
  rw [← Finset.sum_fiberwise Finset.univ R.project]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← R.liftWeight_pushforward hw T, Finset.sum_mul]
  refine Finset.sum_congr rfl fun Ť hŤ => ?_
  rw [(Finset.mem_filter.mp hŤ).2]

/-- **`expCard` lifts.**  The expected number of pieces over `F` in a lifted
set is the expected number of edges of `F` in the base set — the bridge
applied on the support, where every set is a transversal. -/
theorem expCard_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (F : Finset (Sym2 (Fin n))) :
    expCard (R.liftWeight w) (R.piecesOver F) = expCard w F := by
  unfold expCard
  rw [← R.sum_liftWeight_mul_project hw (fun T => ((T ∩ F).card : ℝ))]
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases h : R.liftWeight w Ť = 0
  · rw [h, zero_mul, zero_mul]
  · rw [R.card_inter_piecesOver_of_transversal (R.liftWeight_ne_zero h).1]

/-! ### Conditioning commutes with lifting -/

/-- **Face conditioning commutes with the lift.**  Conditioning the lifted
weight on "exactly `m` pieces over `K`" is the lift of the base weight
conditioned on "exactly `m` edges of `K`".  Pointwise: on a transversal the
two counts agree by the bridge; off transversals both sides vanish. -/
theorem faceWeight_liftWeight (w : Finset (Sym2 (Fin n)) → ℝ) (K : Finset (Sym2 (Fin n)))
    (m : ℕ) :
    faceWeight (R.liftWeight w) (indicatorCost (R.piecesOver K)) m
      = R.liftWeight (faceWeight w (indicatorCost K) m) := by
  funext Ť
  simp only [faceWeight, setCost_indicatorCost, liftWeight]
  by_cases htr : R.IsTransversal Ť
  · simp only [htr, if_true, R.card_inter_piecesOver_of_transversal htr]
    split_ifs <;> simp
  · simp [htr]

/-- **Avoid conditioning commutes with the lift**: the `m = 0` face. -/
theorem avoidWeight_liftWeight (w : Finset (Sym2 (Fin n)) → ℝ) (K : Finset (Sym2 (Fin n))) :
    avoidWeight (R.liftWeight w) (R.piecesOver K) = R.liftWeight (avoidWeight w K) := by
  funext Ť
  simp only [avoidWeight_apply, liftWeight]
  by_cases htr : R.IsTransversal Ť
  · simp only [htr, if_true, R.card_inter_piecesOver_of_transversal htr]
    split_ifs <;> simp
  · simp [htr]

/-! ### Conditioning on a general cost -/

/-- **The cost bridge.**  On a transversal, a base cost pulled back to pieces
along `base` sums to the base cost of the projection — each edge of the
projection is hit by exactly one piece. -/
theorem setCost_comp_base_of_transversal {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (c : Sym2 (Fin n) → ℕ) :
    setCost (c ∘ R.base) Ť = setCost c (R.project Ť) := by
  unfold setCost project
  rw [Finset.sum_image htr]
  rfl

/-- **Face conditioning commutes with the lift, for any cost.**  Conditioning
the lifted weight on the pulled-back cost `c ∘ base` is the lift of the base
weight conditioned on `c`.  The indicator case (`faceWeight_liftWeight`) is
`c = indicatorCost K`, since `indicatorCost K ∘ base = indicatorCost (piecesOver K)`. -/
theorem faceWeight_liftWeight_cost (w : Finset (Sym2 (Fin n)) → ℝ) (c : Sym2 (Fin n) → ℕ)
    (m : ℕ) :
    faceWeight (R.liftWeight w) (c ∘ R.base) m = R.liftWeight (faceWeight w c m) := by
  funext Ť
  simp only [faceWeight, liftWeight]
  by_cases htr : R.IsTransversal Ť
  · simp only [htr, if_true, R.setCost_comp_base_of_transversal htr]
    split_ifs <;> simp
  · simp [htr]

/-- The pulled-back indicator cost is the indicator cost of the pieces over `K`. -/
theorem indicatorCost_comp_base (K : Finset (Sym2 (Fin n))) :
    indicatorCost K ∘ R.base = indicatorCost (R.piecesOver K) := by
  funext p
  simp [indicatorCost, R.mem_piecesOver]

end EdgeRefinement

end TSPGap

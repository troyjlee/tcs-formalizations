/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedTreeCondIndep
import TSPGap.TreeFace
import TSPGap.NestedChain
import TSPGap.Lemma524Independence

/-!
# The tree face on pieces, and the determinacy combinators

The consumer-facing half of step 2.  `RefinedTreeCondIndep.lean` states
Fact 2.8 on pieces; this file supplies what a consumer needs to *apply* it,
mirroring what `Lemma524Independence.lean` and `PolygonIndep.lean` provide on
the base:

* **Determinacy combinators.**  Conjunction; an event that only looks at
  `Ť ∩ P` is inside-determined when every piece of `P` has its base edge
  inside `S` and outside-determined when every piece leaves `S`
  (`refinedInsideDetermined_inter`, `refinedOutsideDetermined_inter`, and the
  `piecesOver` forms); membership of one piece; and the **pullback** of a
  base-determined event along `project`
  (`refinedInsideDetermined_project`), which is how the base atom-tree events
  `InducesTree u` are read on pieces.
* **The piece tree face** `refinedTreeFace f S`: conditioning a piece weight
  on exactly `|S| − 1` pieces over `S`'s internal edges.  On the lifted law it
  is the lift of the base tree face (`refinedTreeFace_liftProb`), and its
  total face mass is the base one — so the positivity hypothesis consumers
  carry stays a statement about `μ`.
* **The support bridge** `inducesTreeOn_project_iff_card`: on a transversal
  projecting to a spanning tree, "`S` induces a tree in the projection" *is*
  the piece count `|Ť ∩ piecesOver (internalEdges S)| + 1 = |S|`, by the
  guarded cardinality bridge and the base `inducesTreeOn_iff_card`.
* **The unwinding** `refinedTreeFace_unwind`: the mass of an event under the
  piece tree face, cross-multiplied, is the lifted mass of the event
  conjoined with `RefinedInducesTreeOn S` — the shape the cross identity is
  stated in.
* **The conditioned cross identity** `refinedCondIndep_conditioned`, the
  piece analogue of `condIndep_conditioned`, for any nonnegative weight
  satisfying `RefinedTreeCondIndep`.

Graph geometry is still read only on `project Ť`.  Note that
`RefinedInducesTreeOn u` for a sub-atom `u ⊆ S` is *not* inside-determined —
its transversality conjunct is global — so sub-atom tree events enter as
`InducesTree u (project Ť)`, via the pullback.
-/

namespace TSPGap

/-- A tree law, as a weight, lives on genuine edges. -/
theorem TreeDist.weightSupportedOn_edgeFinset {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) :
    WeightSupportedOn μ.prob (edgeFinset n) :=
  fun _ hT => μ.support_subset_edgeFinset hT

end TSPGap

namespace TSPGap.EdgeRefinement

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

variable {S : Finset (Fin n)}

/-! ### Determinacy combinators -/

section Combinators

variable {R}

theorem RefinedInsideDetermined.and {A A' : Finset R.Piece → Prop}
    (h : R.RefinedInsideDetermined S A) (h' : R.RefinedInsideDetermined S A') :
    R.RefinedInsideDetermined S (fun Ť => A Ť ∧ A' Ť) :=
  fun Ť Ť' hŤ => and_congr (h Ť Ť' hŤ) (h' Ť Ť' hŤ)

theorem RefinedOutsideDetermined.and {B B' : Finset R.Piece → Prop}
    (h : R.RefinedOutsideDetermined S B) (h' : R.RefinedOutsideDetermined S B') :
    R.RefinedOutsideDetermined S (fun Ť => B Ť ∧ B' Ť) :=
  fun Ť Ť' hŤ => and_congr (h Ť Ť' hŤ) (h' Ť Ť' hŤ)

end Combinators

/-- An event that only looks at `Ť ∩ P`, with every piece of `P` lying over an
edge inside `S`, is inside-determined. -/
theorem refinedInsideDetermined_inter {P : Finset R.Piece}
    (hP : ∀ p ∈ P, ∀ v ∈ R.base p, v ∈ S) (Q : Finset R.Piece → Prop) :
    R.RefinedInsideDetermined S (fun Ť => Q (Ť ∩ P)) := by
  have key : ∀ Ť : Finset R.Piece, Ť ∩ P = R.insidePieces S Ť ∩ P := by
    intro Ť
    ext p
    simp only [Finset.mem_inter, insidePieces, Finset.mem_filter]
    constructor
    · rintro ⟨hT, hp⟩; exact ⟨⟨hT, hP p hp⟩, hp⟩
    · rintro ⟨⟨hT, -⟩, hp⟩; exact ⟨hT, hp⟩
  intro Ť Ť' h
  show Q (Ť ∩ P) ↔ Q (Ť' ∩ P)
  rw [key Ť, key Ť', h]

/-- An event that only looks at `Ť ∩ P`, with every piece of `P` lying over an
edge leaving `S`, is outside-determined. -/
theorem refinedOutsideDetermined_inter {P : Finset R.Piece}
    (hP : ∀ p ∈ P, ¬ ∀ v ∈ R.base p, v ∈ S) (Q : Finset R.Piece → Prop) :
    R.RefinedOutsideDetermined S (fun Ť => Q (Ť ∩ P)) := by
  have key : ∀ Ť : Finset R.Piece, Ť ∩ P = R.outsidePieces S Ť ∩ P := by
    intro Ť
    ext p
    simp only [Finset.mem_inter, outsidePieces, Finset.mem_filter]
    constructor
    · rintro ⟨hT, hp⟩; exact ⟨⟨hT, hP p hp⟩, hp⟩
    · rintro ⟨⟨hT, -⟩, hp⟩; exact ⟨hT, hp⟩
  intro Ť Ť' h
  show Q (Ť ∩ P) ↔ Q (Ť' ∩ P)
  rw [key Ť, key Ť', h]

/-- The `piecesOver` form: a count over the pieces of an edge set inside `S`. -/
theorem refinedInsideDetermined_piecesOver {F : Finset (Sym2 (Fin n))}
    (hF : ∀ e ∈ F, ∀ v ∈ e, v ∈ S) (Q : Finset R.Piece → Prop) :
    R.RefinedInsideDetermined S (fun Ť => Q (Ť ∩ R.piecesOver F)) :=
  R.refinedInsideDetermined_inter (fun p hp => hF _ (R.mem_piecesOver.mp hp)) Q

/-- The `piecesOver` form: a count over the pieces of an edge set leaving `S`. -/
theorem refinedOutsideDetermined_piecesOver {F : Finset (Sym2 (Fin n))}
    (hF : ∀ e ∈ F, ¬ ∀ v ∈ e, v ∈ S) (Q : Finset R.Piece → Prop) :
    R.RefinedOutsideDetermined S (fun Ť => Q (Ť ∩ R.piecesOver F)) :=
  R.refinedOutsideDetermined_inter (fun p hp => hF _ (R.mem_piecesOver.mp hp)) Q

/-- Avoiding the pieces over a set of cut edges is outside-determined. -/
theorem refinedOutsideDetermined_avoid {C : Finset (Sym2 (Fin n))} (hC : C ⊆ cutEdges S) :
    R.RefinedOutsideDetermined S (fun Ť => (Ť ∩ R.piecesOver C).card = 0) :=
  R.refinedOutsideDetermined_piecesOver (fun e he => not_forall_mem_of_mem_cutEdges (hC he))
    (fun X => X.card = 0)

/-- Membership of a single piece over an edge inside `S` is inside-determined. -/
theorem refinedInsideDetermined_mem {p : R.Piece} (hp : ∀ v ∈ R.base p, v ∈ S) :
    R.RefinedInsideDetermined S (fun Ť => p ∈ Ť) := by
  have key : ∀ Ť : Finset R.Piece, p ∈ Ť ↔ p ∈ R.insidePieces S Ť := fun Ť => by
    simp only [insidePieces, Finset.mem_filter]
    exact ⟨fun h => ⟨h, hp⟩, fun h => h.1⟩
  intro Ť Ť' h
  show p ∈ Ť ↔ p ∈ Ť'
  rw [key Ť, key Ť', h]

/-- Membership of a single piece over an edge leaving `S` is outside-determined. -/
theorem refinedOutsideDetermined_mem {p : R.Piece} (hp : ¬ ∀ v ∈ R.base p, v ∈ S) :
    R.RefinedOutsideDetermined S (fun Ť => p ∈ Ť) := by
  have key : ∀ Ť : Finset R.Piece, p ∈ Ť ↔ p ∈ R.outsidePieces S Ť := fun Ť => by
    simp only [outsidePieces, Finset.mem_filter]
    exact ⟨fun h => ⟨h, hp⟩, fun h => h.1⟩
  intro Ť Ť' h
  show p ∈ Ť ↔ p ∈ Ť'
  rw [key Ť, key Ť', h]

/-! ### Pullbacks of base-determined events -/

/-- **A base inside-determined event, read through the projection, is
inside-determined on pieces**: the projection of the inside pieces is the
inside part of the projection. -/
theorem refinedInsideDetermined_project {A : Finset (Sym2 (Fin n)) → Prop}
    (hA : InsideDetermined S A) :
    R.RefinedInsideDetermined S (fun Ť => A (R.project Ť)) := by
  intro Ť Ť' h
  apply hA
  rw [← R.project_insidePieces, ← R.project_insidePieces, h]

theorem refinedOutsideDetermined_project {B : Finset (Sym2 (Fin n)) → Prop}
    (hB : OutsideDetermined S B) :
    R.RefinedOutsideDetermined S (fun Ť => B (R.project Ť)) := by
  intro Ť Ť' h
  apply hB
  rw [← R.project_outsidePieces, ← R.project_outsidePieces, h]

/-- The tree event of a sub-atom, read on the projection, is inside-determined. -/
theorem refinedInsideDetermined_inducesTree {u : Finset (Fin n)} (hu : u ⊆ S) :
    R.RefinedInsideDetermined S (fun Ť => InducesTree u (R.project Ť)) :=
  R.refinedInsideDetermined_project (insideDetermined_inducesTree hu)

/-! ### The lifted tree law as a generic weight -/

theorem liftProb_weightNonneg (μ : TreeDist n x) : WeightNonneg (R.liftProb μ) :=
  fun Ť => R.liftProb_nonneg μ Ť

theorem liftProb_fixedRankWeight (μ : TreeDist n x) : FixedRankWeight (n - 1) (R.liftProb μ) :=
  R.fixedRankWeight_liftWeight μ.fixedRankWeight

/-! ### Scalars and normalization pass through the lift -/

theorem liftWeight_div (w : Finset (Sym2 (Fin n)) → ℝ) (a : ℝ) :
    R.liftWeight (fun T => w T / a) = fun Ť => R.liftWeight w Ť / a := by
  funext Ť
  unfold liftWeight
  split_ifs <;> ring

/-- A face of a weight on genuine edges lives on genuine edges. -/
theorem weightSupportedOn_faceWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    {K : Finset (Sym2 (Fin n))} (hw : WeightSupportedOn w K) (c : Sym2 (Fin n) → ℕ) (m : ℕ) :
    WeightSupportedOn (faceWeight w c m) K :=
  fun T hT => hw T (faceWeight_ne_zero_imp hT).1

/-- **The face's total mass is the same on pieces and on the base.** -/
theorem totalMass_faceWeight_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (K : Finset (Sym2 (Fin n))) (m : ℕ) :
    totalMass (faceWeight (R.liftWeight w) (indicatorCost (R.piecesOver K)) m)
      = totalMass (faceWeight w (indicatorCost K) m) := by
  rw [R.faceWeight_liftWeight, R.totalMass_liftWeight (weightSupportedOn_faceWeight hw _ _)]

/-- **The normalized face commutes with the lift.** -/
theorem faceDist_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (K : Finset (Sym2 (Fin n))) (m : ℕ) :
    faceDist (R.liftWeight w) (indicatorCost (R.piecesOver K)) m
      = R.liftWeight (faceDist w (indicatorCost K) m) := by
  funext Ť
  show faceWeight (R.liftWeight w) (indicatorCost (R.piecesOver K)) m Ť
      / totalMass (faceWeight (R.liftWeight w) (indicatorCost (R.piecesOver K)) m)
    = R.liftWeight (fun T => faceWeight w (indicatorCost K) m T
        / totalMass (faceWeight w (indicatorCost K) m)) Ť
  rw [R.liftWeight_div, R.totalMass_faceWeight_liftWeight hw, R.faceWeight_liftWeight]

/-! ### The piece tree face -/

/-- **The tree face on pieces**: a piece weight conditioned on exactly
`|S| − 1` pieces over the internal edges of `S`. -/
noncomputable def refinedTreeFace (f : Finset R.Piece → ℝ) (S : Finset (Fin n)) :
    Finset R.Piece → ℝ :=
  faceDist f (indicatorCost (R.piecesOver (internalEdges S))) (S.card - 1)

/-- The piece tree face of a lifted weight is the lift of the base tree face. -/
theorem refinedTreeFace_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (S : Finset (Fin n)) :
    R.refinedTreeFace (R.liftWeight w) S = R.liftWeight (treeFace w S) :=
  R.faceDist_liftWeight hw _ _

theorem refinedTreeFace_liftProb (μ : TreeDist n x) (S : Finset (Fin n)) :
    R.refinedTreeFace (R.liftProb μ) S = R.liftWeight (treeFace μ.prob S) := by
  rw [R.liftProb_eq_liftWeight]
  exact R.refinedTreeFace_liftWeight μ.weightSupportedOn_edgeFinset S

/-- The face mass positivity hypothesis is the same statement on pieces and on
the base. -/
theorem totalMass_treeFaceWeight_liftProb (μ : TreeDist n x) (S : Finset (Fin n)) :
    totalMass (faceWeight (R.liftProb μ) (indicatorCost (R.piecesOver (internalEdges S)))
        (S.card - 1))
      = totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) := by
  rw [R.liftProb_eq_liftWeight]
  exact R.totalMass_faceWeight_liftWeight μ.weightSupportedOn_edgeFinset _ _

/-! ### The support bridge: topology through the projection is a piece count -/

/-- **On a transversal projecting to a spanning tree, "`S` induces a tree in
the projection" is the piece count** `|Ť ∩ piecesOver (internalEdges S)| + 1 = |S|`:
the base bridge `inducesTreeOn_iff_card` composed with the guarded
cardinality bridge. -/
theorem inducesTreeOn_project_iff_card {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (hst : IsSpanningTree n (R.project Ť)) (S : Finset (Fin n)) :
    InducesTreeOn S (R.project Ť)
      ↔ (Ť ∩ R.piecesOver (internalEdges S)).card + 1 = S.card := by
  rw [inducesTreeOn_iff_card hst, R.card_inter_piecesOver_of_transversal htr, Finset.inter_comm]

/-- The same, on the support of the lifted tree law. -/
theorem inducesTreeOn_project_iff_card_of_liftProb (μ : TreeDist n x) {Ť : Finset R.Piece}
    (h : R.liftProb μ Ť ≠ 0) (S : Finset (Fin n)) :
    InducesTreeOn S (R.project Ť)
      ↔ (Ť ∩ R.piecesOver (internalEdges S)).card + 1 = S.card :=
  R.inducesTreeOn_project_iff_card (R.liftProb_ne_zero μ h).1 (R.liftProb_ne_zero μ h).2.1 S

/-- On the lifted law the transversality conjunct of `RefinedInducesTreeOn` is
carried by the support, so the two conditioning conventions have equal mass. -/
theorem weightMass_liftWeight_refinedInducesTreeOn (w : Finset (Sym2 (Fin n)) → ℝ)
    (P : Finset R.Piece → Prop) (S : Finset (Fin n)) :
    weightMass (R.liftWeight w) (fun Ť => P Ť ∧ R.RefinedInducesTreeOn S Ť)
      = weightMass (R.liftWeight w) (fun Ť => P Ť ∧ InducesTreeOn S (R.project Ť)) :=
  weightMass_congr_of_support fun Ť h =>
    ⟨fun h' => ⟨h'.1, h'.2.2⟩, fun h' => ⟨h'.1, (R.liftWeight_ne_zero h).1, h'.2⟩⟩

/-! ### The unwinding -/

/-- **The piece tree-face mass, cross-multiplied, is the lifted mass under
`RefinedInducesTreeOn`.**  The normalizer is the *base* face mass. -/
theorem refinedTreeFace_unwind (μ : TreeDist n x) (hSne : S.Nonempty)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)))
    (P : Finset R.Piece → Prop) :
    weightMass (R.refinedTreeFace (R.liftProb μ) S) P
        * totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
      = weightMass (R.liftProb μ) (fun Ť => P Ť ∧ R.RefinedInducesTreeOn S Ť) := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hSne
  unfold refinedTreeFace
  rw [weightMass_faceDist, R.totalMass_treeFaceWeight_liftProb, div_mul_cancel₀ _ hmass.ne',
    weightMass_face]
  refine weightMass_congr_of_support fun Ť hŤ => ?_
  obtain ⟨htr, hst, -⟩ := R.liftProb_ne_zero μ hŤ
  have hI := R.inducesTreeOn_project_iff_card htr hst S
  constructor
  · rintro ⟨hP, hc⟩
    exact ⟨hP, htr, hI.mpr (by omega)⟩
  · rintro ⟨hP, -, hI'⟩
    refine ⟨hP, ?_⟩
    have := hI.mp hI'
    omega

/-- The piece tree face is a probability law when the base face has mass. -/
theorem totalMass_refinedTreeFace (μ : TreeDist n x)
    (hmass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))) :
    totalMass (R.refinedTreeFace (R.liftProb μ) S) = 1 := by
  have hmass' : 0 < totalMass (faceWeight (R.liftProb μ)
      (indicatorCost (R.piecesOver (internalEdges S))) (S.card - 1)) := by
    rw [R.totalMass_treeFaceWeight_liftProb]; exact hmass
  exact (fixedRankNormalized_faceDist (r := n - 1) (R.liftProb_fixedRankWeight μ)
    (R.liftProb_weightNonneg μ) hmass').total

/-! ### The conditioned cross identity on pieces -/

/-- **Independence under the conditioned piece law**, cross-multiplied — the
piece analogue of `condIndep_conditioned`.  With `K_in`, `A` inside-determined
and `K_out`, `B` outside-determined,

`W(K_in ∧ A ∧ K_out ∧ B ∧ C) · W(K_in ∧ K_out ∧ C)
  = W(K_in ∧ A ∧ K_out ∧ C) · W(K_in ∧ K_out ∧ B ∧ C)`,

where `C := RefinedInducesTreeOn S`.  No positivity is assumed. -/
theorem refinedCondIndep_conditioned {f : Finset R.Piece → ℝ} (hnn : WeightNonneg f)
    (hf : R.RefinedTreeCondIndep f) (S : Finset (Fin n))
    {Kin A Kout B : Finset R.Piece → Prop}
    (hKin : R.RefinedInsideDetermined S Kin) (hA : R.RefinedInsideDetermined S A)
    (hKout : R.RefinedOutsideDetermined S Kout) (hB : R.RefinedOutsideDetermined S B) :
    weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť)
        * weightMass f (fun Ť => Kin Ť ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť)
      = weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť)
        * weightMass f (fun Ť => Kin Ť ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť) := by
  have I1 := hf S _ _ (hKin.and hA) (hKout.and hB)
  have I0 := hf S _ _ hKin hKout
  have IA := hf S _ _ (hKin.and hA) hKout
  have IB := hf S _ _ hKin (hKout.and hB)
  unfold RefinedCondIndepCross at I1 I0 IA IB
  set c := weightMass f (R.RefinedInducesTreeOn S) with hc
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- every term lives inside `C`, so all vanish
    have hzero : ∀ Q : Finset R.Piece → Prop,
        (∀ Ť, Q Ť → R.RefinedInducesTreeOn S Ť) → weightMass f Q = 0 := by
      intro Q hQ
      refine le_antisymm ?_ (weightMass_nonneg hnn Q)
      have := weightMass_mono hnn hQ
      rw [← hc, hc0] at this
      exact this
    rw [hzero _ (fun T h => h.2.2), hzero _ (fun T h => h.2.2),
      hzero _ (fun T h => h.2.2), hzero _ (fun T h => h.2.2)]
  · -- cancel `c²`
    have hcc : c * c ≠ 0 := mul_ne_zero hc0 hc0
    apply mul_right_cancel₀ hcc
    calc weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť)
          * weightMass f (fun Ť => Kin Ť ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť) * (c * c)
        = (weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť)
              * c)
          * (weightMass f (fun Ť => Kin Ť ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť) * c) := by ring
      _ = (weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ R.RefinedInducesTreeOn S Ť)
            * weightMass f (fun Ť => (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť))
          * (weightMass f (fun Ť => Kin Ť ∧ R.RefinedInducesTreeOn S Ť)
            * weightMass f (fun Ť => Kout Ť ∧ R.RefinedInducesTreeOn S Ť)) := by rw [I1, I0]
      _ = (weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ R.RefinedInducesTreeOn S Ť)
            * weightMass f (fun Ť => Kout Ť ∧ R.RefinedInducesTreeOn S Ť))
          * (weightMass f (fun Ť => Kin Ť ∧ R.RefinedInducesTreeOn S Ť)
            * weightMass f (fun Ť => (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť)) := by ring
      _ = (weightMass f (fun Ť => (Kin Ť ∧ A Ť) ∧ Kout Ť ∧ R.RefinedInducesTreeOn S Ť) * c)
          * (weightMass f (fun Ť => Kin Ť ∧ (Kout Ť ∧ B Ť) ∧ R.RefinedInducesTreeOn S Ť) * c) := by
          rw [IA, IB]
      _ = _ := by ring

end TSPGap.EdgeRefinement

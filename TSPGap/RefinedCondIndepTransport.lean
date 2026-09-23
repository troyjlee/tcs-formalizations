/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedTreeCondIndep
import TSPGap.Fact28Functional

/-!
# Fact 2.8 transports to the lifted law

The refined tree law is `liftWeight w`; on a transversal it is the base weight
of the projection times the kernel `∏ q`, and the kernel is a **product over
pieces**.  A piece is inside or outside `S` by its base edge alone, so the
kernel factors as (inside copies) × (outside copies), and the transversals over
a tree `T` are exactly the pairs of a transversal over `insidePart S T` and one
over `outsidePart S T` (`sum_transversals_split`).

Hence the lifted mass of an event `A ∧ B ∧ "S induces a tree"`, with `A`
inside-determined and `B` outside-determined on pieces, disintegrates over
projections as

`∑_T w T · [S induces a tree in T] · α_A(insidePart S T) · β_B(outsidePart S T)`

where `α_A` is the `q`-mass of the inside copy choices satisfying `A` — a
function of the inside part of `T` alone — and `β_B` likewise of the outside
part.  These are *weights* in `[0,1]`, not indicators: a piece event can
distinguish copies and is not projection-determined.  That is why base
Fact 2.8 is needed for determined **functions** (`TreeCondIndep.functional`),
and with it the piece-level cross identity is the base one applied to
`α_A, β_B`.

## Main result

* `EdgeRefinement.treeCondIndep_liftWeight` — `TreeCondIndep w` transports to
  `RefinedTreeCondIndep (liftWeight w)`.
* `IsMaxEntropyLimit.refinedTreeCondIndep` — the export for the tree law.
-/

namespace TSPGap.EdgeRefinement

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-! ### Pieces over the two parts of a tree -/

variable {S : Finset (Fin n)}

/-- A piece set projecting inside `S` and one projecting outside `S` are disjoint. -/
theorem disjoint_of_project_parts {Ťi Ťo : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hpi : R.project Ťi = insidePart S F) (hpo : R.project Ťo = outsidePart S F) :
    Disjoint Ťi Ťo := by
  rw [Finset.disjoint_left]
  intro p hpi' hpo'
  have hin : R.base p ∈ insidePart S F := hpi ▸ R.mem_project.mpr ⟨p, hpi', rfl⟩
  have hout : R.base p ∈ outsidePart S F := hpo ▸ R.mem_project.mpr ⟨p, hpo', rfl⟩
  exact (Finset.mem_filter.mp hout).2 (Finset.mem_filter.mp hin).2

/-- The inside part of a glued pair is its inside member. -/
theorem insidePieces_union_of_parts {Ťi Ťo : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hpi : R.project Ťi = insidePart S F) (hpo : R.project Ťo = outsidePart S F) :
    R.insidePieces S (Ťi ∪ Ťo) = Ťi := by
  unfold insidePieces
  rw [Finset.filter_union, ← insidePieces, ← insidePieces, R.insidePieces_eq_self_of_project hpi,
    R.insidePieces_eq_empty_of_project hpo, Finset.union_empty]

theorem outsidePieces_union_of_parts {Ťi Ťo : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hpi : R.project Ťi = insidePart S F) (hpo : R.project Ťo = outsidePart S F) :
    R.outsidePieces S (Ťi ∪ Ťo) = Ťo := by
  unfold outsidePieces
  rw [Finset.filter_union, ← outsidePieces, ← outsidePieces, R.outsidePieces_eq_empty_of_project hpi,
    R.outsidePieces_eq_self_of_project hpo, Finset.empty_union]

/-! ### The inside and outside copy masses -/

/-- The `q`-mass of the transversals over `insidePart S T` satisfying `A`:
the inside copy choices of a tree `T` that `A` accepts. -/
noncomputable def insideMass (A : Finset R.Piece → Prop) (T : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ Ťi ∈ Finset.univ.filter
      (fun Ť => R.IsTransversal Ť ∧ R.project Ť = insidePart S T ∧ A Ť), ∏ p ∈ Ťi, R.q p

/-- The `q`-mass of the transversals over `outsidePart S T` satisfying `B`. -/
noncomputable def outsideMass (B : Finset R.Piece → Prop) (T : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ Ťo ∈ Finset.univ.filter
      (fun Ť => R.IsTransversal Ť ∧ R.project Ť = outsidePart S T ∧ B Ť), ∏ p ∈ Ťo, R.q p

/-- `insideMass` depends on `T` only through its inside part. -/
theorem insideMass_insideFunctionDetermined (A : Finset R.Piece → Prop) :
    InsideFunctionDetermined S (R.insideMass (S := S) A) := by
  intro T T' h
  unfold insideMass
  rw [h]

theorem outsideMass_outsideFunctionDetermined (B : Finset R.Piece → Prop) :
    OutsideFunctionDetermined S (R.outsideMass (S := S) B) := by
  intro T T' h
  unfold outsideMass
  rw [h]

/-- With no condition, the copy mass over a set of genuine edges is `1`. -/
theorem insideMass_true {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n) :
    R.insideMass (S := S) (fun _ => True) T = 1 := by
  unfold insideMass
  simp only [and_true]
  exact R.sum_transversals_prod_q (Finset.filter_subset _ _ |>.trans hT)

theorem outsideMass_true {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n) :
    R.outsideMass (S := S) (fun _ => True) T = 1 := by
  unfold outsideMass
  simp only [and_true]
  exact R.sum_transversals_prod_q (Finset.filter_subset _ _ |>.trans hT)

/-- `insideMass` over the split's inside index set, with the event moved into the summand. -/
theorem insideMass_eq (A : Finset R.Piece → Prop) (T : Finset (Sym2 (Fin n))) :
    R.insideMass (S := S) A T
      = ∑ Ťi ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = insidePart S T),
          (if A Ťi then ∏ p ∈ Ťi, R.q p else 0) := by
  unfold insideMass
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases h : R.IsTransversal Ť ∧ R.project Ť = insidePart S T <;> by_cases hA : A Ť <;>
    simp [h, hA]

theorem outsideMass_eq (B : Finset R.Piece → Prop) (T : Finset (Sym2 (Fin n))) :
    R.outsideMass (S := S) B T
      = ∑ Ťo ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = outsidePart S T),
          (if B Ťo then ∏ p ∈ Ťo, R.q p else 0) := by
  unfold outsideMass
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases h : R.IsTransversal Ť ∧ R.project Ť = outsidePart S T <;> by_cases hB : B Ť <;>
    simp [h, hB]

/-- **The kernel factors.**  Over a tree `T`, the `q`-mass of the transversals
satisfying an inside-determined `A` and an outside-determined `B` is the
product of the inside mass of `A` and the outside mass of `B`: split each
transversal into its two parts, note `A` sees only the inside part and `B`
only the outside part, and `∏ q` is multiplicative over the disjoint union. -/
theorem sum_transversals_factor {A B : Finset R.Piece → Prop}
    (hA : R.RefinedInsideDetermined S A) (hB : R.RefinedOutsideDetermined S B)
    (T : Finset (Sym2 (Fin n))) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T ∧ (A Ť ∧ B Ť)),
        ∏ p ∈ Ť, R.q p
      = R.insideMass (S := S) A T * R.outsideMass (S := S) B T := by
  -- move the event into the summand, split, and factor
  have hL : ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T ∧ (A Ť ∧ B Ť)),
        ∏ p ∈ Ť, R.q p
      = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
          (if A Ť ∧ B Ť then ∏ p ∈ Ť, R.q p else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Ť _ => ?_
    by_cases h1 : R.IsTransversal Ť ∧ R.project Ť = T <;> by_cases h2 : A Ť ∧ B Ť <;>
      simp [h1, h2]
  rw [hL, R.sum_transversals_split (S := S) T, R.insideMass_eq, R.outsideMass_eq,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun Ťi hi => Finset.sum_congr rfl fun Ťo ho => ?_
  obtain ⟨-, -, hpi⟩ := Finset.mem_filter.mp hi
  obtain ⟨-, -, hpo⟩ := Finset.mem_filter.mp ho
  -- `A` on the glue is `A` on the inside member; `B` likewise on the outside member
  have hAi : A (Ťi ∪ Ťo) ↔ A Ťi := hA _ _ (by
    rw [R.insidePieces_union_of_parts hpi hpo, R.insidePieces_eq_self_of_project hpi])
  have hBo : B (Ťi ∪ Ťo) ↔ B Ťo := hB _ _ (by
    rw [R.outsidePieces_union_of_parts hpi hpo, R.outsidePieces_eq_self_of_project hpo])
  have hprod : ∏ p ∈ Ťi ∪ Ťo, R.q p = (∏ p ∈ Ťi, R.q p) * ∏ p ∈ Ťo, R.q p :=
    Finset.prod_union (R.disjoint_of_project_parts hpi hpo)
  by_cases ha : A Ťi <;> by_cases hb : B Ťo <;> simp [hAi, hBo, ha, hb, hprod]

/-! ### Disintegration of a lifted event -/

/-- The lifted mass of an event, disintegrated over projections: `w T` times
the `q`-mass of the transversals over `T` satisfying it. -/
theorem weightMass_liftWeight_eq (w : Finset (Sym2 (Fin n)) → ℝ) (E : Finset R.Piece → Prop) :
    weightMass (R.liftWeight w) E
      = ∑ T : Finset (Sym2 (Fin n)), w T *
          ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T ∧ E Ť),
            ∏ p ∈ Ť, R.q p := by
  unfold weightMass
  rw [← Finset.sum_fiberwise Finset.univ R.project]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases hE : E Ť <;> by_cases hproj : R.project Ť = T <;> by_cases htr : R.IsTransversal Ť
    <;> simp [hE, hproj, htr, liftWeight]

/-- A lifted event of the form `A ∧ B ∧ "S induces a tree"` is the base
integral, over "S induces a tree", of the product of the inside mass of `A`
and the outside mass of `B`. -/
theorem weightMass_liftWeight_inside_outside (w : Finset (Sym2 (Fin n)) → ℝ)
    {A B : Finset R.Piece → Prop}
    (hA : R.RefinedInsideDetermined S A) (hB : R.RefinedOutsideDetermined S B) :
    weightMass (R.liftWeight w) (fun Ť => A Ť ∧ B Ť ∧ R.RefinedInducesTreeOn S Ť)
      = eventInt w (InducesTreeOn S)
          (fun T => R.insideMass (S := S) A T * R.outsideMass (S := S) B T) := by
  rw [R.weightMass_liftWeight_eq]
  unfold eventInt
  refine Finset.sum_congr rfl fun T _ => ?_
  dsimp only
  by_cases hI : InducesTreeOn S T
  · rw [if_pos hI, ← R.sum_transversals_factor hA hB T]
    congr 1
    -- the two filters agree on `T`'s fiber: the refined tree conjunct is
    -- implied there.  Compared pointwise, to stay clear of the decidability
    -- instances the two filter terms carry.
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Ť _ => ?_
    by_cases h : R.IsTransversal Ť ∧ R.project Ť = T ∧ (A Ť ∧ B Ť)
    · have h' : R.IsTransversal Ť ∧ R.project Ť = T ∧ A Ť ∧ B Ť ∧ R.RefinedInducesTreeOn S Ť :=
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h.1, by rw [h.2.1]; exact hI⟩
      rw [if_pos h', if_pos h]
    · have h' : ¬ (R.IsTransversal Ť ∧ R.project Ť = T ∧ A Ť ∧ B Ť ∧ R.RefinedInducesTreeOn S Ť) :=
        fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩
      rw [if_neg h', if_neg h]
  · rw [if_neg hI]
    refine mul_eq_zero_of_right _ ?_
    rw [Finset.sum_filter]
    refine Finset.sum_eq_zero fun Ť _ => ?_
    rw [if_neg]
    rintro ⟨-, hproj, -, -, -, hI'⟩
    exact hI (hproj ▸ hI')

/-- Replacing a factor by `1` on the support of `w` does not change the integral. -/
theorem eventInt_congr_support {w : Finset (Sym2 (Fin n)) → ℝ}
    {C : Finset (Sym2 (Fin n)) → Prop} {a b : Finset (Sym2 (Fin n)) → ℝ}
    (h : ∀ T, w T ≠ 0 → a T = b T) : eventInt w C a = eventInt w C b := by
  unfold eventInt
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs
  · by_cases hw : w T = 0
    · rw [hw, zero_mul, zero_mul]
    · rw [h T hw]
  · rfl

/-! ### The transport -/

/-- **Fact 2.8 transports to the lifted law.**  Disintegrate the four lifted
masses over projections; each becomes a base integral over "S induces a tree"
of a product of inside and outside copy masses; the unconditioned masses are
`1` on the support; and the identity is base Fact 2.8 for the determined
functions `insideMass A` and `outsideMass B`. -/
theorem treeCondIndep_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (hf : TreeCondIndep w) :
    R.RefinedTreeCondIndep (R.liftWeight w) := by
  intro S A B hA hB
  unfold RefinedCondIndepCross
  have hTrueIn : R.RefinedInsideDetermined S (fun _ => True) := fun _ _ _ => Iff.rfl
  have hTrueOut : R.RefinedOutsideDetermined S (fun _ => True) := fun _ _ _ => Iff.rfl
  -- the four masses, disintegrated
  have h1 := R.weightMass_liftWeight_inside_outside w hA hB
  have h2 := R.weightMass_liftWeight_inside_outside w hTrueIn hTrueOut
  have h3 := R.weightMass_liftWeight_inside_outside w hA hTrueOut
  have h4 := R.weightMass_liftWeight_inside_outside w hTrueIn hB
  -- align the event shapes with the cross identity's
  have e2 : R.RefinedInducesTreeOn S
      = fun Ť => True ∧ True ∧ R.RefinedInducesTreeOn S Ť := by
    funext Ť; simp
  have e3 : (fun Ť => A Ť ∧ R.RefinedInducesTreeOn S Ť)
      = fun Ť => A Ť ∧ True ∧ R.RefinedInducesTreeOn S Ť := by
    funext Ť; simp
  have e4 : (fun Ť => B Ť ∧ R.RefinedInducesTreeOn S Ť)
      = fun Ť => True ∧ B Ť ∧ R.RefinedInducesTreeOn S Ť := by
    funext Ť; simp
  rw [h1, e3, h3, e4, h4, e2, h2]
  -- the unconditioned masses are `1` on the support of `w`
  have hsupp : ∀ T, w T ≠ 0 → T ⊆ edgeFinset n := fun T h => hw T h
  rw [eventInt_congr_support (a := fun T => R.insideMass (S := S) (fun _ => True) T
        * R.outsideMass (S := S) (fun _ => True) T) (b := fun _ => (1 : ℝ))
      (fun T hT => by rw [R.insideMass_true (hsupp T hT), R.outsideMass_true (hsupp T hT), mul_one]),
    eventInt_congr_support (a := fun T => R.insideMass (S := S) A T
        * R.outsideMass (S := S) (fun _ => True) T) (b := R.insideMass (S := S) A)
      (fun T hT => by rw [R.outsideMass_true (hsupp T hT), mul_one]),
    eventInt_congr_support (a := fun T => R.insideMass (S := S) (fun _ => True) T
        * R.outsideMass (S := S) B T) (b := R.outsideMass (S := S) B)
      (fun T hT => by rw [R.insideMass_true (hsupp T hT), one_mul])]
  exact hf.functional S (R.insideMass_insideFunctionDetermined A)
    (R.outsideMass_outsideFunctionDetermined B)

end TSPGap.EdgeRefinement

namespace TSPGap

/-- **The export.**  The max-entropy limit's lift to any refinement satisfies
Fact 2.8 on pieces: `IsMaxEntropyLimit` is consumed only on the base, through
`hμ.treeCondIndep`, and transported. -/
theorem IsMaxEntropyLimit.refinedTreeCondIndep {n : ℕ} {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ} (R : EdgeRefinement x D ε₁) :
    R.RefinedTreeCondIndep (R.liftProb μ) := by
  rw [R.liftProb_eq_liftWeight μ]
  exact R.treeCondIndep_liftWeight (fun T hT => μ.support_subset_edgeFinset hT) hμ.treeCondIndep

end TSPGap

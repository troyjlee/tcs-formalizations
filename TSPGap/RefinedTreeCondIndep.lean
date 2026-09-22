/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedLawData
import TSPGap.Fact28

/-!
# Fact 2.8 on pieces: the scaffolding

Step 2 of the narrow migration.  KKO21 Fact 2.8 — conditional independence of
inside- and outside-determined events given "`S` induces a tree" — is
`TreeCondIndep` on the base (`Fact28.lean`), obtained from the max-entropy
limit.  The piece-native top layer needs it for events on piece sets, which
are *not* projection-determined: a degree partition on pieces can distinguish
two copies of one base edge.  So Fact 2.8 is not reused through
`weightMass_liftWeight_project`; it is **transported** through the product
kernel, and this file is the combinatorics that transport rests on.

* A piece is inside or outside `S` according to its base edge alone
  (`insidePieces`, `outsidePieces`), and projection commutes with the split.
* **Topology is read only through the projection**: `RefinedInducesTreeOn`
  is "transversal, and the projection induces a tree".  No graph is ever built
  on pieces; gluing reduces to the base `InducesTreeOn.glue`.
* **Transversals over `T` are pairs** of a transversal over `insidePart S T`
  and one over `outsidePart S T` (`sum_transversals_split`) — the
  section-splitting companion to `sum_transversals_prod`, which is what lets
  inside and outside copy choices be summed independently.
* The refined determinacy predicates and cross identity, via the generic
  `weightMass`.

The transport theorem itself, `treeCondIndep_liftWeight`, follows in the next
file once Fact 2.8 is available for determined *functions*.
-/

namespace TSPGap.EdgeRefinement

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- The pieces of `Ť` whose base edge lies inside `S`. -/
noncomputable def insidePieces (S : Finset (Fin n)) (Ť : Finset R.Piece) : Finset R.Piece :=
  Ť.filter fun p => ∀ v ∈ R.base p, v ∈ S

/-- The pieces of `Ť` whose base edge leaves `S`. -/
noncomputable def outsidePieces (S : Finset (Fin n)) (Ť : Finset R.Piece) : Finset R.Piece :=
  Ť.filter fun p => ¬ ∀ v ∈ R.base p, v ∈ S

variable {S : Finset (Fin n)} {Ť : Finset R.Piece}

theorem insidePieces_subset : R.insidePieces S Ť ⊆ Ť := Finset.filter_subset _ _
theorem outsidePieces_subset : R.outsidePieces S Ť ⊆ Ť := Finset.filter_subset _ _

theorem insidePieces_union_outsidePieces :
    R.insidePieces S Ť ∪ R.outsidePieces S Ť = Ť :=
  Finset.filter_union_filter_not_eq _ _

theorem disjoint_insidePieces_outsidePieces :
    Disjoint (R.insidePieces S Ť) (R.outsidePieces S Ť) :=
  Finset.disjoint_filter_filter_not _ _ _

theorem project_insidePieces :
    R.project (R.insidePieces S Ť) = insidePart S (R.project Ť) := by
  unfold project insidePieces insidePart
  rw [Finset.filter_image]

theorem project_outsidePieces :
    R.project (R.outsidePieces S Ť) = outsidePart S (R.project Ť) := by
  unfold project outsidePieces outsidePart
  rw [Finset.filter_image]

/-- A piece set projecting inside `S` consists of inside pieces. -/
theorem insidePieces_eq_self_of_project {Ť : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hproj : R.project Ť = insidePart S F) : R.insidePieces S Ť = Ť := by
  refine Finset.filter_true_of_mem fun p hp => ?_
  have : R.base p ∈ insidePart S F := hproj ▸ R.mem_project.mpr ⟨p, hp, rfl⟩
  exact (Finset.mem_filter.mp this).2

theorem outsidePieces_eq_self_of_project {Ť : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hproj : R.project Ť = outsidePart S F) : R.outsidePieces S Ť = Ť := by
  refine Finset.filter_true_of_mem fun p hp => ?_
  have : R.base p ∈ outsidePart S F := hproj ▸ R.mem_project.mpr ⟨p, hp, rfl⟩
  exact (Finset.mem_filter.mp this).2

theorem outsidePieces_eq_empty_of_project {Ť : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hproj : R.project Ť = insidePart S F) : R.outsidePieces S Ť = ∅ := by
  unfold outsidePieces
  rw [Finset.filter_eq_empty_iff]
  intro p hp hnot
  have : R.base p ∈ insidePart S F := hproj ▸ R.mem_project.mpr ⟨p, hp, rfl⟩
  exact hnot (Finset.mem_filter.mp this).2

theorem insidePieces_eq_empty_of_project {Ť : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hproj : R.project Ť = outsidePart S F) : R.insidePieces S Ť = ∅ := by
  unfold insidePieces
  rw [Finset.filter_eq_empty_iff]
  intro p hp hin
  have : R.base p ∈ outsidePart S F := hproj ▸ R.mem_project.mpr ⟨p, hp, rfl⟩
  exact (Finset.mem_filter.mp this).2 hin

/-- Gluing an inside transversal and an outside transversal is transversal. -/
theorem isTransversal_union_of_parts {Ťi Ťo : Finset R.Piece} {F : Finset (Sym2 (Fin n))}
    (hi : R.IsTransversal Ťi) (ho : R.IsTransversal Ťo)
    (hpi : R.project Ťi = insidePart S F) (hpo : R.project Ťo = outsidePart S F) :
    R.IsTransversal (Ťi ∪ Ťo) := by
  intro p hp p' hp' hb
  rw [Finset.mem_coe, Finset.mem_union] at hp hp'
  have hin : ∀ p ∈ Ťi, ∀ v ∈ R.base p, v ∈ S := fun p hp =>
    (Finset.mem_filter.mp (hpi ▸ R.mem_project.mpr ⟨p, hp, rfl⟩ : R.base p ∈ insidePart S F)).2
  have hout : ∀ p ∈ Ťo, ¬ ∀ v ∈ R.base p, v ∈ S := fun p hp =>
    (Finset.mem_filter.mp (hpo ▸ R.mem_project.mpr ⟨p, hp, rfl⟩ : R.base p ∈ outsidePart S F)).2
  rcases hp with hp | hp <;> rcases hp' with hp' | hp'
  · exact hi (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hp') hb
  · exact absurd (hin p hp) (hb ▸ hout p' hp')
  · exact absurd (hin p' hp') (hb.symm ▸ hout p hp)
  · exact ho (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hp') hb

/-- The base parts reassemble. -/
theorem insidePart_union_outsidePart (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    insidePart S T ∪ outsidePart S T = T :=
  Finset.filter_union_filter_not_eq _ _

/-- **Transversals over `T` are pairs of transversals over its parts.**  The
sum of any summand over transversals projecting onto `T` is the double sum
over (transversal over `insidePart S T`, transversal over `outsidePart S T`) of
the summand at their union. -/
theorem sum_transversals_split {M : Type*} [AddCommMonoid M] (T : Finset (Sym2 (Fin n)))
    (g : Finset R.Piece → M) :
    ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T), g Ť
      = ∑ Ťi ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = insidePart S T),
          ∑ Ťo ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = outsidePart S T),
            g (Ťi ∪ Ťo) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun P => P.1 ∪ P.2) (fun Ť => (R.insidePieces S Ť, R.outsidePieces S Ť))
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · -- a pair glues to a transversal over `T`
    rintro ⟨Ťi, Ťo⟩ hP
    obtain ⟨hi, ho⟩ := Finset.mem_product.mp hP
    obtain ⟨-, hti, hpi⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, hto, hpo⟩ := Finset.mem_filter.mp ho
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, R.isTransversal_union_of_parts hti hto hpi hpo, ?_⟩
    show (Ťi ∪ Ťo).image R.base = T
    rw [Finset.image_union]
    change R.project Ťi ∪ R.project Ťo = T
    rw [hpi, hpo, insidePart_union_outsidePart]
  · -- a transversal over `T` splits into a pair
    intro Ť hŤ
    obtain ⟨-, htr, hproj⟩ := Finset.mem_filter.mp hŤ
    refine Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          htr.mono (Finset.coe_subset.mpr R.insidePieces_subset), ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          htr.mono (Finset.coe_subset.mpr R.outsidePieces_subset), ?_⟩⟩
    · rw [R.project_insidePieces, hproj]
    · rw [R.project_outsidePieces, hproj]
  · -- left inverse: split then glue
    rintro ⟨Ťi, Ťo⟩ hP
    obtain ⟨hi, ho⟩ := Finset.mem_product.mp hP
    obtain ⟨-, -, hpi⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, -, hpo⟩ := Finset.mem_filter.mp ho
    simp only [Prod.mk.injEq]
    constructor
    · unfold insidePieces
      rw [Finset.filter_union, ← insidePieces, ← insidePieces, R.insidePieces_eq_self_of_project hpi,
        R.insidePieces_eq_empty_of_project hpo, Finset.union_empty]
    · unfold outsidePieces
      rw [Finset.filter_union, ← outsidePieces, ← outsidePieces, R.outsidePieces_eq_empty_of_project hpi,
        R.outsidePieces_eq_self_of_project hpo, Finset.empty_union]
  · -- right inverse: glue then split
    intro Ť _
    exact R.insidePieces_union_outsidePieces

/-! ### Gluing, and topology through the projection -/

variable {Ť₁ Ť₂ : Finset R.Piece}

/-- **Gluing transversals is transversal.**  A piece of the inside part of `Ť₁`
and a piece of the outside part of `Ť₂` cannot share a base edge — that edge
would be both inside and not inside `S` — and within each part injectivity is
inherited. -/
theorem isTransversal_glue (h₁ : R.IsTransversal Ť₁) (h₂ : R.IsTransversal Ť₂) :
    R.IsTransversal (R.insidePieces S Ť₁ ∪ R.outsidePieces S Ť₂) := by
  intro p hp p' hp' hb
  rw [Finset.mem_coe, Finset.mem_union] at hp hp'
  rcases hp with hp | hp <;> rcases hp' with hp' | hp'
  · exact h₁ (Finset.mem_coe.mpr (Finset.mem_filter.mp hp).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hp').1) hb
  · exact absurd ((Finset.mem_filter.mp hp).2) (hb ▸ (Finset.mem_filter.mp hp').2)
  · exact absurd ((Finset.mem_filter.mp hp').2) (hb ▸ (Finset.mem_filter.mp hp).2)
  · exact h₂ (Finset.mem_coe.mpr (Finset.mem_filter.mp hp).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hp').1) hb

/-! ### Topology, read only through the projection -/

/-- **`S` induces a tree in a refined tree**: the piece set is a transversal and
its projection induces a tree in the base sense.  No graph is ever built on
pieces. -/
def RefinedInducesTreeOn (S : Finset (Fin n)) (Ť : Finset R.Piece) : Prop :=
  R.IsTransversal Ť ∧ InducesTreeOn S (R.project Ť)

/-- **Gluing preserves the refined tree property**: transversality by
`isTransversal_glue`, and the topology by projecting the glue to the base glue
and applying `InducesTreeOn.glue`. -/
theorem RefinedInducesTreeOn.glue (h₁ : R.RefinedInducesTreeOn S Ť₁)
    (h₂ : R.RefinedInducesTreeOn S Ť₂) :
    R.RefinedInducesTreeOn S (R.insidePieces S Ť₁ ∪ R.outsidePieces S Ť₂) := by
  refine ⟨R.isTransversal_glue h₁.1 h₂.1, ?_⟩
  have : R.project (R.insidePieces S Ť₁ ∪ R.outsidePieces S Ť₂)
      = insidePart S (R.project Ť₁) ∪ outsidePart S (R.project Ť₂) := by
    unfold project
    rw [Finset.image_union]
    exact congrArg₂ (· ∪ ·) R.project_insidePieces R.project_outsidePieces
  rw [this]
  exact InducesTreeOn.glue h₁.2 h₂.2

/-! ### Determinacy and the cross identity, on pieces -/

/-- An event on piece sets that depends only on the inside pieces. -/
def RefinedInsideDetermined (S : Finset (Fin n)) (A : Finset R.Piece → Prop) : Prop :=
  ∀ Ť Ť', R.insidePieces S Ť = R.insidePieces S Ť' → (A Ť ↔ A Ť')

/-- An event on piece sets that depends only on the outside pieces. -/
def RefinedOutsideDetermined (S : Finset (Fin n)) (B : Finset R.Piece → Prop) : Prop :=
  ∀ Ť Ť', R.outsidePieces S Ť = R.outsidePieces S Ť' → (B Ť ↔ B Ť')

/-- **The conditional-independence cross identity on pieces**, via the generic
`weightMass`. -/
def RefinedCondIndepCross (f : Finset R.Piece → ℝ) (A B C : Finset R.Piece → Prop) : Prop :=
  weightMass f (fun Ť => A Ť ∧ B Ť ∧ C Ť) * weightMass f C
    = weightMass f (fun Ť => A Ť ∧ C Ť) * weightMass f (fun Ť => B Ť ∧ C Ť)

/-- **Fact 2.8 on pieces.** -/
def RefinedTreeCondIndep (f : Finset R.Piece → ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (A B : Finset R.Piece → Prop),
    R.RefinedInsideDetermined S A → R.RefinedOutsideDetermined S B →
      R.RefinedCondIndepCross f A B (R.RefinedInducesTreeOn S)

end TSPGap.EdgeRefinement

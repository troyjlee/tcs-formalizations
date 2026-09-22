/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NestedFace
import TSPGap.LawPackage

/-!
# Face conditioning as a law package

`LawPackage.lean` packages avoiding a set and presenting a one-hot set.  This
file adds the **general maximum-face conditioning** `faceDist ν (𝟙_F) m`
(`LawData.face`), with the four normalized marginal bounds of `MaxFace`
(`face_inside_ge/le`, `face_outside_le/ge`), the mass bound and unwinding,
and the general-cost mass identities.

For tree laws, `TreeLawData` carries the spanning-tree support along a chain
of conditionings; `TreeLawData.face` conditions an atom `X` to induce a tree
(the maximum face of `E(X)` at `|X| − 1`, the forest bound being the support
condition) and `TreeLawData.face_supp` reads the tree event off the support.
Lemma 5.16's nested law is four such steps (`NestedChain.lean`).
-/

namespace TSPGap
open Finset

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem faceWeight_ne_zero_imp {w : Finset ι → ℝ} {c : ι → ℕ} {m : ℕ} {S : Finset ι}
    (h : faceWeight w c m S ≠ 0) : w S ≠ 0 ∧ setCost c S = m := by
  rw [faceWeight_apply] at h
  split at h
  · exact ⟨h, ‹_›⟩
  · exact absurd rfl h

theorem faceDist_ne_zero_imp {w : Finset ι → ℝ} {c : ι → ℕ} {m : ℕ} {S : Finset ι}
    (h : faceDist w c m S ≠ 0) : w S ≠ 0 ∧ setCost c S = m :=
  faceWeight_ne_zero_imp (faceDist_ne_zero h)

/-- The unnormalized face mass of an event, for a general cost. -/
theorem weightMass_faceWeight (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) (Q : Finset ι → Prop) :
    weightMass (faceWeight w c m) Q = weightMass w (fun S => Q S ∧ setCost c S = m) := by
  classical
  unfold weightMass
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [faceWeight_apply]
  by_cases hQ : Q S <;> by_cases hc : setCost c S = m <;> simp [hQ, hc]

theorem totalMass_faceWeight (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) :
    totalMass (faceWeight w c m) = weightMass w (fun S => setCost c S = m) := by
  rw [← weightMass_true (faceWeight w c m), weightMass_faceWeight]
  exact weightMass_congr fun S => by simp

/-- `E[D] = E[D ∩ F] + E[D ∖ F]`. -/
theorem expCard_inter_add_sdiff (w : Finset ι → ℝ) (D F : Finset ι) :
    expCard w D = expCard w (D ∩ F) + expCard w (D \ F) := by
  conv_lhs => rw [← Finset.sdiff_union_inter D F]
  rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter D F), add_comm]

/-! ### The general maximum-face conditioning -/

/-- **Conditioning on a maximum face** preserves the package. -/
theorem LawData.face {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {F : Finset ι} {m : ℕ}
    (hsup : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight ν (indicatorCost F) m)) :
    LawData (faceDist ν (indicatorCost F) m) r where
  st := isRealStable_genPoly_maxFaceDist h.st h.rank h.nn hsup hmass
  rank := fun S hS => by
    by_contra hc
    exact hS ((fixedRankNormalized_faceDist (r := r) h.rank h.nn hmass).supported S hc)
  nn := (fixedRankNormalized_faceDist (r := r) h.rank h.nn hmass).nonneg
  tot := (fixedRankNormalized_faceDist (r := r) h.rank h.nn hmass).total

theorem LawData.face_mass_ge {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {F : Finset ι}
    {m : ℕ} (hsup : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ m) :
    1 - faceDeficiency ν F m ≤ totalMass (faceWeight ν (indicatorCost F) m) :=
  one_sub_faceDeficiency_le_faceMass h.nn h.tot hsup

/-- Inside the face, counts go up. -/
theorem LawData.face_inside_ge {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {F : Finset ι}
    {m : ℕ} (hsup : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight ν (indicatorCost F) m)) {A : Finset ι} (hA : A ⊆ F) :
    expCard ν A ≤ expCard (faceDist ν (indicatorCost F) m) A := by
  rw [expCard_faceDist, le_div_iff₀ hmass]
  exact expCard_face_inside_lower h.st h.rank h.nn h.tot hsup hA

/-- Inside the face, counts go up by at most the deficiency. -/
theorem LawData.face_inside_le {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {F : Finset ι}
    {m : ℕ} (hsup : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight ν (indicatorCost F) m)) {A : Finset ι} (hA : A ⊆ F) :
    expCard (faceDist ν (indicatorCost F) m) A ≤ expCard ν A + faceDeficiency ν F m := by
  rw [expCard_faceDist, div_le_iff₀ hmass]
  exact expCard_face_inside_upper h.st h.rank h.nn h.tot hsup hA

/-- Outside the face, counts go down. -/
theorem LawData.face_outside_le {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {F : Finset ι}
    {m : ℕ} (hsup : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight ν (indicatorCost F) m)) {B : Finset ι} (hB : B ⊆ Fᶜ) :
    expCard (faceDist ν (indicatorCost F) m) B ≤ expCard ν B := by
  rw [expCard_faceDist, div_le_iff₀ hmass]
  exact expCard_face_outside_upper h.st h.rank h.nn h.tot hsup hB

/-- Outside the face, counts go down by at most the deficiency. -/
theorem LawData.face_outside_ge {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {F : Finset ι}
    {m : ℕ} (hsup : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight ν (indicatorCost F) m)) {B : Finset ι} (hB : B ⊆ Fᶜ) :
    expCard ν B - faceDeficiency ν F m ≤ expCard (faceDist ν (indicatorCost F) m) B := by
  rw [expCard_faceDist, le_div_iff₀ hmass]
  exact expCard_face_outside_lower h.st h.rank h.nn h.tot hsup hB

theorem LawData.face_unwind {ν : Finset ι → ℝ} {r : ℕ} (_h : LawData ν r) {F : Finset ι}
    {m : ℕ} (hmass : 0 < totalMass (faceWeight ν (indicatorCost F) m)) (P : Finset ι → Prop) :
    weightMass (faceDist ν (indicatorCost F) m) P * totalMass (faceWeight ν (indicatorCost F) m)
      = weightMass ν (fun T => P T ∧ (T ∩ F).card = m) := by
  rw [weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_face]

/-- A set disjoint from `F` lies in `Fᶜ`. -/
theorem subset_compl_of_disjoint {B F : Finset ι} (h : Disjoint B F) : B ⊆ Fᶜ :=
  fun e he => Finset.mem_compl.mpr fun hF => Finset.disjoint_left.mp h he hF

omit [DecidableEq ι] in
/-- The mass of the second face, measured in the first face law, times the
first face mass is the mass of the summed face. -/
theorem totalMass_faceWeight_faceDist (w : Finset ι → ℝ) {c₁ c₂ : ι → ℕ} {m₁ m₂ : ℕ}
    (hsup : ∀ S, w S ≠ 0 → setCost c₁ S ≤ m₁ ∧ setCost c₂ S ≤ m₂)
    (hM : totalMass (faceWeight w c₁ m₁) ≠ 0) :
    totalMass (faceWeight (faceDist w c₁ m₁) c₂ m₂) * totalMass (faceWeight w c₁ m₁)
      = totalMass (faceWeight w (fun i => c₁ i + c₂ i) (m₁ + m₂)) := by
  have h1 : faceDist w c₁ m₁
      = fun S => (totalMass (faceWeight w c₁ m₁))⁻¹ * faceWeight w c₁ m₁ S := by
    funext S; rw [faceDist, div_eq_inv_mul]
  rw [h1, faceWeight_smul, totalMass_smul, faceWeight_faceWeight w hsup, mul_comm,
    ← mul_assoc, mul_inv_cancel₀ hM, one_mul]

end Generic

/-! ### Tree laws -/

section Tree

variable {n : ℕ}

/-- A law package supported on spanning trees. -/
structure TreeLawData (ν : Finset (Sym2 (Fin n)) → ℝ) (r : ℕ) : Prop where
  law : LawData ν r
  tree : ∀ T, ν T ≠ 0 → IsSpanningTree n T

/-- The forest bound is the support condition of the tree face of `X`. -/
theorem TreeLawData.face_sup {ν : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ} (h : TreeLawData ν r)
    {X : Finset (Fin n)} (hX : X.Nonempty) :
    ∀ T, ν T ≠ 0 → (T ∩ internalEdges X).card ≤ X.card - 1 := by
  intro T hT
  have := card_internal_inter_add_one_le (h.tree T hT) hX
  rw [Finset.inter_comm]
  omega

/-- **Conditioning an atom to induce a tree** preserves the tree package. -/
theorem TreeLawData.face {ν : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ} (h : TreeLawData ν r)
    {X : Finset (Fin n)} (hX : X.Nonempty)
    (hmass : 0 < totalMass (faceWeight ν (indicatorCost (internalEdges X)) (X.card - 1))) :
    TreeLawData (faceDist ν (indicatorCost (internalEdges X)) (X.card - 1)) r where
  law := h.law.face (h.face_sup hX) hmass
  tree := fun T hT => h.tree T (faceDist_ne_zero_imp hT).1

/-- The support of the tree face: the base law's support, and `X` induces a
tree. -/
theorem TreeLawData.face_supp {ν : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ} (h : TreeLawData ν r)
    {X : Finset (Fin n)} (hX : X.Nonempty) {T : Finset (Sym2 (Fin n))}
    (hT : faceDist ν (indicatorCost (internalEdges X)) (X.card - 1) T ≠ 0) :
    ν T ≠ 0 ∧ InducesTreeOn X T := by
  obtain ⟨hν, hc⟩ := faceDist_ne_zero_imp hT
  refine ⟨hν, (inducesTreeOn_iff_card (h.tree T hν) X).mpr ?_⟩
  rw [setCost_indicatorCost, Finset.inter_comm] at hc
  have hpos : 1 ≤ X.card := Finset.card_pos.mpr hX
  omega

end Tree

end TSPGap

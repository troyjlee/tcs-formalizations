/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Blocks
import IPPSPACE.QBF.FiniteReachability

/-!
# Succinct QBFs for repeated squaring of a relation

The recursive reachability formula occurs only once at each level. An
existential midpoint and two universally quantified endpoint blocks select
either half of the path. This avoids the exponential duplication in writing
two recursive reachability formulas directly.

The theorem is parameterized by a concrete base-edge formula and its exact
semantics. Constructing that formula for a machine's bounded configurations,
and proving the encoded reduction polynomial-time, are separate obligations.
No PSPACE-hardness statement is asserted here.
-/

namespace IPPSPACE

open Complexity

/-- Repeated relational squaring: level `depth` describes `2^depth` base edges. -/
def squareReach {α : Type*} (edge : α → α → Prop) : ℕ → α → α → Prop
  | 0, a, b => edge a b
  | depth + 1, a, b => ∃ middle, squareReach edge depth a middle ∧ squareReach edge depth middle b

/-- Repeated squaring is exactly an exponentially long path, not an assumption
about reachability hidden in the base relation. -/
theorem squareReach_iff_pathLength {α : Type*} (edge : α → α → Prop)
    (depth : ℕ) (a b : α) :
    squareReach edge depth a b ↔ pathLength edge (2 ^ depth) a b := by
  induction depth generalizing a b with
  | zero => simp [squareReach, pathLength]
  | succ depth ih =>
    rw [pow_succ, Nat.mul_two, pathLength_add]
    simp only [squareReach, ih]

/-- Universally selecting either endpoint pair checks both halves without
duplicating a formula representing `relation`. -/
theorem forall_selected_pair_iff {α : Type*} (relation : α → α → Prop) (a middle b : α) :
    (∀ u v, ((u = a ∧ v = middle) ∨ (u = middle ∧ v = b)) → relation u v) ↔
      relation a middle ∧ relation middle b := by
  constructor
  · intro h
    exact ⟨h a middle (Or.inl ⟨rfl, rfl⟩), h middle b (Or.inr ⟨rfl, rfl⟩)⟩
  · rintro ⟨hleft, hright⟩ u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hleft
    · exact hright

/-- A gate selecting the pair `(a,middle)` or `(middle,b)`. -/
def selectedPair {width : ℕ} (a middle b u v : Fin width → ℕ) : QBF :=
  .disj (.conj (blockEquality u a) (blockEquality v middle))
    (.conj (blockEquality u middle) (blockEquality v b))

theorem eval_selectedPair {width : ℕ} (a middle b u v : Fin width → ℕ)
    (assignment : ℕ → Bool) :
    (selectedPair a middle b u v).eval assignment = true ↔
      (assignment ∘ u = assignment ∘ a ∧ assignment ∘ v = assignment ∘ middle) ∨
        (assignment ∘ u = assignment ∘ middle ∧ assignment ∘ v = assignment ∘ b) := by
  simp [selectedPair, QBF.eval, eval_blockEquality]

@[simp] theorem nodeCount_selectedPair {width : ℕ} (a middle b u v : Fin width → ℕ) :
    nodeCount (selectedPair a middle b u v) = 40 * width + 7 := by
  simp [selectedPair, nodeCount]
  omega

theorem eval_reachImplication (premise conclusion : QBF) (assignment : ℕ → Bool) :
    (QBF.disj (.neg premise) conclusion).eval assignment = true ↔
      (premise.eval assignment = true → conclusion.eval assignment = true) := by
  simp only [QBF.eval]
  cases premise.eval assignment <;> cases conclusion.eval assignment <;> decide

/-- Three fresh blocks at each level: midpoint, universally selected left
endpoint, and universally selected right endpoint. There is one recursive copy. -/
def reachFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF) :
    ℕ → ℕ → (Fin width → ℕ) → (Fin width → ℕ) → QBF
  | 0, _, a, b => edgeFormula a b
  | depth + 1, fresh, a, b =>
      let middle := blockNames fresh width
      let u := blockNames (fresh + width) width
      let v := blockNames (fresh + 2 * width) width
      existsBlock fresh width
        (forallBlock (fresh + width) width
          (forallBlock (fresh + 2 * width) width
            (.disj (.neg (selectedPair a middle b u v))
              (reachFormula width edgeFormula depth (fresh + 3 * width) u v))))

/-- The three block quantifiers preserve the old endpoints and independently
choose exactly the midpoint and the two new endpoint vectors. -/
theorem reachBlock_assignments {width : ℕ} (fresh : ℕ) (a b : Fin width → ℕ)
    (ha : ∀ i, a i < fresh) (hb : ∀ i, b i < fresh)
    (middle u v : Fin width → Bool) (assignment : ℕ → Bool) :
    let updated := writeBlock (fresh + 2 * width) v
      (writeBlock (fresh + width) u (writeBlock fresh middle assignment))
    updated ∘ a = assignment ∘ a ∧ updated ∘ b = assignment ∘ b ∧
      updated ∘ blockNames fresh width = middle ∧
      updated ∘ blockNames (fresh + width) width = u ∧
      updated ∘ blockNames (fresh + 2 * width) width = v := by
  dsimp only
  have ha₂ : ∀ i, a i < fresh + 2 * width := fun i => by have := ha i; omega
  have ha₁ : ∀ i, a i < fresh + width := fun i => by have := ha i; omega
  have hb₂ : ∀ i, b i < fresh + 2 * width := fun i => by have := hb i; omega
  have hb₁ : ∀ i, b i < fresh + width := fun i => by have := hb i; omega
  have hm₂ : ∀ i, blockNames fresh width i < fresh + 2 * width := by
    intro i
    have := i.isLt
    dsimp [blockNames]
    omega
  have hm₁ : ∀ i, blockNames fresh width i < fresh + width := by
    intro i
    have := i.isLt
    dsimp [blockNames]
    omega
  have hu₂ : ∀ i, blockNames (fresh + width) width i < fresh + 2 * width := by
    intro i
    have := i.isLt
    dsimp [blockNames]
    omega
  rw [writeBlock_comp_before _ _ _ a ha₂, writeBlock_comp_before _ _ _ a ha₁,
    writeBlock_comp_before _ _ _ a ha,
    writeBlock_comp_before _ _ _ b hb₂, writeBlock_comp_before _ _ _ b hb₁,
    writeBlock_comp_before _ _ _ b hb,
    writeBlock_comp_before _ _ _ (blockNames fresh width) hm₂,
    writeBlock_comp_before _ _ _ (blockNames fresh width) hm₁,
    writeBlock_comp_before _ _ _ (blockNames (fresh + width) width) hu₂]
  simp

/-- Exact semantics of the succinct construction. The base formula hypothesis
states the local edge computation, not a reachability or complexity inclusion. -/
theorem eval_reachFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (hEdge : ∀ a b assignment,
      (edgeFormula a b).eval assignment = true ↔ edge (assignment ∘ a) (assignment ∘ b))
    (depth fresh : ℕ) (a b : Fin width → ℕ)
    (ha : ∀ i, a i < fresh) (hb : ∀ i, b i < fresh) (assignment : ℕ → Bool) :
    (reachFormula width edgeFormula depth fresh a b).eval assignment = true ↔
      squareReach edge depth (assignment ∘ a) (assignment ∘ b) := by
  induction depth generalizing fresh a b assignment with
  | zero => exact hEdge a b assignment
  | succ depth ih =>
    have hu : ∀ i, blockNames (fresh + width) width i < fresh + 3 * width := by
      intro i
      have := i.isLt
      dsimp [blockNames]
      omega
    have hv : ∀ i, blockNames (fresh + 2 * width) width i < fresh + 3 * width := by
      intro i
      have := i.isLt
      dsimp [blockNames]
      omega
    simp only [reachFormula, eval_existsBlock, eval_forallBlock]
    have hbody (middle u v : Fin width → Bool) :
        let updated := writeBlock (fresh + 2 * width) v
          (writeBlock (fresh + width) u (writeBlock fresh middle assignment))
        (QBF.disj (.neg (selectedPair a (blockNames fresh width) b
          (blockNames (fresh + width) width) (blockNames (fresh + 2 * width) width)))
          (reachFormula width edgeFormula depth (fresh + 3 * width)
            (blockNames (fresh + width) width) (blockNames (fresh + 2 * width) width))).eval
              updated = true ↔
          ((u = assignment ∘ a ∧ v = middle) ∨ (u = middle ∧ v = assignment ∘ b)) →
            squareReach edge depth u v := by
      dsimp only
      rw [eval_reachImplication, eval_selectedPair, ih _ _ _ hu hv]
      obtain ⟨ha', hb', hm', hu', hv'⟩ := reachBlock_assignments fresh a b ha hb middle u v assignment
      rw [ha', hb', hm', hu', hv']
    simp only [hbody, forall_selected_pair_iff, squareReach]

/-- Each squaring level adds `43 * width + 9` nodes. The recursive formula
appears once, so the total is linear in depth and width beyond the base size. -/
theorem nodeCount_reachFormula_le (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (baseSize : ℕ) (hEdge : ∀ a b, nodeCount (edgeFormula a b) ≤ baseSize)
    (depth fresh : ℕ) (a b : Fin width → ℕ) :
    nodeCount (reachFormula width edgeFormula depth fresh a b) ≤
      baseSize + depth * (43 * width + 9) := by
  induction depth generalizing fresh a b with
  | zero => simpa [reachFormula] using hEdge a b
  | succ depth ih =>
    have hrec := ih (fresh + 3 * width) (blockNames (fresh + width) width)
      (blockNames (fresh + 2 * width) width)
    simp only [reachFormula, nodeCount_existsBlock, nodeCount_forallBlock,
      nodeCount, nodeCount_selectedPair, Nat.add_mul, Nat.one_mul]
    omega

/-- Add idle steps to any edge formula using vector equality. -/
def stutterFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (a b : Fin width → ℕ) : QBF :=
  .disj (blockEquality a b) (edgeFormula a b)

theorem eval_stutterFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (hEdge : ∀ a b assignment,
      (edgeFormula a b).eval assignment = true ↔ edge (assignment ∘ a) (assignment ∘ b))
    (a b : Fin width → ℕ) (assignment : ℕ → Bool) :
    (stutterFormula width edgeFormula a b).eval assignment = true ↔
      stutterEdge edge (assignment ∘ a) (assignment ∘ b) := by
  simp [stutterFormula, QBF.eval_disj, eval_blockEquality, hEdge, stutterEdge]

/-- A depth equal to the configuration bit width covers all finite-state
reachability, after adding idle steps to the base-edge formula. -/
theorem eval_reachFormula_reachable (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (hEdge : ∀ a b assignment,
      (edgeFormula a b).eval assignment = true ↔ edge (assignment ∘ a) (assignment ∘ b))
    (fresh : ℕ) (a b : Fin width → ℕ)
    (ha : ∀ i, a i < fresh) (hb : ∀ i, b i < fresh) (assignment : ℕ → Bool) :
    (reachFormula width (stutterFormula width edgeFormula) width fresh a b).eval assignment = true ↔
      Relation.ReflTransGen edge (assignment ∘ a) (assignment ∘ b) := by
  rw [eval_reachFormula width _ (stutterEdge edge)
    (eval_stutterFormula width edgeFormula edge hEdge) width fresh a b ha hb assignment,
    squareReach_iff_pathLength]
  exact (bitStates_reachable_iff_pathLength width edge _ _).symm

/-- The finite-state reachability formula is quadratic in configuration width,
plus the cost of representing one edge. -/
theorem nodeCount_reachFormula_stutter_le (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (baseSize : ℕ) (hEdge : ∀ a b, nodeCount (edgeFormula a b) ≤ baseSize)
    (fresh : ℕ) (a b : Fin width → ℕ) :
    nodeCount (reachFormula width (stutterFormula width edgeFormula) width fresh a b) ≤
      baseSize + 10 * width + 2 + width * (43 * width + 9) := by
  apply nodeCount_reachFormula_le
  intro a b
  have h := hEdge a b
  simp only [stutterFormula, nodeCount, nodeCount_blockEquality]
  omega

/-- Bind two endpoint blocks to the supplied concrete source and target states,
then run the succinct finite-state reachability formula on those blocks. -/
def fixedEndpointReachFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (source target : Fin width → Bool) : QBF :=
  existsBlock 0 width (existsBlock width width
    (.conj (blockValues (blockNames 0 width) source)
      (.conj (blockValues (blockNames width width) target)
        (reachFormula width (stutterFormula width edgeFormula) width (2 * width)
          (blockNames 0 width) (blockNames width width)))))

/-- Fixing the endpoint bits gives an assignment-independent formula for the
actual reachability relation between the supplied finite states. -/
theorem eval_fixedEndpointReachFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (hEdge : ∀ a b assignment,
      (edgeFormula a b).eval assignment = true ↔ edge (assignment ∘ a) (assignment ∘ b))
    (source target : Fin width → Bool) (assignment : ℕ → Bool) :
    (fixedEndpointReachFormula width edgeFormula source target).eval assignment = true ↔
      Relation.ReflTransGen edge source target := by
  have hfirst : ∀ i, blockNames 0 width i < width := by
    intro i
    simp [blockNames]
  have ha : ∀ i, blockNames 0 width i < 2 * width := by
    intro i
    have := hfirst i
    omega
  have hb : ∀ i, blockNames width width i < 2 * width := by
    intro i
    have := i.isLt
    dsimp [blockNames]
    omega
  have hread (left right : Fin width → Bool) :
      writeBlock width right (writeBlock 0 left assignment) ∘ blockNames 0 width = left := by
    rw [writeBlock_comp_before _ _ _ _ hfirst, writeBlock_comp_blockNames]
  simp only [fixedEndpointReachFormula, eval_existsBlock, QBF.eval_conj,
    Bool.and_eq_true, eval_blockValues,
    eval_reachFormula_reachable width edgeFormula edge hEdge (2 * width) _ _ ha hb,
    hread, writeBlock_comp_blockNames]
  simp

theorem nodeCount_fixedEndpointReachFormula_le (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (baseSize : ℕ) (hEdge : ∀ a b, nodeCount (edgeFormula a b) ≤ baseSize)
    (source target : Fin width → Bool) :
    nodeCount (fixedEndpointReachFormula width edgeFormula source target) ≤
      baseSize + 18 * width + 6 + width * (43 * width + 9) := by
  have hreach := nodeCount_reachFormula_stutter_le width edgeFormula baseSize hEdge
    (2 * width) (blockNames 0 width) (blockNames width width)
  have hsource := nodeCount_blockValues_le (blockNames 0 width) source
  have htarget := nodeCount_blockValues_le (blockNames width width) target
  simp only [fixedEndpointReachFormula, nodeCount_existsBlock, nodeCount]
  omega

/-- A genuinely closed upstream QBF for reachability between two concrete bit
vectors. Closing removes irrelevant free names in a supplied edge formula too. -/
def closedReachabilityFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (source target : Fin width → Bool) : QBF :=
  closeQBF (fixedEndpointReachFormula width edgeFormula source target)

theorem closedReachabilityFormula_closed (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (source target : Fin width → Bool) :
    (closedReachabilityFormula width edgeFormula source target).Closed :=
  closeQBF_closed _

/-- Truth of the resulting closed QBF is exactly finite-state reachability.
The only representation premise is correctness of the local base-edge formula. -/
theorem closedReachabilityFormula_true_iff (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (hEdge : ∀ a b assignment,
      (edgeFormula a b).eval assignment = true ↔ edge (assignment ∘ a) (assignment ∘ b))
    (source target : Fin width → Bool) :
    (closedReachabilityFormula width edgeFormula source target).IsTrue ↔
      Relation.ReflTransGen edge source target :=
  eval_closeQBF_of_constant _ _
    (eval_fixedEndpointReachFormula width edgeFormula edge hEdge source target) _

/-- Closure and fixed endpoints preserve the quadratic configuration-width bound. -/
theorem nodeCount_closedReachabilityFormula_le (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (baseSize : ℕ) (hEdge : ∀ a b, nodeCount (edgeFormula a b) ≤ baseSize)
    (source target : Fin width → Bool) :
    nodeCount (closedReachabilityFormula width edgeFormula source target) ≤
      2 * (baseSize + 18 * width + 6 + width * (43 * width + 9)) :=
  (nodeCount_closeQBF_le _).trans (Nat.mul_le_mul_left 2
    (nodeCount_fixedEndpointReachFormula_le width edgeFormula baseSize hEdge source target))

end IPPSPACE

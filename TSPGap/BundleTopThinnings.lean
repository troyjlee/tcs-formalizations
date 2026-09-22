/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleGoodness
import TSPGap.RefinedTopThinnings

/-!
# Top thinning certificates with an explicit goodness policy

The policy determines good pairs and the bad-mass alternative. Events,
uniform thinnings and degree sides remain on pieces. The case-three pair
shares one thinning, and rectangularity is retained at both endpoints.
The legacy conversions preserve the events and thinnings exactly.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {D : Finset (Sym2 (Fin n))} {eps : ℝ}
variable (G : BundleGoodnessPolicy) (R : EdgeRefinement x D eps)

open Classical in
/-- The bad-mass alternative for the selected goodness policy. -/
def BadCase (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S u : Finset (Fin n)) : Prop :=
  1 / 2 - G.halfWidth ≤ ∑ v ∈ (H.siblings S u).filter (fun v => ¬ G.IsGood μ u v),
    pairSum x u v

/-- Exact legacy specialization of the bad-mass alternative. -/
theorem badCase_legacy (H : Hierarchy x e₀ eta) (μ : TreeDist n x)
    (h : ℝ) (S u : Finset (Fin n)) :
    (legacy h).BadCase H μ S u ↔ TSPGap.BadCase H μ h S u := Iff.rfl

/-- A single bad half bundle already supplies the bad-mass alternative. -/
theorem good_of_not_badCase (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (H : Hierarchy x e₀ eta) {S u v : Finset (Fin n)}
    (hnb : ¬ G.BadCase H μ S u) (hv : v ∈ H.siblings S u) : G.IsGood μ u v := by
  classical
  by_contra hng
  apply hnb
  exact (half_of_not_good hng).ge.trans
    (Finset.single_le_sum (f := fun v => pairSum x u v)
      (fun v _ => pairSum_nonneg hx.nonneg u v) (Finset.mem_filter.mpr ⟨hv, hng⟩))

/-- Endpoint happiness with the selected policy and arbitrary piece sides. -/
def HappyWrtOn (μ : TreeDist n x) (a : ℝ) (u v : Finset (Fin n))
    (P : R.DegreePartitionOn eta u) (T : Finset R.Piece) : Prop :=
  G.IsGood μ u v ∧
    ((R.IsTwoOneOneGoodOn μ a u v P.A P.B P.C ∧ R.TwoOneOneHappyOn u v P.A P.B P.C T)
      ∨ (¬ R.IsTwoOneOneGoodOn μ a u v P.A P.B P.C ∧ R.TwoTwoHappyOn u v T))

/-- Exact legacy specialization of endpoint happiness. -/
theorem happyWrtOn_legacy (μ : TreeDist n x) (h a : ℝ) (u v : Finset (Fin n))
    (P : R.DegreePartitionOn eta u) (T : Finset R.Piece) :
    (legacy h).HappyWrtOn R μ a u v P T ↔ R.HappyWrtOn μ h a u v P T := Iff.rfl

section HappyWrtOn

variable {G R} {μ : TreeDist n x} {p : ℝ} {u u' : Finset (Fin n)}
  {P : R.DegreePartitionOn eta u} {Ť : Finset R.Piece}

theorem HappyWrtOn.good (h : G.HappyWrtOn R μ p u u' P Ť) : G.IsGood μ u u' := h.1

/-- A reduced bundle has two pieces over `δ(u)` at its reducing endpoint. -/
theorem HappyWrtOn.card_eq_two (h : G.HappyWrtOn R μ p u u' P Ť) :
    (Ť ∩ R.piecesOver (cutEdges u)).card = 2 := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.card_eq_two P
  · exact h.1

/-- A reduced bundle has two pieces over `δ(u')` at its other endpoint too. -/
theorem HappyWrtOn.card_eq_two' (h : G.HappyWrtOn R μ p u u' P Ť) :
    (Ť ∩ R.piecesOver (cutEdges u')).card = 2 := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.2.2.2.1
  · exact h.2.1

/-- Both atoms of a reduced bundle induce trees in the projection. -/
theorem HappyWrtOn.inducesTree (h : G.HappyWrtOn R μ p u u' P Ť) :
    InducesTree u (R.project Ť) ∧ InducesTree u' (R.project Ť) := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  · exact ⟨h.2.2.1, h.2.2.2⟩

/-- **No reduction at an odd atom**: the piece count over `δ(u)` is even on
`H_{e,u}`. -/
theorem HappyWrtOn.not_odd (h : G.HappyWrtOn R μ p u u' P Ť) :
    ¬ Odd (Ť ∩ R.piecesOver (cutEdges u)).card := by
  rw [h.card_eq_two]
  decide

/-- On a transversal the parity of the piece count is the parity of the base
count, so the base "odd atom" hypothesis is what is read. -/
theorem HappyWrtOn.not_odd_project (htr : R.IsTransversal Ť)
    (h : G.HappyWrtOn R μ p u u' P Ť) : ¬ Odd (R.project Ť ∩ cutEdges u).card := by
  rw [← R.card_inter_piecesOver_of_transversal htr]
  exact h.not_odd

/-- The 2-2-2 event lies in `H_{e,u}` for a good bundle that is not 2-1-1 good. -/
theorem HappyWrtOn.of_twoTwoTwo {f : Finset (Fin n)} (hg : G.IsGood μ u u')
    (hn : ¬ R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C) (h : R.TwoTwoTwoHappyOn u' u f Ť) :
    G.HappyWrtOn R μ p u u' P Ť :=
  ⟨hg, Or.inr ⟨hn, h.twoTwoHappyOn_left⟩⟩

end HappyWrtOn

/-- The ordinary piece event supplies policy-specific endpoint happiness. -/
theorem happyEventOn_happyWrtOn {μ : TreeDist n x} {a : ℝ} {u v : Finset (Fin n)}
    {P : R.DegreePartitionOn eta u} {T : Finset R.Piece}
    (hg : G.IsGood μ u v) (hT : R.happyEventOn μ a u v P T) :
    G.HappyWrtOn R μ a u v P T := by
  classical
  unfold EdgeRefinement.happyEventOn EdgeRefinement.happyEventOfOn at hT
  split_ifs at hT with h211
  · exact ⟨hg, Or.inl ⟨h211, hT⟩⟩
  · exact ⟨hg, Or.inr ⟨h211, hT⟩⟩

structure TopThinningsOn (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S : Finset (Fin n))
    (p : ℝ) (P : R.DegreePartitionsOn H) where
  /-- The event `E_{e,u}` the thinning of the ordered pair `(u, u')` is uniform over. -/
  event : Finset (Fin n) → Finset (Fin n) → Finset R.Piece → Prop
  /-- The thinning `R_{e,u}` of the ordered pair `(u, u')`. -/
  thin : Finset (Fin n) → Finset (Fin n) → Finset R.Piece → ℝ
  /-- A good ordered pair carries a uniform thinning of the lifted law at mass `p`. -/
  uniform : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → G.IsGood μ u u' →
    IsUniformThinning (R.liftProb μ) (thin u u') (event u u') p
  /-- The event lies in KKO's `H_{e,u}`, on pieces. -/
  event_happy : ∀ u, ∀ hu : u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    ∀ Ť, event u u' Ť → G.HappyWrtOn R μ p u u' (P.get u (H.mem_cuts_of_mem_children hu)) Ť
  /-- Outside the good ordered pairs of atoms the thinning is zero. -/
  thin_eq_zero : ∀ u u',
    ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u') → thin u u' = 0
  /-- **Case (iii) coherence** on pieces. -/
  coherent : ∀ u, ∀ hu : u ∈ H.children S, ¬ G.BadCase H μ S u →
    ¬ R.TwoOneOneCaseOn H μ G.halfWidth S u p (P.get u (H.mem_cuts_of_mem_children hu)) →
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f
      ∧ IsHalfBundle x G.halfWidth u e ∧ IsHalfBundle x G.halfWidth u f
      ∧ ∑ g ∈ R.piecesOver (betweenEdges u e)
          ∩ (P.get u (H.mem_cuts_of_mem_children hu)).B, R.weight g ≤ G.halfWidth
      ∧ ∑ g ∈ R.piecesOver (betweenEdges u f)
          ∩ (P.get u (H.mem_cuts_of_mem_children hu)).A, R.weight g ≤ G.halfWidth
      ∧ (∀ Ť, event u e Ť ↔ R.TwoTwoTwoHappyOn e u f Ť)
      ∧ (∀ Ť, event u f Ť ↔ R.TwoTwoTwoHappyOn e u f Ť)
      ∧ thin u f = thin u e

/-- **The rectangularity certificate of a `TopThinningsOn`**, in the piece sense. -/
structure TopRectangularOn {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {S : Finset (Fin n)}
    {p : ℝ} {P : R.DegreePartitionsOn H} (Θ : G.TopThinningsOn R H μ S p P) : Prop where
  /-- Rectangular at the reducing endpoint. -/
  rect_fst : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    R.IsRectangularAtOn u (Θ.event u u')
  /-- Rectangular at the other endpoint. -/
  rect_snd : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    R.IsRectangularAtOn u' (Θ.event u u')

/-- Convert a legacy-policy certificate without changing its event or thinning. -/
def TopThinningsOn.toLegacy {R : EdgeRefinement x D eps} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {S : Finset (Fin n)} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (Θ : (legacy h).TopThinningsOn R H μ S a P) : R.TopThinningsOn H μ S h a P :=
  ⟨Θ.event, Θ.thin, Θ.uniform, Θ.event_happy, Θ.thin_eq_zero, Θ.coherent⟩

/-- Recover the policy certificate from the original legacy datum. -/
def TopThinningsOn.ofLegacy {R : EdgeRefinement x D eps} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {S : Finset (Fin n)} {h a : ℝ} {P : R.DegreePartitionsOn H}
    (Θ : R.TopThinningsOn H μ S h a P) : (legacy h).TopThinningsOn R H μ S a P :=
  ⟨Θ.event, Θ.thin, Θ.uniform, Θ.event_happy, Θ.thin_eq_zero, Θ.coherent⟩

theorem TopThinningsOn.toLegacy_ofLegacy {R : EdgeRefinement x D eps}
    {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {S : Finset (Fin n)} {h a : ℝ}
    {P : R.DegreePartitionsOn H} (Θ : R.TopThinningsOn H μ S h a P) :
    (TopThinningsOn.ofLegacy Θ).toLegacy = Θ := by cases Θ; rfl

theorem TopThinningsOn.ofLegacy_toLegacy {R : EdgeRefinement x D eps}
    {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {S : Finset (Fin n)} {h a : ℝ}
    {P : R.DegreePartitionsOn H} (Θ : (legacy h).TopThinningsOn R H μ S a P) :
    TopThinningsOn.ofLegacy Θ.toLegacy = Θ := by cases Θ; rfl

/-- The legacy conversion preserves both rectangularity certificates. -/
theorem TopRectangularOn.legacy_iff {R : EdgeRefinement x D eps}
    {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {S : Finset (Fin n)} {h a : ℝ}
    {P : R.DegreePartitionsOn H} (Θ : (legacy h).TopThinningsOn R H μ S a P) :
    (legacy h).TopRectangularOn R Θ ↔ R.TopRectangularOn Θ.toLegacy := by
  constructor <;> intro hΘ <;> exact ⟨hΘ.rect_fst, hΘ.rect_snd⟩

end TSPGap.BundleGoodnessPolicy

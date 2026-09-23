/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Claim75

/-!
# KKO21 Claim 7.4

For a descendant cut `d ⊊ U` carrying almost all of a side —
`x(δ(d) ∩ δ(U)) ≥ 1 − ε₁` — and a thinning uniform over an event rectangular
at `U` and supported on 2-1-1 happy trees,

`W_v[δ(d)_T odd] ≤ p · (2ε_η + ε₁)`.

The geometry comes from `DegreePartition.ControlsDescendants`, whose
alternative is split **explicitly**: one of `A`, `B` lies inside `δ(d) ∩ δ(U)`
and the other misses `δ(d)`.  In *either* orientation 2-1-1 happiness makes the
crossing count exactly one (`card_crossing_eq_one_of_sides`): the contained side
forces it to be at least one, and `δ(d) ∩ δ(U)` avoiding the other side leaves
only that side and `C`, which is not met at all.

So `δ(d)_T = D_in + 1`, and `δ(d)_T` is odd exactly when `D_in` is **even**.
Since `D_in ≥ 1` almost surely at the tree face, an even `D_in` costs two —
that is `weightMass_even_add_total_le_expCard`, a shifted Markov bound —
so `W_face[D_in even] ≤ E_face[D_in] − 1`, and the face mean is at most
`1 + 2ε_η + ε₁`.  `IsRectangularAt.thin_weightMass_le` moves that to the
thinning.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Shifted Markov -/

/-- **Shifted Markov at level one.**  If the count over `D` is at least one on
the support, the even outcomes cost two, so
`W[D even] + total ≤ E[D]`.  ⚠️ Belongs beside `weightMass_hit_le_expCard` in
`Conditioning`; kept here to avoid a rebuild of that file's deep cone. -/
theorem weightMass_even_add_total_le_expCard {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : Finset ι → ℝ} (hnn : WeightNonneg w) {D : Finset ι}
    (hone : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ D).card) :
    weightMass w (fun S => Even (S ∩ D).card) + totalMass w ≤ expCard w D := by
  classical
  rw [weightMass, totalMass, expCard, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases hS : w S = 0
  · rw [hS]
    split_ifs <;> simp
  · have h1 := hone S hS
    by_cases he : Even (S ∩ D).card
    · rw [if_pos he]
      have h2 : 2 ≤ (S ∩ D).card := by rw [Nat.even_iff] at he; omega
      have hc : (2:ℝ) ≤ ((S ∩ D).card : ℝ) := by exact_mod_cast h2
      nlinarith [hnn S]
    · rw [if_neg he]
      have hc : (1:ℝ) ≤ ((S ∩ D).card : ℝ) := by exact_mod_cast h1
      nlinarith [hnn S]

/-! ### The crossing count is exactly one -/

/-- **Either orientation of `ControlsDescendants` pins the crossing count.**
`A` inside `δ(d) ∩ δ(U)` makes it at least one; `B` missing `δ(d)` leaves only
`A` and `C` available, and `C` is not met. -/
theorem card_crossing_eq_one_of_sides {U d : Finset (Fin n)}
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges U = (A ∪ B) ∪ C)
    (hsub : A ⊆ cutEdges d ∩ cutEdges U) (hdisj : Disjoint B (cutEdges d))
    {T : Finset (Sym2 (Fin n))} (hA : (T ∩ A).card = 1) (hC : (T ∩ C).card = 0) :
    (T ∩ (cutEdges d ∩ cutEdges U)).card = 1 := by
  classical
  have hle : T ∩ (cutEdges d ∩ cutEdges U) ⊆ (T ∩ A) ∪ (T ∩ C) := by
    intro g hg
    obtain ⟨hgT, hg2⟩ := Finset.mem_inter.mp hg
    obtain ⟨hgd, hgU⟩ := Finset.mem_inter.mp hg2
    rw [hpart] at hgU
    rcases Finset.mem_union.mp hgU with hab | hc
    · rcases Finset.mem_union.mp hab with ha2 | hb
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hgT, ha2⟩)
      · exact absurd hgd (fun hd => Finset.disjoint_left.mp hdisj hb hd)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hgT, hc⟩)
  have hup : (T ∩ (cutEdges d ∩ cutEdges U)).card ≤ 1 := by
    calc (T ∩ (cutEdges d ∩ cutEdges U)).card
        ≤ ((T ∩ A) ∪ (T ∩ C)).card := Finset.card_le_card hle
      _ ≤ (T ∩ A).card + (T ∩ C).card := Finset.card_union_le _ _
      _ = 1 := by rw [hA, hC]
  have hlow : 1 ≤ (T ∩ (cutEdges d ∩ cutEdges U)).card := by
    rw [← hA]
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hsub)
  omega

/-! ### The claim -/

set_option maxHeartbeats 400000 in
-- the face law package, the shifted Markov bound and the mean in one chain
/-- **KKO21 Claim 7.4**, in the consumer form.  ⚠️ The 2-1-1 support is taken as
a hypothesis rather than read off a `TopThinnings`: the caller supplies it from
`event_happy` together with the bundle's 2-1-1 goodness, which keeps this
statement free of the thinning-datum plumbing. -/
theorem claim_7_4 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {εη ε₁ : ℝ} (H : Hierarchy x e₀ εη)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {U d : Finset (Fin n)} (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hdne : d.Nonempty)
    (hdU : d ⊂ U)
    (hd : d ∈ H.cuts) (hUcut : cutSum x U ≤ 2 + εη) (hdcut : cutSum x d ≤ 2 + εη)
    {P : DegreePartition x ε₁ εη U} (hctrl : P.ControlsDescendants H)
    (hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges d ∩ cutEdges U, x g)
    {E : Finset (Sym2 (Fin n)) → Prop} (hE : IsRectangularAt U E)
    {v : Finset (Sym2 (Fin n)) → ℝ} {p : ℝ} (hv : IsUniformThinning μ.prob v E p)
    (hsupp : ∀ T, v T ≠ 0 →
      (T ∩ P.A).card = 1 ∧ (T ∩ P.B).card = 1 ∧ (T ∩ P.C).card = 0) :
    weightMass v (fun T => Odd (T ∩ cutEdges d).card) ≤ p * (2 * εη + ε₁) := by
  classical
  -- the law package at the tree face of `U`
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsup := hbase.face_sup hUne
  have hdefle : faceDeficiency μ.prob (internalEdges U) (U.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hUne hU0]; linarith
  have hmassge := hbase.law.face_mass_ge hsup
  have hmass : 0 <
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges U)) (U.card - 1)) := by
    linarith
  have hFlaw : LawData (treeFace μ.prob U) (n - 1) := (hbase.face hUne hmass).law
  -- the crossing count is exactly one on the support of `v`
  have hcard1 : ∀ T, v T ≠ 0 → (T ∩ (cutEdges d ∩ cutEdges U)).card = 1 := by
    intro T hT
    obtain ⟨hA, hB, hC⟩ := hsupp T hT
    rcases hctrl d hd hdU hcross with ⟨hsub, hdisj⟩ | ⟨hsub, hdisj⟩
    · exact card_crossing_eq_one_of_sides P.part hsub hdisj hA hC
    · refine card_crossing_eq_one_of_sides (A := P.B) (B := P.A) (C := P.C) ?_ hsub hdisj hB hC
      rw [P.part, Finset.union_comm P.A P.B]
  -- so `δ(d)_T` is odd exactly when the inside count is even
  have hcongr : weightMass v (fun T => Odd (T ∩ cutEdges d).card)
      = weightMass v (fun T => Even (T ∩ (cutEdges d ∩ internalEdges U)).card) := by
    refine weightMass_congr_of_support fun T hT => ?_
    have hsp := card_split_of_subcut hdU.subset T
    rw [hsp, hcard1 T hT]
    simp only [Nat.odd_iff, Nat.even_iff]
    omega
  rw [hcongr]
  -- the face mean of the inside count
  have hxDin : expCard μ.prob (cutEdges d ∩ internalEdges U)
      = ∑ e ∈ cutEdges d ∩ internalEdges U, x e :=
    expCard_prob_eq_sum μ (Finset.inter_subset_right.trans (internalEdges_subset_edgeFinset U))
  have hsplit : cutSum x d = (∑ e ∈ cutEdges d ∩ internalEdges U, x e)
      + ∑ e ∈ cutEdges d ∩ cutEdges U, x e := by
    conv_lhs => rw [cutSum, cutEdges_eq_din_union_dout hdU.subset]
    exact Finset.sum_union (din_disjoint_dout U d)
  have hface_le : expCard (treeFace μ.prob U) (cutEdges d ∩ internalEdges U)
      ≤ expCard μ.prob (cutEdges d ∩ internalEdges U)
        + faceDeficiency μ.prob (internalEdges U) (U.card - 1) :=
    hbase.law.face_inside_le hsup hmass Finset.inter_subset_right
  have hmean : expCard (treeFace μ.prob U) (cutEdges d ∩ internalEdges U)
      ≤ 1 + 2 * εη + ε₁ := by
    rw [hxDin] at hface_le; linarith
  -- shifted Markov at the face
  have hshift := weightMass_even_add_total_le_expCard hFlaw.nn
    (D := cutEdges d ∩ internalEdges U)
    (fun T hT => one_le_card_din_treeFace hUne hdne hdU hT)
  rw [hFlaw.tot] at hshift
  -- move it to the thinning
  refine hE.thin_weightMass_le μ hμ hUne hmass hv
    (insideDetermined_inter (fun g hg w hw =>
      (mem_internalEdges.mp (Finset.mem_inter.mp hg).2).2 w hw) (fun X => Even X.card)) ?_
  linarith

end TSPGap

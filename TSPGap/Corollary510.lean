/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Observation432
import TSPGap.OddCount

/-!
# KKO21 Corollary 5.10

`P[δ(u)_T odd | E_S] ≤ 0.5678` for a cut `u` nested in a polygon cut `S`.

The crossing edges split as `δ(u) = D_in ⊔ D_out` with
`D_in = δ(u) ∩ E(S)` and `D_out = δ(u) ∩ δ(S)`
(`cutEdges_subset_internal_union_cut`, `cutEdges_disjoint_internalEdges_self`).
Observation 4.32 puts `D_out` inside `A ∪ C` or `B ∪ C`, and on the support of
the max-flow selection `A_T = B_T = 1` and `C_T = 0`, so
**`|T ∩ D_out| ≤ 1`** (`card_dout_le_one`).  Writing `X = |T ∩ D_in|`,

`δ(u)_T odd  ⟺  (D_out = 0 ∧ X odd) ∨ (D_out = 1 ∧ X even)`

on that support, and `X`'s parity is *inside*-determined while `D_out`'s count
is *outside*-determined, so `weightMass_selected_cross` splits the mass into
`a·b₀ + (1 − a)·b₁` — which, at `β = b₁/M`, is exactly `odd_split_le`'s
`a(1 − 2β) + β`.  The two branches then use `oddCount_le` (`β ≤ 1/2`) and
`oddCount_ge` (`β > 1/2`), both applied to `X` under the polygon law `ν`,
which is stable and normalized.

The deviation of the mean from `2` is carried **symbolically** as `d`; the
consumer supplies `d = ε_M + O(ε_η)`, comfortably inside the `0.0005` that
`odd_split_le_num` needs.

Both analytic inputs of `corollary_5_10_core` are discharged in this file:
`weightMass_din_eq_zero` (`X ≥ 1` almost surely under `ν` — `S` induces a tree
and `∅ ≠ u ⊊ S`, so the induced tree joins `u` to `S ∖ u`) and
`mean_bounds_of_part` (Corollary 5.9(ii)/(iii), at deviation
`d = ε_M + 4.5ε_η`).  `corollary_5_10` is the wrapper that picks the part `P`
from Observation 4.32 and feeds them in.

The two transfer lemmas `tv_subset` and `expCard_union_face_avoid` are stated
generically and are reused by Corollary 5.11.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Generic count facts -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An event that fails on the support has no mass.  (The companion
`expCard_eq_weightMass_one` is already in `Lemma227Bundle`.) -/
theorem weightMass_eq_zero_of_support {w : Finset ι → ℝ} {P : Finset ι → Prop}
    (h : ∀ T, w T ≠ 0 → ¬ P T) : weightMass w P = 0 := by
  classical
  unfold weightMass
  refine Finset.sum_eq_zero fun T _ => ?_
  by_cases hw : w T = 0
  · rw [hw]
    split_ifs <;> rfl
  · rw [if_neg (h T hw)]

end Generic

/-! ### The inside crossing is almost sure -/

/-- **The induced tree joins `u` to `S ∖ u`.**  If `T` induces a tree on `S`
and `∅ ≠ u ⊊ S`, then `δ(u) ∩ E(S)` is met — the crossing-edge argument of
`BundleSetup.exists_crossing_edge`, run *inside* `S` on a walk of
`insidePart S T` rather than of `T`. -/
theorem one_le_card_din {T : Finset (Sym2 (Fin n))} {S u : Finset (Fin n)}
    (hT : InducesTreeOn S T) (hune : u.Nonempty) (huS : u ⊂ S) :
    1 ≤ (T ∩ (cutEdges u ∩ internalEdges S)).card := by
  classical
  obtain ⟨p, hp⟩ := hune
  obtain ⟨q, hqS, hqu⟩ := Finset.exists_of_ssubset huS
  have hpS : p ∈ S := huS.subset hp
  obtain ⟨w⟩ := hT.2.2 p hpS q hqS
  obtain ⟨e, hep, hecut⟩ := exists_crossing_edge w hp hqu
  have heIn : e ∈ insidePart S T := by
    have hw := w.edges_subset_edgeSet hep
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hw
    simpa using hw.1
  rw [insidePart_eq_internalEdges_inter hT.1.1 S] at heIn
  obtain ⟨heInt, heT⟩ := Finset.mem_inter.mp heIn
  exact Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨heT,
    Finset.mem_inter.mpr ⟨hecut, heInt⟩⟩⟩

/-- **Corollary 5.10's first hypothesis**: under the polygon law the inside
crossing count never vanishes. -/
theorem weightMass_din_eq_zero {μ : TreeDist n x} {S u : Finset (Fin n)}
    {C : Finset (Sym2 (Fin n))} (hSne : S.Nonempty) (hune : u.Nonempty) (huS : u ⊂ S) :
    weightMass (polygonLaw μ S C)
      (fun T => (T ∩ (cutEdges u ∩ internalEdges S)).card = 0) = 0 := by
  classical
  refine weightMass_eq_zero_of_support fun T hT => ?_
  have h1 : treeFace μ.prob S T ≠ 0 := (avoidDist_ne_zero_imp hT).1
  obtain ⟨hprob, hcost⟩ := faceDist_ne_zero_imp h1
  have hTst := μ.support_spanningTree T hprob
  rw [setCost_indicatorCost] at hcost
  have h1S : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hcard : (internalEdges S ∩ T).card + 1 = S.card := by
    rw [Finset.inter_comm]
    omega
  have hind : InducesTreeOn S T := (inducesTreeOn_iff_card hTst S).mpr hcard
  have := one_le_card_din hind hune huS
  omega

/-- Under the polygon law, `C` is never met. -/
theorem expCard_polygonLaw_eq_zero (μ : TreeDist n x) (S : Finset (Fin n))
    (C : Finset (Sym2 (Fin n))) : expCard (polygonLaw μ S C) C = 0 := by
  classical
  unfold expCard
  refine Finset.sum_eq_zero fun T _ => ?_
  by_cases hT : polygonLaw μ S C T = 0
  · rw [hT]; ring
  · rw [(avoidDist_ne_zero_imp hT).2]
    norm_num

/-! ### Two reusable transfer lemmas

Both are used by Corollary 5.10 and again by Corollary 5.11. -/

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Subset total variation.**  Proposition 5.6's bound over `A` restricts to
any `D ⊆ A`: the selected expected count is within `ζ·M` of `M` times the
law's. -/
theorem tv_subset {v ν : Finset ι → ℝ} {A D : Finset ι} {ζ : ℝ} (hDA : D ⊆ A)
    (htv : ∑ e ∈ A, |weightMass v (fun T => e ∈ T)
        - totalMass v * weightMass ν (fun T => e ∈ T)| ≤ ζ * totalMass v) :
    |expCard v D - totalMass v * expCard ν D| ≤ ζ * totalMass v := by
  classical
  have hrw : expCard v D - totalMass v * expCard ν D
      = ∑ e ∈ D, (weightMass v (fun T => e ∈ T)
          - totalMass v * weightMass ν (fun T => e ∈ T)) := by
    rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.mul_sum,
      Finset.sum_sub_distrib]
  rw [hrw]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ htv)
  exact Finset.sum_le_sum_of_subset_of_nonneg hDA fun e _ _ => abs_nonneg _

/-- **The face-then-avoid transfer of a mixed union.**  Taking `D_in ⊆ F` and
`D_sel ⊆ Fᶜ` *together* charges the face deficiency once with the two signs
cancelling — inside counts rise, outside counts fall — and charges `C` once,
instead of once per piece. -/
theorem expCard_union_face_avoid {w : Finset ι → ℝ} {r : ℕ} (law : LawData w r)
    {F C Din Dsel : Finset ι} {m : ℕ}
    (hsup : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ m)
    (hmass : 0 < totalMass (faceWeight w (indicatorCost F) m))
    (hmass₂ : 0 < totalMass (avoidWeight (faceDist w (indicatorCost F) m) C))
    (hDinF : Din ⊆ F) (hDselF : Dsel ⊆ Fᶜ) (hCF : C ⊆ Fᶜ)
    (hUC : Disjoint (Din ∪ Dsel) C) (hd : Disjoint Din Dsel) :
    expCard w Din + expCard w Dsel - faceDeficiency w F m
        ≤ expCard (avoidDist (faceDist w (indicatorCost F) m) C) (Din ∪ Dsel)
      ∧ expCard (avoidDist (faceDist w (indicatorCost F) m) C) (Din ∪ Dsel)
        ≤ expCard w Din + expCard w Dsel + faceDeficiency w F m + expCard w C := by
  have hlaw₁ : LawData (faceDist w (indicatorCost F) m) r := law.face hsup hmass
  have hsplit : expCard (faceDist w (indicatorCost F) m) (Din ∪ Dsel)
      = expCard (faceDist w (indicatorCost F) m) Din
        + expCard (faceDist w (indicatorCost F) m) Dsel :=
    expCard_union_of_disjoint _ hd
  have hin1 := law.face_inside_ge hsup hmass hDinF
  have hin2 := law.face_inside_le hsup hmass hDinF
  have hout1 := law.face_outside_ge hsup hmass hDselF
  have hout2 := law.face_outside_le hsup hmass hDselF
  have hCle := law.face_outside_le hsup hmass hCF
  have hav1 := hlaw₁.avoid_ge hUC hmass₂
  have hav2 := hlaw₁.avoid_le hUC hmass₂
  constructor <;> linarith

end Transfer

/-! ### The crossing count is at most one -/

/-- On the support of the selection, `δ(u)` meets `δ(S)` at most once: one of
`A`, `B` misses `δ(u)` (Observation 4.32), the other is met exactly once, and
`C` is not met at all. -/
theorem card_dout_le_one {εη : ℝ} {S u : Finset (Fin n)}
    {N : NearCycle x εη} (hroot : N.root = Sᶜ)
    (hAB : Disjoint (cutEdges u) N.partA ∨ Disjoint (cutEdges u) N.partB)
    {T : Finset (Sym2 (Fin n))} (hA : (T ∩ N.partA).card = 1) (hB : (T ∩ N.partB).card = 1)
    (hC : (T ∩ N.partC).card = 0) :
    (T ∩ (cutEdges u ∩ cutEdges S)).card ≤ 1 := by
  classical
  have hpart : N.partA ∪ N.partB ∪ N.partC = cutEdges S := by
    rw [N.partA_union_partB_union_partC, hroot, cutEdges_compl]
  -- the crossing edges of `u` avoid one of `A`, `B`, so they sit in the other plus `C`
  have hkey : ∀ (P Q : Finset (Sym2 (Fin n))), Disjoint (cutEdges u) Q →
      N.partA ∪ N.partB ∪ N.partC = cutEdges S →
      (P = N.partA ∧ Q = N.partB) ∨ (P = N.partB ∧ Q = N.partA) →
      T ∩ (cutEdges u ∩ cutEdges S) ⊆ (T ∩ P) ∪ (T ∩ N.partC) := by
    intro P Q hQ hpart' hPQ g hg
    obtain ⟨hgT, hg2⟩ := Finset.mem_inter.mp hg
    obtain ⟨hgu, hgS⟩ := Finset.mem_inter.mp hg2
    have hgQ : g ∉ Q := fun hc => Finset.disjoint_left.mp hQ hgu hc
    rw [← hpart'] at hgS
    rcases Finset.mem_union.mp hgS with hAB' | hCg
    · rcases Finset.mem_union.mp hAB' with hA' | hB'
      · rcases hPQ with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hgT, hA'⟩)
        · exact absurd hA' hgQ
      · rcases hPQ with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hB' hgQ
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hgT, hB'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hgT, hCg⟩)
  have hbound : ∀ P : Finset (Sym2 (Fin n)), (T ∩ P).card = 1 →
      T ∩ (cutEdges u ∩ cutEdges S) ⊆ (T ∩ P) ∪ (T ∩ N.partC) →
      (T ∩ (cutEdges u ∩ cutEdges S)).card ≤ 1 := by
    intro P hP hsub
    calc (T ∩ (cutEdges u ∩ cutEdges S)).card
        ≤ ((T ∩ P) ∪ (T ∩ N.partC)).card := Finset.card_le_card hsub
      _ ≤ (T ∩ P).card + (T ∩ N.partC).card := Finset.card_union_le _ _
      _ = 1 := by rw [hP, hC]
  rcases hAB with h | h
  · exact hbound N.partB hB (hkey N.partB N.partA h hpart (Or.inr ⟨rfl, rfl⟩))
  · exact hbound N.partA hA (hkey N.partA N.partB h hpart (Or.inl ⟨rfl, rfl⟩))

/-! ### The count splits -/

theorem card_split_of_subcut {S u : Finset (Fin n)} (huS : u ⊆ S)
    (T : Finset (Sym2 (Fin n))) :
    (T ∩ cutEdges u).card
      = (T ∩ (cutEdges u ∩ internalEdges S)).card + (T ∩ (cutEdges u ∩ cutEdges S)).card := by
  classical
  have hd : Disjoint (T ∩ (cutEdges u ∩ internalEdges S)) (T ∩ (cutEdges u ∩ cutEdges S)) := by
    refine Finset.disjoint_left.mpr fun g h1 h2 => ?_
    have hi := (Finset.mem_inter.mp (Finset.mem_inter.mp h1).2).2
    have hc := (Finset.mem_inter.mp (Finset.mem_inter.mp h2).2).2
    exact Finset.disjoint_left.mp (cutEdges_disjoint_internalEdges_self S) hc hi
  have he : T ∩ cutEdges u
      = (T ∩ (cutEdges u ∩ internalEdges S)) ∪ (T ∩ (cutEdges u ∩ cutEdges S)) := by
    ext g
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hgT, hgu⟩
      rcases Finset.mem_union.mp (cutEdges_subset_internal_union_cut huS hgu) with h | h
      · exact Or.inl ⟨hgT, hgu, h⟩
      · exact Or.inr ⟨hgT, hgu, h⟩
    · rintro (⟨hgT, hgu, -⟩ | ⟨hgT, hgu, -⟩) <;> exact ⟨hgT, hgu⟩
  rw [he, Finset.card_union_of_disjoint hd]

/-! ### The mean transfer -/

/-- The two pieces of `δ(u)` and their union. -/
theorem cutEdges_eq_din_union_dout {S u : Finset (Fin n)} (huS : u ⊆ S) :
    cutEdges u = (cutEdges u ∩ internalEdges S) ∪ (cutEdges u ∩ cutEdges S) := by
  classical
  ext g
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · intro hgu
    rcases Finset.mem_union.mp (cutEdges_subset_internal_union_cut huS hgu) with h | h
    · exact Or.inl ⟨hgu, h⟩
    · exact Or.inr ⟨hgu, h⟩
  · rintro (⟨hgu, -⟩ | ⟨hgu, -⟩) <;> exact hgu

theorem din_disjoint_dout (S u : Finset (Fin n)) :
    Disjoint (cutEdges u ∩ internalEdges S) (cutEdges u ∩ cutEdges S) := by
  refine Finset.disjoint_left.mpr fun g h1 h2 => ?_
  exact Finset.disjoint_left.mp (cutEdges_disjoint_internalEdges_self S)
    (Finset.mem_inter.mp h2).2 (Finset.mem_inter.mp h1).2

/-- A subset of `E(S) ∪ δ(S)` splits into its inside and crossing parts. -/
theorem subset_eq_din_union_dout {S : Finset (Fin n)} {D : Finset (Sym2 (Fin n))}
    (hD : D ⊆ internalEdges S ∪ cutEdges S) :
    D = (D ∩ internalEdges S) ∪ (D ∩ cutEdges S) := by
  classical
  ext g
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · intro hg
    rcases Finset.mem_union.mp (hD hg) with h | h
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, h⟩
  · rintro (⟨hg, -⟩ | ⟨hg, -⟩) <;> exact hg

theorem disjoint_din_dout (S : Finset (Fin n)) (D : Finset (Sym2 (Fin n))) :
    Disjoint (D ∩ internalEdges S) (D ∩ cutEdges S) := by
  refine Finset.disjoint_left.mpr fun g h1 h2 => ?_
  exact Finset.disjoint_left.mp (cutEdges_disjoint_internalEdges_self S)
    (Finset.mem_inter.mp h2).2 (Finset.mem_inter.mp h1).2

set_option maxHeartbeats 2000000 in
-- the chain threads a dozen face/avoid comparisons through one `linarith`
/-- **The mean bounds for an arbitrary `D ⊆ δ(u)`**, at a chosen part `P`.
Transferring `D_in ∪ D_sel` through the face *and* the avoidance as one set
charges the deficiency once — with the two signs cancelling, since inside
counts rise and outside counts fall — and charges `C` once.  The deviation is
`ε_M + 3.5ε_η`, around `x(D)` itself; a caller that knows `x(D)` only to
within `ε_η` (as `δ(u)` is known, via `x(δ(u)) ≤ 2 + ε_η`) pays that on top. -/
theorem mean_bounds_of_subset_part {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S u : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    (hS0 : AvoidsRootEdge e₀ S) (huS : u ⊆ S)
    (hεη : 0 ≤ εη) (hScut : cutSum x S ≤ 2 + εη)
    {D : Finset (Sym2 (Fin n))} (hDu : D ⊆ cutEdges u)
    {P : Finset (Sym2 (Fin n))} (hPC : Disjoint P N.partC)
    (htv : ∑ e ∈ P, |weightMass v (fun T => e ∈ T)
        - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)|
      ≤ 0.00025 * totalMass v)
    (hsel : (D ∩ cutEdges S) \ P ⊆ N.partC)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1) :
    (∑ e ∈ D, x e) - (0.00025 + 3.5 * εη)
        ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ∧ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
        ≤ (∑ e ∈ D, x e) + (0.00025 + 3.5 * εη) := by
  classical
  have hMpos : 0 < totalMass v := by
    by_contra hc
    push_neg at hc
    nlinarith [hb.mass, hb.cst_pos]
  -- the three pieces
  have hcutdisj : Disjoint (cutEdges S) (internalEdges S) :=
    cutEdges_disjoint_internalEdges_self S
  have hCS : N.partC ⊆ cutEdges S := N.partC_subset_cutEdges hroot
  have hDinF : D ∩ internalEdges S ⊆ internalEdges S := Finset.inter_subset_right
  have hSelP : D ∩ cutEdges S ∩ P ⊆ P := Finset.inter_subset_right
  have hSelS : D ∩ cutEdges S ∩ P ⊆ cutEdges S :=
    Finset.inter_subset_left.trans Finset.inter_subset_right
  have hSelF : D ∩ cutEdges S ∩ P ⊆ (internalEdges S)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left hSelS hcutdisj)
  have hCF : N.partC ⊆ (internalEdges S)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left hCS hcutdisj)
  have hSelC : Disjoint (D ∩ cutEdges S ∩ P) N.partC :=
    Finset.disjoint_of_subset_left hSelP hPC
  have hDinC : Disjoint (D ∩ internalEdges S) N.partC :=
    Finset.disjoint_of_subset_left hDinF (Finset.disjoint_of_subset_right hCS hcutdisj.symm)
  have hd : Disjoint (D ∩ internalEdges S) (D ∩ cutEdges S ∩ P) :=
    Finset.disjoint_of_subset_right Finset.inter_subset_left (disjoint_din_dout S D)
  -- the `x`-masses
  have hxDin : expCard μ.prob (D ∩ internalEdges S)
      = ∑ e ∈ D ∩ internalEdges S, x e :=
    expCard_prob_eq_sum μ (hDinF.trans (internalEdges_subset_edgeFinset S))
  have hxSel : expCard μ.prob (D ∩ cutEdges S ∩ P)
      = ∑ e ∈ D ∩ cutEdges S ∩ P, x e :=
    expCard_prob_eq_sum μ (hSelS.trans (cutEdges_subset_edgeFinset S))
  have hxC : expCard μ.prob N.partC = ∑ e ∈ N.partC, x e :=
    expCard_prob_eq_sum μ (hCS.trans (cutEdges_subset_edgeFinset S))
  have hCle : ∑ e ∈ N.partC, x e ≤ 3 * εη := N.sum_partC_le
  have hxsplit : (∑ e ∈ D, x e) = (∑ e ∈ D ∩ internalEdges S, x e)
      + ∑ e ∈ D ∩ cutEdges S, x e := by
    calc (∑ e ∈ D, x e)
        = ∑ e ∈ (D ∩ internalEdges S) ∪ (D ∩ cutEdges S), x e := by
          congr 1
          exact subset_eq_din_union_dout (hDu.trans (cutEdges_subset_internal_union_cut huS))
      _ = _ := Finset.sum_union (disjoint_din_dout S D)
  have hselle : (∑ e ∈ D ∩ cutEdges S ∩ P, x e)
      ≤ ∑ e ∈ D ∩ cutEdges S, x e :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun e _ _ => hx.nonneg e
  have hselge : (∑ e ∈ D ∩ cutEdges S, x e) - 3 * εη
      ≤ ∑ e ∈ D ∩ cutEdges S ∩ P, x e := by
    have hsub : (D ∩ cutEdges S) \ (D ∩ cutEdges S ∩ P) ⊆ N.partC := by
      intro g hg
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
      exact hsel (Finset.mem_sdiff.mpr ⟨hg1, fun hcP => hg2 (Finset.mem_inter.mpr ⟨hg1, hcP⟩)⟩)
    have hle : ∑ e ∈ (D ∩ cutEdges S) \ (D ∩ cutEdges S ∩ P), x e
        ≤ ∑ e ∈ N.partC, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => hx.nonneg e
    rw [Finset.sum_sdiff_eq_sub Finset.inter_subset_left] at hle
    linarith
  -- the face, the avoidance, on the union
  have hsupF : ∀ T, μ.prob T ≠ 0 → (T ∩ internalEdges S).card ≤ S.card - 1 := by
    intro T hT
    have := card_internal_inter_add_one_le (μ.support_spanningTree T hT) hSne
    rw [Finset.inter_comm]
    omega
  have hlaw : LawData μ.prob (n - 1) :=
    ⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩
  have hq : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hSne hS0]
    linarith
  obtain ⟨hlo, hhi⟩ := expCard_union_face_avoid hlaw hsupF hb.faceMass hb.avoidMass
    hDinF hSelF hCF (Finset.disjoint_union_left.mpr ⟨hDinC, hSelC⟩) hd
  have hUsplit : expCard (polygonLaw μ S N.partC)
      ((D ∩ internalEdges S) ∪ (D ∩ cutEdges S ∩ P))
      = expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
        + expCard (polygonLaw μ S N.partC) (D ∩ cutEdges S ∩ P) :=
    expCard_union_of_disjoint _ hd
  -- the selected mass is the expected crossing count
  have hC0 : ∀ T, v T ≠ 0 → (T ∩ N.partC).card = 0 := by
    intro T hT
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  have hb1 : weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1)
      = expCard v (D ∩ cutEdges S) := (expCard_eq_weightMass_one hone).symm
  have hb1sel : expCard v (D ∩ cutEdges S)
      = expCard v (D ∩ cutEdges S ∩ P) := by
    rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal]
    refine (Finset.sum_subset Finset.inter_subset_left fun e he heP => ?_).symm
    have heC : e ∈ N.partC :=
      hsel (Finset.mem_sdiff.mpr ⟨he, fun hcP => heP (Finset.mem_inter.mpr ⟨he, hcP⟩)⟩)
    refine weightMass_eq_zero_of_support fun T hT hmem => ?_
    have h0 := hC0 T hT
    rw [Finset.card_eq_zero] at h0
    have hmem2 : e ∈ T ∩ N.partC := Finset.mem_inter.mpr ⟨hmem, heC⟩
    rw [h0] at hmem2
    exact absurd hmem2 (by simp)
  obtain ⟨htv1, htv2⟩ := abs_le.mp (tv_subset hSelP htv)
  have hβhi : weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ≤ expCard (polygonLaw μ S N.partC) (D ∩ cutEdges S ∩ P) + 0.00025 := by
    rw [hb1, hb1sel, div_le_iff₀ hMpos]
    nlinarith [htv2]
  have hβlo : expCard (polygonLaw μ S N.partC) (D ∩ cutEdges S ∩ P) - 0.00025
      ≤ weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v := by
    rw [hb1, hb1sel, le_div_iff₀ hMpos]
    nlinarith [htv1]
  rw [hxDin, hxSel] at hlo hhi
  rw [hxC] at hhi
  rw [← polygonLaw_eq] at hlo hhi
  rw [hUsplit] at hlo hhi
  constructor <;> linarith

set_option maxHeartbeats 2000000 in
-- the chain threads a dozen face/avoid comparisons through one `linarith`
/-- **The mean bounds of Corollary 5.10**, at a chosen part `P` of the polygon
partition.  Transferring `D_in ∪ D_sel` through the face *and* the avoidance as
one set charges the deficiency once — with the two signs cancelling, since
inside counts rise and outside counts fall — and charges `C` once.  The
resulting deviation is `ε_M + 4.5ε_η`. -/
theorem mean_bounds_of_part {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S u : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    (hS0 : AvoidsRootEdge e₀ S) (huS : u ⊆ S)
    (hεη : 0 ≤ εη) (hu2 : 2 ≤ cutSum x u) (hule : cutSum x u ≤ 2 + εη)
    (hScut : cutSum x S ≤ 2 + εη)
    {P : Finset (Sym2 (Fin n))} (hPC : Disjoint P N.partC)
    (htv : ∑ e ∈ P, |weightMass v (fun T => e ∈ T)
        - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)|
      ≤ 0.00025 * totalMass v)
    (hsel : (cutEdges u ∩ cutEdges S) \ P ⊆ N.partC)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (cutEdges u ∩ cutEdges S)).card ≤ 1) :
    2 - (0.00025 + 4.5 * εη)
        ≤ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
      ∧ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
        ≤ 2 + (0.00025 + 4.5 * εη) := by
  obtain ⟨hlo, hhi⟩ := mean_bounds_of_subset_part hx hμ hb hroot hSne hS0 huS hεη hScut
    (Finset.Subset.refl (cutEdges u)) hPC htv hsel hone
  have hcs : ∑ e ∈ cutEdges u, x e = cutSum x u := rfl
  rw [hcs] at hlo hhi
  constructor <;> linarith

/-! ### The division-free split of a selected expected count -/

/-- **Inside preservation for expected counts.**  For a set inside `E(S)` the
selected expected count is `M` times the polygon law's. -/
theorem PolygonBase.expCard_inside {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {Din : Finset (Sym2 (Fin n))} (hDin : Din ⊆ internalEdges S) :
    expCard v Din = totalMass v * expCard (polygonLaw μ S N.partC) Din := by
  classical
  obtain ⟨z, hvz⟩ := hb.selected
  have hAcut : N.partA ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partA_subset_cutEdges_root
  have hBcut : N.partB ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partB_subset_cutEdges_root
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hin : InsideDetermined S (fun T => e ∈ T) :=
    insideDetermined_mem (mem_internalEdges.mp (hDin he)).2
  have hcross : ∀ e' f', weightMass (polygonLaw μ S N.partC)
      (fun T => e ∈ T ∧ PairCell N.partA N.partB e' f' T)
      = weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)
        * weightMass (polygonLaw μ S N.partC) (PairCell N.partA N.partB e' f') :=
    fun e' f' => polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass
      hb.avoidMass hin (outsideDetermined_pairCell hAcut hBcut e' f')
  rw [hvz, weightMass_selected_inside _ _ _ z (fun T => e ∈ T) hcross]
  ring

/-- **The division-free split.**  Inside preservation supplies the first term,
one-hot support the second.  ⚠️ No positivity of the mass is needed here; `M > 0`
is required only when a *normalized* crossing probability `β` is introduced. -/
theorem PolygonBase.expCard_split {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1) :
    expCard v D = totalMass v * expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) := by
  classical
  have hsplit : expCard v D
      = expCard v (D ∩ internalEdges S) + expCard v (D ∩ cutEdges S) := by
    conv_lhs => rw [subset_eq_din_union_dout hD]
    exact expCard_union_of_disjoint _ (disjoint_din_dout S D)
  rw [hsplit, hb.expCard_inside hμ hroot hSne Finset.inter_subset_right,
    expCard_eq_weightMass_one hone]

/-! ### The core -/

-- the parity split unfolds several conditioned laws at once
set_option maxHeartbeats 2000000 in
/-- **KKO21 Corollary 5.10**, at the selection.  The two analytic inputs — the
almost-sure crossing `hzero` and the mean bounds — are hypotheses; everything
else is the split. -/
theorem corollary_5_10_core {μ : TreeDist n x} {εη : ℝ} {S u : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ)
    (hSne : S.Nonempty) (huS : u ⊆ S)
    (hAB : Disjoint (cutEdges u) N.partA ∨ Disjoint (cutEdges u) N.partB)
    (hzero : weightMass (polygonLaw μ S N.partC)
      (fun T => (T ∩ (cutEdges u ∩ internalEdges S)).card = 0) = 0)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 0.0005)
    (hmlo : 2 - d ≤ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v)
    (hmhi : expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
      ≤ 2 + d) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card) ≤ 0.5678 * totalMass v := by
  classical
  obtain ⟨z, hvz⟩ := hb.selected
  set ν : Finset (Sym2 (Fin n)) → ℝ := polygonLaw μ S N.partC with hν
  set Din : Finset (Sym2 (Fin n)) := cutEdges u ∩ internalEdges S with hDin
  set Dout : Finset (Sym2 (Fin n)) := cutEdges u ∩ cutEdges S with hDout
  set M : ℝ := totalMass v with hM
  set a : ℝ := weightMass ν (fun T => Odd (T ∩ Din).card) with ha
  set b0 : ℝ := weightMass v (fun T => (T ∩ Dout).card = 0) with hb0
  set b1 : ℝ := weightMass v (fun T => (T ∩ Dout).card = 1) with hb1
  -- the support facts
  have hsupp : ∀ T, v T ≠ 0 → (T ∩ N.partA).card = 1 ∧ (T ∩ N.partB).card = 1
      ∧ (T ∩ N.partC).card = 0 := by
    intro T hT
    obtain ⟨hA, hB⟩ := hb.support T hT
    refine ⟨hA, hB, ?_⟩
    have hνT : ν T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  have hle1 : ∀ T, v T ≠ 0 → (T ∩ Dout).card ≤ 1 := by
    intro T hT
    obtain ⟨hA, hB, hC⟩ := hsupp T hT
    exact card_dout_le_one hroot hAB hA hB hC
  -- determinacy
  have hDinsub : ∀ g ∈ Din, ∀ w ∈ g, w ∈ S := by
    intro g hg w hw
    exact (mem_internalEdges.mp (Finset.mem_inter.mp hg).2).2 w hw
  have hDoutsub : Dout ⊆ cutEdges S := fun g hg => (Finset.mem_inter.mp hg).2
  have hinOdd : InsideDetermined S (fun T => Odd (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Odd X.card)
  have hinEven : InsideDetermined S (fun T => Even (T ∩ Din).card) :=
    insideDetermined_inter hDinsub (fun X => Even X.card)
  have houtD : ∀ k : ℕ, OutsideDetermined S (fun T => (T ∩ Dout).card = k) := fun k =>
    outsideDetermined_inter (fun g hg => not_forall_mem_of_mem_cutEdges (hDoutsub hg))
      (fun X => X.card = k)
  have hAcut : N.partA ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partA_subset_cutEdges_root
  have hBcut : N.partB ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partB_subset_cutEdges_root
  -- the cross-independence hypotheses
  have hcross : ∀ (P : Finset (Sym2 (Fin n)) → Prop), InsideDetermined S P → ∀ k : ℕ,
      weightMass v (fun T => P T ∧ (T ∩ Dout).card = k)
        = weightMass ν P * weightMass v (fun T => (T ∩ Dout).card = k) := by
    intro P hP k
    rw [hvz]
    refine weightMass_selected_cross ν N.partA N.partB z P _ (fun e f => ?_)
    exact polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass hb.avoidMass hP
      ((houtD k).and (outsideDetermined_pairCell hAcut hBcut e f))
  -- the parity split
  have hOr : weightMass v (fun T => Odd (T ∩ cutEdges u).card)
      = weightMass v (fun T => Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
        + weightMass v (fun T => Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1) := by
    have hcongr : weightMass v (fun T => Odd (T ∩ cutEdges u).card)
        = weightMass v (fun T => (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
            ∨ (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) := by
      refine weightMass_congr_of_support fun T hT => ?_
      have hc := hle1 T hT
      have hsplitT := card_split_of_subcut huS T
      rw [← hDin, ← hDout] at hsplitT
      rw [hsplitT]
      have hcases : (T ∩ Dout).card = 0 ∨ (T ∩ Dout).card = 1 := by omega
      rcases hcases with h0 | h1
      · rw [h0]
        constructor
        · intro hodd
          exact Or.inl ⟨by simpa using hodd, rfl⟩
        · rintro (⟨hodd, -⟩ | ⟨-, hc1⟩)
          · simpa using hodd
          · exact absurd hc1 (by norm_num)
      · rw [h1]
        constructor
        · intro hodd
          refine Or.inr ⟨?_, rfl⟩
          rw [Nat.even_iff]
          rw [Nat.odd_iff] at hodd
          omega
        · rintro (⟨-, hc0⟩ | ⟨heven, -⟩)
          · exact absurd hc0 (by norm_num)
          · rw [Nat.odd_iff]
            rw [Nat.even_iff] at heven
            omega
    rw [hcongr]
    have hand : weightMass v (fun T => (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
        ∧ (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
            ∧ (Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)) = fun _ => False from ?_,
        weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      have h1 := h.1.2
      have h2 := h.2.2
      omega
    have := weightMass_or v (fun T => Odd (T ∩ Din).card ∧ (T ∩ Dout).card = 0)
      (fun T => Even (T ∩ Din).card ∧ (T ∩ Dout).card = 1)
    rw [hand, add_zero] at this
    exact this
  -- the two factors
  have hOdd := hcross (fun T => Odd (T ∩ Din).card) hinOdd 0
  have hEven := hcross (fun T => Even (T ∩ Din).card) hinEven 1
  have haEven : weightMass ν (fun T => Even (T ∩ Din).card) = 1 - a := by
    have hnot := weightMass_not ν (fun T => Odd (T ∩ Din).card)
    rw [hb.law.tot] at hnot
    rw [← hnot]
    exact weightMass_congr fun T => by rw [Nat.not_odd_iff_even]
  rw [hOdd, hEven, haEven] at hOr
  rw [← ha, ← hb0, ← hb1] at hOr
  -- the masses
  have hb0nn : 0 ≤ b0 := weightMass_nonneg hb.nonneg _
  have hb1nn : 0 ≤ b1 := weightMass_nonneg hb.nonneg _
  have hann : 0 ≤ a := weightMass_nonneg hb.law.nn _
  have ha1 : a ≤ 1 := by
    rw [← hb.law.tot]; exact weightMass_le_totalMass hb.law.nn _
  have hsum : b0 + b1 = M := by
    have hor := weightMass_or v (fun T => (T ∩ Dout).card = 0) (fun T => (T ∩ Dout).card = 1)
    have hand : weightMass v (fun T => (T ∩ Dout).card = 0 ∧ (T ∩ Dout).card = 1) = 0 := by
      rw [show (fun T : Finset (Sym2 (Fin n)) =>
          (T ∩ Dout).card = 0 ∧ (T ∩ Dout).card = 1) = fun _ => False from ?_, weightMass_false]
      funext T
      refine propext ⟨fun h => ?_, fun h => h.elim⟩
      have h1 := h.1
      have h2 := h.2
      omega
    have htrue : weightMass v (fun T => (T ∩ Dout).card = 0 ∨ (T ∩ Dout).card = 1) = M := by
      rw [hM, ← weightMass_true v]
      refine weightMass_congr_of_support fun T hT => ?_
      have := hle1 T hT
      exact ⟨fun _ => trivial, fun _ => by omega⟩
    rw [hand, add_zero, htrue] at hor
    exact hor.symm
  -- the zero-mass case
  have hMnn : 0 ≤ M := totalMass_nonneg hb.nonneg
  rcases eq_or_lt_of_le hMnn with hM0 | hMpos
  · have hb0z : b0 = 0 := by linarith
    have hb1z : b1 = 0 := by linarith
    rw [hOr, hb0z, hb1z, ← hM0]
    norm_num
  · -- the genuine case
    set β : ℝ := b1 / M with hβ
    have hβ0 : 0 ≤ β := div_nonneg hb1nn hMpos.le
    have hβ1 : β ≤ 1 := by
      rw [hβ, div_le_one hMpos]; linarith
    have hb1eq : b1 = β * M := by rw [hβ]; field_simp
    have hb0eq : b0 = M - β * M := by rw [← hb1eq]; linarith
    -- the inside mean is at most `2.2`
    have hEle : expCard ν Din ≤ 2.2 := by linarith
    have hup : β ≤ 1 / 2 →
        a ≤ (1 + Real.exp (-2 * ((expCard ν Din + β) - β - 1))) / 2 := by
      intro _
      have h := oddCount_le hb.law.st hb.law.rank hb.law.nn hb.law.tot Din hzero hEle
      have he : (expCard ν Din + β) - β - 1 = expCard ν Din - 1 := by ring
      rw [he]
      exact h
    have hlow : 1 / 2 < β → 2 - ((expCard ν Din + β) - β) ≤ a := by
      intro _
      have h := oddCount_ge hb.law.st hb.law.rank hb.law.nn hb.law.tot Din hzero
      have he : (expCard ν Din + β) - β = expCard ν Din := by ring
      rw [he]
      exact h
    have hkey := odd_split_le_num hβ0 hβ1 hd0 hd (E := expCard ν Din + β) hmlo hmhi hup hlow
    have hring : a * (M - β * M) + (1 - a) * (β * M) = (a * (1 - 2 * β) + β) * M := by ring
    rw [hOr, hb0eq, hb1eq, hring]
    exact mul_le_mul_of_nonneg_right hkey hMpos.le


/-! ### The wrapper -/

set_option maxHeartbeats 1000000 in
/-- **KKO21 Corollary 5.10.**  `P[δ(u)_T odd | E_S] ≤ 0.5678` for a hierarchy
cut `u` strictly inside a polygon cut `S`. -/
theorem corollary_5_10 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card) ≤ 0.5678 * totalMass v := by
  classical
  have hSne : S.Nonempty := (H.nearMin S hS).nonempty
  have hune : u.Nonempty := (H.nearMin u hu).nonempty
  have huS : u ⊆ S := hlt.subset
  have hScut : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hucut : cutSum x u ≤ 2 + εη := (H.nearMin u hu).cut_le
  have hu2 : 2 ≤ cutSum x u := H.two_le_cutSum hx hu
  have hroot : N.root = Sᶜ := hN.1
  have hAB := H.disjoint_partA_or_partB hS hu hlt hN
  -- the outer part `C_S` is never met by the selection
  have hC0 : ∀ T, v T ≠ 0 → (T ∩ N.partC).card = 0 := by
    intro T hT
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  have hone : ∀ T, v T ≠ 0 → (T ∩ (cutEdges u ∩ cutEdges S)).card ≤ 1 := by
    intro T hT
    obtain ⟨hA, hB⟩ := hb.support T hT
    exact card_dout_le_one hroot hAB hA hB (hC0 T hT)
  have hzero := weightMass_din_eq_zero (μ := μ) (C := N.partC) hSne hune hlt
  have hd0 : (0:ℝ) ≤ 0.00025 + 4.5 * εη := by linarith
  have hdcap : (0.00025 : ℝ) + 4.5 * εη ≤ 0.0005 := by linarith
  have hpart : N.partA ∪ N.partB ∪ N.partC = cutEdges S := by
    rw [N.partA_union_partB_union_partC, hroot, cutEdges_compl]
  -- pick the part of the polygon partition that `δ(u)` can still meet
  have hchoose : ∀ Q R : Finset (Sym2 (Fin n)), Disjoint (cutEdges u) Q →
      N.partA ∪ N.partB ∪ N.partC = cutEdges S →
      (Q = N.partA ∧ R = N.partB) ∨ (Q = N.partB ∧ R = N.partA) →
      (cutEdges u ∩ cutEdges S) \ R ⊆ N.partC := by
    intro Q R hQ hpart' hQR g hg
    obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨hgu, hgS⟩ := Finset.mem_inter.mp hg1
    rw [← hpart'] at hgS
    rcases Finset.mem_union.mp hgS with hab | hc
    · rcases Finset.mem_union.mp hab with ha | hbb
      · rcases hQR with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
        · exact absurd ha (fun hc' => Finset.disjoint_left.mp hQ hgu hc')
        · exact absurd ha hg2
      · rcases hQR with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hbb hg2
        · exact absurd hbb (fun hc' => Finset.disjoint_left.mp hQ hgu hc')
    · exact hc
  rcases hAB with hDA | hDB
  · -- `δ(u)` misses `A`: select inside `B`
    obtain ⟨hlo, hhi⟩ := mean_bounds_of_part hx hμ hb hroot hSne (H.avoids S hS) huS hεη hu2 hucut hScut
      N.partB_disjoint_partC hb.tvB
      (hchoose N.partA N.partB hDA hpart (Or.inl ⟨rfl, rfl⟩)) hone
    exact corollary_5_10_core hb hμ hroot hSne huS (Or.inl hDA) hzero hd0 hdcap hlo hhi
  · -- `δ(u)` misses `B`: select inside `A`
    obtain ⟨hlo, hhi⟩ := mean_bounds_of_part hx hμ hb hroot hSne (H.avoids S hS) huS hεη hu2 hucut hScut
      N.partA_disjoint_partC hb.tvA
      (hchoose N.partB N.partA hDB hpart (Or.inr ⟨rfl, rfl⟩)) hone
    exact corollary_5_10_core hb hμ hroot hSne huS (Or.inr hDB) hzero hd0 hdcap hlo hhi

end TSPGap

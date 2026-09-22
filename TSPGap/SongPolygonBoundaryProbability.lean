/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonBottomGuarantees
import TSPGap.SongParameters
import TSPGap.Lemma711

/-!
# Boundary polygon probability at Song's selection tolerance

The actual raw selection has tolerance epsilonM=0.000282. The boundary
calculation carries the full error 0.000564+40*eta. No conversion to the
smaller legacy tolerance is used.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

open Classical in
theorem boundary_product {εη b a' X Y : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    (hb : 0 ≤ b) (ha'b : b - 3 * εη ≤ a')
    (hX : b - 26 * εη ≤ X) (hX0 : 0 ≤ X) (hY : a' - (0.000282 + εη / 2) ≤ Y) (hY0 : 0 ≤ Y) :
    b ^ 2 - b * (0.000282 + 29.5 * εη) - εη ≤ X * Y := by
  have hXY : 0 ≤ X * Y := mul_nonneg hX0 hY0
  have hk : (0:ℝ) ≤ 0.000282 + 29.5 * εη := by linarith
  by_cases hb1 : b < 26 * εη
  · have h1 : b * b ≤ b * (26 * εη) := mul_le_mul_of_nonneg_left hb1.le hb
    have h2 : b * (26 * εη) ≤ (26 * εη) * (26 * εη) :=
      mul_le_mul_of_nonneg_right hb1.le (by positivity)
    have h3 : (26 * εη) * (26 * εη) ≤ εη := by nlinarith
    have h4 : 0 ≤ b * (0.000282 + 29.5 * εη) := mul_nonneg hb hk
    nlinarith
  · push Not at hb1
    by_cases hb2 : b < 3 * εη + (0.000282 + εη / 2)
    · have h1 : b * (b - (0.000282 + 29.5 * εη)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb (by linarith)
      nlinarith
    · push Not at hb2
      have hY' : b - 3 * εη - (0.000282 + εη / 2) ≤ Y := by linarith
      have h := mul_le_mul hX hY' (by linarith) hX0
      have hid : (b - 26 * εη) * (b - 3 * εη - (0.000282 + εη / 2))
          = b ^ 2 - b * (0.000282 + 29.5 * εη) + 26 * εη * (3 * εη + (0.000282 + εη / 2)) := by
        ring
      have h0 : 0 ≤ 26 * εη * (3 * εη + (0.000282 + εη / 2)) := by positivity
      nlinarith

open Classical in
/-- **Lemma 7.10's arithmetic.**  `a, a'` are `x(A→), x(A↑)`, `b, b'` are `x(B→),
x(B↑)`, `c = x(C→)`; `X₁, X₂` the two inside masses, `Y₁, Y₂` the two normalized
outside marginals. -/
theorem boundary_arith {εη a a' b b' c X1 Y1 X2 Y2 : ℝ}
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 1 - εη ≤ a + a') (hB : 1 - εη ≤ b + b')
    (harrow : a + b + c ≤ 1 + 2 * εη) (harrow' : 1 - 2 * εη ≤ a + b + c) (hc3 : c ≤ 3 * εη)
    (hX1 : b - 26 * εη ≤ X1) (hX10 : 0 ≤ X1) (hY1 : a' - (0.000282 + εη / 2) ≤ Y1) (hY10 : 0 ≤ Y1)
    (hX2 : a - 26 * εη ≤ X2) (hX20 : 0 ≤ X2) (hY2 : b' - (0.000282 + εη / 2) ≤ Y2) (hY20 : 0 ≤ Y2) :
    (1 - a) ^ 2 + a ^ 2 - 0.000564 - 40 * εη ≤ X1 * Y1 + X2 * Y2 := by
  have ha'b : b - 3 * εη ≤ a' := by linarith
  have hb'a : a - 3 * εη ≤ b' := by linarith
  have hP1 := boundary_product hεη hεηcap hb ha'b hX1 hX10 hY1 hY10
  have hP2 := boundary_product hεη hεηcap ha hb'a hX2 hX20 hY2 hY20
  have hsq : (1 - a) ^ 2 ≤ b ^ 2 + 10 * εη := by
    by_cases h : 1 - a - 5 * εη ≤ 0
    · nlinarith
    · have hb5 : 1 - a - 5 * εη ≤ b := by linarith
      have := mul_le_mul hb5 hb5 (by linarith) hb
      nlinarith
  have hk : (0:ℝ) ≤ 0.000282 + 29.5 * εη := by linarith
  have hab : (a + b) * (0.000282 + 29.5 * εη) ≤ (1 + 2 * εη) * (0.000282 + 29.5 * εη) :=
    mul_le_mul_of_nonneg_right (by linarith) hk
  have hsmall : (1 + 2 * εη) * (0.000282 + 29.5 * εη) ≤ 0.000282 + 30 * εη := by nlinarith
  nlinarith

/-! ### The core, at an abstract boundary group -/

set_option maxHeartbeats 4000000 in
-- Two independent events with the actual polygon tolerance.
open Classical in
theorem boundary_happy_core (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {Ŝ : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) {Nh : NearCycle x εη} (hNh : H.Presents Nh Ŝ)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} {minMass : ℝ}
    (hb : PolygonSelection epsilonM minMass μ Ŝ Nh cst v)
    {S : Finset (Fin n)} (hSŜ : IsChildOf H.cuts S Ŝ) {N : NearCycle x εη} (hN : H.Presents N S)
    {G : Finset (Sym2 (Fin n))} (hGup : cutEdges S ∩ cutEdges Ŝ = G)
    (hGC : Disjoint G Nh.partC) (hG1 : ∀ T, v T ≠ 0 → (T ∩ G).card = 1)
    (htv : ∑ e ∈ G, |weightMass v (fun T => e ∈ T)
        - totalMass v * weightMass (polygonLaw μ Ŝ Nh.partC) (fun T => e ∈ T)|
      ≤ 0.000282 * totalMass v)
    (hGlow : 1 - εη ≤ ∑ e ∈ G, x e) (hGhigh : ∑ e ∈ G, x e ≤ 1 + 2 * εη) :
    ((1 - ∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2
        + (∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2 - 0.000564 - 40 * εη) * totalMass v
      ≤ weightMass v N.Happy := by
  classical
  set ν := polygonLaw μ Ŝ Nh.partC with hν
  set M := totalMass v with hM
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hroot : Nh.root = Ŝᶜ := hNh.1
  have hŜne : Ŝ.Nonempty := (H.nearMin Ŝ hŜ).nonempty
  have hSne : S.Nonempty := H.child_nonempty hSŜ
  have huS : S ⊂ Ŝ := hSŜ.2.2.1
  have hS : S ∈ H.cuts := hSŜ.1
  have hMpos : 0 < M := hb.total_pos
  have hAcut : Nh.partA ⊆ cutEdges Ŝ := Nh.partA_subset_cutEdges hroot
  have hBcut : Nh.partB ⊆ cutEdges Ŝ := Nh.partB_subset_cutEdges hroot
  have hCcut : Nh.partC ⊆ cutEdges Ŝ := Nh.partC_subset_cutEdges hroot
  have hcutint : Disjoint (cutEdges Ŝ) (internalEdges Ŝ) := cutEdges_disjoint_internalEdges_self Ŝ
  have hGcut : G ⊆ cutEdges Ŝ := by rw [← hGup]; exact Finset.inter_subset_right
  -- `S`'s partition
  have hSroot : cutEdges N.root = cutEdges S := hN.cutEdges_root_eq
  have hAS : N.partA ⊆ cutEdges S := hSroot ▸ N.partA_subset_cutEdges_root
  have hBS : N.partB ⊆ cutEdges S := hSroot ▸ N.partB_subset_cutEdges_root
  have hCS : N.partC ⊆ cutEdges S := by
    rw [← hSroot, NearCycle.partC]; exact Finset.sdiff_subset
  have hAB := N.partA_disjoint_partB
  have hAC := N.partA_disjoint_partC
  have hBC := N.partB_disjoint_partC
  have hunion : N.partA ∪ N.partB ∪ N.partC = cutEdges S := hSroot ▸ N.partA_union_partB_union_partC
  have hSsub : cutEdges S ⊆ internalEdges Ŝ ∪ cutEdges Ŝ :=
    cutEdges_subset_internal_union_cut huS.subset
  -- the inside and outside parts
  set Ain := N.partA ∩ internalEdges Ŝ with hAin
  set Aup := N.partA ∩ cutEdges Ŝ with hAup
  set Bin := N.partB ∩ internalEdges Ŝ with hBin
  set Bup := N.partB ∩ cutEdges Ŝ with hBup
  set Cin := N.partC ∩ internalEdges Ŝ with hCin
  set Cup := N.partC ∩ cutEdges Ŝ with hCup
  have hcardA : ∀ T, (T ∩ N.partA).card = (T ∩ Ain).card + (T ∩ Aup).card :=
    fun T => card_split_of_subset (hAS.trans hSsub) T
  have hcardB : ∀ T, (T ∩ N.partB).card = (T ∩ Bin).card + (T ∩ Bup).card :=
    fun T => card_split_of_subset (hBS.trans hSsub) T
  have hcardC : ∀ T, (T ∩ N.partC).card = (T ∩ Cin).card + (T ∩ Cup).card :=
    fun T => card_split_of_subset (hCS.trans hSsub) T
  have hAupG : Aup ⊆ G := by rw [← hGup]; exact Finset.inter_subset_inter hAS (Finset.Subset.refl _)
  have hBupG : Bup ⊆ G := by rw [← hGup]; exact Finset.inter_subset_inter hBS (Finset.Subset.refl _)
  have hCupG : Cup ⊆ G := by rw [← hGup]; exact Finset.inter_subset_inter hCS (Finset.Subset.refl _)
  have hAinF : Ain ⊆ internalEdges Ŝ := Finset.inter_subset_right
  have hBinF : Bin ⊆ internalEdges Ŝ := Finset.inter_subset_right
  have hCinF : Cin ⊆ internalEdges Ŝ := Finset.inter_subset_right
  have hAupBup : Disjoint Aup Bup :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB)
  have hAupCup : Disjoint Aup Cup :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hAC)
  have hBupCup : Disjoint Bup Cup :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hBC)
  -- on the support, the three boundary counts sum to one
  have hsupp1 : ∀ T, v T ≠ 0 →
      (T ∩ Aup).card + (T ∩ Bup).card + (T ∩ Cup).card ≤ 1 := by
    intro T hT
    have h1 := hG1 T hT
    have hsub : (T ∩ Aup) ∪ (T ∩ Bup) ∪ (T ∩ Cup) ⊆ T ∩ G := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact Finset.inter_subset_inter (Finset.Subset.refl T) hAupG
      · exact Finset.inter_subset_inter (Finset.Subset.refl T) hBupG
      · exact Finset.inter_subset_inter (Finset.Subset.refl T) hCupG
    have hd1 : Disjoint (T ∩ Aup) (T ∩ Bup) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hAupBup)
    have hd2 : Disjoint ((T ∩ Aup) ∪ (T ∩ Bup)) (T ∩ Cup) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hAupCup),
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hBupCup)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, h1] at this
    exact this
  -- the two events
  set P1 : Finset (Sym2 (Fin n)) → Prop :=
    fun T => (T ∩ Ain).card = 0 ∧ (T ∩ Bin).card = 1 ∧ (T ∩ Cin).card = 0 with hP1
  set Q1 : Finset (Sym2 (Fin n)) → Prop := fun T => (T ∩ Aup).card = 1 with hQ1
  set P2 : Finset (Sym2 (Fin n)) → Prop :=
    fun T => (T ∩ Bin).card = 0 ∧ (T ∩ Ain).card = 1 ∧ (T ∩ Cin).card = 0 with hP2
  set Q2 : Finset (Sym2 (Fin n)) → Prop := fun T => (T ∩ Bup).card = 1 with hQ2
  -- each event makes `S` happy
  have hE1 : ∀ T, v T ≠ 0 → P1 T ∧ Q1 T → N.Happy T := by
    rintro T hT ⟨⟨hA0, hB1, hC0⟩, hAu⟩
    have hs := hsupp1 T hT
    have hBu : (T ∩ Bup).card = 0 := by omega
    have hCu : (T ∩ Cup).card = 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.inter_comm, hcardA, hA0, hAu]; decide
    · rw [Finset.inter_comm, hcardB, hB1, hBu]; decide
    · rw [Finset.inter_comm, ← Finset.card_eq_zero, hcardC, hC0, hCu]
  have hE2 : ∀ T, v T ≠ 0 → P2 T ∧ Q2 T → N.Happy T := by
    rintro T hT ⟨⟨hB0, hA1, hC0⟩, hBu⟩
    have hs := hsupp1 T hT
    have hAu : (T ∩ Aup).card = 0 := by omega
    have hCu : (T ∩ Cup).card = 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.inter_comm, hcardA, hA1, hAu]; decide
    · rw [Finset.inter_comm, hcardB, hB0, hBu]; decide
    · rw [Finset.inter_comm, ← Finset.card_eq_zero, hcardC, hC0, hCu]
  have hdisjE : ∀ T, v T ≠ 0 → ¬ ((P1 T ∧ Q1 T) ∧ (P2 T ∧ Q2 T)) := by
    rintro T hT ⟨⟨-, hAu⟩, ⟨-, hBu⟩⟩
    have hs := hsupp1 T hT
    omega
  -- the happy mass dominates the sum of the two events
  have hHappy : weightMass v (fun T => P1 T ∧ Q1 T) + weightMass v (fun T => P2 T ∧ Q2 T)
      ≤ weightMass v N.Happy := by
    have hor := weightMass_or v (fun T => P1 T ∧ Q1 T) (fun T => P2 T ∧ Q2 T)
    have hand : weightMass v (fun T => (P1 T ∧ Q1 T) ∧ (P2 T ∧ Q2 T)) = 0 :=
      weightMass_eq_zero_of_support fun T hT h => hdisjE T hT h
    have hcongr : weightMass v (fun T => (P1 T ∧ Q1 T) ∨ (P2 T ∧ Q2 T))
        = weightMass v (fun T => ((P1 T ∧ Q1 T) ∨ (P2 T ∧ Q2 T)) ∧ N.Happy T) :=
      weightMass_congr_of_support fun T hT =>
        ⟨fun h => ⟨h, h.elim (hE1 T hT) (hE2 T hT)⟩, fun h => h.1⟩
    have hmono : weightMass v (fun T => ((P1 T ∧ Q1 T) ∨ (P2 T ∧ Q2 T)) ∧ N.Happy T)
        ≤ weightMass v N.Happy := weightMass_mono hb.nonneg fun T h => h.2
    linarith
  -- the factorization
  obtain ⟨z, hvz⟩ := hb.selected
  have hP1in : InsideDetermined Ŝ P1 :=
    (insideDetermined_inter (fun e he => (mem_internalEdges.mp (hAinF he)).2)
          (fun X => X.card = 0)).and
      ((insideDetermined_inter (fun e he => (mem_internalEdges.mp (hBinF he)).2)
          (fun X => X.card = 1)).and
        (insideDetermined_inter (fun e he => (mem_internalEdges.mp (hCinF he)).2)
          (fun X => X.card = 0)))
  have hP2in : InsideDetermined Ŝ P2 :=
    (insideDetermined_inter (fun e he => (mem_internalEdges.mp (hBinF he)).2)
          (fun X => X.card = 0)).and
      ((insideDetermined_inter (fun e he => (mem_internalEdges.mp (hAinF he)).2)
          (fun X => X.card = 1)).and
        (insideDetermined_inter (fun e he => (mem_internalEdges.mp (hCinF he)).2)
          (fun X => X.card = 0)))
  have hQ1out : OutsideDetermined Ŝ Q1 :=
    outsideDetermined_inter (fun e he => not_forall_mem_of_mem_cutEdges (Finset.mem_inter.mp he).2)
      (fun X => X.card = 1)
  have hQ2out : OutsideDetermined Ŝ Q2 :=
    outsideDetermined_inter (fun e he => not_forall_mem_of_mem_cutEdges (Finset.mem_inter.mp he).2)
      (fun X => X.card = 1)
  have hcross1 : weightMass v (fun T => P1 T ∧ Q1 T) = weightMass ν P1 * weightMass v Q1 := by
    rw [hvz]
    exact weightMass_selected_cross ν Nh.partA Nh.partB z P1 Q1 fun e f =>
      polygonLaw_indep μ hμ hŜne hCcut hb.faceMass hb.avoidMass hP1in
        (hQ1out.and (outsideDetermined_pairCell hAcut hBcut e f))
  have hcross2 : weightMass v (fun T => P2 T ∧ Q2 T) = weightMass ν P2 * weightMass v Q2 := by
    rw [hvz]
    exact weightMass_selected_cross ν Nh.partA Nh.partB z P2 Q2 fun e f =>
      polygonLaw_indep μ hμ hŜne hCcut hb.faceMass hb.avoidMass hP2in
        (hQ2out.and (outsideDetermined_pairCell hAcut hBcut e f))
  -- the outside marginals
  have hlaw : LawData μ.prob (n - 1) :=
    ⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩
  have hsupF : ∀ T, μ.prob T ≠ 0 → (T ∩ internalEdges Ŝ).card ≤ Ŝ.card - 1 := by
    intro T hT
    have := card_internal_inter_add_one_le (μ.support_spanningTree T hT) hŜne
    rw [Finset.inter_comm]
    omega
  have hdef : faceDeficiency μ.prob (internalEdges Ŝ) (Ŝ.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hŜne (H.avoids Ŝ hŜ)]
    linarith [(H.nearMin Ŝ hŜ).cut_le]
  have hCF : Nh.partC ⊆ (internalEdges Ŝ)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left hCcut hcutint)
  have hxC : expCard μ.prob Nh.partC ≤ 3 * εη := by
    rw [expCard_prob_eq_sum μ (hCcut.trans (cutEdges_subset_edgeFinset Ŝ))]
    exact Nh.sum_partC_le
  have houtside : ∀ D ⊆ G, M * ((∑ e ∈ D, x e) - (0.000282 + εη / 2)) ≤ expCard v D := by
    intro D hDG
    have hDcut : D ⊆ cutEdges Ŝ := hDG.trans hGcut
    have hDF : D ⊆ (internalEdges Ŝ)ᶜ :=
      subset_compl_of_disjoint (Finset.disjoint_of_subset_left hDcut hcutint)
    have hDC : Disjoint D Nh.partC := Finset.disjoint_of_subset_left hDG hGC
    obtain ⟨hlo, -⟩ := expCard_union_face_avoid hlaw hsupF hb.faceMass hb.avoidMass
      (Finset.empty_subset (internalEdges Ŝ)) hDF hCF
      (by rw [Finset.empty_union]; exact hDC) (Finset.disjoint_empty_left D)
    rw [Finset.empty_union, expCard_empty, zero_add] at hlo
    have hxD : expCard μ.prob D = ∑ e ∈ D, x e :=
      expCard_prob_eq_sum μ (hDcut.trans (cutEdges_subset_edgeFinset Ŝ))
    obtain ⟨h1, -⟩ := abs_le.mp (tv_subset hDG htv)
    have hν' : expCard ν D = expCard (avoidDist (faceDist μ.prob (indicatorCost (internalEdges Ŝ))
        (Ŝ.card - 1)) Nh.partC) D := rfl
    rw [← hν'] at hlo
    rw [hxD] at hlo
    have := mul_le_mul_of_nonneg_left
      (show (∑ e ∈ D, x e) - εη / 2 ≤ expCard ν D by linarith) hMpos.le
    nlinarith
  -- the inside means
  have hinside : ∀ D ⊆ internalEdges Ŝ,
      (∑ e ∈ D, x e) - εη / 2 ≤ expCard ν D ∧ expCard ν D ≤ (∑ e ∈ D, x e) + εη / 2 + 3 * εη := by
    intro D hDF
    have hDC : Disjoint D Nh.partC :=
      Finset.disjoint_of_subset_left hDF (Finset.disjoint_of_subset_right hCcut hcutint.symm)
    obtain ⟨hlo, hhi⟩ := expCard_union_face_avoid hlaw hsupF hb.faceMass hb.avoidMass hDF
      (Finset.empty_subset _) hCF (by rw [Finset.union_empty]; exact hDC)
      (Finset.disjoint_empty_right D)
    rw [Finset.union_empty, expCard_empty, add_zero] at hlo hhi
    have hxD : expCard μ.prob D = ∑ e ∈ D, x e :=
      expCard_prob_eq_sum μ (hDF.trans (internalEdges_subset_edgeFinset Ŝ))
    have hν' : expCard ν D = expCard (avoidDist (faceDist μ.prob (indicatorCost (internalEdges Ŝ))
        (Ŝ.card - 1)) Nh.partC) D := rfl
    rw [← hν'] at hlo hhi
    rw [hxD] at hlo hhi
    constructor <;> linarith
  -- the inside set `δ→(S)` is met at least once under `ν`
  have hdin : cutEdges S ∩ internalEdges Ŝ = (Ain ∪ Bin) ∪ Cin := by
    rw [← hunion, Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
  have hAinBin : Disjoint Ain Bin :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB)
  have hABinCin : Disjoint (Ain ∪ Bin) Cin := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAC),
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hBC)⟩
  have hone_in : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ Ain).card + (T ∩ Bin).card + (T ∩ Cin).card := by
    intro T hT
    have hind := polygonLaw_inducesTreeOn hŜne hT
    have h1 := one_le_card_din hind hSne huS
    rw [hdin, Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint] at h1
    · exact h1
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hAinBin)
    · rw [← Finset.inter_union_distrib_left]
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hABinCin)
  have hone_in' : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ Bin).card + (T ∩ Ain).card + (T ∩ Cin).card := by
    intro T hT; have := hone_in T hT; omega
  have hdef1 : expCard ν Bin - 2 * (expCard ν Ain + expCard ν Bin + expCard ν Cin - 1)
      ≤ weightMass ν P1 := weightMass_singleton_ge hb.law.nn hb.law.tot hone_in
  have hdef2 : expCard ν Ain - 2 * (expCard ν Bin + expCard ν Ain + expCard ν Cin - 1)
      ≤ weightMass ν P2 := weightMass_singleton_ge hb.law.nn hb.law.tot hone_in'
  -- the masses
  obtain ⟨hAin1, hAin2⟩ := hinside Ain hAinF
  obtain ⟨hBin1, hBin2⟩ := hinside Bin hBinF
  obtain ⟨hCin1, hCin2⟩ := hinside Cin hCinF
  have hxA : ∑ e ∈ N.partA, x e = (∑ e ∈ Ain, x e) + ∑ e ∈ Aup, x e := by
    conv_lhs => rw [subset_eq_din_union_dout (hAS.trans hSsub)]
    exact Finset.sum_union (disjoint_din_dout Ŝ N.partA)
  have hxB : ∑ e ∈ N.partB, x e = (∑ e ∈ Bin, x e) + ∑ e ∈ Bup, x e := by
    conv_lhs => rw [subset_eq_din_union_dout (hBS.trans hSsub)]
    exact Finset.sum_union (disjoint_din_dout Ŝ N.partB)
  have hxCs : ∑ e ∈ N.partC, x e = (∑ e ∈ Cin, x e) + ∑ e ∈ Cup, x e := by
    conv_lhs => rw [subset_eq_din_union_dout (hCS.trans hSsub)]
    exact Finset.sum_union (disjoint_din_dout Ŝ N.partC)
  have hxarrow : ∑ e ∈ cutEdges S ∩ internalEdges Ŝ, x e
      = (∑ e ∈ Ain, x e) + (∑ e ∈ Bin, x e) + ∑ e ∈ Cin, x e := by
    rw [hdin, Finset.sum_union hABinCin, Finset.sum_union hAinBin]
  have hxS : cutSum x S = (∑ e ∈ cutEdges S ∩ internalEdges Ŝ, x e) + ∑ e ∈ G, x e := by
    rw [← hGup]
    unfold cutSum
    conv_lhs => rw [subset_eq_din_union_dout hSsub]
    exact Finset.sum_union (disjoint_din_dout Ŝ (cutEdges S))
  have hS2 : 2 ≤ cutSum x S := H.two_le_cutSum hx hS
  have hScut : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hA1 : 1 - εη ≤ ∑ e ∈ N.partA, x e := N.one_sub_le_sum_partA
  have hB1 : 1 - εη ≤ ∑ e ∈ N.partB, x e := N.one_sub_le_sum_partB
  have hCin3 : ∑ e ∈ Cin, x e ≤ 3 * εη := by
    have := N.sum_partC_le
    have h0 : 0 ≤ ∑ e ∈ Cup, x e := Finset.sum_nonneg fun e _ => hx0 e
    linarith
  have hAin0 : 0 ≤ ∑ e ∈ Ain, x e := Finset.sum_nonneg fun e _ => hx0 e
  have hBin0 : 0 ≤ ∑ e ∈ Bin, x e := Finset.sum_nonneg fun e _ => hx0 e
  have hCin0 : 0 ≤ ∑ e ∈ Cin, x e := Finset.sum_nonneg fun e _ => hx0 e
  -- the four factors
  have hX1 : (∑ e ∈ Bin, x e) - 26 * εη ≤ weightMass ν P1 := by linarith
  have hX2 : (∑ e ∈ Ain, x e) - 26 * εη ≤ weightMass ν P2 := by linarith
  have hX10 : 0 ≤ weightMass ν P1 := weightMass_nonneg hb.law.nn _
  have hX20 : 0 ≤ weightMass ν P2 := weightMass_nonneg hb.law.nn _
  have hone_up : ∀ D ⊆ G, ∀ T, v T ≠ 0 → (T ∩ D).card ≤ 1 := by
    intro D hD T hT
    rw [← hG1 T hT]
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hD)
  have hQ1eq : weightMass v Q1 = expCard v Aup :=
    (expCard_eq_weightMass_one (hone_up Aup hAupG)).symm
  have hQ2eq : weightMass v Q2 = expCard v Bup :=
    (expCard_eq_weightMass_one (hone_up Bup hBupG)).symm
  have hY1 := houtside Aup hAupG
  have hY2 := houtside Bup hBupG
  have hQ10 : 0 ≤ weightMass v Q1 := weightMass_nonneg hb.nonneg _
  have hQ20 : 0 ≤ weightMass v Q2 := weightMass_nonneg hb.nonneg _
  -- normalize the outside marginals by `M`
  set Y1 := weightMass v Q1 / M with hY1def
  set Y2 := weightMass v Q2 / M with hY2def
  have hY1lo : (∑ e ∈ Aup, x e) - (0.000282 + εη / 2) ≤ Y1 := by
    rw [hY1def, le_div_iff₀ hMpos, hQ1eq]; linarith
  have hY2lo : (∑ e ∈ Bup, x e) - (0.000282 + εη / 2) ≤ Y2 := by
    rw [hY2def, le_div_iff₀ hMpos, hQ2eq]; linarith
  have hY10 : 0 ≤ Y1 := div_nonneg hQ10 hMpos.le
  have hY20 : 0 ≤ Y2 := div_nonneg hQ20 hMpos.le
  have harith := boundary_arith hεη hεηcap hAin0 hBin0 hCin0 (by linarith) (by linarith)
    (by linarith) (by linarith) hCin3 hX1 hX10 hY1lo hY10 hX2 hX20 hY2lo hY20
  -- assemble
  have hprod : weightMass v N.Happy ≥ M * (weightMass ν P1 * Y1 + weightMass ν P2 * Y2) := by
    have e1 : M * (weightMass ν P1 * Y1) = weightMass ν P1 * weightMass v Q1 := by
      rw [hY1def]; field_simp
    have e2 : M * (weightMass ν P2 * Y2) = weightMass ν P2 * weightMass v Q2 := by
      rw [hY2def]; field_simp
    rw [mul_add, e1, e2, ← hcross1, ← hcross2]
    exact hHappy
  calc ((1 - ∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2
        + (∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2 - 0.000564 - 40 * εη) * M
      ≤ (weightMass ν P1 * Y1 + weightMass ν P2 * Y2) * M :=
        mul_le_mul_of_nonneg_right harith hMpos.le
    _ = M * (weightMass ν P1 * Y1 + weightMass ν P2 * Y2) := mul_comm _ _
    _ ≤ weightMass v N.Happy := hprod

/-! ### The two boundary atoms, at the thinning -/

open Classical in
theorem boundary_happy_left (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {H : Hierarchy x e₀ εη} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {Ŝ : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) {p : ℝ} (hp : 0 ≤ p)
    {Ξ : BottomThinning H μ Ŝ p} {minMass oddBound unhappyBound : ℝ}
    (hG : PolygonBottomGuarantees epsilonM minMass oddBound unhappyBound H μ Ŝ p Ξ)
    {S : Finset (Fin n)} (hSt : S = Ξ.cycle.atom 1)
    {N : NearCycle x εη} (hN : H.Presents N S) :
    ((1 - ∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2
        + (∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2 - 0.000564 - 40 * εη) * p
      ≤ weightMass Ξ.thin N.Happy := by
  obtain ⟨W⟩ := hG.polygonWitness
  have hpres : H.Presents Ξ.cycle Ŝ := Ξ.presents
  have hSŜ : IsChildOf H.cuts S Ŝ := hSt ▸ hpres.atom_isChildOf Fin.zero_lt_one.ne'
  have hGup : cutEdges S ∩ cutEdges Ŝ = Ξ.cycle.partA := hSt ▸ hpres.cutEdges_inter_eq_partA
  have hcore := boundary_happy_core hx hμ H hεη hεηcap hŜ hpres W.polygon hSŜ hN hGup
    Ξ.cycle.partA_disjoint_partC (fun T hT => (W.polygon.support T hT).1) W.polygon.tvA
    Ξ.cycle.one_sub_le_sum_partA (Ξ.cycle.sum_partA_le hx.nonneg)
  have hkey := W.totalMass_raw_mul_weightMass_thin N.Happy
  have hMpos := W.totalMass_raw_pos
  have := mul_le_mul_of_nonneg_left hcore hp
  nlinarith

open Classical in
/-- **Lemma 7.10** for the rightmost atom `S = a_{m−1}`, with `B̂` as the boundary group. -/
theorem boundary_happy_right (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ)
    {H : Hierarchy x e₀ εη} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {Ŝ : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) {p : ℝ} (hp : 0 ≤ p)
    {Ξ : BottomThinning H μ Ŝ p} {minMass oddBound unhappyBound : ℝ}
    (hG : PolygonBottomGuarantees epsilonM minMass oddBound unhappyBound H μ Ŝ p Ξ)
    {S : Finset (Fin n)} (hSt : S = Ξ.cycle.atom Ξ.cycle.lastIdx)
    {N : NearCycle x εη} (hN : H.Presents N S) :
    ((1 - ∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2
        + (∑ g ∈ N.partA ∩ internalEdges Ŝ, x g) ^ 2 - 0.000564 - 40 * εη) * p
      ≤ weightMass Ξ.thin N.Happy := by
  obtain ⟨W⟩ := hG.polygonWitness
  have hpres : H.Presents Ξ.cycle Ŝ := Ξ.presents
  have hSŜ : IsChildOf H.cuts S Ŝ :=
    hSt ▸ hpres.atom_isChildOf (Ne.symm Ξ.cycle.zero_ne_lastIdx)
  have hGup : cutEdges S ∩ cutEdges Ŝ = Ξ.cycle.partB := hSt ▸ hpres.cutEdges_inter_eq_partB
  have hcore := boundary_happy_core hx hμ H hεη hεηcap hŜ hpres W.polygon hSŜ hN hGup
    Ξ.cycle.partB_disjoint_partC (fun T hT => (W.polygon.support T hT).2) W.polygon.tvB
    Ξ.cycle.one_sub_le_sum_partB (Ξ.cycle.sum_partB_le hx.nonneg)
  have hkey := W.totalMass_raw_mul_weightMass_thin N.Happy
  have hMpos := W.totalMass_raw_pos
  have := mul_le_mul_of_nonneg_left hcore hp
  nlinarith

end TSPGap.Song

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPairedFace

/-!
# Paired prefixes instantiated from original fiber-tree inputs

Both earlier prefix laws now supply their mass floors, chosen-bundle
one-hot support, and initial residual means. The indexed export takes
only the original law, face deficiency, partition and marginal hypotheses.
The two branch conditions remain explicit; a separate export instantiates
the existing dichotomy from the two original rank events.

Rank-event identification on the pruned sets, the not-good-to-rank inputs,
and capacity coefficient extraction remain separate. This file changes no
payment or gap constant.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The numerical inputs to the shared avoid-F/present-E construction.
The original-space interpretation of M is supplied by the existing exact
unwinding identities, not by an independence assumption in this packet. -/
structure PairedStartData (ν : Finset ι → ℝ) (rank : ℕ) (A B E F : Finset ι)
    (M pre e lower upper : ℝ) : Prop where
  law : LawData ν rank
  mass_pos : 0 < M
  f_mean : expCard ν F < 1
  e_mean : e ≤ expCard ν E
  e_one : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1
  pre_mass : pre ≤ M * totalMass (avoidWeight ν F)
  final_mass : pre * e ≤ M * pairedInputMass ν F E
  a_lower : lower ≤ expCard ν A
  a_upper : expCard ν A ≤ upper
  b_upper : expCard ν B ≤ upper

/-- Both branch constructions, starting at the same atom-tree face. -/
structure PairedPrefixPair (ν : Finset ι → ℝ) (rank : ℕ) (A B C E F Z : Finset ι)
    (M : ℝ) : Prop where
  absent : expCard ν Z ≤ 3 * epsilon →
    PairedStartData (avoidDist ν (Z ∪ (C ∪ (E ∩ B)))) rank (A \ E) (B \ F) (E ∩ A) F
      (M * totalMass (avoidWeight ν (Z ∪ (C ∪ (E ∩ B)))))
      pairedAbsentPreMass (1 / 2 - 3 * h) (1 / 2 - 2 * h - 2 * r - 4 * d₀)
      (1 / 2 + 3 * h + 4 * r + 6 * d₀ + 3 * epsilon)
  present : 1 - 3 * epsilon ≤ expCard ν Z →
    PairedStartData (presentPrefixLaw ν Z (C ∪ (E ∩ B))) rank
      (A \ E) (B \ F) (E ∩ A) F (M * presentPrefixMass ν Z (C ∪ (E ∩ B)))
      pairedPresentPreMass (1 / 2 - 2 * h - 2 * r - 4 * d₀ - 3 * epsilon)
      (1 / 2 - 2 * h - 2 * r - 4 * d₀ - 3 * epsilon)
      (1 / 2 + 3 * h + 4 * r + 6 * d₀)

/-- Assemble the generic prefixes from the initial face estimates. The
union bound uses the whole avoided set, and presence of Z costs only its
deficiency in the lower mean. -/
theorem paired_prefix_pair {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {A B C E F Z I : Finset ι} (G : PairedBoundaryGeometry A B C E F Z I)
    (HB : PairedFaceBounds ν A B C E F) {M : ℝ} (hM : 1 - 3 * d₀ ≤ M)
    (honeE : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1) :
    PairedPrefixPair ν rank A B C E F Z M := by
  obtain ⟨hRZ, heZ, heD, heF, haZ, hbZ, haD⟩ := G.present_disjoint
  obtain ⟨heD0, haD0⟩ := G.absent_disjoint
  have honeEA : ∀ T, ν T ≠ 0 → (T ∩ (E ∩ A)).card ≤ 1 := by
    intro T hT
    exact (card_le_card (inter_subset_inter (Subset.refl T) inter_subset_left)).trans (honeE T hT)
  have hd0 : (0 : ℝ) ≤ d₀ := by norm_num [d₀]
  constructor
  · intro hZ
    have hR : expCard ν ((Z ∪ (C ∪ (E ∩ B))) ∪ F) ≤
        1 / 2 + 3 * epsilon + 2 * r + d₀ + 2 * h := by
      rw [union_assoc]
      have hh := expCard_union_le hw.nn Z ((C ∪ (E ∩ B)) ∪ F)
      linarith only [hh, hZ, HB.union_upper]
    obtain ⟨hmp, hwa, hf, he, hpre, hfinal⟩ :=
      paired_absent_prefix_mass hw hM honeF honeEA heD0 heF hR HB.ea_lower
    have hDpos : 0 < totalMass (avoidWeight ν (Z ∪ (C ∪ (E ∩ B)))) := by
      have hDle := expCard_mono hw.nn
        (subset_union_left (s₁ := Z ∪ (C ∪ (E ∩ B))) (s₂ := F))
      have hh := hw.avoid_mass_ge (Z ∪ (C ∪ (E ∩ B)))
      have hcap : 1 / 2 + 3 * epsilon + 2 * r + d₀ + 2 * h < (1 : ℝ) := by
        norm_num [epsilon, K, h, r, d₀]
      linarith only [hDle, hh, hcap, hR]
    have hDmean : expCard ν (Z ∪ (C ∪ (E ∩ B))) ≤
        3 * epsilon + h + 2 * r + d₀ := by
      have hh := expCard_union_le hw.nn Z (C ∪ (E ∩ B))
      linarith only [hh, hZ, HB.zero_upper]
    refine ⟨hwa, hmp, hf, he,
      fun T hT => honeEA T (avoidDist_ne_zero_imp hT).1, hpre, hfinal,
      HB.a_lower.trans (hw.avoid_ge haD0 hDpos), ?_, ?_⟩
    · have hh := avoid_overlap_le hw (A \ E) (Z ∪ (C ∪ (E ∩ B))) hDpos
      linarith only [hh, HB.a_upper, hDmean, hd0]
    · have hh := avoid_overlap_le hw (B \ F) (Z ∪ (C ∪ (E ∩ B))) hDpos
      linarith only [hh, HB.b_upper, hDmean, hd0]
  · intro hZ
    have hR : expCard ν ((C ∪ (E ∩ B)) ∪ F) ≤
        1 / 2 + 2 * r + 2 * h + 4 * d₀ := by
      linarith only [HB.union_upper, hd0]
    obtain ⟨hmp, hwa, hf, he, hpre, hfinal⟩ :=
      paired_present_prefix_mass hw hM honeZ honeF honeEA hRZ heZ heD heF hZ hR HB.ea_lower
    obtain ⟨hz, hd, _, _, _⟩ := present_prefix_setup hw hRZ honeZ honeF
      (lt_of_lt_of_le (by norm_num [epsilon, K, h]) hZ)
      (lt_of_le_of_lt hR (by norm_num [r, h, d₀]))
    have hDZ : Disjoint (C ∪ (E ∩ B)) Z :=
      disjoint_of_subset_left subset_union_left hRZ
    obtain ⟨haL, haU, hbU, _⟩ :=
      present_prefix_mean_bounds hw honeZ hz hd haZ hbZ heZ hDZ haD heD
    refine ⟨hwa, hmp, hf, he, fun T hT => honeEA T (present_prefix_support hT).1,
      hpre, hfinal, ?_, ?_, ?_⟩
    · linarith only [haL, HB.a_lower, hZ]
    · linarith only [haU, HB.a_upper, HB.zero_upper, hd0]
    · linarith only [hbU, HB.b_upper, HB.zero_upper, hd0]

/-- Original-law, fiber-tree export. All conditional means and one-hot
facts used by the prefixes are derived here, including arbitrary piece sides. -/
theorem paired_prefixes_indexed {n : ℕ} (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {rank : ℕ} (hw : LawData w rank) {u v z : Finset (Fin n)}
    (hc : M.ThreeAtomUzData w u v z)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) ≤ 3 * d₀)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ h)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ h)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ h) :
    PairedPrefixPair (M.tau3 w u v z) rank A B C (M.fiberOver (betweenEdges u v))
      (M.fiberOver (betweenEdges v z)) (M.fiberOver (betweenEdges u z))
      (totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
        (atomBudget u v z))) := by
  have H := paired_atom_law M hw hc hdef
  have G := paired_boundary_geometry M huv hvz huz hpart hAB hAC hBC
  have HB := paired_face_bounds hw.nn G H.lower H.upper hxE hxF hxA hxB hxC hxEB hxFA
  exact paired_prefix_pair H.law G HB H.mass_ge H.one_e H.one_f H.one_z

/-- Song's defect fits the existing dichotomy. Its two original central
rank probabilities remain explicit until the not-goodness producer is supplied. -/
theorem paired_dichotomy_indexed {n : ℕ} (M : FiberTreeModel ι n) {w : Finset ι → ℝ}
    {k : ℕ} (hw : LawData w (k + 1)) {u v z : Finset (Fin n)}
    (hu : u.Nonempty) (hv : v.Nonempty) (hz : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hc : M.ThreeAtomUzData w u v z) {A B : Finset ι}
    (hA : A ⊆ M.fiberOver (cutEdges v)) (hB : B ⊆ M.fiberOver (cutEdges v))
    (hAB : Disjoint A B)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) ≤ 3 * d₀)
    (hX : 1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card +
        (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2))
    (hY : 1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card +
        (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)) :
    expCard (M.tau3 w u v z) (M.fiberOver (betweenEdges u z)) ≤ 3 * epsilon ∨
      1 - 3 * epsilon ≤ expCard (M.tau3 w u v z) (M.fiberOver (betweenEdges u z)) := by
  exact lemma_5_27_dichotomy_indexed M hw.st hw.rank hw.nn hw.tot hu hv hz huv hvz huz hc
    hA hB hAB (by norm_num [d₀]) (by norm_num [d₀])
    (by norm_num [epsilon, K, h]) (by norm_num [epsilon, K, h]) hdef hX hY

end TSPGap.Song

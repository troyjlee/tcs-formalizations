/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGIntersections
import TSPGap.TuckerTheorem7

/-!
# The Benczúr–Goemans polygon core, III: the representation

`polygonRep_exists_of_connected`: a family `𝒞` of at least two sets avoiding a root `r`,
connected under `Crossing`, whose symmetric closure has no 3-cycle, no 4-cycle and no comb,
has a `PolygonRep` with root atom `atomOf 𝒞 r`.  This is BG08 Theorem 4 in the repository's
interval encoding, with the no-4-cycle hypothesis replacing BG08's duplicated-vertex
construction (BG08 Proposition 20).

The construction:

* `F := symmetrize 𝒞` is a BG family (`isBGFamily_symmetrize`);
* the outside atoms are `O := {a ∈ atoms 𝒞 : no cycle of F avoids a}` (BG08 Definition 4 /
  KKO22 Lemma 4.20), which is the `outside_iff_no_avoiding_kCycle` field verbatim;
* the cyclic order is Tucker's: the pivot family on `O` is Tucker-free (BG08 Corollary 7,
  `isTuckerFree_pivotFamily`), hence has the consecutive-ones property (Tucker's Theorem 7
  through `hasConsecutiveOnes_of_tuckerFree_tucker`), hence `rowsOn F O` has the
  circular-ones property, and `CircularOnesData` provides `enum`, `start`, `len`;
* `two_le_len`, `len_le`, `hm` and `cross_arc` come from outside elements in the four regions
  of a crossing pair (BG08 Corollary 14, `outside_regions`);
* `arc_injective` is BG08 Propositions 15 and 20 (`eq_of_same_trace`) and `arcs_ne_univ` is
  KKO22 Fact 4.8, proved from Corollary 14 and Proposition 20 (`not_cover`).
-/

namespace TSPGap
open Finset

variable {n : ℕ}

namespace BG

section Assembly

variable {𝒞 : Finset (Finset (Fin n))} {r : Fin n}

/-- Every member of a connected family with at least two members crosses another member. -/
theorem exists_cross (hcard : 2 ≤ 𝒞.card)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    {S : Finset (Fin n)} (hS : S ∈ 𝒞) : ∃ T ∈ 𝒞, Crossing S T := by
  obtain ⟨T', hT', hne⟩ : ∃ T' ∈ 𝒞, T' ≠ S := by
    by_contra hcon
    push Not at hcon
    have hsub : 𝒞 ⊆ {S} := fun X hX => mem_singleton.mpr (hcon X hX)
    have := card_le_card hsub
    simp at this
    omega
  rcases (hconn S hS T' hT').cases_head with heq | ⟨c, ⟨-, hc, hSc⟩, -⟩
  · exact absurd heq.symm hne
  · exact ⟨c, hc, hSc⟩

/-- The symmetric closure of a connected rooted family with at least two members is a BG
family. -/
theorem isBGFamily_symmetrize (hcard : 2 ≤ 𝒞.card)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hroot : ∀ S ∈ 𝒞, r ∉ S) (hno3 : NoKCycle (symmetrize 𝒞) 3)
    (hnocomb : NoComb (symmetrize 𝒞)) : IsBGFamily (symmetrize 𝒞) where
  sym := fun _ hS => compl_mem_symmetrize hS
  conn := by
    have rev : ∀ {A B : Finset (Fin n)},
        Relation.ReflTransGen (fun A B => A ∈ symmetrize 𝒞 ∧ B ∈ symmetrize 𝒞 ∧ Crossing A B)
          A B →
        Relation.ReflTransGen (fun A B => A ∈ symmetrize 𝒞 ∧ B ∈ symmetrize 𝒞 ∧ Crossing A B)
          B A := by
      intro A B h
      induction h with
      | refl => exact .refl
      | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih
    have lift : ∀ S T, Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T →
        Relation.ReflTransGen (fun A B => A ∈ symmetrize 𝒞 ∧ B ∈ symmetrize 𝒞 ∧ Crossing A B)
          S T := by
      intro S T h
      induction h with
      | refl => exact .refl
      | tail _ hbc ih =>
        exact ih.tail ⟨mem_symmetrize_of_mem hbc.1, mem_symmetrize_of_mem hbc.2.1, hbc.2.2⟩
    have reach : ∀ S ∈ symmetrize 𝒞, ∃ S' ∈ 𝒞,
        Relation.ReflTransGen (fun A B => A ∈ symmetrize 𝒞 ∧ B ∈ symmetrize 𝒞 ∧ Crossing A B)
          S S' := by
      intro S hS
      rcases mem_symmetrize.mp hS with h | h
      · exact ⟨S, h, .refl⟩
      · obtain ⟨T, hT, hc⟩ := exists_cross hcard hconn h
        exact ⟨T, hT, .single ⟨hS, mem_symmetrize_of_mem hT, by simpa using hc.compl_left⟩⟩
    intro S hS T hT
    obtain ⟨S', hS', h1⟩ := reach S hS
    obtain ⟨T', hT', h2⟩ := reach T hT
    exact h1.trans ((lift _ _ (hconn S' hS' T' hT')).trans (rev h2))
  no3 := hno3
  nocomb := hnocomb
  nonempty := by
    intro S hS
    rcases mem_symmetrize.mp hS with h | h
    · obtain ⟨T, hT, hc⟩ := exists_cross hcard hconn h
      exact hc.1.mono inter_subset_left
    · exact ⟨r, by simpa using hroot _ h⟩

/-- An atom has an avoiding cycle iff its elements are inside. -/
theorem hasAvoidingKCycle_iff_inside {F : Finset (Finset (Fin n))} {a : Finset (Fin n)}
    (ha : a ∈ atoms F) {v : Fin n} (hv : v ∈ a) : HasAvoidingKCycle F a ↔ Inside F v := by
  constructor
  · rintro ⟨k, D, hD, hmem, hav⟩
    exact ⟨k, D, hD, hmem, fun i hi hvi => disjoint_left.mp (hav i hi) hv hvi⟩
  · rintro ⟨k, D, hD, hmem, hav⟩
    refine ⟨k, D, hD, hmem, fun i hi => ?_⟩
    rcases atom_subset_or_disjoint ha (hmem i hi) with h | h
    · exact absurd (h hv) (hav i hi)
    · exact h

/-- Clipping an arc length at `m` does not change the arc. -/
theorem arcSet_min {m : ℕ} (s : Fin m) (l : ℕ) : arcSet s (min l m) = arcSet s l := by
  ext i
  simp only [mem_arcSet]
  have := (i - s).isLt
  omega

/-- **BG08 Theorem 4 in interval form.**  A family of at least two sets avoiding `r`,
connected under crossing, whose symmetric closure has no 3-cycle, no 4-cycle and no comb, has
a polygon representation with root atom `atomOf 𝒞 r`. -/
theorem polygonRep_exists_of_connected (hcard : 2 ≤ 𝒞.card)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hroot : ∀ S ∈ 𝒞, r ∉ S) (hno3 : NoKCycle (symmetrize 𝒞) 3)
    (hno4 : NoKCycle (symmetrize 𝒞) 4) (hnocomb : NoComb (symmetrize 𝒞)) :
    ∃ P : PolygonRep 𝒞, P.rootAtom = atomOf 𝒞 r := by
  classical
  have hF : IsBGFamily (symmetrize 𝒞) := isBGFamily_symmetrize hcard hconn hroot hno3 hnocomb
  have hatoms : atoms (symmetrize 𝒞) = atoms 𝒞 := atoms_symmetrize 𝒞
  -- the outside atoms
  set O : Finset (Finset (Fin n)) :=
    (atoms 𝒞).filter fun a => ¬ HasAvoidingKCycle (symmetrize 𝒞) a with hOdef
  have mem_O : ∀ a, a ∈ O ↔ a ∈ atoms 𝒞 ∧ ¬ HasAvoidingKCycle (symmetrize 𝒞) a :=
    fun a => mem_filter
  have hO : O ⊆ atoms (symmetrize 𝒞) := fun a ha => hatoms ▸ ((mem_O a).mp ha).1
  have atom_mem_O : ∀ v, atomOf 𝒞 v ∈ O ↔ ¬ Inside (symmetrize 𝒞) v := by
    intro v
    rw [mem_O]
    have ha : atomOf 𝒞 v ∈ atoms (symmetrize 𝒞) := hatoms ▸ mem_atoms.mpr ⟨v, rfl⟩
    rw [hasAvoidingKCycle_iff_inside ha (mem_atomOf_self 𝒞 v)]
    exact ⟨fun h => h.2, fun h => ⟨mem_atoms.mpr ⟨v, rfl⟩, h⟩⟩
  have hout : ∀ a ∈ O, ∀ (k : ℕ) (D : ℕ → Finset (Fin n)), IsKCycle k D →
      (∀ i < k, D i ∈ symmetrize 𝒞) → ∃ i < k, a ⊆ D i := by
    intro a ha k D hD hmem
    by_contra hcon
    push Not at hcon
    exact ((mem_O a).mp ha).2 ⟨k, D, hD, hmem, fun i hi =>
      Tucker.atom_disjoint_of_not_subset (hO ha) (hmem i hi) (hcon i hi)⟩
  -- a pivot
  obtain ⟨S₀, hS₀⟩ : 𝒞.Nonempty := card_pos.mp (by omega)
  obtain ⟨v₀, -, hv₀⟩ := hF.exists_outside_mem (mem_symmetrize_of_mem hS₀)
  have hp : atomOf 𝒞 v₀ ∈ O := (atom_mem_O v₀).mpr hv₀
  -- Tucker: the rows on the outside atoms have the circular-ones property
  have hrows : ∀ R ∈ Tucker.rowsOn (symmetrize 𝒞) O, R ⊆ O := by
    intro R hR
    obtain ⟨S, -, rfl⟩ := mem_image.mp hR
    exact inter_subset_right
  have hcirc : CircularOnes.HasCircularOnes O (Tucker.rowsOn (symmetrize 𝒞) O) :=
    (CircularOnes.hasCircularOnes_iff_hasConsecutiveOnes_pivot hp hrows).mpr
      (Tucker.hasConsecutiveOnes_of_tuckerFree_tucker
        (Tucker.isTuckerFree_pivotFamily hF.sym hno3 hnocomb hO hout hp))
  have hO0 : 0 < O.card := card_pos.mpr ⟨_, hp⟩
  obtain ⟨data⟩ := CircularOnes.exists_data_of_hasCircularOnes hcirc hO0
  haveI : NeZero O.card := ⟨hO0.ne'⟩
  -- the data
  let out : Fin O.card → Finset (Fin n) := fun i => (data.enum i : Finset (Fin n))
  let row : Finset (Fin n) → Finset (Finset (Fin n)) := fun S =>
    Tucker.atomRow (symmetrize 𝒞) S ∩ O
  let start : Finset (Fin n) → Fin O.card := fun S => data.start (row S)
  let len : Finset (Fin n) → ℕ := fun S => min (data.len (row S)) O.card
  have out_mem_O : ∀ i, out i ∈ O := fun i => (data.enum i).2
  have exists_idx : ∀ a ∈ O, ∃ i, out i = a := fun a ha =>
    ⟨data.enum.symm ⟨a, ha⟩, by simp [out]⟩
  have out_inj : Function.Injective out := fun i j h => data.enum.injective (Subtype.ext h)
  have out_atom : ∀ i, out i ∈ atoms 𝒞 := fun i => ((mem_O _).mp (out_mem_O i)).1
  have arc_spec : ∀ S ∈ 𝒞, ∀ i, (out i ⊆ S ↔ i ∈ arcSet (start S) (len S)) := by
    intro S hS i
    have hR : row S ∈ Tucker.rowsOn (symmetrize 𝒞) O :=
      mem_image_of_mem _ (mem_symmetrize_of_mem hS)
    have := data.outside_eq_arc _ hR i
    change out i ⊆ S ↔ i ∈ arcSet (data.start (row S)) (min (data.len (row S)) O.card)
    rw [arcSet_min, ← this, mem_inter, Tucker.mem_atomRow]
    exact ⟨fun h => ⟨⟨hO (out_mem_O i), h⟩, out_mem_O i⟩, fun h => h.1.2⟩
  have len_le_m : ∀ S, len S ≤ O.card := fun S => min_le_right _ _
  have card_arc : ∀ S, (arcSet (start S) (len S)).card = len S :=
    fun S => arcSet_card _ (len_le_m S)
  -- outside elements and their atoms
  have mem_iff_sub : ∀ S ∈ 𝒞, ∀ v, v ∈ S ↔ atomOf 𝒞 v ⊆ S := fun S hS v =>
    ⟨atomOf_subset_of_mem hS, fun h => h (mem_atomOf_self 𝒞 v)⟩
  have idx_of_outside : ∀ v, ¬ Inside (symmetrize 𝒞) v → ∃ i, out i = atomOf 𝒞 v :=
    fun v hv => exists_idx _ ((atom_mem_O v).mpr hv)
  -- the four regions of a crossing pair, as indices
  have regions : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞, Crossing S T → ∃ i₁ i₂ i₃ i₄ : Fin O.card,
      (out i₁ ⊆ S ∧ out i₁ ⊆ T) ∧ (out i₂ ⊆ S ∧ ¬ out i₂ ⊆ T) ∧
        (¬ out i₃ ⊆ S ∧ out i₃ ⊆ T) ∧ (¬ out i₄ ⊆ S ∧ ¬ out i₄ ⊆ T) := by
    intro S hS T hT hc
    obtain ⟨⟨v₁, h₁S, h₁T, h₁o⟩, ⟨v₂, h₂S, h₂T, h₂o⟩, ⟨v₃, h₃S, h₃T, h₃o⟩, ⟨v₄, h₄S, h₄T, h₄o⟩⟩ :=
      hF.outside_regions (mem_symmetrize_of_mem hS) (mem_symmetrize_of_mem hT) hc
    obtain ⟨i₁, e₁⟩ := idx_of_outside v₁ h₁o
    obtain ⟨i₂, e₂⟩ := idx_of_outside v₂ h₂o
    obtain ⟨i₃, e₃⟩ := idx_of_outside v₃ h₃o
    obtain ⟨i₄, e₄⟩ := idx_of_outside v₄ h₄o
    refine ⟨i₁, i₂, i₃, i₄, ?_, ?_, ?_, ?_⟩ <;> simp only [e₁, e₂, e₃, e₄]
    · exact ⟨(mem_iff_sub S hS v₁).mp h₁S, (mem_iff_sub T hT v₁).mp h₁T⟩
    · exact ⟨(mem_iff_sub S hS v₂).mp h₂S, fun h => h₂T ((mem_iff_sub T hT v₂).mpr h)⟩
    · exact ⟨fun h => h₃S ((mem_iff_sub S hS v₃).mpr h), (mem_iff_sub T hT v₃).mp h₃T⟩
    · exact ⟨fun h => h₄S ((mem_iff_sub S hS v₄).mpr h), fun h => h₄T ((mem_iff_sub T hT v₄).mpr h)⟩
  -- lengths
  have two_le_len : ∀ S ∈ 𝒞, 2 ≤ len S := by
    intro S hS
    obtain ⟨T, hT, hc⟩ := exists_cross hcard hconn hS
    obtain ⟨i₁, i₂, -, -, ⟨h₁S, h₁T⟩, ⟨h₂S, h₂T⟩, -, -⟩ := regions S hS T hT hc
    have hne : i₁ ≠ i₂ := fun e => h₂T (e ▸ h₁T)
    have hsub : ({i₁, i₂} : Finset (Fin O.card)) ⊆ arcSet (start S) (len S) := by
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact (arc_spec S hS _).mp h₁S
      · rw [mem_singleton.mp hi]
        exact (arc_spec S hS _).mp h₂S
    have := card_le_card hsub
    rw [card_pair hne, card_arc] at this
    exact this
  have len_le : ∀ S ∈ 𝒞, len S ≤ O.card - 2 := by
    intro S hS
    obtain ⟨T, hT, hc⟩ := exists_cross hcard hconn hS
    obtain ⟨-, -, i₃, i₄, -, -, ⟨h₃S, h₃T⟩, ⟨h₄S, h₄T⟩⟩ := regions S hS T hT hc
    have hne : i₃ ≠ i₄ := fun e => h₄T (e ▸ h₃T)
    have hdisj : Disjoint (arcSet (start S) (len S)) {i₃, i₄} := by
      rw [disjoint_left]
      intro i hi hi'
      rcases mem_insert.mp hi' with rfl | hi'
      · exact h₃S ((arc_spec S hS _).mpr hi)
      · rw [mem_singleton.mp hi'] at hi
        exact h₄S ((arc_spec S hS _).mpr hi)
    have h1 := card_le_univ (arcSet (start S) (len S) ∪ {i₃, i₄})
    rw [card_union_eq_card_add_card.mpr hdisj, card_pair hne, card_arc, Fintype.card_fin] at h1
    omega
  have hm : 4 ≤ O.card := by
    have h1 := two_le_len S₀ hS₀
    have h2 := len_le S₀ hS₀
    omega
  -- the representation
  refine ⟨⟨O.card, hm, out, out_atom, out_inj, ?_, hcard, start, len, two_le_len, len_le,
    arc_spec, ?_, ?_, atomOf 𝒞 r, mem_atoms.mpr ⟨r, rfl⟩,
    fun S hS => atomOf_disjoint_of_notMem hS (hroot S hS), ?_⟩, rfl⟩
  · -- `outside_iff_no_avoiding_kCycle`
    intro a ha
    constructor
    · intro h
      obtain ⟨i, -, rfl⟩ := mem_image.mp h
      exact ((mem_O _).mp (out_mem_O i)).2
    · intro h
      obtain ⟨i, hi⟩ := exists_idx a ((mem_O a).mpr ⟨ha, h⟩)
      exact mem_image.mpr ⟨i, mem_univ _, hi⟩
  · -- `arc_injective`
    intro S hS S' hS' hstart hlen
    refine hF.eq_of_same_trace hno4 (mem_symmetrize_of_mem hS) (mem_symmetrize_of_mem hS')
      fun v hv => ?_
    obtain ⟨i, hi⟩ := idx_of_outside v hv
    rw [mem_iff_sub S hS, mem_iff_sub S' hS', ← hi, arc_spec S hS, arc_spec S' hS', hstart, hlen]
  · -- `cross_arc`
    intro S hS S' hS' hc
    obtain ⟨i₁, i₂, i₃, i₄, ⟨h₁S, h₁T⟩, ⟨h₂S, h₂T⟩, ⟨h₃S, h₃T⟩, ⟨h₄S, h₄T⟩⟩ :=
      regions S hS S' hS' hc
    exact crossing_of_witnesses ((arc_spec S hS _).mp h₁S) ((arc_spec S' hS' _).mp h₁T)
      ((arc_spec S hS _).mp h₂S) (fun h => h₂T ((arc_spec S' hS' _).mpr h))
      ((arc_spec S' hS' _).mp h₃T) (fun h => h₃S ((arc_spec S hS _).mpr h))
      (fun h => h₄S ((arc_spec S hS _).mpr h)) (fun h => h₄T ((arc_spec S' hS' _).mpr h))
  · -- `arcs_ne_univ`
    intro S hS S' hS' heq
    refine hF.not_cover hno4 (mem_symmetrize_of_mem hS) (mem_symmetrize_of_mem hS')
      (hroot S hS) (hroot S' hS') fun v hv => ?_
    obtain ⟨i, hi⟩ := idx_of_outside v hv
    have : i ∈ arcSet (start S) (len S) ∪ arcSet (start S') (len S') := heq ▸ mem_univ i
    rcases mem_union.mp this with h | h
    · exact Or.inl ((mem_iff_sub S hS v).mpr (hi ▸ (arc_spec S hS i).mpr h))
    · exact Or.inr ((mem_iff_sub S' hS' v).mpr (hi ▸ (arc_spec S' hS' i).mpr h))

/-- **The polygon of a family of near-minimum cuts.**  A crossing-connected family of at
least two `η`-near minimum cuts avoiding a root `r`, `η < 2/5`, has a polygon representation
with root atom `atomOf 𝒞 r`: its symmetric closure has no 3-cycle and no 4-cycle by BG08
Lemma 22 (`noKCycle_of_nearMin`) and no comb by BG08 Lemma 23 (`noComb_of_nearMin`). -/
theorem polygonRep_exists_of_nearMin {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) {η : ℝ}
    (hη : η < 2 / 5) (hnm : ∀ S ∈ 𝒞, IsNearMinCut x η S) (hroot : ∀ S ∈ 𝒞, r ∉ S)
    (hconn : ∀ S ∈ 𝒞, ∀ T ∈ 𝒞,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S T)
    (hns : 2 ≤ 𝒞.card) : ∃ P : PolygonRep 𝒞, P.rootAtom = atomOf 𝒞 r :=
  have hnm' : ∀ S ∈ symmetrize 𝒞, IsNearMinCut x η S :=
    fun _ hS => isNearMinCut_of_mem_symmetrize hnm hS
  polygonRep_exists_of_connected hns hconn hroot
    (noKCycle_of_nearMin hx hnm' hη.le (by norm_num)) (noKCycle_of_nearMin hx hnm' hη.le le_rfl)
    (noComb_of_nearMin hx hnm' hη)

end Assembly

end BG

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Uncrossing

/-!
# The polygon representation of crossing near-minimum cuts (KKO22 §4.1)

Phase 2 of the roadmap.  This file lays the combinatorial foundation:

## Atoms (KKO22 Definition 4.1)

For a family `𝒞` of cuts, `atomOf 𝒞 u` is the set of vertices lying on the
same side of every cut of `𝒞` as `u`.  The atoms are the classes of this
(finite, decidable) equivalence; every cut of `𝒞` is a union of atoms
(`atomOf_subset_of_mem` / `atomOf_disjoint_of_notMem`).  This layer is
fully proved.

## Crossing components

`IsCrossingComponent x η 𝒞`: a nonempty family of η-near-min cuts of `x`,
connected under `Crossing` (via `Relation.ReflTransGen`), and maximal.

## The polygon representation, interval form (**prototype encoding**)

The Benczúr–Goemans polygon representation (KKO22 §4.1, properties 1–4)
places the `m` *outside atoms* of a component on the sides of a convex
`m`-gon, one atom per side, and realizes every cut of the component as a
straight *representing diagonal*; *inside atoms* occupy interior cells.
We axiomatize its combinatorial content, discarding the geometry:

* `arcSet start len` — the cyclic interval `{start, …, start + len - 1}`
  of `Fin m`, encoded by wrap-around subtraction (`(i - start).val < len`);
* `PolygonRep 𝒞` — a cyclic labelling `out : Fin m → _` of the outside
  atoms together with, for each cut `S ∈ 𝒞`, an arc `(start S, len S)`
  such that the outside atoms inside `S` are exactly the atoms of the arc
  (`outside_eq_arc`), with `2 ≤ len S ≤ m - 2` (both sides of a diagonal
  span at least two polygon sides — Fact 4.2) and cuts determined by
  their arcs (`arc_injective`, from property 4: diagonals ↔ cuts).

The geometric picture is recovered by reading `start S` and
`start S + len S` as the two polygon points of the representing diagonal
of `S`.  Inside atoms are the derived `insideAtoms P`.

Existence of the representation for `η ≤ 2/5` ([Ben97, Ch. 4], [BG08]) is
the declared black box `polygonRep_exists` in `TSPGap/BlackBoxes.lean`.
This encoding is a *prototype* (roadmap Phase 2 explicitly budgets for
revising it); the sanity lemmas at the end (`outsideIn_eq_arc`,
`two_le_card_outsideIn`, Fact 4.2) exercise it.
-/

namespace TSPGap

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ}
  {𝒞 : Finset (Finset (Fin n))} {S : Finset (Fin n)} {u v : Fin n}

/-! ### Atoms of a family of cuts -/

/-- The atom of `u` for the family `𝒞`: all vertices lying on the same
side of every cut of `𝒞` as `u` (KKO22 Definition 4.1). -/
def atomOf (𝒞 : Finset (Finset (Fin n))) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∀ S ∈ 𝒞, (u ∈ S ↔ v ∈ S)

theorem mem_atomOf : v ∈ atomOf 𝒞 u ↔ ∀ S ∈ 𝒞, (u ∈ S ↔ v ∈ S) := by
  simp [atomOf]

theorem mem_atomOf_self (𝒞 : Finset (Finset (Fin n))) (u : Fin n) :
    u ∈ atomOf 𝒞 u :=
  mem_atomOf.mpr fun _ _ => Iff.rfl

theorem atomOf_nonempty (𝒞 : Finset (Finset (Fin n))) (u : Fin n) :
    (atomOf 𝒞 u).Nonempty :=
  ⟨u, mem_atomOf_self 𝒞 u⟩

/-- Atoms are the classes of an equivalence: membership is symmetric and
transitive, so equal atoms or disjoint. -/
theorem atomOf_eq_of_mem (h : v ∈ atomOf 𝒞 u) : atomOf 𝒞 v = atomOf 𝒞 u := by
  rw [mem_atomOf] at h
  ext w
  rw [mem_atomOf, mem_atomOf]
  exact ⟨fun hw S hS => (h S hS).trans (hw S hS),
    fun hw S hS => (h S hS).symm.trans (hw S hS)⟩

theorem atomOf_eq_or_disjoint (𝒞 : Finset (Finset (Fin n))) (u v : Fin n) :
    atomOf 𝒞 u = atomOf 𝒞 v ∨ Disjoint (atomOf 𝒞 u) (atomOf 𝒞 v) := by
  by_cases h : Disjoint (atomOf 𝒞 u) (atomOf 𝒞 v)
  · exact Or.inr h
  · left
    obtain ⟨w, hwu, hwv⟩ := Finset.not_disjoint_iff.mp h
    rw [← atomOf_eq_of_mem hwu, ← atomOf_eq_of_mem hwv]

/-- Cuts of the family are unions of atoms: the atom of a member is
contained in the cut. -/
theorem atomOf_subset_of_mem (hS : S ∈ 𝒞) (hu : u ∈ S) : atomOf 𝒞 u ⊆ S :=
  fun _ hv => (mem_atomOf.mp hv S hS).mp hu

/-- ... and the atom of a non-member is disjoint from the cut. -/
theorem atomOf_disjoint_of_notMem (hS : S ∈ 𝒞) (hu : u ∉ S) :
    Disjoint (atomOf 𝒞 u) S :=
  Finset.disjoint_left.mpr fun {_} hv hvS =>
    hu ((mem_atomOf.mp hv S hS).mpr hvS)

/-- The atoms of the family. -/
def atoms (𝒞 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  Finset.univ.image (atomOf 𝒞)

theorem mem_atoms {A : Finset (Fin n)} :
    A ∈ atoms 𝒞 ↔ ∃ u, atomOf 𝒞 u = A := by
  simp [atoms]

/-- Every atom is contained in, or disjoint from, every cut of the
family. -/
theorem atom_subset_or_disjoint {A : Finset (Fin n)} (hA : A ∈ atoms 𝒞)
    (hS : S ∈ 𝒞) : A ⊆ S ∨ Disjoint A S := by
  obtain ⟨u, rfl⟩ := mem_atoms.mp hA
  by_cases hu : u ∈ S
  · exact Or.inl (atomOf_subset_of_mem hS hu)
  · exact Or.inr (atomOf_disjoint_of_notMem hS hu)

/-! ### `k`-cycles (KKO22 Definition 4.18 = [BG08, Definition 3]) -/

/-- A `k`-cycle: `k ≥ 3` sets, cyclically indexed by `ℕ` modulo `k`, with
consecutive sets crossing, non-consecutive sets disjoint, union not
everything, and (for `k = 3`) no set containing the intersection of the
other two.  `k`-cycles certify inside atoms (KKO22 Lemma 4.20) and cannot
be short (Lemma 4.19). -/
structure IsKCycle (k : ℕ) (C : ℕ → Finset (Fin n)) : Prop where
  three_le : 3 ≤ k
  cross_succ : ∀ i < k, Crossing (C i) (C ((i + 1) % k))
  disjoint_far : ∀ i < k, ∀ j < k, j ≠ (i + k - 1) % k → j ≠ i →
    j ≠ (i + 1) % k → Disjoint (C i) (C j)
  union_ne : (Finset.range k).biUnion C ≠ Finset.univ
  three_cond : k = 3 → ∀ i < k, ¬ (C i ∩ C ((i + 1) % k) ⊆ C ((i + k - 1) % k))

/-- The three-set instance of `IsKCycle`, spelled out. -/
structure IsThreeCycle (A B C : Finset (Fin n)) : Prop where
  crossAB : Crossing A B
  crossBC : Crossing B C
  crossCA : Crossing C A
  union_ne : A ∪ B ∪ C ≠ Finset.univ
  interAB : ¬ (A ∩ B ⊆ C)
  interBC : ¬ (B ∩ C ⊆ A)
  interCA : ¬ (C ∩ A ⊆ B)

/-- The cyclic family of a three-cycle. -/
def cyc3 (A B C : Finset (Fin n)) : ℕ → Finset (Fin n) := fun i =>
  if i % 3 = 0 then A else if i % 3 = 1 then B else C

theorem IsThreeCycle.isKCycle {A B C : Finset (Fin n)}
    (h : IsThreeCycle A B C) : IsKCycle 3 (cyc3 A B C) := by
  constructor
  · exact le_rfl
  · intro i hi
    interval_cases i <;> simp only [cyc3] <;> norm_num
    · exact h.crossAB
    · exact h.crossBC
    · exact h.crossCA
  · intro i hi j hj h1 h2 h3
    interval_cases i <;> interval_cases j <;> simp_all
  · rw [show Finset.range 3 = ({0, 1, 2} : Finset ℕ) from rfl]
    simp only [Finset.biUnion_insert, Finset.singleton_biUnion, cyc3]
    norm_num
    rw [← Finset.union_assoc]
    exact h.union_ne
  · intro _ i hi
    interval_cases i <;> simp only [cyc3] <;> norm_num
    · exact h.interAB
    · exact h.interBC
    · exact h.interCA

/-! ### Crossing-connected components -/

/-- A (maximal) connected component of crossing `η`-near minimum cuts
(KKO22 Definition 4.1): every member is an `η`-near min cut, members are
connected through crossings inside `𝒞`, and any `η`-near min cut crossing
a member belongs to `𝒞`. -/
structure IsCrossingComponent (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (𝒞 : Finset (Finset (Fin n))) : Prop where
  nonempty : 𝒞.Nonempty
  nearMin : ∀ S ∈ 𝒞, IsNearMinCut x η S
  conn : ∀ S ∈ 𝒞, ∀ S' ∈ 𝒞,
    Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) S S'
  maximal : ∀ S, IsNearMinCut x η S → (∃ S' ∈ 𝒞, Crossing S S') → S ∈ 𝒞

/-- Atoms are nonempty. -/
theorem atoms_nonempty {a : Finset (Fin n)} (ha : a ∈ atoms 𝒞) : a.Nonempty := by
  obtain ⟨u, rfl⟩ := mem_atoms.mp ha
  exact atomOf_nonempty 𝒞 u

/-- Distinct atoms are disjoint. -/
theorem atoms_disjoint {a b : Finset (Fin n)} (ha : a ∈ atoms 𝒞)
    (hb : b ∈ atoms 𝒞) (hne : a ≠ b) : Disjoint a b := by
  obtain ⟨u, rfl⟩ := mem_atoms.mp ha
  obtain ⟨v, rfl⟩ := mem_atoms.mp hb
  exact (atomOf_eq_or_disjoint 𝒞 u v).resolve_left hne

/-! ### Every near-minimum cut lies in a crossing component

The crossing relation on `η`-near min cuts is symmetric, so reachability
under it is an equivalence; the reachability class of a cut `B` is a
crossing component containing `B` (`isCrossingComponent_crossComp`).  This
is the component decomposition implicit in KKO22 Definition 4.1, and it is
what lets Lemma 4.6 speak of "the other component" containing a cut. -/

/-- Two `η`-near minimum cuts that cross. -/
def CrossRel (x : Sym2 (Fin n) → ℝ) (η : ℝ) (A B : Finset (Fin n)) : Prop :=
  IsNearMinCut x η A ∧ IsNearMinCut x η B ∧ Crossing A B

theorem CrossRel.symm' {A B : Finset (Fin n)} (h : CrossRel x η A B) :
    CrossRel x η B A := ⟨h.2.1, h.1, h.2.2.symm⟩

/-- The crossing-reachability class of `B` among `η`-near minimum cuts. -/
noncomputable def crossComp (x : Sym2 (Fin n) → ℝ) (η : ℝ) (B : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  letI : DecidablePred fun S : Finset (Fin n) =>
      Relation.ReflTransGen (CrossRel x η) B S := fun _ => Classical.propDecidable _
  Finset.univ.filter fun S => Relation.ReflTransGen (CrossRel x η) B S

theorem mem_crossComp {B S : Finset (Fin n)} :
    S ∈ crossComp x η B ↔ Relation.ReflTransGen (CrossRel x η) B S := by
  letI : DecidablePred fun S : Finset (Fin n) =>
      Relation.ReflTransGen (CrossRel x η) B S := fun _ => Classical.propDecidable _
  rw [crossComp, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Reachability from a near-min cut stays inside the near-min cuts. -/
theorem isNearMinCut_of_reflTransGen {B S : Finset (Fin n)}
    (hB : IsNearMinCut x η B) (h : Relation.ReflTransGen (CrossRel x η) B S) :
    IsNearMinCut x η S := by
  induction h with
  | refl => exact hB
  | tail _ hbc _ => exact hbc.2.1

/-- Crossing-reachability is symmetric. -/
theorem reflTransGen_crossRel_symm {A B : Finset (Fin n)}
    (h : Relation.ReflTransGen (CrossRel x η) A B) :
    Relation.ReflTransGen (CrossRel x η) B A := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm' ih

/-- A path inside the reachability class of `B` is a path in the
component-restricted relation. -/
theorem reflTransGen_restrict {B S S' : Finset (Fin n)}
    (hBS : Relation.ReflTransGen (CrossRel x η) B S)
    (h : Relation.ReflTransGen (CrossRel x η) S S') :
    Relation.ReflTransGen
      (fun A A' => A ∈ crossComp x η B ∧ A' ∈ crossComp x η B ∧ Crossing A A')
      S S' := by
  induction h with
  | refl => exact .refl
  | @tail c d hSc hcd ih =>
      exact ih.tail ⟨mem_crossComp.mpr (hBS.trans hSc),
        mem_crossComp.mpr ((hBS.trans hSc).tail hcd), hcd.2.2⟩

/-- The reachability class of a near-min cut is a crossing component. -/
theorem isCrossingComponent_crossComp {B : Finset (Fin n)}
    (hB : IsNearMinCut x η B) : IsCrossingComponent x η (crossComp x η B) := by
  refine ⟨⟨B, mem_crossComp.mpr .refl⟩, ?_, ?_, ?_⟩
  · intro S hS
    exact isNearMinCut_of_reflTransGen hB (mem_crossComp.mp hS)
  · intro S hS S' hS'
    exact reflTransGen_restrict (mem_crossComp.mp hS)
      ((reflTransGen_crossRel_symm (mem_crossComp.mp hS)).trans
        (mem_crossComp.mp hS'))
  · rintro S hS ⟨S', hS', hcross⟩
    refine mem_crossComp.mpr ((mem_crossComp.mp hS').tail ?_)
    exact ⟨isNearMinCut_of_reflTransGen hB (mem_crossComp.mp hS'), hS,
      hcross.symm⟩

/-- **Every near-minimum cut lies in a crossing component.** -/
theorem exists_isCrossingComponent_mem {B : Finset (Fin n)}
    (hB : IsNearMinCut x η B) :
    ∃ 𝒞', IsCrossingComponent x η 𝒞' ∧ B ∈ 𝒞' :=
  ⟨crossComp x η B, isCrossingComponent_crossComp hB, mem_crossComp.mpr .refl⟩

/-! ### Cyclic arcs of `Fin m` -/

/-- The cyclic arc `{start, start + 1, …, start + len - 1}` of `Fin m`,
encoded by wrap-around subtraction. -/
def arcSet {m : ℕ} (start : Fin m) (len : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => (i - start).val < len

theorem mem_arcSet {m : ℕ} {start i : Fin m} {len : ℕ} :
    i ∈ arcSet start len ↔ (i - start).val < len := by
  simp [arcSet]

/-- Complement of an arc, in subtraction form. -/
theorem mem_arcSet_compl {m : ℕ} {start i : Fin m} {len : ℕ} :
    i ∉ arcSet start len ↔ len ≤ (i - start).val := by
  rw [mem_arcSet, not_lt]

theorem arcSet_mono {m : ℕ} {start : Fin m} {len len' : ℕ}
    (h : len ≤ len') : arcSet start len ⊆ arcSet start len' := fun _ hi =>
  mem_arcSet.mpr (lt_of_lt_of_le (mem_arcSet.mp hi) h)

/-- The two wrap-around distances between distinct points sum to `m`. -/
theorem val_sub_add_val_sub {m : ℕ} [NeZero m] {s s' : Fin m}
    (hne : s ≠ s') : (s' - s).val + (s - s').val = m := by
  have hx : (s' - s) + (s - s') = 0 := by abel
  have h0 : ((s' - s).val + (s - s').val) % m = 0 := by
    have h := congrArg Fin.val hx
    rwa [Fin.val_add, Fin.val_zero] at h
  have h1 : (s' - s).val < m := Fin.is_lt _
  have h2 : (s - s').val < m := Fin.is_lt _
  have h3 : (s' - s).val ≠ 0 := by
    intro hc
    exact hne (sub_eq_zero.mp (Fin.val_injective (by simpa using hc))).symm
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
  match k, hk with
  | 0, hk => omega
  | 1, hk => omega
  | (k + 2), hk =>
    exfalso
    have hexp : m * (k + 2) = m * k + 2 * m := by ring
    rw [hexp] at hk
    set q := m * k with hq
    omega

/-- If two arcs each contain the other's start, together they cover the
whole cycle. -/
theorem arcSet_union_eq_univ {m : ℕ} [NeZero m] {s s' : Fin m} {l l' : ℕ}
    (hne : s ≠ s') (h1 : (s' - s).val < l) (h2 : (s - s').val < l') :
    arcSet s l ∪ arcSet s' l' = Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_arcSet]
  by_contra hcon
  push Not at hcon
  obtain ⟨hd, hd'⟩ := hcon
  have hab := val_sub_add_val_sub hne
  have hrel : (i - s).val = ((i - s').val + (s' - s).val) % m := by
    have h : i - s = (i - s') + (s' - s) := by abel
    rw [h, Fin.val_add]
  have hm2 : (i - s').val < m := Fin.is_lt _
  have hge : m ≤ (i - s').val + (s' - s).val := by omega
  have hx : ((i - s').val + (s' - s).val) % m
      = (i - s').val + (s' - s).val - m := by
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  rw [hx] at hrel
  omega

/-- If two arcs with distinct starts intersect, one of them contains the
other's start. -/
theorem arc_mem_or_mem_of_inter {m : ℕ} [NeZero m] {s s' : Fin m}
    {l l' : ℕ} (hne : s ≠ s')
    (hw : (arcSet s l ∩ arcSet s' l').Nonempty) :
    (s' - s).val < l ∨ (s - s').val < l' := by
  obtain ⟨w, hw⟩ := hw
  rw [Finset.mem_inter, mem_arcSet, mem_arcSet] at hw
  obtain ⟨hd, hd'⟩ := hw
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hab := val_sub_add_val_sub hne
  have hrel : (w - s').val = ((w - s).val + (s - s').val) % m := by
    have h : w - s' = (w - s) + (s - s') := by abel
    rw [h, Fin.val_add]
  have hlt : (w - s).val + (s - s').val < m := by omega
  rw [Nat.mod_eq_of_lt hlt] at hrel
  omega

/-- Wrap-around subtraction relative to two base points. -/
theorem val_sub_rel {m : ℕ} [NeZero m] (i s s' : Fin m) :
    (i - s).val = ((i - s').val + (s' - s).val) % m := by
  have h : i - s = (i - s') + (s' - s) := by abel
  rw [h, Fin.val_add]

/-- Wrap-around distances subtract along a common base point. -/
theorem val_sub_of_le {m : ℕ} [NeZero m] {s α β : Fin m}
    (h : (α - s).val ≤ (β - s).val) :
    (β - α).val = (β - s).val - (α - s).val := by
  rcases eq_or_ne α s with rfl | hne
  · simp
  · have hab := val_sub_add_val_sub hne
    have hrel := val_sub_rel β α s
    have hαs : 0 < (α - s).val := by
      rcases Nat.eq_zero_or_pos (α - s).val with h0 | h0
      · exact absurd (sub_eq_zero.mp (Fin.val_injective (by simpa using h0))) hne
      · exact h0
    have hsα : (s - α).val = m - (α - s).val := by omega
    have hβs : (β - s).val < m := Fin.is_lt _
    rw [hrel, hsα,
      show (β - s).val + (m - (α - s).val)
          = m + ((β - s).val - (α - s).val) by omega,
      Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)

/-- An arc contained in the span of another is a subset. -/
theorem arcSet_subset {m : ℕ} [NeZero m] {s s' : Fin m} {l l' : ℕ}
    (h : l' + (s' - s).val ≤ l) (hlm : l ≤ m) :
    arcSet s' l' ⊆ arcSet s l := by
  intro i hi
  rw [mem_arcSet] at hi ⊢
  have hrel := val_sub_rel i s s'
  have hlt : (i - s').val + (s' - s).val < m := by omega
  rw [hrel, Nat.mod_eq_of_lt hlt]
  omega

/-- Intersection of arcs when the second starts inside the first but the
first does not start inside the second: a single arc from the second
start. -/
theorem arcSet_inter_of_mem_of_notMem {m : ℕ} [NeZero m] {s s' : Fin m}
    {l l' : ℕ} (hne : s ≠ s') (hd : (s' - s).val < l)
    (hb : l' ≤ (s - s').val) :
    arcSet s l ∩ arcSet s' l'
      = arcSet s' (min l' (l - (s' - s).val)) := by
  ext i
  simp only [Finset.mem_inter, mem_arcSet]
  have hab := val_sub_add_val_sub hne
  have hrel := val_sub_rel i s s'
  constructor
  · rintro ⟨hA, hR⟩
    have hlt : (i - s').val + (s' - s).val < m := by omega
    rw [Nat.mod_eq_of_lt hlt] at hrel
    omega
  · intro hk
    have hlt : (i - s').val + (s' - s).val < m := by omega
    refine ⟨?_, by omega⟩
    rw [hrel, Nat.mod_eq_of_lt hlt]
    omega

/-- The last element of a nonempty arc. -/
theorem exists_last_mem_arcSet {m : ℕ} [NeZero m] (s : Fin m) {l : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ m) :
    ∃ i, (i - s).val = l - 1 ∧ i ∈ arcSet s l := by
  refine ⟨s + ⟨l - 1, by omega⟩, ?_, ?_⟩
  · rw [add_sub_cancel_left]
  · rw [mem_arcSet, add_sub_cancel_left]
    simp only []
    omega

/-- **Converse of `arcSet_subset`**: a contained arc lies within the span of
the containing one.  The wrap-around alternative — the small arc reaching the
big one's start from the left — is excluded by the point diametrically before
`s'`, which the big arc misses but the wrapped small arc would contain. -/
theorem le_of_arcSet_subset {m : ℕ} [NeZero m] {s s' : Fin m} {l l' : ℕ}
    (hsub : arcSet s l ⊆ arcSet s' l') (hl : 1 ≤ l) (hl' : l' < m) :
    (s - s').val + l ≤ l' := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hlm : l ≤ m := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hjval, -⟩ := exists_last_mem_arcSet s' (l := m) (by omega) le_rfl
    have hj : (j - s').val < l' := mem_arcSet.mp
      (hsub (mem_arcSet.mpr (lt_of_lt_of_le (Fin.is_lt _) (by omega))))
    omega
  have hs : s ∈ arcSet s l := by
    rw [mem_arcSet, sub_self]
    simp only [Fin.val_zero]
    omega
  have hc := mem_arcSet.mp (hsub hs)
  obtain ⟨i, hival, himem⟩ := exists_last_mem_arcSet s hl hlm
  have hi := mem_arcSet.mp (hsub himem)
  have hrel := val_sub_rel i s' s
  rw [hival] at hrel
  by_cases hwrap : l - 1 + (s - s').val < m
  · rw [Nat.mod_eq_of_lt hwrap] at hrel
    omega
  · exfalso
    push Not at hwrap
    have hcpos : 0 < (s - s').val := by omega
    have hne : s ≠ s' := by
      intro h
      rw [h, sub_self] at hcpos
      simp only [Fin.val_zero] at hcpos
      omega
    have hsum := val_sub_add_val_sub hne
    obtain ⟨j, hjval, -⟩ := exists_last_mem_arcSet s' (l := m) (by omega) le_rfl
    have hjrel := val_sub_rel j s s'
    rw [hjval, show m - 1 + (s' - s).val = m + ((s' - s).val - 1) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hjrel
    have hjin : j ∈ arcSet s l := mem_arcSet.mpr (by omega)
    have hjout := mem_arcSet.mp (hsub hjin)
    rw [hjval] at hjout
    omega

/-- If an arc starts inside another but is not contained in it, it
contains that other arc's last element. -/
theorem last_mem_arcSet_of_not_subset {m : ℕ} [NeZero m] {s r i : Fin m}
    {ls lr : ℕ} (hlast : (i - s).val = ls - 1) (hls : 1 ≤ ls)
    (hd : (r - s).val < ls) (hlsm : ls ≤ m)
    (hnsub : ¬ arcSet r lr ⊆ arcSet s ls) :
    i ∈ arcSet r lr := by
  rcases eq_or_ne r s with rfl | hne
  · -- same start: `¬ ⊆` forces `ls < lr`
    have hlr : ls < lr := by
      by_contra hcon
      push Not at hcon
      exact hnsub (arcSet_mono hcon)
    rw [mem_arcSet, hlast]
    omega
  · have hab := val_sub_add_val_sub hne
    have hrel := val_sub_rel i r s
    have hsr : (s - r).val = m - (r - s).val := by omega
    have hval : (i - r).val = ls - 1 - (r - s).val := by
      rw [hrel, hlast, hsr,
        show ls - 1 + (m - (r - s).val) = m + (ls - 1 - (r - s).val) by omega,
        Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [mem_arcSet, hval]
    by_contra hcon
    push Not at hcon
    exact hnsub (arcSet_subset (by omega) hlsm)

/-- If an arc contains another's start but they cross, it does **not**
contain that other arc's last element. -/
theorem last_notMem_arcSet_of_crossing {m : ℕ} [NeZero m] {s l i : Fin m}
    {ls ll : ℕ} (hlast : (i - s).val = ls - 1) (hls : 1 ≤ ls)
    (hllm : ll ≤ m) (hmem : (s - l).val < ll)
    (hc : Crossing (arcSet l ll) (arcSet s ls)) :
    i ∉ arcSet l ll := by
  intro hi
  have hls' : l ≠ s := by
    rintro rfl
    rcases le_total ll ls with h | h
    · obtain ⟨w, hw⟩ := hc.2.1
      rw [Finset.mem_sdiff] at hw
      exact hw.2 (arcSet_mono h hw.1)
    · obtain ⟨w, hw⟩ := hc.2.2.1
      rw [Finset.mem_sdiff] at hw
      exact hw.2 (arcSet_mono h hw.1)
  have hab := val_sub_add_val_sub hls'
  have hf0 : 0 < (s - l).val := by
    rcases Nat.eq_zero_or_pos (s - l).val with h0 | h0
    · exact absurd (sub_eq_zero.mp (Fin.val_injective (by simpa using h0))).symm
        hls'
    · exact h0
  have hrel : (i - l).val = ((i - s).val + (s - l).val) % m := val_sub_rel i l s
  rw [hlast] at hrel
  by_cases hwrap : ls - 1 + (s - l).val < m
  · -- no wrap: `arc S ⊆ arc L`, contradicting `arc S ∖ arc L ≠ ∅`
    rw [Nat.mod_eq_of_lt hwrap] at hrel
    have hlt : (i - l).val < ll := mem_arcSet.mp hi
    rw [hrel] at hlt
    obtain ⟨w, hw⟩ := hc.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_subset (by omega) hllm hw.1)
  · -- wrap: the two arcs cover everything, contradicting `∪ ≠ univ`
    push Not at hwrap
    refine hc.2.2.2 ?_
    ext j
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_arcSet]
    by_cases hj : (j - l).val < ll
    · exact Or.inl hj
    · refine Or.inr ?_
      push Not at hj
      -- `(j - s).val = (j - l).val - (s - l).val`, and `(j-l).val < m`
      have hrelj : (j - s).val = ((j - l).val + (l - s).val) % m :=
        val_sub_rel j s l
      have hls2 : (l - s).val = m - (s - l).val := by omega
      have hjm : (j - l).val < m := Fin.is_lt _
      have hge : (s - l).val ≤ (j - l).val := by omega
      have hval : (j - s).val = (j - l).val - (s - l).val := by
        rw [hrelj, hls2,
          show (j - l).val + (m - (s - l).val)
              = m + ((j - l).val - (s - l).val) by omega,
          Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hval]
      omega

/-- **The union of two overlapping arcs is an arc.**  If the second arc
starts inside the first and the two do not cover the cycle, their union
is the arc from the first start covering both.

This is the contiguity behind KKO22's "`O(L(p) ∪ L(q))` forms a
contiguous interval", which they infer from Fact 4.8 (the union is not
everything). -/
theorem arcSet_union_of_mem {m : ℕ} [NeZero m] {s s' : Fin m} {l l' : ℕ}
    (hmem : (s' - s).val < l)
    (hcov : arcSet s l ∪ arcSet s' l' ≠ Finset.univ) :
    arcSet s l ∪ arcSet s' l' = arcSet s (max l ((s' - s).val + l')) := by
  rcases eq_or_ne s s' with rfl | hne
  · ext j
    simp only [Finset.mem_union, mem_arcSet, sub_self, Fin.val_zero,
      Nat.zero_add]
    omega
  · have hsum := val_sub_add_val_sub hne
    have hkey : ∀ j : Fin m, (s' - s).val ≤ (j - s).val →
        (j - s').val = (j - s).val - (s' - s).val := by
      intro j hj
      have hjm : (j - s).val < m := Fin.is_lt _
      have hrel := val_sub_rel j s' s
      rw [show (j - s).val + (s - s').val
          = m + ((j - s).val - (s' - s).val) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hrel
      exact hrel
    have hkey2 : ∀ j : Fin m, (j - s).val < (s' - s).val →
        (j - s').val = (j - s).val + (s - s').val := by
      intro j hj
      have hjm : (j - s).val < m := Fin.is_lt _
      have hrel := val_sub_rel j s' s
      rw [Nat.mod_eq_of_lt (by omega)] at hrel
      exact hrel
    have hdm : (s' - s).val + l' ≤ m := by
      by_contra hcon
      push Not at hcon
      refine hcov ?_
      ext j
      simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_arcSet]
      by_cases hj : (j - s).val < l
      · exact Or.inl hj
      · have hge : (s' - s).val ≤ (j - s).val := by omega
        have hjm : (j - s).val < m := Fin.is_lt _
        refine Or.inr ?_
        rw [hkey j hge]
        omega
    ext j
    simp only [Finset.mem_union, mem_arcSet]
    have hjm : (j - s).val < m := Fin.is_lt _
    by_cases hge : (s' - s).val ≤ (j - s).val
    · rw [hkey j hge]
      omega
    · rw [hkey2 j (by omega)]
      omega

/-- Crossing arcs have distinct starts. -/
theorem start_ne_of_crossing_arcs {m : ℕ} {s s' : Fin m} {l l' : ℕ}
    (hc : Crossing (arcSet s l) (arcSet s' l')) : s ≠ s' := by
  rintro rfl
  rcases le_total l l' with h | h
  · obtain ⟨w, hw⟩ := hc.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_mono h hw.1)
  · obtain ⟨w, hw⟩ := hc.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_mono h hw.1)

/-- Arcs of the same positive, proper length determine their left
endpoint: if `arcSet s₁ l = arcSet s₂ l` with `1 ≤ l < m` then `s₁ = s₂`.
The distinguishing witness is `s₂ + l`, the first element beyond the
second arc. -/
theorem arcSet_left_injective {m : ℕ} [NeZero m] {s₁ s₂ : Fin m} {l : ℕ}
    (hl1 : 1 ≤ l) (hlm : l < m) (h : arcSet s₁ l = arcSet s₂ l) :
    s₁ = s₂ := by
  by_contra hne
  have hs₁ : s₁ ∈ arcSet s₂ l := by
    rw [← h, mem_arcSet, sub_self, Fin.val_zero]
    omega
  rw [mem_arcSet] at hs₁
  have hd1 : 1 ≤ (s₁ - s₂).val := by
    rcases Nat.eq_zero_or_pos (s₁ - s₂).val with h0 | h0
    · exact absurd (sub_eq_zero.mp (Fin.val_injective (by simpa using h0)))
        hne
    · exact h0
  have hj_notmem : s₂ + ⟨l, hlm⟩ ∉ arcSet s₂ l := by
    rw [mem_arcSet_compl, add_sub_cancel_left]
  have hj_mem : s₂ + ⟨l, hlm⟩ ∈ arcSet s₁ l := by
    rw [mem_arcSet]
    have he : s₂ + ⟨l, hlm⟩ - s₁ = (⟨l, hlm⟩ : Fin m) - (s₁ - s₂) := by
      abel
    have hΔ : (⟨l, hlm⟩ : Fin m).val = l := rfl
    rw [he, Fin.sub_val_of_le (Fin.le_def.mpr (by rw [hΔ]; exact hs₁.le)), hΔ]
    omega
  rw [h] at hj_mem
  exact hj_notmem hj_mem

theorem arcSet_card {m : ℕ} [NeZero m] (start : Fin m) {len : ℕ}
    (hlen : len ≤ m) : (arcSet start len).card = len := by
  conv_rhs => rw [← Finset.card_range len]
  refine Finset.card_bij (fun i _ => (i - start).val) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_range.mpr (mem_arcSet.mp hi)
  · intro i hi j hj hij
    have h1 : i - start = j - start := Fin.val_injective hij
    exact sub_left_inj.mp h1
  · intro k hk
    have hkm : k < m := lt_of_lt_of_le (Finset.mem_range.mp hk) hlen
    refine ⟨⟨k, hkm⟩ + start, ?_, ?_⟩
    · rw [mem_arcSet, add_sub_cancel_right]
      exact Finset.mem_range.mp hk
    · rw [add_sub_cancel_right]

/-! ### The symmetric closure of a family of cuts

BG08 work with *symmetric* families (`S ∈ F ↔ V ∖ S ∈ F`); this development's
families are rooted sides.  `symmetrize 𝒞` is the closure, and it is what the
inside/outside certificate below reads cycles in.  Atoms are unchanged by the
closure (`atoms_symmetrize`), and a member of the closure avoiding a vertex that
every member of `𝒞` avoids is itself in `𝒞` (`mem_of_mem_symmetrize_of_notMem`,
the rooted-side recovery). -/

/-- The symmetric closure of a family of cuts: each cut together with its
complement. -/
def symmetrize (𝒞 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  𝒞 ∪ 𝒞.image (·ᶜ)

theorem mem_symmetrize {𝒞 : Finset (Finset (Fin n))} {S : Finset (Fin n)} :
    S ∈ symmetrize 𝒞 ↔ S ∈ 𝒞 ∨ Sᶜ ∈ 𝒞 := by
  unfold symmetrize
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨T, hT, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rwa [compl_compl])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨Sᶜ, h, compl_compl S⟩

theorem subset_symmetrize (𝒞 : Finset (Finset (Fin n))) : 𝒞 ⊆ symmetrize 𝒞 :=
  Finset.subset_union_left

theorem mem_symmetrize_of_mem {𝒞 : Finset (Finset (Fin n))} {S : Finset (Fin n)} (h : S ∈ 𝒞) :
    S ∈ symmetrize 𝒞 := subset_symmetrize 𝒞 h

theorem compl_mem_symmetrize {𝒞 : Finset (Finset (Fin n))} {S : Finset (Fin n)}
    (h : S ∈ symmetrize 𝒞) : Sᶜ ∈ symmetrize 𝒞 := by
  rw [mem_symmetrize] at h ⊢
  rw [compl_compl]
  exact h.symm

/-- Complementing adds no separating power: the atoms of the closure are the atoms. -/
theorem atomOf_symmetrize (𝒞 : Finset (Finset (Fin n))) (u : Fin n) :
    atomOf (symmetrize 𝒞) u = atomOf 𝒞 u := by
  ext v
  simp only [mem_atomOf]
  constructor
  · intro h S hS
    exact h S (subset_symmetrize 𝒞 hS)
  · intro h S hS
    rcases mem_symmetrize.mp hS with hS | hS
    · exact h S hS
    · have := h Sᶜ hS
      rw [Finset.mem_compl, Finset.mem_compl] at this
      exact not_iff_not.mp this

theorem atoms_symmetrize (𝒞 : Finset (Finset (Fin n))) : atoms (symmetrize 𝒞) = atoms 𝒞 := by
  unfold atoms
  rw [funext (atomOf_symmetrize 𝒞)]

/-- **Rooted-side recovery**: a member of the closure avoiding a vertex that every
member of `𝒞` avoids is a member of `𝒞`. -/
theorem mem_of_mem_symmetrize_of_notMem {𝒞 : Finset (Finset (Fin n))} {r : Fin n}
    (hr : ∀ S ∈ 𝒞, r ∉ S) {S : Finset (Fin n)} (hS : S ∈ symmetrize 𝒞) (hrS : r ∉ S) :
    S ∈ 𝒞 := by
  rcases mem_symmetrize.mp hS with h | h
  · exact h
  · exact absurd (Finset.mem_compl.mpr hrS) (hr _ h)

/-! ### The polygon representation, interval form -/

/-- **A `k`-cycle of a family that avoids the atom `a`.**  BG08 Definition 4 and
KKO22 Lemma 4.20 characterize the *inside* atoms of a polygon as exactly those
avoided by some `k`-cycle of the *symmetric* family of the component's cuts;
`PolygonRep`'s `outside_iff_no_avoiding_kCycle` field records that
characterization, reading cycles in `symmetrize 𝒞`.  This is the raw-family
predicate: it says nothing about complements, and applying it to `𝒞` itself
(cycles of rooted sides only) is a genuinely different, weaker notion — see the
field's docstring. -/
def HasAvoidingKCycle (𝒞 : Finset (Finset (Fin n))) (a : Finset (Fin n)) : Prop :=
  ∃ (k : ℕ) (D : ℕ → Finset (Fin n)),
    IsKCycle k D ∧ (∀ i < k, D i ∈ 𝒞) ∧ ∀ i < k, Disjoint a (D i)

theorem HasAvoidingKCycle.mono {𝒞 𝒟 : Finset (Finset (Fin n))} (h : 𝒞 ⊆ 𝒟) {a : Finset (Fin n)}
    (ha : HasAvoidingKCycle 𝒞 a) : HasAvoidingKCycle 𝒟 a :=
  let ⟨k, D, hcyc, hmem, hav⟩ := ha
  ⟨k, D, hcyc, fun i hi => h (hmem i hi), hav⟩

/-- **The Benczúr–Goemans polygon representation** of a crossing component
(KKO22 §4.1, properties 1–4), in combinatorial interval form
(*prototype encoding*, see the module docstring).

`out` lists the outside atoms in (counterclockwise) cyclic order; each
cut `S ∈ 𝒞` is represented by the diagonal cutting off the arc
`arcSet (start S) (len S)` of outside atoms.  Reading `start S` and
`start S + len S` as polygon points recovers the diagonal picture. -/
structure PolygonRep (𝒞 : Finset (Finset (Fin n))) where
  /-- The number of outside atoms (= polygon points/sides). -/
  m : ℕ
  /-- Both sides of any representing diagonal span two or more polygon
  sides, so a nonsingleton component has at least four outside atoms. -/
  hm : 4 ≤ m
  /-- The outside atoms, in cyclic order. -/
  out : Fin m → Finset (Fin n)
  out_atom : ∀ i, out i ∈ atoms 𝒞
  out_injective : Function.Injective out
  /-- **BG08 Definition 4 = KKO22 Lemma 4.20**: an atom is outside — i.e. it
  is one of the `out i` — iff **no** `k`-cycle of the **symmetric closure**
  `symmetrize 𝒞 = 𝒞 ∪ {Sᶜ : S ∈ 𝒞}` avoids it.

  ⚠️ The closure is essential, not a convenience.  BG08 read cycles in the
  symmetric family, and quantifying over cycles of rooted sides only
  (`HasAvoidingKCycle 𝒞 a`) is a different, weaker certificate: orientation
  invariance is **false**.  Orient the five sides of a 5-cycle away from the
  root — the symmetric closure contains the original avoiding `IsKCycle 5`,
  while the rooted sides do not form a cycle, because some non-consecutive
  sides become nested; and this persists with no 3/4-cycle and no comb.
  (Decision of 2026-09-07; the rooted-side form was the field until then, and
  the rooted-side proposition is kept as the raw predicate.)

  ⚠️ This is the field that ties the encoding to BG08's *actual* polygon.
  Without it `out` is merely an injective list of some atoms, and the three
  results KKO22 prove *about BG08's polygon* — Lemma 4.23
  (`eq_of_outsideIn_eq`), Lemma 4.24/Fact 4.26 (`cross_arc_of_almostDiagonal`)
  and Lemma A.1 (`oneSide_no_inside_atoms`) — would be asserted over
  representations their proofs never cover: each proof contracts the atoms and
  argues that inside atoms *stay* inside because their avoiding cycle survives
  (KKO22 lines 1252-1255, 1276-1288, 2084-2089), which is exactly this
  characterization.  It is dischargeable by the only two producers of a
  `PolygonRep`, the boxes `polygonRep_exists` and `polygonRep_exists_oneSide`,
  because it is part of what BG08 construct. -/
  outside_iff_no_avoiding_kCycle : ∀ a ∈ atoms 𝒞,
    a ∈ Finset.univ.image out ↔ ¬ HasAvoidingKCycle (symmetrize 𝒞) a
  /-- **KKO22's `|C| > 1`.**  Lemma 4.23 and Lemma A.1 are stated for a
  component with more than one cut; both producing boxes already require it
  (`hns`), so it is carried here rather than threaded through every consumer. -/
  nontrivial : 2 ≤ 𝒞.card
  /-- Left polygon point of the representing diagonal of a cut. -/
  start : Finset (Fin n) → Fin m
  /-- Arc length of a cut: the number of outside atoms it contains. -/
  len : Finset (Fin n) → ℕ
  /-- Fact 4.2: every representing diagonal has at least two outside
  atoms on each side. -/
  two_le_len : ∀ S ∈ 𝒞, 2 ≤ len S
  len_le : ∀ S ∈ 𝒞, len S ≤ m - 2
  /-- Property 4, one direction: the outside atoms contained in a cut are
  exactly those of its arc. -/
  outside_eq_arc : ∀ S ∈ 𝒞, ∀ i : Fin m,
    (out i ⊆ S ↔ i ∈ arcSet (start S) (len S))
  /-- Property 4, the other direction: distinct cuts have distinct
  representing diagonals. -/
  arc_injective : ∀ S ∈ 𝒞, ∀ S' ∈ 𝒞,
    start S = start S' → len S = len S' → S = S'
  /-- Observation 4.4 ([BG08, Prop 19]): crossing cuts have crossing
  outside-atom arcs, and their arcs do not jointly cover the polygon. -/
  cross_arc : ∀ S ∈ 𝒞, ∀ S' ∈ 𝒞, Crossing S S' →
    Crossing (arcSet (start S) (len S)) (arcSet (start S') (len S'))
  /-- The **root atom** (KKO22 §4.2): the atom containing `u₀, v₀`, which
  lies in no cut of the component.  Cuts are thus proper subsets of
  `V ∖ rootAtom`, which is what makes unions of cuts automatically proper.

  KKO22 §4.2 are explicit that "the root `r` is not necessarily an outside
  atom", so this is an *atom*, not a polygon point.  Requiring it to be a
  polygon point is not a harmless simplification: see `TSPGap/Rooted.lean`,
  where an outside root is shown to be impossible once the component
  contains both sides of a cut.

  Nothing on the mainline path needs more than this.  `HasOutsideRoot`
  below records the stronger "the root is a polygon point" assumption, but
  only the auxiliary `no_outside_atom_diag` uses it. -/
  rootAtom : Finset (Fin n)
  rootAtom_mem : rootAtom ∈ atoms 𝒞
  rootAtom_disjoint : ∀ S ∈ 𝒞, Disjoint rootAtom S
  /-- **KKO22 Fact 4.8**: the arcs of two cuts never cover every polygon
  point.  KKO derive it from the root atom lying in neither cut ("then
  there must be a polygon point which is in neither of them") — a step
  that reads the polygon's cell structure, which the interval encoding
  does not carry.  With an outside root it would be immediate; in general
  it is part of what the representation provides. -/
  arcs_ne_univ : ∀ S ∈ 𝒞, ∀ S' ∈ 𝒞,
    arcSet (start S) (len S) ∪ arcSet (start S') (len S') ≠ Finset.univ

namespace PolygonRep

variable (P : PolygonRep 𝒞)

instance : NeZero P.m := ⟨by have := P.hm; omega⟩

/-- The inside atoms: atoms of the component that are not outside
atoms. -/
def insideAtoms : Finset (Finset (Fin n)) :=
  atoms 𝒞 \ (Finset.univ.image P.out)

/-- The outside atoms contained in a cut side `S`. -/
def outsideIn (S : Finset (Fin n)) : Finset (Fin P.m) :=
  Finset.univ.filter fun i => P.out i ⊆ S

theorem mem_outsideIn {S : Finset (Fin n)} {i : Fin P.m} :
    i ∈ P.outsideIn S ↔ P.out i ⊆ S := by
  rw [outsideIn, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩

theorem outsideIn_inter (S T : Finset (Fin n)) :
    P.outsideIn (S ∩ T) = P.outsideIn S ∩ P.outsideIn T := by
  ext i
  rw [Finset.mem_inter, mem_outsideIn, mem_outsideIn, mem_outsideIn,
    Finset.subset_inter_iff]

/-- An intersection of unions of atoms is a union of atoms. -/
theorem unionOfAtoms_inter {S T : Finset (Fin n)}
    (hS : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S)
    (hT : ∀ a ∈ atoms 𝒞, a ⊆ T ∨ Disjoint a T) :
    ∀ a ∈ atoms 𝒞, a ⊆ S ∩ T ∨ Disjoint a (S ∩ T) := by
  intro a ha
  rcases hS a ha with h1 | h1
  · rcases hT a ha with h2 | h2
    · exact Or.inl (Finset.subset_inter h1 h2)
    · exact Or.inr (h2.mono_right Finset.inter_subset_right)
  · exact Or.inr (h1.mono_right Finset.inter_subset_left)

theorem outsideIn_eq_arc (hS : S ∈ 𝒞) :
    P.outsideIn S = arcSet (P.start S) (P.len S) := by
  ext i
  rw [outsideIn, Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact (P.outside_eq_arc S hS i).mp h
  · intro h
    exact ⟨Finset.mem_univ i, (P.outside_eq_arc S hS i).mpr h⟩

theorem card_outsideIn (hS : S ∈ 𝒞) : (P.outsideIn S).card = P.len S := by
  rw [P.outsideIn_eq_arc hS]
  exact arcSet_card _ (le_trans (P.len_le S hS) (by omega))

/-- Outside atoms are nonempty. -/
theorem out_nonempty (i : Fin P.m) : (P.out i).Nonempty :=
  atoms_nonempty (P.out_atom i)

/-- The root atom is disjoint from every cut of the component. -/
theorem disjoint_root (hS : S ∈ 𝒞) : Disjoint P.rootAtom S :=
  P.rootAtom_disjoint S hS

/-- The root atom is nonempty. -/
theorem rootAtom_nonempty : P.rootAtom.Nonempty :=
  atoms_nonempty P.rootAtom_mem

include P in
/-- Unions of cuts of the component are proper: they all avoid the root
atom.  This is the formal content of KKO22's root convention, and it
supplies the "`∪ ≠ V`" clause of `Crossing` for free.

Note this needs only that the root is an *atom* in no cut — not that it is
an outside atom — so it survives the correction of KKO22 §4.2. -/
theorem union_ne_univ {S T : Finset (Fin n)} (hS : S ∈ 𝒞) (hT : T ∈ 𝒞) :
    S ∪ T ≠ Finset.univ := by
  obtain ⟨v, hv⟩ := P.rootAtom_nonempty
  intro hcov
  have hmem : v ∈ S ∪ T := by rw [hcov]; exact Finset.mem_univ v
  rcases Finset.mem_union.mp hmem with h | h
  · exact Finset.disjoint_left.mp (P.disjoint_root hS) hv h
  · exact Finset.disjoint_left.mp (P.disjoint_root hT) hv h

include P in
/-- ... and likewise for three cuts. -/
theorem union₃_ne_univ {S T U : Finset (Fin n)} (hS : S ∈ 𝒞) (hT : T ∈ 𝒞)
    (hU : U ∈ 𝒞) : S ∪ T ∪ U ≠ Finset.univ := by
  obtain ⟨v, hv⟩ := P.rootAtom_nonempty
  intro hcov
  have hmem : v ∈ S ∪ T ∪ U := by rw [hcov]; exact Finset.mem_univ v
  rcases Finset.mem_union.mp hmem with h | h
  · rcases Finset.mem_union.mp h with h' | h'
    · exact Finset.disjoint_left.mp (P.disjoint_root hS) hv h'
    · exact Finset.disjoint_left.mp (P.disjoint_root hT) hv h'
  · exact Finset.disjoint_left.mp (P.disjoint_root hU) hv h

/-- **KKO22's "the root is an outside atom" case.**  A polygon point lying
in no cut's arc.

KKO22 §4.2 note the root need not be an outside atom, so this is a genuine
extra assumption on a polygon, not a consequence of `PolygonRep`.  It is
what the diagonal-emptiness argument needs — that argument works by showing
the root has nowhere to sit along an arc, which requires it to *be* a
polygon point. -/
def HasOutsideRoot : Prop :=
  ∃ r : Fin P.m, ∀ S ∈ 𝒞, r ∉ arcSet (P.start S) (P.len S)

/-- **KKO22 Fact 4.2**: every cut of the component contains at least two
outside atoms. -/
theorem two_le_card_outsideIn (hS : S ∈ 𝒞) : 2 ≤ (P.outsideIn S).card := by
  rw [P.card_outsideIn hS]
  exact P.two_le_len S hS

/-- ... and at least two outside atoms lie outside it. -/
theorem two_le_card_outsideIn_compl (hS : S ∈ 𝒞) :
    2 ≤ (P.outsideIn S)ᶜ.card := by
  rw [Finset.card_compl, Fintype.card_fin, P.card_outsideIn hS]
  have h1 := P.len_le S hS
  have h2 := P.hm
  omega

/-- Distinct cuts of the component contain distinct sets of outside
atoms. -/
theorem outsideIn_injective (hS : S ∈ 𝒞) {S' : Finset (Fin n)}
    (hS' : S' ∈ 𝒞) (h : P.outsideIn S = P.outsideIn S') : S = S' := by
  have hm := P.hm
  have harc : arcSet (P.start S) (P.len S)
      = arcSet (P.start S') (P.len S') := by
    rw [← P.outsideIn_eq_arc hS, ← P.outsideIn_eq_arc hS', h]
  have hlen : P.len S = P.len S' := by
    have h1 := arcSet_card (P.start S) (m := P.m)
      (le_trans (P.len_le S hS) (by omega))
    have h2 := arcSet_card (P.start S') (m := P.m)
      (le_trans (P.len_le S' hS') (by omega))
    rw [← h1, ← h2, harc]
  rw [← hlen] at harc
  have hstart : P.start S = P.start S' :=
    arcSet_left_injective (by have := P.two_le_len S hS; omega)
      (by have := P.len_le S hS; omega) harc
  exact P.arc_injective S hS S' hS' hstart hlen

/-! ### Polygon points of a cut (KKO22 Definition 4.10) -/

/-- The polygon point immediately to the left of the leftmost outside atom
of `S`: the left endpoint of its representing diagonal. -/
def leftPoint (S : Finset (Fin n)) : Fin P.m := P.start S

/-- The polygon point immediately to the right of the rightmost outside
atom of `S`: the right endpoint of its representing diagonal. -/
def rightPoint (S : Finset (Fin n)) : Fin P.m :=
  P.start S + ⟨P.len S % P.m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne P.m))⟩

/-- A cut is determined by its right polygon point and its arc length. -/
theorem eq_of_rightPoint_eq_of_len_eq (hS : S ∈ 𝒞) {S' : Finset (Fin n)}
    (hS' : S' ∈ 𝒞) (hp : P.rightPoint S = P.rightPoint S')
    (hl : P.len S = P.len S') : S = S' := by
  refine P.arc_injective S hS S' hS' ?_ hl
  have hfin : (⟨P.len S % P.m,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne P.m))⟩ : Fin P.m)
      = ⟨P.len S' % P.m,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne P.m))⟩ :=
    Fin.ext (by rw [hl])
  have h := hp
  unfold rightPoint at h
  rw [hfin] at h
  exact add_right_cancel h

theorem val_rightPoint_sub_start (hS : S ∈ 𝒞) :
    (P.rightPoint S - P.start S).val = P.len S := by
  have h1 := P.len_le S hS
  have h2 := P.hm
  rw [rightPoint, add_sub_cancel_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- Two cuts with the same right polygon point have starts separated by
their length difference: their arcs share a right endpoint. -/
theorem val_start_sub_start_of_rightPoint_eq (hA : S ∈ 𝒞)
    {T : Finset (Fin n)} (hB : T ∈ 𝒞) (hpt : P.rightPoint S = P.rightPoint T)
    (hlen : P.len S ≤ P.len T) :
    (P.start S - P.start T).val = P.len T - P.len S := by
  have hm := P.hm
  have hmS := P.len_le S hA
  have hmT := P.len_le T hB
  have h3 : (P.rightPoint S - P.start T).val = P.len T := by
    rw [hpt]; exact P.val_rightPoint_sub_start hB
  have hsplit : P.rightPoint S - P.start T
      = (P.rightPoint S - P.start S) + (P.start S - P.start T) := by abel
  have hval := congrArg Fin.val hsplit
  rw [Fin.val_add, P.val_rightPoint_sub_start hA] at hval
  have hx : (P.start S - P.start T).val < P.m := Fin.is_lt _
  rw [h3] at hval
  rcases lt_or_ge (P.len S + (P.start S - P.start T).val) P.m with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hval
    omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-! ### Left and right crossing (KKO22 Definitions 4.12–4.13) -/

/-- **KKO22 Definition 4.12**: `S'` crosses `S` *on the left* — the
leftmost outside atom of `S ∪ S'` belongs to `S'`; in arc terms, the arc
of `S'` contains the start of the arc of `S`. -/
def CrossesOnLeft (S' S : Finset (Fin n)) : Prop :=
  Crossing S' S ∧ P.start S ∈ arcSet (P.start S') (P.len S')

/-- **KKO22 Definition 4.12**: `S'` crosses `S` *on the right* — in arc
terms, the arc of `S` contains the start of the arc of `S'`. -/
def CrossesOnRight (S' S : Finset (Fin n)) : Prop :=
  Crossing S' S ∧ P.start S' ∈ arcSet (P.start S) (P.len S)

/-- A crossing cut crosses on the left or on the right (the paper treats
this as obvious from the picture; here it is derived from
Observation 4.4). -/
theorem crossesOnLeft_or_crossesOnRight {S' : Finset (Fin n)} (hS' : S' ∈ 𝒞)
    (hS : S ∈ 𝒞) (hc : Crossing S' S) :
    P.CrossesOnLeft S' S ∨ P.CrossesOnRight S' S := by
  have harc := P.cross_arc S' hS' S hS hc
  have hne : P.start S' ≠ P.start S := start_ne_of_crossing_arcs harc
  rcases arc_mem_or_mem_of_inter hne harc.1 with h | h
  · exact Or.inl ⟨hc, mem_arcSet.mpr h⟩
  · exact Or.inr ⟨hc, mem_arcSet.mpr h⟩

/-- ... but never both: the sides of a crossing are mutually exclusive. -/
theorem not_crossesOnLeft_and_crossesOnRight {S' : Finset (Fin n)}
    (hS' : S' ∈ 𝒞) (hS : S ∈ 𝒞) :
    ¬ (P.CrossesOnLeft S' S ∧ P.CrossesOnRight S' S) := by
  rintro ⟨⟨hc, hleft⟩, ⟨-, hright⟩⟩
  have harc := P.cross_arc S' hS' S hS hc
  have hne : P.start S' ≠ P.start S := start_ne_of_crossing_arcs harc
  exact harc.2.2.2 (arcSet_union_eq_univ hne (mem_arcSet.mp hleft)
    (mem_arcSet.mp hright))

/-- **KKO22 Definition 4.13**: `S` is crossed on both sides (within the
component). -/
def CrossedOnBothSides (S : Finset (Fin n)) : Prop :=
  (∃ A ∈ 𝒞, P.CrossesOnLeft A S) ∧ (∃ A ∈ 𝒞, P.CrossesOnRight A S)

/-! ### `L(p)` and `R(p)` (KKO22 Definition 4.11)

We anchor at polygon points as in §5 (Figure 13): `L(p)` is the cut
crossed on both sides whose **right** polygon point is `p`, extending
farthest to the left (maximal arc length); `R(p)` symmetrically has left
polygon point `p` and extends farthest right.  (Definition 4.11 indexes
the same objects through the atoms adjacent to `p`; the two conventions
differ by an index shift, and we follow §5's.) -/

/-- `S` is `L(p)`: rightmost polygon point `p`, crossed on both sides,
of maximal arc length among such cuts. -/
def IsLp (p : Fin P.m) (S : Finset (Fin n)) : Prop :=
  S ∈ 𝒞 ∧ P.rightPoint S = p ∧ P.CrossedOnBothSides S ∧
    ∀ S' ∈ 𝒞, P.rightPoint S' = p → P.CrossedOnBothSides S' →
      P.len S' ≤ P.len S

/-- `S` is `R(p)`: leftmost polygon point `p`, crossed on both sides, of
maximal arc length among such cuts. -/
def IsRp (p : Fin P.m) (S : Finset (Fin n)) : Prop :=
  S ∈ 𝒞 ∧ P.leftPoint S = p ∧ P.CrossedOnBothSides S ∧
    ∀ S' ∈ 𝒞, P.leftPoint S' = p → P.CrossedOnBothSides S' →
      P.len S' ≤ P.len S

/-- `L(p)` exists as soon as some cut crossed on both sides has right
point `p`. -/
theorem exists_isLp {p : Fin P.m}
    (h : ∃ S ∈ 𝒞, P.rightPoint S = p ∧ P.CrossedOnBothSides S) :
    ∃ S, P.IsLp p S := by
  classical
  obtain ⟨S₀, hS₀, hp₀, hb₀⟩ := h
  obtain ⟨S, hSmem, hmax⟩ := Finset.exists_max_image
    (𝒞.filter fun S => P.rightPoint S = p ∧ P.CrossedOnBothSides S) P.len
    ⟨S₀, Finset.mem_filter.mpr ⟨hS₀, hp₀, hb₀⟩⟩
  obtain ⟨hS, hp, hb⟩ := Finset.mem_filter.mp hSmem
  exact ⟨S, hS, hp, hb, fun S' hS' hp' hb' =>
    hmax S' (Finset.mem_filter.mpr ⟨hS', hp', hb'⟩)⟩

/-- `R(p)` exists as soon as some cut crossed on both sides has left
point `p`. -/
theorem exists_isRp {p : Fin P.m}
    (h : ∃ S ∈ 𝒞, P.leftPoint S = p ∧ P.CrossedOnBothSides S) :
    ∃ S, P.IsRp p S := by
  classical
  obtain ⟨S₀, hS₀, hp₀, hb₀⟩ := h
  obtain ⟨S, hSmem, hmax⟩ := Finset.exists_max_image
    (𝒞.filter fun S => P.leftPoint S = p ∧ P.CrossedOnBothSides S) P.len
    ⟨S₀, Finset.mem_filter.mpr ⟨hS₀, hp₀, hb₀⟩⟩
  obtain ⟨hS, hp, hb⟩ := Finset.mem_filter.mp hSmem
  exact ⟨S, hS, hp, hb, fun S' hS' hp' hb' =>
    hmax S' (Finset.mem_filter.mpr ⟨hS', hp', hb'⟩)⟩

/-- `L(p)` is unique: its right point and (maximal) length pin down its
diagonal. -/
theorem IsLp.unique {p : Fin P.m} {S S' : Finset (Fin n)}
    (h1 : P.IsLp p S) (h2 : P.IsLp p S') : S = S' := by
  obtain ⟨hS, hp, hb, hmax⟩ := h1
  obtain ⟨hS', hp', hb', hmax'⟩ := h2
  have hlen : P.len S = P.len S' :=
    le_antisymm (hmax' S hS hp hb) (hmax S' hS' hp' hb')
  exact P.eq_of_rightPoint_eq_of_len_eq hS hS' (hp.trans hp'.symm) hlen

/-- `R(p)` is unique. -/
theorem IsRp.unique {p : Fin P.m} {S S' : Finset (Fin n)}
    (h1 : P.IsRp p S) (h2 : P.IsRp p S') : S = S' := by
  obtain ⟨hS, hp, hb, hmax⟩ := h1
  obtain ⟨hS', hp', hb', hmax'⟩ := h2
  have hlen : P.len S = P.len S' :=
    le_antisymm (hmax' S hS hp hb) (hmax S' hS' hp' hb')
  exact P.arc_injective S hS S' hS' (hp.trans hp'.symm) hlen

/-- A cut crossing `S` on the right reaches past `S`'s right polygon
point: that point lies in its arc.  (Otherwise its arc would end exactly
at `S`'s right end and so be contained in `S`'s arc, contradicting
crossing.) -/
theorem rightPoint_mem_arc_of_crossesOnRight (hS : S ∈ 𝒞)
    {R : Finset (Fin n)} (hR : R ∈ 𝒞) (hcr : P.CrossesOnRight R S) :
    P.rightPoint S ∈ arcSet (P.start R) (P.len R) := by
  have hm := P.hm
  have hlenS := P.len_le S hS
  have hd : (P.start R - P.start S).val < P.len S := mem_arcSet.mp hcr.2
  have hrp := P.val_rightPoint_sub_start hS
  have hval : (P.rightPoint S - P.start R).val
      = P.len S - (P.start R - P.start S).val := by
    have := val_sub_of_le (s := P.start S) (α := P.start R)
      (β := P.rightPoint S) (by omega)
    omega
  rw [mem_arcSet, hval]
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw⟩ := (P.cross_arc R hR S hS hcr.1).2.1
  rw [Finset.mem_sdiff] at hw
  exact hw.2 (arcSet_subset (by omega) (by omega) hw.1)

/-- The right polygon point of a cut is outside its own arc. -/
theorem rightPoint_notMem_arc (hS : S ∈ 𝒞) :
    P.rightPoint S ∉ arcSet (P.start S) (P.len S) := by
  have hm := P.hm
  have hlenS := P.len_le S hS
  rw [mem_arcSet_compl, P.val_rightPoint_sub_start hS]

/-! ### Left-to-right order within an arc, and the "rightmost point" WLOG

KKO's proofs repeatedly say "WLOG assume `q` is the rightmost point of
the interval".  That is an ordering of polygon points *relative to the
arc they lie in*: measured from the arc's start, further right means
larger offset.  `LeFrom s` is that order — a total order for each base
point `s` — and `rightmost_wlog` is the corresponding symmetry
reduction. -/

/-- `i` is weakly left of `j` as seen from the base point `s`. -/
def LeFrom (s i j : Fin P.m) : Prop := (i - s).val ≤ (j - s).val

theorem leFrom_total (s i j : Fin P.m) : P.LeFrom s i j ∨ P.LeFrom s j i :=
  le_total _ _

theorem leFrom_trans {s i j k : Fin P.m} (h₁ : P.LeFrom s i j)
    (h₂ : P.LeFrom s j k) : P.LeFrom s i k := le_trans h₁ h₂

theorem leFrom_antisymm {s i j : Fin P.m} (h₁ : P.LeFrom s i j)
    (h₂ : P.LeFrom s j i) : i = j :=
  sub_left_inj.mp (Fin.val_injective (le_antisymm h₁ h₂))

include P in
/-- **The "rightmost point" WLOG.**  A symmetric goal about two polygon
points may be proved assuming the first is weakly left of the second. -/
theorem rightmost_wlog (s : Fin P.m) {motive : Fin P.m → Fin P.m → Prop}
    (hsymm : ∀ i j, motive j i → motive i j)
    (hcase : ∀ i j, P.LeFrom s i j → motive i j) :
    ∀ i j, motive i j := by
  intro i j
  rcases P.leFrom_total s i j with h | h
  · exact hcase i j h
  · exact hsymm i j (hcase j i h)

include P in
/-- A nonempty set of polygon points has a rightmost element as seen from
any base point — KKO's "the rightmost point in this interval". -/
theorem exists_rightmost (s : Fin P.m) {t : Finset (Fin P.m)}
    (ht : t.Nonempty) : ∃ j ∈ t, ∀ i ∈ t, P.LeFrom s i j := by
  classical
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image t (fun i => (i - s).val) ht
  exact ⟨j, hj, fun i hi => hmax i hi⟩

/-! ### Almost diagonal cuts (KKO22 Definition 4.25)

The §5 constructions speak of sets like `L ∩ L_R`, which are *not* cuts
of the component and so carry no arc in the basic encoding.  Definition
4.25 names the right class: a `2η`-near minimum cut which is a union of
atoms and whose outside atoms form a contiguous arc.  Every cut of `𝒞`
is one, and so is every pairwise intersection or difference of cuts.

Contiguity is recorded as an existential over arc data (`IsArcOf`).  That
data is unique when the arc is proper — `arcSet_card` pins the length and
`arcSet_left_injective` the start — so the "arc of an almost diagonal
cut" is well defined without choosing it (`IsArcOf.unique`), and downstream
lemmas can simply take `s`, `l` as parameters. -/

/-- `S`'s outside atoms form the arc `[s, s + l)`, with `l` proper. -/
def IsArcOf (S : Finset (Fin n)) (s : Fin P.m) (l : ℕ) : Prop :=
  P.outsideIn S = arcSet s l ∧ 1 ≤ l ∧ l < P.m

/-- The arc of a set is unique. -/
theorem IsArcOf.unique {S : Finset (Fin n)} {s s' : Fin P.m} {l l' : ℕ}
    (h : P.IsArcOf S s l) (h' : P.IsArcOf S s' l') : s = s' ∧ l = l' := by
  obtain ⟨he, hl1, hl2⟩ := h
  obtain ⟨he', hl1', hl2'⟩ := h'
  have harc : arcSet s l = arcSet s' l' := by rw [← he, he']
  have hlen : l = l' := by
    have c1 := arcSet_card s (le_of_lt hl2)
    have c2 := arcSet_card s' (le_of_lt hl2')
    rw [← c1, ← c2, harc]
  refine ⟨?_, hlen⟩
  rw [hlen] at harc
  exact arcSet_left_injective hl1' (by omega) harc

/-- **KKO22 Definition 4.25**: an almost diagonal cut — a `2η`-near
minimum cut which is a union of atoms of the component, avoids the root
atom, and whose outside atoms form a nonempty proper contiguous arc.

`root_disjoint` is KKO's `S ⊆ A(𝒞) ∖ {r}`.  It is what makes unions of
almost diagonal cuts proper, and hence what lets Lemma 4.27 be stated at
the paper's generality — with an almost diagonal central cut rather than a
member of `𝒞`.  Without it the `∪ ≠ V` clause of `Crossing` would have to
be bought back from the polygon's root, which is exactly the dependence
that forced an outside root on Corollary 5.8. -/
structure IsAlmostDiagonal (x : Sym2 (Fin n) → ℝ) (η : ℝ)
    (S : Finset (Fin n)) : Prop where
  nearMin : IsNearMinCut x (2 * η) S
  unionOfAtoms : ∀ a ∈ atoms 𝒞, a ⊆ S ∨ Disjoint a S
  contiguous : ∃ (s : Fin P.m) (l : ℕ), P.IsArcOf S s l
  root_disjoint : Disjoint P.rootAtom S

/-- Every cut of the component is an almost diagonal cut, with its own
arc (KKO22's "any cut in `𝒞` is an almost diagonal cut"). -/
theorem isArcOf_of_mem (hS : S ∈ 𝒞) : P.IsArcOf S (P.start S) (P.len S) := by
  have hm := P.hm
  have h2 := P.two_le_len S hS
  have hle := P.len_le S hS
  exact ⟨P.outsideIn_eq_arc hS, by omega, by omega⟩

theorem isAlmostDiagonal_of_mem {x : Sym2 (Fin n) → ℝ} {η : ℝ} (hη0 : 0 ≤ η)
    (hnm : ∀ T ∈ 𝒞, IsNearMinCut x η T) (hS : S ∈ 𝒞) :
    P.IsAlmostDiagonal x η S :=
  { nearMin := (hnm S hS).mono (by linarith)
    unionOfAtoms := fun a ha => atom_subset_or_disjoint ha hS
    contiguous := ⟨P.start S, P.len S, P.isArcOf_of_mem hS⟩
    root_disjoint := P.rootAtom_disjoint S hS }

/-! ### Crossing an almost diagonal cut, and `L*(p)`

Definition 4.12 reads a crossing side off the crossed set's *arc*, so it
extends verbatim to almost diagonal cuts once their arc data is supplied
(Definition 4.25).  These are the same propositions as `CrossesOnLeft` /
`CrossesOnRight` when the crossed set is a member of `𝒞` carrying its own
arc — definitionally so (`crossesOnLeftArc_of_mem`).

With them, `L*(p)` from §5 — the cut crossing `L(p)^∩R` on the left with
*maximal* shared outside atoms — becomes definable. -/

/-- `W` crosses the almost diagonal cut `T` (arc starting at `s`) on the
left: `T`'s arc starts inside `W`'s. -/
def CrossesOnLeftArc (W T : Finset (Fin n)) (s : Fin P.m) : Prop :=
  Crossing W T ∧ s ∈ arcSet (P.start W) (P.len W)

/-- `W` crosses the almost diagonal cut `T` with arc `[s, s+l)` on the
right: `W`'s arc starts inside `T`'s. -/
def CrossesOnRightArc (W T : Finset (Fin n)) (s : Fin P.m) (l : ℕ) : Prop :=
  Crossing W T ∧ P.start W ∈ arcSet s l

theorem crossesOnLeftArc_of_mem {W : Finset (Fin n)} :
    P.CrossesOnLeftArc W S (P.start S) ↔ P.CrossesOnLeft W S := Iff.rfl

theorem crossesOnRightArc_of_mem {W : Finset (Fin n)} :
    P.CrossesOnRightArc W S (P.start S) (P.len S) ↔ P.CrossesOnRight W S :=
  Iff.rfl

/-- **`L*(p)`** (KKO22 §5, the display defining `E(B→(p))`): among the
cuts crossing the almost diagonal cut `T` on the left, one maximizing the
shared outside atoms.  (KKO set `L*(p) = ∅` when no such cut exists; here
existence is a hypothesis of the lemmas that use it.) -/
def IsLStar (T : Finset (Fin n)) (s : Fin P.m) (W : Finset (Fin n)) : Prop :=
  W ∈ 𝒞 ∧ P.CrossesOnLeftArc W T s ∧
    ∀ W' ∈ 𝒞, P.CrossesOnLeftArc W' T s →
      (P.outsideIn T ∩ P.outsideIn W').card
        ≤ (P.outsideIn T ∩ P.outsideIn W).card

theorem exists_isLStar {T : Finset (Fin n)} {s : Fin P.m}
    (h : ∃ W ∈ 𝒞, P.CrossesOnLeftArc W T s) : ∃ W, P.IsLStar T s W := by
  classical
  obtain ⟨W₀, hW₀, hc₀⟩ := h
  obtain ⟨W, hWmem, hmax⟩ := Finset.exists_max_image
    (𝒞.filter fun W => P.CrossesOnLeftArc W T s)
    (fun W => (P.outsideIn T ∩ P.outsideIn W).card)
    ⟨W₀, Finset.mem_filter.mpr ⟨hW₀, hc₀⟩⟩
  obtain ⟨hW, hc⟩ := Finset.mem_filter.mp hWmem
  exact ⟨W, hW, hc, fun W' hW' hc' =>
    hmax W' (Finset.mem_filter.mpr ⟨hW', hc'⟩)⟩

/-- **`R*(p)`** (KKO22 §5, the display defining `E(B←(p))`): among the cuts
crossing the almost diagonal cut `T` (arc `[s, s+l)`) on the right, one
maximizing the shared outside atoms — the mirror of `IsLStar`.  The right
side of the crossing reads `T`'s arc *length* as well as its start, so `l`
is a parameter here where `IsLStar` needed only `s`. -/
def IsRStar (T : Finset (Fin n)) (s : Fin P.m) (l : ℕ)
    (W : Finset (Fin n)) : Prop :=
  W ∈ 𝒞 ∧ P.CrossesOnRightArc W T s l ∧
    ∀ W' ∈ 𝒞, P.CrossesOnRightArc W' T s l →
      (P.outsideIn T ∩ P.outsideIn W').card
        ≤ (P.outsideIn T ∩ P.outsideIn W).card

theorem exists_isRStar {T : Finset (Fin n)} {s : Fin P.m} {l : ℕ}
    (h : ∃ W ∈ 𝒞, P.CrossesOnRightArc W T s l) : ∃ W, P.IsRStar T s l W := by
  classical
  obtain ⟨W₀, hW₀, hc₀⟩ := h
  obtain ⟨W, hWmem, hmax⟩ := Finset.exists_max_image
    (𝒞.filter fun W => P.CrossesOnRightArc W T s l)
    (fun W => (P.outsideIn T ∩ P.outsideIn W).card)
    ⟨W₀, Finset.mem_filter.mpr ⟨hW₀, hc₀⟩⟩
  obtain ⟨hW, hc⟩ := Finset.mem_filter.mp hWmem
  exact ⟨W, hW, hc, fun W' hW' hc' =>
    hmax W' (Finset.mem_filter.mpr ⟨hW', hc'⟩)⟩

/-! ### The total star choice

KKO set `L*(p) = ∅` when no cut crosses `L(p)^∩R` on the left, and likewise
for `R*`.  `IsLStar`/`IsRStar` capture only the maximizer case, so a
bad-event datum carrying them would be conditional on candidates existing.
The `Chosen` forms are total: a maximizer if one exists, `∅` otherwise —
with an unconditional witness, which is what the bad-event index needs. -/

/-- **`L*(p)`, total**: a maximizer among the left-crossers of `T` when any
exists, and `∅` — with no candidate at all — otherwise. -/
def IsChosenLStar (T : Finset (Fin n)) (s : Fin P.m)
    (W : Finset (Fin n)) : Prop :=
  P.IsLStar T s W ∨ (W = ∅ ∧ ∀ W' ∈ 𝒞, ¬ P.CrossesOnLeftArc W' T s)

theorem exists_isChosenLStar (T : Finset (Fin n)) (s : Fin P.m) :
    ∃ W, P.IsChosenLStar T s W := by
  classical
  by_cases h : ∃ W' ∈ 𝒞, P.CrossesOnLeftArc W' T s
  · obtain ⟨W, hW⟩ := P.exists_isLStar h
    exact ⟨W, Or.inl hW⟩
  · push Not at h
    exact ⟨∅, Or.inr ⟨rfl, h⟩⟩

/-- **`R*(p)`, total** — the mirror. -/
def IsChosenRStar (T : Finset (Fin n)) (s : Fin P.m) (l : ℕ)
    (W : Finset (Fin n)) : Prop :=
  P.IsRStar T s l W ∨ (W = ∅ ∧ ∀ W' ∈ 𝒞, ¬ P.CrossesOnRightArc W' T s l)

theorem exists_isChosenRStar (T : Finset (Fin n)) (s : Fin P.m) (l : ℕ) :
    ∃ W, P.IsChosenRStar T s l W := by
  classical
  by_cases h : ∃ W' ∈ 𝒞, P.CrossesOnRightArc W' T s l
  · obtain ⟨W, hW⟩ := P.exists_isRStar h
    exact ⟨W, Or.inl hW⟩
  · push Not at h
    exact ⟨∅, Or.inr ⟨rfl, h⟩⟩

/-! ### `S_L` and `S_R` (KKO22 Definition 4.17) -/

/-- The outside atoms shared with a right-crossing cut form the arc from
that cut's start to the right end of `S`. -/
theorem outsideIn_inter_right_eq_arc (hS : S ∈ 𝒞) {R : Finset (Fin n)}
    (hR : R ∈ 𝒞) (hcr : P.CrossesOnRight R S) :
    P.outsideIn S ∩ P.outsideIn R
      = arcSet (P.start R) (P.len S - (P.start R - P.start S).val) := by
  obtain ⟨hc, hmem⟩ := hcr
  have harc := P.cross_arc R hR S hS hc
  have hne : P.start R ≠ P.start S := start_ne_of_crossing_arcs harc
  have hsL : P.start S ∉ arcSet (P.start R) (P.len R) := fun hmem' =>
    P.not_crossesOnLeft_and_crossesOnRight hR hS ⟨⟨hc, hmem'⟩, hc, hmem⟩
  have hd := mem_arcSet.mp hmem
  have hb := mem_arcSet_compl.mp hsL
  have hml := P.len_le S hS
  have hm := P.hm
  rw [P.outsideIn_eq_arc hS, P.outsideIn_eq_arc hR,
    arcSet_inter_of_mem_of_notMem hne.symm hd hb]
  have hle : P.len S - (P.start R - P.start S).val ≤ P.len R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := harc.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_subset (by omega) (by omega) hw.1)
  rw [min_eq_right hle]

theorem card_outsideIn_inter_right (hS : S ∈ 𝒞) {R : Finset (Fin n)}
    (hR : R ∈ 𝒞) (hcr : P.CrossesOnRight R S) :
    (P.outsideIn S ∩ P.outsideIn R).card
      = P.len S - (P.start R - P.start S).val := by
  have hml := P.len_le S hS
  have hm := P.hm
  rw [P.outsideIn_inter_right_eq_arc hS hR hcr]
  exact arcSet_card _ (by omega)

/-- Mirror image: the outside atoms shared with a left-crossing cut form
the arc from `start S` to the right end of `L`.  These arcs all *begin*
at `start S`, so they are nested by length — the left-hand counterpart of
`outsideIn_inter_right_eq_arc`, whose arcs all *end* at `S`'s right end. -/
theorem outsideIn_inter_left_eq_arc (hS : S ∈ 𝒞) {L : Finset (Fin n)}
    (hL : L ∈ 𝒞) (hcl : P.CrossesOnLeft L S) :
    P.outsideIn S ∩ P.outsideIn L
      = arcSet (P.start S) (P.len L - (P.start S - P.start L).val) := by
  obtain ⟨hc, hmem⟩ := hcl
  have harc := P.cross_arc L hL S hS hc
  have hne : P.start L ≠ P.start S := start_ne_of_crossing_arcs harc
  have hsR : P.start L ∉ arcSet (P.start S) (P.len S) := fun hmem' =>
    P.not_crossesOnLeft_and_crossesOnRight hL hS ⟨⟨hc, hmem⟩, hc, hmem'⟩
  have hd := mem_arcSet.mp hmem
  have hb := mem_arcSet_compl.mp hsR
  have hmlS := P.len_le S hS
  have hmlL := P.len_le L hL
  have hm := P.hm
  rw [Finset.inter_comm, P.outsideIn_eq_arc hL, P.outsideIn_eq_arc hS,
    arcSet_inter_of_mem_of_notMem hne hd hb]
  have hle : P.len L - (P.start S - P.start L).val ≤ P.len S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := harc.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_subset (by omega) (by omega) hw.1)
  rw [min_eq_right hle]

theorem card_outsideIn_inter_left (hS : S ∈ 𝒞) {L : Finset (Fin n)}
    (hL : L ∈ 𝒞) (hcl : P.CrossesOnLeft L S) :
    (P.outsideIn S ∩ P.outsideIn L).card
      = P.len L - (P.start S - P.start L).val := by
  obtain ⟨hc, hmem⟩ := hcl
  have harc := P.cross_arc L hL S hS hc
  have hne : P.start L ≠ P.start S := start_ne_of_crossing_arcs harc
  have hsR : P.start L ∉ arcSet (P.start S) (P.len S) := fun hmem' =>
    P.not_crossesOnLeft_and_crossesOnRight hL hS ⟨⟨hc, hmem⟩, hc, hmem'⟩
  have hd := mem_arcSet.mp hmem
  have hb := mem_arcSet_compl.mp hsR
  have hmlS := P.len_le S hS
  have hmlL := P.len_le L hL
  have hm := P.hm
  rw [Finset.inter_comm, P.outsideIn_eq_arc hL, P.outsideIn_eq_arc hS,
    arcSet_inter_of_mem_of_notMem hne hd hb]
  have hle : P.len L - (P.start S - P.start L).val ≤ P.len S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := harc.2.2.1
    rw [Finset.mem_sdiff] at hw
    exact hw.2 (arcSet_subset (by omega) (by omega) hw.1)
  rw [min_eq_right hle]
  exact arcSet_card _ (by omega)

/-- **KKO22 Definition 4.17**: `R` is `S_R` — a cut crossing `S` on the
right minimizing the number of shared outside atoms `|O(S ∩ S_R)|`, with
ties broken by smallest arc length. -/
def IsSR (S R : Finset (Fin n)) : Prop :=
  R ∈ 𝒞 ∧ P.CrossesOnRight R S ∧
    (∀ R' ∈ 𝒞, P.CrossesOnRight R' S →
      (P.outsideIn S ∩ P.outsideIn R).card
        ≤ (P.outsideIn S ∩ P.outsideIn R').card) ∧
    ∀ R' ∈ 𝒞, P.CrossesOnRight R' S →
      (P.outsideIn S ∩ P.outsideIn R').card
        = (P.outsideIn S ∩ P.outsideIn R).card →
      P.len R ≤ P.len R'

/-- **KKO22 Definition 4.17**: `L` is `S_L`, symmetrically. -/
def IsSL (S L : Finset (Fin n)) : Prop :=
  L ∈ 𝒞 ∧ P.CrossesOnLeft L S ∧
    (∀ L' ∈ 𝒞, P.CrossesOnLeft L' S →
      (P.outsideIn S ∩ P.outsideIn L).card
        ≤ (P.outsideIn S ∩ P.outsideIn L').card) ∧
    ∀ L' ∈ 𝒞, P.CrossesOnLeft L' S →
      (P.outsideIn S ∩ P.outsideIn L').card
        = (P.outsideIn S ∩ P.outsideIn L).card →
      P.len L ≤ P.len L'

theorem exists_isSR (h : ∃ R ∈ 𝒞, P.CrossesOnRight R S) :
    ∃ R, P.IsSR S R := by
  classical
  obtain ⟨R₀, hR₀, hc₀⟩ := h
  obtain ⟨R₁, hR₁mem, hmin₁⟩ := Finset.exists_min_image
    (𝒞.filter fun R => P.CrossesOnRight R S)
    (fun R => (P.outsideIn S ∩ P.outsideIn R).card)
    ⟨R₀, Finset.mem_filter.mpr ⟨hR₀, hc₀⟩⟩
  obtain ⟨R, hRmem, hmin₂⟩ := Finset.exists_min_image
    ((𝒞.filter fun R => P.CrossesOnRight R S).filter
      fun R => (P.outsideIn S ∩ P.outsideIn R).card
        = (P.outsideIn S ∩ P.outsideIn R₁).card)
    P.len ⟨R₁, Finset.mem_filter.mpr ⟨hR₁mem, rfl⟩⟩
  obtain ⟨hRmem', hRcard⟩ := Finset.mem_filter.mp hRmem
  obtain ⟨hR, hc⟩ := Finset.mem_filter.mp hRmem'
  refine ⟨R, hR, hc, ?_, ?_⟩
  · intro R' hR' hc'
    rw [hRcard]
    exact hmin₁ R' (Finset.mem_filter.mpr ⟨hR', hc'⟩)
  · intro R' hR' hc' hcard'
    refine hmin₂ R' (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hR', hc'⟩, ?_⟩)
    rw [hcard', hRcard]

theorem exists_isSL (h : ∃ L ∈ 𝒞, P.CrossesOnLeft L S) :
    ∃ L, P.IsSL S L := by
  classical
  obtain ⟨L₀, hL₀, hc₀⟩ := h
  obtain ⟨L₁, hL₁mem, hmin₁⟩ := Finset.exists_min_image
    (𝒞.filter fun L => P.CrossesOnLeft L S)
    (fun L => (P.outsideIn S ∩ P.outsideIn L).card)
    ⟨L₀, Finset.mem_filter.mpr ⟨hL₀, hc₀⟩⟩
  obtain ⟨L, hLmem, hmin₂⟩ := Finset.exists_min_image
    ((𝒞.filter fun L => P.CrossesOnLeft L S).filter
      fun L => (P.outsideIn S ∩ P.outsideIn L).card
        = (P.outsideIn S ∩ P.outsideIn L₁).card)
    P.len ⟨L₁, Finset.mem_filter.mpr ⟨hL₁mem, rfl⟩⟩
  obtain ⟨hLmem', hLcard⟩ := Finset.mem_filter.mp hLmem
  obtain ⟨hL, hc⟩ := Finset.mem_filter.mp hLmem'
  refine ⟨L, hL, hc, ?_, ?_⟩
  · intro L' hL' hc'
    rw [hLcard]
    exact hmin₁ L' (Finset.mem_filter.mpr ⟨hL', hc'⟩)
  · intro L' hL' hc' hcard'
    refine hmin₂ L' (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hL', hc'⟩, ?_⟩)
    rw [hcard', hLcard]

/-- `S_R` is unique: the minimal overlap count pins down its start (the
overlap is `len S - (start R - start S)`), and the length tie-break pins
down its diagonal. -/
theorem IsSR.unique (hS : S ∈ 𝒞) {R R' : Finset (Fin n)}
    (h1 : P.IsSR S R) (h2 : P.IsSR S R') : R = R' := by
  obtain ⟨hR, hc, hmin, htie⟩ := h1
  obtain ⟨hR', hc', hmin', htie'⟩ := h2
  have hcard : (P.outsideIn S ∩ P.outsideIn R).card
      = (P.outsideIn S ∩ P.outsideIn R').card :=
    le_antisymm (hmin R' hR' hc') (hmin' R hR hc)
  have hlen : P.len R = P.len R' :=
    le_antisymm (htie R' hR' hc' hcard.symm) (htie' R hR hc hcard)
  have e1 := P.card_outsideIn_inter_right hS hR hc
  have e2 := P.card_outsideIn_inter_right hS hR' hc'
  have hd1 := mem_arcSet.mp hc.2
  have hd2 := mem_arcSet.mp hc'.2
  have hstart : P.start R = P.start R' := by
    have hv : (P.start R - P.start S).val
        = (P.start R' - P.start S).val := by omega
    exact sub_left_inj.mp (Fin.val_injective hv)
  exact P.arc_injective R hR R' hR' hstart hlen

/-! ### The edge trichotomy `E←`, `E→`, `E∘` (KKO22 §3, Eq. (4))

For `S` crossed on both sides with `S_L`, `S_R` as in Definition 4.17:

* `E←(S) = E(S ∩ S_L, S_L ∖ S)` — the edges of `δ(S)` "hidden behind"
  the left crossing cut;
* `E→(S) = E(S ∩ S_R, S_R ∖ S)` — symmetrically on the right;
* `E∘(S) = δ(S) ∖ E←(S) ∖ E→(S)` — the rest.

These are pairwise disjoint subsets of `δ(S)` (`arrowLeft_subset_cut`,
`disjoint_arrowLeft_arrowRight`), so the `x`-masses split
(`cutSum_eq_arrow_sum`); combined with the uncrossing bounds this is what
makes `x(E∘(S))` small (`sum_arrowCirc_le`: at most `2η`, the paper's
`x(E∘(S)) ≤ 2 + η - x(E←) - x(E→) ≤ 2η`).  The bad events of §3/§5 are
defined on these sets.

The disjointness `L ∖ S` vs `R ∖ S` is taken as a hypothesis here: it
holds because `S_L`, `S_R` cross `S` from opposite sides, but deriving it
needs control of inside atoms (KKO22 Lemma 4.15/4.27, §4.3–4.4), which is
the next block of work. -/

/-- `E←(S) = E(S ∩ L, L ∖ S)` for `L = S_L`. -/
def arrowLeft (S L : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  betweenEdges (S ∩ L) (L \ S)

/-- `E→(S) = E(S ∩ R, R ∖ S)` for `R = S_R`. -/
def arrowRight (S R : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  betweenEdges (S ∩ R) (R \ S)

/-- `E∘(S) = δ(S) ∖ E←(S) ∖ E→(S)`. -/
def arrowCirc (S L R : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (cutEdges S \ arrowLeft S L) \ arrowRight S R

theorem arrowLeft_subset_cut (S L : Finset (Fin n)) :
    arrowLeft S L ⊆ cutEdges S := by
  intro e he
  rw [arrowLeft, betweenEdges, Finset.mem_filter] at he
  obtain ⟨-, u, hu, v, hv, rfl⟩ := he
  rw [Finset.mem_inter] at hu
  rw [Finset.mem_sdiff] at hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    u, hu.1, v, Finset.mem_compl.mpr hv.2, rfl⟩

theorem arrowRight_subset_cut (S R : Finset (Fin n)) :
    arrowRight S R ⊆ cutEdges S :=
  arrowLeft_subset_cut S R

/-- `E←` and `E→` are disjoint when `S_L` and `S_R` cross `S` on opposite
sides: an edge of `E←(S)` has its outside endpoint in `L ∖ S`, an edge of
`E→(S)` in `R ∖ S`, and these are disjoint since `L ∖ S` and `R ∖ S` are
(the crossing sides are exclusive). -/
theorem disjoint_arrowLeft_arrowRight {S L R : Finset (Fin n)}
    (h : Disjoint (L \ S) (R \ S)) :
    Disjoint (arrowLeft S L) (arrowRight S R) := by
  rw [Finset.disjoint_left]
  intro e heL heR
  rw [arrowLeft, betweenEdges, Finset.mem_filter] at heL
  rw [arrowRight, betweenEdges, Finset.mem_filter] at heR
  obtain ⟨-, u, hu, v, hv, huv⟩ := heL
  obtain ⟨-, u', hu', v', hv', huv'⟩ := heR
  have huS : u ∈ S := (Finset.mem_inter.mp hu).1
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hv'S : v' ∉ S := (Finset.mem_sdiff.mp hv').2
  have heq : s(u, v) = s(u', v') := huv ▸ huv'
  rcases Sym2.eq_iff.mp heq with ⟨-, hvv⟩ | ⟨huv2, -⟩
  · exact Finset.disjoint_left.mp h hv (hvv ▸ hv')
  · exact hv'S (huv2 ▸ huS)

/-- The `x`-mass of the cut splits along the trichotomy. -/
theorem cutSum_eq_arrow_sum (x : Sym2 (Fin n) → ℝ) {S L R : Finset (Fin n)}
    (hd : Disjoint (L \ S) (R \ S)) :
    cutSum x S = (∑ e ∈ arrowLeft S L, x e) + (∑ e ∈ arrowRight S R, x e)
      + ∑ e ∈ arrowCirc S L R, x e := by
  classical
  have hLR := disjoint_arrowLeft_arrowRight (S := S) hd
  have hsub : arrowLeft S L ∪ arrowRight S R ⊆ cutEdges S :=
    Finset.union_subset (arrowLeft_subset_cut S L) (arrowRight_subset_cut S R)
  have h1 : ∑ e ∈ arrowLeft S L ∪ arrowRight S R, x e
      = (∑ e ∈ arrowLeft S L, x e) + ∑ e ∈ arrowRight S R, x e :=
    Finset.sum_union hLR
  have h2 : arrowCirc S L R = cutEdges S \ (arrowLeft S L ∪ arrowRight S R) := by
    rw [arrowCirc, sdiff_sdiff_left]
    rfl
  rw [h2, cutSum, ← Finset.sum_sdiff hsub, h1]
  ring

/-- The `x`-mass of `E←(S)` is the pair sum, when `S ∩ L` and `L ∖ S` are
disjoint (always). -/
theorem sum_arrowLeft (x : Sym2 (Fin n) → ℝ) (S L : Finset (Fin n)) :
    ∑ e ∈ arrowLeft S L, x e = pairSum x (S ∩ L) (L \ S) :=
  sum_betweenEdges x (Finset.disjoint_left.mpr fun _ hu hv =>
    (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hu).1)

theorem sum_arrowRight (x : Sym2 (Fin n) → ℝ) (S R : Finset (Fin n)) :
    ∑ e ∈ arrowRight S R, x e = pairSum x (S ∩ R) (R \ S) :=
  sum_arrowLeft x S R

/-- **KKO22 §3 display after Claim 3.3**: for `S` crossed on both sides
by near-min cuts `L`, `R`, the arrow masses are at least `1 - η/2` each
(this is Lemma 2.9 = our `one_sub_half_le_pairSum_inter_sdiff'`). -/
theorem one_sub_half_le_sum_arrowLeft {x : Sym2 (Fin n) → ℝ}
    (hx : x ∈ subtourLP n) {S L : Finset (Fin n)} {η : ℝ}
    (hL : IsNearMinCut x η L) (hc : Crossing L S) :
    1 - η / 2 ≤ ∑ e ∈ arrowLeft S L, x e := by
  rw [sum_arrowLeft, Finset.inter_comm]
  exact one_sub_half_le_pairSum_inter_sdiff hx hL hc

theorem one_sub_half_le_sum_arrowRight {x : Sym2 (Fin n) → ℝ}
    (hx : x ∈ subtourLP n) {S R : Finset (Fin n)} {η : ℝ}
    (hR : IsNearMinCut x η R) (hc : Crossing R S) :
    1 - η / 2 ≤ ∑ e ∈ arrowRight S R, x e :=
  one_sub_half_le_sum_arrowLeft hx hR hc

/-- **KKO22 §3, `x(E∘(S)) = O(η)`**: for `S` an `η`-near min cut crossed
on both sides by near-min cuts `L`, `R`, the leftover mass is at most
`2η`. -/
theorem sum_arrowCirc_le {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n)
    {S L R : Finset (Fin n)} {η : ℝ} (hS : IsNearMinCut x η S)
    (hL : IsNearMinCut x η L) (hR : IsNearMinCut x η R)
    (hcL : Crossing L S) (hcR : Crossing R S)
    (hd : Disjoint (L \ S) (R \ S)) :
    ∑ e ∈ arrowCirc S L R, x e ≤ 2 * η := by
  have hsplit := cutSum_eq_arrow_sum x (S := S) hd
  have h1 := one_sub_half_le_sum_arrowLeft hx hL hcL
  have h2 := one_sub_half_le_sum_arrowRight hx hR hcR
  linarith [hS.cut_le]

/-- `S_L` is unique. -/
theorem IsSL.unique (hS : S ∈ 𝒞) {L L' : Finset (Fin n)}
    (h1 : P.IsSL S L) (h2 : P.IsSL S L') : L = L' := by
  obtain ⟨hL, hc, hmin, htie⟩ := h1
  obtain ⟨hL', hc', hmin', htie'⟩ := h2
  have hcard : (P.outsideIn S ∩ P.outsideIn L).card
      = (P.outsideIn S ∩ P.outsideIn L').card :=
    le_antisymm (hmin L' hL' hc') (hmin' L hL hc)
  have hlen : P.len L = P.len L' :=
    le_antisymm (htie L' hL' hc' hcard.symm) (htie' L hL hc hcard)
  have e1 := P.card_outsideIn_inter_left hS hL hc
  have e2 := P.card_outsideIn_inter_left hS hL' hc'
  have hd1 := mem_arcSet.mp hc.2
  have hd2 := mem_arcSet.mp hc'.2
  have hstart : P.start L = P.start L' := by
    have hv : (P.start S - P.start L).val
        = (P.start S - P.start L').val := by omega
    exact sub_right_inj.mp (Fin.val_injective hv)
  exact P.arc_injective L hL L' hL' hstart hlen

end PolygonRep

end TSPGap

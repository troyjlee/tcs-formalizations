/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Polygon

/-!
# Crossing components: separation, and Theorem 4.5

KKO22 Theorem 4.5 (= [Ben97, Lemma 4.1.7]) says two *distinct* crossing
components have atoms covering `V` between them.  KKO give no proof — they
cite Benczúr's thesis, which survives only as an image scan — so it is proved
here, from Benczúr's argument as transcribed in `NOTES/benczur-4.1.7.md`.

The file runs in four movements.

1. **Separation.**  What the word "distinct" is doing all the work in: cuts in
   different crossing components never cross (`not_crossing_of_ne`).  With the
   fact that a shared member forces two components to coincide, this is the
   whole content of `maximal` unfolded, and it turns "distinct components"
   into the combinatorial hypothesis Benczúr's argument consumes.
2. **Local orientation.**  Benczúr renames `D` and `D̄` freely; the carrier
   here stores one side per cut, so the renaming is done pointwise instead —
   `toward r S` / `away r S` are the sides of `S` containing and missing `r`,
   and the two atoms of the lemma are read off them.
3. **The two uses of connectivity.**  `sideSubset_const` is the first (the
   class of `𝒞₂` relative to a fixed cut of `𝒞₁` is constant);
   `away_subset_of_step` is the second — the consistency step Benczúr's proof
   elides, which is what lets one orientation of `𝒞₂` serve every cut of `𝒞₁`.
4. **The lemma.**  `exists_atomOf_union_atomOf_eq_univ` in root-free form, and
   `exists_atom_union_eq_univ` as the interface the development consumes.

Near-minimality of the cuts is used only to know they are proper, so the
root-free form takes properness as a hypothesis and mentions neither `x` nor
`η`; Theorem 4.5 accordingly no longer needs `x ∈ subtourLP n`.
-/

namespace TSPGap

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ}

/-- Crossing components that share a cut are equal.

Reachability inside `𝒞'` is walked one crossing at a time: each step lands on
a near-minimum cut that crosses something already known to be in `𝒞`, and
`maximal` pulls it into `𝒞`. -/
theorem IsCrossingComponent.eq_of_mem_of_mem {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsCrossingComponent x η 𝒞) (hC' : IsCrossingComponent x η 𝒞')
    {S : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S ∈ 𝒞') : 𝒞 = 𝒞' := by
  have key : ∀ (𝒟 𝒟' : Finset (Finset (Fin n))), IsCrossingComponent x η 𝒟 →
      IsCrossingComponent x η 𝒟' → S ∈ 𝒟 → S ∈ 𝒟' → 𝒟' ⊆ 𝒟 := by
    intro 𝒟 𝒟' hD hD' hSD hSD' T hT
    have h := hD'.conn S hSD' T hT
    clear hT
    induction h with
    | refl => exact hSD
    | tail _ hstep ih =>
        exact hD.maximal _ (hD'.nearMin _ hstep.2.1) ⟨_, ih, hstep.2.2.symm⟩
  exact Finset.Subset.antisymm (key 𝒞' 𝒞 hC' hC hS' hS) (key 𝒞 𝒞' hC hC' hS hS')

/-- **Cuts in different crossing components do not cross.**

If they did, `maximal` would place the first cut inside the second component
as well, and a shared member forces the components to coincide. -/
theorem IsCrossingComponent.not_crossing_of_ne
    {𝒞 𝒞' : Finset (Finset (Fin n))} (hC : IsCrossingComponent x η 𝒞)
    (hC' : IsCrossingComponent x η 𝒞') (hne : 𝒞 ≠ 𝒞') {S S' : Finset (Fin n)}
    (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞') : ¬ Crossing S S' := by
  intro hcr
  exact hne (hC.eq_of_mem_of_mem hC' hS
    (hC'.maximal S (hC.nearMin S hS) ⟨S', hS', hcr⟩))

/-- The contrapositive, in the form Benczúr's argument uses: from a crossing
pair, the two components are the same. -/
theorem IsCrossingComponent.eq_of_crossing {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsCrossingComponent x η 𝒞) (hC' : IsCrossingComponent x η 𝒞')
    {S S' : Finset (Fin n)} (hS : S ∈ 𝒞) (hS' : S' ∈ 𝒞')
    (hcr : Crossing S S') : 𝒞 = 𝒞' := by
  by_contra hne
  exact hC.not_crossing_of_ne hC' hne hS hS' hcr

/-! ### Local orientation, for Benczúr's `wlog`

Benczúr renames `D` and `D̄` freely.  The carrier here stores one side per
cut, and that side is *not* canonically oriented — near-minimality and
crossing are both complement-invariant, so a maximal component can contain
both `S` and `Sᶜ`.  Rather than orient the stored cuts, the renaming is done
locally: `toward r S` is the side of `S` containing `r`, `away r S` the other.

`atomOf 𝒞 r` is then exactly `⋂_{S ∈ 𝒞} toward r S`, and its complement
exactly `⋃_{S ∈ 𝒞} away r S` — which are the intersection and union in
Benczúr's proof, expressed without touching the stored cuts. -/

/-- The side of the cut `S` containing `r`. -/
def toward (r : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if r ∈ S then S else Sᶜ

/-- The side of the cut `S` not containing `r`. -/
def away (r : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if r ∈ S then Sᶜ else S

theorem toward_compl (r : Fin n) (S : Finset (Fin n)) :
    (toward r S)ᶜ = away r S := by
  rw [toward, away]
  by_cases h : r ∈ S <;> simp [h]

/-- A side of `S` containing `r` *is* `toward r S` — the two sides partition
`V`, so containing `r` identifies which one it is.  This is how a side arrived
at by other means is recognized as the one the atom characterization wants. -/
theorem toward_eq_of_mem_side {S B : Finset (Fin n)} {r : Fin n}
    (hB : B = S ∨ B = Sᶜ) (hr : r ∈ B) : toward r S = B := by
  rcases hB with rfl | rfl
  · rw [toward, if_pos hr]
  · rw [toward, if_neg (Finset.mem_compl.mp hr)]

/-- `atomOf 𝒞 r = ⋂_{S ∈ 𝒞} toward r S`, pointwise. -/
theorem mem_atomOf_iff_forall_toward {𝒞 : Finset (Finset (Fin n))} {r v : Fin n} :
    v ∈ atomOf 𝒞 r ↔ ∀ S ∈ 𝒞, v ∈ toward r S := by
  rw [mem_atomOf]
  refine ⟨fun h S hS => ?_, fun h S hS => ?_⟩
  · have hiff := h S hS
    by_cases hr : r ∈ S
    · simpa [toward, hr] using hiff.mp hr
    · simp only [toward, if_neg hr, Finset.mem_compl]
      exact fun hv => hr (hiff.mpr hv)
  · have hv := h S hS
    by_cases hr : r ∈ S
    · simp only [toward, if_pos hr] at hv
      exact ⟨fun _ => hv, fun _ => hr⟩
    · simp only [toward, if_neg hr, Finset.mem_compl] at hv
      exact ⟨fun h' => absurd h' hr, fun h' => absurd h' hv⟩

/-- The complement of an atom is `⋃_{S ∈ 𝒞} away r S`, pointwise. -/
theorem notMem_atomOf_iff_exists_away {𝒞 : Finset (Finset (Fin n))}
    {r v : Fin n} : v ∉ atomOf 𝒞 r ↔ ∃ S ∈ 𝒞, v ∈ away r S := by
  rw [mem_atomOf_iff_forall_toward]
  push Not
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨S, hS, hv⟩ := h
    exact ⟨S, hS, by rw [← toward_compl]; exact Finset.mem_compl.mpr hv⟩
  · obtain ⟨S, hS, hv⟩ := h
    refine ⟨S, hS, ?_⟩
    rw [← toward_compl] at hv
    exact Finset.mem_compl.mp hv

/-! ### The dichotomy -/

/-- **Benczúr's four-way split.**  Non-crossing cuts have a side of one inside
a side of the other: either some side of `D` lies in `C`, or some side of `D`
lies in `Cᶜ`.  This is what puts every cut of `𝒞₂` into one of the two
classes in the proof of Lemma 4.1.7. -/
theorem side_subset_of_not_crossing {C D : Finset (Fin n)} (h : ¬ Crossing C D) :
    (D ⊆ C ∨ Dᶜ ⊆ C) ∨ (D ⊆ Cᶜ ∨ Dᶜ ⊆ Cᶜ) := by
  by_cases h1 : (C ∩ D).Nonempty
  · by_cases h2 : (C \ D).Nonempty
    · by_cases h3 : (D \ C).Nonempty
      · have h4 : C ∪ D = Finset.univ := by
          by_contra h4
          exact h ⟨h1, h2, h3, h4⟩
        refine Or.inl (Or.inr fun v hv => ?_)
        have hmem : v ∈ C ∪ D := by rw [h4]; exact Finset.mem_univ v
        exact (Finset.mem_union.mp hmem).resolve_right (Finset.mem_compl.mp hv)
      · exact Or.inl (Or.inl (Finset.sdiff_eq_empty_iff_subset.mp
          (Finset.not_nonempty_iff_eq_empty.mp h3)))
    · exact Or.inr (Or.inr (Finset.compl_subset_compl.mpr
        (Finset.sdiff_eq_empty_iff_subset.mp
          (Finset.not_nonempty_iff_eq_empty.mp h2))))
  · exact Or.inr (Or.inl (Finset.disjoint_left.mp
      (Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp h1)) |> fun hd v hv =>
          Finset.mem_compl.mpr fun hc => hd hc hv))

/-! ### The two classes, and why they cannot cross -/

/-- Some side of the cut `D` lies inside `A`.  This is the classification
Benczúr applies to the cuts of `𝒞₂` relative to a fixed `C ∈ 𝒞₁`. -/
def SideSubset (D A : Finset (Fin n)) : Prop := D ⊆ A ∨ Dᶜ ⊆ A

/-- Restatement of the four-way split: relative to `C`, every cut not
crossing `C` falls into one of the two classes. -/
theorem sideSubset_or_of_not_crossing {C D : Finset (Fin n)}
    (h : ¬ Crossing C D) : SideSubset D C ∨ SideSubset D Cᶜ :=
  side_subset_of_not_crossing h

/-- Cuts with disjoint sides do not cross.

No complement-invariance of `Crossing` is needed: each of the four choices
of sides kills a different one of its four conjuncts.  Disjoint `D, D'` empty
`D ∩ D'`; `D, D'ᶜ` force `D ⊆ D'`; `Dᶜ, D'` force `D' ⊆ D`; and `Dᶜ, D'ᶜ`
force `D ∪ D' = V`. -/
theorem not_crossing_of_sides_disjoint {D D' X Y : Finset (Fin n)}
    (hX : X = D ∨ X = Dᶜ) (hY : Y = D' ∨ Y = D'ᶜ) (hd : Disjoint X Y) :
    ¬ Crossing D D' := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases hX with rfl | rfl
  · rcases hY with rfl | rfl
    · rw [Finset.disjoint_iff_inter_eq_empty.mp hd] at h1
      exact Finset.not_nonempty_empty h1
    · have hsub : X ⊆ D' := fun v hv => by
        by_contra hc
        exact Finset.disjoint_left.mp hd hv (Finset.mem_compl.mpr hc)
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h2
      exact Finset.not_nonempty_empty h2
  · rcases hY with rfl | rfl
    · have hsub : Y ⊆ D := fun v hv => by
        by_contra hc
        exact Finset.disjoint_left.mp hd (Finset.mem_compl.mpr hc) hv
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h3
      exact Finset.not_nonempty_empty h3
    · refine h4 ?_
      rw [Finset.eq_univ_iff_forall]
      intro v
      by_contra hc
      rw [Finset.mem_union] at hc
      push Not at hc
      exact Finset.disjoint_left.mp hd (Finset.mem_compl.mpr hc.1)
        (Finset.mem_compl.mpr hc.2)

/-- **Opposite classes cannot cross.**  A cut with a side inside `C` never
crosses one with a side inside `Cᶜ` — the two sides are disjoint. -/
theorem not_crossing_of_opposite {C D D' : Finset (Fin n)}
    (hD : SideSubset D C) (hD' : SideSubset D' Cᶜ) : ¬ Crossing D D' := by
  have key : ∀ {X Y : Finset (Fin n)}, X ⊆ C → Y ⊆ Cᶜ → Disjoint X Y := by
    intro X Y hXC hYC
    refine Finset.disjoint_left.mpr fun v hvX hvY => ?_
    exact (Finset.mem_compl.mp (hYC hvY)) (hXC hvX)
  rcases hD with h | h <;> rcases hD' with h' | h'
  · exact not_crossing_of_sides_disjoint (Or.inl rfl) (Or.inl rfl) (key h h')
  · exact not_crossing_of_sides_disjoint (Or.inl rfl) (Or.inr rfl) (key h h')
  · exact not_crossing_of_sides_disjoint (Or.inr rfl) (Or.inl rfl) (key h h')
  · exact not_crossing_of_sides_disjoint (Or.inr rfl) (Or.inr rfl) (key h h')

/-! ### Benczúr's first use of connectivity: the class is constant -/

/-- The four-way split, read against a chosen side `A` of `C` rather than
against `C` itself.  Only the two sides get swapped, since `Aᶜ` is the other
side of `C` either way. -/
theorem sideSubset_or {C D A : Finset (Fin n)} (h : ¬ Crossing C D)
    (hA : A = C ∨ A = Cᶜ) : SideSubset D A ∨ SideSubset D Aᶜ := by
  rcases hA with rfl | rfl
  · exact sideSubset_or_of_not_crossing h
  · rw [compl_compl]
    exact (sideSubset_or_of_not_crossing h).symm

/-- **The class is constant across a component.**  If no cut of `𝒞₂` crosses
`C`, then the classification "has a side inside `A`", for a fixed side `A` of
`C`, is the same for every cut of `𝒞₂`.

This is Benczúr's "one of the two subsets must be empty", and it is where
connectivity of `𝒞₂` is used: walk the crossing path out of `D₀`; each step
crosses, and opposite classes cannot cross, so the class never changes.

Only connectivity is consumed, so the hypothesis is taken bare rather than
through `IsCrossingComponent`; near-minimality plays no part. -/
theorem sideSubset_const {𝒞₂ : Finset (Finset (Fin n))}
    (hconn : ∀ D ∈ 𝒞₂, ∀ D' ∈ 𝒞₂,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞₂ ∧ B ∈ 𝒞₂ ∧ Crossing A B) D D')
    {C A : Finset (Fin n)} (hA : A = C ∨ A = Cᶜ)
    (hnc : ∀ D ∈ 𝒞₂, ¬ Crossing C D)
    {D₀ : Finset (Fin n)} (hD₀ : D₀ ∈ 𝒞₂) (hcls : SideSubset D₀ A)
    {D : Finset (Fin n)} (hD : D ∈ 𝒞₂) : SideSubset D A := by
  have h := hconn D₀ hD₀ D hD
  clear hD
  induction h with
  | refl => exact hcls
  | tail _ hstep ih =>
      rcases sideSubset_or (hnc _ hstep.2.1) hA with h' | h'
      · exact h'
      · exact absurd hstep.2.2 (not_crossing_of_opposite ih h')

/-- **Benczúr's first `wlog`, packaged.**  Relative to a cut `C` crossed by no
member of `𝒞₂`, there is one side `A` of `C` inside which *every* cut of `𝒞₂`
has a side.  Which side it is comes from any one member; constancy does the
rest. -/
theorem exists_side_const {𝒞₂ : Finset (Finset (Fin n))} (h₂ : 𝒞₂.Nonempty)
    (hconn : ∀ D ∈ 𝒞₂, ∀ D' ∈ 𝒞₂,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞₂ ∧ B ∈ 𝒞₂ ∧ Crossing A B) D D')
    {C : Finset (Fin n)} (hnc : ∀ D ∈ 𝒞₂, ¬ Crossing C D) :
    ∃ A, (A = C ∨ A = Cᶜ) ∧ ∀ D ∈ 𝒞₂, SideSubset D A := by
  obtain ⟨D₀, hD₀⟩ := h₂
  rcases sideSubset_or_of_not_crossing (hnc D₀ hD₀) with h | h
  · exact ⟨C, Or.inl rfl, fun D hD => sideSubset_const hconn (Or.inl rfl) hnc hD₀ h hD⟩
  · exact ⟨Cᶜ, Or.inr rfl, fun D hD => sideSubset_const hconn (Or.inr rfl) hnc hD₀ h hD⟩

/-! ### The conclusion of Lemma 4.1.7 -/

/-- **The pointwise conclusion.**  Once every `away q D` sits inside every
`toward p C`, the two atoms cover `V`.

This is Benczúr's last step, `⋃_{𝒞₂} D ⊆ ⋂_{𝒞₁} C`, read through the two
characterizations: the union is the complement of `atomOf 𝒞₂ q` and the
intersection is `atomOf 𝒞₁ p`, so the containment *is* the covering. -/
theorem atomOf_union_atomOf_eq_univ {𝒞₁ 𝒞₂ : Finset (Finset (Fin n))}
    {p q : Fin n}
    (h : ∀ C ∈ 𝒞₁, ∀ D ∈ 𝒞₂, away q D ⊆ toward p C) :
    atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro v
  rw [Finset.mem_union]
  by_cases hv : v ∈ atomOf 𝒞₂ q
  · exact Or.inr hv
  · refine Or.inl (mem_atomOf_iff_forall_toward.mpr fun C hC => ?_)
    obtain ⟨D, hD, hvD⟩ := notMem_atomOf_iff_exists_away.mp hv
    exact h C hC D hD hvD

/-- The side of a cut missing `q` is the one inside `C`, when `q ∉ C`.

This is how a class membership is converted into the `away` form the
conclusion needs: a side of `D` inside `C` cannot contain a vertex outside
`C`, and the two sides of `D` partition `V`. -/
theorem away_subset_of_sideSubset {C D : Finset (Fin n)} {q : Fin n}
    (hq : q ∉ C) (h : SideSubset D C) : away q D ⊆ C := by
  rcases h with h | h
  · have hqD : q ∉ D := fun hc => hq (h hc)
    rw [away, if_neg hqD]
    exact h
  · have hqD : q ∈ D := by
      by_contra hc
      exact hq (h (Finset.mem_compl.mpr hc))
    rw [away, if_pos hqD]
    exact h

/-! ### Benczúr's second use of connectivity

Benczúr orients each `D ∈ 𝒞₂` by "renaming `D` and `D̄`" relative to a fixed
`C ∈ 𝒞₁`, then asserts the same orientation serves every other `C`.  That
consistency is the step his proof elides, and it is where the second use of
connectivity lives.  It holds because an *inconsistent* orientation forces two
sides of `C` and `C'` to cover `V`, i.e. empties one of their four Venn
regions — which contradicts `C` and `C'` crossing.
-/

/-- Sides of crossing cuts always meet.  The exact converse of
`not_crossing_of_sides_disjoint`, and the form the consistency argument
consumes. -/
theorem inter_nonempty_of_crossing {C C' X Y : Finset (Fin n)}
    (h : Crossing C C') (hX : X = C ∨ X = Cᶜ) (hY : Y = C' ∨ Y = C'ᶜ) :
    (X ∩ Y).Nonempty := by
  rw [← Finset.not_disjoint_iff_nonempty_inter]
  exact fun hd => not_crossing_of_sides_disjoint hX hY hd h

theorem side_compl {C X : Finset (Fin n)} (h : X = C ∨ X = Cᶜ) :
    Xᶜ = C ∨ Xᶜ = Cᶜ := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (compl_compl C)

/-- **The consistency step.**  If every `away q D` already lies in a side `B`
of `C`, and every `D` has *some* side inside a side `A` of a crossing cut
`C'`, then that side is `away q D` again — so `away q D ⊆ A`.

The other orientation is impossible: it would give `Aᶜ ⊆ away q D ⊆ B`, hence
`Aᶜ ∩ Bᶜ = ∅`, emptying one of the four Venn regions of `C` and `C'` and
contradicting `Crossing C C'`. -/
theorem away_subset_of_step {𝒞₂ : Finset (Finset (Fin n))}
    {C C' A B : Finset (Fin n)} {q : Fin n} (hcr : Crossing C C')
    (hA : A = C' ∨ A = C'ᶜ) (hB : B = C ∨ B = Cᶜ)
    (hIH : ∀ D ∈ 𝒞₂, away q D ⊆ B)
    (hconst : ∀ D ∈ 𝒞₂, SideSubset D A) :
    ∀ D ∈ 𝒞₂, away q D ⊆ A := by
  intro D hD
  have contra : Aᶜ ⊆ B → False := by
    intro hsub
    obtain ⟨v, hv⟩ := inter_nonempty_of_crossing hcr (side_compl hB) (side_compl hA)
    rw [Finset.mem_inter] at hv
    exact (Finset.mem_compl.mp hv.1) (hsub hv.2)
  rcases hconst D hD with h | h
  · by_cases hqD : q ∈ D
    · refine absurd ?_ contra
      refine Finset.Subset.trans ?_ (hIH D hD)
      rw [away, if_pos hqD]
      exact Finset.compl_subset_compl.mpr h
    · rw [away, if_neg hqD]; exact h
  · by_cases hqD : q ∈ D
    · rw [away, if_pos hqD]; exact h
    · refine absurd ?_ contra
      refine Finset.Subset.trans ?_ (hIH D hD)
      rw [away, if_neg hqD]
      have hc := Finset.compl_subset_compl.mpr h
      rwa [compl_compl] at hc

/-! ### Benczúr's Lemma 4.1.7, root-free

The theorem below is the whole of [Ben97, Lemma 4.1.7] with the cut systems
replaced by exactly what its proof consumes: the two connectivity proofs,
pairwise non-crossing, and properness of the cuts of `𝒞₁` (needed only to find
a vertex outside one side of the base cut).  Near-minimality — and with it the
LP point `x` and the parameter `η` — never appears; the statement is pure
finite combinatorics, which is why Theorem 4.5 below needs no `x ∈ subtourLP n`.
-/

/-- **[Ben97, Lemma 4.1.7] / KKO22 Theorem 4.5, root-free form.**  Two families
of cuts, each connected under crossing and no member of one crossing a member
of the other, have an atom apiece covering `V`.

The proof runs Benczúr's argument with the sides chosen locally rather than by
renaming: fix `C₀ ∈ 𝒞₁`, let `A₀` be the side of `C₀` housing a side of every
`D ∈ 𝒞₂` (`exists_side_const`, his first `wlog`), and pick `q ∉ A₀`, which makes
`away q D` *be* that side.  Chaining `away_subset_of_step` along the crossing
paths of `𝒞₁` — the consistency step his proof elides — carries that inclusion
from `C₀` to every `C ∈ 𝒞₁`.  Any `p` outside `atomOf 𝒞₂ q` then lies in the
side of `C` reached, identifying it as `toward p C`. -/
theorem exists_atomOf_union_atomOf_eq_univ {𝒞₁ 𝒞₂ : Finset (Finset (Fin n))}
    (h₁ : 𝒞₁.Nonempty) (h₂ : 𝒞₂.Nonempty)
    (hconn₁ : ∀ C ∈ 𝒞₁, ∀ C' ∈ 𝒞₁,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞₁ ∧ B ∈ 𝒞₁ ∧ Crossing A B) C C')
    (hconn₂ : ∀ D ∈ 𝒞₂, ∀ D' ∈ 𝒞₂,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞₂ ∧ B ∈ 𝒞₂ ∧ Crossing A B) D D')
    (hproper : ∀ C ∈ 𝒞₁, C.Nonempty ∧ C ≠ Finset.univ)
    (hnc : ∀ C ∈ 𝒞₁, ∀ D ∈ 𝒞₂, ¬ Crossing C D) :
    ∃ p q, atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q = Finset.univ := by
  -- The base point: a side `A₀` of some `C₀ ∈ 𝒞₁` housing a side of every `D`.
  obtain ⟨C₀, hC₀⟩ := h₁
  obtain ⟨A₀, hA₀, hconst₀⟩ := exists_side_const h₂ hconn₂ (hnc C₀ hC₀)
  have hA₀ne : A₀ ≠ Finset.univ := by
    intro hc
    rcases hA₀ with h | h
    · exact (hproper C₀ hC₀).2 (by rw [← h]; exact hc)
    · obtain ⟨v, hv⟩ := (hproper C₀ hC₀).1
      have hvc : v ∈ A₀ := by rw [hc]; exact Finset.mem_univ v
      rw [h] at hvc
      exact (Finset.mem_compl.mp hvc) hv
  obtain ⟨q, hq⟩ : ∃ q, q ∉ A₀ := by
    by_contra hcon
    push Not at hcon
    exact hA₀ne (Finset.eq_univ_iff_forall.mpr hcon)
  -- The induction: that side travels to every cut of `𝒞₁`.
  have key : ∀ C ∈ 𝒞₁, ∃ B, (B = C ∨ B = Cᶜ) ∧ ∀ D ∈ 𝒞₂, away q D ⊆ B := by
    intro C hC
    have h := hconn₁ C₀ hC₀ C hC
    clear hC
    induction h with
    | refl => exact ⟨A₀, hA₀, fun D hD => away_subset_of_sideSubset hq (hconst₀ D hD)⟩
    | tail _ hstep ih =>
        obtain ⟨B, hB, hBsub⟩ := ih
        obtain ⟨A, hA, hconst⟩ := exists_side_const h₂ hconn₂ (hnc _ hstep.2.1)
        exact ⟨A, hA, away_subset_of_step hstep.2.2 hA hB hBsub hconst⟩
  -- The choice of `p`, and the conclusion.
  by_cases hU : ∃ p, p ∉ atomOf 𝒞₂ q
  · obtain ⟨p, hp⟩ := hU
    refine ⟨p, q, atomOf_union_atomOf_eq_univ fun C hC D hD => ?_⟩
    obtain ⟨B, hB, hBsub⟩ := key C hC
    obtain ⟨D', hD', hpD'⟩ := notMem_atomOf_iff_exists_away.mp hp
    rw [toward_eq_of_mem_side hB (hBsub D' hD' hpD')]
    exact hBsub D hD
  · push Not at hU
    exact ⟨q, q, Finset.eq_univ_iff_forall.mpr fun v =>
      Finset.mem_union.mpr (Or.inr (hU v))⟩

/-- **KKO22 Theorem 4.5** (= [Ben97, Lemma 4.1.7]).  Two distinct crossing
components have an atom apiece covering `V`.

This is the interface the rest of the development consumes; the content is
`exists_atomOf_union_atomOf_eq_univ`, and all this wrapper does is feed it the
three facts `IsCrossingComponent` supplies — nonemptiness, connectivity, and
(via `not_crossing_of_ne`) the separation that distinctness buys — together
with properness of the cuts, which comes from near-minimality.

Near-minimality enters *only* through properness, so the subtour-LP membership
of `x` that this statement used to carry as a black box is not needed. -/
theorem exists_atom_union_eq_univ {𝒞 𝒞' : Finset (Finset (Fin n))}
    (hC : IsCrossingComponent x η 𝒞) (hC' : IsCrossingComponent x η 𝒞')
    (hne : 𝒞 ≠ 𝒞') :
    ∃ a ∈ atoms 𝒞, ∃ a' ∈ atoms 𝒞', a ∪ a' = Finset.univ := by
  obtain ⟨p, q, h⟩ := exists_atomOf_union_atomOf_eq_univ hC.nonempty hC'.nonempty
    hC.conn hC'.conn
    (fun C hCm => ⟨(hC.nearMin C hCm).nonempty, (hC.nearMin C hCm).ne_univ⟩)
    (fun C hCm D hDm => hC.not_crossing_of_ne hC' hne hCm hDm)
  exact ⟨atomOf 𝒞 p, mem_atoms.mpr ⟨p, rfl⟩, atomOf 𝒞' q, mem_atoms.mpr ⟨q, rfl⟩, h⟩

end TSPGap

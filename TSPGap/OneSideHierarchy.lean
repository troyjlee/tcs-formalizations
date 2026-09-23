/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonReflect

/-!
# KKO21 §4.2: the left and right hierarchies of a one-side polygon

For a rooted polygon `P` of a component `𝒞` of `N_{η,≤1}` (KKO21 Definition 4.10):

* `StrictAncR A B`: `B` is a **strict ancestor** of `A` in the right hierarchy — both open
  on the right, `A ⊆ B`, and `B` ends strictly later; `StrictParentR A B`: the closest one
  (contained in every strict ancestor; `exists_strictParentR`).
* `common_ancestorR` (Lemma 4.13): two disjoint cuts open on the right have a common
  ancestor open on the right.
* `exists_strictAncR` (Lemma 4.14): a cut open on the right that does not reach the last
  atom has a strict ancestor.
* `exists_crossesOnLeft_of_strictParentR` (Lemma 4.12): a strict parent pair in the right
  hierarchy is crossed on the left by a common member.

KKO21 prove Lemmas 4.12–4.13 with a shortest crossing path and its first cut leaving an
interval; here that is `exists_boundary_crossing` — along any crossing path from a cut
satisfying a predicate to one violating it, some crossing pair straddles the predicate —
and, for Lemma 4.12, the left crosser of `A` starting earliest.  The left-hierarchy
versions are the right-hierarchy ones on the reflected polygon (`StrictAncL`,
`common_ancestorL`, `exists_strictAncL`, `exists_crossesOnRight_of_strictParentL`).
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

/-- Along a crossing path from a cut satisfying `Good` to one violating it, some crossing
pair straddles `Good`. -/
theorem exists_boundary_crossing {Good : Finset (Fin n) → Prop} {C : Finset (Fin n)}
    (hC : Good C) : ∀ B : Finset (Fin n),
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) C B → ¬ Good B →
      ∃ D ∈ 𝒞, ∃ E ∈ 𝒞, Good D ∧ ¬ Good E ∧ Crossing D E := by
  intro B hpath
  induction hpath with
  | refl => exact fun h => absurd hC h
  | @tail b c _ hbc ih =>
    intro hc
    by_cases hb : Good b
    · exact ⟨b, hbc.1, c, hbc.2.1, hb, hc, hbc.2.2⟩
    · exact ih hb

namespace PolygonRep

variable (P : PolygonRep 𝒞) (R : P.Rooted)

/-! ### Crossers -/

/-- A cut open on the right is crossed on the left by some member (the component is
nontrivial, so every member is crossed). -/
theorem exists_crossesOnLeft_of_openRight (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {A : Finset (Fin n)} (hA : P.OpenRight A) : ∃ C ∈ 𝒞, P.CrossesOnLeft C A := by
  obtain ⟨T, hT, hc⟩ := BG.exists_cross P.nontrivial hcomp.conn hA.1
  rcases P.crossesOnLeft_or_crossesOnRight hT hA.1 hc.symm with h | h
  · exact ⟨T, hT, h⟩
  · exact absurd h (hA.2 T hT)

/-- A cut open on the left is crossed on the right by some member. -/
theorem exists_crossesOnRight_of_openLeft (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {A : Finset (Fin n)} (hA : P.OpenLeft A) : ∃ C ∈ 𝒞, P.CrossesOnRight C A := by
  obtain ⟨T, hT, hc⟩ := BG.exists_cross P.nontrivial hcomp.conn hA.1
  rcases P.crossesOnLeft_or_crossesOnRight hT hA.1 hc.symm with h | h
  · exact absurd h (hA.2 T hT)
  · exact ⟨T, hT, h⟩

/-- Two cuts open on the right that meet are nested. -/
theorem nested_of_openRight (hcomp : IsOneSideComponent e₀ x η 𝒞) {A B : Finset (Fin n)}
    (hA : P.OpenRight A) (hB : P.OpenRight B) (h : ¬ Disjoint A B) : A ⊆ B ∨ B ⊆ A := by
  rcases nested_or_disjoint_of_not_crossing (hcomp.avoids A hA.1) (hcomp.avoids B hB.1)
    (P.not_crossing_of_openRight hA hB) with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 h

/-! ### The right hierarchy -/

/-- `B` is a strict ancestor of `A` in the right hierarchy. -/
def StrictAncR (A B : Finset (Fin n)) : Prop :=
  P.OpenRight A ∧ P.OpenRight B ∧ A ⊆ B ∧ P.hi R A < P.hi R B

/-- `B` is the strict parent of `A` in the right hierarchy: a strict ancestor contained
in every strict ancestor. -/
def StrictParentR (A B : Finset (Fin n)) : Prop :=
  P.StrictAncR R A B ∧ ∀ B', P.StrictAncR R A B' → B ⊆ B'

/-- A cut with a strict ancestor has a strict parent. -/
theorem exists_strictParentR (hcomp : IsOneSideComponent e₀ x η 𝒞) {A : Finset (Fin n)}
    (h : ∃ B, P.StrictAncR R A B) : ∃ B, P.StrictParentR R A B := by
  classical
  obtain ⟨B₀, hB₀⟩ := h
  obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image (𝒞.filter fun B => P.StrictAncR R A B)
    Finset.card ⟨B₀, mem_filter.mpr ⟨hB₀.2.1.1, hB₀⟩⟩
  rw [mem_filter] at hB
  refine ⟨B, hB.2, fun B' hB' => ?_⟩
  have hle := hmin B' (mem_filter.mpr ⟨hB'.2.1.1, hB'⟩)
  have hne : ¬ Disjoint B B' := by
    obtain ⟨v, hv⟩ := (hcomp.nearMin A hB.2.1.1).nonempty
    exact fun hd => disjoint_left.mp hd (hB.2.2.2.1 hv) (hB'.2.2.1 hv)
  rcases P.nested_of_openRight hcomp hB.2.2.1 hB'.2.1 hne with h1 | h1
  · exact h1
  · rw [eq_of_subset_of_card_le h1 hle]

/-- **KKO21 Lemma 4.13**, the ordered case: `A` lies left of `B`. -/
theorem common_ancestorR_aux (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A B : Finset (Fin n)} (hA : P.OpenRight A)
    (hB : P.OpenRight B) (hAB : P.hi R A < P.lo R B) :
    ∃ C, P.OpenRight C ∧ A ⊆ C ∧ B ⊆ C := by
  classical
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image (𝒞.filter fun C => P.OpenRight C ∧ A ⊆ C)
    Finset.card ⟨A, mem_filter.mpr ⟨hA.1, hA, subset_rfl⟩⟩
  rw [mem_filter] at hC
  obtain ⟨hCm, hCo, hAC⟩ := hC
  have hAlh := P.lo_lt_hi R hA.1
  have hBlh := P.lo_lt_hi R hB.1
  have hClh := P.lo_lt_hi R hCm
  by_cases hCB : Disjoint C B
  · exfalso
    have hAC' := (P.subset_iff R hA.1 hCm).mp hAC
    have hCB' : P.hi R C < P.lo R B := by
      rcases (P.disjoint_iff R hCm hB.1).mp hCB with h | h
      · exact h
      · omega
    obtain ⟨D, hD, E, hE, hGD, hGE, hDE⟩ :=
      exists_boundary_crossing (𝒞 := 𝒞) (Good := fun D => P.hi R D ≤ P.hi R C) le_rfl B
        (hcomp.conn C hCm B hB.1) (by omega)
    simp only [not_le] at hGE
    have hcr := (P.crossing_iff R hD hE).mp hDE
    have hleft : P.lo R D < P.lo R E ∧ P.lo R E ≤ P.hi R D ∧ P.hi R D < P.hi R E := by omega
    have hEcl : P.CrossesOnLeft D E := (P.crossesOnLeft_iff R hD hE).mpr hleft
    have hEo : P.OpenRight E := by
      rcases P.openLeft_or_openRight hx hcomp hη0 hη hE with h | h
      · exact absurd hEcl (h.2 D hD)
      · exact h
    have hnc := P.not_crossing_of_openRight hEo hCo
    rw [P.crossing_iff R hE hCm] at hnc
    have hCE : C ⊆ E := by
      rw [P.subset_iff R hCm hE]
      omega
    have hlt : C.card < E.card := card_lt_card (ssubset_of_subset_of_ne hCE fun e => by
      rw [e] at hGE
      omega)
    have := hmax E (mem_filter.mpr ⟨hE, hEo, hAC.trans hCE⟩)
    omega
  · rcases P.nested_of_openRight hcomp hCo hB hCB with h | h
    · exfalso
      have := (P.subset_iff R hA.1 hB.1).mp (hAC.trans h)
      omega
    · exact ⟨C, hCo, hAC, h⟩

/-- **KKO21 Lemma 4.13**: two disjoint cuts open on the right have a common ancestor open
on the right. -/
theorem common_ancestorR (R : P.Rooted) (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞) (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A B : Finset (Fin n)}
    (hA : P.OpenRight A) (hB : P.OpenRight B) (hd : Disjoint A B) :
    ∃ C, P.OpenRight C ∧ A ⊆ C ∧ B ⊆ C := by
  rcases (P.disjoint_iff R hA.1 hB.1).mp hd with hAB | hBA
  · exact P.common_ancestorR_aux R hx hcomp hη0 hη hA hB hAB
  · obtain ⟨C, hC, h1, h2⟩ := P.common_ancestorR_aux R hx hcomp hη0 hη hB hA hBA
    exact ⟨C, hC, h2, h1⟩

/-- **KKO21 Lemma 4.14**: a cut open on the right not reaching the last atom has a strict
ancestor. -/
theorem exists_strictAncR (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A : Finset (Fin n)} (hA : P.OpenRight A)
    (hlt : P.hi R A < P.m - 1) : ∃ B, P.StrictAncR R A B := by
  obtain ⟨B₀, hB₀, hhi⟩ := P.exists_hi_last R
  have hB₀o : P.OpenRight B₀ := ⟨hB₀, fun W hW hc => by
    rw [P.crossesOnRight_iff R hW hB₀] at hc
    have := P.hi_lt R hW
    omega⟩
  by_cases hd : Disjoint A B₀
  · obtain ⟨C, hCo, hAC, hBC⟩ := P.common_ancestorR R hx hcomp hη0 hη hA hB₀o hd
    refine ⟨C, hA, hCo, hAC, ?_⟩
    have := (P.subset_iff R hB₀ hCo.1).mp hBC
    have := P.hi_lt R hCo.1
    omega
  · rcases P.nested_of_openRight hcomp hA hB₀o hd with h | h
    · exact ⟨B₀, hA, hB₀o, h, by omega⟩
    · exfalso
      have := (P.subset_iff R hB₀ hA.1).mp h
      omega

/-- **KKO21 Lemma 4.12**: a strict parent pair in the right hierarchy is crossed on the
left by a common member — the left crosser of `A` starting earliest. -/
theorem exists_crossesOnLeft_of_strictParentR (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞) (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    {A B : Finset (Fin n)} (hAB : P.StrictParentR R A B) :
    ∃ C ∈ 𝒞, P.CrossesOnLeft C A ∧ P.CrossesOnLeft C B := by
  classical
  obtain ⟨⟨hAo, hBo, hsub, hlt⟩, hclosest⟩ := hAB
  have hAm := hAo.1
  have hBm := hBo.1
  have hsub' := (P.subset_iff R hAm hBm).mp hsub
  obtain ⟨C₁, hC₁, hmin⟩ := Finset.exists_min_image (𝒞.filter fun C => P.CrossesOnLeft C A)
    (P.lo R) (by
      obtain ⟨C, hC, hc⟩ := P.exists_crossesOnLeft_of_openRight hcomp hAo
      exact ⟨C, mem_filter.mpr ⟨hC, hc⟩⟩)
  rw [mem_filter] at hC₁
  obtain ⟨hC₁m, hC₁c⟩ := hC₁
  have hC₁' := (P.crossesOnLeft_iff R hC₁m hAm).mp hC₁c
  by_cases hlo : P.lo R C₁ < P.lo R B
  · exact ⟨C₁, hC₁m, hC₁c, (P.crossesOnLeft_iff R hC₁m hBm).mpr (by omega)⟩
  · push Not at hlo
    obtain ⟨D, hD, E, hE, hGD, hGE, hDE⟩ :=
      exists_boundary_crossing (𝒞 := 𝒞)
        (Good := fun D => P.lo R C₁ ≤ P.lo R D ∧ P.hi R D ≤ P.hi R A) ⟨le_rfl, by omega⟩ B
        (hcomp.conn C₁ hC₁m B hBm) (by omega)
    have hcr := (P.crossing_iff R hD hE).mp hDE
    rw [not_and_or, not_le, not_le] at hGE
    rcases hGE with hGE | hGE
    · -- `E` starts before `C₁`: crossed on the right by `D`, so open on the left; it contains
      -- `C₁` and crosses `A` on the left, earlier than `C₁`
      exfalso
      have hright : P.lo R E < P.lo R D ∧ P.lo R D ≤ P.hi R E ∧ P.hi R E < P.hi R D := by omega
      have hEo : P.OpenLeft E := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hE with h | h
        · exact h
        · exact absurd ((P.crossesOnRight_iff R hD hE).mpr hright) (h.2 D hD)
      have hC₁o : P.OpenLeft C₁ := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hC₁m with h | h
        · exact h
        · exact absurd ((P.crossesOnRight_iff R hAm hC₁m).mpr (by omega)) (h.2 A hAm)
      have hnc := P.not_crossing_of_openLeft hEo hC₁o
      rw [P.crossing_iff R hE hC₁m] at hnc
      have hEA : P.CrossesOnLeft E A := (P.crossesOnLeft_iff R hE hAm).mpr (by omega)
      have := hmin E (mem_filter.mpr ⟨hE, hEA⟩)
      omega
    · -- `E` ends after `A`: crossed on the left by `D`, so open on the right; it is a strict
      -- ancestor of `A`, hence contains `B`, and `C₁` crosses `B`
      have hleft : P.lo R D < P.lo R E ∧ P.lo R E ≤ P.hi R D ∧ P.hi R D < P.hi R E := by omega
      have hEo : P.OpenRight E := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hE with h | h
        · exact absurd ((P.crossesOnLeft_iff R hD hE).mpr hleft) (h.2 D hD)
        · exact h
      have hnc := P.not_crossing_of_openRight hEo hAo
      rw [P.crossing_iff R hE hAm] at hnc
      have hAE : A ⊆ E := by
        rw [P.subset_iff R hAm hE]
        omega
      have hanc : P.StrictAncR R A E := ⟨hAo, hEo, hAE, by omega⟩
      have hBE := (P.subset_iff R hBm hE).mp (hclosest E hanc)
      exact ⟨C₁, hC₁m, hC₁c, (P.crossesOnLeft_iff R hC₁m hBm).mpr (by omega)⟩

/-! ### The left hierarchy, by reflection -/

/-- `B` is a strict ancestor of `A` in the left hierarchy. -/
def StrictAncL (A B : Finset (Fin n)) : Prop :=
  P.OpenLeft A ∧ P.OpenLeft B ∧ A ⊆ B ∧ P.lo R B < P.lo R A

/-- `B` is the strict parent of `A` in the left hierarchy. -/
def StrictParentL (A B : Finset (Fin n)) : Prop :=
  P.StrictAncL R A B ∧ ∀ B', P.StrictAncL R A B' → B ⊆ B'

theorem strictAncL_iff {A B : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) :
    P.StrictAncL R A B ↔ P.reflect.StrictAncR R.reflect A B := by
  unfold StrictAncL StrictAncR
  rw [P.reflect_openRight R, P.reflect_openRight R, P.reflect_hi R hA, P.reflect_hi R hB]
  have := P.one_le_lo R hA
  have := P.one_le_lo R hB
  have := P.hi_lt R hA
  have := P.hi_lt R hB
  have := P.lo_lt_hi R hA
  have := P.lo_lt_hi R hB
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by omega⟩

theorem strictParentL_iff {A B : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) :
    P.StrictParentL R A B ↔ P.reflect.StrictParentR R.reflect A B := by
  unfold StrictParentL StrictParentR
  rw [P.strictAncL_iff R hA hB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun B' hB' => h2 B' ((P.strictAncL_iff R hA hB'.2.1.1).mpr hB')⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun B' hB' => h2 B' ((P.strictAncL_iff R hA hB'.2.1.1).mp hB')⟩

/-- **KKO21 Lemma 4.13**, left. -/
theorem common_ancestorL (R : P.Rooted) (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞) (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A B : Finset (Fin n)}
    (hA : P.OpenLeft A) (hB : P.OpenLeft B) (hd : Disjoint A B) :
    ∃ C, P.OpenLeft C ∧ A ⊆ C ∧ B ⊆ C := by
  obtain ⟨C, hC, h1, h2⟩ := P.reflect.common_ancestorR R.reflect hx hcomp hη0 hη
    ((P.reflect_openRight R).mpr hA) ((P.reflect_openRight R).mpr hB) hd
  exact ⟨C, (P.reflect_openRight R).mp hC, h1, h2⟩

/-- **KKO21 Lemma 4.14**, left: a cut open on the left not starting at the first atom has
a strict ancestor. -/
theorem exists_strictAncL (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {A : Finset (Fin n)} (hA : P.OpenLeft A)
    (hlt : 1 < P.lo R A) : ∃ B, P.StrictAncL R A B := by
  obtain ⟨B, hB⟩ := P.reflect.exists_strictAncR R.reflect hx hcomp hη0 hη
    ((P.reflect_openRight R).mpr hA) (by
      rw [P.reflect_hi R hA.1]
      change P.m - P.lo R A < P.m - 1
      have := P.hi_lt R hA.1
      have := P.lo_lt_hi R hA.1
      omega)
  exact ⟨B, (P.strictAncL_iff R hA.1 hB.2.1.1).mpr hB⟩

/-- A cut with a strict ancestor in the left hierarchy has a strict parent. -/
theorem exists_strictParentL (hcomp : IsOneSideComponent e₀ x η 𝒞) {A : Finset (Fin n)}
    (h : ∃ B, P.StrictAncL R A B) : ∃ B, P.StrictParentL R A B := by
  obtain ⟨B₀, hB₀⟩ := h
  obtain ⟨B, hB⟩ := P.reflect.exists_strictParentR R.reflect hcomp
    ⟨B₀, (P.strictAncL_iff R hB₀.1.1 hB₀.2.1.1).mp hB₀⟩
  exact ⟨B, (P.strictParentL_iff R hB.1.1.1 hB.1.2.1.1).mpr hB⟩

/-- **KKO21 Lemma 4.12**, left: a strict parent pair in the left hierarchy is crossed on
the right by a common member. -/
theorem exists_crossesOnRight_of_strictParentL (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞) (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    {A B : Finset (Fin n)} (hAB : P.StrictParentL R A B) :
    ∃ C ∈ 𝒞, P.CrossesOnRight C A ∧ P.CrossesOnRight C B := by
  have hA := hAB.1.1.1
  have hB := hAB.1.2.1.1
  obtain ⟨C, hC, h1, h2⟩ := P.reflect.exists_crossesOnLeft_of_strictParentR R.reflect hx hcomp
    hη0 hη ((P.strictParentL_iff R hA hB).mp hAB)
  exact ⟨C, hC, (P.reflect_crossesOnLeft R hC hA).mp h1, (P.reflect_crossesOnLeft R hC hB).mp h2⟩

end PolygonRep

end TSPGap

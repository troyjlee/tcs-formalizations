/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OneSideStructure

/-!
# Uncrossed cuts, other components, and the atoms of a one-side polygon

The laminarity facts behind KKO22 Fact B.4 (the hierarchy of Theorem B.3), for a component
`𝒞` of `N_{η,≤1}` with rooted polygon `P`:

* `members_subset_of_not_crossing` — **propagation**: a rooted cut crossing no member and
  containing one member contains every member (walk the crossing paths), hence the whole
  outer cut `compl_rootAtom_subset`;
* `atom_laminar_of_not_crossing` — a rooted cut crossing no member is laminar with every
  non-root atom: it cannot split one, since the members containing that atom would then all
  contain the cut, and a member separating the atom from another one the cut meets could
  not;
* `subset_atom_of_ssubset_outer` — a rooted cut crossing no member and properly inside the
  outer cut lies inside a single non-root atom;
* the **covering pair** of two distinct components (KKO22 Theorem 4.5,
  `exists_atomOf_union_atomOf_eq_univ`): `exists_cover_pair`, and its consequences — the
  non-root atoms of two components are laminar (`atoms_laminar_of_ne`), an outer cut is
  laminar with the other component's non-root atoms (`atom_outer_laminar_of_ne`), two outer
  cuts are laminar and, when one is properly inside the other, it lies inside a single
  non-root atom (`outer_laminar_of_ne`), a non-root atom properly inside the other
  component's outer cut lies inside a single non-root atom of it
  (`subset_atom_of_atom_ssubset_outer`), no outer cut lies inside an atom
  (`not_compl_rootAtom_subset_atom`), and distinct components have distinct outer cuts
  (`outer_injective_of_ne`).
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

namespace PolygonRep

variable (P : PolygonRep 𝒞) (R : P.Rooted)

/-! ### Propagation along the crossing graph -/

/-- A rooted cut crossing no member and containing one member contains every member. -/
theorem members_subset_of_not_crossing (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {S : Finset (Fin n)} (hS : AvoidsRootEdge e₀ S) (hnc : ∀ T ∈ 𝒞, ¬ Crossing S T)
    {T₀ : Finset (Fin n)} (hT₀ : T₀ ∈ 𝒞) (hsub : T₀ ⊆ S) :
    ∀ T ∈ 𝒞, T ⊆ S := by
  have key : ∀ T,
      Relation.ReflTransGen (fun A B => A ∈ 𝒞 ∧ B ∈ 𝒞 ∧ Crossing A B) T₀ T →
      T ⊆ S := by
    intro T hpath
    induction hpath with
    | refl => exact hsub
    | @tail b c _ hbc ih =>
      rcases nested_or_disjoint_of_not_crossing (hcomp.avoids _ hbc.2.1) hS
        (fun h => hnc _ hbc.2.1 h.symm) with h | h | h
      · exact h
      · exfalso
        obtain ⟨v, hv⟩ := hbc.2.2.2.1
        rw [mem_sdiff] at hv
        exact hv.2 (h (ih hv.1))
      · exfalso
        obtain ⟨v, hv⟩ := hbc.2.2.1
        rw [mem_inter] at hv
        exact disjoint_left.mp h hv.2 (ih hv.1)
  exact fun T hT => key T (hcomp.conn T₀ hT₀ T hT)

/-- Every vertex outside the root atom lies in a member. -/
theorem exists_mem_of_notMem_root (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {v : Fin n}
    (hv : v ∉ P.rootAtom) : ∃ T ∈ 𝒞, v ∈ T := by
  have hm := P.hm
  have hpos : P.pos R (P.idx R v) ≠ 0 := by
    intro h0
    have hidx := (P.pos_eq_zero_iff R).mp h0
    have hmem := P.mem_out_idx R v
    rw [hidx, R.hr] at hmem
    exact hv hmem
  have hlt := P.pos_lt R (P.idx R v)
  obtain ⟨T, hT, h1, h2⟩ := P.exists_mem_of_pos R hcomp (t := P.pos R (P.idx R v))
    (by omega) (by omega)
  exact ⟨T, hT, (P.mem_iff_pos R hT v).mpr ⟨h1, h2⟩⟩

/-- A rooted cut crossing no member and containing one member contains the outer cut. -/
theorem compl_rootAtom_subset (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {S : Finset (Fin n)}
    (hS : AvoidsRootEdge e₀ S) (hnc : ∀ T ∈ 𝒞, ¬ Crossing S T) {T₀ : Finset (Fin n)}
    (hT₀ : T₀ ∈ 𝒞) (hsub : T₀ ⊆ S) : P.rootAtomᶜ ⊆ S := by
  intro v hv
  obtain ⟨T, hT, hvT⟩ := P.exists_mem_of_notMem_root R hcomp (mem_compl.mp hv)
  exact members_subset_of_not_crossing hcomp hS hnc hT₀ hsub T hT hvT

/-! ### Uncrossed cuts do not split atoms -/

/-- A rooted cut crossing no member is laminar with every non-root atom. -/
theorem atom_laminar_of_not_crossing (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {S : Finset (Fin n)} (hS : AvoidsRootEdge e₀ S) (hnc : ∀ T ∈ 𝒞, ¬ Crossing S T)
    {a : Finset (Fin n)} (ha : a ∈ atoms 𝒞) (har : a ≠ P.rootAtom) :
    S ⊆ a ∨ a ⊆ S ∨ Disjoint S a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, huS, hua⟩ := not_disjoint_iff.mp hcon.2.2
  obtain ⟨w, hwa, hwS⟩ := not_subset.mp hcon.2.1
  obtain ⟨z, hzS, hza⟩ := not_subset.mp hcon.1
  -- the atom `a` is `out i` for the index of `u`; it is not the root's
  have hai : a = P.out (P.idx R u) := by
    by_contra hne
    exact disjoint_left.mp (atoms_disjoint ha (P.out_atom _) hne) hua (P.mem_out_idx R u)
  have hur : P.idx R u ≠ R.r := fun h => har (by rw [hai, h, R.hr])
  -- a member containing `a` cannot lie inside `S` (propagation would put `a` in `S`), so it
  -- contains `S`
  have hcont : ∀ T ∈ 𝒞, a ⊆ T → S ⊆ T := by
    intro T hT haT
    rcases nested_or_disjoint_of_not_crossing hS (hcomp.avoids T hT) (hnc T hT) with h | h | h
    · exact h
    · exfalso
      exact hwS (P.compl_rootAtom_subset R hcomp hS hnc hT h
        (mem_compl.mpr fun hw => disjoint_left.mp
          (atoms_disjoint ha P.rootAtom_mem har) hwa hw))
    · exact absurd (haT hua) (disjoint_left.mp h huS)
  -- `z` lies outside `a`; its atom is separated from `a` by a member
  have hpz : P.pos R (P.idx R z) ≠ P.pos R (P.idx R u) := by
    intro h
    have := (P.pos_eq_iff R).mp h
    exact hza (by rw [hai, ← this]; exact P.mem_out_idx R z)
  obtain ⟨T, hT, hsep⟩ := P.exists_separating R hpz
  have haT : a ⊆ T ∨ Disjoint a T := atom_subset_or_disjoint ha hT
  by_cases hzT : z ∈ T
  · -- `T` contains `z` but not `u`: `T` lies inside `S` or contains it; both fail
    have huT : u ∉ T := fun h => hsep ⟨fun _ => h, fun _ => hzT⟩
    rcases nested_or_disjoint_of_not_crossing hS (hcomp.avoids T hT) (hnc T hT) with h | h | h
    · exact huT (h huS)
    · exact hwS (P.compl_rootAtom_subset R hcomp hS hnc hT h
        (mem_compl.mpr fun hw => disjoint_left.mp
          (atoms_disjoint ha P.rootAtom_mem har) hwa hw))
    · exact disjoint_left.mp h hzS hzT
  · -- `T` contains `u`, hence `a`, hence `S ∋ z`
    have huT : u ∈ T := by
      by_contra h
      exact hsep ⟨fun h' => absurd h' hzT, fun h' => absurd h' h⟩
    have haT' : a ⊆ T := haT.resolve_right fun h => disjoint_left.mp h hua huT
    exact hzT (hcont T hT haT' hzS)

/-- A rooted cut crossing no member, properly inside the outer cut, lies inside a single
non-root atom. -/
theorem subset_atom_of_ssubset_outer (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {S : Finset (Fin n)} (hS : AvoidsRootEdge e₀ S) (hnc : ∀ T ∈ 𝒞, ¬ Crossing S T)
    (hne : S.Nonempty) (hsub : S ⊆ P.rootAtomᶜ) (hproper : S ≠ P.rootAtomᶜ) :
    ∃ a ∈ atoms 𝒞, a ≠ P.rootAtom ∧ S ⊆ a := by
  obtain ⟨u, hu⟩ := hne
  have haat : P.out (P.idx R u) ∈ atoms 𝒞 := P.out_atom _
  have hua : u ∈ P.out (P.idx R u) := P.mem_out_idx R u
  have har : P.out (P.idx R u) ≠ P.rootAtom := by
    intro h
    rw [h] at hua
    exact (mem_compl.mp (hsub hu)) hua
  refine ⟨P.out (P.idx R u), haat, har, ?_⟩
  -- no member lies inside `S`
  have hnoin : ∀ T ∈ 𝒞, ¬ T ⊆ S := by
    intro T hT hTS
    exact hproper (subset_antisymm hsub (P.compl_rootAtom_subset R hcomp hS hnc hT hTS))
  rcases P.atom_laminar_of_not_crossing R hcomp hS hnc haat har with h1 | h2 | h3
  · exact h1
  · -- `a ⊆ S`: another atom of `S` would be separated from `a` by a member inside `S`
    by_contra hSa
    obtain ⟨z, hzS, hza⟩ := not_subset.mp hSa
    have hpz : P.pos R (P.idx R z) ≠ P.pos R (P.idx R u) := by
      intro h'
      have := (P.pos_eq_iff R).mp h'
      exact hza (by rw [← this]; exact P.mem_out_idx R z)
    obtain ⟨T, hT, hsep⟩ := P.exists_separating R hpz
    have hTS : T ⊆ S ∨ S ⊆ T := by
      rcases nested_or_disjoint_of_not_crossing hS (hcomp.avoids T hT) (hnc T hT)
        with h' | h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
      · exfalso
        by_cases hzT : z ∈ T
        · exact disjoint_left.mp h' hzS hzT
        · have huT : u ∈ T := by
            by_contra h''
            exact hsep ⟨fun h1 => absurd h1 hzT, fun h1 => absurd h1 h''⟩
          exact disjoint_left.mp h' hu huT
    rcases hTS with hTS | hTS
    · exact hnoin T hT hTS
    · exact hsep ⟨fun _ => hTS hu, fun _ => hTS hzS⟩
  · exact absurd hua (disjoint_left.mp h3 hu)

end PolygonRep

/-! ### Two components -/

section TwoComponents

variable {𝒞₁ 𝒞₂ : Finset (Finset (Fin n))}

/-- **The covering pair** (KKO22 Theorem 4.5): two distinct components of `N_{η,≤1}` have
an atom apiece covering `V`. -/
theorem exists_cover_pair (h₁ : IsOneSideComponent e₀ x η 𝒞₁)
    (h₂ : IsOneSideComponent e₀ x η 𝒞₂) (hne : 𝒞₁ ≠ 𝒞₂) :
    ∃ p q, atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q = univ :=
  exists_atomOf_union_atomOf_eq_univ h₁.nonempty h₂.nonempty h₁.conn h₂.conn
    (fun C hC => ⟨(h₁.nearMin C hC).nonempty, (h₁.nearMin C hC).ne_univ⟩)
    (fun _ hC _ hD => IsOneSideComponent.not_crossing_of_ne h₁ h₂ hne hC hD)

/-- An atom other than one of a covering pair lies inside the other. -/
theorem atom_subset_of_cover {p q : Fin n} (hcov : atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q = univ)
    {a : Finset (Fin n)} (ha : a ∈ atoms 𝒞₁) (hne : a ≠ atomOf 𝒞₁ p) :
    a ⊆ atomOf 𝒞₂ q := by
  intro v hv
  have hd := atoms_disjoint ha (mem_atoms.mpr ⟨p, rfl⟩) hne
  have : v ∈ atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q := hcov ▸ mem_univ v
  rcases mem_union.mp this with h | h
  · exact absurd h (disjoint_left.mp hd hv)
  · exact h

/-- The root atom of a component: the atom of `u₀`. -/
theorem mem_root_of_cover {p q : Fin n} (hcov : atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q = univ) :
    atomOf 𝒞₁ p = atomOf 𝒞₁ e₀.u₀ ∨
      atomOf 𝒞₂ q = atomOf 𝒞₂ e₀.u₀ := by
  have : e₀.u₀ ∈ atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q := hcov ▸ mem_univ _
  rcases mem_union.mp this with h | h
  · exact Or.inl (atomOf_eq_of_mem h).symm
  · exact Or.inr (atomOf_eq_of_mem h).symm

/-- The non-root atoms of two distinct components are laminar. -/
theorem atoms_laminar_of_ne (h₁ : IsOneSideComponent e₀ x η 𝒞₁)
    (h₂ : IsOneSideComponent e₀ x η 𝒞₂) (hne : 𝒞₁ ≠ 𝒞₂) {a b : Finset (Fin n)}
    (ha : a ∈ atoms 𝒞₁) (har : a ≠ atomOf 𝒞₁ e₀.u₀) (hb : b ∈ atoms 𝒞₂)
    (hbr : b ≠ atomOf 𝒞₂ e₀.u₀) : a ⊆ b ∨ b ⊆ a ∨ Disjoint a b := by
  obtain ⟨p, q, hcov⟩ := exists_cover_pair h₁ h₂ hne
  have hcov' : atomOf 𝒞₂ q ∪ atomOf 𝒞₁ p = univ := by rw [union_comm]; exact hcov
  by_cases hap : a = atomOf 𝒞₁ p
  · -- `a` is the covering atom of `𝒞₁`, so the covering atom of `𝒞₂` is its root
    rcases mem_root_of_cover hcov with h | h
    · exact absurd (hap.trans h) har
    · have hbq : b ≠ atomOf 𝒞₂ q := fun e => hbr (e.trans h)
      exact Or.inr (Or.inl (by rw [hap]; exact atom_subset_of_cover hcov' hb hbq))
  · have haq : a ⊆ atomOf 𝒞₂ q := atom_subset_of_cover hcov ha hap
    by_cases hbq : b = atomOf 𝒞₂ q
    · exact Or.inl (by rw [hbq]; exact haq)
    · have hbp : b ⊆ atomOf 𝒞₁ p := atom_subset_of_cover hcov' hb hbq
      refine Or.inr (Or.inr (disjoint_left.mpr fun v hva hvb => ?_))
      exact disjoint_left.mp (atoms_disjoint ha (mem_atoms.mpr ⟨p, rfl⟩) hap) hva (hbp hvb)

/-- Membership in the outer cut of a component, the complement of its root atom. -/
theorem mem_outer_iff (𝒞 : Finset (Finset (Fin n))) (v : Fin n) :
    v ∈ (atomOf 𝒞 e₀.u₀)ᶜ ↔ atomOf 𝒞 v ≠ atomOf 𝒞 e₀.u₀ := by
  rw [mem_compl]
  constructor
  · intro h e
    exact h (e ▸ mem_atomOf_self 𝒞 v)
  · intro h hv
    exact h (atomOf_eq_of_mem hv)

/-- A non-root atom of `𝒞₁` and the outer cut of `𝒞₂` are laminar. -/
theorem atom_outer_laminar_of_ne (h₁ : IsOneSideComponent e₀ x η 𝒞₁)
    (h₂ : IsOneSideComponent e₀ x η 𝒞₂) (hne : 𝒞₁ ≠ 𝒞₂) {a : Finset (Fin n)}
    (ha : a ∈ atoms 𝒞₁) (har : a ≠ atomOf 𝒞₁ e₀.u₀) :
    a ⊆ (atomOf 𝒞₂ e₀.u₀)ᶜ ∨ (atomOf 𝒞₂ e₀.u₀)ᶜ ⊆ a ∨
      Disjoint a (atomOf 𝒞₂ e₀.u₀)ᶜ := by
  obtain ⟨p, q, hcov⟩ := exists_cover_pair h₁ h₂ hne
  have hcov' : atomOf 𝒞₂ q ∪ atomOf 𝒞₁ p = univ := by rw [union_comm]; exact hcov
  by_cases hap : a = atomOf 𝒞₁ p
  · rcases mem_root_of_cover hcov with h | h
    · exact absurd (hap.trans h) har
    · -- every non-root atom of `𝒞₂` lies inside `a`
      refine Or.inr (Or.inl fun v hv => ?_)
      have hv' := (mem_outer_iff 𝒞₂ v).mp hv
      have hvq : atomOf 𝒞₂ v ≠ atomOf 𝒞₂ q := fun e => hv' (e.trans h)
      rw [hap]
      exact atom_subset_of_cover hcov' (mem_atoms.mpr ⟨v, rfl⟩) hvq (mem_atomOf_self _ _)
  · have haq : a ⊆ atomOf 𝒞₂ q := atom_subset_of_cover hcov ha hap
    by_cases hqr : atomOf 𝒞₂ q = atomOf 𝒞₂ e₀.u₀
    · exact Or.inr (Or.inr (disjoint_left.mpr fun v hva hv =>
        (mem_compl.mp hv) (by rw [← hqr]; exact haq hva)))
    · exact Or.inl fun v hva => mem_compl.mpr fun hv =>
        disjoint_left.mp
          (atoms_disjoint (mem_atoms.mpr ⟨q, rfl⟩) (mem_atoms.mpr ⟨_, rfl⟩) hqr)
          (haq hva) hv

/-- The outer cuts of two distinct components are laminar; when one lies inside the other,
it lies inside a single non-root atom of the other. -/
theorem outer_laminar_of_ne (h₁ : IsOneSideComponent e₀ x η 𝒞₁)
    (h₂ : IsOneSideComponent e₀ x η 𝒞₂) (hne : 𝒞₁ ≠ 𝒞₂) :
    Disjoint (atomOf 𝒞₁ e₀.u₀)ᶜ (atomOf 𝒞₂ e₀.u₀)ᶜ ∨
      (∃ b ∈ atoms 𝒞₂,
        b ≠ atomOf 𝒞₂ e₀.u₀ ∧ (atomOf 𝒞₁ e₀.u₀)ᶜ ⊆ b) ∨
      (∃ a ∈ atoms 𝒞₁,
        a ≠ atomOf 𝒞₁ e₀.u₀ ∧ (atomOf 𝒞₂ e₀.u₀)ᶜ ⊆ a) := by
  obtain ⟨p, q, hcov⟩ := exists_cover_pair h₁ h₂ hne
  have hcov' : atomOf 𝒞₂ q ∪ atomOf 𝒞₁ p = univ := by rw [union_comm]; exact hcov
  by_cases hp : atomOf 𝒞₁ p = atomOf 𝒞₁ e₀.u₀ <;>
    by_cases hq : atomOf 𝒞₂ q = atomOf 𝒞₂ e₀.u₀
  · -- both covering atoms are roots: the outer cuts are disjoint
    left
    rw [disjoint_left]
    intro v h1 h2
    have : v ∈ atomOf 𝒞₁ p ∪ atomOf 𝒞₂ q := hcov ▸ mem_univ v
    rcases mem_union.mp this with h | h
    · exact (mem_compl.mp h1) (hp ▸ h)
    · exact (mem_compl.mp h2) (hq ▸ h)
  · -- the outer cut of `𝒞₁` lies inside the covering atom of `𝒞₂`
    right; left
    refine ⟨atomOf 𝒞₂ q, mem_atoms.mpr ⟨q, rfl⟩, hq, fun v hv => ?_⟩
    have hv' := (mem_outer_iff 𝒞₁ v).mp hv
    have hvp : atomOf 𝒞₁ v ≠ atomOf 𝒞₁ p := fun e => hv' (e.trans hp)
    exact atom_subset_of_cover hcov (mem_atoms.mpr ⟨v, rfl⟩) hvp (mem_atomOf_self _ _)
  · right; right
    refine ⟨atomOf 𝒞₁ p, mem_atoms.mpr ⟨p, rfl⟩, hp, fun v hv => ?_⟩
    have hv' := (mem_outer_iff 𝒞₂ v).mp hv
    have hvq : atomOf 𝒞₂ v ≠ atomOf 𝒞₂ q := fun e => hv' (e.trans hq)
    exact atom_subset_of_cover hcov' (mem_atoms.mpr ⟨v, rfl⟩) hvq (mem_atomOf_self _ _)
  · exfalso
    rcases mem_root_of_cover hcov with h | h
    · exact hp h
    · exact hq h

/-- The outer cut of a nontrivial component lies inside no atom: a member inside an atom
would be that atom, and a single atom is crossed by nothing. -/
theorem not_compl_rootAtom_subset_atom (h : IsOneSideComponent e₀ x η 𝒞₁)
    (hcard : 2 ≤ 𝒞₁.card) {b : Finset (Fin n)} (hb : b ∈ atoms 𝒞₁)
    (hsub : (atomOf 𝒞₁ e₀.u₀)ᶜ ⊆ b) : False := by
  obtain ⟨T, hT⟩ := h.nonempty
  obtain ⟨T', hT', hc⟩ := BG.exists_cross hcard h.conn hT
  -- `T ⊆ b`: it avoids the root atom
  have hTb : T ⊆ b := fun v hv =>
    hsub (mem_compl.mpr fun hr => (h.avoids T hT).1 ((mem_atomOf.mp hr T hT).mpr hv))
  -- `T` is a nonempty union of atoms inside the atom `b`: `T = b`, a single atom
  have hbT : b ⊆ T := by
    obtain ⟨v, hv⟩ := (h.nearMin T hT).nonempty
    exact (atom_subset_or_disjoint hb hT).resolve_right fun hd =>
      disjoint_left.mp hd (hTb hv) hv
  have hTeq : T = b := subset_antisymm hTb hbT
  -- a single atom is not crossed
  obtain ⟨v, hv⟩ := hc.1
  rw [mem_inter] at hv
  have : T ⊆ T' := by
    rw [hTeq] at hv ⊢
    exact (atom_subset_or_disjoint hb hT').resolve_right fun hd =>
      disjoint_left.mp hd hv.1 hv.2
  obtain ⟨w, hw⟩ := hc.2.1
  rw [mem_sdiff] at hw
  exact hw.2 (this hw.1)

/-- A non-root atom of `𝒞₂` properly inside the outer cut of `𝒞₁` lies inside a single
non-root atom of `𝒞₁`. -/
theorem subset_atom_of_atom_ssubset_outer (h₁ : IsOneSideComponent e₀ x η 𝒞₁)
    (h₂ : IsOneSideComponent e₀ x η 𝒞₂) (hne : 𝒞₁ ≠ 𝒞₂) {b : Finset (Fin n)}
    (hb : b ∈ atoms 𝒞₂) (hbr : b ≠ atomOf 𝒞₂ e₀.u₀)
    (hsub : b ⊆ (atomOf 𝒞₁ e₀.u₀)ᶜ)
    (hne' : b ≠ (atomOf 𝒞₁ e₀.u₀)ᶜ) :
    ∃ a ∈ atoms 𝒞₁, a ≠ atomOf 𝒞₁ e₀.u₀ ∧ b ⊆ a := by
  obtain ⟨p, q, hcov⟩ := exists_cover_pair h₁ h₂ hne
  have hcov' : atomOf 𝒞₂ q ∪ atomOf 𝒞₁ p = univ := by rw [union_comm]; exact hcov
  obtain ⟨v, hv⟩ : b.Nonempty := by
    obtain ⟨u, rfl⟩ := mem_atoms.mp hb
    exact atomOf_nonempty _ _
  by_cases hbq : b = atomOf 𝒞₂ q
  · -- `b` is the covering atom of `𝒞₂`, so the covering atom of `𝒞₁` is its root and the
    -- outer cut of `𝒞₁` lies inside `b`
    exfalso
    rcases mem_root_of_cover hcov with h | h
    · refine hne' (subset_antisymm hsub fun w hw => ?_)
      have hw' := (mem_outer_iff 𝒞₁ w).mp hw
      have hwp : atomOf 𝒞₁ w ≠ atomOf 𝒞₁ p := fun e => hw' (e.trans h)
      rw [hbq]
      exact atom_subset_of_cover hcov (mem_atoms.mpr ⟨w, rfl⟩) hwp (mem_atomOf_self _ _)
    · exact hbr (hbq.trans h)
  · refine ⟨atomOf 𝒞₁ p, mem_atoms.mpr ⟨p, rfl⟩, fun hp => ?_,
      atom_subset_of_cover hcov' hb hbq⟩
    exact (mem_compl.mp (hsub hv)) (hp ▸ atom_subset_of_cover hcov' hb hbq hv)

/-- Distinct nontrivial components have distinct outer cuts. -/
theorem outer_injective_of_ne (h₁ : IsOneSideComponent e₀ x η 𝒞₁)
    (h₂ : IsOneSideComponent e₀ x η 𝒞₂) (hne : 𝒞₁ ≠ 𝒞₂)
    (hc₁ : 2 ≤ 𝒞₁.card) (hc₂ : 2 ≤ 𝒞₂.card) :
    (atomOf 𝒞₁ e₀.u₀)ᶜ ≠ (atomOf 𝒞₂ e₀.u₀)ᶜ := by
  intro heq
  rcases outer_laminar_of_ne h₁ h₂ hne with h | ⟨b, hb, -, hsub⟩ | ⟨a, ha, -, hsub⟩
  · -- disjoint and equal: the outer cut is empty, but it contains a member
    obtain ⟨T, hT⟩ := h₁.nonempty
    obtain ⟨v, hv⟩ := (h₁.nearMin T hT).nonempty
    have hvO : v ∈ (atomOf 𝒞₁ e₀.u₀)ᶜ := mem_compl.mpr fun hr =>
      (h₁.avoids T hT).1 ((mem_atomOf.mp hr T hT).mpr hv)
    exact disjoint_left.mp h hvO (by rw [← heq]; exact hvO)
  · exact not_compl_rootAtom_subset_atom h₂ hc₂ hb (heq ▸ hsub)
  · exact not_compl_rootAtom_subset_atom h₁ hc₁ ha (heq.symm ▸ hsub)

end TwoComponents

end TSPGap

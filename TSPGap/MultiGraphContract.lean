/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MultiGraphWalks

/-!
# Contraction of a vertex set, and the contraction inequality

`contract G U` identifies the vertices of `U` to a single new vertex `none`, keeps every edge
with an end outside `U` under its own label (`{e // OutU G U e}`), and drops the edges inside
`U`.  Edge sets of the contraction lift to `G` by forgetting the subtype (`lift`), edge sets
of `G` restrict by filtering (`restrict`); degrees at vertices outside `U` are unchanged,
and the degree at `none` is the number of lifted edges crossing `U`
(`deg_none_eq_card_inter_cut`).

The **terminal set** transforms by `cterm`: the terminals outside `U`, plus `none` exactly
when `|U ∩ T|` is odd; a `T`-join restricts to a `cterm T`-join (`isJoin_restrict`).

For the **star** `U = {u} ∪ N(u)` in a graph where no edge joins two neighbours of `u`
(`NoNbrEdge`, automatic in a bipartite graph), joins **lift back**: a `cterm T`-join `K*`
becomes the `T`-join `lift K* ∪ A`, `A` being one star edge to each neighbour whose parity
needs fixing, with `deg u = |A|` (`exists_lift_join`).

The **contraction inequality** (`card_restrict_le`): if `J` is a minimum `T`-join with a
single edge `ux` at `u`, and `wt J D ≥ deg_D u − 2·[ux ∈ D]` for every even `D` (the
inequality (♠) of `OJOIN_DESIGN.md`), then every `cterm T`-join of the contraction has at
least `|J| − 1 = |restrict J|` edges.  (♠) itself follows from the cycle bound (★) — every
cycle at `u` avoiding `ux` has weight at least `2` — by peeling cycles at `u`
(`sharp_of_cycles`).
-/

namespace TSPGap
namespace MGraph

open Finset
open Classical
open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E] (G : MGraph V E)

/-! ### The contraction -/

/-- An edge with an end outside `U`. -/
def OutU (U : Finset V) (e : E) : Prop := ¬ ∀ a ∈ G.ends e, a ∈ U

/-- The vertex map of the contraction. -/
noncomputable def cvert (U : Finset V) (v : V) : Option {v // v ∉ U} :=
  if h : v ∈ U then none else some ⟨v, h⟩

theorem cvert_of_mem {U : Finset V} {v : V} (h : v ∈ U) : cvert U v = none := by
  simp [cvert, h]

theorem cvert_of_notMem {U : Finset V} {v : V} (h : v ∉ U) : cvert U v = some ⟨v, h⟩ := by
  simp [cvert, h]

theorem cvert_eq_some_iff {U : Finset V} {v : V} {w : {v // v ∉ U}} :
    cvert U v = some w ↔ v = w.1 := by
  by_cases h : v ∈ U
  · rw [cvert_of_mem h]
    constructor
    · intro h'; exact absurd h' (by simp)
    · intro h'; exact absurd (h' ▸ h) w.2
  · rw [cvert_of_notMem h]
    constructor
    · intro h'
      have := Option.some_injective _ h'
      rw [← this]
    · intro h'
      exact congrArg some (Subtype.ext h')

theorem cvert_eq_none_iff {U : Finset V} {v : V} : cvert U v = none ↔ v ∈ U := by
  by_cases h : v ∈ U
  · simp [cvert_of_mem h, h]
  · simp [cvert_of_notMem h, h]

/-- **The contraction** of `U` to the single vertex `none`. -/
noncomputable def contract (U : Finset V) : MGraph (Option {v // v ∉ U}) {e // G.OutU U e} where
  ends e := (G.ends e.1).map (cvert U)
  loopless := by
    rintro ⟨e, he⟩ hd
    have hl := G.loopless e
    obtain ⟨a, b, hab⟩ : ∃ a b, G.ends e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) (G.ends e)
    unfold OutU at he
    rw [hab] at he hl
    change ((G.ends e).map (cvert U)).IsDiag at hd
    rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff] at hd
    rw [Sym2.mk_isDiag_iff] at hl
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, not_and] at he
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
    · exact he ha hb
    · rw [cvert_of_mem ha, cvert_of_notMem hb] at hd; simp at hd
    · rw [cvert_of_notMem ha, cvert_of_mem hb] at hd; simp at hd
    · rw [cvert_of_notMem ha, cvert_of_notMem hb] at hd
      exact hl (Subtype.ext_iff.mp (Option.some_injective _ hd))

variable (U : Finset V)

/-- Forgetting the subtype: an edge set of the contraction as an edge set of `G`. -/
noncomputable def lift (D : Finset {e // G.OutU U e}) : Finset E :=
  D.map (Function.Embedding.subtype _)

/-- Restricting to the edges with an end outside `U`. -/
noncomputable def restrict (D : Finset E) : Finset {e // G.OutU U e} :=
  D.subtype (G.OutU U)

theorem mem_lift {D : Finset {e // G.OutU U e}} {e : E} :
    e ∈ G.lift U D ↔ ∃ h : G.OutU U e, ⟨e, h⟩ ∈ D := by
  simp only [lift, mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨⟨f, hf⟩, hfD, rfl⟩
    exact ⟨hf, hfD⟩
  · rintro ⟨h, hD⟩
    exact ⟨⟨e, h⟩, hD, rfl⟩

theorem mem_lift' {D : Finset {e // G.OutU U e}} {e : {e // G.OutU U e}} :
    e.1 ∈ G.lift U D ↔ e ∈ D := by
  rw [mem_lift]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨e.2, h⟩⟩

theorem mem_restrict {D : Finset E} {e : {e // G.OutU U e}} :
    e ∈ G.restrict U D ↔ e.1 ∈ D := by
  simp [restrict, mem_subtype]

theorem outU_of_mem_lift {D : Finset {e // G.OutU U e}} {e : E} (h : e ∈ G.lift U D) :
    G.OutU U e := ((G.mem_lift U).mp h).choose

theorem lift_restrict (D : Finset E) : G.lift U (G.restrict U D) = D.filter (G.OutU U) := by
  ext e
  rw [mem_lift, mem_filter]
  constructor
  · rintro ⟨h, hD⟩
    exact ⟨(G.mem_restrict U).mp hD, h⟩
  · rintro ⟨hD, h⟩
    exact ⟨h, (G.mem_restrict U).mpr hD⟩

theorem card_lift (D : Finset {e // G.OutU U e}) : (G.lift U D).card = D.card := card_map _

theorem inside_eq_filter_not_outU (D : Finset E) :
    G.inside U D = D.filter fun e => ¬ G.OutU U e := by
  ext e
  simp [inside, OutU]

theorem card_restrict (D : Finset E) :
    (G.restrict U D).card + (G.inside U D).card = D.card := by
  rw [restrict, card_subtype, inside_eq_filter_not_outU, filter_card_add_filter_neg_card_eq_card]

theorem lift_union (D D' : Finset {e // G.OutU U e}) :
    G.lift U (D ∪ D') = G.lift U D ∪ G.lift U D' := map_union _ _

theorem lift_symmDiff (D D' : Finset {e // G.OutU U e}) :
    G.lift U (D ∆ D') = G.lift U D ∆ G.lift U D' := by
  ext e
  rw [mem_lift, mem_symmDiff, mem_lift, mem_lift]
  constructor
  · rintro ⟨h, hD⟩
    rcases mem_symmDiff.mp hD with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨h, h1⟩, fun ⟨h', hh⟩ => h2 hh⟩
    · exact Or.inr ⟨⟨h, h1⟩, fun ⟨h', hh⟩ => h2 hh⟩
  · rintro (⟨⟨h, h1⟩, h2⟩ | ⟨⟨h, h1⟩, h2⟩)
    · exact ⟨h, mem_symmDiff.mpr (Or.inl ⟨h1, fun hh => h2 ⟨h, hh⟩⟩)⟩
    · exact ⟨h, mem_symmDiff.mpr (Or.inr ⟨h1, fun hh => h2 ⟨h, hh⟩⟩)⟩

/-! ### Degrees under contraction -/

theorem mem_ends_contract {e : {e // G.OutU U e}} {v : V} (hv : v ∉ U) :
    (some ⟨v, hv⟩ : Option {v // v ∉ U}) ∈ (G.contract U).ends e ↔ v ∈ G.ends e.1 := by
  change some ⟨v, hv⟩ ∈ (G.ends e.1).map (cvert U) ↔ _
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨a, ha, hav⟩
    rw [cvert_eq_some_iff] at hav
    rw [hav] at ha
    exact ha
  · intro h
    exact ⟨v, h, cvert_of_notMem hv⟩

theorem none_mem_ends_contract {e : {e // G.OutU U e}} :
    (none : Option {v // v ∉ U}) ∈ (G.contract U).ends e ↔ ∃ a ∈ G.ends e.1, a ∈ U := by
  change none ∈ (G.ends e.1).map (cvert U) ↔ _
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨a, ha, han⟩
    exact ⟨a, ha, cvert_eq_none_iff.mp han⟩
  · rintro ⟨a, ha, haU⟩
    exact ⟨a, ha, cvert_of_mem haU⟩

/-- Degrees outside `U` are unchanged. -/
theorem deg_contract_some (D : Finset {e // G.OutU U e}) {v : V} (hv : v ∉ U) :
    (G.contract U).deg D (some ⟨v, hv⟩) = G.deg (G.lift U D) v := by
  unfold deg
  rw [inc, inc]
  have : (G.lift U D).filter (fun e => v ∈ G.ends e) =
      (D.filter fun e => some ⟨v, hv⟩ ∈ (G.contract U).ends e).map
        (Function.Embedding.subtype _) := by
    ext e
    simp only [mem_filter, mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hD, hv'⟩
      obtain ⟨h, hD'⟩ := (G.mem_lift U).mp hD
      exact ⟨⟨e, h⟩, ⟨hD', (G.mem_ends_contract U hv).mpr hv'⟩, rfl⟩
    · rintro ⟨⟨f, hf⟩, ⟨hD, hv'⟩, rfl⟩
      exact ⟨(G.mem_lift U).mpr ⟨hf, hD⟩, (G.mem_ends_contract U hv).mp hv'⟩
  rw [this, card_map]
  congr

/-- The degree at the contracted vertex counts the lifted edges crossing `U`. -/
theorem deg_contract_none (D : Finset {e // G.OutU U e}) :
    (G.contract U).deg D none = (G.lift U D ∩ G.cut U).card := by
  unfold deg
  rw [inc]
  have : G.lift U D ∩ G.cut U =
      (D.filter fun e => (none : Option {v // v ∉ U}) ∈ (G.contract U).ends e).map
        (Function.Embedding.subtype _) := by
    ext e
    simp only [mem_inter, mem_map, mem_filter, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hD, hc⟩
      obtain ⟨h, hD'⟩ := (G.mem_lift U).mp hD
      refine ⟨⟨e, h⟩, ⟨hD', ?_⟩, rfl⟩
      rw [none_mem_ends_contract]
      exact (G.mem_cut.mp hc).1
    · rintro ⟨⟨f, hf⟩, ⟨hD, hn⟩, rfl⟩
      refine ⟨(G.mem_lift U).mpr ⟨hf, hD⟩, ?_⟩
      rw [none_mem_ends_contract] at hn
      rw [mem_cut]
      refine ⟨hn, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hf hcon
  rw [this, card_map]
  congr

/-- A lifted edge set has no edge inside `U`. -/
theorem inside_lift (D : Finset {e // G.OutU U e}) : G.inside U (G.lift U D) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_inside] at he
  exact G.outU_of_mem_lift U he.1 he.2

theorem sum_deg_lift (D : Finset {e // G.OutU U e}) :
    ∑ v ∈ U, G.deg (G.lift U D) v = (G.contract U).deg D none := by
  rw [G.sum_deg_eq, inside_lift, card_empty, mul_zero, zero_add, deg_contract_none]

/-! ### Terminal sets and joins under contraction -/

/-- The terminal set of the contraction: the terminals outside `U`, and `none` when `U`
holds an odd number of terminals. -/
noncomputable def cterm (T : Finset V) : Finset (Option {v // v ∉ U}) :=
  (T.subtype (· ∉ U)).map Function.Embedding.some ∪
    (if Odd (U ∩ T).card then {none} else ∅)

theorem some_mem_cterm {T : Finset V} {v : V} (hv : v ∉ U) :
    (some ⟨v, hv⟩ : Option {v // v ∉ U}) ∈ cterm U T ↔ v ∈ T := by
  simp only [cterm, mem_union, mem_map, mem_subtype, Function.Embedding.some_apply]
  constructor
  · rintro (⟨⟨w, hw⟩, hwT, hwv⟩ | h)
    · have hwv' : w = v := Subtype.ext_iff.mp (Option.some_injective _ hwv)
      subst hwv'
      exact hwT
    · split_ifs at h <;> simp at h
  · intro h
    exact Or.inl ⟨⟨v, hv⟩, h, rfl⟩

theorem none_mem_cterm {T : Finset V} :
    (none : Option {v // v ∉ U}) ∈ cterm U T ↔ Odd (U ∩ T).card := by
  simp only [cterm, mem_union, mem_map, mem_subtype, Function.Embedding.some_apply]
  constructor
  · rintro (⟨w, -, hw⟩ | h)
    · exact absurd hw (by simp)
    · split_ifs at h with hodd
      · exact hodd
      · simp at h
  · intro h
    right
    rw [if_pos h]
    exact mem_singleton_self _

/-- The parity of `|D ∩ δ(U)|` for a `T`-join `D` is that of `|U ∩ T|`. -/
theorem odd_card_inter_cut_iff {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) :
    Odd (J ∩ G.cut U).card ↔ Odd (U ∩ T).card := by
  have h := G.sum_deg_eq U J
  have hpar : (∑ v ∈ U, G.deg J v) % 2 = (U ∩ T).card % 2 := by
    rw [sum_nat_mod, ← hJ]
    have : ∀ v ∈ U, G.deg J v % 2 = if v ∈ G.odd J then 1 else 0 := by
      intro v _
      by_cases hv : v ∈ G.odd J
      · rw [if_pos hv]; rw [mem_odd, Nat.odd_iff] at hv; exact hv
      · rw [if_neg hv]; rw [mem_odd, Nat.odd_iff] at hv; omega
    rw [sum_congr rfl this, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one,
      filter_mem_eq_inter]
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- **A `T`-join restricts to a `cterm T`-join of the contraction.** -/
theorem isJoin_restrict {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) :
    (G.contract U).IsJoin (cterm U T) (G.restrict U J) := by
  rw [isJoin_iff]
  rintro (_ | ⟨v, hv⟩)
  · rw [none_mem_cterm, deg_contract_none, lift_restrict]
    have : J.filter (G.OutU U) ∩ G.cut U = J ∩ G.cut U := by
      ext e
      simp only [mem_inter, mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        intro hin
        obtain ⟨-, b, hb, hbU⟩ := G.mem_cut.mp h2
        exact hbU (hin b hb)
    rw [this, G.odd_card_inter_cut_iff U hJ]
  · rw [some_mem_cterm, deg_contract_some, lift_restrict, (G.isJoin_iff.mp hJ) v]
    have hdeg : G.deg J v = G.deg (J.filter (G.OutU U)) v := by
      unfold deg inc
      congr 1
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun hin => hv (hin v h2)⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hdeg]

/-! ### The star of a vertex -/

/-- The neighbours of `u`. -/
noncomputable def nbrs (u : V) : Finset V := univ.filter fun v => ∃ e, G.ends e = s(u, v)

theorem mem_nbrs {u v : V} : v ∈ G.nbrs u ↔ ∃ e, G.ends e = s(u, v) := by simp [nbrs]

theorem notMem_nbrs_self (u : V) : u ∉ G.nbrs u := by
  rw [mem_nbrs]
  rintro ⟨e, he⟩
  exact G.loopless e (by rw [he]; exact Sym2.mk_isDiag_iff.mpr rfl)

/-- The star of `u`: `u` and its neighbours. -/
noncomputable def star (u : V) : Finset V := insert u (G.nbrs u)

/-- No edge joins two neighbours of `u`: every edge inside the star is at `u`. -/
def NoNbrEdge (u : V) : Prop := ∀ e, (∀ a ∈ G.ends e, a ∈ G.star u) → u ∈ G.ends e

theorem noNbrEdge_of_bipartite {col : V → Bool} (hcol : G.IsBipartite col) (u : V) :
    G.NoNbrEdge u := by
  intro e he
  have hl := G.loopless e
  have hc := hcol e
  revert he hl hc
  refine Sym2.ind (fun a b he hl hc => ?_) (G.ends e)
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at he ⊢
  rw [star, mem_insert, mem_insert] at he
  rcases he with ⟨ha, hb⟩
  rcases ha with rfl | ha
  · exact Or.inl rfl
  · rcases hb with rfl | hb
    · exact Or.inr rfl
    · -- both are neighbours of `u`: same colour, contradicting the edge between them
      exfalso
      obtain ⟨ea, hea⟩ := G.mem_nbrs.mp ha
      obtain ⟨eb, heb⟩ := G.mem_nbrs.mp hb
      have h1 := hcol ea u a hea
      have h2 := hcol eb u b heb
      have h3 := hc a b rfl
      cases hcu : col u <;> cases hca : col a <;> cases hcb : col b <;> simp_all

/-- An edge inside the star with `u` as an end. -/
theorem mem_ends_of_inside_star {u : V} (hstar : G.NoNbrEdge u) {D : Finset E} {e : E}
    (he : e ∈ G.inside (G.star u) D) : e ∈ D ∧ u ∈ G.ends e :=
  ⟨(G.mem_inside.mp he).1, hstar e (G.mem_inside.mp he).2⟩

/-- The edges of `D` inside the star are exactly the edges of `D` at `u`. -/
theorem inside_star_eq_inc {u : V} (hstar : G.NoNbrEdge u) (D : Finset E) :
    G.inside (G.star u) D = G.inc D u := by
  ext e
  rw [mem_inc]
  constructor
  · exact G.mem_ends_of_inside_star hstar
  · rintro ⟨hD, hu⟩
    rw [mem_inside]
    refine ⟨hD, fun a ha => ?_⟩
    rw [star, mem_insert, mem_nbrs]
    by_cases hau : a = u
    · exact Or.inl hau
    · right
      obtain ⟨z, hz⟩ := Walk.exists_ends_eq hu
      rw [hz, Sym2.mem_iff] at ha
      rcases ha with rfl | rfl
      · exact absurd rfl hau
      · exact ⟨e, hz⟩

theorem outU_star_iff {u : V} (hstar : G.NoNbrEdge u) (e : E) :
    G.OutU (G.star u) e ↔ u ∉ G.ends e := by
  constructor
  · intro h hu
    have := (G.inside_star_eq_inc hstar univ)
    have he : e ∈ G.inc univ u := G.mem_inc.mpr ⟨mem_univ _, hu⟩
    rw [← this, mem_inside] at he
    exact h he.2
  · intro hu hin
    exact hu (hstar e hin)

/-- A chosen edge from `u` to a neighbour `x`. -/
noncomputable def starEdge (u : V) {x : V} (hx : x ∈ G.nbrs u) : E :=
  Classical.choose (G.mem_nbrs.mp hx)

theorem starEdge_spec (u : V) {x : V} (hx : x ∈ G.nbrs u) :
    G.ends (G.starEdge u hx) = s(u, x) :=
  Classical.choose_spec (G.mem_nbrs.mp hx)

/-- The chosen star edges to the neighbours in `X`. -/
noncomputable def starEdges (u : V) (X : Finset V) (hX : X ⊆ G.nbrs u) : Finset E :=
  X.attach.image fun x => G.starEdge u (hX x.2)

theorem mem_starEdges {u : V} {X : Finset V} {hX : X ⊆ G.nbrs u} {e : E} :
    e ∈ G.starEdges u X hX ↔ ∃ x, ∃ h : x ∈ X, e = G.starEdge u (hX h) := by
  simp only [starEdges, mem_image, mem_attach, true_and]
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩

theorem starEdge_injective (u : V) {X : Finset V} (hX : X ⊆ G.nbrs u) {x x' : V} (hx : x ∈ X)
    (hx' : x' ∈ X) (h : G.starEdge u (hX hx) = G.starEdge u (hX hx')) : x = x' := by
  have h1 := G.starEdge_spec u (hX hx)
  have h2 := G.starEdge_spec u (hX hx')
  rw [h, h2] at h1
  rcases Sym2.eq_iff.mp h1 with ⟨-, h3⟩ | ⟨h3, h4⟩
  · exact h3.symm
  · exact (h4.trans h3).symm

theorem card_starEdges (u : V) (X : Finset V) (hX : X ⊆ G.nbrs u) :
    (G.starEdges u X hX).card = X.card := by
  rw [starEdges, card_image_of_injective _ fun ⟨x, hx⟩ ⟨x', hx'⟩ h =>
    Subtype.ext (G.starEdge_injective u hX hx hx' h), card_attach]

theorem mem_ends_starEdges {u : V} {X : Finset V} {hX : X ⊆ G.nbrs u} {e : E}
    (he : e ∈ G.starEdges u X hX) : u ∈ G.ends e := by
  obtain ⟨x, hx, rfl⟩ := G.mem_starEdges.mp he
  rw [starEdge_spec]
  exact Sym2.mem_mk_left _ _

theorem deg_starEdges_self (u : V) (X : Finset V) (hX : X ⊆ G.nbrs u) :
    G.deg (G.starEdges u X hX) u = X.card := by
  rw [deg, ← card_starEdges G u X hX]
  congr 1
  ext e
  rw [mem_inc]
  exact ⟨fun h => h.1, fun h => ⟨h, G.mem_ends_starEdges h⟩⟩

theorem deg_starEdges_of_ne (u : V) (X : Finset V) (hX : X ⊆ G.nbrs u) {v : V} (hv : v ≠ u) :
    G.deg (G.starEdges u X hX) v = if v ∈ X then 1 else 0 := by
  rw [deg]
  split_ifs with hvX
  · rw [card_eq_one]
    refine ⟨G.starEdge u (hX hvX), ?_⟩
    ext e
    rw [mem_inc, mem_singleton, mem_starEdges]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hve⟩
      rw [starEdge_spec, Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact absurd rfl hv
      · rfl
    · rintro rfl
      refine ⟨⟨v, hvX, rfl⟩, ?_⟩
      rw [starEdge_spec]
      exact Sym2.mem_mk_right _ _
  · rw [card_eq_zero]
    rw [eq_empty_iff_forall_notMem]
    intro e he
    rw [mem_inc, mem_starEdges] at he
    obtain ⟨⟨x, hx, rfl⟩, hve⟩ := he
    rw [starEdge_spec, Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · exact hv rfl
    · exact hvX hx

theorem starEdges_subset_inc (u : V) (X : Finset V) (hX : X ⊆ G.nbrs u) :
    G.starEdges u X hX ⊆ G.inc univ u := fun e he =>
  G.mem_inc.mpr ⟨mem_univ _, G.mem_ends_starEdges he⟩

/-- A lifted edge set of the star contraction has no edge at `u`. -/
theorem deg_lift_star (u : V) (hstar : G.NoNbrEdge u) (K : Finset {e // G.OutU (G.star u) e}) :
    G.deg (G.lift (G.star u) K) u = 0 := by
  rw [deg, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_inc] at he
  exact ((G.outU_star_iff hstar e).mp (G.outU_of_mem_lift _ he.1)) he.2

theorem card_star_inter (u : V) (T : Finset V) :
    (G.star u ∩ T).card = (if u ∈ T then 1 else 0) + (G.nbrs u ∩ T).card := by
  unfold star
  split_ifs with hu
  · rw [insert_inter_of_mem hu, card_insert_of_notMem]
    · ring
    · intro h; exact G.notMem_nbrs_self u (mem_inter.mp h).1
  · rw [insert_inter_of_notMem hu, zero_add]

/-- **Joins lift back from the star contraction**: a `cterm T`-join `K` of the contraction
becomes the `T`-join `lift K ∪ A` of `G`, `A` a set of star edges with `deg u = |A|`. -/
theorem exists_lift_join {u : V} (hstar : G.NoNbrEdge u) {T : Finset V}
    {K : Finset {e // G.OutU (G.star u) e}}
    (hK : (G.contract (G.star u)).IsJoin (cterm (G.star u) T) K) :
    ∃ A : Finset E, Disjoint (G.lift (G.star u) K) A ∧
      G.IsJoin T (G.lift (G.star u) K ∪ A) ∧ G.deg (G.lift (G.star u) K ∪ A) u = A.card := by
  set L := G.lift (G.star u) K with hL
  set X : Finset V := (G.nbrs u).filter fun x => Odd (G.deg L x + if x ∈ T then 1 else 0) with hX
  have hXsub : X ⊆ G.nbrs u := filter_subset _ _
  set A := G.starEdges u X hXsub with hA
  have hdisj : Disjoint L A := by
    rw [disjoint_left]
    intro e heL heA
    have h := G.mem_ends_starEdges heA
    exact ((G.outU_star_iff hstar e).mp (G.outU_of_mem_lift _ heL)) h
  have hLu : G.deg L u = 0 := G.deg_lift_star u hstar K
  have hdegu : G.deg (L ∪ A) u = A.card := by
    rw [G.deg_add_of_disjoint hdisj, hLu, zero_add, hA, deg_starEdges_self, card_starEdges]
  refine ⟨A, hdisj, ?_, hdegu⟩
  rw [isJoin_iff]
  intro v
  rw [G.deg_add_of_disjoint hdisj]
  by_cases hvu : v = u
  · -- the parity at `u` is that of `|X|`, which is that of `u ∈ T`
    rw [hvu, hLu, zero_add, hA, deg_starEdges_self]
    -- `|X| ≡ ∑_{x ∈ nbrs} (deg_L x + [x ∈ T])`
    have hXpar : X.card % 2 = (∑ x ∈ G.nbrs u, (G.deg L x + if x ∈ T then 1 else 0)) % 2 := by
      rw [sum_nat_mod, hX, card_filter]
      congr 1
      refine sum_congr rfl fun x _ => ?_
      by_cases h : Odd (G.deg L x + if x ∈ T then 1 else 0)
      · rw [if_pos h, Nat.odd_iff.mp h]
      · rw [if_neg h]; rw [Nat.not_odd_iff_even, Nat.even_iff] at h; exact h.symm
    have hsplit : ∑ w ∈ G.star u, G.deg L w = G.deg L u + ∑ x ∈ G.nbrs u, G.deg L x := by
      unfold star
      rw [sum_insert (G.notMem_nbrs_self u)]
    have hsum : ∑ x ∈ G.nbrs u, (G.deg L x + if x ∈ T then 1 else 0) =
        (G.contract (G.star u)).deg K none + (G.nbrs u ∩ T).card := by
      rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one,
        filter_mem_eq_inter, ← G.sum_deg_lift (G.star u) K, hsplit, hLu, zero_add]
    have hnone := ((G.contract (G.star u)).isJoin_iff.mp hK) none
    rw [none_mem_cterm, card_star_inter] at hnone
    rw [Nat.odd_iff, hXpar, hsum]
    rw [Nat.odd_iff, Nat.odd_iff] at hnone
    by_cases hvT : u ∈ T
    · rw [if_pos hvT] at hnone
      exact ⟨fun _ => by omega, fun _ => hvT⟩
    · rw [if_neg hvT] at hnone
      exact ⟨fun h => absurd h hvT, fun h => absurd (by omega) hvT⟩
  · by_cases hvn : v ∈ G.nbrs u
    · -- a neighbour: one star edge fixes its parity
      rw [hA, deg_starEdges_of_ne G u X hXsub hvu]
      by_cases hvX : v ∈ X
      · rw [if_pos hvX]
        have := (mem_filter.mp hvX).2
        rw [Nat.odd_iff] at this ⊢
        by_cases hvT : v ∈ T
        · rw [if_pos hvT] at this
          exact ⟨fun _ => by omega, fun _ => hvT⟩
        · rw [if_neg hvT] at this
          exact ⟨fun h => absurd h hvT, fun h => absurd (by omega) hvT⟩
      · rw [if_neg hvX, add_zero]
        have : ¬ Odd (G.deg L v + if v ∈ T then 1 else 0) := fun h =>
          hvX (mem_filter.mpr ⟨hvn, h⟩)
        rw [Nat.not_odd_iff_even, Nat.even_iff] at this
        rw [Nat.odd_iff]
        by_cases hvT : v ∈ T
        · rw [if_pos hvT] at this
          exact ⟨fun _ => by omega, fun _ => hvT⟩
        · rw [if_neg hvT] at this
          exact ⟨fun h => absurd h hvT, fun h => absurd (by omega) hvT⟩
    · -- outside the star: the degree is that in the contraction
      have hvs : v ∉ G.star u := by
        rw [star, mem_insert]
        rintro (h | h)
        · exact hvu h
        · exact hvn h
      rw [hA, deg_starEdges_of_ne G u X hXsub hvu, if_neg (fun h => hvn (hXsub h)), add_zero]
      have := ((G.contract (G.star u)).isJoin_iff.mp hK) (some ⟨v, hvs⟩)
      rw [some_mem_cterm, deg_contract_some] at this
      exact this

/-! ### The contraction inequality -/

/-- **(♠) from (★)**: if every cycle at `u` avoiding the edge `ux` at `u` weighs at least `2`
against the minimum join `J`, then every even set `D` weighs at least `deg_D u − 2·[ux ∈ D]`.
Peel cycles at `u`. -/
theorem sharp_of_cycles {T : Finset V} {J : Finset E} (hJ : G.IsMinJoin T J) {u : V} {ux : E}
    (hux : u ∈ G.ends ux)
    (hcyc : ∀ c : Walk G u u, c.IsCycle → ux ∉ c.edgeSet → 2 ≤ wt J c.edgeSet) :
    ∀ D, G.IsEven D → (G.deg D u : ℤ) - 2 * (if ux ∈ D then 1 else 0) ≤ wt J D := by
  intro D
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | _ n ih =>
  intro hD
  have hwt := (G.isMinJoin_iff hJ.1).mp hJ
  by_cases hu : G.deg D u = 0
  · have hux' : ux ∉ D := fun h => by
      have : ux ∈ G.inc D u := G.mem_inc.mpr ⟨h, hux⟩
      rw [deg, card_eq_zero] at hu
      rw [hu] at this
      exact notMem_empty _ this
    rw [hu, if_neg hux']
    have := hwt D hD
    push_cast
    linarith
  · obtain ⟨c, hc, hcD⟩ := Walk.exists_cycle_of_isEven hD (Nat.one_le_iff_ne_zero.mpr hu)
    have hCeven : G.IsEven c.edgeSet := Walk.isEven_edgeSet_of_closed hc.2.1
    have hCu : G.deg c.edgeSet u = 2 := Walk.deg_edgeSet_of_isCycle hc
    have hD' : G.IsEven (D \ c.edgeSet) := G.isEven_sdiff_of_subset hD hCeven hcD
    have hCne : 1 ≤ c.edgeSet.card := by
      by_contra h
      push Not at h
      have : c.edgeSet = ∅ := card_eq_zero.mp (by omega)
      rw [deg, this] at hCu
      simp [inc] at hCu
    have hcard : (D \ c.edgeSet).card < n := by
      rw [← hn]
      have := card_sdiff_add_card_eq_card hcD
      omega
    have ih' := ih _ hcard (D \ c.edgeSet) rfl hD'
    have hunion : D = c.edgeSet ∪ (D \ c.edgeSet) := (union_sdiff_of_subset hcD).symm
    have hdisj : Disjoint c.edgeSet (D \ c.edgeSet) := disjoint_sdiff
    have hdeg : G.deg D u = G.deg c.edgeSet u + G.deg (D \ c.edgeSet) u := by
      conv_lhs => rw [hunion]
      exact G.deg_add_of_disjoint hdisj u
    have hwtD : wt J D = wt J c.edgeSet + wt J (D \ c.edgeSet) := by
      conv_lhs => rw [hunion]
      exact wt_add_of_disjoint J hdisj
    have hC2 : 2 - 2 * (if ux ∈ c.edgeSet then (1 : ℤ) else 0) ≤ wt J c.edgeSet := by
      by_cases h : ux ∈ c.edgeSet
      · rw [if_pos h]; have := hwt _ hCeven; linarith
      · rw [if_neg h]; have := hcyc c hc h; linarith
    have hind : (if ux ∈ D then (1 : ℤ) else 0) =
        (if ux ∈ c.edgeSet then 1 else 0) + (if ux ∈ D \ c.edgeSet then 1 else 0) := by
      by_cases h : ux ∈ c.edgeSet
      · rw [if_pos h, if_pos (hcD h), if_neg (fun h' => (mem_sdiff.mp h').2 h)]; ring
      · by_cases h' : ux ∈ D
        · rw [if_pos h', if_neg h, if_pos (mem_sdiff.mpr ⟨h', h⟩)]; ring
        · rw [if_neg h', if_neg h, if_neg (fun h'' => h' (mem_sdiff.mp h'').1)]; ring
    rw [hwtD, hind, hdeg, hCu]
    push_cast
    linarith

/-- **The contraction inequality.**  For a minimum `T`-join `J` with the single edge `ux` at
`u`, and (♠) for `J` at `u`, every `cterm T`-join of the star contraction has at least
`|J| − 1 = |restrict J|` edges. -/
theorem card_restrict_le {u x : V} (hstar : G.NoNbrEdge u) {T : Finset V} {J : Finset E}
    (hJ : G.IsMinJoin T J) {ux : E} (hux : G.ends ux = s(u, x)) (huxJ : ux ∈ J)
    (hdeg : G.deg J u = 1)
    (hsp : ∀ D, G.IsEven D → (G.deg D u : ℤ) - 2 * (if ux ∈ D then 1 else 0) ≤ wt J D)
    {K : Finset {e // G.OutU (G.star u) e}}
    (hK : (G.contract (G.star u)).IsJoin (cterm (G.star u) T) K) :
    (G.restrict (G.star u) J).card ≤ K.card := by
  obtain ⟨A, hdisj, hjoin, hdegu⟩ := G.exists_lift_join hstar hK
  have huxu : u ∈ G.ends ux := by rw [hux]; exact Sym2.mem_mk_left _ _
  have hKfcard : (G.lift (G.star u) K ∪ A).card = K.card + A.card := by
    rw [card_union_of_disjoint hdisj, card_lift]
  have hD : G.IsEven (J ∆ (G.lift (G.star u) K ∪ A)) := G.isEven_symmDiff_of_isJoin hJ.1 hjoin
  have hwt : wt J (J ∆ (G.lift (G.star u) K ∪ A)) =
      ((G.lift (G.star u) K ∪ A).card : ℤ) - J.card := by
    have := card_symmDiff_eq_add_wt J (J ∆ (G.lift (G.star u) K ∪ A))
    rw [symmDiff_symmDiff_cancel] at this
    linarith
  have hincJ : G.inc J u = {ux} := by
    have hmem : ux ∈ G.inc J u := G.mem_inc.mpr ⟨huxJ, huxu⟩
    rw [deg] at hdeg
    obtain ⟨e, he⟩ := card_eq_one.mp hdeg
    rw [he] at hmem ⊢
    rw [mem_singleton] at hmem
    rw [hmem]
  have huxL : ux ∉ G.lift (G.star u) K := fun h =>
    ((G.outU_star_iff hstar ux).mp (G.outU_of_mem_lift _ h)) huxu
  have hint : (({ux} : Finset E) ∩ G.inc (G.lift (G.star u) K ∪ A) u).card =
      if ux ∈ A then 1 else 0 := by
    by_cases h' : ux ∈ A
    · rw [if_pos h', singleton_inter_of_mem (G.mem_inc.mpr ⟨mem_union_right _ h', huxu⟩),
        card_singleton]
    · rw [if_neg h', singleton_inter_of_notMem, card_empty]
      intro hm
      rw [mem_inc, mem_union] at hm
      rcases hm.1 with hm | hm
      · exact huxL hm
      · exact h' hm
  have hdegD : G.deg (J ∆ (G.lift (G.star u) K ∪ A)) u +
      2 * (if ux ∈ A then 1 else 0) = A.card + 1 := by
    rw [deg, inc_symmDiff, hincJ]
    have h := card_symmDiff_add ({ux} : Finset E) (G.inc (G.lift (G.star u) K ∪ A) u)
    rw [hint, card_singleton] at h
    have hS : (G.inc (G.lift (G.star u) K ∪ A) u).card = A.card := hdegu
    omega
  have huxD : (if ux ∈ J ∆ (G.lift (G.star u) K ∪ A) then (1 : ℤ) else 0) =
      1 - (if ux ∈ A then 1 else 0) := by
    by_cases h' : ux ∈ A
    · rw [if_pos h', if_neg]
      · ring
      · intro hm
        rw [mem_symmDiff] at hm
        rcases hm with ⟨-, hn⟩ | ⟨-, hn⟩
        · exact hn (mem_union_right _ h')
        · exact hn huxJ
    · rw [if_neg h', if_pos]
      · ring
      · rw [mem_symmDiff]
        left
        refine ⟨huxJ, fun hm => ?_⟩
        rcases mem_union.mp hm with hm | hm
        · exact huxL hm
        · exact h' hm
  have hsp' := hsp _ hD
  rw [huxD, hwt, hKfcard] at hsp'
  have hres := G.card_restrict (G.star u) J
  rw [G.inside_star_eq_inc hstar, hincJ, card_singleton] at hres
  have hdegD' : (G.deg (J ∆ (G.lift (G.star u) K ∪ A)) u : ℤ) +
      2 * (if ux ∈ A then (1 : ℤ) else 0) = A.card + 1 := by
    have := hdegD
    split_ifs at this ⊢ <;> push_cast at this ⊢ <;> omega
  split_ifs at hsp' hdegD' <;> push_cast at hsp' hdegD' <;> omega

end MGraph
end TSPGap

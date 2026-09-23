/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerTheorem6

/-!
# Tucker's Theorem 7: minimal asteroidal triples are the five patterns

Tucker's Theorem 7: the elements contain no asteroidal triple iff the incidence graph
contains none of `I_n, II_n, III_n, IV, V` as a bipartite subgraph, i.e. (in our terms) iff
the family contains none of `MI k, MII k, MIII k, MIV, MV` as a configuration.  Necessity is
the easy direction and is not needed by any consumer.  Sufficiency is proved for a
**minimal** instance: every sub-instance of smaller size has no asteroidal triple.

This file has the reduction to a minimal instance (`exists_minimal_asteroidal`), Theorem 7
for minimal instances as the explicit hypothesis `MinimalTriplePattern α` (to be discharged
by the case analysis of Tucker's proof), and the compositions: Tucker-free families have no
asteroidal triple (`no_asteroidal_of_tuckerFree`), hence a consecutive-ones order
(`hasConsecutiveOnes_of_tuckerFree'`, Tucker's Theorem 6).
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Among the sub-instances carrying an asteroidal triple there is one of minimal size. -/
theorem exists_minimal_asteroidal {O : Finset α} {F : Finset (Finset α)}
    (h : ∃ x y z, IsAsteroidalTriple O F x y z) :
    ∃ O' ⊆ O, ∃ F' ⊆ F, (∃ x y z, IsAsteroidalTriple O' F' x y z) ∧
      ∀ O'' ⊆ O', ∀ F'' ⊆ F', O''.card + F''.card < O'.card + F'.card →
        ∀ x y z, ¬ IsAsteroidalTriple O'' F'' x y z := by
  suffices key : ∀ n, ∀ (O : Finset α) (F : Finset (Finset α)), O.card + F.card = n →
      (∃ x y z, IsAsteroidalTriple O F x y z) →
      ∃ O' ⊆ O, ∃ F' ⊆ F, (∃ x y z, IsAsteroidalTriple O' F' x y z) ∧
        ∀ O'' ⊆ O', ∀ F'' ⊆ F', O''.card + F''.card < O'.card + F'.card →
          ∀ x y z, ¬ IsAsteroidalTriple O'' F'' x y z from key _ O F rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O F hn h
  by_cases hmin : ∀ O'' ⊆ O, ∀ F'' ⊆ F, O''.card + F''.card < O.card + F.card →
      ∀ x y z, ¬ IsAsteroidalTriple O'' F'' x y z
  · exact ⟨O, le_rfl, F, le_rfl, h, hmin⟩
  · push Not at hmin
    obtain ⟨O'', hO'', F'', hF'', hlt, x, y, z, hAT⟩ := hmin
    obtain ⟨O', hO', F', hF', h', hmin'⟩ := ih _ (hn ▸ hlt) O'' F'' rfl ⟨x, y, z, hAT⟩
    exact ⟨O', hO'.trans hO'', F', hF'.trans hF'', h', hmin'⟩

/-- **Tucker's Theorem 7 for minimal instances**, as a hypothesis: an instance carrying an
asteroidal triple, all of whose smaller sub-instances carry none, contains one of the five
patterns as a configuration. -/
def MinimalTriplePattern (α : Type*) [DecidableEq α] : Prop :=
  ∀ (O : Finset α) (F : Finset (Finset α)), (∃ x y z, IsAsteroidalTriple O F x y z) →
    (∀ O' ⊆ O, ∀ F' ⊆ F, O'.card + F'.card < O.card + F.card →
      ∀ x y z, ¬ IsAsteroidalTriple O' F' x y z) →
    ¬ IsTuckerFree F

/-- A Tucker-free family has no asteroidal triple (modulo Theorem 7 for minimal instances). -/
theorem no_asteroidal_of_tuckerFree (h7 : MinimalTriplePattern α) {O : Finset α}
    {F : Finset (Finset α)} (hT : IsTuckerFree F) :
    ∀ x y z, ¬ IsAsteroidalTriple O F x y z := by
  intro x y z h
  obtain ⟨O', -, F', hF', hAT, hmin⟩ := exists_minimal_asteroidal ⟨x, y, z, h⟩
  exact h7 O' F' hAT hmin (hT.mono hF')

/-- **Tucker's Theorem 9 (sufficiency), modulo Theorem 7 for minimal instances**: a
Tucker-free family has a consecutive-ones order. -/
theorem hasConsecutiveOnes_of_tuckerFree' (h7 : MinimalTriplePattern α) {O : Finset α}
    {F : Finset (Finset α)} (hT : IsTuckerFree F) : CircularOnes.HasConsecutiveOnes O F :=
  hasConsecutiveOnes_iff_list.mpr
    (exists_c1pList_of_no_asteroidal' (no_asteroidal_of_tuckerFree h7 hT))

/-! ### The avoiding graph and shortest avoiding paths -/

/-- The sets of `F` not containing `a`. -/
def avoidSets (F : Finset (Finset α)) (a : α) : Finset (Finset α) := F.filter fun S => a ∉ S

theorem mem_avoidSets {F : Finset (Finset α)} {a : α} {S : Finset α} :
    S ∈ avoidSets F a ↔ S ∈ F ∧ a ∉ S := Finset.mem_filter

/-- The incidence graph restricted to the sets avoiding `a`: its walks between elements
are exactly the paths "not adjacent to `a`". -/
abbrev avoidGraph (O : Finset α) (F : Finset (Finset α)) (a : α) : SimpleGraph (α ⊕ Finset α) :=
  incGraph O (avoidSets F a)

theorem avoidGraph_le (O : Finset α) (F : Finset (Finset α)) (a : α) :
    avoidGraph O F a ≤ incGraph O F :=
  incGraph_mono le_rfl (Finset.filter_subset _ _)

/-- A walk of the avoiding graph is a walk of the incidence graph nowhere adjacent to `a`. -/
theorem avoidingPath_of_avoidGraph_walk {O : Finset α} {F : Finset (Finset α)} {a x z : α}
    (W : (avoidGraph O F a).Walk (Sum.inl x) (Sum.inl z)) : AvoidingPath O F a x z := by
  have hedges : ∀ e ∈ W.edges, e ∈ (incGraph O F).edgeSet := fun e he =>
    SimpleGraph.edgeSet_subset_edgeSet.mpr (avoidGraph_le O F a) (W.edges_subset_edgeSet he)
  refine ⟨W.transfer _ hedges, fun v hv => ?_⟩
  rw [W.support_transfer hedges] at hv
  rcases v with b | S
  · exact incGraph_not_adj_inl_inl
  · rw [incGraph_adj_inr_inl]
    rintro ⟨-, hS, haS⟩
    -- `S` is a set vertex of a walk of the avoiding graph, hence avoids `a`
    have hSF : S ∈ avoidSets F a := mem_of_inr_mem_support W hv
    exact (mem_avoidSets.mp hSF).2 haS

/-- Conversely, a walk nowhere adjacent to `a ∈ O` transfers to the avoiding graph. -/
theorem exists_avoidGraph_walk_of_avoiding {O : Finset α} {F : Finset (Finset α)} {a x z : α}
    (ha : a ∈ O) (W : (incGraph O F).Walk (Sum.inl x) (Sum.inl z))
    (hW : ∀ v ∈ W.support, ¬ (incGraph O F).Adj v (Sum.inl a)) :
    ∃ W' : (avoidGraph O F a).Walk (Sum.inl x) (Sum.inl z),
      W'.length = W.length ∧ W'.support = W.support := by
  have hedges : ∀ e ∈ W.edges, e ∈ (avoidGraph O F a).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    have hadj : (incGraph O F).Adj u v := (SimpleGraph.mem_edgeSet _).mp (W.edges_subset_edgeSet he)
    have hu : u ∈ W.support := W.fst_mem_support_of_mem_edges he
    have hv : v ∈ W.support := W.snd_mem_support_of_mem_edges he
    rcases u with b | S <;> rcases v with c | T
    · exact absurd hadj incGraph_not_adj_inl_inl
    · rw [incGraph_adj_inl_inr] at hadj ⊢
      refine ⟨hadj.1, mem_avoidSets.mpr ⟨hadj.2.1, fun haT => ?_⟩, hadj.2.2⟩
      exact hW _ hv (incGraph_adj_inr_inl.mpr ⟨ha, hadj.2.1, haT⟩)
    · rw [incGraph_adj_inr_inl] at hadj ⊢
      refine ⟨hadj.1, mem_avoidSets.mpr ⟨hadj.2.1, fun haS => ?_⟩, hadj.2.2⟩
      exact hW _ hu (incGraph_adj_inr_inl.mpr ⟨ha, hadj.2.1, haS⟩)
    · exact absurd hadj incGraph_not_adj_inr_inr
  exact ⟨W.transfer _ hedges, W.length_transfer hedges, W.support_transfer hedges⟩

theorem reachable_avoidGraph_iff {O : Finset α} {F : Finset (Finset α)} {a x z : α} (ha : a ∈ O) :
    (avoidGraph O F a).Reachable (Sum.inl x) (Sum.inl z) ↔ AvoidingPath O F a x z :=
  ⟨fun ⟨W⟩ => avoidingPath_of_avoidGraph_walk W, fun ⟨W, hW⟩ =>
    let ⟨W', _, _⟩ := exists_avoidGraph_walk_of_avoiding ha W hW; ⟨W'⟩⟩

omit [DecidableEq α] in
/-- **Shortest walks are chordless**: two vertices of a shortest walk that are not
consecutive are not adjacent. -/
theorem not_adj_of_shortest {V : Type*} {G : SimpleGraph V} {u v : V} (P : G.Walk u v)
    (hP : P.length = G.dist u v) {i j : ℕ} (hij : i + 1 < j) (hj : j ≤ P.length) :
    ¬ G.Adj (P.getVert i) (P.getVert j) := by
  intro hadj
  have := SimpleGraph.dist_le ((P.take i).append (SimpleGraph.Walk.cons hadj (P.drop j)))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length] at this
  omega

/-- A set vertex of a walk of the incidence graph of `F'` lies in `F'`; for the avoiding
graph this means it avoids `a`. -/
theorem notMem_of_inr_mem_support_avoid {O : Finset α} {F : Finset (Finset α)} {a x : α}
    {w : α ⊕ Finset α} (W : (avoidGraph O F a).Walk (Sum.inl x) w) {S : Finset α}
    (hS : Sum.inr S ∈ W.support) : S ∈ F ∧ a ∉ S :=
  mem_avoidSets.mp (mem_of_inr_mem_support W hS)

/-- A chord of the incidence graph between two vertices of a shortest walk of the avoiding
graph is impossible: the chord lies in the avoiding graph. -/
theorem not_incGraph_adj_of_shortest {O : Finset α} {F : Finset (Finset α)} {a x z : α}
    (P : (avoidGraph O F a).Walk (Sum.inl x) (Sum.inl z))
    (hP : P.length = (avoidGraph O F a).dist (Sum.inl x) (Sum.inl z)) {i j : ℕ}
    (hij : i + 1 < j) (hj : j ≤ P.length) :
    ¬ (incGraph O F).Adj (P.getVert i) (P.getVert j) := by
  intro hadj
  refine not_adj_of_shortest P hP hij hj ?_
  have hi : P.getVert i ∈ P.support := P.getVert_mem_support i
  have hj' : P.getVert j ∈ P.support := P.getVert_mem_support j
  rcases hgi : P.getVert i with b | S <;> rcases hgj : P.getVert j with c | T <;>
    rw [hgi, hgj] at hadj
  · exact absurd hadj incGraph_not_adj_inl_inl
  · rw [hgj] at hj'
    obtain ⟨hTF, haT⟩ := notMem_of_inr_mem_support_avoid P hj'
    rw [incGraph_adj_inl_inr] at hadj
    exact incGraph_adj_inl_inr.mpr ⟨hadj.1, mem_avoidSets.mpr ⟨hTF, haT⟩, hadj.2.2⟩
  · rw [hgi] at hi
    obtain ⟨hSF, haS⟩ := notMem_of_inr_mem_support_avoid P hi
    rw [incGraph_adj_inr_inl] at hadj
    exact incGraph_adj_inr_inl.mpr ⟨hadj.1, mem_avoidSets.mpr ⟨hSF, haS⟩, hadj.2.2⟩
  · exact absurd hadj incGraph_not_adj_inr_inr

/-! ### Minimality: the three paths carry every vertex, and deleting any vertex kills the
triple -/

/-- A minimal instance: it carries an asteroidal triple, and no smaller sub-instance
does. -/
structure IsMinimalTriple (O : Finset α) (F : Finset (Finset α)) (x y z : α) : Prop where
  triple : IsAsteroidalTriple O F x y z
  min : ∀ O' ⊆ O, ∀ F' ⊆ F, O'.card + F'.card < O.card + F.card →
    ∀ a b c, ¬ IsAsteroidalTriple O' F' a b c

/-- Three avoiding walks whose vertices all lie in `O'`, `F'` give the triple in `(O', F')`. -/
theorem triple_of_walks {O O' : Finset α} {F F' : Finset (Finset α)} {x y z : α}
    (h : IsAsteroidalTriple O F x y z)
    (Pxy : (avoidGraph O F z).Walk (Sum.inl x) (Sum.inl y))
    (Pxz : (avoidGraph O F y).Walk (Sum.inl x) (Sum.inl z))
    (Pyz : (avoidGraph O F x).Walk (Sum.inl y) (Sum.inl z))
    (hOxy : ∀ a, Sum.inl a ∈ Pxy.support → a ∈ O') (hFxy : ∀ S, Sum.inr S ∈ Pxy.support → S ∈ F')
    (hOxz : ∀ a, Sum.inl a ∈ Pxz.support → a ∈ O') (hFxz : ∀ S, Sum.inr S ∈ Pxz.support → S ∈ F')
    (hOyz : ∀ a, Sum.inl a ∈ Pyz.support → a ∈ O') (hFyz : ∀ S, Sum.inr S ∈ Pyz.support → S ∈ F') :
    IsAsteroidalTriple O' F' x y z := by
  have hxO' : x ∈ O' := hOxy x Pxy.start_mem_support
  have hyO' : y ∈ O' := hOxy y Pxy.end_mem_support
  have hzO' : z ∈ O' := hOxz z Pxz.end_mem_support
  -- transfer of a walk into the smaller avoiding graph
  have transfer : ∀ {a b c : α} (W : (avoidGraph O F a).Walk (Sum.inl b) (Sum.inl c)),
      (∀ d, Sum.inl d ∈ W.support → d ∈ O') → (∀ S, Sum.inr S ∈ W.support → S ∈ F') →
      (avoidGraph O' F' a).Reachable (Sum.inl b) (Sum.inl c) := by
    intro a b c W hO hF
    have hedges : ∀ e ∈ W.edges, e ∈ (avoidGraph O' F' a).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hadj : (avoidGraph O F a).Adj u v :=
        (SimpleGraph.mem_edgeSet _).mp (W.edges_subset_edgeSet he)
      have hu : u ∈ W.support := W.fst_mem_support_of_mem_edges he
      have hv : v ∈ W.support := W.snd_mem_support_of_mem_edges he
      rcases u with d | S <;> rcases v with d' | T
      · exact absurd hadj incGraph_not_adj_inl_inl
      · rw [incGraph_adj_inl_inr, mem_avoidSets] at hadj ⊢
        exact ⟨hO d hu, ⟨hF T hv, hadj.2.1.2⟩, hadj.2.2⟩
      · rw [incGraph_adj_inr_inl, mem_avoidSets] at hadj ⊢
        exact ⟨hO d' hv, ⟨hF S hu, hadj.2.1.2⟩, hadj.2.2⟩
      · exact absurd hadj incGraph_not_adj_inr_inr
    exact ⟨W.transfer _ hedges⟩
  exact ⟨hxO', hyO', hzO', h.ne_xy, h.ne_yz, h.ne_xz,
    (reachable_avoidGraph_iff hzO').mp (transfer Pxy hOxy hFxy),
    (reachable_avoidGraph_iff hyO').mp (transfer Pxz hOxz hFxz),
    (reachable_avoidGraph_iff hxO').mp (transfer Pyz hOyz hFyz)⟩

/-- **Every vertex of a minimal instance lies on one of three given avoiding walks.** -/
theorem mem_paths_of_minimal {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (hmin : IsMinimalTriple O F x y z)
    (Pxy : (avoidGraph O F z).Walk (Sum.inl x) (Sum.inl y))
    (Pxz : (avoidGraph O F y).Walk (Sum.inl x) (Sum.inl z))
    (Pyz : (avoidGraph O F x).Walk (Sum.inl y) (Sum.inl z)) :
    (∀ a ∈ O, Sum.inl a ∈ Pxy.support ∨ Sum.inl a ∈ Pxz.support ∨ Sum.inl a ∈ Pyz.support) ∧
      ∀ S ∈ F, Sum.inr S ∈ Pxy.support ∨ Sum.inr S ∈ Pxz.support ∨ Sum.inr S ∈ Pyz.support := by
  classical
  set O' := O.filter fun a =>
    Sum.inl a ∈ Pxy.support ∨ Sum.inl a ∈ Pxz.support ∨ Sum.inl a ∈ Pyz.support
  set F' := F.filter fun S =>
    Sum.inr S ∈ Pxy.support ∨ Sum.inr S ∈ Pxz.support ∨ Sum.inr S ∈ Pyz.support
  have hO'O : O' ⊆ O := Finset.filter_subset _ _
  have hF'F : F' ⊆ F := Finset.filter_subset _ _
  have hOxy : ∀ a, Sum.inl a ∈ Pxy.support → a ∈ O' := fun a ha =>
    Finset.mem_filter.mpr ⟨mem_of_inl_mem_support Pxy hmin.triple.y_mem ha, Or.inl ha⟩
  have hFxy : ∀ S, Sum.inr S ∈ Pxy.support → S ∈ F' := fun S hS =>
    Finset.mem_filter.mpr ⟨(notMem_of_inr_mem_support_avoid Pxy hS).1, Or.inl hS⟩
  have hOxz : ∀ a, Sum.inl a ∈ Pxz.support → a ∈ O' := fun a ha =>
    Finset.mem_filter.mpr ⟨mem_of_inl_mem_support Pxz hmin.triple.z_mem ha, Or.inr (Or.inl ha)⟩
  have hFxz : ∀ S, Sum.inr S ∈ Pxz.support → S ∈ F' := fun S hS =>
    Finset.mem_filter.mpr ⟨(notMem_of_inr_mem_support_avoid Pxz hS).1, Or.inr (Or.inl hS)⟩
  have hOyz : ∀ a, Sum.inl a ∈ Pyz.support → a ∈ O' := fun a ha =>
    Finset.mem_filter.mpr ⟨mem_of_inl_mem_support Pyz hmin.triple.z_mem ha, Or.inr (Or.inr ha)⟩
  have hFyz : ∀ S, Sum.inr S ∈ Pyz.support → S ∈ F' := fun S hS =>
    Finset.mem_filter.mpr ⟨(notMem_of_inr_mem_support_avoid Pyz hS).1, Or.inr (Or.inr hS)⟩
  have htriple := triple_of_walks hmin.triple Pxy Pxz Pyz hOxy hFxy hOxz hFxz hOyz hFyz
  have hFle : F'.card ≤ F.card := Finset.card_le_card hF'F
  have hOle : O'.card ≤ O.card := Finset.card_le_card hO'O
  constructor
  · intro a ha
    by_contra hcon
    have hlt : O'.card < O.card := Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨a, ha, hcon⟩)
    exact hmin.min O' hO'O F' hF'F (by omega) x y z htriple
  · intro S hS
    by_contra hcon
    have hlt : F'.card < F.card := Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨S, hS, hcon⟩)
    exact hmin.min O' hO'O F' hF'F (by omega) x y z htriple

/-- **Deleted-element certificate**: in a minimal instance, three avoiding walks none of
which visits the element `r` cannot exist. -/
theorem no_walks_avoiding_elem {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (hmin : IsMinimalTriple O F x y z) {r : α} (hr : r ∈ O)
    (Pxy : (avoidGraph O F z).Walk (Sum.inl x) (Sum.inl y)) (h1 : Sum.inl r ∉ Pxy.support)
    (Pxz : (avoidGraph O F y).Walk (Sum.inl x) (Sum.inl z)) (h2 : Sum.inl r ∉ Pxz.support)
    (Pyz : (avoidGraph O F x).Walk (Sum.inl y) (Sum.inl z)) (h3 : Sum.inl r ∉ Pyz.support) :
    False := by
  have hO' : O.erase r ⊆ O := Finset.erase_subset _ _
  have hlt : (O.erase r).card < O.card := Finset.card_erase_lt_of_mem hr
  refine hmin.min (O.erase r) hO' F le_rfl (by omega) x y z
    (triple_of_walks hmin.triple Pxy Pxz Pyz ?_ ?_ ?_ ?_ ?_ ?_)
  · exact fun a ha => Finset.mem_erase.mpr ⟨fun e => h1 (e ▸ ha),
      mem_of_inl_mem_support Pxy hmin.triple.y_mem ha⟩
  · exact fun S hS => (notMem_of_inr_mem_support_avoid Pxy hS).1
  · exact fun a ha => Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ ha),
      mem_of_inl_mem_support Pxz hmin.triple.z_mem ha⟩
  · exact fun S hS => (notMem_of_inr_mem_support_avoid Pxz hS).1
  · exact fun a ha => Finset.mem_erase.mpr ⟨fun e => h3 (e ▸ ha),
      mem_of_inl_mem_support Pyz hmin.triple.z_mem ha⟩
  · exact fun S hS => (notMem_of_inr_mem_support_avoid Pyz hS).1

/-- **Deleted-set certificate**: in a minimal instance, three avoiding walks none of which
visits the set `r` cannot exist. -/
theorem no_walks_avoiding_set {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (hmin : IsMinimalTriple O F x y z) {r : Finset α} (hr : r ∈ F)
    (Pxy : (avoidGraph O F z).Walk (Sum.inl x) (Sum.inl y)) (h1 : Sum.inr r ∉ Pxy.support)
    (Pxz : (avoidGraph O F y).Walk (Sum.inl x) (Sum.inl z)) (h2 : Sum.inr r ∉ Pxz.support)
    (Pyz : (avoidGraph O F x).Walk (Sum.inl y) (Sum.inl z)) (h3 : Sum.inr r ∉ Pyz.support) :
    False := by
  have hF' : F.erase r ⊆ F := Finset.erase_subset _ _
  have hlt : (F.erase r).card < F.card := Finset.card_erase_lt_of_mem hr
  refine hmin.min O le_rfl (F.erase r) hF' (by omega) x y z
    (triple_of_walks hmin.triple Pxy Pxz Pyz ?_ ?_ ?_ ?_ ?_ ?_)
  · exact fun a ha => mem_of_inl_mem_support Pxy hmin.triple.y_mem ha
  · exact fun S hS => Finset.mem_erase.mpr ⟨fun e => h1 (e ▸ hS),
      (notMem_of_inr_mem_support_avoid Pxy hS).1⟩
  · exact fun a ha => mem_of_inl_mem_support Pxz hmin.triple.z_mem ha
  · exact fun S hS => Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hS),
      (notMem_of_inr_mem_support_avoid Pxz hS).1⟩
  · exact fun a ha => mem_of_inl_mem_support Pyz hmin.triple.z_mem ha
  · exact fun S hS => Finset.mem_erase.mpr ⟨fun e => h3 (e ▸ hS),
      (notMem_of_inr_mem_support_avoid Pyz hS).1⟩

end Tucker

end TSPGap

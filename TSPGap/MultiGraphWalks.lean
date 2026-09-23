/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MultiGraph
import Mathlib.Data.List.TakeWhile

/-!
# Walks in a labelled multigraph

A walk records the edge labels it traverses (`Walk.cons e he p` with `he : G.ends e = s(u, v)`),
so parallel edges stay distinct and the edge set of a walk is a finset of labels.  Trails
have no repeated edge, paths no repeated vertex, and a cycle is a nonempty closed trail whose
vertices other than the base are distinct.

The one identity everything rests on is the **degree count of a trail**
(`deg_edgeSet_add_eq`): for a trail from `u` to `w` and any vertex `x`,
`deg x + [x = u] + [x = w] = 2 · (occurrences of x in the support)`.  It gives the boundary
of a trail (`{u, w}` or `∅`), the degree `2` of the base of a cycle, and the degree `1` of the
start of a path.

The two structural facts for Seymour's theorem:
* `exists_cycle_of_isEven` — an even edge set with an edge at `u` contains a cycle at `u`
  (a maximal trail from `u` inside the set is closed; a shortest nonempty closed trail is a
  cycle);
* `exists_longest_path` and `deg_eq_one_of_longest` — in a forest (an edge set with no
  nonempty even subset) a longest path exists and its start has degree one; a path extends
  by an edge to a new vertex (`isPath_cons`).
`takeUntil`/`dropUntil` split a walk at the first occurrence of a vertex, with their supports
characterised by `takeWhile`/`dropWhile`.
-/

namespace TSPGap
namespace MGraph

open Finset
open Classical
open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E]

/-- A walk from `u` to `w`, recording the labels of the edges it traverses. -/
inductive Walk (G : MGraph V E) : V → V → Type _
  | nil {v : V} : Walk G v v
  | cons {u v w : V} (e : E) (he : G.ends e = s(u, v)) (p : Walk G v w) : Walk G u w

namespace Walk

variable {G : MGraph V E} {u v w : V}

/-- The edge labels of a walk, in order. -/
def edges : ∀ {u w : V}, Walk G u w → List E
  | _, _, nil => []
  | _, _, cons e _ p => e :: p.edges

/-- The vertices of a walk, in order, starting with `u`. -/
def support : ∀ {u w : V}, Walk G u w → List V
  | u, _, nil => [u]
  | u, _, cons _ _ p => u :: p.support

/-- The number of edges. -/
def length (p : Walk G u w) : ℕ := p.edges.length

/-- The edge set of a walk. -/
noncomputable def edgeSet (p : Walk G u w) : Finset E := p.edges.toFinset

/-- No repeated edge. -/
def IsTrail (p : Walk G u w) : Prop := p.edges.Nodup

/-- No repeated vertex. -/
def IsPath (p : Walk G u w) : Prop := p.support.Nodup

/-- A cycle: a nonempty closed trail whose vertices after the base are distinct. -/
def IsCycle (p : Walk G u u) : Prop := p.edges ≠ [] ∧ p.edges.Nodup ∧ p.support.tail.Nodup

@[simp] theorem edges_nil : (nil : Walk G u u).edges = [] := rfl
@[simp] theorem edges_cons (e : E) (he : G.ends e = s(u, v)) (p : Walk G v w) :
    (cons e he p).edges = e :: p.edges := rfl
@[simp] theorem support_nil : (nil : Walk G u u).support = [u] := rfl
@[simp] theorem support_cons (e : E) (he : G.ends e = s(u, v)) (p : Walk G v w) :
    (cons e he p).support = u :: p.support := rfl

theorem length_support (p : Walk G u w) : p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp [length, support, edges] at ih ⊢; exact ih

theorem support_ne_nil (p : Walk G u w) : p.support ≠ [] := by
  cases p <;> simp [support]

theorem start_mem_support (p : Walk G u w) : u ∈ p.support := by
  cases p <;> simp [support]

theorem end_mem_support (p : Walk G u w) : w ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons e he p ih => simp [support, ih]

theorem mem_edgeSet {p : Walk G u w} {e : E} : e ∈ p.edgeSet ↔ e ∈ p.edges := by
  simp [edgeSet]

theorem card_edgeSet_of_isTrail {p : Walk G u w} (hp : p.IsTrail) :
    p.edgeSet.card = p.length := by
  rw [edgeSet, List.toFinset_card_of_nodup hp]
  rfl

theorem edges_ne_nil_iff_edgeSet_nonempty (p : Walk G u w) :
    p.edges ≠ [] ↔ p.edgeSet.Nonempty := by
  rw [edgeSet, List.toFinset_nonempty_iff]

/-- The edges of a path are at most the vertices. -/
theorem length_le_card_of_isPath {p : Walk G u w} (hp : p.IsPath) :
    p.length + 1 ≤ Fintype.card V := by
  rw [← length_support]
  exact hp.length_le_card

theorem length_le_card_of_isTrail {p : Walk G u w} (hp : p.IsTrail) {D : Finset E}
    (hD : p.edgeSet ⊆ D) : p.length ≤ D.card := by
  rw [← card_edgeSet_of_isTrail hp]
  exact card_le_card hD

/-- A loopless edge joins distinct vertices. -/
theorem ne_of_ends {e : E} (he : G.ends e = s(u, v)) : u ≠ v := by
  intro h
  subst h
  exact G.loopless e (by rw [he]; exact Sym2.mk_isDiag_iff.mpr rfl)

/-! ### Append and copy -/

/-- Concatenation. -/
def append : ∀ {u v w : V}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, nil, q => q
  | _, _, _, cons e he p, q => cons e he (p.append q)

@[simp] theorem nil_append (q : Walk G u w) : (nil : Walk G u u).append q = q := rfl
@[simp] theorem cons_append (e : E) (he : G.ends e = s(u, v)) (p : Walk G v w)
    (q : Walk G w w') : (cons e he p).append q = cons e he (p.append q) := rfl

theorem edges_append (p : Walk G u v) (q : Walk G v w) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp [ih]

theorem support_append (p : Walk G u v) (q : Walk G v w) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p with
  | nil => cases q <;> simp [support]
  | cons e he p ih => simp [ih]

theorem length_append (p : Walk G u v) (q : Walk G v w) :
    (p.append q).length = p.length + q.length := by
  simp [length, edges_append]

/-- Transport along equalities of the endpoints. -/
def copy (p : Walk G u v) {u' v' : V} (hu : u = u') (hv : v = v') : Walk G u' v' :=
  hu ▸ hv ▸ p

@[simp] theorem edges_copy (p : Walk G u v) {u' v' : V} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by
  subst hu hv; rfl

@[simp] theorem support_copy (p : Walk G u v) {u' v' : V} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by
  subst hu hv; rfl

/-! ### Splitting at the first occurrence of a vertex -/

theorem mem_support_nil_iff {x : V} : x ∈ (nil : Walk G u u).support ↔ x = u := by
  simp [support]

/-- The prefix up to the first occurrence of `x`. -/
noncomputable def takeUntil : ∀ {v w : V} (p : Walk G v w) (x : V), x ∈ p.support → Walk G v x
  | _, _, nil, x, h => (nil : Walk G _ _).copy rfl (mem_support_nil_iff.mp h).symm
  | v, _, cons e he p, x, h =>
    if hx : v = x then (nil : Walk G v v).copy rfl hx
    else cons e he (p.takeUntil x (by
      rcases List.mem_cons.mp h with rfl | h'
      · exact absurd rfl hx
      · exact h'))

/-- The suffix from the first occurrence of `x`. -/
noncomputable def dropUntil : ∀ {v w : V} (p : Walk G v w) (x : V), x ∈ p.support → Walk G x w
  | _, _, nil, x, h => (nil : Walk G _ _).copy (mem_support_nil_iff.mp h).symm rfl
  | v, _, cons e he p, x, h =>
    if hx : v = x then (cons e he p).copy hx rfl
    else p.dropUntil x (by
      rcases List.mem_cons.mp h with rfl | h'
      · exact absurd rfl hx
      · exact h')

theorem takeUntil_append_dropUntil (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.takeUntil x h).append (p.dropUntil x h) = p := by
  induction p with
  | nil =>
    have hx := mem_support_nil_iff.mp h
    subst hx
    rfl
  | @cons a b c e he p ih =>
    by_cases hx : a = x
    · subst hx
      simp [takeUntil, dropUntil, copy]
    · simp only [takeUntil, dropUntil, dif_neg hx, cons_append]
      rw [ih]

theorem edges_takeUntil_append (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.takeUntil x h).edges ++ (p.dropUntil x h).edges = p.edges := by
  rw [← edges_append, takeUntil_append_dropUntil]

theorem support_takeUntil (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.takeUntil x h).support = p.support.takeWhile (· ≠ x) ++ [x] := by
  induction p with
  | nil =>
    have hx := mem_support_nil_iff.mp h
    subst hx
    simp [takeUntil]
  | @cons a b c e he p ih =>
    by_cases hx : a = x
    · subst hx
      simp [takeUntil]
    · simp only [takeUntil, dif_neg hx, support_cons, ih]
      rw [List.takeWhile_cons_of_pos (by simpa using hx)]
      rfl

theorem support_dropUntil (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.dropUntil x h).support = p.support.dropWhile (· ≠ x) := by
  induction p with
  | nil =>
    have hx := mem_support_nil_iff.mp h
    subst hx
    simp [dropUntil]
  | @cons a b c e he p ih =>
    by_cases hx : a = x
    · subst hx
      simp [dropUntil]
    · simp only [dropUntil, dif_neg hx, support_cons, ih]
      rw [List.dropWhile_cons_of_pos (by simpa using hx)]

theorem isTrail_of_sublist {p : Walk G u v} {q : Walk G u' v'} (hq : q.IsTrail)
    (h : p.edges.Sublist q.edges) : p.IsTrail := hq.sublist h

theorem edges_takeUntil_sublist (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.takeUntil x h).edges.Sublist p.edges := by
  rw [← edges_takeUntil_append p x h]
  exact List.sublist_append_left _ _

theorem edges_dropUntil_sublist (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.dropUntil x h).edges.Sublist p.edges := by
  conv_rhs => rw [← edges_takeUntil_append p x h]
  exact List.sublist_append_right _ _

theorem count_support_takeUntil (p : Walk G v w) (x : V) (h : x ∈ p.support) :
    (p.takeUntil x h).support.count x = 1 := by
  rw [support_takeUntil, List.count_append, List.count_singleton_self]
  rw [List.count_eq_zero.mpr]
  intro hx
  have := List.mem_takeWhile_imp hx
  simp at this

/-! ### The degree count of a trail -/

theorem inc_insert (D : Finset E) (e : E) (x : V) :
    G.inc (insert e D) x = if x ∈ G.ends e then insert e (G.inc D x) else G.inc D x := by
  ext f
  simp only [mem_inc, mem_insert]
  split_ifs with hx
  · simp only [mem_insert, mem_inc]
    constructor
    · rintro ⟨rfl | hf, hxf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hf, hxf⟩
    · rintro (rfl | ⟨hf, hxf⟩)
      · exact ⟨Or.inl rfl, hx⟩
      · exact ⟨Or.inr hf, hxf⟩
  · simp only [mem_inc]
    constructor
    · rintro ⟨rfl | hf, hxf⟩
      · exact absurd hxf hx
      · exact ⟨hf, hxf⟩
    · rintro ⟨hf, hxf⟩
      exact ⟨Or.inr hf, hxf⟩

theorem deg_insert {D : Finset E} {e : E} (he : e ∉ D) (x : V) :
    G.deg (insert e D) x = G.deg D x + if x ∈ G.ends e then 1 else 0 := by
  rw [deg, deg, inc_insert]
  split_ifs with hx
  · rw [card_insert_of_notMem]
    intro h
    exact he (G.mem_inc.mp h).1
  · rfl

/-- **The degree count of a trail**: every interior occurrence of `x` contributes two edges,
each end one. -/
theorem deg_edgeSet_add_eq {p : Walk G u w} (hp : p.IsTrail) (x : V) :
    G.deg p.edgeSet x + ((if x = u then 1 else 0) + if x = w then 1 else 0) =
      2 * p.support.count x := by
  induction p with
  | @nil v =>
    simp only [edgeSet, edges_nil, List.toFinset_nil, support_nil, List.count_singleton]
    have : G.deg ∅ x = 0 := by simp [deg, inc]
    rw [this]
    by_cases h : x = v
    · subst h; simp
    · simp [h, Ne.symm h]
  | @cons a b c e he p ih =>
    have hp' : p.IsTrail := (List.nodup_cons.mp hp).2
    have hne : e ∉ p.edgeSet := by
      rw [mem_edgeSet]; exact (List.nodup_cons.mp hp).1
    have ih := ih hp'
    have hab := ne_of_ends he
    simp only [edgeSet, edges_cons, List.toFinset_cons] at hne ⊢
    rw [deg_insert hne, he, support_cons]
    simp only [Sym2.mem_iff]
    simp only [edgeSet] at ih
    have hite : (if x = a ∨ x = b then 1 else 0) =
        (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
      by_cases hxa : x = a <;> by_cases hxb : x = b
      · exact absurd (hxa.symm.trans hxb) hab
      · simp [hxa, hxb, hab, Ne.symm hab]
      · simp [hxa, hxb, hab, Ne.symm hab]
      · simp [hxa, hxb]
    have hcnt : (a :: p.support).count x = p.support.count x + if x = a then 1 else 0 := by
      by_cases h : x = a
      · subst h; simp [List.count_cons]
      · simp [List.count_cons, h, Ne.symm h]
    rw [hite, hcnt]
    omega

theorem mem_odd_edgeSet_iff {p : Walk G u w} (hp : p.IsTrail) {x : V} :
    x ∈ G.odd p.edgeSet ↔ Xor' (x = u) (x = w) := by
  have h := deg_edgeSet_add_eq hp x
  rw [mem_odd, Nat.odd_iff]
  by_cases hxu : x = u <;> by_cases hxw : x = w
  · rw [if_pos hxu, if_pos hxw] at h
    refine ⟨fun h' => absurd h' (by omega), fun hx => ?_⟩
    rcases hx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> contradiction
  · rw [if_pos hxu, if_neg hxw] at h
    exact ⟨fun _ => Or.inl ⟨hxu, hxw⟩, fun _ => by omega⟩
  · rw [if_neg hxu, if_pos hxw] at h
    exact ⟨fun _ => Or.inr ⟨hxw, hxu⟩, fun _ => by omega⟩
  · rw [if_neg hxu, if_neg hxw] at h
    refine ⟨fun h' => absurd h' (by omega), fun hx => ?_⟩
    rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> contradiction

/-- A closed trail has an even edge set. -/
theorem isEven_edgeSet_of_closed {p : Walk G u u} (hp : p.IsTrail) : G.IsEven p.edgeSet := by
  rw [isEven_iff_odd_eq_empty]
  refine eq_empty_of_forall_notMem fun x hx => ?_
  rw [mem_odd_edgeSet_iff hp] at hx
  simp [Xor'] at hx

/-- The boundary of an open trail. -/
theorem odd_edgeSet_of_ne {p : Walk G u w} (hp : p.IsTrail) (huw : u ≠ w) :
    G.odd p.edgeSet = {u, w} := by
  ext x
  rw [mem_odd_edgeSet_iff hp, mem_insert, mem_singleton]
  constructor
  · intro h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, huw⟩
    · exact Or.inr ⟨rfl, huw.symm⟩

theorem deg_edgeSet_of_isCycle {c : Walk G u u} (hc : c.IsCycle) : G.deg c.edgeSet u = 2 := by
  have h := deg_edgeSet_add_eq hc.2.1 u
  have hcount : c.support.count u = 2 := by
    obtain ⟨hne, -, htail⟩ := hc
    cases c with
    | nil => exact absurd rfl hne
    | cons e he p =>
      simp only [support_cons, List.count_cons, List.tail_cons] at htail ⊢
      rw [List.count_eq_one_of_mem htail (end_mem_support p)]
      simp
  simp only [if_true] at h
  omega

/-- Both ends of an edge of a walk lie on its support. -/
theorem ends_mem_support : ∀ {u w : V} {p : Walk G u w} {e : E}, e ∈ p.edges →
    ∀ x ∈ G.ends e, x ∈ p.support
  | _, _, nil, _, h => absurd h List.not_mem_nil
  | _, _, cons f hf p, e, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · intro x hx
      rw [hf, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (start_mem_support p)
    · intro x hx
      exact List.mem_cons_of_mem _ (ends_mem_support h' x hx)

/-- A path is a trail. -/
theorem isTrail_of_isPath : ∀ {u w : V} {p : Walk G u w}, p.IsPath → p.IsTrail
  | _, _, nil, _ => List.nodup_nil
  | _, _, cons e he p, h => by
    simp only [IsPath, support_cons, List.nodup_cons] at h
    simp only [IsTrail, edges_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, isTrail_of_isPath h.2⟩
    have := ends_mem_support hmem
    rw [he] at this
    exact h.1 (this _ (Sym2.mem_mk_left _ _))

theorem start_ne_end_of_isPath {p : Walk G u w} (hp : p.IsPath) (hne : p.edges ≠ []) :
    u ≠ w := by
  intro h
  subst h
  cases p with
  | nil => exact hne rfl
  | cons e he p =>
    simp only [IsPath, support_cons, List.nodup_cons] at hp
    exact hp.1 (end_mem_support p)

/-- The start of a nonempty path has degree one in its edge set. -/
theorem deg_edgeSet_start_of_isPath {p : Walk G u w} (hp : p.IsPath) (hne : p.edges ≠ []) :
    G.deg p.edgeSet u = 1 := by
  have huw := start_ne_end_of_isPath hp hne
  have h := deg_edgeSet_add_eq (isTrail_of_isPath hp) u
  rw [List.count_eq_one_of_mem hp (start_mem_support p)] at h
  simp [huw] at h
  omega

/-- A path extends by an edge to a new vertex. -/
theorem isPath_cons {p : Walk G u w} (hp : p.IsPath) {e : E} {z : V} (he : G.ends e = s(z, u))
    (hz : z ∉ p.support) : (cons e he p).IsPath :=
  List.nodup_cons.mpr ⟨hz, hp⟩

/-! ### Maximal walks -/

/-- Among the walks with a length-bounded property there is one of maximal length. -/
theorem exists_max_length (P : ∀ {a b : V}, Walk G a b → Prop) (N : ℕ)
    (hbound : ∀ {a b : V} (p : Walk G a b), P p → p.length ≤ N)
    (hex : ∃ (a b : V) (p : Walk G a b), P p) :
    ∃ (a b : V) (p : Walk G a b), P p ∧
      ∀ {a' b' : V} (q : Walk G a' b'), P q → q.length ≤ p.length := by
  obtain ⟨a, b, p, hp⟩ := hex
  have hQp : ∃ (a' b' : V) (q : Walk G a' b'), P q ∧ q.length = p.length := ⟨a, b, p, hp, rfl⟩
  obtain ⟨a', b', p', hp', hlen⟩ := Nat.findGreatest_spec
    (P := fun k => ∃ (a b : V) (p : Walk G a b), P p ∧ p.length = k) (hbound p hp) hQp
  refine ⟨a', b', p', hp', fun q hq => ?_⟩
  rw [hlen]
  by_contra hlt
  push Not at hlt
  exact Nat.findGreatest_is_greatest
    (P := fun k => ∃ (a b : V) (p : Walk G a b), P p ∧ p.length = k) hlt (hbound q hq)
    ⟨_, _, q, hq, rfl⟩

/-- The other end of an edge at `x`. -/
theorem exists_ends_eq {e : E} {x : V} (h : x ∈ G.ends e) : ∃ z, G.ends e = s(x, z) :=
  ⟨Sym2.Mem.other h, (Sym2.other_spec h).symm⟩

/-- **A maximal trail from `u` inside an even set is closed.** -/
theorem exists_closed_trail {D : Finset E} (hD : G.IsEven D) {u : V} (hu : 1 ≤ G.deg D u) :
    ∃ p : Walk G u u, p.IsTrail ∧ p.edgeSet ⊆ D ∧ p.edges ≠ [] := by
  -- a one-edge trail
  obtain ⟨e, he⟩ : (G.inc D u).Nonempty := by
    rw [← card_pos]; exact hu
  rw [mem_inc] at he
  obtain ⟨z, hz⟩ := exists_ends_eq he.2
  have hex : ∃ (a b : V) (p : Walk G a b), a = u ∧ p.IsTrail ∧ p.edgeSet ⊆ D :=
    ⟨u, z, cons e hz nil, rfl, List.nodup_singleton e, by
      intro f hf
      simp only [mem_edgeSet, edges_cons, edges_nil, List.mem_singleton] at hf
      rw [hf]; exact he.1⟩
  obtain ⟨a, b, p, ⟨rfl, hp, hpD⟩, hmax⟩ := exists_max_length
    (fun {a b} (p : Walk G a b) => a = u ∧ p.IsTrail ∧ p.edgeSet ⊆ D) D.card
    (fun p hp => length_le_card_of_isTrail hp.2.1 hp.2.2) hex
  have hlen : 1 ≤ p.length := hmax (cons e hz nil) ⟨rfl, List.nodup_singleton e, by
    intro f hf
    simp only [mem_edgeSet, edges_cons, edges_nil, List.mem_singleton] at hf
    rw [hf]; exact he.1⟩
  have hne : p.edges ≠ [] := by
    intro h; simp [length, h] at hlen
  -- the end is `u`: otherwise the trail extends
  by_cases hb : b = a
  · subst hb
    exact ⟨p, hp, hpD, hne⟩
  · exfalso
    have hodd : Odd (G.deg p.edgeSet b) := by
      rw [← mem_odd, mem_odd_edgeSet_iff hp]
      exact Or.inr ⟨rfl, hb⟩
    have hsub : G.inc p.edgeSet b ⊆ G.inc D b := G.inc_mono hpD b
    have hne' : G.inc p.edgeSet b ≠ G.inc D b := by
      intro h
      have := hD b
      rw [deg, ← h] at this
      exact (Nat.not_even_iff_odd.mpr hodd) this
    obtain ⟨f, hfD, hfp⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hsub hne')
    rw [mem_inc] at hfD hfp
    obtain ⟨z', hz'⟩ := exists_ends_eq hfD.2
    have hfnot : f ∉ p.edges := fun h => hfp ⟨mem_edgeSet.mpr h, hfD.2⟩
    have hq := hmax (p.append (cons f hz' nil)) ⟨rfl, ?_, ?_⟩
    · rw [length_append] at hq
      simp [length] at hq
    · rw [IsTrail, edges_append, edges_cons, edges_nil, List.nodup_append]
      exact ⟨hp, List.nodup_singleton f, by
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        rw [hy] at hxy
        rw [hxy] at hx
        exact hfnot hx⟩
    · intro g hg
      simp only [mem_edgeSet, edges_append, edges_cons, edges_nil, List.mem_append,
        List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hpD (mem_edgeSet.mpr hg)
      · exact hfD.1

/-- **A nonempty closed trail contains a cycle at its base.** -/
theorem exists_cycle_of_closed_trail : ∀ (n : ℕ) {u : V} (p : Walk G u u), p.length = n →
    p.IsTrail → p.edges ≠ [] → ∃ c : Walk G u u, c.IsCycle ∧ c.edgeSet ⊆ p.edgeSet := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u p hlen hp hne
  by_cases hnd : p.support.tail.Nodup
  · exact ⟨p, ⟨hne, hp, hnd⟩, subset_rfl⟩
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ v _ e he q =>
  simp only [support_cons, List.tail_cons] at hnd
  -- a repeated vertex of `q.support`
  obtain ⟨y, hy⟩ : ∃ y, 1 < q.support.count y := by
    by_contra h
    push Not at h
    exact hnd (List.nodup_iff_count_le_one.mpr h)
  have hymem : y ∈ q.support := List.count_pos_iff.mp (by omega)
  set A := q.takeUntil y hymem with hA
  set R := q.dropUntil y hymem with hR
  have hsplit : A.append R = q := takeUntil_append_dropUntil q y hymem
  have hcount : q.support.count y = 1 + R.support.tail.count y := by
    conv_lhs => rw [← hsplit]
    rw [support_append, List.count_append, count_support_takeUntil]
  have hyR : y ∈ R.support.tail := List.count_pos_iff.mp (by omega)
  -- `R` is nonempty
  cases hRc : R with
  | nil => rw [hRc] at hyR; simp at hyR
  | @cons _ y' _ f hf R' =>
  rw [hRc] at hyR
  simp only [support_cons, List.tail_cons] at hyR
  set R'' := R'.dropUntil y hyR with hR''
  -- the shortcut
  have hR''sub : R''.edges.Sublist R'.edges := edges_dropUntil_sublist R' y hyR
  have hsub : (A.append R'').edges.Sublist q.edges := by
    conv_rhs => rw [← hsplit]
    rw [edges_append, edges_append, hRc, edges_cons]
    exact (hR''sub.trans (List.sublist_cons_self f _)).append_left _
  have hlt : (cons e he (A.append R'')).length < n := by
    rw [← hlen]
    simp only [length, edges_cons, List.length_cons, edges_append]
    have h1 : (A.edges ++ R.edges).length = q.edges.length := by
      rw [← edges_append, hsplit]
    rw [hRc, edges_cons] at h1
    have h2 : R''.edges.length ≤ R'.edges.length := hR''sub.length_le
    simp only [List.length_append, List.length_cons] at h1 h2 ⊢
    omega
  obtain ⟨c, hc, hcsub⟩ := ih _ hlt (cons e he (A.append R'')) rfl
    (by
      rw [IsTrail, edges_cons, List.nodup_cons]
      rw [IsTrail, edges_cons, List.nodup_cons] at hp
      exact ⟨fun h => hp.1 (hsub.subset h), hp.2.sublist hsub⟩)
    (by simp)
  refine ⟨c, hc, hcsub.trans fun g hg => ?_⟩
  rw [mem_edgeSet, edges_cons] at hg ⊢
  rcases List.mem_cons.mp hg with rfl | hg
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hsub.subset hg)

/-- **An even edge set with an edge at `u` contains a cycle at `u`.** -/
theorem exists_cycle_of_isEven {D : Finset E} (hD : G.IsEven D) {u : V} (hu : 1 ≤ G.deg D u) :
    ∃ c : Walk G u u, c.IsCycle ∧ c.edgeSet ⊆ D := by
  obtain ⟨p, hp, hpD, hne⟩ := exists_closed_trail hD hu
  obtain ⟨c, hc, hcp⟩ := exists_cycle_of_closed_trail p.length p rfl hp hne
  exact ⟨c, hc, hcp.trans hpD⟩

/-- **The two arcs of a cycle** through a second vertex `y`: two trails `u → y` and `y → u`
partitioning its edges. -/
theorem exists_arcs {c : Walk G u u} (hc : c.IsCycle) {y : V} (hy : y ∈ c.support) :
    ∃ (A : Walk G u y) (B : Walk G y u), A.IsTrail ∧ B.IsTrail ∧
      Disjoint A.edgeSet B.edgeSet ∧ A.edgeSet ∪ B.edgeSet = c.edgeSet := by
  refine ⟨c.takeUntil y hy, c.dropUntil y hy, hc.2.1.sublist (edges_takeUntil_sublist c y hy),
    hc.2.1.sublist (edges_dropUntil_sublist c y hy), ?_, ?_⟩
  · have h := hc.2.1
    rw [← edges_takeUntil_append c y hy, List.nodup_append] at h
    rw [Finset.disjoint_left]
    intro g hgA hgB
    rw [mem_edgeSet] at hgA hgB
    exact h.2.2 g hgA g hgB rfl
  · rw [edgeSet, edgeSet, edgeSet, ← List.toFinset_append, edges_takeUntil_append]

/-! ### Longest paths in a forest -/

/-- A nonempty edge set carries a longest path. -/
theorem exists_longest_path {J : Finset E} (hJ : J.Nonempty) :
    ∃ (a b : V) (p : Walk G a b), p.IsPath ∧ p.edgeSet ⊆ J ∧ p.edges ≠ [] ∧
      ∀ {a' b' : V} (q : Walk G a' b'), q.IsPath → q.edgeSet ⊆ J → q.length ≤ p.length := by
  obtain ⟨e, he⟩ := hJ
  obtain ⟨a, b, hab⟩ : ∃ a b, G.ends e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) (G.ends e)
  have hne := ne_of_ends hab
  have hone : (cons e hab nil : Walk G a b).IsPath ∧ (cons e hab nil).edgeSet ⊆ J :=
    ⟨by simp [IsPath, support, hne], by
      intro f hf
      simp only [mem_edgeSet, edges_cons, edges_nil, List.mem_singleton] at hf
      rw [hf]; exact he⟩
  obtain ⟨a', b', p, ⟨hp, hpJ⟩, hmax⟩ := exists_max_length
    (fun {a b} (p : Walk G a b) => p.IsPath ∧ p.edgeSet ⊆ J) (Fintype.card V)
    (fun p hp => by have := length_le_card_of_isPath hp.1; omega) ⟨a, b, _, hone⟩
  refine ⟨a', b', p, hp, hpJ, ?_, fun q hq hqJ => hmax q ⟨hq, hqJ⟩⟩
  have h1 := hmax _ hone
  intro h
  simp [length, h] at h1

/-- **The start of a longest path in a forest has degree one.**  A forest here is an edge
set with no nonempty even subset. -/
theorem deg_eq_one_of_longest {J : Finset E} (hJ : ∀ C, G.IsEven C → C ⊆ J → C = ∅)
    {a b : V} {p : Walk G a b} (hp : p.IsPath) (hpJ : p.edgeSet ⊆ J) (hne : p.edges ≠ [])
    (hmax : ∀ {a' b' : V} (q : Walk G a' b'), q.IsPath → q.edgeSet ⊆ J →
      q.length ≤ p.length) :
    G.deg J a = 1 := by
  have h1 := deg_edgeSet_start_of_isPath hp hne
  have hsub : G.inc p.edgeSet a ⊆ G.inc J a := G.inc_mono hpJ a
  by_contra hdeg
  have hlt : G.deg p.edgeSet a < G.deg J a := by
    have h2 : (G.inc p.edgeSet a).card ≤ (G.inc J a).card := card_le_card hsub
    have h3 : (G.inc J a).card ≠ 1 := hdeg
    have h4 : (G.inc p.edgeSet a).card = 1 := h1
    change (G.inc p.edgeSet a).card < (G.inc J a).card
    omega
  obtain ⟨f, hfJ, hfp⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hsub (fun h => by
    rw [deg, deg, h] at hlt; exact lt_irrefl _ hlt))
  rw [mem_inc] at hfJ hfp
  obtain ⟨z, hz⟩ := exists_ends_eq hfJ.2
  have hfnot : f ∉ p.edges := fun h => hfp ⟨mem_edgeSet.mpr h, hfJ.2⟩
  have hz' : G.ends f = s(z, a) := by rw [hz, Sym2.eq_swap]
  by_cases hzp : z ∈ p.support
  · -- close a cycle inside `J`
    set A := p.takeUntil z hzp with hA
    set C : Walk G a a := A.append (cons f hz' nil) with hC
    have hCtrail : C.IsTrail := by
      rw [IsTrail, hC, edges_append, edges_cons, edges_nil, List.nodup_append]
      refine ⟨(isTrail_of_isPath hp).sublist (edges_takeUntil_sublist p z hzp),
        List.nodup_singleton f, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      rw [hy] at hxy
      rw [hxy] at hx
      exact hfnot ((edges_takeUntil_sublist p z hzp).subset hx)
    have hCsub : C.edgeSet ⊆ J := by
      intro g hg
      simp only [mem_edgeSet, hC, edges_append, edges_cons, edges_nil, List.mem_append,
        List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hpJ (mem_edgeSet.mpr ((edges_takeUntil_sublist p z hzp).subset hg))
      · exact hfJ.1
    have hCne : C.edgeSet.Nonempty := ⟨f, by
      rw [mem_edgeSet, hC, edges_append, edges_cons, edges_nil]; simp⟩
    have := hJ _ (isEven_edgeSet_of_closed hCtrail) hCsub
    rw [this] at hCne
    exact not_nonempty_empty hCne
  · -- extend the path
    have hq := hmax (cons f hz' p) (isPath_cons hp hz' hzp) (by
      intro g hg
      rw [mem_edgeSet, edges_cons] at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hfJ.1
      · exact hpJ (mem_edgeSet.mpr hg))
    simp [length] at hq

end Walk

end MGraph
end TSPGap

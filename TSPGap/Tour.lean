/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# The output layer: shortcutting a spanning closed walk into a tour

KKO's algorithm outputs a *multiset* of edges — a spanning tree together with
an O-join — which is connected and has even degrees, hence carries an Eulerian
circuit.  The theorem's conclusion, however, is about a **Hamiltonian cycle**:
the Euler tour must be shortcut, and under the triangle inequality this does
not raise the cost.  That step is what this file supplies, and it is proved in
full — no assumption of the KKO development enters here.

The route is deliberately list-theoretic:

* `listCost c l` is the cost of travelling through the vertices of `l` in
  order.  A walk's cost is the cost of its support (`sum_edges_eq_listCost`).
* **Shortcutting** (`listCost_le_of_sublist`): deleting vertices from a route
  never increases its cost.  The induction is over `List.Sublist`, and its two
  interesting steps are exactly the two reasons a deletion is safe — the
  triangle inequality when the deleted vertex is passed through, and
  nonnegativity when it is dropped from the end.
* `walkOfChain` builds the walk through a list of vertices; in the complete
  graph the only condition is that consecutive entries differ.
* `exists_hamiltonianCycle_of_nodup` turns a duplicate-free listing of every
  vertex into a Hamiltonian cycle of exactly the list's cost.

Composing them, `exists_hamiltonianCycle_le_of_spanning_walk` shortcuts any
closed walk through all the vertices to a Hamiltonian cycle of no greater
cost: `List.dedup` picks out the tour order (it keeps *last* occurrences, so
the walk's final return to its start survives, which is what closes the
cycle).
-/

namespace TSPGap

open SimpleGraph

variable {n : ℕ} {c : Sym2 (Fin n) → ℝ}

/-! ### Two facts about `getLastD` -/

/-- The default of `getLastD` is irrelevant on a nonempty list. -/
theorem getLastD_congr {α : Type*} {l : List α} (h : l ≠ []) (a b : α) :
    l.getLastD a = l.getLastD b := by
  obtain ⟨z, hz⟩ : ∃ z, l.getLast? = some z := ⟨l.getLast h, List.getLast?_eq_getLast h⟩
  simp [List.getLastD_eq_getLast?, hz]

/-- The last entry of a nonempty list belongs to it. -/
theorem getLastD_mem {α : Type*} : ∀ {l : List α}, l ≠ [] → ∀ a : α, l.getLastD a ∈ l
  | [], h, _ => absurd rfl h
  | _ :: _, _, a => by
      rw [List.getLastD_cons]
      exact List.getLastD_mem_cons

/-- **Deduplication keeps the last entry.**  `List.dedup` retains the final
occurrence of each vertex, so the end of the route is preserved — which is
what lets a closed walk be shortcut to a *cycle*. -/
theorem getLastD_dedup {α : Type*} [DecidableEq α] :
    ∀ (l : List α) (a : α), l.dedup.getLastD a = l.getLastD a
  | [], _ => rfl
  | b :: t, a => by
      by_cases hb : b ∈ t
      · rw [List.dedup_cons_of_mem hb, getLastD_dedup t a, List.getLastD_cons]
        exact getLastD_congr (List.ne_nil_of_mem hb) a b
      · rw [List.dedup_cons_of_notMem hb, List.getLastD_cons, List.getLastD_cons,
          getLastD_dedup t b]

/-! ### The cost of a route -/

/-- The cost of travelling through a list of vertices in order. -/
def listCost (c : Sym2 (Fin n) → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: t => c s(a, b) + listCost c (b :: t)

@[simp] theorem listCost_nil : listCost c [] = 0 := rfl

@[simp] theorem listCost_singleton (a : Fin n) : listCost c [a] = 0 := rfl

@[simp] theorem listCost_cons_cons (a b : Fin n) (t : List (Fin n)) :
    listCost c (a :: b :: t) = c s(a, b) + listCost c (b :: t) := rfl

/-- **Going through `a` first cannot be cheaper**: the triangle inequality
when the route continues, nonnegativity when it stops. -/
theorem listCost_cons_le (hc : IsMetric c) (v a : Fin n) (l : List (Fin n)) :
    listCost c (v :: l) ≤ c s(v, a) + listCost c (a :: l) := by
  cases l with
  | nil => simpa using hc.nonneg s(v, a)
  | cons b t =>
      have h := hc.triangle v a b
      rw [listCost_cons_cons, listCost_cons_cons]
      linarith

/-- **Shortcutting.**  Deleting vertices from a route never increases its
cost.  Each deletion is either passed over by the triangle inequality
(`cons`) or dropped from the end, where costs are nonnegative. -/
theorem listCost_le_of_sublist (hc : IsMetric c) {m l : List (Fin n)}
    (h : m.Sublist l) : ∀ v : Fin n, listCost c (v :: m) ≤ listCost c (v :: l) := by
  induction h with
  | slnil => intro v; exact le_rfl
  | cons a h ih =>
      intro v
      calc listCost c (v :: _) ≤ listCost c (v :: _) := ih v
        _ ≤ c s(v, a) + listCost c (a :: _) := listCost_cons_le hc v a _
        _ = listCost c (v :: a :: _) := (listCost_cons_cons v a _).symm
  | cons_cons a h ih =>
      intro v
      rw [listCost_cons_cons, listCost_cons_cons]
      linarith [ih a]

/-! ### Walks through a list of vertices -/

/-- Consecutive entries of a duplicate-free list differ. -/
theorem isChain_ne_of_nodup : ∀ {l : List (Fin n)}, l.Nodup →
    List.IsChain (· ≠ ·) l
  | [], _ => List.IsChain.nil
  | [a], _ => List.IsChain.singleton a
  | a :: b :: t, h => by
      rw [List.nodup_cons] at h
      exact List.isChain_cons_cons.mpr
        ⟨fun hab => h.1 (by rw [hab]; simp), isChain_ne_of_nodup h.2⟩

/-- **The walk through a list of vertices.**  In the complete graph the only
requirement is that consecutive entries differ; the endpoint is carried as a
parameter so that no dependent rewriting is needed. -/
def walkOfChain : ∀ (u v : Fin n) (l : List (Fin n)),
    List.IsChain (· ≠ ·) (u :: l) → (u :: l).getLastD u = v →
    (⊤ : SimpleGraph (Fin n)).Walk u v
  | u, v, [], _, h =>
      SimpleGraph.Walk.nil.copy rfl (by
        rw [List.getLastD_cons, List.getLastD_nil] at h; exact h)
  | _, v, a :: t, hch, h =>
      SimpleGraph.Walk.cons (by simpa using (List.isChain_cons_cons.mp hch).1)
        (walkOfChain a v t (List.isChain_cons_cons.mp hch).2 (by
          rw [List.getLastD_cons] at h ⊢
          rw [List.getLastD_cons] at h
          exact h))

theorem support_walkOfChain (v : Fin n) : ∀ (u : Fin n) (l : List (Fin n))
    (hch : List.IsChain (· ≠ ·) (u :: l)) (h : (u :: l).getLastD u = v),
    (walkOfChain u v l hch h).support = u :: l := by
  intro u l
  induction l generalizing u with
  | nil => intro hch h; simp [walkOfChain]
  | cons a t ih => intro hch h; simp [walkOfChain, ih]

theorem edges_walkOfChain_cons (v u a : Fin n) (t : List (Fin n))
    (hch : List.IsChain (· ≠ ·) (u :: a :: t)) (h : (u :: a :: t).getLastD u = v) :
    (walkOfChain u v (a :: t) hch h).edges =
      s(u, a) :: (walkOfChain a v t (List.isChain_cons_cons.mp hch).2 (by
        rw [List.getLastD_cons] at h ⊢
        rw [List.getLastD_cons] at h
        exact h)).edges := by
  rw [walkOfChain, SimpleGraph.Walk.edges_cons]

/-- A walk costs what its support costs. -/
theorem sum_edges_eq_listCost {u v : Fin n}
    (w : (⊤ : SimpleGraph (Fin n)).Walk u v) :
    (w.edges.map c).sum = listCost c w.support := by
  induction w with
  | nil => rfl
  | cons h p ih =>
      rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, ih,
        SimpleGraph.Walk.support_cons]
      conv_rhs => rw [← SimpleGraph.Walk.cons_tail_support p]
      rw [listCost_cons_cons, SimpleGraph.Walk.cons_tail_support]

/-! ### A tour order becomes a Hamiltonian cycle -/

/-- **A Hamiltonian cycle from a tour order.**  If `m` lists every vertex
exactly once and ends where the tour began, the walk through `v :: m` is a
Hamiltonian cycle of exactly the route's cost.

The cycle conditions come out of the listing: the interior is duplicate-free,
so the walk is a path (`IsPath.mk'`); and the closing edge `{v, w}` is new
because `w`'s only neighbour along the path is the second entry, which is not
`v` — that is where the third vertex is needed, hence `3 ≤ n`. -/
theorem exists_hamiltonianCycle_of_nodup (hn : 3 ≤ n) {v : Fin n}
    {m : List (Fin n)} (hnd : m.Nodup) (hall : ∀ u : Fin n, u ∈ m)
    (hlast : m.getLastD v = v) :
    ∃ H : (⊤ : SimpleGraph (Fin n)).Walk v v,
      H.IsHamiltonianCycle ∧ tourCost c H = listCost c (v :: m) := by
  classical
  have hcard : m.length = n := by
    have huniv : m.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun u => List.mem_toFinset.mpr (hall u)
    have hc := List.toFinset_card_of_nodup hnd
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hc
    exact hc.symm
  -- the listing has at least three entries
  obtain ⟨w, w₂, m₃, rfl⟩ : ∃ w w₂ m₃, m = w :: w₂ :: m₃ := by
    rcases m with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hcard; omega
    · simp at hcard; omega
    · exact ⟨a, b, t, rfl⟩
  rw [List.nodup_cons, List.nodup_cons] at hnd
  obtain ⟨hw, hw₂, hnd₃⟩ := hnd
  simp only [List.length_cons] at hcard
  have hm₃ : m₃ ≠ [] := by
    rintro rfl
    simp at hcard
    omega
  -- the tour's far end is `v`
  rw [List.getLastD_cons, List.getLastD_cons] at hlast
  have hvm₃ : v ∈ m₃ := hlast ▸ getLastD_mem hm₃ w₂
  have hvw₂ : v ≠ w₂ := fun h => hw₂ (h ▸ hvm₃)
  have hvw : v ≠ w := by
    intro hvw'
    exact hw (by rw [← hvw']; exact List.mem_cons_of_mem _ hvm₃)
  -- the path through the listing, and the edge closing it
  have hnd' : (w :: w₂ :: m₃).Nodup := by
    rw [List.nodup_cons, List.nodup_cons]; exact ⟨hw, hw₂, hnd₃⟩
  have hch : List.IsChain (· ≠ ·) (w :: w₂ :: m₃) := isChain_ne_of_nodup hnd'
  have hend : (w :: w₂ :: m₃).getLastD w = v := by
    rw [List.getLastD_cons, List.getLastD_cons]; exact hlast
  set p : (⊤ : SimpleGraph (Fin n)).Walk w v := walkOfChain w v (w₂ :: m₃) hch hend
    with hp
  have hsupp : p.support = w :: w₂ :: m₃ := support_walkOfChain v w _ hch hend
  have hpath : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by rw [hsupp]; exact hnd')
  have hedge : s(v, w) ∉ p.edges := by
    rw [hp, edges_walkOfChain_cons]
    simp only [List.mem_cons]
    rintro (heq | hmem)
    · rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvw h1
      · exact hvw₂ h1
    · have hmemw := SimpleGraph.Walk.snd_mem_support_of_mem_edges _ hmem
      rw [support_walkOfChain] at hmemw
      exact hw hmemw
  refine ⟨SimpleGraph.Walk.cons (by simpa using hvw) p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
    refine ⟨(SimpleGraph.Walk.cons_isCycle_iff p _).mpr ⟨hpath, hedge⟩, ?_⟩
    have hlen : p.length + 1 = (w :: w₂ :: m₃).length := by
      have hls := SimpleGraph.Walk.length_support p
      rw [hsupp] at hls
      omega
    rw [SimpleGraph.Walk.length_cons, Fintype.card_fin]
    simp only [List.length_cons] at hcard hlen ⊢
    omega
  · rw [tourCost, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
      listCost_cons_cons, sum_edges_eq_listCost, hsupp]

/-! ### Shortcutting a spanning closed walk -/

/-- **Shortcutting a closed route.**  A list that starts at `v`, ends at `v`
and hits every vertex shortcuts to a Hamiltonian cycle of no greater cost.

`List.dedup` of the route is the tour order:
it is duplicate-free, still lists every vertex, and — because `dedup` keeps
*last* occurrences — still ends where the walk returns, so the cycle closes.
`listCost_le_of_sublist` then does the metric work. -/
theorem exists_hamiltonianCycle_le_of_list (hc : IsMetric c) (hn : 3 ≤ n)
    {v : Fin n} {L : List (Fin n)} (hall : ∀ u : Fin n, u ∈ v :: L)
    (hlast : L.getLastD v = v) :
    ∃ H : (⊤ : SimpleGraph (Fin n)).Walk v v,
      H.IsHamiltonianCycle ∧ tourCost c H ≤ listCost c (v :: L) := by
  classical
  -- another vertex exists, so the route really moves
  obtain ⟨z, hz⟩ : ∃ z : Fin n, z ≠ v := by
    rcases eq_or_ne (⟨0, by omega⟩ : Fin n) v with h | h
    · exact ⟨⟨1, by omega⟩, by rw [← h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, h⟩
  have hLne : L ≠ [] := by
    intro h
    have hzs := hall z
    rw [h, List.mem_singleton] at hzs
    exact hz hzs
  -- the tour order
  have hnd : L.dedup.Nodup := List.nodup_dedup _
  have hall' : ∀ u : Fin n, u ∈ L.dedup := by
    intro u
    rw [List.mem_dedup]
    rcases eq_or_ne u v with rfl | hne
    · have hmem := getLastD_mem hLne u
      rwa [hlast] at hmem
    · exact (List.mem_cons.mp (hall u)).resolve_left hne
  have hlast' : L.dedup.getLastD v = v := by
    rw [getLastD_dedup, hlast]
  obtain ⟨H, hham, hcost⟩ :=
    exists_hamiltonianCycle_of_nodup (c := c) hn hnd hall' hlast'
  refine ⟨H, hham, ?_⟩
  rw [hcost]
  exact listCost_le_of_sublist hc (List.dedup_sublist _) v

/-- **The output layer.**  A closed walk through every vertex can be shortcut
to a Hamiltonian cycle of no greater cost. -/
theorem exists_hamiltonianCycle_le_of_spanning_walk (hc : IsMetric c)
    (hn : 3 ≤ n) {v : Fin n} (W : (⊤ : SimpleGraph (Fin n)).Walk v v)
    (hall : ∀ u : Fin n, u ∈ W.support) :
    ∃ H : (⊤ : SimpleGraph (Fin n)).Walk v v,
      H.IsHamiltonianCycle ∧ tourCost c H ≤ tourCost c W := by
  classical
  have hsupp : W.support = v :: W.support.tail :=
    (SimpleGraph.Walk.cons_tail_support W).symm
  have hlastW : W.support.getLastD v = v := by
    have h1 : W.support.getLast? = some v := by
      rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support]
    simp [List.getLastD_eq_getLast?, h1]
  have hlastL : W.support.tail.getLastD v = v := by
    conv_lhs => rw [← List.getLastD_cons (a := v) (b := v) (l := W.support.tail)]
    rw [← hsupp, hlastW]
  have hall' : ∀ u : Fin n, u ∈ v :: W.support.tail := by
    intro u; rw [← hsupp]; exact hall u
  obtain ⟨H, hham, hcost⟩ :=
    exists_hamiltonianCycle_le_of_list (c := c) hc hn hall' hlastL
  refine ⟨H, hham, hcost.trans (le_of_eq ?_)⟩
  rw [tourCost, sum_edges_eq_listCost]
  conv_rhs => rw [hsupp]

end TSPGap

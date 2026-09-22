/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerArrangement

/-!
# The core step of Tucker's Theorem 6: distances, diameter points, Lemmas 2 and 4

Distances between elements in the incidence graph (`edist`), the bridge between chains of
sets and walks, the triangle inequality for reachable vertices, Tucker's Lemma 4 in
distance form (`edist_le_of_between`, non-strict — the strict form in the paper is false,
see `TUCKER_DESIGN.md`), diameter points and their existence, and Lemma 2: deleting a
diameter point keeps the elements mutually reachable, provided every set has at least two
elements of `O` (`isConnected_erase_of_diameterPoint`).  Lemma 5, the rotation claim and the
final order follow in the next tranche, which will discharge `CoreStep α`.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-! ### Distances between elements -/

/-- The distance between two elements in the incidence graph. -/
noncomputable def edist (O : Finset α) (F : Finset (Finset α)) (x z : α) : ℕ :=
  (incGraph O F).dist (Sum.inl x) (Sum.inl z)

omit [DecidableEq α] in
theorem edist_comm {O : Finset α} {F : Finset (Finset α)} {x z : α} :
    edist O F x z = edist O F z x := SimpleGraph.dist_comm

omit [DecidableEq α] in
/-- The triangle inequality between reachable vertices. -/
theorem dist_triangle_of_reachable {V : Type*} {G : SimpleGraph V} {u v w : V}
    (h₁ : G.Reachable u v) (h₂ : G.Reachable v w) : G.dist u w ≤ G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := h₁.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := h₂.exists_walk_length_eq_dist
  have := SimpleGraph.dist_le (p.append q)
  rwa [SimpleGraph.Walk.length_append, hp, hq] at this

omit [DecidableEq α] in
/-- A share step is a two-edge walk. -/
theorem reachable_of_shareStep {O : Finset α} {F : Finset (Finset α)} {a b : α}
    (h : ShareStep O F a b) : (incGraph O F).Reachable (Sum.inl a) (Sum.inl b) :=
  let ⟨ha, hb, _, hS, haS, hbS⟩ := h
  (incGraph_adj_inl_inr.mpr ⟨ha, hS, haS⟩).reachable.trans
    (incGraph_adj_inr_inl.mpr ⟨hb, hS, hbS⟩).reachable

omit [DecidableEq α] in
theorem reachable_of_reach {O : Finset α} {F : Finset (Finset α)} {a b : α} (h : Reach O F a b) :
    (incGraph O F).Reachable (Sum.inl a) (Sum.inl b) := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans (reachable_of_shareStep hbc)

/-- Along a walk of the incidence graph avoiding the vertex `inl p`, elements are joined by
chains of sets inside `O.erase p`. -/
theorem reach_erase_of_walk {O : Finset α} {F : Finset (Finset α)} {p : α}
    {v w : α ⊕ Finset α} (q : (incGraph O F).Walk v w) (hp : Sum.inl p ∉ q.support) :
    (∀ x z, v = Sum.inl x → w = Sum.inl z → Reach (O.erase p) F x z) ∧
      (∀ S z, v = Sum.inr S → w = Sum.inl z → S ∈ F → ∀ a ∈ O, a ≠ p → a ∈ S →
        Reach (O.erase p) F a z) := by
  induction q with
  | nil =>
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 => ?_⟩
    · rw [h1, Sum.inl.injEq] at h2
      subst h2
      exact Relation.ReflTransGen.refl
    · rw [h1] at h2
      exact absurd h2 (by simp)
  | @cons v v' w huv q ih =>
    have hq : Sum.inl p ∉ q.support := fun h =>
      hp (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ h)
    have ih' := ih hq
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 hS a ha hap haS => ?_⟩
    · subst h1
      rcases v' with b | S
      · exact absurd huv incGraph_not_adj_inl_inl
      · have h := incGraph_adj_inl_inr.mp huv
        have hxp : x ≠ p := fun hxp =>
          hp (by rw [SimpleGraph.Walk.support_cons, hxp]; exact List.mem_cons_self ..)
        exact ih'.2 S z rfl h2 h.2.1 x h.1 hxp h.2.2
    · subst h1
      rcases v' with b | T
      · have h := incGraph_adj_inr_inl.mp huv
        have hbp : b ≠ p := by
          intro hbp
          subst hbp
          exact hq q.start_mem_support
        exact Relation.ReflTransGen.head
          ⟨Finset.mem_erase.mpr ⟨hap, ha⟩, Finset.mem_erase.mpr ⟨hbp, h.1⟩, S, hS, haS, h.2.2⟩
          (ih'.1 b z rfl h2)
      · exact absurd huv incGraph_not_adj_inr_inr

/-! ### Lemma 4 in distance form -/

omit [DecidableEq α] in
/-- A walk between elements not avoiding `y ∈ O` passes through a set containing `y`. -/
theorem exists_mem_support_of_not_avoiding {O : Finset α} {F : Finset (Finset α)} {y x z : α}
    {q : (incGraph O F).Walk (Sum.inl x) (Sum.inl z)}
    (h : ¬ ∀ v ∈ q.support, ¬ (incGraph O F).Adj v (Sum.inl y)) :
    ∃ S, Sum.inr S ∈ q.support ∧ S ∈ F ∧ y ∈ S := by
  push Not at h
  obtain ⟨v, hv, hadj⟩ := h
  rcases v with a | S
  · exact absurd hadj incGraph_not_adj_inl_inl
  · exact ⟨S, hv, (incGraph_adj_inr_inl.mp hadj).2.1, (incGraph_adj_inr_inl.mp hadj).2.2⟩

/-- **Tucker's Lemma 4, distance form (non-strict).**  In a consecutive-ones order with
`x < y < z`, `d(x, y) ≤ d(x, z)` and `d(y, z) ≤ d(x, z)`. -/
theorem edist_le_of_between {O : Finset α} {F : Finset (Finset α)} {L : List α}
    (hL : L.toFinset = O) (hC : IsC1PList L F) {x y z : α} (hy : y ∈ L)
    (hxy : L.idxOf x < L.idxOf y) (hyz : L.idxOf y < L.idxOf z)
    (hr : (incGraph O F).Reachable (Sum.inl x) (Sum.inl z)) :
    edist O F x y ≤ edist O F x z ∧ edist O F y z ≤ edist O F x z := by
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  have hyO : y ∈ O := by rw [← hL]; exact List.mem_toFinset.mpr hy
  have hmeet : ∃ S, Sum.inr S ∈ q.support ∧ S ∈ F ∧ y ∈ S := by
    refine exists_mem_support_of_not_avoiding fun hav => ?_
    have hside := idxOf_side_of_avoidChain hL hC hy ((avoidingPath_iff_chain hyO).mp ⟨q, hav⟩)
    have h1 : ¬ L.idxOf y < L.idxOf x := by omega
    exact h1 (hside.mpr hyz)
  obtain ⟨S, hS, hSF, hyS⟩ := hmeet
  have hspec := q.take_spec hS
  have hlen : (q.takeUntil _ hS).length + (q.dropUntil _ hS).length = q.length := by
    rw [← SimpleGraph.Walk.length_append, hspec]
  have hdrop : 1 ≤ (q.dropUntil _ hS).length := by
    by_contra h0
    have : (q.dropUntil _ hS).length = 0 := by omega
    have := SimpleGraph.Walk.exists_length_eq_zero_iff.mp ⟨_, this⟩
    exact absurd this (by simp)
  have htake : 1 ≤ (q.takeUntil _ hS).length := by
    by_contra h0
    have : (q.takeUntil _ hS).length = 0 := by omega
    have := SimpleGraph.Walk.exists_length_eq_zero_iff.mp ⟨_, this⟩
    exact absurd this (by simp)
  have hadj : (incGraph O F).Adj (Sum.inr S) (Sum.inl y) := incGraph_adj_inr_inl.mpr ⟨hyO, hSF, hyS⟩
  constructor
  · have := SimpleGraph.dist_le
      ((q.takeUntil _ hS).append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at this
    unfold edist
    omega
  · have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj.symm (q.dropUntil _ hS))
    rw [SimpleGraph.Walk.length_cons] at this
    unfold edist
    omega

/-! ### Diameter points and Lemma 2 -/

/-- `p` is a *diameter point*: some `q` realizes the maximum distance between elements. -/
def IsDiameterPoint (O : Finset α) (F : Finset (Finset α)) (p : α) : Prop :=
  p ∈ O ∧ ∃ q ∈ O, ∀ a ∈ O, ∀ b ∈ O, edist O F a b ≤ edist O F p q

omit [DecidableEq α] in
theorem exists_diameterPoint {O : Finset α} (F : Finset (Finset α)) (hO : O.Nonempty) :
    ∃ p, IsDiameterPoint O F p := by
  obtain ⟨⟨p, q⟩, hpq, hmax⟩ :=
    Finset.exists_max_image (O ×ˢ O) (fun ab => edist O F ab.1 ab.2) (hO.product hO)
  exact ⟨p, (Finset.mem_product.mp hpq).1, q, (Finset.mem_product.mp hpq).2,
    fun a ha b hb => hmax (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)⟩

/-- Distinct reachable vertices are at positive distance. -/
theorem one_le_dist_of_ne {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Reachable u v)
    (hne : u ≠ v) : 1 ≤ G.dist u v := by
  by_contra h0
  have : G.dist u v = 0 := by omega
  exact hne ((h.dist_eq_zero_iff).mp this)

/-- **Tucker's Lemma 2** (with the size hypothesis).  Deleting a diameter point keeps the
elements mutually reachable, provided every set has at least two elements of `O`. -/
theorem isConnected_erase_of_diameterPoint {O : Finset α} {F : Finset (Finset α)}
    (hconn : IsConnected O F) {p : α} (hp : IsDiameterPoint O F p) :
    IsConnected (O.erase p) F := by
  obtain ⟨hpO, q, hqO, hmax⟩ := hp
  -- every element other than `p` reaches `q` inside `O.erase p`
  have key : ∀ v ∈ O.erase p, Reach (O.erase p) F v q := by
    intro v hv
    obtain ⟨hvp, hvO⟩ := Finset.mem_erase.mp hv
    have hr : (incGraph O F).Reachable (Sum.inl v) (Sum.inl q) :=
      reachable_of_reach (hconn v hvO q hqO)
    obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
    have hnot : Sum.inl p ∉ w.support := by
      intro hpw
      have hspec := w.take_spec hpw
      have hlen : (w.takeUntil _ hpw).length + (w.dropUntil _ hpw).length = w.length := by
        rw [← SimpleGraph.Walk.length_append, hspec]
      have h1 := SimpleGraph.dist_le (w.takeUntil _ hpw)
      have h2 := SimpleGraph.dist_le (w.dropUntil _ hpw)
      have h3 : 1 ≤ (incGraph O F).dist (Sum.inl v) (Sum.inl p) :=
        one_le_dist_of_ne (w.takeUntil _ hpw).reachable (by simpa using hvp)
      have h4 := hmax v hvO q hqO
      unfold edist at h4
      omega
    exact (reach_erase_of_walk w hnot).1 v q rfl rfl
  intro a ha b hb
  -- `q ≠ p` unless `O.erase p` is empty
  have hqp : q ∈ O.erase p := by
    refine Finset.mem_erase.mpr ⟨fun hqp => ?_, hqO⟩
    subst hqp
    obtain ⟨hap, haO⟩ := Finset.mem_erase.mp ha
    have h1 := hmax a haO q hqO
    have hr : (incGraph O F).Reachable (Sum.inl a) (Sum.inl q) :=
      reachable_of_reach (hconn a haO q hqO)
    have h2 := one_le_dist_of_ne hr (by simpa using hap)
    unfold edist at h1
    rw [SimpleGraph.dist_self] at h1
    omega
  exact (key a ha).trans (key b hb).symm

/-! ### Towards Lemma 5: walks avoiding `p`, and shortest walks out of `p` -/

/-- A walk of `incGraph O F` whose support avoids `inl p` is a walk of `incGraph (O.erase p) F`
of the same length. -/
theorem exists_walk_erase_of_notMem_support {O : Finset α} {F : Finset (Finset α)} {p : α}
    {u v : α ⊕ Finset α} (q : (incGraph O F).Walk u v) (hp : Sum.inl p ∉ q.support) :
    ∃ q' : (incGraph (O.erase p) F).Walk u v, q'.length = q.length ∧ q'.support = q.support := by
  have hedges : ∀ e ∈ q.edges, e ∈ (incGraph (O.erase p) F).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet]
    have hadj : (incGraph O F).Adj a b := (SimpleGraph.mem_edgeSet _).mp (q.edges_subset_edgeSet he)
    have ha : a ∈ q.support := q.fst_mem_support_of_mem_edges he
    have hb : b ∈ q.support := q.snd_mem_support_of_mem_edges he
    rcases a with a | S <;> rcases b with b | T
    · exact absurd hadj incGraph_not_adj_inl_inl
    · rw [incGraph_adj_inl_inr] at hadj ⊢
      exact ⟨Finset.mem_erase.mpr ⟨fun h => hp (h ▸ ha), hadj.1⟩, hadj.2⟩
    · rw [incGraph_adj_inr_inl] at hadj ⊢
      exact ⟨Finset.mem_erase.mpr ⟨fun h => hp (h ▸ hb), hadj.1⟩, hadj.2⟩
    · exact absurd hadj incGraph_not_adj_inr_inr
  exact ⟨q.transfer _ hedges, q.length_transfer hedges, q.support_transfer hedges⟩

/-- Distances in `incGraph O F` are at most distances in the smaller graph
`incGraph (O.erase p) F`, between vertices reachable there. -/
theorem dist_le_dist_erase {O : Finset α} {F : Finset (Finset α)} {p : α} {u v : α ⊕ Finset α}
    (h : (incGraph (O.erase p) F).Reachable u v) :
    (incGraph O F).dist u v ≤ (incGraph (O.erase p) F).dist u v := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have hedges : ∀ e ∈ q.edges, e ∈ (incGraph O F).edgeSet := fun e he =>
    SimpleGraph.edgeSet_subset_edgeSet.mpr (incGraph_mono (Finset.erase_subset _ _) le_rfl)
      (q.edges_subset_edgeSet he)
  have := SimpleGraph.dist_le (q.transfer _ hedges)
  rwa [q.length_transfer hedges, hq] at this

/-- `w` is a *second neighbour* of `p`: an element other than `p` sharing a set with it. -/
def InN2 (O : Finset α) (F : Finset (Finset α)) (p w : α) : Prop :=
  w ∈ O ∧ w ≠ p ∧ ∃ S ∈ F, p ∈ S ∧ w ∈ S

omit [DecidableEq α] in
/-- A second neighbour is at distance at most two. -/
theorem dist_le_two_of_inN2 {O : Finset α} {F : Finset (Finset α)} {p w : α} (hp : p ∈ O)
    (h : InN2 O F p w) : (incGraph O F).dist (Sum.inl p) (Sum.inl w) ≤ 2 := by
  obtain ⟨hw, -, S, hS, hpS, hwS⟩ := h
  have := SimpleGraph.dist_le (SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr ⟨hp, hS, hpS⟩)
    (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr ⟨hw, hS, hwS⟩) SimpleGraph.Walk.nil))
  simpa using this

/-- **A shortest walk out of `p`** to another element starts `p – S – w` with `w` a second
neighbour, and the rest is a walk from `w` avoiding `p`, two shorter. -/
theorem exists_inN2_of_shortest {O : Finset α} {F : Finset (Finset α)} {p y : α} (hpy : p ≠ y)
    (q : (incGraph O F).Walk (Sum.inl p) (Sum.inl y))
    (hq : q.length = (incGraph O F).dist (Sum.inl p) (Sum.inl y)) :
    ∃ w, InN2 O F p w ∧ ∃ r : (incGraph O F).Walk (Sum.inl w) (Sum.inl y),
      r.length + 2 = q.length ∧ Sum.inl p ∉ r.support := by
  cases q with
  | nil => exact absurd rfl hpy
  | @cons _ v₁ _ h₁ q₁ =>
    rcases v₁ with a | S
    · exact absurd h₁ incGraph_not_adj_inl_inl
    cases q₁ with
    | @cons _ v₂ _ h₂ q₂ =>
      rcases v₂ with w | T
      swap
      · exact absurd h₂ incGraph_not_adj_inr_inr
      have hS := incGraph_adj_inl_inr.mp h₁
      have hw := incGraph_adj_inr_inl.mp h₂
      simp only [SimpleGraph.Walk.length_cons] at hq
      -- `p` does not reappear on the rest, and `w ≠ p`
      have hnot : Sum.inl p ∉ q₂.support := by
        intro hmem
        have h1 := SimpleGraph.dist_le (q₂.dropUntil _ hmem)
        have h2 := q₂.length_dropUntil_le_length hmem
        omega
      have hwp : w ≠ p := by
        intro hwp
        subst hwp
        exact hnot q₂.start_mem_support
      exact ⟨w, ⟨hw.1, hwp, S, hS.2.1, hS.2.2, hw.2.2⟩, q₂,
        by simp only [SimpleGraph.Walk.length_cons], hnot⟩

/-- Positions in a list determine the element. -/
theorem eq_of_idxOf_eq {L : List α} {a b : α} (ha : a ∈ L) (hb : b ∈ L)
    (h : L.idxOf a = L.idxOf b) : a = b := by
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ha)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb)
  rw [← h1, ← h2]
  simp only [h]

/-- **Lemma 5, one side.**  In an order `L` of `O.erase p` with right end `y`, if every second
neighbour of `p` lies left of `q`, then `d(p, q) ≤ d(p, y)`. -/
theorem edist_le_of_inN2_left {O : Finset α} {F : Finset (Finset α)} {p q y : α} {L : List α}
    (hLO : L.toFinset = O.erase p) (hC : IsC1PList L F) (hpO : p ∈ O)
    (hconn' : IsConnected (O.erase p) F) (hq : q ∈ L) (hy : y ∈ L)
    (hylast : ∀ a ∈ L, L.idxOf a ≤ L.idxOf y) (hleft : ∀ w, InN2 O F p w → L.idxOf w < L.idxOf q)
    (hreach : (incGraph O F).Reachable (Sum.inl p) (Sum.inl y)) :
    edist O F p q ≤ edist O F p y := by
  have memL : ∀ a, a ∈ L ↔ a ∈ O ∧ a ≠ p := fun a => by
    rw [← List.mem_toFinset, hLO, Finset.mem_erase, and_comm]
  have hpy : p ≠ y := fun h => ((memL y).mp hy).2 h.symm
  obtain ⟨s, hs⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨w, hw, r, hr, hnot⟩ := exists_inN2_of_shortest hpy s hs
  have hwL : w ∈ L := (memL w).mpr ⟨hw.1, hw.2.1⟩
  by_cases hqy : q = y
  · subst hqy; exact le_rfl
  have hqy' : L.idxOf q < L.idxOf y :=
    lt_of_le_of_ne (hylast q hq) fun h => hqy (eq_of_idxOf_eq hq hy h)
  -- Lemma 4 in `G − p`
  obtain ⟨r', hr'len, -⟩ := exists_walk_erase_of_notMem_support r hnot
  have hwy' : edist (O.erase p) F w y ≤ r.length := by
    have := SimpleGraph.dist_le r'
    rw [hr'len] at this
    exact this
  have h4 := (edist_le_of_between hLO hC hq (hleft w hw) hqy' r'.reachable).1
  -- the triangle inequality in `G`
  have hpw : (incGraph O F).Reachable (Sum.inl p) (Sum.inl w) :=
    reachable_of_shareStep ⟨hpO, hw.1, let ⟨S, hS, hpS, hwS⟩ := hw.2.2; ⟨S, hS, hpS, hwS⟩⟩
  have hwq' : (incGraph (O.erase p) F).Reachable (Sum.inl w) (Sum.inl q) :=
    reachable_of_reach (hconn' w ((memL w).mp hwL |> fun h => Finset.mem_erase.mpr ⟨h.2, h.1⟩)
      q ((memL q).mp hq |> fun h => Finset.mem_erase.mpr ⟨h.2, h.1⟩))
  have hwq : (incGraph O F).Reachable (Sum.inl w) (Sum.inl q) :=
    hwq'.mono (incGraph_mono (Finset.erase_subset _ _) le_rfl)
  have htri := dist_triangle_of_reachable hpw hwq
  have h2 := dist_le_two_of_inN2 hpO hw
  have h5 := dist_le_dist_erase (O := O) (p := p) hwq'
  unfold edist at h4 hwy' h5 ⊢
  omega

/-- **Lemma 5, the mirror side.**  In an order `L` of `O.erase p` with left end `x`, if every
second neighbour of `p` lies right of `q`, then `d(p, q) ≤ d(p, x)`. -/
theorem edist_le_of_inN2_right {O : Finset α} {F : Finset (Finset α)} {p q x : α} {L : List α}
    (hLO : L.toFinset = O.erase p) (hC : IsC1PList L F) (hpO : p ∈ O)
    (hconn' : IsConnected (O.erase p) F) (hq : q ∈ L) (hx : x ∈ L)
    (hxfirst : ∀ a ∈ L, L.idxOf x ≤ L.idxOf a)
    (hright : ∀ w, InN2 O F p w → L.idxOf q < L.idxOf w)
    (hreach : (incGraph O F).Reachable (Sum.inl p) (Sum.inl x)) :
    edist O F p q ≤ edist O F p x := by
  have memL : ∀ a, a ∈ L ↔ a ∈ O ∧ a ≠ p := fun a => by
    rw [← List.mem_toFinset, hLO, Finset.mem_erase, and_comm]
  have hpx : p ≠ x := fun h => ((memL x).mp hx).2 h.symm
  obtain ⟨s, hs⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨w, hw, r, hr, hnot⟩ := exists_inN2_of_shortest hpx s hs
  have hwL : w ∈ L := (memL w).mpr ⟨hw.1, hw.2.1⟩
  by_cases hqx : q = x
  · subst hqx; exact le_rfl
  have hxq : L.idxOf x < L.idxOf q :=
    lt_of_le_of_ne (hxfirst q hq) fun h => hqx (eq_of_idxOf_eq hq hx h.symm)
  obtain ⟨r', hr'len, -⟩ := exists_walk_erase_of_notMem_support r hnot
  have hwx' : edist (O.erase p) F w x ≤ r.length := by
    have := SimpleGraph.dist_le r'
    rw [hr'len] at this
    exact this
  -- Lemma 4 in `G − p`, for `x < q < w`: `d(q, w) ≤ d(x, w)`
  have h4 := (edist_le_of_between hLO hC hq hxq (hright w hw) r'.reverse.reachable).2
  have hpw : (incGraph O F).Reachable (Sum.inl p) (Sum.inl w) :=
    reachable_of_shareStep ⟨hpO, hw.1, let ⟨S, hS, hpS, hwS⟩ := hw.2.2; ⟨S, hS, hpS, hwS⟩⟩
  have hwq' : (incGraph (O.erase p) F).Reachable (Sum.inl w) (Sum.inl q) :=
    reachable_of_reach (hconn' w ((memL w).mp hwL |> fun h => Finset.mem_erase.mpr ⟨h.2, h.1⟩)
      q ((memL q).mp hq |> fun h => Finset.mem_erase.mpr ⟨h.2, h.1⟩))
  have hwq : (incGraph O F).Reachable (Sum.inl w) (Sum.inl q) :=
    hwq'.mono (incGraph_mono (Finset.erase_subset _ _) le_rfl)
  have htri := dist_triangle_of_reachable hpw hwq
  have h2 := dist_le_two_of_inN2 hpO hw
  have h5 := dist_le_dist_erase (O := O) (p := p) hwq'
  have hc1 : edist (O.erase p) F q w = edist (O.erase p) F w q := edist_comm
  have hc2 : edist (O.erase p) F x w = edist (O.erase p) F w x := edist_comm
  unfold edist at h4 hwx' h5 hc1 hc2 ⊢
  omega

omit [DecidableEq α] in
/-- A walk between distinct vertices has positive length. -/
theorem one_le_length_of_ne {V : Type*} {G : SimpleGraph V} {u v : V} (W : G.Walk u v)
    (h : u ≠ v) : 1 ≤ W.length := by
  by_contra h0
  exact h (SimpleGraph.Walk.exists_length_eq_zero_iff.mp ⟨W, by omega⟩)

omit [DecidableEq α] in
/-- An element vertex of a walk of `incGraph O F` lies in `O`. -/
theorem mem_of_inl_mem_support {O : Finset α} {F : Finset (Finset α)} {u : α ⊕ Finset α} {v : α}
    (P : (incGraph O F).Walk u (Sum.inl v)) (hv : v ∈ O) {t : α} (ht : Sum.inl t ∈ P.support) :
    t ∈ O := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at ht
  obtain ⟨i, hi, hile⟩ := ht
  rcases Nat.lt_or_ge i P.length with hlt | hge
  · have := P.adj_getVert_succ hlt
    rw [hi] at this
    rcases h : P.getVert (i + 1) with b | S
    · rw [h] at this; exact absurd this incGraph_not_adj_inl_inl
    · rw [h] at this; exact (incGraph_adj_inl_inr.mp this).1
  · have : i = P.length := le_antisymm hile hge
    rw [this, SimpleGraph.Walk.getVert_length, Sum.inl.injEq] at hi
    subst hi
    exact hv

/-- **Intermediate elements of a shortest walk lie between its ends** (in an order of the
graph): the side argument of Lemma 4 gives a shortcut otherwise. -/
theorem idxOf_between_of_shortest {O : Finset α} {F : Finset (Finset α)} {L : List α}
    (hLO : L.toFinset = O) (hC : IsC1PList L F) {v₁ v₂ : α} (hv₁ : v₁ ∈ L) (hv₂ : v₂ ∈ L)
    (h12 : L.idxOf v₁ < L.idxOf v₂) (P : (incGraph O F).Walk (Sum.inl v₁) (Sum.inl v₂))
    (hP : P.length = (incGraph O F).dist (Sum.inl v₁) (Sum.inl v₂)) {t : α}
    (ht : Sum.inl t ∈ P.support) : L.idxOf v₁ ≤ L.idxOf t ∧ L.idxOf t ≤ L.idxOf v₂ := by
  have memL : ∀ a, a ∈ L ↔ a ∈ O := fun a => by rw [← List.mem_toFinset, hLO]
  have hv₁O : v₁ ∈ O := (memL v₁).mp hv₁
  have hv₂O : v₂ ∈ O := (memL v₂).mp hv₂
  have htL : t ∈ L := (memL t).mpr (mem_of_inl_mem_support P hv₂O ht)
  have hspec := P.take_spec ht
  have hlen : (P.takeUntil _ ht).length + (P.dropUntil _ ht).length = P.length := by
    rw [← SimpleGraph.Walk.length_append, hspec]
  by_contra hcon
  rcases Nat.lt_or_ge (L.idxOf t) (L.idxOf v₁) with hA | hA
  · -- `t` left of `v₁`: the part from `t` to `v₂` meets a set containing `v₁`
    have hne : t ≠ v₁ := fun h => by subst h; omega
    have hP₁ : 1 ≤ (P.takeUntil _ ht).length := one_le_length_of_ne _ (by simpa using hne.symm)
    have hmeet : ∃ U, Sum.inr U ∈ (P.dropUntil _ ht).support ∧ U ∈ F ∧ v₁ ∈ U := by
      refine exists_mem_support_of_not_avoiding fun hav => ?_
      have hside := idxOf_side_of_avoidChain hLO hC hv₁
        ((avoidingPath_iff_chain hv₁O).mp ⟨P.dropUntil _ ht, hav⟩)
      have : ¬ L.idxOf v₁ < L.idxOf t := by omega
      exact this (hside.mpr h12)
    obtain ⟨U, hU, hUF, hv₁U⟩ := hmeet
    have hadj : (incGraph O F).Adj (Sum.inl v₁) (Sum.inr U) := incGraph_adj_inl_inr.mpr ⟨hv₁O, hUF, hv₁U⟩
    have hQ := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj ((P.dropUntil _ ht).dropUntil _ hU))
    have hsplit : ((P.dropUntil _ ht).takeUntil _ hU).length + ((P.dropUntil _ ht).dropUntil _ hU).length
        = (P.dropUntil _ ht).length := by
      rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
    have htk : 1 ≤ ((P.dropUntil _ ht).takeUntil _ hU).length :=
      one_le_length_of_ne _ (by simp)
    rw [SimpleGraph.Walk.length_cons] at hQ
    omega
  · -- `t` right of `v₂`: the part from `v₁` to `t` meets a set containing `v₂`
    have hB : L.idxOf v₂ < L.idxOf t := by
      rcases Nat.lt_or_ge (L.idxOf v₂) (L.idxOf t) with h | h
      · exact h
      · exact absurd ⟨hA, h⟩ hcon
    have hne : t ≠ v₂ := fun h => by subst h; omega
    have hP₂ : 1 ≤ (P.dropUntil _ ht).length := one_le_length_of_ne _ (by simpa using hne)
    have hmeet : ∃ U, Sum.inr U ∈ (P.takeUntil _ ht).support ∧ U ∈ F ∧ v₂ ∈ U := by
      refine exists_mem_support_of_not_avoiding fun hav => ?_
      have hside := idxOf_side_of_avoidChain hLO hC hv₂
        ((avoidingPath_iff_chain hv₂O).mp ⟨P.takeUntil _ ht, hav⟩)
      have : ¬ L.idxOf v₂ < L.idxOf v₁ := by omega
      exact this (hside.mpr hB)
    obtain ⟨U, hU, hUF, hv₂U⟩ := hmeet
    have hadj : (incGraph O F).Adj (Sum.inr U) (Sum.inl v₂) := incGraph_adj_inr_inl.mpr ⟨hv₂O, hUF, hv₂U⟩
    have hQ := SimpleGraph.dist_le (((P.takeUntil _ ht).takeUntil _ hU).append
      (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))
    have hsplit : ((P.takeUntil _ ht).takeUntil _ hU).length + ((P.takeUntil _ ht).dropUntil _ hU).length
        = (P.takeUntil _ ht).length := by
      rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
    have hdr : 1 ≤ ((P.takeUntil _ ht).dropUntil _ hU).length :=
      one_le_length_of_ne _ (by simp)
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at hQ
    omega

/-- A set that is an interval of `L` and contains two elements contains everything between
them. -/
theorem mem_of_idxOf_between {L : List α} {F : Finset (Finset α)} (hC : IsC1PList L F)
    {U : Finset α} (hU : U ∈ F) {a b c : α} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (haU : a ∈ U)
    (hbU : b ∈ U) (hab : L.idxOf a ≤ L.idxOf c) (hcb : L.idxOf c ≤ L.idxOf b) : c ∈ U := by
  obtain ⟨s, l, hsl⟩ := (hC U hU).idx
  have h1 := hsl _ (List.idxOf_lt_length_iff.mpr ha)
  have h2 := hsl _ (List.idxOf_lt_length_iff.mpr hb)
  have h3 := hsl _ (List.idxOf_lt_length_iff.mpr hc)
  rw [List.getElem_idxOf] at h1 h2 h3
  have := h1.mp haU
  have := h2.mp hbU
  exact h3.mpr ⟨by omega, by omega⟩

/-- **Claim D of Lemma 5.**  On a shortest path of `G − p` from `v₁` to `v₂` — the nearest
second neighbours of `p` on either side of the diameter partner `q` — no set contains `p`. -/
theorem notMem_of_mem_support_shortest {O : Finset α} {F : Finset (Finset α)} {p q : α}
    {L : List α} (hLO : L.toFinset = O.erase p) (hC : IsC1PList L F) (hq : q ∈ L)
    (hqN : ¬ InN2 O F p q) {v₁ v₂ : α} (hv₁ : InN2 O F p v₁) (hv₂ : InN2 O F p v₂)
    (h1q : L.idxOf v₁ < L.idxOf q) (hq2 : L.idxOf q < L.idxOf v₂)
    (hmax₁ : ∀ w, InN2 O F p w → L.idxOf w < L.idxOf q → L.idxOf w ≤ L.idxOf v₁)
    (hmin₂ : ∀ w, InN2 O F p w → L.idxOf q < L.idxOf w → L.idxOf v₂ ≤ L.idxOf w)
    (P : (incGraph (O.erase p) F).Walk (Sum.inl v₁) (Sum.inl v₂)) (hPp : P.IsPath)
    (hP : P.length = (incGraph (O.erase p) F).dist (Sum.inl v₁) (Sum.inl v₂))
    {U : Finset α} (hU : Sum.inr U ∈ P.support) (hUF : U ∈ F) : p ∉ U := by
  intro hpU
  have memL : ∀ a, a ∈ L ↔ a ∈ O ∧ a ≠ p := fun a => by
    rw [← List.mem_toFinset, hLO, Finset.mem_erase, and_comm]
  have hv₁L : v₁ ∈ L := (memL v₁).mpr ⟨hv₁.1, hv₁.2.1⟩
  have hv₂L : v₂ ∈ L := (memL v₂).mpr ⟨hv₂.1, hv₂.2.1⟩
  -- the neighbours of `U` on `P` are second neighbours of `p` between `v₁` and `v₂`, hence
  -- `v₁` or `v₂` themselves
  have hnb : ∀ a, Sum.inl a ∈ P.support → a ∈ U → a = v₁ ∨ a = v₂ := by
    intro a ha haU
    have haO : a ∈ O.erase p := mem_of_inl_mem_support P (Finset.mem_erase.mpr ⟨hv₂.2.1, hv₂.1⟩) ha
    have haN : InN2 O F p a := ⟨(Finset.mem_erase.mp haO).2, (Finset.mem_erase.mp haO).1, U, hUF, hpU, haU⟩
    have haL : a ∈ L := (memL a).mpr ⟨haN.1, haN.2.1⟩
    have hbet := idxOf_between_of_shortest hLO hC hv₁L hv₂L (by omega) P hP ha
    have haq : a ≠ q := fun h => hqN (h ▸ haN)
    rcases lt_or_gt_of_ne (fun h => haq (eq_of_idxOf_eq haL hq h) : L.idxOf a ≠ L.idxOf q) with h | h
    · exact Or.inl (eq_of_idxOf_eq haL hv₁L (le_antisymm (hmax₁ a haN h) hbet.1))
    · exact Or.inr (eq_of_idxOf_eq haL hv₂L (le_antisymm hbet.2 (hmin₂ a haN h)))
  -- locate `U` on the path
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hU
  obtain ⟨i, hi, hile⟩ := hU
  have hi0 : i ≠ 0 := fun h => by
    rw [h, SimpleGraph.Walk.getVert_zero] at hi; exact absurd hi (by simp)
  have hiL : i ≠ P.length := fun h => by
    rw [h, SimpleGraph.Walk.getVert_length] at hi; exact absurd hi (by simp)
  have hinj := hPp.getVert_injOn
  -- the element before `U`
  have hprev := P.adj_getVert_succ (i := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega, hi] at hprev
  rcases hp1 : P.getVert (i - 1) with a | S
  · rw [hp1] at hprev
    have haU : a ∈ U := (incGraph_adj_inl_inr.mp hprev).2.2
    have haS : Sum.inl a ∈ P.support := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]; exact ⟨i - 1, hp1, by omega⟩
    rcases hnb a haS haU with rfl | rfl
    · -- `a = v₁`: then `i = 1`
      have hi1 : i - 1 = 0 := hinj (by simp; omega) (by simp) (by rw [hp1, SimpleGraph.Walk.getVert_zero])
      -- the element after `U`
      have hnext := P.adj_getVert_succ (i := i) (by omega)
      rw [hi] at hnext
      rcases hp2 : P.getVert (i + 1) with b | T
      · rw [hp2] at hnext
        have hbU : b ∈ U := (incGraph_adj_inr_inl.mp hnext).2.2
        have hbS : Sum.inl b ∈ P.support := by
          rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]; exact ⟨i + 1, hp2, by omega⟩
        rcases hnb b hbS hbU with rfl | rfl
        · have : i + 1 = 0 := hinj (by simp; omega) (by simp) (by rw [hp2, SimpleGraph.Walk.getVert_zero])
          omega
        · have hi2 : i + 1 = P.length :=
            hinj (by simp; omega) (by simp) (by rw [hp2, SimpleGraph.Walk.getVert_length])
          -- `P = v₁ – U – v₂`, so `U ∋ v₁, v₂`, hence `q ∈ U`
          have hqU : q ∈ U := mem_of_idxOf_between hC hUF hv₁L hv₂L hq haU hbU h1q.le hq2.le
          exact hqN ⟨(memL q).mp hq |>.1, (memL q).mp hq |>.2, U, hUF, hpU, hqU⟩
      · rw [hp2] at hnext; exact absurd hnext incGraph_not_adj_inr_inr
    · -- `a = v₂` before the end: impossible on a path
      have : i - 1 = P.length :=
        hinj (by simp; omega) (by simp) (by rw [hp1, SimpleGraph.Walk.getVert_length])
      omega
  · rw [hp1] at hprev; exact absurd hprev incGraph_not_adj_inr_inr

/-- **Tucker's Lemma 5.**  For a diameter point `p` whose partner `q` is at distance at
least four, every order of `G − p` has an end at distance `d(p, q)` from `p`. -/
theorem edist_end_eq_of_diameterPoint {O : Finset α} {F : Finset (Finset α)}
    (hconn : IsConnected O F) (hAT : ∀ x y z, ¬ IsAsteroidalTriple O F x y z) {p q : α}
    (hpO : p ∈ O) (hqO : q ∈ O) (hmax : ∀ a ∈ O, ∀ b ∈ O, edist O F a b ≤ edist O F p q)
    (hδ : 4 ≤ edist O F p q) {L : List α} (hLO : L.toFinset = O.erase p) (hC : IsC1PList L F)
    {x y : α} (hx : x ∈ L) (hy : y ∈ L) (hxfirst : ∀ a ∈ L, L.idxOf x ≤ L.idxOf a)
    (hylast : ∀ a ∈ L, L.idxOf a ≤ L.idxOf y) :
    edist O F p x = edist O F p q ∨ edist O F p y = edist O F p q := by
  classical
  have hconn' : IsConnected (O.erase p) F :=
    isConnected_erase_of_diameterPoint hconn ⟨hpO, q, hqO, hmax⟩
  have memL : ∀ a, a ∈ L ↔ a ∈ O ∧ a ≠ p := fun a => by
    rw [← List.mem_toFinset, hLO, Finset.mem_erase, and_comm]
  have hqp : q ≠ p := by
    intro h
    subst h
    unfold edist at hδ
    rw [SimpleGraph.dist_self] at hδ
    omega
  have hqL : q ∈ L := (memL q).mpr ⟨hqO, hqp⟩
  have hqN : ¬ InN2 O F p q := fun h => by
    have := dist_le_two_of_inN2 hpO h
    unfold edist at hδ
    omega
  have hN2L : ∀ w, InN2 O F p w → w ∈ L := fun w hw => (memL w).mpr ⟨hw.1, hw.2.1⟩
  have hreachx : (incGraph O F).Reachable (Sum.inl p) (Sum.inl x) :=
    reachable_of_reach (hconn p hpO x ((memL x).mp hx).1)
  have hreachy : (incGraph O F).Reachable (Sum.inl p) (Sum.inl y) :=
    reachable_of_reach (hconn p hpO y ((memL y).mp hy).1)
  by_cases hS₂ : ∃ w, InN2 O F p w ∧ L.idxOf q < L.idxOf w
  swap
  · push Not at hS₂
    right
    refine le_antisymm (hmax p hpO y ((memL y).mp hy).1)
      (edist_le_of_inN2_left hLO hC hpO hconn' hqL hy hylast (fun w hw => ?_) hreachy)
    have hne : w ≠ q := fun h => hqN (h ▸ hw)
    exact lt_of_le_of_ne (hS₂ w hw) fun h => hne (eq_of_idxOf_eq (hN2L w hw) hqL h)
  by_cases hS₁ : ∃ w, InN2 O F p w ∧ L.idxOf w < L.idxOf q
  swap
  · push Not at hS₁
    left
    refine le_antisymm (hmax p hpO x ((memL x).mp hx).1)
      (edist_le_of_inN2_right hLO hC hpO hconn' hqL hx hxfirst (fun w hw => ?_) hreachx)
    have hne : w ≠ q := fun h => hqN (h ▸ hw)
    exact lt_of_le_of_ne (hS₁ w hw) fun h => hne (eq_of_idxOf_eq (hN2L w hw) hqL h.symm)
  -- both sides are nonempty: the nearest second neighbours form an asteroidal triple with `p`
  exfalso
  obtain ⟨w₂, hw₂, hw₂q⟩ := hS₂
  obtain ⟨w₁, hw₁, hw₁q⟩ := hS₁
  obtain ⟨v₁, hv₁S, hv₁max⟩ := Finset.exists_max_image
    (L.toFinset.filter fun w => InN2 O F p w ∧ L.idxOf w < L.idxOf q) L.idxOf
    ⟨w₁, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hN2L w₁ hw₁), hw₁, hw₁q⟩⟩
  obtain ⟨v₂, hv₂S, hv₂min⟩ := Finset.exists_min_image
    (L.toFinset.filter fun w => InN2 O F p w ∧ L.idxOf q < L.idxOf w) L.idxOf
    ⟨w₂, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hN2L w₂ hw₂), hw₂, hw₂q⟩⟩
  obtain ⟨hv₁L', hv₁N, h1q⟩ := Finset.mem_filter.mp hv₁S
  obtain ⟨hv₂L', hv₂N, hq2⟩ := Finset.mem_filter.mp hv₂S
  have hv₁L : v₁ ∈ L := List.mem_toFinset.mp hv₁L'
  have hv₂L : v₂ ∈ L := List.mem_toFinset.mp hv₂L'
  have hmax₁ : ∀ w, InN2 O F p w → L.idxOf w < L.idxOf q → L.idxOf w ≤ L.idxOf v₁ :=
    fun w hw hwq => hv₁max w (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hN2L w hw), hw, hwq⟩)
  have hmin₂ : ∀ w, InN2 O F p w → L.idxOf q < L.idxOf w → L.idxOf v₂ ≤ L.idxOf w :=
    fun w hw hwq => hv₂min w (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hN2L w hw), hw, hwq⟩)
  have hv₁O' : v₁ ∈ O.erase p := Finset.mem_erase.mpr ⟨hv₁N.2.1, hv₁N.1⟩
  have hv₂O' : v₂ ∈ O.erase p := Finset.mem_erase.mpr ⟨hv₂N.2.1, hv₂N.1⟩
  obtain ⟨P, hPp, hP⟩ := (reachable_of_reach (hconn' v₁ hv₁O' v₂ hv₂O')).exists_path_of_dist
  have hD : ∀ U, Sum.inr U ∈ P.support → U ∈ F → p ∉ U := fun U hU hUF =>
    notMem_of_mem_support_shortest hLO hC hqL hqN hv₁N hv₂N h1q hq2 hmax₁ hmin₂ P hPp hP hU hUF
  obtain ⟨U₁, hU₁F, hpU₁, hv₁U₁⟩ := hv₁N.2.2
  obtain ⟨U₂, hU₂F, hpU₂, hv₂U₂⟩ := hv₂N.2.2
  have hv₂U₁ : v₂ ∉ U₁ := fun h => hqN ⟨hqO, hqp, U₁, hU₁F, hpU₁,
    mem_of_idxOf_between hC hU₁F hv₁L hv₂L hqL hv₁U₁ h h1q.le hq2.le⟩
  have hv₁U₂ : v₁ ∉ U₂ := fun h => hqN ⟨hqO, hqp, U₂, hU₂F, hpU₂,
    mem_of_idxOf_between hC hU₂F hv₁L hv₂L hqL h hv₂U₂ h1q.le hq2.le⟩
  refine hAT p v₁ v₂ ⟨hpO, hv₁N.1, hv₂N.1, hv₁N.2.1.symm, fun h => by subst h; omega,
    hv₂N.2.1.symm, ?_, ?_, ?_⟩
  · refine ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr ⟨hpO, hU₁F, hpU₁⟩)
      (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr ⟨hv₁N.1, hU₁F, hv₁U₁⟩)
        SimpleGraph.Walk.nil), fun v hv => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact incGraph_not_adj_inl_inl
    · rw [incGraph_adj_inr_inl]; exact fun h => hv₂U₁ h.2.2
    · exact incGraph_not_adj_inl_inl
  · refine ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr ⟨hpO, hU₂F, hpU₂⟩)
      (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr ⟨hv₂N.1, hU₂F, hv₂U₂⟩)
        SimpleGraph.Walk.nil), fun v hv => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact incGraph_not_adj_inl_inl
    · rw [incGraph_adj_inr_inl]; exact fun h => hv₁U₂ h.2.2
    · exact incGraph_not_adj_inl_inl
  · have hedges : ∀ e ∈ P.edges, e ∈ (incGraph O F).edgeSet := fun e he =>
      SimpleGraph.edgeSet_subset_edgeSet.mpr (incGraph_mono (Finset.erase_subset _ _) le_rfl)
        (P.edges_subset_edgeSet he)
    refine ⟨P.transfer _ hedges, fun v hv => ?_⟩
    rw [P.support_transfer hedges] at hv
    rcases v with a | U
    · exact incGraph_not_adj_inl_inl
    · rw [incGraph_adj_inr_inl]; exact fun h => hD U hv h.2.1 h.2.2

end Tucker

end TSPGap

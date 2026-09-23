/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerArrangementCore

/-!
# The rotation claim of Tucker's Theorem 6

The claim: there are a diameter point `p` and an order `R` of `G − p`, with left end `x` and
right end `y`, such that every path from `p` to `x` meets a set containing `y`.  Tucker
proves it by rotating through diameter points; this file carries the helper lemmas of that
rotation, in the corrected form recorded in `TUCKER_DESIGN.md`:

* a chain of sets avoiding `y` covers everything between its ends in a consecutive-ones
  order (`avoidChain_of_idxOf_between`);
* a walk whose sets avoid `q` and `c'`, and which does not visit `c'`, is a chain avoiding
  `q` inside `O.erase c'` (`avoidChain_erase_of_walk`);
* if `q` meets every path from `x` to `c'` and `d(x, q) = d(x, c')` is the diameter, then a
  shortest path from `x` to `c'` ends with a set containing both `q` and `c'`, and its
  earlier part is a chain avoiding both (`exists_last_set_of_meets`);
* the **transfer** step: the property "`q` meets every path to `c'`" passes from `x` to the
  left end `x'` of an order of `G − c'` (`not_avoidChain_of_transfer`).
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-- Positions of elements outside the list are the length. -/
theorem idxOf_eq_length_of_notMem {L : List α} {a : α} (h : a ∉ L) : L.idxOf a = L.length :=
  List.idxOf_eq_length_iff.mpr h

/-- **A chain of intervals covers everything between its ends.**  In a consecutive-ones
order, an element positioned between the ends of a chain avoiding `y` is reached by the
chain. -/
theorem avoidChain_of_idxOf_between {O : Finset α} {F : Finset (Finset α)} {L : List α}
    (hLO : L.toFinset = O) (hC : IsC1PList L F) {y a b : α} (h : AvoidChain O F y a b)
    {u : α} (hu : u ∈ L)
    (hbet : (L.idxOf a ≤ L.idxOf u ∧ L.idxOf u ≤ L.idxOf b) ∨
      (L.idxOf b ≤ L.idxOf u ∧ L.idxOf u ≤ L.idxOf a)) : AvoidChain O F y a u := by
  have memL : ∀ c, c ∈ L ↔ c ∈ O := fun c => by rw [← List.mem_toFinset, hLO]
  induction h with
  | refl =>
    have hua : u = a := by
      by_cases haL : a ∈ L
      · exact eq_of_idxOf_eq hu haL (by omega)
      · have h1 := idxOf_eq_length_of_notMem haL
        have h2 := List.idxOf_lt_length_iff.mpr hu
        omega
    rw [hua]
    exact Relation.ReflTransGen.refl
  | @tail b' c hab' hb'c ih =>
    have hb'L : b' ∈ L := (memL b').mpr hb'c.1
    have hcL : c ∈ L := (memL c).mpr hb'c.2.1
    by_cases h1 : (L.idxOf a ≤ L.idxOf u ∧ L.idxOf u ≤ L.idxOf b') ∨
        (L.idxOf b' ≤ L.idxOf u ∧ L.idxOf u ≤ L.idxOf a)
    · exact ih h1
    · obtain ⟨S, hS, hyS, hb'S, hcS⟩ := hb'c.2.2
      have huS : u ∈ S := by
        rcases Nat.le_total (L.idxOf b') (L.idxOf c) with hbc | hcb
        · exact mem_of_idxOf_between hC hS hb'L hcL hu hb'S hcS (by omega) (by omega)
        · exact mem_of_idxOf_between hC hS hcL hb'L hu hcS hb'S (by omega) (by omega)
      exact hab'.tail ⟨hb'c.1, (memL u).mp hu, S, hS, hyS, hb'S, huS⟩

/-- A walk whose sets avoid `q` is a chain avoiding `q`; if it also never visits `c'`, the
chain lives in `O.erase c'`. -/
theorem avoidChain_erase_of_walk {O : Finset α} {F : Finset (Finset α)} {q c' : α}
    {v w : α ⊕ Finset α} (W : (incGraph O F).Walk v w)
    (hq : ∀ S, Sum.inr S ∈ W.support → q ∉ S) (hc' : Sum.inl c' ∉ W.support) :
    (∀ x z, v = Sum.inl x → w = Sum.inl z → AvoidChain (O.erase c') F q x z) ∧
      (∀ S z, v = Sum.inr S → w = Sum.inl z → S ∈ F → ∀ a ∈ O, a ≠ c' → a ∈ S →
        AvoidChain (O.erase c') F q a z) := by
  induction W with
  | nil =>
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 => ?_⟩
    · rw [h1, Sum.inl.injEq] at h2
      subst h2
      exact Relation.ReflTransGen.refl
    · rw [h1] at h2
      exact absurd h2 (by simp)
  | @cons v v' w huv W ih =>
    have hq' : ∀ S, Sum.inr S ∈ W.support → q ∉ S := fun S hS =>
      hq S (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hS)
    have hc'' : Sum.inl c' ∉ W.support := fun h =>
      hc' (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ h)
    have ih' := ih hq' hc''
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 hS a ha hac haS => ?_⟩
    · subst h1
      rcases v' with b | S
      · exact absurd huv incGraph_not_adj_inl_inl
      · have h := incGraph_adj_inl_inr.mp huv
        have hxc : x ≠ c' := by
          intro hxc
          subst hxc
          exact hc' (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self ..)
        exact ih'.2 S z rfl h2 h.2.1 x h.1 hxc h.2.2
    · subst h1
      rcases v' with b | T
      · have h := incGraph_adj_inr_inl.mp huv
        have hbc : b ≠ c' := by
          intro hbc
          subst hbc
          exact hc'' W.start_mem_support
        have hqS : q ∉ S := hq S (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self ..)
        exact Relation.ReflTransGen.head
          ⟨Finset.mem_erase.mpr ⟨hac, ha⟩, Finset.mem_erase.mpr ⟨hbc, h.1⟩, S, hS, hqS, haS, h.2.2⟩
          (ih'.1 b z rfl h2)
      · exact absurd huv incGraph_not_adj_inr_inr

omit [DecidableEq α] in
/-- A set vertex of a walk of `incGraph O F` (starting at an element) is a set of `F`. -/
theorem mem_of_inr_mem_support {O : Finset α} {F : Finset (Finset α)} {x : α} {w : α ⊕ Finset α}
    (W : (incGraph O F).Walk (Sum.inl x) w) {S : Finset α} (hS : Sum.inr S ∈ W.support) : S ∈ F := by
  obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hS
  have hi0 : i ≠ 0 := fun h => by
    rw [h, SimpleGraph.Walk.getVert_zero] at hi; exact absurd hi (by simp)
  have hadj := W.adj_getVert_succ (i := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega, hi] at hadj
  rcases hg : W.getVert (i - 1) with g | G'
  · rw [hg] at hadj; exact (incGraph_adj_inl_inr.mp hadj).2.1
  · rw [hg] at hadj; exact absurd hadj incGraph_not_adj_inr_inr

/-- A shortest walk between elements visits its endpoint only at the end and never has a
set containing the endpoint before the last step. -/
theorem notMem_of_shortest {O : Finset α} {F : Finset (Finset α)} {x c' : α}
    (Q : (incGraph O F).Walk (Sum.inl x) (Sum.inl c'))
    (hQ : Q.length = (incGraph O F).dist (Sum.inl x) (Sum.inl c')) {U : Finset α}
    (hU : Sum.inr U ∈ Q.support) (hc'U : c' ∈ U) (hc'O : c' ∈ O) (hUF : U ∈ F) :
    (Q.dropUntil _ hU).length = 1 := by
  have hspec := Q.take_spec hU
  have hlen : (Q.takeUntil _ hU).length + (Q.dropUntil _ hU).length = Q.length := by
    rw [← SimpleGraph.Walk.length_append, hspec]
  have hadj : (incGraph O F).Adj (Sum.inr U) (Sum.inl c') := incGraph_adj_inr_inl.mpr ⟨hc'O, hUF, hc'U⟩
  have h1 := SimpleGraph.dist_le ((Q.takeUntil _ hU).append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
  have h2 := one_le_length_of_ne (Q.dropUntil _ hU) (by simp)
  omega

/-- **The last set of a shortest path to `c'` contains `q`** when `q` meets every path from
`x` to `c'` and `d(x, q) = d(x, c')`; the earlier part is a chain from `x` avoiding `q` and
`c'`, inside `O.erase c'`, ending at an element `f` of that set with `d(x, f) + 2 ≤ d(x, c')`. -/
theorem exists_last_set_of_meets {O : Finset α} {F : Finset (Finset α)} {x q c' : α}
    (hqO : q ∈ O) (hc'O : c' ∈ O)
    (hmeet : ¬ AvoidChain O F q x c') (hdq : edist O F x c' ≤ edist O F x q)
    (hreach : (incGraph O F).Reachable (Sum.inl x) (Sum.inl c')) :
    ∃ S' ∈ F, q ∈ S' ∧ c' ∈ S' ∧ ∃ f, f ∈ O ∧ f ∈ S' ∧ f ≠ c' ∧
      edist O F x f + 2 ≤ edist O F x c' ∧ AvoidChain (O.erase c') F q x f := by
  obtain ⟨Q, hQ⟩ := hreach.exists_walk_length_eq_dist
  -- `Q` meets a set containing `q`
  have hU : ∃ U, Sum.inr U ∈ Q.support ∧ U ∈ F ∧ q ∈ U := by
    refine exists_mem_support_of_not_avoiding fun hav => hmeet ?_
    exact (avoidingPath_iff_chain hqO).mp ⟨Q, hav⟩
  obtain ⟨U, hU, hUF, hqU⟩ := hU
  have hspec := Q.take_spec hU
  have hlen : (Q.takeUntil _ hU).length + (Q.dropUntil _ hU).length = Q.length := by
    rw [← SimpleGraph.Walk.length_append, hspec]
  -- `U` is the last set: the walk `x ⇝ U → q` has length at least `d(x, q) ≥ d(x, c')`
  have hadjq : (incGraph O F).Adj (Sum.inr U) (Sum.inl q) := incGraph_adj_inr_inl.mpr ⟨hqO, hUF, hqU⟩
  have h1 := SimpleGraph.dist_le ((Q.takeUntil _ hU).append (SimpleGraph.Walk.cons hadjq SimpleGraph.Walk.nil))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
  have hdrop1 : (Q.dropUntil _ hU).length = 1 := by
    have := one_le_length_of_ne (Q.dropUntil _ hU) (by simp)
    unfold edist at hdq
    omega
  -- so `c' ∈ U`: the drop part is a single edge `U → c'`
  have hc'U : c' ∈ U := by
    have hadj := (Q.dropUntil _ hU).adj_getVert_succ (i := 0) (by omega)
    rw [SimpleGraph.Walk.getVert_zero, show (0 : ℕ) + 1 = (Q.dropUntil _ hU).length by omega,
      SimpleGraph.Walk.getVert_length] at hadj
    exact (incGraph_adj_inr_inl.mp hadj).2.2
  -- the element `f` before `U`
  set T := Q.takeUntil _ hU with hT
  have hTlen : 1 ≤ T.length := one_le_length_of_ne T (by simp)
  have hadjf := T.adj_getVert_succ (i := T.length - 1) (by omega)
  rw [show T.length - 1 + 1 = T.length by omega, SimpleGraph.Walk.getVert_length] at hadjf
  rcases hf : T.getVert (T.length - 1) with f | V
  swap
  · rw [hf] at hadjf; exact absurd hadjf incGraph_not_adj_inr_inr
  rw [hf] at hadjf
  have hfU := incGraph_adj_inl_inr.mp hadjf
  -- the prefix `x ⇝ f` of `T`
  have hfmem : Sum.inl f ∈ T.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]; exact ⟨T.length - 1, hf, by omega⟩
  have hPlen : (T.takeUntil _ hfmem).length + 1 ≤ T.length := by
    have h3 : (T.takeUntil _ hfmem).length + (T.dropUntil _ hfmem).length = T.length := by
      rw [← SimpleGraph.Walk.length_append, T.take_spec hfmem]
    have h4 := one_le_length_of_ne (T.dropUntil _ hfmem) (by simp)
    omega
  -- no set of the prefix contains `q` or `c'`, and `c'` is not visited
  have hPsub : (T.takeUntil _ hfmem).support ⊆ Q.support := fun v hv =>
    Q.support_takeUntil_subset_support hU (T.support_takeUntil_subset_support hfmem hv)
  have hno : ∀ S, Sum.inr S ∈ (T.takeUntil _ hfmem).support → q ∉ S ∧ c' ∉ S := by
    intro S hS
    have hSF : S ∈ F := mem_of_inr_mem_support Q (hPsub hS)
    have h6 := (T.takeUntil _ hfmem).length_takeUntil_le_length hS
    constructor
    · intro hqS
      have hadj' : (incGraph O F).Adj (Sum.inr S) (Sum.inl q) := incGraph_adj_inr_inl.mpr ⟨hqO, hSF, hqS⟩
      have h5 := SimpleGraph.dist_le (((T.takeUntil _ hfmem).takeUntil _ hS).append
        (SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil))
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil] at h5
      unfold edist at hdq
      omega
    · intro hc'S
      have hadj' : (incGraph O F).Adj (Sum.inr S) (Sum.inl c') := incGraph_adj_inr_inl.mpr ⟨hc'O, hSF, hc'S⟩
      have h5 := SimpleGraph.dist_le (((T.takeUntil _ hfmem).takeUntil _ hS).append
        (SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil))
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil] at h5
      omega
  have hc'not : Sum.inl c' ∉ (T.takeUntil _ hfmem).support := by
    intro hmem
    have h5 := SimpleGraph.dist_le ((T.takeUntil _ hfmem).takeUntil _ hmem)
    have h6 := (T.takeUntil _ hfmem).length_takeUntil_le_length hmem
    omega
  have hchain := (avoidChain_erase_of_walk (T.takeUntil _ hfmem) (fun S hS => (hno S hS).1) hc'not).1
    x f rfl rfl
  refine ⟨U, hUF, hqU, hc'U, f, hfU.1, hfU.2.2, ?_, ?_, hchain⟩
  · intro hfc
    subst hfc
    exact hc'not (T.takeUntil _ hfmem).end_mem_support
  · have h5 := SimpleGraph.dist_le (T.takeUntil _ hfmem)
    unfold edist
    omega

/-- A chain avoiding `q` from `a ≠ c'` to `c'` ends with a step through a set containing `c'`,
preceded by a chain that never visits `c'`. -/
theorem exists_last_step_of_avoidChain {O : Finset α} {F : Finset (Finset α)} {q a c' : α}
    (h : AvoidChain O F q a c') (hac : a ≠ c') :
    ∃ e S, S ∈ F ∧ q ∉ S ∧ e ∈ S ∧ c' ∈ S ∧ e ∈ O ∧ e ≠ c' ∧ AvoidChain (O.erase c') F q a e := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd rfl hac
  | @head a b hab hbc ih =>
    obtain ⟨haO, hbO, S, hS, hqS, haS, hbS⟩ := hab
    by_cases hbc' : b = c'
    · subst hbc'
      exact ⟨a, S, hS, hqS, haS, hbS, haO, hac, Relation.ReflTransGen.refl⟩
    · obtain ⟨e, S', hS', hqS', heS', hc'S', heO, hec, hchain⟩ := ih hbc'
      exact ⟨e, S', hS', hqS', heS', hc'S', heO, hec, Relation.ReflTransGen.head
        ⟨Finset.mem_erase.mpr ⟨hac, haO⟩, Finset.mem_erase.mpr ⟨hbc', hbO⟩, S, hS, hqS, haS, hbS⟩
        hchain⟩

/-- **The transfer step of the rotation.**  Let `L` be an order of `G − c` with right end
`c'`, and `L'` an order of `G − c'` with left end `x'`.  If `q` meets every path from `x` to
`c'`, with `d(x, c')` the diameter (at least four), `d(x, q)` and `d(x, c)` at least as large,
and `x` left of both `q` and `c` in `L'`, then `q` meets every path from `x'` to `c'`. -/
theorem not_avoidChain_of_transfer {O : Finset α} {F : Finset (Finset α)} {x q c c' x' : α}
    {L L' : List α} (hL : L.toFinset = O.erase c) (hC : IsC1PList L F) (hc'L : c' ∈ L)
    (hc'last : ∀ a ∈ L, L.idxOf a ≤ L.idxOf c') (hL' : L'.toFinset = O.erase c')
    (hC' : IsC1PList L' F) (hx' : x' ∈ L') (hx'first : ∀ a ∈ L', L'.idxOf x' ≤ L'.idxOf a)
    (hxO : x ∈ O) (hqO : q ∈ O) (hc'O : c' ∈ O) (hxc' : x ≠ c') (hqc' : q ≠ c') (hcc' : c ≠ c')
    (hxq : L'.idxOf x ≤ L'.idxOf q) (hxc : L'.idxOf x ≤ L'.idxOf c)
    (hmeet : ¬ AvoidChain O F q x c') (hdq : edist O F x c' ≤ edist O F x q)
    (hdc : edist O F x c' ≤ edist O F x c) (hδ : 4 ≤ edist O F x c')
    (hreach : (incGraph O F).Reachable (Sum.inl x) (Sum.inl c')) :
    ¬ AvoidChain O F q x' c' := by
  intro hav
  have memL : ∀ a, a ∈ L ↔ a ∈ O ∧ a ≠ c := fun a => by
    rw [← List.mem_toFinset, hL, Finset.mem_erase, and_comm]
  have memL' : ∀ a, a ∈ L' ↔ a ∈ O ∧ a ≠ c' := fun a => by
    rw [← List.mem_toFinset, hL', Finset.mem_erase, and_comm]
  have hxL' : x ∈ L' := (memL' x).mpr ⟨hxO, hxc'⟩
  have hqL' : q ∈ L' := (memL' q).mpr ⟨hqO, hqc'⟩
  have hx'c' : x' ≠ c' := ((memL' x').mp hx').2
  -- `d(x, q) ≥ 4`: `x ∉ S'` for any set `S' ∋ q`, and `x ≠ q`
  have hxq_ne : x ≠ q := by
    intro h
    subst h
    unfold edist at hdq hδ
    rw [SimpleGraph.dist_self] at hdq
    omega
  have hnotS : ∀ S ∈ F, q ∈ S → x ∉ S := by
    intro S hS hqS hxS
    have := SimpleGraph.dist_le (SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr ⟨hxO, hS, hxS⟩)
      (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr ⟨hqO, hS, hqS⟩) SimpleGraph.Walk.nil))
    unfold edist at hdq hδ
    simp at this
    omega
  -- the last step of the avoiding chain from `x'`
  obtain ⟨e, S, hS, hqS, heS, hc'S, heO, hec', hchain⟩ := exists_last_step_of_avoidChain hav hx'c'
  have heL' : e ∈ L' := (memL' e).mpr ⟨heO, hec'⟩
  -- the last set of a shortest path from `x`
  obtain ⟨S', hS', hqS', hc'S', f, hfO, hfS', hfc', hdf, hchainf⟩ :=
    exists_last_set_of_meets hqO hc'O hmeet hdq hreach
  have hfL' : f ∈ L' := (memL' f).mpr ⟨hfO, hfc'⟩
  -- sides in `L'`: `e` and `f` lie left of `q`
  have hx'q : L'.idxOf x' < L'.idxOf q := by
    refine lt_of_le_of_ne (hx'first q hqL') fun h => ?_
    have := eq_of_idxOf_eq hx' hqL' h
    subst this
    -- the chain from `q` avoiding `q` is trivial, so `e = q ∈ S`, contradiction
    rcases Relation.ReflTransGen.cases_head hchain with h | ⟨b, hqb, -⟩
    · subst h; exact hqS heS
    · obtain ⟨-, -, U, -, hqU, hqU', -⟩ := hqb
      exact hqU hqU'
  have he_q : L'.idxOf e < L'.idxOf q := by
    have hside := idxOf_side_of_avoidChain hL' hC' hqL' hchain
    have h1 : ¬ L'.idxOf q < L'.idxOf x' := by omega
    have h2 : ¬ L'.idxOf q < L'.idxOf e := fun h => h1 (hside.mpr h)
    have heq : e ≠ q := fun h => hqS (h ▸ heS)
    exact lt_of_le_of_ne (by omega) fun h => heq (eq_of_idxOf_eq heL' hqL' h)
  have hxq' : L'.idxOf x < L'.idxOf q :=
    lt_of_le_of_ne hxq fun h => hxq_ne (eq_of_idxOf_eq hxL' hqL' h)
  have hf_q : L'.idxOf f < L'.idxOf q := by
    have hside := idxOf_side_of_avoidChain hL' hC' hqL' hchainf
    have h2 : ¬ L'.idxOf q < L'.idxOf f := fun h => (by omega : ¬ L'.idxOf q < L'.idxOf x) (hside.mpr h)
    have hfq : f ≠ q := by
      intro h
      subst h
      unfold edist at hdf hdq
      omega
    exact lt_of_le_of_ne (by omega) fun h => hfq (eq_of_idxOf_eq hfL' hqL' h)
  -- `x` is not covered by the chain `x' ⇝ e`: so `e < x` in `L'`
  have he_x : L'.idxOf e < L'.idxOf x := by
    by_contra h
    push Not at h
    have hcov := avoidChain_of_idxOf_between hL' hC' hchain hxL'
      (Or.inl ⟨hx'first x hxL', h⟩)
    -- a path `x ⇝ x' ⇝ e –S– c'` avoiding `q`
    have hxe : AvoidChain (O.erase c') F q x e := hcov.symm.trans hchain
    exact hmeet ((hxe.mono (Finset.erase_subset _ _) le_rfl).tail
      ⟨heO, hc'O, S, hS, hqS, heS, hc'S⟩)
  -- `e, f ≠ c`, so both lie in `L`
  have hec : e ≠ c := fun h => by subst h; omega
  have hfc : f ≠ c := by
    intro h
    subst h
    unfold edist at hdf hdc
    omega
  have heL : e ∈ L := (memL e).mpr ⟨heO, hec⟩
  have hfL : f ∈ L := (memL f).mpr ⟨hfO, hfc⟩
  rcases Nat.le_total (L.idxOf e) (L.idxOf f) with hef | hfe
  · -- `f ∈ S`: the chain `x ⇝ f` then `S` avoids `q`
    have hfS : f ∈ S := mem_of_idxOf_between hC hS heL hc'L hfL heS hc'S hef (hc'last f hfL)
    exact hmeet ((hchainf.mono (Finset.erase_subset _ _) le_rfl).tail
      ⟨hfO, hc'O, S, hS, hqS, hfS, hc'S⟩)
  · -- `e ∈ S'`, so in `L'` the set `S' ∋ e, q` contains `x`: contradiction with `d(x, q) ≥ 4`
    have heS' : e ∈ S' := mem_of_idxOf_between hC hS' hfL hc'L heL hfS' hc'S' hfe (hc'last e heL)
    have hxS' : x ∈ S' := mem_of_idxOf_between hC' hS' heL' hqL' hxL' heS' hqS' he_x.le hxq
    exact hnotS S' hS' hqS' hxS'

/-! ### Reversal, parity, and two small facts about chains -/

omit [DecidableEq α] in
theorem IsIntervalList.reverse {L : List α} {S : Finset α} (h : IsIntervalList L S) :
    IsIntervalList L.reverse S := by
  obtain ⟨L₁, L₂, L₃, rfl, h1, h2, h3⟩ := h
  refine ⟨L₃.reverse, L₂.reverse, L₁.reverse, by simp, ?_, ?_, ?_⟩
  · intro x hx; rw [List.mem_reverse] at hx; exact h3 x hx
  · intro x hx; rw [List.mem_reverse] at hx; exact h2 x hx
  · intro x hx; rw [List.mem_reverse] at hx; exact h1 x hx

omit [DecidableEq α] in
theorem IsC1PList.reverse {L : List α} {F : Finset (Finset α)} (h : IsC1PList L F) :
    IsC1PList L.reverse F := fun S hS => (h S hS).reverse

/-- Positions in the reversed list. -/
theorem idxOf_reverse_add {L : List α} (hL : L.Nodup) {a : α} (ha : a ∈ L) :
    L.reverse.idxOf a + L.idxOf a + 1 = L.length := by
  have h1 : L.idxOf a < L.length := List.idxOf_lt_length_iff.mpr ha
  have h2 : L.reverse.idxOf a < L.reverse.length :=
    List.idxOf_lt_length_iff.mpr (List.mem_reverse.mpr ha)
  rw [List.length_reverse] at h2
  have e1 := List.getElem_idxOf h1
  have e2 := List.getElem_idxOf (by rwa [List.length_reverse] : L.reverse.idxOf a < L.reverse.length)
  rw [List.getElem_reverse] at e2
  have := (hL.getElem_inj_iff).mp (e2.trans e1.symm)
  omega

omit [DecidableEq α] in
/-- Walks between element vertices have even length. -/
theorem even_length_of_inl {O : Finset α} {F : Finset (Finset α)} {u w : α ⊕ Finset α}
    (W : (incGraph O F).Walk u w) :
    (∀ x z, u = Sum.inl x → w = Sum.inl z → Even W.length) ∧
      (∀ S z, u = Sum.inr S → w = Sum.inl z → Odd W.length) := by
  induction W with
  | nil =>
    refine ⟨fun x z _ _ => by simp, fun S z h1 h2 => ?_⟩
    rw [h1] at h2; exact absurd h2 (by simp)
  | @cons u v w huv W ih =>
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 => ?_⟩
    · subst h1
      rcases v with b | S
      · exact absurd huv incGraph_not_adj_inl_inl
      · rw [SimpleGraph.Walk.length_cons]
        exact (ih.2 S z rfl h2).add_one
    · subst h1
      rcases v with b | T
      · rw [SimpleGraph.Walk.length_cons]
        exact (ih.1 b z rfl h2).add_one
      · exact absurd huv incGraph_not_adj_inr_inr

omit [DecidableEq α] in
/-- Two elements sharing no set are at distance at least four (when reachable and
distinct). -/
theorem four_le_edist_of_not_share {O : Finset α} {F : Finset (Finset α)} {a b : α}
    (hab : a ≠ b) (hr : (incGraph O F).Reachable (Sum.inl a) (Sum.inl b))
    (hno : ¬ ∃ S ∈ F, a ∈ S ∧ b ∈ S) : 4 ≤ edist O F a b := by
  obtain ⟨W, hW⟩ := hr.exists_walk_length_eq_dist
  have heven := (even_length_of_inl W).1 a b rfl rfl
  have h1 := one_le_length_of_ne W (by simpa using hab)
  have hne2 : W.length ≠ 2 := by
    intro h2
    -- a walk of length two is `a – S – b`
    cases W with
    | nil => simp at h2
    | @cons _ v _ h₁ W₁ =>
      rcases v with c | S
      · exact absurd h₁ incGraph_not_adj_inl_inl
      cases W₁ with
      | @cons _ v₂ _ h₂ W₂ =>
        rcases v₂ with c | T
        swap
        · exact absurd h₂ incGraph_not_adj_inr_inr
        have h3 : W₂.length = 0 := by
          simp only [SimpleGraph.Walk.length_cons] at h2
          omega
        have hc : c = b := by
          cases W₂ with
          | nil => rfl
          | cons _ _ => simp at h3
        subst hc
        exact hno ⟨S, (incGraph_adj_inl_inr.mp h₁).2.1, (incGraph_adj_inl_inr.mp h₁).2.2,
          (incGraph_adj_inr_inl.mp h₂).2.2⟩
  unfold edist
  rw [← hW]
  obtain ⟨k, hk⟩ := heven
  omega

/-- If `c` meets every path from `x` to `y` then `d(x, c) ≤ d(x, y)`. -/
theorem edist_le_of_meets {O : Finset α} {F : Finset (Finset α)} {x y c : α} (hcO : c ∈ O)
    (hmeet : ¬ AvoidChain O F c x y) (hr : (incGraph O F).Reachable (Sum.inl x) (Sum.inl y)) :
    edist O F x c ≤ edist O F x y := by
  obtain ⟨Q, hQ⟩ := hr.exists_walk_length_eq_dist
  have hU : ∃ U, Sum.inr U ∈ Q.support ∧ U ∈ F ∧ c ∈ U := by
    refine exists_mem_support_of_not_avoiding fun hav => hmeet ?_
    exact (avoidingPath_iff_chain hcO).mp ⟨Q, hav⟩
  obtain ⟨U, hU, hUF, hcU⟩ := hU
  have hlen : (Q.takeUntil _ hU).length + (Q.dropUntil _ hU).length = Q.length := by
    rw [← SimpleGraph.Walk.length_append, Q.take_spec hU]
  have hdrop := one_le_length_of_ne (Q.dropUntil _ hU) (by simp)
  have hadj : (incGraph O F).Adj (Sum.inr U) (Sum.inl c) := incGraph_adj_inr_inl.mpr ⟨hcO, hUF, hcU⟩
  have h1 := SimpleGraph.dist_le ((Q.takeUntil _ hU).append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
  unfold edist
  omega

/-- A chain avoiding `q` from `x ≠ c` either stays away from `c` or reaches `c`. -/
theorem avoidChain_erase_or_reach {O : Finset α} {F : Finset (Finset α)} {q x y c : α}
    (h : AvoidChain O F q x y) (hxc : x ≠ c) :
    AvoidChain (O.erase c) F q x y ∨ AvoidChain O F q x c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a b hab hby ih =>
    obtain ⟨haO, hbO, S, hS, hqS, haS, hbS⟩ := hab
    by_cases hbc : b = c
    · subst hbc
      exact Or.inr (Relation.ReflTransGen.single ⟨haO, hbO, S, hS, hqS, haS, hbS⟩)
    · rcases ih hbc with h | h
      · exact Or.inl (Relation.ReflTransGen.head
          ⟨Finset.mem_erase.mpr ⟨hxc, haO⟩, Finset.mem_erase.mpr ⟨hbc, hbO⟩, S, hS, hqS, haS, hbS⟩ h)
      · exact Or.inr (Relation.ReflTransGen.head ⟨haO, hbO, S, hS, hqS, haS, hbS⟩ h)

/-! ### The rotation state -/

/-- In a list whose consecutive entries are related by `R`, if the last entry satisfies `P`
and some entry does not, two consecutive entries straddle `P`. -/
theorem exists_straddle {β : Type*} {R : β → β → Prop} {P : β → Prop} {Y : List β}
    (hR : ∀ i (h : i + 1 < Y.length), R Y[i] Y[i + 1]) {c : β} (hc : Y.getLast? = some c)
    (hPc : P c) {q : β} (hq : q ∈ Y) (hPq : ¬ P q) :
    ∃ a b, a ∈ Y ∧ b ∈ Y ∧ R a b ∧ ¬ P a ∧ P b := by
  classical
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  -- the largest index whose entry fails `P`
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    ((Finset.range Y.length).filter fun i => ∃ h : i < Y.length, ¬ P Y[i]) id
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, hPq⟩⟩
  obtain ⟨hi', hilt, hPi⟩ := Finset.mem_filter.mp hi
  have hlast : ∃ h : Y.length - 1 < Y.length, Y[Y.length - 1] = c := by
    rw [← List.getElem?_eq_some_iff, ← List.getLast?_eq_getElem?]
    exact hc
  obtain ⟨hl1, hl⟩ := hlast
  have hiL : i + 1 < Y.length := by
    rcases Nat.lt_or_ge (i + 1) Y.length with h | h
    · exact h
    · have : i = Y.length - 1 := by omega
      subst this
      exact (hPi (by rw [hl]; exact hPc)).elim
  refine ⟨Y[i], Y[i + 1], List.getElem_mem _, List.getElem_mem _, hR i hiL, hPi, ?_⟩
  by_contra hP
  have := himax (i + 1) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiL, hiL, hP⟩)
  simp at this

/-- **The rotation claim**: a diameter point `p` (here just an element) and an order of
`G − p` with ends `x, y` such that every path from `p` to `x` meets a set containing `y`. -/
def ClaimHolds (O : Finset α) (F : Finset (Finset α)) : Prop :=
  ∃ p ∈ O, ∃ (L : List α) (x y : α), L.Nodup ∧ L.toFinset = O.erase p ∧ IsC1PList L F ∧
    x ∈ L ∧ y ∈ L ∧ (∀ a ∈ L, L.idxOf x ≤ L.idxOf a) ∧ (∀ a ∈ L, L.idxOf a ≤ L.idxOf y) ∧
    ¬ AvoidChain O F y p x

/-- The state of the rotation: the list `Y` of points used so far (consecutive ones at
distance at most two), the current point `c` (the last of `Y`), an order `L` of `G − c` with
ends `x, y`, every point of `Y` at distance `δ` from `x`, and every earlier point meeting
every path from `x` to `c`. -/
structure RotState (O : Finset α) (F : Finset (Finset α)) (δ : ℕ) (Y : List α) (c : α)
    (L : List α) (x y : α) : Prop where
  Y_nodup : Y.Nodup
  Y_sub : ∀ q ∈ Y, q ∈ O
  Y_last : Y.getLast? = some c
  Y_chain : ∀ i (h : i + 1 < Y.length), ∃ S ∈ F, Y[i] ∈ S ∧ Y[i + 1] ∈ S
  L_nodup : L.Nodup
  L_fs : L.toFinset = O.erase c
  L_c1p : IsC1PList L F
  x_mem : x ∈ L
  y_mem : y ∈ L
  x_first : ∀ a ∈ L, L.idxOf x ≤ L.idxOf a
  y_last : ∀ a ∈ L, L.idxOf a ≤ L.idxOf y
  dist_x : ∀ q ∈ Y, edist O F x q = δ
  meets : ∀ q ∈ Y, q ≠ c → ¬ AvoidChain O F q x c

/-- Orient an order so that `x` comes before `c`. -/
theorem exists_order_oriented {F : Finset (Finset α)} {L₀ : List α}
    (hnd : L₀.Nodup) {O' : Finset α} (hfs : L₀.toFinset = O') (hC : IsC1PList L₀ F) {x c : α}
    (hx : x ∈ L₀) (hc : c ∈ L₀) :
    ∃ L' : List α, L'.Nodup ∧ L'.toFinset = O' ∧ IsC1PList L' F ∧ L'.idxOf x ≤ L'.idxOf c := by
  by_cases h : L₀.idxOf x ≤ L₀.idxOf c
  · exact ⟨L₀, hnd, hfs, hC, h⟩
  · refine ⟨L₀.reverse, List.nodup_reverse.mpr hnd, by rw [List.toFinset_reverse, hfs], hC.reverse, ?_⟩
    have := idxOf_reverse_add hnd hx
    have := idxOf_reverse_add hnd hc
    omega

/-- If `q` meets every path from `x'` to `y`, a shortest walk from `x'` to `q` never
visits `y`: the walk could be shortcut at the set containing `q` on its way to `y`. -/
theorem notMem_support_of_meets {O : Finset α} {F : Finset (Finset α)} {x' q y : α}
    (hqO : q ∈ O) (hqy : q ≠ y) (hmeet : ¬ AvoidChain O F q x' y)
    (W : (incGraph O F).Walk (Sum.inl x') (Sum.inl q))
    (hW : W.length = (incGraph O F).dist (Sum.inl x') (Sum.inl q)) :
    Sum.inl y ∉ W.support := by
  intro hy
  have hlen : (W.takeUntil _ hy).length + (W.dropUntil _ hy).length = W.length := by
    rw [← SimpleGraph.Walk.length_append, W.take_spec hy]
  have hdrop := one_le_length_of_ne (W.dropUntil _ hy) (by simpa using hqy.symm)
  have hU : ∃ U, Sum.inr U ∈ (W.takeUntil _ hy).support ∧ U ∈ F ∧ q ∈ U := by
    refine exists_mem_support_of_not_avoiding fun hav => hmeet ?_
    exact (avoidingPath_iff_chain hqO).mp ⟨W.takeUntil _ hy, hav⟩
  obtain ⟨U, hU, hUF, hqU⟩ := hU
  have hlen2 : ((W.takeUntil _ hy).takeUntil _ hU).length + ((W.takeUntil _ hy).dropUntil _ hU).length
      = (W.takeUntil _ hy).length := by
    rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
  have hdrop2 := one_le_length_of_ne ((W.takeUntil _ hy).dropUntil _ hU) (by simp)
  have hadj : (incGraph O F).Adj (Sum.inr U) (Sum.inl q) := incGraph_adj_inr_inl.mpr ⟨hqO, hUF, hqU⟩
  have h1 := SimpleGraph.dist_le (((W.takeUntil _ hy).takeUntil _ hU).append
    (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
  omega

/-- **One step of the rotation.**  Either the claim holds (for the current point and order,
possibly reversed), or the rotation moves to the right end `y` with one more used point. -/
theorem rotation_step {O : Finset α} {F : Finset (Finset α)} {δ : ℕ} (hconn : IsConnected O F)
    (hAT : ∀ x y z, ¬ IsAsteroidalTriple O F x y z)
    (hIH : ∀ p ∈ O, ∃ L : List α, L.Nodup ∧ L.toFinset = O.erase p ∧ IsC1PList L F)
    (hmax : ∀ a ∈ O, ∀ b ∈ O, edist O F a b ≤ δ) (hδ : 4 ≤ δ) {Y : List α} {c : α}
    {L : List α} {x y : α} (st : RotState O F δ Y c L x y) :
    ClaimHolds O F ∨ ∃ (Y' : List α) (c' : α) (L' : List α) (x' y' : α),
      RotState O F δ Y' c' L' x' y' ∧ Y'.length = Y.length + 1 := by
  classical
  have memL : ∀ a, a ∈ L ↔ a ∈ O ∧ a ≠ c := fun a => by
    rw [← List.mem_toFinset, st.L_fs, Finset.mem_erase, and_comm]
  have hcY : c ∈ Y := List.mem_of_mem_getLast? (by rw [st.Y_last]; rfl)
  have hcO : c ∈ O := st.Y_sub c hcY
  have hxO : x ∈ O := ((memL x).mp st.x_mem).1
  have hxc : x ≠ c := ((memL x).mp st.x_mem).2
  have hyO : y ∈ O := ((memL y).mp st.y_mem).1
  have hyc : y ≠ c := ((memL y).mp st.y_mem).2
  have hdxc : edist O F x c = δ := st.dist_x c hcY
  by_cases hA : ¬ AvoidChain O F y c x
  · exact Or.inl ⟨c, hcO, L, x, y, st.L_nodup, st.L_fs, st.L_c1p, st.x_mem, st.y_mem, st.x_first,
      st.y_last, hA⟩
  by_cases hB : ¬ AvoidChain O F x c y
  · refine Or.inl ⟨c, hcO, L.reverse, y, x, List.nodup_reverse.mpr st.L_nodup,
      by rw [List.toFinset_reverse, st.L_fs], st.L_c1p.reverse, List.mem_reverse.mpr st.y_mem,
      List.mem_reverse.mpr st.x_mem, fun a ha => ?_, fun a ha => ?_, hB⟩
    · rw [List.mem_reverse] at ha
      have := idxOf_reverse_add st.L_nodup ha
      have := idxOf_reverse_add st.L_nodup st.y_mem
      have := st.y_last a ha
      omega
    · rw [List.mem_reverse] at ha
      have := idxOf_reverse_add st.L_nodup ha
      have := idxOf_reverse_add st.L_nodup st.x_mem
      have := st.x_first a ha
      omega
  push Not at hA hB
  -- `x ≠ y`: a shortest walk from `c` to `x` provides a second element of `G − c`
  have hxy_ne : x ≠ y := by
    intro hxy
    have hreach : (incGraph O F).Reachable (Sum.inl c) (Sum.inl x) :=
      reachable_of_reach (hconn c hcO x hxO)
    obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
    obtain ⟨w, hw, r, hr, -⟩ := exists_inN2_of_shortest hxc.symm W hW
    have hwL : w ∈ L := (memL w).mpr ⟨hw.1, hw.2.1⟩
    have hwx : w ≠ x := by
      intro hwx
      subst hwx
      have := SimpleGraph.dist_le r
      have h2 := dist_le_two_of_inN2 hcO hw
      unfold edist at hdxc
      rw [SimpleGraph.dist_comm] at h2
      omega
    have h1 := st.x_first w hwL
    have h2 := st.y_last w hwL
    subst hxy
    exact hwx (eq_of_idxOf_eq hwL st.x_mem (le_antisymm h2 h1))
  -- `y` is a new point
  have hyY : y ∉ Y := fun hyY => st.meets y hyY hyc hA.symm
  -- `c` meets every path from `x` to `y`
  have hmeet_c : ¬ AvoidChain O F c x y := fun h =>
    hAT x y c ⟨hxO, hyO, hcO, hxy_ne, hyc, hxc, walk_of_chain h, walk_of_chain hA.symm,
      walk_of_chain hB.symm⟩
  -- every point of `Y` meets every path from `x` to `y`
  have hmeet_q : ∀ q ∈ Y, ¬ AvoidChain O F q x y := by
    intro q hqY h
    by_cases hqc : q = c
    · subst hqc; exact hmeet_c h
    rcases avoidChain_erase_or_reach h hxc with h' | h'
    · have hqL : q ∈ L := (memL q).mpr ⟨st.Y_sub q hqY, hqc⟩
      have hside := idxOf_side_of_avoidChain st.L_fs st.L_c1p hqL h'
      have hxq_ne : x ≠ q := by
        intro e
        subst e
        have := st.dist_x x hqY
        unfold edist at this
        rw [SimpleGraph.dist_self] at this
        omega
      have hxq : L.idxOf x < L.idxOf q :=
        lt_of_le_of_ne (st.x_first q hqL) fun e => hxq_ne (eq_of_idxOf_eq st.x_mem hqL e)
      have hqy : L.idxOf q < L.idxOf y :=
        lt_of_le_of_ne (st.y_last q hqL) fun e => hyY (eq_of_idxOf_eq hqL st.y_mem e ▸ hqY)
      exact (by omega : ¬ L.idxOf q < L.idxOf x) (hside.mpr hqy)
    · exact st.meets q hqY hqc h'
  have hreach_xy : (incGraph O F).Reachable (Sum.inl x) (Sum.inl y) :=
    reachable_of_reach (hconn x hxO y hyO)
  -- `d(x, y) = δ` and `d(c, y) ≤ 2`
  have hdxy : edist O F x y = δ := by
    refine le_antisymm (hmax x hxO y hyO) ?_
    have := edist_le_of_meets hcO hmeet_c hreach_xy
    rw [hdxc] at this
    exact this
  have hcy_share : ∃ S ∈ F, c ∈ S ∧ y ∈ S := by
    obtain ⟨S', hS', hcS', hyS', -⟩ :=
      exists_last_set_of_meets hcO hyO hmeet_c (by rw [hdxy, hdxc]) hreach_xy
    exact ⟨S', hS', hcS', hyS'⟩
  -- `y` is a diameter point, so `G − y` stays connected
  have hconn' : IsConnected (O.erase y) F :=
    isConnected_erase_of_diameterPoint hconn ⟨hyO, x, hxO, fun a ha b hb => by
      rw [edist_comm (x := y), hdxy]; exact hmax a ha b hb⟩
  -- the new order of `G − y`, oriented with `x` before `c`
  obtain ⟨L₀, hL₀nd, hL₀fs, hL₀C⟩ := hIH y hyO
  have memL₀ : ∀ a, a ∈ L₀ ↔ a ∈ O ∧ a ≠ y := fun a => by
    rw [← List.mem_toFinset, hL₀fs, Finset.mem_erase, and_comm]
  obtain ⟨L', hL'nd, hL'fs, hL'C, hxc'⟩ := exists_order_oriented hL₀nd hL₀fs hL₀C
    ((memL₀ x).mpr ⟨hxO, hxy_ne⟩) ((memL₀ c).mpr ⟨hcO, hyc.symm⟩)
  have memL' : ∀ a, a ∈ L' ↔ a ∈ O ∧ a ≠ y := fun a => by
    rw [← List.mem_toFinset, hL'fs, Finset.mem_erase, and_comm]
  have hxL' : x ∈ L' := (memL' x).mpr ⟨hxO, hxy_ne⟩
  obtain ⟨x', hx'L', hx'first⟩ := Finset.exists_min_image L'.toFinset L'.idxOf
    ⟨x, List.mem_toFinset.mpr hxL'⟩
  obtain ⟨y', hy'L', hy'last⟩ := Finset.exists_max_image L'.toFinset L'.idxOf
    ⟨x, List.mem_toFinset.mpr hxL'⟩
  rw [List.mem_toFinset] at hx'L' hy'L'
  have hx'first' : ∀ a ∈ L', L'.idxOf x' ≤ L'.idxOf a := fun a ha =>
    hx'first a (List.mem_toFinset.mpr ha)
  have hy'last' : ∀ a ∈ L', L'.idxOf a ≤ L'.idxOf y' := fun a ha =>
    hy'last a (List.mem_toFinset.mpr ha)
  -- all used points lie right of `x` in `L'`
  have hYL' : ∀ q ∈ Y, q ∈ L' := fun q hq => (memL' q).mpr ⟨st.Y_sub q hq, fun e => hyY (e ▸ hq)⟩
  have hside : ∀ q ∈ Y, L'.idxOf x ≤ L'.idxOf q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hqY, hq⟩ := hcon
    obtain ⟨a, b, haY, hbY, hab, ha, hb⟩ := exists_straddle
      (R := fun a b => ∃ S ∈ F, a ∈ S ∧ b ∈ S) (P := fun q => L'.idxOf x ≤ L'.idxOf q)
      st.Y_chain st.Y_last hxc' hqY (not_le.mpr hq)
    push Not at ha
    have haL' := hYL' a haY
    have hbL' := hYL' b hbY
    have hxb_ne : x ≠ b := by
      intro e
      subst e
      have := st.dist_x x hbY
      unfold edist at this
      rw [SimpleGraph.dist_self] at this
      omega
    have hxb : L'.idxOf x < L'.idxOf b :=
      lt_of_le_of_ne hb fun e => hxb_ne (eq_of_idxOf_eq hxL' hbL' e)
    have haO' : a ∈ O.erase y := Finset.mem_erase.mpr ⟨((memL' a).mp haL').2, st.Y_sub a haY⟩
    have hbO' : b ∈ O.erase y := Finset.mem_erase.mpr ⟨((memL' b).mp hbL').2, st.Y_sub b hbY⟩
    have hxO' : x ∈ O.erase y := Finset.mem_erase.mpr ⟨hxy_ne, hxO⟩
    have hreach_ab : (incGraph (O.erase y) F).Reachable (Sum.inl a) (Sum.inl b) :=
      reachable_of_reach (hconn' a haO' b hbO')
    -- Lemma 4 in `G − y`: `d'(x, b) ≤ d'(a, b) ≤ 2`, but `d(x, b) = δ ≤ d'(x, b)`
    have h4 := (edist_le_of_between hL'fs hL'C hxL' ha hxb hreach_ab).2
    obtain ⟨S, hS, haS, hbS⟩ := hab
    have hba : b ≠ a := fun e => by subst e; omega
    have h2 : edist (O.erase y) F a b ≤ 2 :=
      dist_le_two_of_inN2 haO' ⟨hbO', hba, S, hS, haS, hbS⟩
    have h5 := dist_le_dist_erase (O := O) (p := y)
      (reachable_of_reach (hconn' x hxO' b hbO'))
    have := st.dist_x b hbY
    unfold edist at h4 h2 h5 this
    omega
  -- `q` meets every path from `x'` to `y`, for every used `q`
  have hmeet' : ∀ q ∈ Y, ¬ AvoidChain O F q x' y := fun q hqY =>
    not_avoidChain_of_transfer st.L_fs st.L_c1p st.y_mem st.y_last hL'fs hL'C hx'L' hx'first'
      hxO (st.Y_sub q hqY) hyO hxy_ne (fun e => hyY (e ▸ hqY)) hyc.symm (hside q hqY) hxc'
      (hmeet_q q hqY) (by rw [hdxy, st.dist_x q hqY]) (by rw [hdxy, hdxc])
      (by rw [hdxy]; exact hδ) hreach_xy
  have hx'O : x' ∈ O := ((memL' x').mp hx'L').1
  -- distances from the new left end: a shortest walk from `x'` to a used point avoids `y`
  -- (`q` meets every path to `y`), so Lemma 4 in `G − y` applies
  have hx'O' : x' ∈ O.erase y := Finset.mem_erase.mpr ⟨((memL' x').mp hx'L').2, hx'O⟩
  have hxO' : x ∈ O.erase y := Finset.mem_erase.mpr ⟨hxy_ne, hxO⟩
  have hdist' : ∀ q ∈ Y, edist O F x' q = δ := by
    intro q hqY
    have hqO := st.Y_sub q hqY
    have hqy : q ≠ y := fun e => hyY (e ▸ hqY)
    have hqO' : q ∈ O.erase y := Finset.mem_erase.mpr ⟨hqy, hqO⟩
    refine le_antisymm (hmax x' hx'O q hqO) ?_
    obtain ⟨W, hW⟩ := (reachable_of_reach (hconn x' hx'O q hqO)).exists_walk_length_eq_dist
    have hnot := notMem_support_of_meets hqO hqy (hmeet' q hqY) W hW
    obtain ⟨W', hW'len, -⟩ := exists_walk_erase_of_notMem_support W hnot
    have h1 : edist (O.erase y) F x' q ≤ edist O F x' q := by
      have := SimpleGraph.dist_le W'
      unfold edist
      omega
    have h2 : edist O F x q ≤ edist (O.erase y) F x q :=
      dist_le_dist_erase (reachable_of_reach (hconn' x hxO' q hqO'))
    have h3 : edist (O.erase y) F x q ≤ edist (O.erase y) F x' q := by
      by_cases hxx' : x' = x
      · rw [hxx']
      have hx'x : L'.idxOf x' < L'.idxOf x :=
        lt_of_le_of_ne (hx'first' x hxL') fun e => hxx' (eq_of_idxOf_eq hx'L' hxL' e)
      have hxq_ne : x ≠ q := by
        intro e
        subst e
        have := st.dist_x x hqY
        unfold edist at this
        rw [SimpleGraph.dist_self] at this
        omega
      have hxq : L'.idxOf x < L'.idxOf q :=
        lt_of_le_of_ne (hside q hqY) fun e => hxq_ne (eq_of_idxOf_eq hxL' (hYL' q hqY) e)
      exact (edist_le_of_between hL'fs hL'C hxL' hx'x hxq
        (reachable_of_reach (hconn' x' hx'O' q hqO'))).2
    have := st.dist_x q hqY
    omega
  have hdist'y : edist O F x' y = δ := by
    refine le_antisymm (hmax x' hx'O y hyO) ?_
    have := edist_le_of_meets hcO (hmeet' c hcY)
      (reachable_of_reach (hconn x' hx'O y hyO))
    rw [hdist' c hcY] at this
    exact this
  -- assemble the new state
  refine Or.inr ⟨Y ++ [y], y, L', x', y', ?_, by simp⟩
  refine ⟨?_, ?_, List.getLast?_concat, ?_, hL'nd, hL'fs, hL'C, hx'L', hy'L', hx'first',
    hy'last', ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨st.Y_nodup, List.nodup_singleton y, fun a ha b hb hab => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact hyY (hab ▸ ha)
  · intro q hq
    rw [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact st.Y_sub q hq
    · exact hyO
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases h1 : i + 1 < Y.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
      exact st.Y_chain i h1
    · have hi' : i + 1 = Y.length := by omega
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      have hc' : Y[i]'(by omega) = c := by
        obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp st.Y_last
        have : i = ys.length := by rw [hys] at hi'; simp at hi'; omega
        subst this
        simp [hys, List.getElem_append_right]
      rw [hc']
      simpa using hcy_share
  · intro q hq
    rw [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hdist' q hq
    · exact hdist'y
  · intro q hq hqy
    rw [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hmeet' q hq
    · exact absurd rfl hqy

/-! ### Termination, and the claim -/

/-- The rotation terminates: from any state the claim follows (the used points are
distinct elements of `O`). -/
theorem claimHolds_of_rotState {O : Finset α} {F : Finset (Finset α)} {δ : ℕ}
    (hconn : IsConnected O F) (hAT : ∀ x y z, ¬ IsAsteroidalTriple O F x y z)
    (hIH : ∀ p ∈ O, ∃ L : List α, L.Nodup ∧ L.toFinset = O.erase p ∧ IsC1PList L F)
    (hmax : ∀ a ∈ O, ∀ b ∈ O, edist O F a b ≤ δ) (hδ : 4 ≤ δ) :
    ∀ (n : ℕ) (Y : List α) (c : α) (L : List α) (x y : α), RotState O F δ Y c L x y →
      O.card - Y.length ≤ n → ClaimHolds O F := by
  intro n
  induction n with
  | zero =>
    intro Y c L x y st hn
    rcases rotation_step hconn hAT hIH hmax hδ st with h | ⟨Y', c', L', x', y', st', hlen⟩
    · exact h
    · exfalso
      have h1 : Y'.length ≤ O.card := by
        have := Finset.card_le_card (show Y'.toFinset ⊆ O from
          fun q hq => st'.Y_sub q (List.mem_toFinset.mp hq))
        rwa [List.toFinset_card_of_nodup st'.Y_nodup] at this
      omega
  | succ n ih =>
    intro Y c L x y st hn
    rcases rotation_step hconn hAT hIH hmax hδ st with h | ⟨Y', c', L', x', y', st', hlen⟩
    · exact h
    · exact ih Y' c' L' x' y' st' (by omega)

/-- **The rotation claim** (Tucker, proof of Theorem 6): for a connected instance with at
least two elements, every set having at least two elements of `O` and missing one, no
asteroidal triple, and orders of every `G − p`, there are a point `p` and an order of `G − p`
whose right end meets every path from `p` to its left end. -/
theorem claimHolds {O : Finset α} {F : Finset (Finset α)} (hconn : IsConnected O F)
    (hAT : ∀ x y z, ¬ IsAsteroidalTriple O F x y z)
    (hIH : ∀ p ∈ O, ∃ L : List α, L.Nodup ∧ L.toFinset = O.erase p ∧ IsC1PList L F)
    (hO : 2 ≤ O.card) (hF2 : ∀ S ∈ F, 2 ≤ (S ∩ O).card ∧ ¬ O ⊆ S) : ClaimHolds O F := by
  classical
  have hOne : O.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀, hp₀O, q₀, hq₀O, hmax⟩ := exists_diameterPoint F hOne
  -- the diameter is at least four: otherwise any two elements share a set, and Lemma 3
  -- produces a set containing all of `O`
  have hδ : 4 ≤ edist O F p₀ q₀ := by
    by_contra h
    push Not at h
    have hshare : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → ∃ T ∈ F, a ∈ T ∧ b ∈ T := by
      intro a ha b hb hab
      by_contra hno
      have h1 := four_le_edist_of_not_share hab (reachable_of_reach (hconn a ha b hb)) hno
      have h2 := hmax a ha b hb
      omega
    obtain ⟨T, hT, hOT⟩ := exists_superset_of_pairwise_share hAT hshare O le_rfl hO
    exact (hF2 T hT).2 hOT
  have hq₀p₀ : q₀ ≠ p₀ := by
    intro e
    subst e
    unfold edist at hδ
    rw [SimpleGraph.dist_self] at hδ
    omega
  obtain ⟨L₀, hL₀nd, hL₀fs, hL₀C⟩ := hIH p₀ hp₀O
  have memL₀ : ∀ a, a ∈ L₀ ↔ a ∈ O ∧ a ≠ p₀ := fun a => by
    rw [← List.mem_toFinset, hL₀fs, Finset.mem_erase, and_comm]
  have hq₀L₀ : q₀ ∈ L₀ := (memL₀ q₀).mpr ⟨hq₀O, hq₀p₀⟩
  obtain ⟨x₀, hx₀L₀, hx₀first⟩ := Finset.exists_min_image L₀.toFinset L₀.idxOf
    ⟨q₀, List.mem_toFinset.mpr hq₀L₀⟩
  obtain ⟨y₀, hy₀L₀, hy₀last⟩ := Finset.exists_max_image L₀.toFinset L₀.idxOf
    ⟨q₀, List.mem_toFinset.mpr hq₀L₀⟩
  rw [List.mem_toFinset] at hx₀L₀ hy₀L₀
  have hx₀first' : ∀ a ∈ L₀, L₀.idxOf x₀ ≤ L₀.idxOf a := fun a ha =>
    hx₀first a (List.mem_toFinset.mpr ha)
  have hy₀last' : ∀ a ∈ L₀, L₀.idxOf a ≤ L₀.idxOf y₀ := fun a ha =>
    hy₀last a (List.mem_toFinset.mpr ha)
  -- Lemma 5: an end at distance `δ` from `p₀`; make it the left end
  have hstate : ∀ (L : List α) (x y : α), L.Nodup → L.toFinset = O.erase p₀ → IsC1PList L F →
      x ∈ L → y ∈ L → (∀ a ∈ L, L.idxOf x ≤ L.idxOf a) → (∀ a ∈ L, L.idxOf a ≤ L.idxOf y) →
      edist O F p₀ x = edist O F p₀ q₀ → ClaimHolds O F := by
    intro L x y hnd hfs hC hx hy hxf hyl hdx
    refine claimHolds_of_rotState hconn hAT hIH hmax hδ O.card [p₀] p₀ L x y ⟨?_, ?_, rfl, ?_,
      hnd, hfs, hC, hx, hy, hxf, hyl, ?_, ?_⟩ (by simp)
    · exact List.nodup_singleton _
    · intro q hq; rw [List.mem_singleton] at hq; exact hq ▸ hp₀O
    · intro i hi; simp at hi
    · intro q hq; rw [List.mem_singleton] at hq; subst hq; rw [edist_comm]; exact hdx
    · intro q hq hqp; rw [List.mem_singleton] at hq; exact absurd hq hqp
  rcases edist_end_eq_of_diameterPoint hconn hAT hp₀O hq₀O hmax hδ hL₀fs hL₀C hx₀L₀ hy₀L₀
    hx₀first' hy₀last' with h | h
  · exact hstate L₀ x₀ y₀ hL₀nd hL₀fs hL₀C hx₀L₀ hy₀L₀ hx₀first' hy₀last' h
  · refine hstate L₀.reverse y₀ x₀ (List.nodup_reverse.mpr hL₀nd)
      (by rw [List.toFinset_reverse, hL₀fs]) hL₀C.reverse (List.mem_reverse.mpr hy₀L₀)
      (List.mem_reverse.mpr hx₀L₀) (fun a ha => ?_) (fun a ha => ?_) h
    · rw [List.mem_reverse] at ha
      have := idxOf_reverse_add hL₀nd ha
      have := idxOf_reverse_add hL₀nd hy₀L₀
      have := hy₀last' a ha
      omega
    · rw [List.mem_reverse] at ha
      have := idxOf_reverse_add hL₀nd ha
      have := idxOf_reverse_add hL₀nd hx₀L₀
      have := hx₀first' a ha
      omega

end Tucker

end TSPGap

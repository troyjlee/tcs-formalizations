/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic

/-!
# Euler's theorem for edge multisets

A connected multigraph with even degrees has a closed walk using every edge
exactly once (with multiplicity).  Multigraphs on `Fin n` are edge multisets
`M : Multiset (Sym2 (Fin n))` without diagonals; walks are walks in the complete
graph `⊤`, and "uses the edges of `M`" is `(W.edges : Multiset _) = M`.

Hierholzer's argument, in the form that needs no components:

* every vertex `x` is met an even number of times by the edges of a closed walk
  (`even_mdeg_edges_of_closed`);
* from a vertex of positive degree of an even multigraph there is a nonempty
  closed walk (`exists_closed_walk_pos`), by the open-walk lemma
  `exists_walk_of_parity` — walk greedily, the parity invariant says one never
  gets stuck away from the target;
* a closed walk not yet using all of `M` can be lengthened
  (`exists_longer_closed_walk`): the unused edges form an even multigraph, some
  vertex of the walk has positive unused degree (a spanning tree inside `M`
  connects the walk's support to any unused edge), so a nonempty closed walk on
  unused edges can be spliced in there (`Walk.rotate`, `Walk.append`);
* counting closes (`exists_eulerian_closed_walk`).

`exists_spanning_closed_walk_core` is the form the O-join argument consumes:
for a spanning tree `T` and a join `J` with `T ⊎ J` even, a closed walk through
every vertex of cost exactly `c(T) + c(J)`.
-/

namespace TSPGap
open Finset SimpleGraph

variable {n : ℕ}

/-- The degree of `v` in the edge multiset `M`. -/
def mdeg (M : Multiset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  Multiset.card (M.filter fun e => v ∈ e)

theorem mdeg_add (M N : Multiset (Sym2 (Fin n))) (v : Fin n) :
    mdeg (M + N) v = mdeg M v + mdeg N v := by
  unfold mdeg
  rw [Multiset.filter_add, Multiset.card_add]

theorem mdeg_cons (e : Sym2 (Fin n)) (M : Multiset (Sym2 (Fin n))) (v : Fin n) :
    mdeg (e ::ₘ M) v = (if v ∈ e then 1 else 0) + mdeg M v := by
  unfold mdeg
  rw [Multiset.filter_cons, Multiset.card_add]
  split_ifs <;> simp

theorem mdeg_zero (v : Fin n) : mdeg (0 : Multiset (Sym2 (Fin n))) v = 0 := by
  simp [mdeg]

theorem mdeg_coe (l : List (Sym2 (Fin n))) (v : Fin n) :
    mdeg (l : Multiset (Sym2 (Fin n))) v = l.countP (fun e => v ∈ e) := by
  unfold mdeg
  rw [Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter]

/-- A vertex of positive degree is on some edge of `M`. -/
theorem exists_mem_of_mdeg_pos {M : Multiset (Sym2 (Fin n))} {v : Fin n} (h : 0 < mdeg M v) :
    ∃ e ∈ M, v ∈ e := by
  by_contra hcon
  push Not at hcon
  have : M.filter (fun e => v ∈ e) = 0 :=
    Multiset.filter_eq_nil.mpr fun e he => hcon e he
  simp [mdeg, this] at h

/-- An edge containing `v` is `s(v, z)` for some `z`. -/
theorem exists_eq_mk_of_mem {e : Sym2 (Fin n)} {v : Fin n} (hv : v ∈ e) : ∃ z, e = s(v, z) := by
  induction e using Sym2.ind with
  | h a b =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨b, rfl⟩
    · exact ⟨a, Sym2.eq_swap⟩

/-! ### Parity along a walk -/

/-- Along any walk from `u` to `v`, the number of edges at `x`, plus one for each of
`x = u` and `x = v`, is even. -/
theorem even_countP_edges_add {u v : Fin n} (p : (⊤ : SimpleGraph (Fin n)).Walk u v)
    (x : Fin n) :
    Even (p.edges.countP (fun e => x ∈ e) + (if x = u then 1 else 0)
      + (if x = v then 1 else 0)) := by
  induction p with
  | nil =>
    simp only [Walk.edges_nil, List.countP_nil, zero_add]
    split_ifs <;> simp
  | @cons a b w hab q ih =>
    have hab' : a ≠ b := hab
    rw [Walk.edges_cons, List.countP_cons]
    simp only [decide_eq_true_eq]
    rw [Nat.even_iff] at ih ⊢
    have hmem : (if x ∈ s(a, b) then 1 else 0 : ℕ)
        = (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
      by_cases hxa : x = a <;> by_cases hxb : x = b
      · exact absurd (hxa.symm.trans hxb) hab'
      all_goals simp [Sym2.mem_iff, hxa, hxb, hab', hab'.symm]
    rw [hmem]
    split_ifs at ih ⊢ <;> omega

/-- The edges of a closed walk meet every vertex an even number of times. -/
theorem even_mdeg_edges_of_closed {v : Fin n} (W : (⊤ : SimpleGraph (Fin n)).Walk v v)
    (x : Fin n) : Even (mdeg (W.edges : Multiset (Sym2 (Fin n))) x) := by
  have h := even_countP_edges_add W x
  rw [mdeg_coe, Nat.even_iff] at *
  split_ifs at h <;> omega

/-! ### Walks in an even multigraph -/

/-- **The open-walk lemma.**  If every vertex `z` has even `mdeg M z + [z = u] + [z = w]`
— all degrees even except `u` and `w` odd when `u ≠ w` — then there is a walk from
`w` to `u` using edges of `M`. -/
theorem exists_walk_of_parity (u : Fin n) (M : Multiset (Sym2 (Fin n))) :
    (∀ e ∈ M, ¬ e.IsDiag) → ∀ w : Fin n,
    (∀ z, Even (mdeg M z + (if z = u then 1 else 0) + (if z = w then 1 else 0))) →
    ∃ p : (⊤ : SimpleGraph (Fin n)).Walk w u, (p.edges : Multiset (Sym2 (Fin n))) ≤ M := by
  induction M using Multiset.strongInductionOn with
  | ih M IH =>
  intro hM w hpar
  by_cases huw : w = u
  · subst huw
    exact ⟨Walk.nil, by simp⟩
  · -- `w` has odd, hence positive, degree
    have hpos : 0 < mdeg M w := by
      have h := hpar w
      rw [if_neg huw, if_pos rfl, Nat.even_iff] at h
      omega
    obtain ⟨e, he, hwe⟩ := exists_mem_of_mdeg_pos hpos
    obtain ⟨z, rfl⟩ := exists_eq_mk_of_mem hwe
    have hzw : z ≠ w := fun h => hM _ he (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)
    set M' := M.erase s(w, z) with hM'
    have hMeq : M = s(w, z) ::ₘ M' := (Multiset.cons_erase he).symm
    have hlt : M' < M := Multiset.erase_lt.mpr he
    have hM'diag : ∀ e ∈ M', ¬ e.IsDiag := fun e he' => hM e (Multiset.mem_of_mem_erase he')
    have hpar' : ∀ y, Even (mdeg M' y + (if y = u then 1 else 0) + (if y = z then 1 else 0)) := by
      intro y
      have hy := hpar y
      rw [hMeq, mdeg_cons] at hy
      rw [Nat.even_iff] at hy ⊢
      have hmem : (if y ∈ s(w, z) then 1 else 0 : ℕ)
          = (if y = w then 1 else 0) + (if y = z then 1 else 0) := by
        by_cases hyw : y = w <;> by_cases hyz : y = z
        · exact absurd (hyz.symm.trans hyw) hzw
        all_goals simp [Sym2.mem_iff, hyw, hyz, hzw, hzw.symm]
      rw [hmem] at hy
      split_ifs at hy ⊢ <;> omega
    obtain ⟨p, hp⟩ := IH M' hlt hM'diag z hpar'
    refine ⟨Walk.cons (show (⊤ : SimpleGraph (Fin n)).Adj w z from hzw.symm) p, ?_⟩
    rw [Walk.edges_cons]
    calc ((s(w, z) :: p.edges : List (Sym2 (Fin n))) : Multiset (Sym2 (Fin n)))
        = s(w, z) ::ₘ (p.edges : Multiset (Sym2 (Fin n))) := rfl
      _ ≤ s(w, z) ::ₘ M' := Multiset.cons_le_cons _ hp
      _ = M := hMeq.symm

/-- **A nonempty closed walk** at any vertex of positive degree of an even multigraph. -/
theorem exists_closed_walk_pos (M : Multiset (Sym2 (Fin n))) (hM : ∀ e ∈ M, ¬ e.IsDiag)
    (hev : ∀ z, Even (mdeg M z)) {v : Fin n} (hv : 0 < mdeg M v) :
    ∃ C : (⊤ : SimpleGraph (Fin n)).Walk v v,
      (C.edges : Multiset (Sym2 (Fin n))) ≤ M ∧ 0 < C.length := by
  obtain ⟨e, he, hve⟩ := exists_mem_of_mdeg_pos hv
  obtain ⟨z, rfl⟩ := exists_eq_mk_of_mem hve
  have hzv : z ≠ v := fun h => hM _ he (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)
  set M' := M.erase s(v, z) with hM'
  have hMeq : M = s(v, z) ::ₘ M' := (Multiset.cons_erase he).symm
  have hM'diag : ∀ e ∈ M', ¬ e.IsDiag := fun e he' => hM e (Multiset.mem_of_mem_erase he')
  have hpar : ∀ y, Even (mdeg M' y + (if y = v then 1 else 0) + (if y = z then 1 else 0)) := by
    intro y
    have hy := hev y
    rw [hMeq, mdeg_cons] at hy
    rw [Nat.even_iff] at hy ⊢
    have hmem : (if y ∈ s(v, z) then 1 else 0 : ℕ)
        = (if y = v then 1 else 0) + (if y = z then 1 else 0) := by
      by_cases hyv : y = v <;> by_cases hyz : y = z
      · exact absurd (hyz.symm.trans hyv) hzv
      all_goals simp [Sym2.mem_iff, hyv, hyz, hzv, hzv.symm]
    rw [hmem] at hy
    split_ifs at hy ⊢ <;> omega
  obtain ⟨p, hp⟩ := exists_walk_of_parity v M' hM'diag z hpar
  refine ⟨Walk.cons (show (⊤ : SimpleGraph (Fin n)).Adj v z from hzv.symm) p, ?_, ?_⟩
  · rw [Walk.edges_cons]
    calc ((s(v, z) :: p.edges : List (Sym2 (Fin n))) : Multiset (Sym2 (Fin n)))
        = s(v, z) ::ₘ (p.edges : Multiset (Sym2 (Fin n))) := rfl
      _ ≤ s(v, z) ::ₘ M' := Multiset.cons_le_cons _ hp
      _ = M := hMeq.symm
  · simp

/-! ### Lengthening a closed walk -/

/-- **The extension step.**  A closed walk using a proper sub-multiset of an even
multigraph `M` that contains a spanning tree can be lengthened: the unused edges form
an even multigraph, one of the walk's vertices has positive unused degree, and a
nonempty closed walk on unused edges is spliced in there. -/
theorem exists_longer_closed_walk (M : Multiset (Sym2 (Fin n))) (hM : ∀ e ∈ M, ¬ e.IsDiag)
    (hev : ∀ z, Even (mdeg M z)) {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    (hTM : (T.val : Multiset (Sym2 (Fin n))) ≤ M)
    {v : Fin n} (W : (⊤ : SimpleGraph (Fin n)).Walk v v)
    (hW : (W.edges : Multiset (Sym2 (Fin n))) ≤ M)
    (hlt : Multiset.card (W.edges : Multiset (Sym2 (Fin n))) < Multiset.card M) :
    ∃ (v' : Fin n) (W' : (⊤ : SimpleGraph (Fin n)).Walk v' v'),
      (W'.edges : Multiset (Sym2 (Fin n))) ≤ M ∧
      Multiset.card (W.edges : Multiset (Sym2 (Fin n)))
        < Multiset.card (W'.edges : Multiset (Sym2 (Fin n))) := by
  classical
  set R := M - (W.edges : Multiset (Sym2 (Fin n))) with hR
  have hMR : (W.edges : Multiset (Sym2 (Fin n))) + R = M := add_tsub_cancel_of_le hW
  have hRle : R ≤ M := tsub_le_self
  have hRdiag : ∀ e ∈ R, ¬ e.IsDiag := fun e he => hM e (Multiset.mem_of_le hRle he)
  have hRev : ∀ y, Even (mdeg R y) := by
    intro y
    have h1 := hev y
    have h2 := even_mdeg_edges_of_closed W y
    rw [← hMR, mdeg_add] at h1
    exact (Nat.even_add.mp h1).mp h2
  have hcardR : 0 < Multiset.card R := by
    rw [hR, Multiset.card_sub hW]
    omega
  -- some vertex of `W` has positive unused degree
  obtain ⟨u, hu, hdeg⟩ : ∃ u ∈ W.support, 0 < mdeg R u := by
    by_contra hcon
    push Not at hcon
    have hnot : ∀ e ∈ R, ∀ y ∈ e, y ∉ W.support := by
      intro e he y hy hys
      have h0 := hcon y hys
      have : 0 < mdeg R y := by
        unfold mdeg
        rw [Multiset.card_pos_iff_exists_mem]
        exact ⟨e, Multiset.mem_filter.mpr ⟨he, hy⟩⟩
      omega
    obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp hcardR
    induction e using Sym2.ind with
    | h a b =>
    have ha : a ∉ W.support := hnot _ he a (Sym2.mem_mk_left a b)
    obtain ⟨q⟩ := hT.2.2.preconnected v a
    obtain ⟨d, -, hdfst, hdsnd⟩ :=
      q.exists_boundary_dart {y | y ∈ W.support} W.start_mem_support ha
    have hdT : s(d.fst, d.snd) ∈ T := (SimpleGraph.fromEdgeSet_adj (s := (↑T : Set (Sym2 (Fin n))))).mp d.adj |>.1
    have hdM : s(d.fst, d.snd) ∈ M := Multiset.mem_of_le hTM (Finset.mem_val.mpr hdT)
    rw [← hMR, Multiset.mem_add] at hdM
    rcases hdM with h | h
    · exact hdsnd (W.snd_mem_support_of_mem_edges (Multiset.mem_coe.mp h))
    · exact hnot _ h d.fst (Sym2.mem_mk_left _ _) hdfst
  obtain ⟨C, hC, hCpos⟩ := exists_closed_walk_pos R hRdiag hRev hdeg
  refine ⟨u, (W.rotate u hu).append C, ?_, ?_⟩
  · rw [Walk.edges_append, ← Multiset.coe_add]
    have hrot : ((W.rotate u hu).edges : Multiset (Sym2 (Fin n)))
        = (W.edges : Multiset (Sym2 (Fin n))) :=
      Multiset.coe_eq_coe.mpr (W.rotate_edges u hu).perm
    rw [hrot]
    calc (W.edges : Multiset (Sym2 (Fin n))) + (C.edges : Multiset (Sym2 (Fin n)))
        ≤ (W.edges : Multiset (Sym2 (Fin n))) + R := by gcongr
      _ = M := hMR
  · rw [Walk.edges_append, ← Multiset.coe_add, Multiset.card_add]
    have hrot : Multiset.card ((W.rotate u hu).edges : Multiset (Sym2 (Fin n)))
        = Multiset.card (W.edges : Multiset (Sym2 (Fin n))) := by
      rw [Multiset.coe_card, Multiset.coe_card]
      exact (W.rotate_edges u hu).perm.length_eq
    have hCcard : 0 < Multiset.card (C.edges : Multiset (Sym2 (Fin n))) := by
      rw [Multiset.coe_card, Walk.length_edges]
      exact hCpos
    omega

/-! ### Euler -/

/-- **Euler's theorem for edge multisets.**  An even multigraph containing a spanning
tree has a closed walk using each of its edges exactly once (with multiplicity). -/
theorem exists_eulerian_closed_walk (M : Multiset (Sym2 (Fin n))) (hM : ∀ e ∈ M, ¬ e.IsDiag)
    (hev : ∀ z, Even (mdeg M z)) {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    (hTM : (T.val : Multiset (Sym2 (Fin n))) ≤ M) :
    ∃ (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v),
      (W.edges : Multiset (Sym2 (Fin n))) = M := by
  obtain ⟨v₀⟩ := hT.2.2.nonempty
  have key : ∀ k : ℕ, ∀ (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v),
      (W.edges : Multiset (Sym2 (Fin n))) ≤ M →
      Multiset.card M - Multiset.card (W.edges : Multiset (Sym2 (Fin n))) ≤ k →
      ∃ (v' : Fin n) (W' : (⊤ : SimpleGraph (Fin n)).Walk v' v'),
        (W'.edges : Multiset (Sym2 (Fin n))) = M := by
    intro k
    induction k with
    | zero =>
      intro v W hW hk
      exact ⟨v, W, Multiset.eq_of_le_of_card_le hW (by omega)⟩
    | succ k ih =>
      intro v W hW hk
      by_cases hle : Multiset.card M - Multiset.card (W.edges : Multiset (Sym2 (Fin n))) ≤ k
      · exact ih v W hW hle
      · obtain ⟨v', W', hW', hlt⟩ :=
          exists_longer_closed_walk M hM hev hT hTM W hW (by omega)
        exact ih v' W' hW' (by omega)
  exact key _ v₀ Walk.nil (by simp) le_rfl

/-- **The O-join output.**  For a spanning tree `T` and a loopless edge set `J` with
`T ⊎ J` of even degrees, a closed walk through every vertex of cost exactly
`c(T) + c(J)`. -/
theorem exists_spanning_closed_walk_core {c : Sym2 (Fin n) → ℝ} {T J : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) (hJ : ∀ e ∈ J, ¬ e.IsDiag)
    (heven : ∀ v : Fin n, Even (mdeg (T.val + J.val) v)) :
    ∃ (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v),
      (∀ u : Fin n, u ∈ W.support) ∧
      tourCost c W ≤ (∑ e ∈ T, c e) + ∑ e ∈ J, c e := by
  have hdiag : ∀ e ∈ (T.val + J.val : Multiset (Sym2 (Fin n))), ¬ e.IsDiag := by
    intro e he
    rcases Multiset.mem_add.mp he with h | h
    · exact hT.1 e (Finset.mem_val.mp h)
    · exact hJ e (Finset.mem_val.mp h)
  obtain ⟨v, W, hW⟩ := exists_eulerian_closed_walk (T.val + J.val) hdiag heven hT
    (Multiset.le_add_right _ _)
  refine ⟨v, W, ?_, ?_⟩
  · intro u
    by_cases huv : u = v
    · subst huv; exact W.start_mem_support
    · obtain ⟨q⟩ := hT.2.2.preconnected u v
      cases q with
      | nil => exact absurd rfl huv
      | @cons _ w _ h q' =>
        have hT' : s(u, w) ∈ T := (SimpleGraph.fromEdgeSet_adj (s := (↑T : Set (Sym2 (Fin n))))).mp h |>.1
        have hmem : s(u, w) ∈ (W.edges : Multiset (Sym2 (Fin n))) := by
          rw [hW]
          exact Multiset.mem_add.mpr (Or.inl (Finset.mem_val.mpr hT'))
        exact W.fst_mem_support_of_mem_edges (Multiset.mem_coe.mp hmem)
  · unfold tourCost
    have h1 : (W.edges.map c).sum = ((W.edges : Multiset (Sym2 (Fin n))).map c).sum := rfl
    rw [h1, hW, Multiset.map_add, Multiset.sum_add, Finset.sum_eq_multiset_sum,
      Finset.sum_eq_multiset_sum]

end TSPGap

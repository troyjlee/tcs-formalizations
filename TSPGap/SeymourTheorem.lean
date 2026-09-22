/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MultiGraphContract

/-!
# Seymour's theorem: packing `T`-cuts in a bipartite multigraph

**Seymour (1981).**  In a bipartite multigraph, for a minimum `T`-join `J` there are `|J|`
pairwise edge-disjoint `T`-cuts (`seymour`).  Together with the trivial direction (every
`T`-join meets every `T`-cut, `nonempty_inter_cut`) this is the min–max theorem
`min |T-join| = max #{disjoint T-cuts}`; the packing is the substantive half.

The proof follows Sebő and Conforti (Cornuéjols, *Packing and Covering*, Theorem 2.3),
rewritten in the even-set terms of `OJOIN_DESIGN.md`:

* the extremal choice: among all minimum `T`-joins and all paths inside them, a longest path
  `Q`, starting at `u` with first edge `ux`; then `deg_J u = 1` (`deg_eq_one_of_longest`);
* the **claim** (`claim_mem_of_wt_eq_zero`): a cycle through `u` of weight `0` contains `ux`.
  Case A (the cycle meets `Q` again at `y`): with `P` the prefix of `Q` to `y` and `A`, `B`
  the two arcs of the cycle, the even sets `P ∆ A`, `P ∆ B` have weights summing to
  `-2 |P \ C| ≤ -2`, so one is negative — contradicting minimality.  (The weight identity
  `wt_symmDiff` makes the "first vertex of `C` on `Q`" of the textbook proof unnecessary.)
  Case B (the cycle meets `Q` only at `u`): switching `J` along the cycle gives a minimum
  join containing `Q` extended by the cycle's edge at `u`, a longer path;
* **(★)** (`two_le_wt_cycle`): every cycle through `u` avoiding `ux` has weight `≥ 2`
  (nonnegative, even by bipartiteness, nonzero by the claim), hence (♠) and the contraction
  inequality (`sharp_of_cycles`, `card_restrict_le`): `J \ {ux}` is a minimum join of the
  star contraction;
* the **induction** on `Fintype.card V` (`seymour_aux`): the contraction has fewer vertices
  and is bipartite (`ccol`); its packing lifts back through `expand` (a vertex set of the
  contraction, with the contracted vertex replaced by the star), the lifted cuts are the
  same edge sets (`cut_expand`), stay `T`-cuts (`odd_card_expand_inter`) and disjoint; the
  cut `δ({u})` is a further `T`-cut disjoint from all of them.

A packing is an indexed family `Fin k → Finset V` (`IsCutPacking`); the consumers count
`#{i : e ∈ δ(S i)}` directly.
-/

universe u v

namespace TSPGap
namespace MGraph

open Finset
open Classical
open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E] (G : MGraph V E)

/-! ### Packings -/

/-- A packing of `T`-cuts: `k` vertex sets, each holding an odd number of terminals, with
pairwise disjoint cuts. -/
def IsCutPacking (T : Finset V) {k : ℕ} (S : Fin k → Finset V) : Prop :=
  (∀ i, Odd (S i ∩ T).card) ∧ ∀ i j, i ≠ j → Disjoint (G.cut (S i)) (G.cut (S j))

theorem isCutPacking_cast {T : Finset V} {k k' : ℕ} (h : k' = k) {S : Fin k → Finset V}
    (hS : G.IsCutPacking T S) : G.IsCutPacking T (S ∘ Fin.cast h) := by
  refine ⟨fun i => hS.1 _, fun i j hij => hS.2 _ _ ?_⟩
  intro heq
  exact hij (Fin.ext (by simpa using congrArg Fin.val heq))

/-- Adding a cut disjoint from all the others. -/
theorem isCutPacking_cons {T : Finset V} {k : ℕ} {S : Fin k → Finset V}
    (hS : G.IsCutPacking T S) {S₀ : Finset V} (h₀ : Odd (S₀ ∩ T).card)
    (hdisj : ∀ i, Disjoint (G.cut S₀) (G.cut (S i))) :
    G.IsCutPacking T (Fin.cons S₀ S) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h₀
    · simpa using hS.1 i
  · revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · exact absurd rfl hij
    · simpa using hdisj j
    · simpa using (hdisj i).symm
    · simp only [Fin.cons_succ]
      exact hS.2 i j (fun h => hij (by rw [h]))

/-! ### Weights of symmetric differences -/

theorem wt_symmDiff (J X Y : Finset E) :
    wt J (X ∆ Y) = wt J X + wt J Y - 2 * wt J (X ∩ Y) := by
  have hX : wt J X = wt J (X \ Y) + wt J (X ∩ Y) := by
    rw [← wt_add_of_disjoint J (disjoint_sdiff_inter _ _), sdiff_union_inter]
  have hY : wt J Y = wt J (Y \ X) + wt J (X ∩ Y) := by
    rw [inter_comm, ← wt_add_of_disjoint J (disjoint_sdiff_inter _ _), sdiff_union_inter]
  rw [Finset.symmDiff_def, wt_add_of_disjoint J disjoint_sdiff_sdiff, hX, hY]
  ring

/-! ### Walk facts for the claim -/

namespace Walk

variable {G}

theorem takeUntil_cons_of_ne {u v w : V} (e : E) (he : G.ends e = s(u, v)) (p : Walk G v w)
    {x : V} (h : x ∈ (cons e he p).support) (hux : u ≠ x) :
    (cons e he p).takeUntil x h = cons e he (p.takeUntil x (by
      rcases List.mem_cons.mp h with rfl | h'
      · exact absurd rfl hux
      · exact h')) := by
  rw [takeUntil, dif_neg hux]

theorem mem_support_takeUntil {u w : V} (p : Walk G u w) {x : V} (h : x ∈ p.support) {z : V}
    (hz : z ∈ (p.takeUntil x h).support) : z ∈ p.support := by
  rw [support_takeUntil, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact List.takeWhile_subset _ hz
  · exact h

omit [Fintype V] [Fintype E] in
theorem eq_of_edges_eq_nil {u w : V} (p : Walk G u w) (h : p.edges = []) : u = w := by
  cases p with
  | nil => rfl
  | cons e he p => simp at h

omit [Fintype V] [Fintype E] in
theorem support_cons_eq {u v w : V} (e : E) (he : G.ends e = s(u, v)) (p : Walk G v w) :
    (cons e he p).support = u :: p.support := rfl

end Walk

/-! ### Lifting a packing through the star contraction -/

section Lift

variable (U : Finset V)

omit [Fintype V] [Fintype E] in
theorem lift_inter (D D' : Finset {e // G.OutU U e}) :
    G.lift U (D ∩ D') = G.lift U D ∩ G.lift U D' := map_inter _ _

omit [Fintype V] [Fintype E] in
theorem disjoint_lift {D D' : Finset {e // G.OutU U e}} (h : Disjoint D D') :
    Disjoint (G.lift U D) (G.lift U D') := (disjoint_map _).mpr h

theorem lift_restrict_inter (J : Finset E) (C : Finset {e // G.OutU U e}) :
    G.lift U (G.restrict U J ∩ C) = J ∩ G.lift U C := by
  ext e
  simp only [mem_lift, mem_inter, mem_restrict]
  constructor
  · rintro ⟨h, hJ, hC⟩
    exact ⟨hJ, h, hC⟩
  · rintro ⟨hJ, h, hC⟩
    exact ⟨h, hJ, hC⟩

/-- A vertex set of the contraction, read back in `G`: the contracted vertex stands for
all of `U`. -/
noncomputable def expand (S : Finset (Option {v // v ∉ U})) : Finset V :=
  univ.filter fun v => cvert U v ∈ S

theorem mem_expand {S : Finset (Option {v // v ∉ U})} {v : V} :
    v ∈ expand U S ↔ cvert U v ∈ S := by simp [expand]

/-- The cut of the expanded set is the lifted cut. -/
theorem cut_expand (S : Finset (Option {v // v ∉ U})) :
    G.cut (expand U S) = G.lift U ((G.contract U).cut S) := by
  ext e
  rw [mem_cut, mem_lift]
  simp only [mem_expand]
  constructor
  · rintro ⟨⟨a, ha, haS⟩, ⟨b, hb, hbS⟩⟩
    have h : G.OutU U e := by
      intro hin
      rw [cvert_of_mem (hin a ha)] at haS
      rw [cvert_of_mem (hin b hb)] at hbS
      exact hbS haS
    refine ⟨h, ?_⟩
    rw [mem_cut]
    change (∃ a ∈ (G.ends e).map (cvert U), a ∈ S) ∧
      ∃ b ∈ (G.ends e).map (cvert U), b ∉ S
    exact ⟨⟨cvert U a, Sym2.mem_map.mpr ⟨a, ha, rfl⟩, haS⟩,
      ⟨cvert U b, Sym2.mem_map.mpr ⟨b, hb, rfl⟩, hbS⟩⟩
  · rintro ⟨h, hc⟩
    rw [mem_cut] at hc
    change (∃ a ∈ (G.ends e).map (cvert U), a ∈ S) ∧
      (∃ b ∈ (G.ends e).map (cvert U), b ∉ S) at hc
    obtain ⟨⟨a', ha', haS⟩, ⟨b', hb', hbS⟩⟩ := hc
    obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Sym2.mem_map.mp hb'
    exact ⟨⟨a, ha, haS⟩, ⟨b, hb, hbS⟩⟩

/-- The expanded set is a `T`-cut set iff the original is a `cterm T`-cut set (through the
parity of a join). -/
theorem odd_card_expand_inter {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J)
    (S : Finset (Option {v // v ∉ U})) :
    Odd (expand U S ∩ T).card ↔ Odd (S ∩ cterm U T).card := by
  have h1 := G.odd_card_inter_cut_iff (expand U S) hJ
  have h2 := (G.contract U).odd_card_inter_cut_iff S (G.isJoin_restrict U hJ)
  rw [← h1, cut_expand, ← lift_restrict_inter, card_lift]
  convert h2 using 3 <;> congr <;> exact Subsingleton.elim _ _

/-- The bipartite colouring of the contraction of a star. -/
def ccol (col : V → Bool) (u : V) : Option {v // v ∉ U} → Bool
  | none => !col u
  | some v => col v.1

/-- Across an edge leaving the star of `u` from a vertex of the star, the outside end has
the colour of `u`. -/
theorem col_eq_of_star_edge {col : V → Bool} (hcol : G.IsBipartite col) {u x y : V} {e : E}
    (he : G.ends e = s(x, y)) (hx : x ∈ G.star u) (hy : y ∉ G.star u) : col y = col u := by
  unfold star at hx hy
  rw [mem_insert] at hx hy
  rcases hx with rfl | hx
  · exact absurd (Or.inr (G.mem_nbrs.mpr ⟨e, he⟩)) hy
  · obtain ⟨f, hf⟩ := G.mem_nbrs.mp hx
    have h1 := hcol f u x hf
    have h2 := hcol e x y he
    cases hcu : col u <;> cases hcx : col x <;> cases hcy : col y <;> simp_all

theorem ccol_ne {col : V → Bool} (hcol : G.IsBipartite col) {u x y : V} {e : E}
    (he : G.ends e = s(x, y)) (hnot : ¬ (x ∈ G.star u ∧ y ∈ G.star u)) :
    ccol (G.star u) col u (cvert (G.star u) x) ≠ ccol (G.star u) col u (cvert (G.star u) y) := by
  by_cases hx : x ∈ G.star u <;> by_cases hy : y ∈ G.star u
  · exact absurd ⟨hx, hy⟩ hnot
  · rw [cvert_of_mem hx, cvert_of_notMem hy]
    change (!col u) ≠ col y
    rw [G.col_eq_of_star_edge hcol he hx hy]
    simp
  · rw [cvert_of_notMem hx, cvert_of_mem hy]
    change col x ≠ (!col u)
    rw [G.col_eq_of_star_edge hcol (by rw [he, Sym2.eq_swap]) hy hx]
    simp
  · rw [cvert_of_notMem hx, cvert_of_notMem hy]
    exact hcol e x y he

theorem isBipartite_contract_star {col : V → Bool} (hcol : G.IsBipartite col) (u : V) :
    (G.contract (G.star u)).IsBipartite (ccol (G.star u) col u) := by
  rintro ⟨e, he⟩ a' b' hab'
  change (G.ends e).map (cvert (G.star u)) = s(a', b') at hab'
  obtain ⟨a, b, hab⟩ : ∃ a b, G.ends e = s(a, b) :=
    Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) (G.ends e)
  rw [hab, Sym2.map_mk, Sym2.eq_iff] at hab'
  have hnot : ¬ (a ∈ G.star u ∧ b ∈ G.star u) := by
    rintro ⟨ha, hb⟩
    apply he
    rw [hab]
    intro c hc
    rw [Sym2.mem_iff] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact hb
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact G.ccol_ne hcol hab hnot
  · exact (G.ccol_ne hcol hab hnot).symm

end Lift

/-! ### The claim and (★) -/

theorem exists_ends_eq_ne (e : E) : ∃ a b, G.ends e = s(a, b) ∧ a ≠ b := by
  obtain ⟨a, b, hab⟩ : ∃ a b, G.ends e = s(a, b) :=
    Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) (G.ends e)
  exact ⟨a, b, hab, Walk.ne_of_ends hab⟩

/-- **The claim**: for the extremal minimum join `J` and the longest path `Q = ux · Q'`
inside it, every cycle through `u` of weight `0` contains `ux`. -/
theorem claim_mem_of_wt_eq_zero {T : Finset V} {J : Finset E} (hJ : G.IsMinJoin T J)
    {u x w : V} {ux : E} (hux : G.ends ux = s(u, x)) (Q' : Walk G x w)
    (hQ : (Walk.cons ux hux Q').IsPath) (hQJ : (Walk.cons ux hux Q').edgeSet ⊆ J)
    (hdeg : G.deg J u = 1)
    (hmax : ∀ {a' b' : V} (q : Walk G a' b'),
      (∃ J', G.IsMinJoin T J' ∧ q.edgeSet ⊆ J' ∧ q.IsPath) →
        q.length ≤ (Walk.cons ux hux Q').length)
    (c : Walk G u u) (hc : c.IsCycle) (hc0 : wt J c.edgeSet = 0) : ux ∈ c.edgeSet := by
  classical
  set Q := Walk.cons ux hux Q' with hQdef
  by_contra hux_c
  have hmin : ∀ D, G.IsEven D → 0 ≤ wt J D := (G.isMinJoin_iff hJ.1).mp hJ
  by_cases hA : ∃ y ∈ c.support, y ∈ Q.support ∧ y ≠ u
  · -- Case A: the cycle meets `Q` again at `y`
    obtain ⟨y, hyc, hyQ, hyu⟩ := hA
    set P := Q.takeUntil y hyQ with hPdef
    have hPsub := Walk.edges_takeUntil_sublist Q y hyQ
    have hPtrail : P.IsTrail := (Walk.isTrail_of_isPath hQ).sublist hPsub
    have hPJ : P.edgeSet ⊆ J := fun e he =>
      hQJ (Walk.mem_edgeSet.mpr (hPsub.subset (Walk.mem_edgeSet.mp he)))
    have hPux : ux ∈ P.edgeSet := by
      show ux ∈ ((Walk.cons ux hux Q').takeUntil y hyQ).edgeSet
      rw [Walk.takeUntil_cons_of_ne ux hux Q' hyQ hyu.symm, Walk.mem_edgeSet, Walk.edges_cons]
      exact List.mem_cons_self
    obtain ⟨A, B, hA, hB, hAB, hABc⟩ := Walk.exists_arcs hc hyc
    have hoddP : G.odd P.edgeSet = {u, y} := Walk.odd_edgeSet_of_ne hPtrail hyu.symm
    have hoddA : G.odd A.edgeSet = {u, y} := Walk.odd_edgeSet_of_ne hA hyu.symm
    have hoddB : G.odd B.edgeSet = {u, y} := by
      rw [Walk.odd_edgeSet_of_ne hB hyu, pair_comm]
    have hevA : G.IsEven (P.edgeSet ∆ A.edgeSet) := by
      rw [isEven_iff_odd_eq_empty, odd_symmDiff, hoddP, hoddA, symmDiff_self, bot_eq_empty]
    have hevB : G.IsEven (P.edgeSet ∆ B.edgeSet) := by
      rw [isEven_iff_odd_eq_empty, odd_symmDiff, hoddP, hoddB, symmDiff_self, bot_eq_empty]
    have h0A := hmin _ hevA
    have h0B := hmin _ hevB
    rw [wt_symmDiff] at h0A h0B
    have hwP : wt J P.edgeSet = -(P.edgeSet.card : ℤ) := wt_of_subset hPJ
    have hwPA : wt J (P.edgeSet ∩ A.edgeSet) = -((P.edgeSet ∩ A.edgeSet).card : ℤ) :=
      wt_of_subset (inter_subset_left.trans hPJ)
    have hwPB : wt J (P.edgeSet ∩ B.edgeSet) = -((P.edgeSet ∩ B.edgeSet).card : ℤ) :=
      wt_of_subset (inter_subset_left.trans hPJ)
    have hwc : wt J A.edgeSet + wt J B.edgeSet = 0 := by
      rw [← wt_add_of_disjoint J hAB, hABc, hc0]
    have hcard : (P.edgeSet ∩ A.edgeSet).card + (P.edgeSet ∩ B.edgeSet).card =
        (P.edgeSet ∩ c.edgeSet).card := by
      rw [← hABc, inter_union_distrib_left, card_union_of_disjoint]
      exact disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right hAB)
    have hlt : (P.edgeSet ∩ c.edgeSet).card < P.edgeSet.card :=
      card_lt_card (Finset.ssubset_def.mpr
        ⟨inter_subset_left, fun h => hux_c (mem_inter.mp (h hPux)).2⟩)
    have hcard' : ((P.edgeSet ∩ A.edgeSet).card : ℤ) + (P.edgeSet ∩ B.edgeSet).card =
        (P.edgeSet ∩ c.edgeSet).card := by exact_mod_cast hcard
    have hlt' : ((P.edgeSet ∩ c.edgeSet).card : ℤ) < P.edgeSet.card := by exact_mod_cast hlt
    linarith
  · -- Case B: the cycle meets `Q` only at `u`; extend `Q` into `J ∆ C`
    push Not at hA
    cases c with
    | nil => exact hc.1 rfl
    | @cons _ z _ e he c' =>
      have hz : z ∈ (Walk.cons e he c').support := by
        rw [Walk.support_cons_eq]
        exact List.mem_cons_of_mem _ (Walk.start_mem_support c')
      have hzu : z ≠ u := (Walk.ne_of_ends he).symm
      have hzQ : z ∉ Q.support := fun h => hzu (hA z hz h)
      have he_c : e ∈ (Walk.cons e he c').edgeSet := by
        rw [Walk.mem_edgeSet, Walk.edges_cons]
        exact List.mem_cons_self
      have huxu : u ∈ G.ends ux := by rw [hux]; exact Sym2.mem_mk_left _ _
      have huxQ : ux ∈ Q.edgeSet := by
        show ux ∈ (Walk.cons ux hux Q').edgeSet
        rw [Walk.mem_edgeSet, Walk.edges_cons]
        exact List.mem_cons_self
      have heu : u ∈ G.ends e := by rw [he]; exact Sym2.mem_mk_left _ _
      have heJ : e ∉ J := by
        intro heJ
        have h2 : 1 < G.deg J u := one_lt_card.mpr
          ⟨e, G.mem_inc.mpr ⟨heJ, heu⟩, ux, G.mem_inc.mpr ⟨hQJ huxQ, huxu⟩,
            fun h => hux_c (h ▸ he_c)⟩
        omega
      have hJ' : G.IsMinJoin T (J ∆ (Walk.cons e he c').edgeSet) :=
        G.isMinJoin_symmDiff hJ (Walk.isEven_edgeSet_of_closed hc.2.1) hc0
      -- no edge of `Q` lies on the cycle
      have hQc : ∀ f ∈ Q.edgeSet, f ∉ (Walk.cons e he c').edgeSet := by
        intro f hfQ hfc
        obtain ⟨a, b, hab, hne⟩ := G.exists_ends_eq_ne f
        have h1 := Walk.ends_mem_support (Walk.mem_edgeSet.mp hfQ)
        have h2 := Walk.ends_mem_support (Walk.mem_edgeSet.mp hfc)
        rw [hab] at h1 h2
        have ha := hA a (h2 a (Sym2.mem_mk_left _ _)) (h1 a (Sym2.mem_mk_left _ _))
        have hb := hA b (h2 b (Sym2.mem_mk_right _ _)) (h1 b (Sym2.mem_mk_right _ _))
        exact hne (ha.trans hb.symm)
      have he' : G.ends e = s(z, u) := by rw [he, Sym2.eq_swap]
      have hR := hmax (Walk.cons e he' Q) ⟨_, hJ', ?_, Walk.isPath_cons hQ he' hzQ⟩
      · simp [Walk.length] at hR
      · intro f hf
        rw [Walk.mem_edgeSet, Walk.edges_cons] at hf
        rw [mem_symmDiff]
        rcases List.mem_cons.mp hf with rfl | hf
        · exact Or.inr ⟨he_c, heJ⟩
        · exact Or.inl ⟨hQJ (Walk.mem_edgeSet.mpr hf), hQc f (Walk.mem_edgeSet.mpr hf)⟩

/-- **(★)**: every cycle through `u` avoiding `ux` has weight at least `2`. -/
theorem two_le_wt_cycle {col : V → Bool} (hcol : G.IsBipartite col) {T : Finset V}
    {J : Finset E} (hJ : G.IsMinJoin T J)
    {u x w : V} {ux : E} (hux : G.ends ux = s(u, x)) (Q' : Walk G x w)
    (hQ : (Walk.cons ux hux Q').IsPath) (hQJ : (Walk.cons ux hux Q').edgeSet ⊆ J)
    (hdeg : G.deg J u = 1)
    (hmax : ∀ {a' b' : V} (q : Walk G a' b'),
      (∃ J', G.IsMinJoin T J' ∧ q.edgeSet ⊆ J' ∧ q.IsPath) →
        q.length ≤ (Walk.cons ux hux Q').length)
    (c : Walk G u u) (hc : c.IsCycle) (hux_c : ux ∉ c.edgeSet) : 2 ≤ wt J c.edgeSet := by
  have heven := Walk.isEven_edgeSet_of_closed hc.2.1
  have h0 := (G.isMinJoin_iff hJ.1).mp hJ _ heven
  have hev := G.even_wt_of_isEven hcol J heven
  have hne : wt J c.edgeSet ≠ 0 := fun h =>
    hux_c (G.claim_mem_of_wt_eq_zero hJ hux Q' hQ hQJ hdeg hmax c hc h)
  obtain ⟨m, hm⟩ := hev
  omega

/-! ### The induction -/

/-- The number of vertices of the star contraction is smaller. -/
theorem card_contract_star_lt {u x : V} {ux : E} (hux : G.ends ux = s(u, x)) :
    Fintype.card (Option {v // v ∉ G.star u}) < Fintype.card V := by
  rw [Fintype.card_option, Fintype.card_subtype]
  have h1 : (univ.filter fun v => v ∉ G.star u) = (G.star u)ᶜ := by
    ext v; simp
  rw [h1, card_compl]
  have h2 : 2 ≤ (G.star u).card := by
    unfold star
    rw [card_insert_of_notMem (G.notMem_nbrs_self u)]
    have : 0 < (G.nbrs u).card := card_pos.mpr ⟨x, G.mem_nbrs.mpr ⟨ux, hux⟩⟩
    omega
  have h3 := card_le_univ (G.star u)
  omega

/-- Seymour's theorem, in the form used for the induction on the number of vertices. -/
theorem seymour_aux (n : ℕ) :
    ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E] (G : MGraph V E),
      Fintype.card V = n → ∀ {col : V → Bool}, G.IsBipartite col →
      ∀ {T : Finset V} {J : Finset E}, G.IsMinJoin T J →
        ∃ S : Fin J.card → Finset V, G.IsCutPacking T S := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E _ _ G hn col hcol T J hJ
  by_cases hT : T = ∅
  · -- base: no terminals, the empty join, the empty packing
    have h0 : G.IsJoin T ∅ := by
      rw [IsJoin, G.isEven_iff_odd_eq_empty.mp G.isEven_empty, hT]
    have hcard : J.card = 0 := Nat.le_zero.mp (hJ.2 ∅ h0)
    exact ⟨fun _ => ∅, fun i => (Fin.cast hcard i).elim0,
      fun i _ _ => (Fin.cast hcard i).elim0⟩
  -- the join is nonempty
  have hJne : J.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    have h1 := hJ.1
    rw [h, IsJoin, G.isEven_iff_odd_eq_empty.mp G.isEven_empty] at h1
    exact hT h1.symm
  -- the extremal choice: a longest path among all paths inside minimum joins
  obtain ⟨a, b, Q, ⟨J', hJ', hQJ, hQ⟩, hmax⟩ := Walk.exists_max_length (G := G)
    (fun {a b} q => ∃ J', G.IsMinJoin T J' ∧ q.edgeSet ⊆ J' ∧ q.IsPath) (Fintype.card V)
    (fun p ⟨_, _, _, hp⟩ => by have := Walk.length_le_card_of_isPath hp; omega)
    (by
      obtain ⟨e, he⟩ := hJne
      obtain ⟨a, b, hab, hne⟩ := G.exists_ends_eq_ne e
      refine ⟨a, b, Walk.cons e hab Walk.nil, J, hJ, ?_, ?_⟩
      · intro f hf
        rw [Walk.mem_edgeSet, Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at hf
        rw [hf]; exact he
      · simp [Walk.IsPath, Walk.support, hne])
  -- all minimum joins have the same size: it suffices to pack `|J'|` cuts
  have hcard : J.card = J'.card := le_antisymm (hJ.2 J' hJ'.1) (hJ'.2 J hJ.1)
  suffices h : ∃ S : Fin J'.card → Finset V, G.IsCutPacking T S by
    obtain ⟨S, hS⟩ := h
    exact ⟨S ∘ Fin.cast hcard, G.isCutPacking_cast hcard hS⟩
  clear hcard hJ hJne J
  rename' J' => J, hJ' => hJ
  -- `Q` has an edge
  have hne : Q.edges ≠ [] := by
    intro h
    obtain ⟨e, he⟩ : J.Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro h'
      have h1 := hJ.1
      rw [h', IsJoin, G.isEven_iff_odd_eq_empty.mp G.isEven_empty] at h1
      exact hT h1.symm
    obtain ⟨a', b', hab, hne⟩ := G.exists_ends_eq_ne e
    have := hmax (Walk.cons e hab Walk.nil) ⟨J, hJ, ?_, ?_⟩
    · simp [Walk.length, h] at this
    · intro f hf
      rw [Walk.mem_edgeSet, Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at hf
      rw [hf]; exact he
    · simp [Walk.IsPath, Walk.support, hne]
  have hdeg : G.deg J a = 1 :=
    Walk.deg_eq_one_of_longest (fun C hC hsub => G.eq_empty_of_isEven_of_subset hJ hC hsub)
      hQ hQJ hne (fun q hq hqJ => hmax q ⟨J, hJ, hqJ, hq⟩)
  cases Q with
  | nil => exact (hne rfl).elim
  | @cons _ x _ ux hux Q' =>
  have huxJ : ux ∈ J := hQJ (by rw [Walk.mem_edgeSet, Walk.edges_cons]; exact List.mem_cons_self)
  have hstar := G.noNbrEdge_of_bipartite hcol a
  have huxu : a ∈ G.ends ux := by rw [hux]; exact Sym2.mem_mk_left _ _
  have hsp := G.sharp_of_cycles hJ huxu
    (fun c hc hnot => G.two_le_wt_cycle hcol hJ hux Q' hQ hQJ hdeg hmax c hc hnot)
  -- the contraction and its minimum join
  have hJstar : (G.contract (G.star a)).IsMinJoin (cterm (G.star a) T) (G.restrict (G.star a) J) :=
    ⟨G.isJoin_restrict (G.star a) hJ.1,
      fun K hK => G.card_restrict_le hstar hJ hux huxJ hdeg hsp hK⟩
  obtain ⟨S, hS⟩ := ih _ (hn ▸ G.card_contract_star_lt hux) (G.contract (G.star a)) rfl
    (G.isBipartite_contract_star hcol a) hJstar
  -- lift the packing and add `δ({a})`
  have haT : a ∈ T := (G.isJoin_iff.mp hJ.1 a).mpr (by rw [hdeg]; exact odd_one)
  have hpack : G.IsCutPacking T (Fin.cons {a} fun i => expand (G.star a) (S i)) := by
    refine G.isCutPacking_cons ⟨fun i => ?_, fun i j hij => ?_⟩ ?_ ?_
    · have h := hS.1 i
      refine (G.odd_card_expand_inter (G.star a) hJ.1 (S i)).mpr ?_
      convert h using 3
      congr
      exact Subsingleton.elim _ _
    · rw [G.cut_expand (G.star a), G.cut_expand (G.star a)]
      exact G.disjoint_lift (G.star a) (hS.2 i j hij)
    · rw [singleton_inter_of_mem haT, card_singleton]
      exact odd_one
    · intro i
      rw [G.cut_expand (G.star a), disjoint_left]
      intro e he hel
      have h1 := G.outU_of_mem_lift (G.star a) hel
      rw [G.outU_star_iff hstar] at h1
      apply h1
      obtain ⟨⟨c, hc, hc'⟩, -⟩ := G.mem_cut.mp he
      rw [mem_singleton] at hc'
      rw [← hc']; exact hc
  have hcard : J.card = (G.restrict (G.star a) J).card + 1 := by
    have h := G.card_restrict (G.star a) J
    rw [G.inside_star_eq_inc hstar] at h
    change (G.restrict (G.star a) J).card + G.deg J a = J.card at h
    omega
  exact ⟨_ ∘ Fin.cast hcard, G.isCutPacking_cast hcard hpack⟩

/-- **Seymour's theorem.**  In a bipartite multigraph, a minimum `T`-join `J` is matched by
`|J|` pairwise edge-disjoint `T`-cuts. -/
theorem seymour {col : V → Bool} (hcol : G.IsBipartite col) {T : Finset V} {J : Finset E}
    (hJ : G.IsMinJoin T J) : ∃ S : Fin J.card → Finset V, G.IsCutPacking T S :=
  seymour_aux _ G rfl hcol hJ


end MGraph
end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

/-!
# Labelled multigraphs: degrees, even edge sets, `T`-joins, cuts

The combinatorial substrate for Edmonds–Johnson (`OJOIN_DESIGN.md`).  A **multigraph** is a
finite type of vertices, a finite type of edge labels, and an endpoint map into `Sym2 V`
with no loops; parallel edges are distinct labels, which is what the contraction step of
Seymour's theorem produces and what joins, cuts and packings must keep apart.

For an edge finset `D`:
* `deg D v` counts the edges of `D` at `v`; `odd D` is the set of odd-degree vertices —
  the **boundary modulo two** of `D`;
* `IsEven D` says every degree is even, `IsJoin T D` that the boundary is `T`;
* `odd (D ∆ D') = odd D ∆ odd D'` (`odd_symmDiff`), so `J ∆ D` is a `T`-join exactly when
  `D` is even (`isJoin_symmDiff_iff`);
* the weight `wt J D = |D ∖ J| − |D ∩ J|` (an integer) satisfies
  `|J ∆ D| = |J| + wt J D`, and a `T`-join is minimum iff `0 ≤ wt J C` for every even `C`
  (`isMinJoin_iff`) — Cornuéjols' Remark 2.6 in even-set form;
* cuts `cut S`, the handshake `∑ deg = 2|D|` and its restriction to `S`, so that a
  `T`-join meets every `T`-cut (`odd_card_inter_cut`);
* bipartite colourings, under which every even set has even size (`even_card_of_isEven`)
  and every weight of an even set is even (`even_wt_of_isEven`).
-/

namespace TSPGap

/-- A finite loopless multigraph: edge labels with an endpoint map. -/
structure MGraph (V E : Type*) where
  /-- The two endpoints of an edge. -/
  ends : E → Sym2 V
  /-- No loops. -/
  loopless : ∀ e, ¬ (ends e).IsDiag

namespace MGraph

open Finset
open Classical
open scoped symmDiff

variable {V E : Type*} [Fintype V] [Fintype E] (G : MGraph V E)

/-! ### Degrees and the boundary modulo two -/

/-- The edges of `D` at `v`. -/
noncomputable def inc (D : Finset E) (v : V) : Finset E := D.filter fun e => v ∈ G.ends e

/-- The degree of `v` in the edge set `D`. -/
noncomputable def deg (D : Finset E) (v : V) : ℕ := (G.inc D v).card

/-- The odd-degree vertices of `D`: its boundary modulo two. -/
noncomputable def odd (D : Finset E) : Finset V := univ.filter fun v => Odd (G.deg D v)

/-- An even edge set: every degree is even. -/
def IsEven (D : Finset E) : Prop := ∀ v, Even (G.deg D v)

/-- A `T`-join: the odd-degree vertices are exactly `T`. -/
def IsJoin (T : Finset V) (J : Finset E) : Prop := G.odd J = T

/-- A minimum `T`-join. -/
def IsMinJoin (T : Finset V) (J : Finset E) : Prop :=
  G.IsJoin T J ∧ ∀ K, G.IsJoin T K → J.card ≤ K.card

theorem mem_inc {D : Finset E} {v : V} {e : E} : e ∈ G.inc D v ↔ e ∈ D ∧ v ∈ G.ends e := by
  simp [inc]

theorem mem_odd {D : Finset E} {v : V} : v ∈ G.odd D ↔ Odd (G.deg D v) := by
  simp [odd]

theorem isJoin_iff {T : Finset V} {J : Finset E} :
    G.IsJoin T J ↔ ∀ v, v ∈ T ↔ Odd (G.deg J v) := by
  unfold IsJoin
  constructor
  · intro h v
    rw [← h, mem_odd]
  · intro h
    ext v
    rw [mem_odd, h]

theorem isEven_iff_odd_eq_empty {D : Finset E} : G.IsEven D ↔ G.odd D = ∅ := by
  constructor
  · intro h
    refine eq_empty_of_forall_notMem fun v hv => ?_
    rw [mem_odd] at hv
    exact (Nat.not_even_iff_odd.mpr hv) (h v)
  · intro h v
    by_contra hv
    rw [Nat.not_even_iff_odd] at hv
    exact (notMem_empty v) (h ▸ (G.mem_odd.mpr hv))

theorem isEven_empty : G.IsEven ∅ := fun v => by simp [deg, inc]

theorem inc_symmDiff (D D' : Finset E) (v : V) :
    G.inc (D ∆ D') v = G.inc D v ∆ G.inc D' v := by
  ext e
  simp only [mem_inc, mem_symmDiff]
  tauto

theorem inc_sdiff (D D' : Finset E) (v : V) : G.inc (D \ D') v = G.inc D v \ G.inc D' v := by
  ext e
  simp only [mem_inc, mem_sdiff]
  tauto

theorem inc_inter (D D' : Finset E) (v : V) : G.inc (D ∩ D') v = G.inc D v ∩ G.inc D' v := by
  ext e
  simp only [mem_inc, mem_inter]
  tauto

theorem inc_mono {D D' : Finset E} (h : D ⊆ D') (v : V) : G.inc D v ⊆ G.inc D' v :=
  fun e he => by
    rw [mem_inc] at he ⊢
    exact ⟨h he.1, he.2⟩

/-- `|A ∆ B| + 2 |A ∩ B| = |A| + |B|`. -/
theorem card_symmDiff_add {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff,
    ← card_sdiff_add_card_inter A B,
    ← card_sdiff_add_card_inter B A, inter_comm B A]
  ring

theorem odd_card_symmDiff_iff {α : Type*} [DecidableEq α] (A B : Finset α) :
    Odd (A ∆ B).card ↔ (Odd A.card ↔ ¬ Odd B.card) := by
  have h := card_symmDiff_add A B
  rw [Nat.odd_iff, Nat.odd_iff, Nat.odd_iff]
  omega

theorem deg_symmDiff_odd_iff (D D' : Finset E) (v : V) :
    Odd (G.deg (D ∆ D') v) ↔ (Odd (G.deg D v) ↔ ¬ Odd (G.deg D' v)) := by
  rw [deg, inc_symmDiff, odd_card_symmDiff_iff]
  rfl

/-- **The boundary of a symmetric difference** is the symmetric difference of the
boundaries. -/
theorem odd_symmDiff (D D' : Finset E) : G.odd (D ∆ D') = G.odd D ∆ G.odd D' := by
  ext v
  rw [mem_odd, mem_symmDiff, mem_odd, mem_odd, deg_symmDiff_odd_iff]
  tauto

theorem deg_sdiff_of_subset {D D' : Finset E} (h : D' ⊆ D) (v : V) :
    G.deg (D \ D') v = G.deg D v - G.deg D' v := by
  rw [deg, deg, deg, inc_sdiff]
  have := card_sdiff_add_card_eq_card (G.inc_mono h v)
  omega

theorem deg_add_of_disjoint {D D' : Finset E} (h : Disjoint D D') (v : V) :
    G.deg (D ∪ D') v = G.deg D v + G.deg D' v := by
  rw [deg, deg, deg]
  have : G.inc (D ∪ D') v = G.inc D v ∪ G.inc D' v := by
    ext e
    simp only [mem_inc, mem_union]
    tauto
  rw [this, card_union_of_disjoint]
  exact disjoint_left.mpr fun e he he' =>
    disjoint_left.mp h (G.mem_inc.mp he).1 (G.mem_inc.mp he').1

/-- `J ∆ D` is a `T`-join iff `D` is even, for a `T`-join `J`. -/
theorem isJoin_symmDiff_iff {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) (D : Finset E) :
    G.IsJoin T (J ∆ D) ↔ G.IsEven D := by
  rw [IsJoin, odd_symmDiff, hJ, isEven_iff_odd_eq_empty, symmDiff_eq_left]
  rfl

theorem isEven_symmDiff_of_isJoin {T : Finset V} {J K : Finset E} (hJ : G.IsJoin T J)
    (hK : G.IsJoin T K) : G.IsEven (J ∆ K) := by
  rw [isEven_iff_odd_eq_empty, odd_symmDiff, hJ, hK, symmDiff_self]
  rfl

theorem isEven_sdiff_of_subset {D C : Finset E} (hD : G.IsEven D) (hC : G.IsEven C)
    (hsub : C ⊆ D) : G.IsEven (D \ C) := by
  intro v
  rw [deg_sdiff_of_subset G hsub]
  obtain ⟨a, ha⟩ := hD v
  obtain ⟨b, hb⟩ := hC v
  have : G.deg C v ≤ G.deg D v := card_le_card (G.inc_mono hsub v)
  exact ⟨a - b, by omega⟩

theorem isEven_union_of_disjoint {D C : Finset E} (hD : G.IsEven D) (hC : G.IsEven C)
    (h : Disjoint D C) : G.IsEven (D ∪ C) := fun v => by
  rw [deg_add_of_disjoint G h]
  exact (hD v).add (hC v)

/-! ### The weight of an edge set against a join -/

/-- `wt J D = |D ∖ J| − |D ∩ J|`: the change of size of `J` under `D`. -/
noncomputable def wt (J D : Finset E) : ℤ := ((D \ J).card : ℤ) - (D ∩ J).card

theorem card_symmDiff_eq_add_wt (J D : Finset E) :
    ((J ∆ D).card : ℤ) = J.card + wt J D := by
  rw [wt, Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := card_sdiff_add_card_inter J D
  rw [inter_comm] at h1
  push_cast
  linarith [(Nat.cast_add (R := ℤ) (J \ D).card (D ∩ J).card)]

theorem wt_add_of_disjoint (J : Finset E) {D D' : Finset E} (h : Disjoint D D') :
    wt J (D ∪ D') = wt J D + wt J D' := by
  unfold wt
  rw [union_sdiff_distrib, union_inter_distrib_right,
    card_union_of_disjoint (h.mono sdiff_subset sdiff_subset),
    card_union_of_disjoint (h.mono inter_subset_left inter_subset_left)]
  push_cast
  ring

theorem wt_of_subset {J D : Finset E} (h : D ⊆ J) : wt J D = -(D.card : ℤ) := by
  rw [wt, sdiff_eq_empty_iff_subset.mpr h, inter_eq_left.mpr h, card_empty]
  simp

theorem wt_of_disjoint {J D : Finset E} (h : Disjoint D J) : wt J D = D.card := by
  rw [wt, Finset.sdiff_eq_self_iff_disjoint.mpr h, disjoint_iff_inter_eq_empty.mp h, card_empty]
  simp

theorem symmDiff_symmDiff_cancel (J K : Finset E) : J ∆ (J ∆ K) = K := by
  rw [symmDiff_symmDiff_cancel_left]

/-- **The minimum-join criterion** (Cornuéjols Remark 2.6(i), in even-set form): a `T`-join
is minimum iff no even edge set has negative weight against it. -/
theorem isMinJoin_iff {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) :
    G.IsMinJoin T J ↔ ∀ C, G.IsEven C → 0 ≤ wt J C := by
  constructor
  · rintro ⟨-, hmin⟩ C hC
    have h := hmin _ ((G.isJoin_symmDiff_iff hJ C).mpr hC)
    have h2 := card_symmDiff_eq_add_wt J C
    have : (J.card : ℤ) ≤ ((J ∆ C).card : ℤ) := by exact_mod_cast h
    linarith
  · intro h
    refine ⟨hJ, fun K hK => ?_⟩
    have hC := G.isEven_symmDiff_of_isJoin hJ hK
    have h1 := h _ hC
    have h2 := card_symmDiff_eq_add_wt J (J ∆ K)
    rw [symmDiff_symmDiff_cancel] at h2
    have : (J.card : ℤ) ≤ K.card := by linarith
    exact_mod_cast this

/-- Remark 2.6(ii): exchanging a minimum join along a zero-weight even set keeps it
minimum. -/
theorem isMinJoin_symmDiff {T : Finset V} {J C : Finset E} (hJ : G.IsMinJoin T J)
    (hC : G.IsEven C) (h0 : wt J C = 0) : G.IsMinJoin T (J ∆ C) := by
  refine ⟨(G.isJoin_symmDiff_iff hJ.1 C).mpr hC, fun K hK => ?_⟩
  have h1 := hJ.2 K hK
  have h2 := card_symmDiff_eq_add_wt J C
  rw [h0, add_zero] at h2
  have h3 : (J ∆ C).card = J.card := by exact_mod_cast h2
  rw [h3]
  exact h1

/-- A minimum join contains no nonempty even set: it is a forest. -/
theorem eq_empty_of_isEven_of_subset {T : Finset V} {J C : Finset E} (hJ : G.IsMinJoin T J)
    (hC : G.IsEven C) (hsub : C ⊆ J) : C = ∅ := by
  have h := (G.isMinJoin_iff hJ.1).mp hJ _ hC
  rw [wt_of_subset hsub] at h
  have : C.card = 0 := by omega
  exact card_eq_zero.mp this

/-- Minimum joins exist as soon as joins do. -/
theorem exists_isMinJoin {T : Finset V} (h : ∃ J, G.IsJoin T J) : ∃ J, G.IsMinJoin T J := by
  obtain ⟨J₀, hJ₀⟩ := h
  obtain ⟨J, hJ, hmin⟩ := exists_min_image (univ.filter fun J => G.IsJoin T J) Finset.card
    ⟨J₀, mem_filter.mpr ⟨mem_univ _, hJ₀⟩⟩
  exact ⟨J, (mem_filter.mp hJ).2, fun K hK => hmin K (mem_filter.mpr ⟨mem_univ _, hK⟩)⟩

/-! ### The handshake lemma and cuts -/

theorem filter_mem_sym2 (a b : V) (S : Finset V) :
    (S.filter fun v : V => v ∈ s(a, b)) = ({a, b} : Finset V).filter (· ∈ S) := by
  ext v
  simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
  tauto

theorem card_filter_mem_ends (e : E) : (univ.filter fun v : V => v ∈ G.ends e).card = 2 := by
  have hl := G.loopless e
  revert hl
  refine Sym2.ind (fun a b hl => ?_) (G.ends e)
  rw [Sym2.mk_isDiag_iff] at hl
  rw [filter_mem_sym2, filter_true_of_mem (fun _ _ => mem_univ _), card_pair hl]

/-- The number of endpoints of `e` in `S`, as a sum of degrees. -/
theorem sum_deg_eq_sum_card (S : Finset V) (D : Finset E) :
    ∑ v ∈ S, G.deg D v = ∑ e ∈ D, (S.filter fun v : V => v ∈ G.ends e).card := by
  simp only [deg, inc, card_filter]
  exact sum_comm

/-- The handshake lemma. -/
theorem sum_deg (D : Finset E) : ∑ v, G.deg D v = 2 * D.card := by
  rw [sum_deg_eq_sum_card]
  rw [show (2 * D.card : ℕ) = ∑ e ∈ D, 2 by rw [sum_const, smul_eq_mul, mul_comm]]
  exact sum_congr rfl fun e _ => G.card_filter_mem_ends e

/-- The edges crossing the cut `(S, Sᶜ)`. -/
noncomputable def cut (S : Finset V) : Finset E :=
  univ.filter fun e => (∃ a ∈ G.ends e, a ∈ S) ∧ ∃ b ∈ G.ends e, b ∉ S

theorem mem_cut {S : Finset V} {e : E} :
    e ∈ G.cut S ↔ (∃ a ∈ G.ends e, a ∈ S) ∧ ∃ b ∈ G.ends e, b ∉ S := by
  simp [cut]

/-- The edges of `D` inside `S`. -/
noncomputable def inside (S : Finset V) (D : Finset E) : Finset E :=
  D.filter fun e => ∀ a ∈ G.ends e, a ∈ S

theorem mem_inside {S : Finset V} {D : Finset E} {e : E} :
    e ∈ G.inside S D ↔ e ∈ D ∧ ∀ a ∈ G.ends e, a ∈ S := by
  simp [inside]

/-- The number of endpoints of `e` in `S`: `2` inside, `1` across, `0` outside. -/
theorem card_filter_mem_ends_mem (S : Finset V) (e : E) :
    (S.filter fun v : V => v ∈ G.ends e).card =
      (if ∀ a ∈ G.ends e, a ∈ S then 2 else 0) + if e ∈ G.cut S then 1 else 0 := by
  have hl := G.loopless e
  have hc := G.mem_cut (S := S) (e := e)
  revert hl hc
  refine Sym2.ind (fun a b hl hc => ?_) (G.ends e)
  rw [Sym2.mk_isDiag_iff] at hl
  have hc' : e ∈ G.cut S ↔ (a ∈ S ∨ b ∈ S) ∧ (a ∉ S ∨ b ∉ S) := by
    rw [hc]
    simp only [Sym2.mem_iff]
    constructor
    · rintro ⟨⟨x, hx, hxS⟩, ⟨y, hy, hyS⟩⟩
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> tauto
    · rintro ⟨h1, h2⟩
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd h1 h2
      · exact ⟨⟨a, Or.inl rfl, h1⟩, ⟨b, Or.inr rfl, h2⟩⟩
      · exact ⟨⟨b, Or.inr rfl, h1⟩, ⟨a, Or.inl rfl, h2⟩⟩
      · exact absurd h1 h2
  have hall : (∀ x ∈ s(a, b), x ∈ S) ↔ a ∈ S ∧ b ∈ S := by
    simp only [Sym2.mem_iff]
    constructor
    · intro h; exact ⟨h a (Or.inl rfl), h b (Or.inr rfl)⟩
    · rintro ⟨h1, h2⟩ x hx; rcases hx with rfl | rfl <;> assumption
  rw [filter_mem_sym2, filter_insert, filter_singleton]
  simp only [hc', hall]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, hl]

/-- The handshake restricted to `S`: edges inside `S` are counted twice, crossing edges
once. -/
theorem sum_deg_eq (S : Finset V) (D : Finset E) :
    ∑ v ∈ S, G.deg D v = 2 * (G.inside S D).card + (D ∩ G.cut S).card := by
  rw [sum_deg_eq_sum_card, sum_congr rfl fun e _ => G.card_filter_mem_ends_mem S e,
    sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, sum_ite,
    sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one, filter_mem_eq_inter]
  simp only [inside]
  ring

/-- **A `T`-join meets every `T`-cut** (with odd intersection). -/
theorem odd_card_inter_cut {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) {S : Finset V}
    (hS : Odd (S ∩ T).card) : Odd (J ∩ G.cut S).card := by
  have h := G.sum_deg_eq S J
  have hpar : (∑ v ∈ S, G.deg J v) % 2 = (S ∩ T).card % 2 := by
    rw [sum_nat_mod, ← hJ]
    have : ∀ v ∈ S, G.deg J v % 2 = if v ∈ G.odd J then 1 else 0 := by
      intro v _
      by_cases hv : v ∈ G.odd J
      · rw [if_pos hv]; rw [mem_odd, Nat.odd_iff] at hv; exact hv
      · rw [if_neg hv]; rw [mem_odd, Nat.odd_iff] at hv; omega
    rw [sum_congr rfl this, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one,
      filter_mem_eq_inter]
  rw [Nat.odd_iff] at hS ⊢
  omega

theorem nonempty_inter_cut {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) {S : Finset V}
    (hS : Odd (S ∩ T).card) : (J ∩ G.cut S).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h
  have := G.odd_card_inter_cut hJ hS
  rw [h, card_empty] at this
  exact (Nat.not_even_iff_odd.mpr this) ⟨0, rfl⟩

/-! ### Bipartite colourings -/

/-- A two-colouring separating the ends of every edge. -/
def IsBipartite (col : V → Bool) : Prop := ∀ e a b, G.ends e = s(a, b) → col a ≠ col b

theorem card_filter_col (col : V → Bool) (hcol : G.IsBipartite col) (e : E) :
    ((univ.filter fun v : V => col v = true).filter fun v => v ∈ G.ends e).card = 1 := by
  have h := hcol e
  revert h
  refine Sym2.ind (fun a b h => ?_) (G.ends e)
  have hab := h a b rfl
  rw [filter_mem_sym2, filter_insert, filter_singleton]
  simp only [mem_filter, mem_univ, true_and]
  cases hca : col a <;> cases hcb : col b
  · exact absurd (hca.trans hcb.symm) hab
  · simp
  · simp
  · exact absurd (hca.trans hcb.symm) hab

/-- In a bipartite graph the size of an edge set is the sum of the degrees on one side. -/
theorem card_eq_sum_deg_col (col : V → Bool) (hcol : G.IsBipartite col) (D : Finset E) :
    D.card = ∑ v ∈ univ.filter (fun v => col v = true), G.deg D v := by
  rw [sum_deg_eq_sum_card, sum_congr rfl fun e _ => G.card_filter_col col hcol e, sum_const,
    smul_eq_mul, mul_one]

/-- In a bipartite graph every even edge set has even size. -/
theorem even_card_of_isEven {col : V → Bool} (hcol : G.IsBipartite col) {D : Finset E}
    (hD : G.IsEven D) : Even D.card := by
  rw [G.card_eq_sum_deg_col col hcol, Nat.even_iff, sum_nat_mod,
    sum_eq_zero fun v _ => Nat.even_iff.mp (hD v)]
  rfl

/-- In a bipartite graph the weight of an even set against any edge set is even. -/
theorem even_wt_of_isEven {col : V → Bool} (hcol : G.IsBipartite col) (J : Finset E)
    {D : Finset E} (hD : G.IsEven D) : Even (wt J D) := by
  have h := G.even_card_of_isEven hcol hD
  have h1 := card_sdiff_add_card_inter D J
  rw [wt]
  obtain ⟨k, hk⟩ := h
  refine ⟨((D \ J).card : ℤ) - k, ?_⟩
  have : ((D \ J).card : ℤ) + (D ∩ J).card = k + k := by exact_mod_cast (h1.trans hk)
  linarith

end MGraph

end TSPGap

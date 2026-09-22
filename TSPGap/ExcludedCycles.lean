/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Polygon

/-!
# `k`-cycles of near-minimum cuts are long (BG08 Lemma 22 = KKO22 Lemma 4.19)

A `k`-cycle of `η`-near minimum cuts of a subtour-LP point has `k ≥ 2/η`.

The proof is edge counting.  For `k ≥ 4`,

`x(δ(⋃ᵢ Cᵢ)) + ∑ᵢ x(δ(Cᵢ ∩ Cᵢ₊₁)) ≤ ∑ᵢ x(δ(Cᵢ))`

holds edge by edge: a vertex lies in at most two of the `Cᵢ`, and then only in
two consecutive ones (`isShort_idxOf`, from the disjointness of non-consecutive
members), so for an edge `s(a, b)` the three counts are functions of the index
sets `A = {i : a ∈ Cᵢ}` and `B = {i : b ∈ Cᵢ}` — cyclic intervals of length at
most two — and the inequality is the cardinality statement `core_ineq`.  Each of
the `k + 1` sets on the left is a nonempty proper subset (consecutive members
cross, the union is not everything), so the LP gives `2(k + 1) ≤ k(2 + η)`.

For `k = 3` the same edge count gives three-way submodularity
(`three_way_submodular`), and the four sets `Cᵢ ∩ Cᵢ₊₁ ∖ Cᵢ₊₂`, `⋃ Cᵢ` are
nonempty and proper by the 3-cycle clause, so `3(2 + η) ≥ 8`.

`kCycle_two_div_le` was a declared box in `BlackBoxes.lean` until 2026-09-06; it is
now proved here, and `InsideAtoms.lean` / `NearCycle.lean` import this file for it.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Cyclic index arithmetic -/

theorem add_mod_ne_self {k i t : ℕ} (hi : i < k) (ht0 : 0 < t) (htk : t < k) :
    (i + t) % k ≠ i := by
  intro h
  rcases lt_or_ge (i + t) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h; omega

theorem add_mod_ne_add_mod {k i s t : ℕ} (hst : s < t) (htk : t < k) :
    (i + t) % k ≠ (i + s) % k := by
  intro h
  have hj : (i + s) % k < k := Nat.mod_lt _ (by omega)
  have : ((i + s) % k + (t - s)) % k = (i + s) % k := by
    rw [Nat.mod_add_mod, show i + s + (t - s) = i + t by omega, h]
  exact add_mod_ne_self hj (by omega) (by omega) this

theorem succ_mod_lt {k : ℕ} (hk : 0 < k) (i : ℕ) : (i + 1) % k < k := Nat.mod_lt _ hk

theorem pred_mod_lt {k : ℕ} (hk : 0 < k) (i : ℕ) : (i + k - 1) % k < k := Nat.mod_lt _ hk

theorem pred_succ_mod {k i : ℕ} (hi : i < k) : ((i + k - 1) % k + 1) % k = i := by
  rw [Nat.mod_add_mod, show i + k - 1 + 1 = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

theorem succ_pred_mod {k i : ℕ} (hi : i < k) : ((i + 1) % k + k - 1) % k = i := by
  rw [show (i + 1) % k + k - 1 = (i + 1) % k + (k - 1) by omega, Nat.mod_add_mod,
    show i + 1 + (k - 1) = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

theorem succ_succ_mod (k i : ℕ) : ((i + 1) % k + 1) % k = (i + 2) % k := by
  rw [Nat.mod_add_mod]

theorem succ_mod_injective {k i j : ℕ} (hi : i < k) (hj : j < k)
    (h : (i + 1) % k = (j + 1) % k) : i = j := by
  have h1 := succ_pred_mod hi
  have h2 := succ_pred_mod hj
  rw [h] at h1
  omega

/-- The adjacency a `k`-cycle's disjointness clause leaves open. -/
theorem IsKCycle.adj_of_mem_both {k : ℕ} {C : ℕ → Finset (Fin n)} (hcyc : IsKCycle k C)
    {i j : ℕ} (hi : i < k) (hj : j < k) {v : Fin n} (hvi : v ∈ C i) (hvj : v ∈ C j) :
    j = i ∨ j = (i + 1) % k ∨ j = (i + k - 1) % k := by
  by_contra hcon
  push Not at hcon
  exact Finset.disjoint_left.mp (hcyc.disjoint_far i hi j hj hcon.2.2 hcon.1 hcon.2.1) hvi hvj

/-! ### The index sets of a vertex -/

/-- The indices `i < k` whose set contains `v`. -/
def idxOf (k : ℕ) (C : ℕ → Finset (Fin n)) (v : Fin n) : Finset ℕ :=
  (range k).filter fun i => v ∈ C i

theorem mem_idxOf {k : ℕ} {C : ℕ → Finset (Fin n)} {v : Fin n} {i : ℕ} :
    i ∈ idxOf k C v ↔ i < k ∧ v ∈ C i := by
  simp [idxOf]

/-- The indices `i < k` with `i` and `(i + 1) % k` both in `X`. -/
def pairsOf (k : ℕ) (X : Finset ℕ) : Finset ℕ :=
  (range k).filter fun i => i ∈ X ∧ (i + 1) % k ∈ X

theorem mem_pairsOf {k : ℕ} {X : Finset ℕ} {i : ℕ} :
    i ∈ pairsOf k X ↔ i < k ∧ i ∈ X ∧ (i + 1) % k ∈ X := by
  simp [pairsOf]

theorem pairsOf_inter (k : ℕ) (X Y : Finset ℕ) :
    pairsOf k (X ∩ Y) = pairsOf k X ∩ pairsOf k Y := by
  ext i
  simp only [mem_pairsOf, Finset.mem_inter]
  tauto

/-- A cyclic interval of length at most two. -/
def IsShort (k : ℕ) (X : Finset ℕ) : Prop :=
  X = ∅ ∨ (∃ p < k, X = {p}) ∨ (∃ p < k, X = {p, (p + 1) % k})

/-- In a `k`-cycle with `k ≥ 4`, every vertex lies in at most two members, and then in
two consecutive ones. -/
theorem IsKCycle.isShort_idxOf {k : ℕ} {C : ℕ → Finset (Fin n)} (hk : 4 ≤ k)
    (hcyc : IsKCycle k C) (v : Fin n) : IsShort k (idxOf k C v) := by
  classical
  have hk0 : 0 < k := by omega
  by_cases hne : (idxOf k C v).Nonempty
  · obtain ⟨p, hp⟩ := hne
    obtain ⟨hpk, hvp⟩ := mem_idxOf.mp hp
    have hadj : ∀ q ∈ idxOf k C v, q = p ∨ q = (p + 1) % k ∨ q = (p + k - 1) % k := by
      intro q hq
      obtain ⟨hqk, hvq⟩ := mem_idxOf.mp hq
      exact hcyc.adj_of_mem_both hpk hqk hvp hvq
    by_cases hsucc : (p + 1) % k ∈ idxOf k C v
    · by_cases hpred : (p + k - 1) % k ∈ idxOf k C v
      · -- both neighbours: they are non-consecutive, so disjoint
        exfalso
        have hsp := succ_pred_mod hpk
        have hps := pred_succ_mod hpk
        have hne1 : (p + k - 1) % k ≠ ((p + 1) % k + k - 1) % k := by
          rw [hsp]; intro h
          have := pred_succ_mod hpk; rw [h] at this
          exact add_mod_ne_self hpk one_pos (by omega) this
        have hne2 : (p + k - 1) % k ≠ (p + 1) % k := by
          intro h
          have := pred_succ_mod hpk
          rw [h, succ_succ_mod] at this
          exact add_mod_ne_self hpk (by norm_num) (by omega) this
        have hne3 : (p + k - 1) % k ≠ ((p + 1) % k + 1) % k := by
          intro h
          have := pred_succ_mod hpk
          rw [h, succ_succ_mod, Nat.mod_add_mod] at this
          simp only [Nat.add_assoc, Nat.reduceAdd] at this
          exact add_mod_ne_self hpk (by norm_num) (by omega) this
        have hd := hcyc.disjoint_far _ (succ_mod_lt hk0 p) _ (pred_mod_lt hk0 p) hne1 hne2 hne3
        exact Finset.disjoint_left.mp hd (mem_idxOf.mp hsucc).2 (mem_idxOf.mp hpred).2
      · right; right
        refine ⟨p, hpk, ?_⟩
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hq
          rcases hadj q hq with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (h ▸ hq) hpred
        · rintro (rfl | rfl)
          · exact hp
          · exact hsucc
    · by_cases hpred : (p + k - 1) % k ∈ idxOf k C v
      · right; right
        refine ⟨(p + k - 1) % k, pred_mod_lt hk0 p, ?_⟩
        rw [pred_succ_mod hpk]
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hq
          rcases hadj q hq with h | h | h
          · exact Or.inr h
          · exact absurd (h ▸ hq) hsucc
          · exact Or.inl h
        · rintro (rfl | rfl)
          · exact hpred
          · exact hp
      · right; left
        refine ⟨p, hpk, ?_⟩
        ext q
        simp only [Finset.mem_singleton]
        constructor
        · intro hq
          rcases hadj q hq with h | h | h
          · exact h
          · exact absurd (h ▸ hq) hsucc
          · exact absurd (h ▸ hq) hpred
        · rintro rfl; exact hp
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hne

/-! ### The cardinality core -/

theorem card_pairsOf_le {k : ℕ} (hk : 3 ≤ k) {X : Finset ℕ} (hX : IsShort k X) :
    (pairsOf k X).card + (if X.Nonempty then 1 else 0) ≤ X.card := by
  classical
  have hk0 : 0 < k := by omega
  rcases hX with rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · simp [pairsOf]
  · have hempty : pairsOf k {p} = ∅ := by
      ext i
      simp only [mem_pairsOf, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨-, rfl, h⟩
      exact add_mod_ne_self hp one_pos (by omega) h
    simp [hempty]
  · have hsub : pairsOf k {p, (p + 1) % k} ⊆ {p} := by
      intro i hi
      obtain ⟨hik, hi1, hi2⟩ := mem_pairsOf.mp hi
      rw [Finset.mem_singleton]
      rcases Finset.mem_insert.mp hi1 with rfl | hi1
      · rfl
      · rw [Finset.mem_singleton] at hi1
        subst hi1
        exfalso
        rw [succ_succ_mod] at hi2
        rcases Finset.mem_insert.mp hi2 with h | h
        · exact add_mod_ne_self hp (by norm_num) (by omega) h
        · rw [Finset.mem_singleton] at h
          exact add_mod_ne_add_mod (by norm_num) (by omega) h
    have h1 : (pairsOf k {p, (p + 1) % k}).card ≤ 1 :=
      (Finset.card_le_card hsub).trans (by simp)
    have h2 : ({p, (p + 1) % k} : Finset ℕ).card = 2 := by
      rw [Finset.card_pair]
      exact (add_mod_ne_self hp one_pos (by omega)).symm
    rw [h2, if_pos ⟨p, Finset.mem_insert_self _ _⟩]
    omega

theorem card_le_pairsOf {k p : ℕ} (hp : p < k) {X : Finset ℕ} (hX : X ⊆ {p, (p + 1) % k}) :
    X.card ≤ (pairsOf k X).card + (if X.Nonempty then 1 else 0) := by
  classical
  by_cases hboth : p ∈ X ∧ (p + 1) % k ∈ X
  · have hpair : p ∈ pairsOf k X := mem_pairsOf.mpr ⟨hp, hboth.1, hboth.2⟩
    have h1 : 1 ≤ (pairsOf k X).card := Finset.card_pos.mpr ⟨p, hpair⟩
    have h2 : X.card ≤ 2 := (Finset.card_le_card hX).trans (Finset.card_le_two)
    rw [if_pos ⟨p, hboth.1⟩]
    omega
  · have h1 : X.card ≤ 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcon
      have ha' := hX ha
      have hb' := hX hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact hab rfl
      · exact hboth ⟨ha, hb⟩
      · exact hboth ⟨hb, ha⟩
      · exact hab rfl
    by_cases hne : X.Nonempty
    · rw [if_pos hne]; omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

theorem card_symmDiff_add (X Y : Finset ℕ) :
    ((X \ Y) ∪ (Y \ X)).card + 2 * (X ∩ Y).card = X.card + Y.card := by
  have hd : Disjoint (X \ Y) (Y \ X) := disjoint_sdiff_sdiff
  rw [Finset.card_union_of_disjoint hd]
  have h1 := Finset.card_sdiff_add_card_inter X Y
  have h2 := Finset.card_sdiff_add_card_inter Y X
  rw [Finset.inter_comm] at h2
  omega

/-- **The cardinality core.**  For cyclic intervals `A, B` of length at most two,
`[A ≠ ∅ xor B ≠ ∅] + |pairs A △ pairs B| ≤ |A △ B|`. -/
theorem core_ineq {k : ℕ} (hk : 3 ≤ k) {A B : Finset ℕ} (hA : IsShort k A) (hB : IsShort k B) :
    (if (A.Nonempty ↔ B.Nonempty) then 0 else 1)
      + ((pairsOf k A \ pairsOf k B) ∪ (pairsOf k B \ pairsOf k A)).card
      ≤ ((A \ B) ∪ (B \ A)).card := by
  classical
  have hcA := card_pairsOf_le hk hA
  have hcB := card_pairsOf_le hk hB
  have hAB : A ∩ B ⊆ {0, (0 + 1) % k} ∨ ∃ p < k, A ∩ B ⊆ {p, (p + 1) % k} := by
    rcases hA with rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · left; simp
    · right; exact ⟨p, hp, Finset.inter_subset_left.trans
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))⟩
    · right; exact ⟨p, hp, Finset.inter_subset_left⟩
  have hI : (A ∩ B).card ≤ (pairsOf k (A ∩ B)).card + (if (A ∩ B).Nonempty then 1 else 0) := by
    rcases hAB with h | ⟨p, hp, h⟩
    · exact card_le_pairsOf (by omega) h
    · exact card_le_pairsOf hp h
  rw [pairsOf_inter] at hI
  have hs1 := card_symmDiff_add A B
  have hs2 := card_symmDiff_add (pairsOf k A) (pairsOf k B)
  have hIne : (A ∩ B).Nonempty → A.Nonempty ∧ B.Nonempty := fun ⟨a, ha⟩ =>
    ⟨⟨a, (Finset.mem_inter.mp ha).1⟩, ⟨a, (Finset.mem_inter.mp ha).2⟩⟩
  by_cases hAn : A.Nonempty <;> by_cases hBn : B.Nonempty
  · rw [if_pos (iff_of_true hAn hBn)]
    rw [if_pos hAn] at hcA
    rw [if_pos hBn] at hcB
    by_cases hIn : (A ∩ B).Nonempty
    · rw [if_pos hIn] at hI; omega
    · rw [if_neg hIn] at hI; omega
  · rw [if_neg (fun h => hBn (h.mp hAn))]
    rw [if_pos hAn] at hcA
    rw [if_neg hBn] at hcB
    rw [if_neg (fun h => hBn (hIne h).2)] at hI
    omega
  · rw [if_neg (fun h => hAn (h.mpr hBn))]
    rw [if_neg hAn] at hcA
    rw [if_pos hBn] at hcB
    rw [if_neg (fun h => hAn (hIne h).1)] at hI
    omega
  · rw [if_pos (iff_of_false hAn hBn)]
    rw [if_neg hAn] at hcA
    rw [if_neg hBn] at hcB
    rw [if_neg (fun h => hAn (hIne h).1)] at hI
    omega

/-! ### Cut sums as sums over all edges -/

theorem cutEdges_subset_edgeFinset_of_cut (S : Finset (Fin n)) : cutEdges S ⊆ edgeFinset n := by
  intro e he
  rw [cutEdges, Finset.mem_filter] at he
  obtain ⟨-, u, hu, v, hv, rfl⟩ := he
  rw [edgeFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.mk_isDiag_iff]
  intro h
  exact (Finset.mem_compl.mp hv) (h ▸ hu)

theorem mk_mem_cutEdges_iff' {S : Finset (Fin n)} {a b : Fin n} :
    s(a, b) ∈ cutEdges S ↔ (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S) := by
  rw [cutEdges, Finset.mem_filter]
  constructor
  · rintro ⟨-, u, hu, v, hv, h⟩
    rw [Finset.mem_compl] at hv
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨Finset.mem_univ _, a, ha, b, Finset.mem_compl.mpr hb, rfl⟩
    · exact ⟨Finset.mem_univ _, b, hb, a, Finset.mem_compl.mpr ha, Sym2.eq_swap⟩

/-- The cut indicator of an edge at a set. -/
def cutInd (S : Finset (Fin n)) (e : Sym2 (Fin n)) : ℕ := if e ∈ cutEdges S then 1 else 0

theorem cutSum_eq_sum_cutInd (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    cutSum x S = ∑ e ∈ edgeFinset n, x e * (cutInd S e : ℝ) := by
  classical
  unfold cutSum cutInd
  have : cutEdges S = (edgeFinset n).filter (fun e => e ∈ cutEdges S) := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (cutEdges_subset_edgeFinset_of_cut S)]
  conv_lhs => rw [this]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem cutInd_mk {S : Finset (Fin n)} {a b : Fin n} :
    cutInd S s(a, b) = if ((a ∈ S) ↔ (b ∈ S)) then 0 else 1 := by
  unfold cutInd
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [mk_mem_cutEdges_iff', ha, hb]

/-! ### The general inequality, `k ≥ 4` -/

/-- Per edge: the three counts, in terms of the index sets of the endpoints. -/
theorem edge_count_le {k : ℕ} {C : ℕ → Finset (Fin n)} (hk : 4 ≤ k) (hcyc : IsKCycle k C)
    (a b : Fin n) :
    cutInd ((range k).biUnion C) s(a, b)
        + ∑ i ∈ range k, cutInd (C i ∩ C ((i + 1) % k)) s(a, b)
      ≤ ∑ i ∈ range k, cutInd (C i) s(a, b) := by
  classical
  have hk0 : 0 < k := by omega
  set A := idxOf k C a with hA
  set B := idxOf k C b with hB
  have hAs := hcyc.isShort_idxOf hk a
  have hBs := hcyc.isShort_idxOf hk b
  -- the three counts
  have h1 : ∑ i ∈ range k, cutInd (C i) s(a, b) = ((A \ B) ∪ (B \ A)).card := by
    unfold cutInd
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, mk_mem_cutEdges_iff', Finset.mem_union,
      Finset.mem_sdiff, hA, hB, mem_idxOf]
    tauto
  have h2 : ∑ i ∈ range k, cutInd (C i ∩ C ((i + 1) % k)) s(a, b)
      = ((pairsOf k A \ pairsOf k B) ∪ (pairsOf k B \ pairsOf k A)).card := by
    unfold cutInd
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, mk_mem_cutEdges_iff', Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_inter, mem_pairsOf, hA, hB, mem_idxOf]
    have := succ_mod_lt hk0 i
    tauto
  have h3 : cutInd ((range k).biUnion C) s(a, b) = if (A.Nonempty ↔ B.Nonempty) then 0 else 1 := by
    rw [cutInd_mk]
    have ha : a ∈ (range k).biUnion C ↔ A.Nonempty := by
      simp only [Finset.mem_biUnion, Finset.mem_range, hA, Finset.Nonempty, mem_idxOf]
    have hb : b ∈ (range k).biUnion C ↔ B.Nonempty := by
      simp only [Finset.mem_biUnion, Finset.mem_range, hB, Finset.Nonempty, mem_idxOf]
    by_cases hAn : A.Nonempty <;> by_cases hBn : B.Nonempty
    · rw [if_pos (iff_of_true (ha.mpr hAn) (hb.mpr hBn)), if_pos (iff_of_true hAn hBn)]
    · rw [if_neg (fun h => hBn (hb.mp (h.mp (ha.mpr hAn)))), if_neg (fun h => hBn (h.mp hAn))]
    · rw [if_neg (fun h => hAn (ha.mp (h.mpr (hb.mpr hBn)))), if_neg (fun h => hAn (h.mpr hBn))]
    · rw [if_pos (iff_of_false (fun h => hAn (ha.mp h)) (fun h => hBn (hb.mp h))),
        if_pos (iff_of_false hAn hBn)]
  rw [h1, h2, h3]
  exact core_ineq (by omega) hAs hBs

/-- **The `k`-cycle inequality**, `k ≥ 4`:
`x(δ(⋃ Cᵢ)) + ∑ x(δ(Cᵢ ∩ Cᵢ₊₁)) ≤ ∑ x(δ(Cᵢ))`. -/
theorem cutSum_union_add_sum_inter_le (hx : ∀ e, 0 ≤ x e) {k : ℕ} {C : ℕ → Finset (Fin n)}
    (hk : 4 ≤ k) (hcyc : IsKCycle k C) :
    cutSum x ((range k).biUnion C) + ∑ i ∈ range k, cutSum x (C i ∩ C ((i + 1) % k))
      ≤ ∑ i ∈ range k, cutSum x (C i) := by
  classical
  simp only [cutSum_eq_sum_cutInd]
  rw [Finset.sum_comm (s := range k), Finset.sum_comm (s := range k), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hx e)
  induction e using Sym2.ind with
  | h a b =>
    have := edge_count_le hk hcyc a b
    exact_mod_cast this

/-! ### Three-way submodularity, `k = 3` -/

/-- Per edge: `[δA] + [δB] + [δC] ≥ [δ(A∩B∖C)] + [δ(B∩C∖A)] + [δ(C∩A∖B)] + [δ(A∪B∪C)]`. -/
theorem edge_count_three (A B C : Finset (Fin n)) (a b : Fin n) :
    cutInd ((A ∩ B) \ C) s(a, b) + cutInd ((B ∩ C) \ A) s(a, b) + cutInd ((C ∩ A) \ B) s(a, b)
        + cutInd (A ∪ B ∪ C) s(a, b)
      ≤ cutInd A s(a, b) + cutInd B s(a, b) + cutInd C s(a, b) := by
  simp only [cutInd_mk, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
  by_cases h1 : a ∈ A <;> by_cases h2 : a ∈ B <;> by_cases h3 : a ∈ C <;>
    by_cases h4 : b ∈ A <;> by_cases h5 : b ∈ B <;> by_cases h6 : b ∈ C <;>
    simp [h1, h2, h3, h4, h5, h6]

/-- **Three-way submodularity** of the cut function. -/
theorem three_way_submodular (hx : ∀ e, 0 ≤ x e) (A B C : Finset (Fin n)) :
    cutSum x ((A ∩ B) \ C) + cutSum x ((B ∩ C) \ A) + cutSum x ((C ∩ A) \ B) + cutSum x (A ∪ B ∪ C)
      ≤ cutSum x A + cutSum x B + cutSum x C := by
  classical
  simp only [cutSum_eq_sum_cutInd]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [← mul_add, ← mul_add, ← mul_add, ← mul_add, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hx e)
  induction e using Sym2.ind with
  | h a b => exact_mod_cast edge_count_three A B C a b

/-! ### The bound -/

/-- **BG08 Lemma 22 = KKO22 Lemma 4.19, proved.**  A `k`-cycle of `η`-near minimum
cuts of a subtour-LP point has `k ≥ 2/η`. -/
theorem kCycle_two_div_le (hx : x ∈ subtourLP n) {η : ℝ} (hη0 : 0 < η) {k : ℕ}
    {C : ℕ → Finset (Fin n)} (hcyc : IsKCycle k C) (hnmc : ∀ i < k, IsNearMinCut x η (C i)) :
    2 / η ≤ (k : ℝ) := by
  classical
  have hx0 : ∀ e, 0 ≤ x e := hx.1
  have hk3 := hcyc.three_le
  have hne : ∀ i < k, (C i).Nonempty := fun i hi => (hnmc i hi).nonempty
  have hnu : ∀ i < k, C i ≠ Finset.univ := fun i hi => (hnmc i hi).ne_univ
  have hU2 : 2 ≤ cutSum x ((range k).biUnion C) := by
    refine two_le_cutSum hx ?_ hcyc.union_ne
    obtain ⟨v, hv⟩ := hne 0 (by omega)
    exact ⟨v, Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by omega), hv⟩⟩
  have hsum_le : ∑ i ∈ range k, cutSum x (C i) ≤ k * (2 + η) := by
    calc ∑ i ∈ range k, cutSum x (C i) ≤ ∑ i ∈ range k, (2 + η) :=
          Finset.sum_le_sum fun i hi => (hnmc i (Finset.mem_range.mp hi)).cut_le
      _ = k * (2 + η) := by simp [mul_add]
  rw [div_le_iff₀ hη0]
  rcases Nat.lt_or_ge k 4 with hk | hk
  · -- `k = 3`: three-way submodularity
    have hk3' : k = 3 := by omega
    subst hk3'
    have hcond := hcyc.three_cond rfl
    have hI : ∀ i < 3, 2 ≤ cutSum x ((C i ∩ C ((i + 1) % 3)) \ C ((i + 3 - 1) % 3)) := by
      intro i hi
      refine two_le_cutSum hx ?_ ?_
      · exact Finset.nonempty_iff_ne_empty.mpr fun h =>
          hcond i hi (Finset.sdiff_eq_empty_iff_subset.mp h)
      · intro h
        exact hnu i hi (Finset.univ_subset_iff.mp
          (h ▸ (Finset.sdiff_subset.trans Finset.inter_subset_left)))
    have h0 := hI 0 (by norm_num)
    have h1 := hI 1 (by norm_num)
    have h2 := hI 2 (by norm_num)
    norm_num at h0 h1 h2
    have hsub := three_way_submodular hx0 (C 0) (C 1) (C 2)
    have hU : (range 3).biUnion C = C 0 ∪ C 1 ∪ C 2 := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
      constructor
      · rintro ⟨i, hi, hv⟩
        interval_cases i
        · exact Or.inl (Or.inl hv)
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
      · rintro ((hv | hv) | hv)
        · exact ⟨0, by norm_num, hv⟩
        · exact ⟨1, by norm_num, hv⟩
        · exact ⟨2, by norm_num, hv⟩
    rw [hU] at hU2
    have hsum3 : ∑ i ∈ range 3, cutSum x (C i) = cutSum x (C 0) + cutSum x (C 1) + cutSum x (C 2) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [hsum3] at hsum_le
    push_cast at hsum_le ⊢
    linarith
  · -- `k ≥ 4`: the cycle inequality
    have hI : ∀ i < k, 2 ≤ cutSum x (C i ∩ C ((i + 1) % k)) := by
      intro i hi
      refine two_le_cutSum hx (hcyc.cross_succ i hi).1 ?_
      intro h
      exact hnu i hi (Finset.univ_subset_iff.mp (h ▸ Finset.inter_subset_left))
    have hsumI : (k : ℝ) * 2 ≤ ∑ i ∈ range k, cutSum x (C i ∩ C ((i + 1) % k)) := by
      calc (k : ℝ) * 2 = ∑ i ∈ range k, (2 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hI i (Finset.mem_range.mp hi)
    have := cutSum_union_add_sum_inter_le hx0 hk hcyc
    linarith
end TSPGap

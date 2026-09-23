/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic

/-!
# Uncrossing near-minimum cuts (KKO21 §2.3)

Phase 1 of the roadmap: the submodularity/uncrossing toolkit for
near-minimum cuts of an LP solution `x`.

* `pairSum x S T` — for disjoint `S`, `T` this is `x(E(S,T))`, the total
  `x`-weight of edges with one endpoint in `S` and one in `T` (each edge
  counted once, via the double sum `∑_{u ∈ S} ∑_{v ∈ T} x s(u,v)`).
* `cutSum_eq_pairSum` — `x(δ(S)) = x(E(S, Sᶜ))`, the bridge between the
  edge-set definition of `cutSum` and the double-sum calculus.
* Three *exact identities* from which all of §2.3 follows by algebra:
  - `cutSum_add_cutSum_of_disjoint`:
    `x(δ(S)) + x(δ(T)) = 2·x(E(S,T)) + x(δ(S ∪ T))` for disjoint `S`, `T`;
  - `cutSum_submodular_identity`:
    `x(δ(A∩B)) + x(δ(A∪B)) + 2·x(E(A∖B, B∖A)) = x(δ(A)) + x(δ(B))`;
  - `cutSum_posimodular_identity`:
    `x(δ(A∖B)) + x(δ(B∖A)) + 2·x(E(A∩B, (A∪B)ᶜ)) = x(δ(A)) + x(δ(B))`.
* `IsNearMinCut x ε S` — proper nonempty `S` with `x(δ(S)) ≤ 2 + ε`;
  `Crossing A B` — all four corners `A∩B, A∖B, B∖A, (A∪B)ᶜ` nonempty.
* **KKO21 Lemma 2.5** ([OSS11]) — `nearMinCut_inter`, `nearMinCut_union`,
  `nearMinCut_sdiff`: the corners of two crossing near-min cuts are
  near-min cuts, with the errors adding.
* **KKO21 Lemma 2.6** ([Ben97, Lem 5.3.5]) — `one_sub_half_le_pairSum_*`:
  each of the four "side" quantities between adjacent corners is at least
  `1 - ε/2`.  We record the sharp attribution: the side lies on the
  boundary of one of the two cuts, and only that cut's `ε` enters.
* **KKO21 Lemma 2.7** — for nested near-min cuts `A ⊊ B`:
  `pairSum_le_of_subset` (`x(E(A, Bᶜ)) ≤ 1 + (ε_A+ε_B)/2`) and
  `le_pairSum_of_subset` (`x(E(A, B∖A)) ≥ 1 - ε_B/2`).

Everything reduces to the disjoint-union identity: for disjoint `S`, `T`,
`x(δ(S)) + x(δ(T)) - x(δ(S ∪ T))` counts the edges between `S` and `T`
exactly twice.
-/

namespace TSPGap

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {A B S T U : Finset (Fin n)}
  {εA εB : ℝ}

/-! ### The pair-sum calculus -/

/-- The double sum `∑_{u ∈ S} ∑_{v ∈ T} x s(u,v)`.  For **disjoint** `S`
and `T` this equals `x(E(S,T))`, each edge counted exactly once. -/
def pairSum (x : Sym2 (Fin n) → ℝ) (S T : Finset (Fin n)) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, x s(u, v)

theorem pairSum_nonneg (hx : ∀ e, 0 ≤ x e) (S T : Finset (Fin n)) :
    0 ≤ pairSum x S T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hx _

/-- A superset of a set equal to `univ` is `univ`. -/
theorem eq_univ_of_subset_of_eq_univ {S T : Finset (Fin n)} (hST : S ⊆ T)
    (h : S = Finset.univ) : T = Finset.univ :=
  Finset.univ_subset_iff.mp (h ▸ hST)

theorem pairSum_comm (x : Sym2 (Fin n) → ℝ) (S T : Finset (Fin n)) :
    pairSum x S T = pairSum x T S := by
  unfold pairSum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
    rw [Sym2.eq_swap]

theorem pairSum_union_right (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n))
    (h : Disjoint T U) :
    pairSum x S (T ∪ U) = pairSum x S T + pairSum x S U := by
  unfold pairSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_union h

theorem pairSum_union_left (x : Sym2 (Fin n) → ℝ) (U : Finset (Fin n))
    (h : Disjoint S T) :
    pairSum x (S ∪ T) U = pairSum x S U + pairSum x T U := by
  unfold pairSum
  rw [Finset.sum_union h]

/-- The edges with one endpoint in `A` and one in `B` (for disjoint `A`,
`B` this is `E(A,B)`). -/
def betweenEdges (A B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ∃ u ∈ A, ∃ v ∈ B, e = s(u, v)

theorem cutEdges_eq_betweenEdges (S : Finset (Fin n)) :
    cutEdges S = betweenEdges S Sᶜ := rfl

/-- For disjoint `A`, `B`, summing `x` over `E(A,B)` gives the pair
sum: each edge is counted exactly once. -/
theorem sum_betweenEdges (x : Sym2 (Fin n) → ℝ) (h : Disjoint A B) :
    ∑ e ∈ betweenEdges A B, x e = pairSum x A B := by
  unfold betweenEdges pairSum
  rw [← Finset.sum_product']
  refine (Finset.sum_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_ ?_).symm
  · -- maps into the between edges
    intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, p.1, hp.1, p.2, hp.2, rfl⟩
  · -- injective
    intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd hq.2 (Finset.disjoint_left.mp h (h1 ▸ hp.1))
  · -- surjective
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨-, u, huA, v, hvB, he⟩ := he
    exact ⟨(u, v), Finset.mem_product.mpr ⟨huA, hvB⟩, he.symm⟩
  · intro p hp
    rfl

/-- The bridge: `x(δ(S))` is the pair sum over `S × Sᶜ`. -/
theorem cutSum_eq_pairSum (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    cutSum x S = pairSum x S Sᶜ := by
  unfold cutSum
  rw [cutEdges_eq_betweenEdges]
  exact sum_betweenEdges x disjoint_compl_right

theorem cutSum_compl (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    cutSum x Sᶜ = cutSum x S := by
  rw [cutSum_eq_pairSum, cutSum_eq_pairSum, compl_compl, pairSum_comm]

/-! ### The three exact identities -/

/-- **Disjoint-union identity**: for disjoint `S`, `T`,
`x(δ(S)) + x(δ(T)) = 2·x(E(S,T)) + x(δ(S ∪ T))`. -/
theorem cutSum_add_cutSum_of_disjoint (x : Sym2 (Fin n) → ℝ)
    (h : Disjoint S T) :
    cutSum x S + cutSum x T = 2 * pairSum x S T + cutSum x (S ∪ T) := by
  have hd := Finset.disjoint_left.mp h
  have hS : Sᶜ = T ∪ (S ∪ T)ᶜ := by
    ext v
    have hdv : v ∈ S → v ∈ T → False := fun h1 h2 => hd h1 h2
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hT : Tᶜ = S ∪ (S ∪ T)ᶜ := by
    ext v
    have hdv : v ∈ S → v ∈ T → False := fun h1 h2 => hd h1 h2
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hdTU : Disjoint T (S ∪ T)ᶜ :=
    Finset.disjoint_left.mpr fun v hvT hvC =>
      (Finset.mem_compl.mp hvC) (Finset.mem_union_right _ hvT)
  have hdSU : Disjoint S (S ∪ T)ᶜ :=
    Finset.disjoint_left.mpr fun v hvS hvC =>
      (Finset.mem_compl.mp hvC) (Finset.mem_union_left _ hvS)
  rw [cutSum_eq_pairSum, cutSum_eq_pairSum, cutSum_eq_pairSum,
    hS, hT, pairSum_union_right x S hdTU, pairSum_union_right x T hdSU,
    pairSum_union_left x _ h, pairSum_comm x T S]
  ring

/-- **Submodularity as an identity**:
`x(δ(A∩B)) + x(δ(A∪B)) + 2·x(E(A∖B, B∖A)) = x(δ(A)) + x(δ(B))`. -/
theorem cutSum_submodular_identity (x : Sym2 (Fin n) → ℝ)
    (A B : Finset (Fin n)) :
    cutSum x (A ∩ B) + cutSum x (A ∪ B) + 2 * pairSum x (A \ B) (B \ A)
      = cutSum x A + cutSum x B := by
  have h1 : Disjoint (A ∩ B) (A \ B) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_sdiff.mp hv2).2 (Finset.mem_inter.mp hv1).2
  have h2 : Disjoint (A ∩ B) (B \ A) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_sdiff.mp hv2).2 (Finset.mem_inter.mp hv1).1
  have h3 : Disjoint (A \ B) (B \ A) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_sdiff.mp hv2).2 (Finset.mem_sdiff.mp hv1).1
  have hA : A = (A ∩ B) ∪ (A \ B) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hB : B = (A ∩ B) ∪ (B \ A) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hAB : A ∪ B = (A ∩ B) ∪ ((A \ B) ∪ (B \ A)) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have h12 : Disjoint (A ∩ B) ((A \ B) ∪ (B \ A)) :=
    Finset.disjoint_union_right.mpr ⟨h1, h2⟩
  -- expand all four cuts using the disjoint-union identity
  have e1 := cutSum_add_cutSum_of_disjoint x h1
  have e2 := cutSum_add_cutSum_of_disjoint x h2
  have e3 := cutSum_add_cutSum_of_disjoint x h3
  have e4 := cutSum_add_cutSum_of_disjoint x h12
  rw [← hA] at e1
  rw [← hB] at e2
  rw [← hAB] at e4
  rw [pairSum_union_right x _ h3] at e4
  linarith [e1, e2, e3, e4]

/-- **Posimodularity as an identity**:
`x(δ(A∖B)) + x(δ(B∖A)) + 2·x(E(A∩B, (A∪B)ᶜ)) = x(δ(A)) + x(δ(B))`. -/
theorem cutSum_posimodular_identity (x : Sym2 (Fin n) → ℝ)
    (A B : Finset (Fin n)) :
    cutSum x (A \ B) + cutSum x (B \ A) + 2 * pairSum x (A ∩ B) (A ∪ B)ᶜ
      = cutSum x A + cutSum x B := by
  have hsub := cutSum_submodular_identity x A B
  have hd : Disjoint (A ∩ B) (A ∪ B)ᶜ :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2)
        (Finset.mem_union_left _ (Finset.mem_inter.mp hv1).1)
  have hd' : Disjoint (A \ B) (B \ A) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_sdiff.mp hv2).2 (Finset.mem_sdiff.mp hv1).1
  have hui : (A ∩ B) ∪ (A ∪ B)ᶜ = ((A \ B) ∪ (B \ A))ᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
      Finset.mem_sdiff]
    tauto
  have e5 := cutSum_add_cutSum_of_disjoint x hd
  have e6 := cutSum_add_cutSum_of_disjoint x hd'
  rw [hui, cutSum_compl] at e5
  -- e5 : cut(A∩B) + cut((A∪B)ᶜ) = 2·pair(A∩B, (A∪B)ᶜ) + cut((A∖B) ∪ (B∖A))
  rw [cutSum_compl] at e5
  -- and cut((A∪B)ᶜ) = cut(A∪B)
  linarith [hsub, e5, e6]

/-! ### Near-minimum cuts and crossing -/

/-- `S` is an `ε`-near minimum cut of `x`: proper, nonempty, and
`x(δ(S)) ≤ 2 + ε` (the minimum cut of a subtour-LP point being `2`).

⚠️ **The two source papers disagree on the boundary, and this follows KKO21.**
KKO21 (2007.01409v6 line 317) defines an `η`-near min cut by `x(δ(S)) ≤ 2 + η`;
KKO22 (2105.10043v3 line 402, Definition 2.6) by `x(δ(S)) < 2 + η`.  The closed
convention is used here throughout, including in the KKO22-facing `Hierarchy`
and component definitions.

That costs nothing, and `IsNearMinCut.cut_lt_of_lt` is the bridge: a closed
`ε`-near min cut is an *open* `ε'`-near min cut for every `ε' > ε`, and every
KKO22 result is stated for all sufficiently small `η`, so a KKO22 statement
wanted at a closed `ε`-cut is obtained by instantiating it at any `ε' > ε`
below KKO22's threshold.  A box cited from KKO22 and assumed at a boundary cut
`x(δ(S)) = 2 + ε` is therefore covered by KKO22's own theorem at `ε'`, not by an
extrapolation. -/
structure IsNearMinCut (x : Sym2 (Fin n) → ℝ) (ε : ℝ)
    (S : Finset (Fin n)) : Prop where
  nonempty : S.Nonempty
  ne_univ : S ≠ Finset.univ
  cut_le : cutSum x S ≤ 2 + ε

theorem IsNearMinCut.mono {ε ε' : ℝ} (h : IsNearMinCut x ε S) (hle : ε ≤ ε') :
    IsNearMinCut x ε' S :=
  ⟨h.nonempty, h.ne_univ, h.cut_le.trans (by linarith)⟩

/-- **The bridge to KKO22's strict convention.**  A closed `ε`-near min cut
satisfies KKO22's `x(δ(S)) < 2 + ε'` for every `ε' > ε`. -/
theorem IsNearMinCut.cut_lt_of_lt {ε ε' : ℝ} (h : IsNearMinCut x ε S) (hlt : ε < ε') :
    cutSum x S < 2 + ε' :=
  h.cut_le.trans_lt (by linarith)

/-- Two finite sets cross when all four corners
`A∩B, A∖B, B∖A, (A∪B)ᶜ` are nonempty.  (Stated for any finite type so it
applies both to vertex sets and to arcs of polygon points.) -/
def Crossing {V : Type*} [DecidableEq V] [Fintype V] (A B : Finset V) : Prop :=
  (A ∩ B).Nonempty ∧ (A \ B).Nonempty ∧ (B \ A).Nonempty ∧
    A ∪ B ≠ Finset.univ

theorem Crossing.symm {V : Type*} [DecidableEq V] [Fintype V]
    {A B : Finset V} (h : Crossing A B) : Crossing B A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rwa [Finset.inter_comm], h3, h2, by rwa [Finset.union_comm]⟩

/-- The subtour-LP cut lower bound, packaged. -/
theorem two_le_cutSum (hx : x ∈ subtourLP n) (h1 : S.Nonempty)
    (h2 : S ≠ Finset.univ) : 2 ≤ cutSum x S :=
  hx.2.2 S h1 h2

theorem compl_nonempty_of_ne_univ (h : S ≠ Finset.univ) :
    (Sᶜ : Finset (Fin n)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hc
  exact h ((Finset.compl_eq_empty_iff S).mp hc)

theorem compl_ne_univ_of_nonempty (h : S.Nonempty) :
    (Sᶜ : Finset (Fin n)) ≠ Finset.univ := by
  intro hc
  rw [Finset.nonempty_iff_ne_empty] at h
  exact h ((Finset.compl_eq_univ_iff S).mp hc)

/-! ### KKO21 Lemma 2.5 -/

/-- **KKO21 Lemma 2.5** ([OSS11]), intersection: crossing near-min cuts
have near-min intersection, with the errors adding. -/
theorem nearMinCut_inter (hx : x ∈ subtourLP n) (hA : IsNearMinCut x εA A)
    (hB : IsNearMinCut x εB B) (hc : Crossing A B) :
    IsNearMinCut x (εA + εB) (A ∩ B) := by
  refine ⟨hc.1, ?_, ?_⟩
  · intro h
    exact hA.ne_univ (eq_univ_of_subset_of_eq_univ Finset.inter_subset_left h)
  · have hid := cutSum_submodular_identity x A B
    have hU : 2 ≤ cutSum x (A ∪ B) :=
      two_le_cutSum hx (hA.nonempty.mono Finset.subset_union_left) hc.2.2.2
    have hP := pairSum_nonneg hx.1 (A \ B) (B \ A)
    linarith [hA.cut_le, hB.cut_le]

/-- **KKO21 Lemma 2.5** ([OSS11]), union. -/
theorem nearMinCut_union (hx : x ∈ subtourLP n) (hA : IsNearMinCut x εA A)
    (hB : IsNearMinCut x εB B) (hc : Crossing A B) :
    IsNearMinCut x (εA + εB) (A ∪ B) := by
  refine ⟨hA.nonempty.mono Finset.subset_union_left, hc.2.2.2, ?_⟩
  have hid := cutSum_submodular_identity x A B
  have hI : 2 ≤ cutSum x (A ∩ B) :=
    two_le_cutSum hx hc.1 fun h =>
      hA.ne_univ (eq_univ_of_subset_of_eq_univ Finset.inter_subset_left h)
  have hP := pairSum_nonneg hx.1 (A \ B) (B \ A)
  linarith [hA.cut_le, hB.cut_le]

/-- **KKO21 Lemma 2.5** ([OSS11]), difference: `A ∖ B` (and by
`Crossing.symm`, `B ∖ A`). -/
theorem nearMinCut_sdiff (hx : x ∈ subtourLP n) (hA : IsNearMinCut x εA A)
    (hB : IsNearMinCut x εB B) (hc : Crossing A B) :
    IsNearMinCut x (εA + εB) (A \ B) := by
  refine ⟨hc.2.1, ?_, ?_⟩
  · intro h
    exact hA.ne_univ (eq_univ_of_subset_of_eq_univ Finset.sdiff_subset h)
  · have hid := cutSum_posimodular_identity x A B
    have hBA : 2 ≤ cutSum x (B \ A) :=
      two_le_cutSum hx hc.2.2.1 fun h =>
        hB.ne_univ (eq_univ_of_subset_of_eq_univ Finset.sdiff_subset h)
    have hP := pairSum_nonneg hx.1 (A ∩ B) (A ∪ B)ᶜ
    linarith [hA.cut_le, hB.cut_le]

/-! ### KKO21 Lemma 2.6 -/

/-- **KKO21 Lemma 2.6** ([Ben97, Lem 5.3.5]), side `(A∩B, A∖B)`: the side
lying on the boundary of `A` has weight at least `1 - εA/2`. -/
theorem one_sub_half_le_pairSum_inter_sdiff (hx : x ∈ subtourLP n)
    (hA : IsNearMinCut x εA A) (hc : Crossing A B) :
    1 - εA / 2 ≤ pairSum x (A ∩ B) (A \ B) := by
  have h1 : Disjoint (A ∩ B) (A \ B) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_sdiff.mp hv2).2 (Finset.mem_inter.mp hv1).2
  have hA' : (A ∩ B) ∪ (A \ B) = A := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hid := cutSum_add_cutSum_of_disjoint x h1
  rw [hA'] at hid
  have hI : 2 ≤ cutSum x (A ∩ B) :=
    two_le_cutSum hx hc.1 fun h =>
      hA.ne_univ (eq_univ_of_subset_of_eq_univ Finset.inter_subset_left h)
  have hD : 2 ≤ cutSum x (A \ B) :=
    two_le_cutSum hx hc.2.1 fun h =>
      hA.ne_univ (eq_univ_of_subset_of_eq_univ Finset.sdiff_subset h)
  linarith [hA.cut_le]

/-- **KKO21 Lemma 2.6**, side `(A∩B, B∖A)`: at least `1 - εB/2`. -/
theorem one_sub_half_le_pairSum_inter_sdiff' (hx : x ∈ subtourLP n)
    (hB : IsNearMinCut x εB B) (hc : Crossing A B) :
    1 - εB / 2 ≤ pairSum x (A ∩ B) (B \ A) := by
  have h := one_sub_half_le_pairSum_inter_sdiff hx hB hc.symm
  rwa [Finset.inter_comm] at h

/-- **KKO21 Lemma 2.6**, side `(A∖B, (A∪B)ᶜ)`: this side lies on the
boundary of `B`, so it is at least `1 - εB/2`. -/
theorem one_sub_half_le_pairSum_sdiff_compl (hx : x ∈ subtourLP n)
    (hA : IsNearMinCut x εA A) (hB : IsNearMinCut x εB B)
    (hc : Crossing A B) :
    1 - εB / 2 ≤ pairSum x (A \ B) (A ∪ B)ᶜ := by
  have h1 : Disjoint (A \ B) (A ∪ B)ᶜ :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2)
        (Finset.mem_union_left _ (Finset.mem_sdiff.mp hv1).1)
  have hBc : (A \ B) ∪ (A ∪ B)ᶜ = Bᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    tauto
  have hid := cutSum_add_cutSum_of_disjoint x h1
  rw [hBc, cutSum_compl, cutSum_compl] at hid
  have hD : 2 ≤ cutSum x (A \ B) :=
    two_le_cutSum hx hc.2.1 fun h =>
      hA.ne_univ (eq_univ_of_subset_of_eq_univ Finset.sdiff_subset h)
  have hC : 2 ≤ cutSum x (A ∪ B) :=
    two_le_cutSum hx (hA.nonempty.mono Finset.subset_union_left) hc.2.2.2
  linarith [hB.cut_le]

/-- **KKO21 Lemma 2.6**, side `(B∖A, (A∪B)ᶜ)`: at least `1 - εA/2`. -/
theorem one_sub_half_le_pairSum_sdiff_compl' (hx : x ∈ subtourLP n)
    (hA : IsNearMinCut x εA A) (hB : IsNearMinCut x εB B)
    (hc : Crossing A B) :
    1 - εA / 2 ≤ pairSum x (B \ A) (A ∪ B)ᶜ := by
  have h := one_sub_half_le_pairSum_sdiff_compl hx hB hA hc.symm
  rwa [Finset.union_comm] at h

/-- **KKO22 Lemma 2.8**: if `A`, `B` are disjoint proper nonempty sets whose
union is an `ε`-near min cut, then `x(E(A,B)) ≥ 1 - ε/2`. -/
theorem le_pairSum_of_union (hx : x ∈ subtourLP n) (hd : Disjoint A B)
    (hA1 : A.Nonempty) (hA2 : A ≠ Finset.univ)
    (hB1 : B.Nonempty) (hB2 : B ≠ Finset.univ)
    (hC : cutSum x (A ∪ B) ≤ 2 + εA) :
    1 - εA / 2 ≤ pairSum x A B := by
  have hid := cutSum_add_cutSum_of_disjoint x hd
  have h2A : 2 ≤ cutSum x A := two_le_cutSum hx hA1 hA2
  have h2B : 2 ≤ cutSum x B := two_le_cutSum hx hB1 hB2
  linarith

/-! ### KKO21 Lemma 2.7 -/

/-- **KKO21 Lemma 2.7**, upper bound: for nested near-min cuts `A ⊆ B`
with `B ∖ A` nonempty, `x(E(A, Bᶜ)) ≤ 1 + (εA + εB)/2`. -/
theorem pairSum_le_of_subset (hx : x ∈ subtourLP n)
    (hA : IsNearMinCut x εA A) (hB : IsNearMinCut x εB B)
    (hAB : A ⊆ B) (hne : (B \ A).Nonempty) :
    pairSum x A Bᶜ ≤ 1 + (εA + εB) / 2 := by
  have hd : Disjoint A Bᶜ :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2) (hAB hv1)
  have hAc : A ∪ Bᶜ = (B \ A)ᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    by_cases hvA : v ∈ A
    · simp only [hvA]
      tauto
    · have : v ∈ B ∨ v ∉ B := em _
      tauto
  have hid := cutSum_add_cutSum_of_disjoint x hd
  rw [hAc, cutSum_compl, cutSum_compl] at hid
  -- hid : cut(A) + cut(B) = 2·pair(A, Bᶜ) + cut(B∖A)
  have hBA : 2 ≤ cutSum x (B \ A) :=
    two_le_cutSum hx hne fun h =>
      hB.ne_univ (eq_univ_of_subset_of_eq_univ Finset.sdiff_subset h)
  linarith [hA.cut_le, hB.cut_le]

/-- **KKO21 Lemma 2.7**, lower bound: for nested near-min cuts `A ⊆ B`
with `B ∖ A` nonempty, `x(E(A, B∖A)) ≥ 1 - εB/2`. -/
theorem le_pairSum_of_subset (hx : x ∈ subtourLP n)
    (hA : IsNearMinCut x εA A) (hB : IsNearMinCut x εB B)
    (hAB : A ⊆ B) (hne : (B \ A).Nonempty) :
    1 - εB / 2 ≤ pairSum x A (B \ A) := by
  have hd : Disjoint A (B \ A) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 => (Finset.mem_sdiff.mp hv2).2 hv1
  have hU : A ∪ (B \ A) = B := Finset.union_sdiff_of_subset hAB
  have hid := cutSum_add_cutSum_of_disjoint x hd
  rw [hU] at hid
  have hA2 : 2 ≤ cutSum x A := two_le_cutSum hx hA.nonempty hA.ne_univ
  have hBA : 2 ≤ cutSum x (B \ A) :=
    two_le_cutSum hx hne fun h =>
      hB.ne_univ (eq_univ_of_subset_of_eq_univ Finset.sdiff_subset h)
  linarith [hB.cut_le]

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.AtomPath
import TSPGap.Uncrossing

/-!
# Lemma 2.26 for an edge bundle

KKO22 §5.3 conditions on a *bundle* `e = (u, v)` being absent, where `u` and
`v` are atoms and `e` is a set of genuine LP edges running between them.  This
file lifts Lemma 2.26 from a single edge to such a bundle.

## Binary support comes first

Nothing works until the bundle is known to be *one-hot* on the support:
`card_inter_bundle_le_one` — when the two endpoint atoms induce trees, a
supported spanning tree contains **at most one** edge of any
`E ⊆ betweenEdges u v`.  Two of them would close a cycle through the atoms;
formally the second edge routes around the first, contradicting the first
being a bridge.  Without this the two layers below do not exhaust the measure
and every mass identity fails.

## The two layers

Projecting along `univ \ E` at fixed rank `k+1`:

* layer `k+1` is `avoidWeight w E` — the trees missing the bundle;
* layer `k` is `bundleContract w E := fun U => ∑ e ∈ E, contractWeight w e U`
  — the trees meeting it once, indexed by the tree with its bundle edge
  removed.

So `exists_adjacent_covering` applies to a bundle exactly as it applied to a
single edge, and every arc still adds exactly one edge.  Defining the lower
layer as a *sum of single-edge contractions* is what makes every identity of
`Lemma226.lean` available term by term.

## The forgotten witness

The lower layer forgets *which* bundle edge was present.  No disintegration is
needed to recover it: a nonzero lower-layer weight is a nonzero sum, so some
`e ∈ E` has `w (insert e U) ≠ 0`, and that witness is all the exchange needs —
because both quantities in play are independent of the choice.  The count
`|S ∩ D|` is, since `D ⊆ δ(A)` for an atom `A` disjoint from `u` and `v`, so no
bundle edge is ever counted; and `OnAtomPath T u v A` is a statement about `T`
alone.

⚠️ `E` is kept abstract as any `E ⊆ betweenEdges u v`.  KKO's top bundles also
filter by hierarchy parent and by the LP support, so a bundle must not be
identified with the whole ambient `betweenEdges u v`.

## Main results

* `card_inter_bundle_le_one` — the one-hot lemma.
* `bundleContract`, `projLayer_sdiff_top`, `projLayer_sdiff_bundle`.
* `totalMass_split_bundle`, `expCard_split_bundle`.
* `expCard_avoid_le_of_exchange` — the aggregation, division-free.
* `expCard_avoid_le_bundle`, `expCard_avoid_le_bundle_conditional` — Lemma 2.26
  for a bundle.
-/

namespace TSPGap
open Finset

/-! ### Edges between atoms -/

variable {n : ℕ}

theorem mem_betweenEdges_iff {A B : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ betweenEdges A B ↔ ∃ a ∈ A, ∃ b ∈ B, e = s(a, b) := by
  rw [betweenEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- An edge of a cut has an endpoint on the near side. -/
theorem exists_mem_of_mem_cutEdges {A : Finset (Fin n)} {e : Sym2 (Fin n)}
    (he : e ∈ cutEdges A) : ∃ x ∈ A, x ∈ e := by
  obtain ⟨p, hp, q, -, rfl⟩ := mem_cutEdges_iff''.mp he
  exact ⟨p, hp, Sym2.mem_mk_left p q⟩

/-- An edge with both endpoints off `A` does not cross `δ(A)`. -/
theorem notMem_cutEdges_of_notMem {A : Finset (Fin n)} {a b : Fin n}
    (ha : a ∉ A) (hb : b ∉ A) : s(a, b) ∉ cutEdges A := by
  intro hc
  obtain ⟨x, hxA, hxe⟩ := exists_mem_of_mem_cutEdges hc
  rcases Sym2.mem_iff.mp hxe with rfl | rfl
  · exact ha hxA
  · exact hb hxA

/-- Any walk of a subgraph is a walk of the ambient graph, on the same
vertices. -/
theorem exists_walk_of_subset {A B : Finset (Sym2 (Fin n))} (hAB : A ⊆ B)
    {a b : Fin n}
    (p : (SimpleGraph.fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Walk a b) :
    ∃ q : (SimpleGraph.fromEdgeSet (↑B : Set (Sym2 (Fin n)))).Walk a b,
      q.support = p.support := by
  have hedge : ∀ e ∈ p.edges,
      e ∈ (SimpleGraph.fromEdgeSet (↑B : Set (Sym2 (Fin n)))).edgeSet := by
    intro e he
    have h1 := p.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at h1 ⊢
    exact ⟨by simpa using hAB (by simpa using h1.1), h1.2⟩
  exact ⟨p.transfer _ hedge, p.support_transfer hedge⟩

/-! ### The one-hot lemma -/

/-- **A supported tree meets a bundle at most once.**  If it met `E` twice, the
second edge together with paths inside the (connected) endpoint atoms would
route around the first, contradicting the first being a bridge. -/
theorem card_inter_bundle_le_one {T : Finset (Sym2 (Fin n))} {u v : Finset (Fin n)}
    (hT : IsSpanningTree n T) (hu : InducesTree u T) (hv : InducesTree v T)
    (huv : Disjoint u v) {E : Finset (Sym2 (Fin n))} (hE : E ⊆ betweenEdges u v) :
    (T ∩ E).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro e₁ h₁ e₂ h₂
  by_contra hne
  obtain ⟨he₁T, he₁E⟩ := Finset.mem_inter.mp h₁
  obtain ⟨he₂T, he₂E⟩ := Finset.mem_inter.mp h₂
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_betweenEdges_iff.mp (hE he₁E)
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := mem_betweenEdges_iff.mp (hE he₂E)
  -- the first edge is a bridge of `T`
  have hnotmem : s(a₁, b₁) ∉ T.erase s(a₁, b₁) := Finset.notMem_erase _ _
  have hins : insert s(a₁, b₁) (T.erase s(a₁, b₁)) = T := Finset.insert_erase he₁T
  refine not_reachable_of_spanningTree_insert hnotmem (by rw [hins]; exact hT) ?_
  -- the inside parts avoid the first edge
  have hinu : insidePart u T ⊆ T.erase s(a₁, b₁) := by
    intro x hx
    obtain ⟨hxT, hxu⟩ := mem_insidePart.mp hx
    refine Finset.mem_erase.mpr ⟨?_, hxT⟩
    intro hc
    exact Finset.disjoint_left.mp huv (hxu b₁ (hc ▸ Sym2.mem_mk_right a₁ b₁)) hb₁
  have hinv : insidePart v T ⊆ T.erase s(a₁, b₁) := by
    intro x hx
    obtain ⟨hxT, hxv⟩ := mem_insidePart.mp hx
    refine Finset.mem_erase.mpr ⟨?_, hxT⟩
    intro hc
    exact Finset.disjoint_left.mp huv ha₁ (hxv a₁ (hc ▸ Sym2.mem_mk_left a₁ b₁))
  -- and the second edge does too
  have he₂ : s(a₂, b₂) ∈ T.erase s(a₁, b₁) := Finset.mem_erase.mpr ⟨Ne.symm hne, he₂T⟩
  have hadj : (SimpleGraph.fromEdgeSet
      (↑(T.erase s(a₁, b₁)) : Set (Sym2 (Fin n)))).Adj a₂ b₂ := by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨Finset.mem_coe.mpr he₂, fun hc => Finset.disjoint_left.mp huv ha₂ (hc ▸ hb₂)⟩
  obtain ⟨pu⟩ := hu.2 a₁ ha₁ a₂ ha₂
  obtain ⟨pv⟩ := hv.2 b₂ hb₂ b₁ hb₁
  obtain ⟨pu', -⟩ := exists_walk_of_subset hinu pu
  obtain ⟨pv', -⟩ := exists_walk_of_subset hinv pv
  exact ⟨pu'.append (SimpleGraph.Walk.cons hadj pv')⟩

/-! ### The lower layer -/

section Layers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The lower layer of the bundle projection: the mass of the sets meeting `E`
exactly once, indexed by the set with its bundle element removed.  Summing over
the bundle is what makes every single-edge identity available term by term. -/
noncomputable def bundleContract (w : Finset ι → ℝ) (E : Finset ι) : Finset ι → ℝ :=
  fun U => ∑ e ∈ E, contractWeight w e U

omit [Fintype ι] in
theorem weightNonneg_bundleContract {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (E : Finset ι) : WeightNonneg (bundleContract w E) := fun U =>
  Finset.sum_nonneg fun e _ => (hnn.contract e) U

omit [Fintype ι] in
/-- **The forgotten witness.**  A nonzero lower-layer weight exhibits a bundle
element that is actually present. -/
theorem exists_witness_of_bundleContract {w : Finset ι → ℝ} {E : Finset ι}
    {U : Finset ι} (h : bundleContract w E U ≠ 0) :
    ∃ e ∈ E, e ∉ U ∧ w (insert e U) ≠ 0 := by
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have heU : e ∉ U := fun hc => hne (by simp [contractWeight, hc])
  exact ⟨e, he, heU, by rwa [contractWeight, if_neg heU] at hne⟩

theorem totalMass_bundleContract (w : Finset ι → ℝ) (E : Finset ι) :
    totalMass (bundleContract w E) = expCard w E := by
  classical
  rw [expCard_eq_sum_marginal, totalMass]
  rw [Finset.sum_congr rfl fun U (_ : U ∈ Finset.univ) => by rw [bundleContract]]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => totalMass_contractWeight w e

/-- The lower layer's expected count, when `D` misses the bundle. -/
theorem expCard_bundleContract (w : Finset ι → ℝ) (E D : Finset ι)
    (hED : Disjoint E D) :
    expCard (bundleContract w E) D
      = ∑ S : Finset ι, w S * ((S ∩ D).card : ℝ) * ((S ∩ E).card : ℝ) := by
  classical
  have step1 : expCard (bundleContract w E) D
      = ∑ e ∈ E, ∑ U : Finset ι, contractWeight w e U * ((U ∩ D).card : ℝ) := by
    rw [expCard]
    rw [Finset.sum_congr rfl fun U (_ : U ∈ Finset.univ) => by
      rw [bundleContract, Finset.sum_mul]]
    exact Finset.sum_comm
  have step2 : ∀ e ∈ E, ∑ U : Finset ι, contractWeight w e U * ((U ∩ D).card : ℝ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S),
          w S * ((S ∩ D).card : ℝ) := by
    intro e he
    have heD : e ∉ D := Finset.disjoint_left.mp hED he
    rw [Finset.sum_congr rfl fun U (_ : U ∈ Finset.univ) => by
      rw [show ((U ∩ D).card : ℝ) = (((insert e U) ∩ D).card : ℝ) by
        rw [Finset.insert_inter_of_notMem heD]]]
    exact sum_contract_eq w e (fun S => ((S ∩ D).card : ℝ))
  rw [step1, Finset.sum_congr rfl step2]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ E) => Finset.sum_filter _ _]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.inter_comm, nsmul_eq_mul]
  ring

/-! ### The two layers of the projection -/

theorem inter_univ_sdiff (S E : Finset ι) : S ∩ (Finset.univ \ E) = S \ E := by
  ext x
  simp

/-- The top layer of the bundle projection is `avoidWeight`. -/
theorem projLayer_sdiff_top {w : Finset ι → ℝ} {k : ℕ}
    (hr : FixedRankWeight (k + 1) w) (E : Finset ι) :
    projLayer w (Finset.univ \ E) (k + 1) = avoidWeight w E := by
  classical
  funext U
  rw [projLayer, avoidWeight_apply]
  by_cases hcard : U.card = k + 1
  · rw [if_pos hcard]
    by_cases hdisj : (U ∩ E).card = 0
    · rw [if_pos hdisj]
      have hUE : Disjoint U E :=
        Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hdisj)
      refine Finset.sum_eq_single U ?_ ?_
      · intro S hS hne
        by_contra hw
        have hSc : S.card = k + 1 := hr S hw
        have hSE : S ∩ (Finset.univ \ E) = U := (Finset.mem_filter.mp hS).2
        rw [inter_univ_sdiff] at hSE
        have hsub : U ⊆ S := hSE ▸ Finset.sdiff_subset
        exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      · intro hU
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [inter_univ_sdiff, Finset.sdiff_eq_self_of_disjoint hUE]⟩) hU
    · rw [if_neg hdisj]
      refine Finset.sum_eq_zero fun S hS => ?_
      exfalso
      have hSE : S ∩ (Finset.univ \ E) = U := (Finset.mem_filter.mp hS).2
      rw [inter_univ_sdiff] at hSE
      refine hdisj ?_
      rw [← hSE]
      simp
  · rw [if_neg hcard]
    by_cases hdisj : (U ∩ E).card = 0
    · rw [if_pos hdisj]
      by_contra hw
      exact hcard (hr U (Ne.symm hw))
    · rw [if_neg hdisj]

/-- The lower layer of the bundle projection is `bundleContract` — **given the
one-hot hypothesis**, without which the layers would not exhaust the measure. -/
theorem projLayer_sdiff_bundle {w : Finset ι → ℝ} {k : ℕ}
    (hr : FixedRankWeight (k + 1) w) (E : Finset ι)
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) :
    projLayer w (Finset.univ \ E) k = bundleContract w E := by
  classical
  funext U
  by_cases hcard : U.card = k
  · rw [projLayer, if_pos hcard]
    by_cases hUE : Disjoint U E
    · have hmemE : ∀ e ∈ E, e ∉ U := fun e he hc =>
        Finset.disjoint_left.mp hUE hc he
      have himg : E.image (fun e => insert e U)
          ⊆ Finset.univ.filter (fun S : Finset ι => S ∩ (Finset.univ \ E) = U) := by
        intro S hS
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hS
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [inter_univ_sdiff]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxE⟩
          · exact absurd he hxE
          · exact hx
        · intro hx
          exact ⟨Or.inr hx, fun hc => Finset.disjoint_left.mp hUE hx hc⟩
      have hzero : ∀ S ∈ Finset.univ.filter
          (fun S : Finset ι => S ∩ (Finset.univ \ E) = U),
          S ∉ E.image (fun e => insert e U) → w S = 0 := by
        intro S hS hSimg
        by_contra hw
        have hSc : S.card = k + 1 := hr S hw
        have hSE : S ∩ (Finset.univ \ E) = U := (Finset.mem_filter.mp hS).2
        rw [inter_univ_sdiff] at hSE
        have hsub : U ⊆ S := hSE ▸ Finset.sdiff_subset
        obtain ⟨e, heS, heU⟩ : ∃ e ∈ S, e ∉ U := by
          refine Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩)
          intro hc
          rw [hc] at hcard
          omega
        have heE : e ∈ E := by
          by_contra hc
          exact heU (hSE ▸ Finset.mem_sdiff.mpr ⟨heS, hc⟩)
        refine hSimg (Finset.mem_image.mpr ⟨e, heE, ?_⟩)
        refine Finset.eq_of_subset_of_card_le (Finset.insert_subset heS hsub) ?_
        rw [Finset.card_insert_of_notMem heU]
        omega
      rw [← Finset.sum_subset himg hzero,
        Finset.sum_image (fun a ha b hb hab => by
          by_contra hne
          have haU : a ∉ U := hmemE a ha
          have : a ∈ insert b U := hab ▸ Finset.mem_insert_self a U
          rcases Finset.mem_insert.mp this with h | h
          · exact hne h
          · exact haU h)]
      exact Finset.sum_congr rfl fun e he => by
        rw [contractWeight, if_neg (hmemE e he)]
    · obtain ⟨e₀, he₀U, he₀E⟩ : ∃ e ∈ U, e ∈ E := Finset.not_disjoint_iff.mp hUE
      have hempty : Finset.univ.filter
          (fun S : Finset ι => S ∩ (Finset.univ \ E) = U) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun S hS => ?_
        have hSE : S ∩ (Finset.univ \ E) = U := (Finset.mem_filter.mp hS).2
        rw [inter_univ_sdiff] at hSE
        exact (Finset.mem_sdiff.mp (hSE ▸ he₀U)).2 he₀E
      rw [hempty, Finset.sum_empty, bundleContract]
      refine (Finset.sum_eq_zero fun e he => ?_).symm
      by_cases heU : e ∈ U
      · simp [contractWeight, heU]
      · rw [contractWeight, if_neg heU]
        by_contra hw
        have h2 : ({e₀, e} : Finset ι) ⊆ (insert e U) ∩ E := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem he₀U, he₀E⟩
          · rw [Finset.mem_singleton] at hx
            subst hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, he⟩
        have hne0 : e₀ ≠ e := fun hc => heU (by rw [← hc]; exact he₀U)
        have hcard2 : ({e₀, e} : Finset ι).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using hne0), Finset.card_singleton]
        have hle := hone _ hw
        have hmono := Finset.card_le_card h2
        omega
  · rw [projLayer, if_neg hcard, bundleContract]
    refine (Finset.sum_eq_zero fun e _ => ?_).symm
    by_cases heU : e ∈ U
    · simp [contractWeight, heU]
    · rw [contractWeight, if_neg heU]
      by_contra hw
      have hcc := hr _ hw
      rw [Finset.card_insert_of_notMem heU] at hcc
      omega

/-! ### The two-layer splits -/

/-- **Mass.**  The two layers exhaust the measure — this is where the one-hot
hypothesis is spent. -/
theorem totalMass_split_bundle {w : Finset ι → ℝ} (E : Finset ι)
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) :
    totalMass w = totalMass (bundleContract w E) + totalMass (avoidWeight w E) := by
  classical
  rw [totalMass_bundleContract, expCard, totalMass, totalMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avoidWeight_apply]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · have hle := hone S h0
    rcases Nat.lt_or_ge (S ∩ E).card 1 with h1 | h1
    · have hz : (S ∩ E).card = 0 := by omega
      rw [if_pos hz, hz]
      simp
    · have hz : (S ∩ E).card = 1 := by omega
      rw [if_neg (by omega), hz]
      simp

/-- **Counts.**  The same split for `expCard`, valid whenever `D` misses the
bundle. -/
theorem expCard_split_bundle {w : Finset ι → ℝ} (E D : Finset ι)
    (hED : Disjoint E D) (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) :
    expCard w D = expCard (bundleContract w E) D + expCard (avoidWeight w E) D := by
  classical
  rw [expCard_bundleContract w E D hED, expCard, expCard, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avoidWeight_apply]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · have hle := hone S h0
    rcases Nat.lt_or_ge (S ∩ E).card 1 with h1 | h1
    · have hz : (S ∩ E).card = 0 := by omega
      rw [if_pos hz, hz]
      simp
    · have hz : (S ∩ E).card = 1 := by omega
      rw [if_neg (by omega), hz]
      simp

/-! ### The aggregation -/

/-- The bundle coupling: rows carry the lower layer, columns the top layer, and
every arc adds exactly one element. -/
theorem exists_bundle_covering {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (E : Finset ι)
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) :
    ∃ z : Finset ι → Finset ι → ℝ, (∀ S T, 0 ≤ z S T)
      ∧ (∀ S T, z S T ≠ 0 → S ⊆ T)
      ∧ (∀ S, ∑ T, z S T = totalMass (avoidWeight w E) * bundleContract w E S)
      ∧ (∀ T, ∑ S, z S T = totalMass (bundleContract w E) * avoidWeight w E T) := by
  obtain ⟨z, hz0, hzsub, hrow, hcol⟩ :=
    exists_adjacent_covering hst hr hnn htot (Finset.univ \ E) k
  rw [projLayer_sdiff_top hr E, projLayer_sdiff_bundle hr E hone] at hrow hcol
  exact ⟨z, hz0, fun S T h => (hzsub S T h).1, hrow, hcol⟩

open Classical in
/-- **The aggregation**, division-free and with no case analysis on degenerate
masses: adding `m_out · E_out` to the coupling inequality and using
`m_in + m_out = 1` with the two-layer split gives the stated form. -/
theorem expCard_avoid_le_of_exchange {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (E D : Finset ι)
    (hED : Disjoint E D) (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1)
    (P : Finset ι → Prop)
    (hexch : ∀ S T : Finset ι, bundleContract w E S ≠ 0 → avoidWeight w E T ≠ 0 →
      S ⊆ T → ((T ∩ D).card : ℝ) ≤ ((S ∩ D).card : ℝ) + (if P T then 1 else 0)) :
    expCard (avoidWeight w E) D
      ≤ totalMass (avoidWeight w E) * expCard w D
        + totalMass (bundleContract w E) * weightMass (avoidWeight w E) P := by
  classical
  obtain ⟨z, hz0, harc, hrow, hcol⟩ := exists_bundle_covering hst hr hnn htot E hone
  set mIn : ℝ := totalMass (bundleContract w E) with hmIn
  set mOut : ℝ := totalMass (avoidWeight w E) with hmOut
  have hLHS : ∑ T, (∑ S, z S T) * ((T ∩ D).card : ℝ)
      = mIn * expCard (avoidWeight w E) D := by
    rw [expCard, Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by rw [hcol T]; ring
  have hR1 : ∑ S, (∑ T, z S T) * ((S ∩ D).card : ℝ)
      = mOut * expCard (bundleContract w E) D := by
    rw [expCard, Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by rw [hrow S]; ring
  have hR2 : ∑ T, (∑ S, z S T) * (if P T then (1:ℝ) else 0)
      = mIn * weightMass (avoidWeight w E) P := by
    rw [weightMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hcol T]
    by_cases hP : P T
    · rw [if_pos hP, if_pos hP, mul_one]
    · rw [if_neg hP, if_neg hP, mul_zero, mul_zero]
  have hpoint : ∀ S T : Finset ι, z S T * ((T ∩ D).card : ℝ)
      ≤ z S T * (((S ∩ D).card : ℝ) + (if P T then (1:ℝ) else 0)) := by
    intro S T
    rcases eq_or_lt_of_le (hz0 S T) with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ hpos.le
      have hzne : z S T ≠ 0 := ne_of_gt hpos
      have hrowpos : (0:ℝ) < ∑ T', z S T' :=
        lt_of_lt_of_le hpos
          (Finset.single_le_sum (fun T' _ => hz0 S T') (Finset.mem_univ T))
      have hcolpos : (0:ℝ) < ∑ S', z S' T :=
        lt_of_lt_of_le hpos
          (Finset.single_le_sum (fun S' _ => hz0 S' T) (Finset.mem_univ S))
      rw [hrow S] at hrowpos
      rw [hcol T] at hcolpos
      refine hexch S T (fun h0 => ?_) (fun h0 => ?_) (harc S T hzne)
      · rw [h0, mul_zero] at hrowpos
        exact lt_irrefl 0 hrowpos
      · rw [h0, mul_zero] at hcolpos
        exact lt_irrefl 0 hcolpos
  have hsum : ∑ T, (∑ S, z S T) * ((T ∩ D).card : ℝ)
      ≤ (∑ S, (∑ T, z S T) * ((S ∩ D).card : ℝ))
        + ∑ T, (∑ S, z S T) * (if P T then (1:ℝ) else 0) := by
    have hexpand : ∀ T : Finset ι, (∑ S, z S T) * ((T ∩ D).card : ℝ)
        = ∑ S, z S T * ((T ∩ D).card : ℝ) := fun T => by rw [Finset.sum_mul]
    have hexpand1 : ∀ S : Finset ι, (∑ T, z S T) * ((S ∩ D).card : ℝ)
        = ∑ T, z S T * ((S ∩ D).card : ℝ) := fun S => by rw [Finset.sum_mul]
    have hexpand2 : ∀ T : Finset ι, (∑ S, z S T) * (if P T then (1:ℝ) else 0)
        = ∑ S, z S T * (if P T then (1:ℝ) else 0) := fun T => by rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun T _ => hexpand T),
      Finset.sum_congr rfl (fun S _ => hexpand1 S),
      Finset.sum_congr rfl (fun T _ => hexpand2 T), Finset.sum_comm
        (f := fun T S => z S T * (if P T then (1:ℝ) else 0)),
      Finset.sum_comm (f := fun T S => z S T * ((T ∩ D).card : ℝ)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun T _ => ?_
    nlinarith [hpoint S T]
  rw [hLHS, hR1, hR2] at hsum
  have hsplit := expCard_split_bundle (w := w) E D hED hone
  have hmass : mIn + mOut = 1 := by
    rw [hmIn, hmOut, ← htot]
    exact (totalMass_split_bundle E hone).symm
  have hprod : (mIn + mOut) * expCard (avoidWeight w E) D
      = expCard (avoidWeight w E) D := by rw [hmass, one_mul]
  have hprod2 : mOut * expCard w D
      = mOut * expCard (bundleContract w E) D + mOut * expCard (avoidWeight w E) D := by
    rw [hsplit]; ring
  linarith [hsum, hprod, hprod2]

end Layers

/-! ### The bundle exchange -/

open Classical in
/-- **The exchange at a bundle.**  The witness `e` is any present bundle edge:
its endpoints lie in `u` and `v`, both disjoint from `A`, so `e` is never
counted by `D ⊆ δ(A)`, and the swapped-in edge `g` can contribute only by
meeting `A` — in which case the tree exchange puts a vertex of `A` on the
`u`–`v` path. -/
theorem card_inter_le_bundle_exchange {S : Finset (Sym2 (Fin n))}
    {u v A : Finset (Fin n)} {E : Finset (Sym2 (Fin n))} {e g : Sym2 (Fin n)}
    (hEuv : E ⊆ betweenEdges u v) (heE : e ∈ E) (heS : e ∉ S)
    (hStree : IsSpanningTree n (insert e S))
    (hTu : InducesTree u (insert g S)) (hTv : InducesTree v (insert g S))
    (huA : Disjoint u A) (hvA : Disjoint v A)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges A) :
    (((insert g S) ∩ D).card : ℝ)
      ≤ ((S ∩ D).card : ℝ) + (if OnAtomPath (insert g S) u v A then 1 else 0) := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp (hEuv heE)
  by_cases hgD : g ∈ D
  · obtain ⟨x, hxA, hxg⟩ := exists_mem_of_mem_cutEdges (hD hgD)
    have hpath : OnUVPath (insert g S) a b x := tree_exchange heS hStree hxg
    rw [if_pos (onAtomPath_of_onUVPath hTu hTv ha hb hxA huA hvA hpath),
      Finset.insert_inter_of_mem hgD]
    have hcard := Finset.card_insert_le g (S ∩ D)
    exact_mod_cast Nat.cast_le.mpr hcard
  · rw [Finset.insert_inter_of_notMem hgD]
    have hind : (0 : ℝ) ≤ (if OnAtomPath (insert g S) u v A then 1 else 0) := by
      split <;> norm_num
    linarith

/-! ### Lemma 2.26 for a bundle -/

open Classical in
/-- **KKO22 Lemma 2.26 at an edge bundle**, division-free.  Conditioning on the
bundle being absent raises the expected count on any `D ⊆ δ(A)`, for an atom
`A` disjoint from the bundle's endpoints, by at most the probability that `A`
separates them. -/
theorem expCard_avoid_le_bundle {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v A : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hsupp : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T)
    (hEuv : E ⊆ betweenEdges u v) (huv : Disjoint u v)
    (huA : Disjoint u A) (hvA : Disjoint v A)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges A) :
    expCard (avoidWeight w E) D
      ≤ totalMass (avoidWeight w E) * expCard w D
        + totalMass (bundleContract w E) *
            weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A) := by
  classical
  have hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1 := by
    intro S hS
    obtain ⟨hT, hu, hv⟩ := hsupp S hS
    exact card_inter_bundle_le_one hT hu hv huv hEuv
  have hED : Disjoint E D := by
    refine Finset.disjoint_left.mpr fun x hxE hxD => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp (hEuv hxE)
    exact notMem_cutEdges_of_notMem (Finset.disjoint_left.mp huA ha)
      (Finset.disjoint_left.mp hvA hb) (hD hxD)
  refine expCard_avoid_le_of_exchange hst hr hnn htot E D hED hone _ ?_
  intro S T hS hT hsub
  obtain ⟨e, heE, heS, hwe⟩ := exists_witness_of_bundleContract hS
  have hTavoid : (T ∩ E).card = 0 := by
    by_contra hc
    exact hT (by rw [avoidWeight_apply, if_neg hc])
  have hwT : w T ≠ 0 := fun hc => hT (by rw [avoidWeight_apply, if_pos hTavoid, hc])
  obtain ⟨hTtree, hTu, hTv⟩ := hsupp T hwT
  obtain ⟨hStree, -, -⟩ := hsupp _ hwe
  have hcardS : S.card + 1 = k + 1 := by
    rw [← Finset.card_insert_of_notMem heS]; exact hr _ hwe
  have hcardT : T.card = k + 1 := hr _ hwT
  obtain ⟨g, hgT, hgS⟩ : ∃ g ∈ T, g ∉ S := by
    refine Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩)
    intro hc
    rw [hc] at hcardS
    omega
  have hTg : T = insert g S := by
    refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hgT hsub) ?_).symm
    rw [Finset.card_insert_of_notMem hgS]
    omega
  subst hTg
  exact card_inter_le_bundle_exchange hEuv heE heS hStree hTu hTv huA hvA hD

open Classical in
/-- The paper-facing form.  ⚠️ The factor `P[bundle present]` is kept exactly,
as Lemma 2.27 needs it. -/
theorem expCard_avoid_le_bundle_conditional {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v A : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hsupp : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T)
    (hEuv : E ⊆ betweenEdges u v) (huv : Disjoint u v)
    (huA : Disjoint u A) (hvA : Disjoint v A)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges A)
    (hpos : 0 < totalMass (avoidWeight w E)) :
    expCard (avoidWeight w E) D / totalMass (avoidWeight w E)
      ≤ expCard w D
        + totalMass (bundleContract w E) *
            (weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A)
              / totalMass (avoidWeight w E)) := by
  have hbase := expCard_avoid_le_bundle hst hr hnn htot hsupp hEuv huv huA hvA hD
  have hne : totalMass (avoidWeight w E) ≠ 0 := ne_of_gt hpos
  rw [div_le_iff₀ hpos, add_mul, mul_assoc, div_mul_cancel₀ _ hne]
  linarith [hbase]

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeExchange

/-!
# KKO22 Lemma 2.27

For two adjacent edges `e = (u,v)`, `f = (v,z)` whose marginals are both within
`ε` of `1/2`, conditioning on `e ∉ T` and on `f ∉ T` cannot raise *both*
punctured degrees `W = δ(z) − f` and `U = δ(u) − e` by much:

`E[W | e ∉ T] + E[U | f ∉ T] ≤ E[W] + E[U] + 0.81`.

(KKO's third vertex is called `w`; here it is `z`, because `w` names the
weight throughout this development.)

## The four steps

1. **The two conditional bounds.**  Lemma 2.26 in its exact conditional form
   gives `E[W|e∉T] ≤ E[W] + P[e ∈ T]·P[z ∈ P_{u,v} | e ∉ T]`, and the factor
   `P[e ∈ T]` is what converts to `+2ε`: with `m_in ≤ 1/2 + ε` and the path
   mass at most `m_out`, `m_in·A/m_out ≤ A + 2ε` whichever of the two masses
   is larger (`cond_path_bound`).

   ⚠️ KKO apply Lemma 2.26 at the *full* degree `δ(z)` and then pass to the
   subset `W` by negative association.  That step is unnecessary here: the
   exchange inequality holds verbatim for any set of edges at `z`, because the
   only new edge `g` can contribute only by being incident to `z`.  So no
   negative association enters Lemma 2.27 at all — the second branch's
   subtraction is likewise an exact identity (`expCard_sdiff_of_subset`), not
   an inequality.

2. **The two path events are exclusive** (`not_onUVPath_both`): in a connected
   graph `z` cannot lie on every `u`–`v` walk while `u` lies on every `v`–`z`
   walk.  The universal form of `OnUVPath` makes this a *distance* argument —
   each hypothesis splits a geodesic, `d(u,z) + d(z,v) ≤ d(u,v)` and
   `d(v,u) + d(u,z) ≤ d(v,z)`, and adding gives `2·d(u,z) ≤ 0`.  Acyclicity is
   never used, only connectivity.

3. **Small conditional marginal.**  If `α = P[f ∈ T | e ∉ T] ≤ 0.6` (or the
   symmetric `β ≤ 0.6`) then `P[e,f ∈ T] ≥ 0.198`, and step 2 turns the two
   path masses into `≤ 1 − P[e,f ∈ T] ≤ 0.802`.

4. **Large conditional marginals.**  Otherwise both exceed `0.6`, and each
   side is bounded directly: `E[W|e∉T] ≤ E[W] + P[e] + P[f] − α ≤ E[W] + 0.405`.

## Main results

* `cond_path_bound`, `joint_ge_of_cond_le`, `side_bound_of_cond_gt` — the three
  numeric steps, isolated as real-variable lemmas.
* `not_onUVPath_both` — step 2.
* `path_masses_le` — steps 2 and 3's measure algebra.
* `lemma_2_27` — the theorem.
-/

namespace TSPGap
open Finset

/-! ### Numeric lemmas -/

/-- **The `+2ε` slack.**  `m_in·A/m_out ≤ A + 2ε` when `A ≤ m_out`,
`m_in + m_out = 1` and `m_in ≤ 1/2 + ε`.  Both orderings of the two masses
occur, and the bound holds in each: if `m_in ≤ m_out` the factor is at most
one, and otherwise `m_in − m_out = 2m_in − 1 ≤ 2ε`. -/
theorem cond_path_bound {A mIn mOut ε : ℝ} (hA0 : 0 ≤ A) (hAm : A ≤ mOut)
    (hpos : 0 < mOut) (hsum : mIn + mOut = 1) (hIn : mIn ≤ 1 / 2 + ε) (hε : 0 ≤ ε) :
    mIn * (A / mOut) ≤ A + 2 * ε := by
  rw [← mul_div_assoc, div_le_iff₀ hpos]
  rcases le_or_gt mIn mOut with h | h
  · nlinarith
  · nlinarith

/-- **Step 3.**  A conditional marginal at most `0.6` forces the joint mass
`P[e, f ∈ T] = P[f] − P[f ∈ T ∧ e ∉ T]` to be at least `0.198`. -/
theorem joint_ge_of_cond_le {pF mOut aF ε : ℝ} (hpF : 1 / 2 - ε ≤ pF)
    (hmOut : mOut ≤ 1 / 2 + ε) (hpos : 0 < mOut) (hcond : aF / mOut ≤ 0.6)
    (hε1 : ε ≤ 1 / 1000) :
    0.198 ≤ pF - aF := by
  have h : aF ≤ 0.6 * mOut := by
    rw [div_le_iff₀ hpos] at hcond; linarith
  nlinarith

/-- **Step 4.**  A conditional marginal above `0.6` bounds one side directly:
`P[e] + P[f] − α ≤ (1/2+ε) + (1/2+ε) − 0.6 ≤ 0.405`. -/
theorem side_bound_of_cond_gt {pE pF aF mOut ε : ℝ} (hpE : pE ≤ 1 / 2 + ε)
    (hpF : pF ≤ 1 / 2 + ε) (hcond : 0.6 ≤ aF / mOut) (hε1 : ε ≤ 1 / 1000) :
    pE + pF - aF / mOut ≤ 0.405 := by
  linarith

/-! ### Mass bridges -/

section Bridges

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass of an event under the deleted weight is the mass of the event
conjoined with avoidance.  (`FederMihail.weightMass_deleteWeight` states this
for `outSection` events; here `A` is arbitrary.) -/
theorem weightMass_delete_eq (w : Finset ι → ℝ) (k : ι) (A : Finset ι → Prop) :
    weightMass (deleteWeight w k) A = weightMass w (fun S => A S ∧ k ∉ S) := by
  classical
  refine Finset.sum_congr rfl fun V _ => ?_
  by_cases h : k ∈ V
  · simp [deleteWeight, h]
  · by_cases hA : A V <;> simp [deleteWeight, h, hA]

/-- The expected count over a single edge is that edge's marginal. -/
theorem expCard_singleton (w : Finset ι → ℝ) (k : ι) :
    expCard w {k} = weightMass w (fun S => k ∈ S) := by
  rw [expCard_eq_sum_marginal, Finset.sum_singleton]

end Bridges

/-! ### Cut-edge membership -/

variable {n : ℕ}

theorem mem_cutEdges_left {a b : Fin n} (hab : a ≠ b) : s(a, b) ∈ cutEdges {a} :=
  mem_cutEdges_iff''.mpr ⟨a, Finset.mem_singleton_self a, b,
    Finset.mem_compl.mpr (by simpa using Ne.symm hab), rfl⟩

theorem mem_cutEdges_right {a b : Fin n} (hab : a ≠ b) : s(a, b) ∈ cutEdges {b} := by
  rw [Sym2.eq_swap]
  exact mem_cutEdges_left (Ne.symm hab)

/-! ### Step 2: the two path events are exclusive -/

/-- **A vertex on every `a`–`b` walk splits every geodesic.**  Only
connectivity is used. -/
theorem dist_add_dist_le_of_onUVPath {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {a b c : Fin n} (h : OnUVPath T a b c) :
    (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist a c
        + (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist c b
      ≤ (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist a b := by
  obtain ⟨p, hp⟩ := hT.2.2.exists_walk_length_eq_dist a b
  have hmem : c ∈ p.support := h p
  have hspec := SimpleGraph.Walk.take_spec p hmem
  have hlen : (p.takeUntil c hmem).length + (p.dropUntil c hmem).length = p.length := by
    conv_rhs => rw [← hspec]
    rw [SimpleGraph.Walk.length_append]
  have h1 := SimpleGraph.dist_le (p.takeUntil c hmem)
  have h2 := SimpleGraph.dist_le (p.dropUntil c hmem)
  omega

/-- **Step 2.**  In a spanning tree, `z` cannot lie on every `u`–`v` walk while
`u` lies on every `v`–`z` walk.  Adding the two geodesic splits gives
`2·d(u,z) ≤ 0`. -/
theorem not_onUVPath_both {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    {u v z : Fin n} (huz : u ≠ z) :
    ¬ (OnUVPath T u v z ∧ OnUVPath T v z u) := by
  rintro ⟨h1, h2⟩
  have k1 := dist_add_dist_le_of_onUVPath hT h1
  have k2 := dist_add_dist_le_of_onUVPath hT h2
  have c1 : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist z v
      = (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist v z := SimpleGraph.dist_comm
  have c2 : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist v u
      = (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist u v := SimpleGraph.dist_comm
  have hz : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).dist u z = 0 := by omega
  exact huz (((hT.2.2.preconnected u z).dist_eq_zero_iff).mp hz)

/-! ### Steps 2 and 3: the measure algebra -/

open Classical in
/-- **The two path masses sum to at most `1 − P[e, f ∈ T]`.**  Splitting each
on the other edge leaves the two conditioned path events, which step 2 makes
disjoint, plus the two mixed cells; the four cells then telescope. -/
theorem path_masses_le {w : Finset (Sym2 (Fin n)) → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Fin n} (huz : u ≠ z) (e f : Sym2 (Fin n)) :
    weightMass w (fun T => OnUVPath T u v z ∧ e ∉ T)
        + weightMass w (fun T => OnUVPath T v z u ∧ f ∉ T)
      ≤ 1 - weightMass w (fun T => e ∈ T ∧ f ∈ T) := by
  classical
  set X : Finset (Sym2 (Fin n)) → Prop :=
    fun T => OnUVPath T u v z ∧ e ∉ T ∧ f ∉ T with hX
  set Y : Finset (Sym2 (Fin n)) → Prop :=
    fun T => OnUVPath T v z u ∧ e ∉ T ∧ f ∉ T with hY
  -- split each path mass on the other edge
  have hsplit₁ : weightMass w (fun T => OnUVPath T u v z ∧ e ∉ T)
      ≤ weightMass w X + weightMass w (fun T => e ∉ T ∧ f ∈ T) := by
    have hmono : weightMass w (fun T => OnUVPath T u v z ∧ e ∉ T)
        ≤ weightMass w (fun T => X T ∨ (e ∉ T ∧ f ∈ T)) := by
      refine weightMass_mono hnn fun S hS => ?_
      by_cases hf : f ∈ S
      · exact Or.inr ⟨hS.2, hf⟩
      · exact Or.inl ⟨hS.1, hS.2, hf⟩
    have hor := weightMass_or w X (fun T => e ∉ T ∧ f ∈ T)
    have hand : 0 ≤ weightMass w (fun T => X T ∧ (e ∉ T ∧ f ∈ T)) :=
      weightMass_nonneg hnn _
    linarith
  have hsplit₂ : weightMass w (fun T => OnUVPath T v z u ∧ f ∉ T)
      ≤ weightMass w Y + weightMass w (fun T => e ∈ T ∧ f ∉ T) := by
    have hmono : weightMass w (fun T => OnUVPath T v z u ∧ f ∉ T)
        ≤ weightMass w (fun T => Y T ∨ (e ∈ T ∧ f ∉ T)) := by
      refine weightMass_mono hnn fun S hS => ?_
      by_cases he : e ∈ S
      · exact Or.inr ⟨he, hS.2⟩
      · exact Or.inl ⟨hS.1, he, hS.2⟩
    have hor := weightMass_or w Y (fun T => e ∈ T ∧ f ∉ T)
    have hand : 0 ≤ weightMass w (fun T => Y T ∧ (e ∈ T ∧ f ∉ T)) :=
      weightMass_nonneg hnn _
    linarith
  -- step 2: the two conditioned path events are disjoint on the support
  have hdisj : weightMass w (fun T => X T ∧ Y T) = 0 := by
    rw [weightMass_congr_of_support (B := fun _ => False) ?_, weightMass_false]
    intro S hS
    constructor
    · rintro ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
      exact absurd ⟨hx, hy⟩ (not_onUVPath_both (htree S hS) huz)
    · exact False.elim
  have hboth : weightMass w X + weightMass w Y
      ≤ weightMass w (fun T => e ∉ T ∧ f ∉ T) := by
    have hor := weightMass_or w X Y
    have hmono : weightMass w (fun T => X T ∨ Y T)
        ≤ weightMass w (fun T => e ∉ T ∧ f ∉ T) := by
      refine weightMass_mono hnn fun S hS => ?_
      rcases hS with h | h
      exacts [h.2, h.2]
    linarith
  -- the four cells telescope
  have hcell₁ : weightMass w (fun T => e ∉ T ∧ f ∉ T)
      = weightMass w (fun T => e ∉ T) - weightMass w (fun T => e ∉ T ∧ f ∈ T) :=
    weightMass_and_not w (fun T => e ∉ T) (fun T => f ∈ T)
  have hcell₂ : weightMass w (fun T => e ∈ T ∧ f ∉ T)
      = weightMass w (fun T => e ∈ T) - weightMass w (fun T => e ∈ T ∧ f ∈ T) :=
    weightMass_and_not w (fun T => e ∈ T) (fun T => f ∈ T)
  have hcompl : weightMass w (fun T => e ∉ T) = 1 - weightMass w (fun T => e ∈ T) := by
    rw [weightMass_not w (fun T => e ∈ T), htot]
  linarith

/-! ### The theorem -/

open Classical in
/-- **KKO22 Lemma 2.27.**  For adjacent edges `e = (u,v)`, `f = (v,z)` with
both marginals within `ε ≤ 1/1000` of `1/2`, conditioning on the absence of
one edge raises the punctured degree at the far end of the other by at most
`0.81` in total.

⚠️ `u`, `v`, `z` are pairwise distinct — the paper leaves this implicit. -/
theorem lemma_2_27 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Fin n} (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hme : |weightMass w (fun T => s(u, v) ∈ T) - 1 / 2| ≤ ε)
    (hmf : |weightMass w (fun T => s(v, z) ∈ T) - 1 / 2| ≤ ε) :
    expCard (deleteWeight w s(u, v)) (cutEdges {z} \ {s(v, z)})
        / totalMass (deleteWeight w s(u, v))
      + expCard (deleteWeight w s(v, z)) (cutEdges {u} \ {s(u, v)})
        / totalMass (deleteWeight w s(v, z))
      ≤ expCard w (cutEdges {z} \ {s(v, z)})
        + expCard w (cutEdges {u} \ {s(u, v)}) + 0.81 := by
  classical
  -- marginals
  have hpe := abs_le.mp hme
  have hpf := abs_le.mp hmf
  have hpeU : weightMass w (fun T => s(u, v) ∈ T) ≤ 1 / 2 + ε := by linarith [hpe.2]
  have hpeL : 1 / 2 - ε ≤ weightMass w (fun T => s(u, v) ∈ T) := by linarith [hpe.1]
  have hpfU : weightMass w (fun T => s(v, z) ∈ T) ≤ 1 / 2 + ε := by linarith [hpf.2]
  have hpfL : 1 / 2 - ε ≤ weightMass w (fun T => s(v, z) ∈ T) := by linarith [hpf.1]
  have hpe0 : 0 ≤ weightMass w (fun T => s(u, v) ∈ T) := weightMass_nonneg hnn _
  have hpf0 : 0 ≤ weightMass w (fun T => s(v, z) ∈ T) := weightMass_nonneg hnn _
  -- the two avoidance masses
  have hme_eq : totalMass (deleteWeight w s(u, v))
      = 1 - weightMass w (fun T => s(u, v) ∈ T) := by
    rw [totalMass_deleteWeight, weightMass_not w (fun T => s(u, v) ∈ T), htot]
  have hmf_eq : totalMass (deleteWeight w s(v, z))
      = 1 - weightMass w (fun T => s(v, z) ∈ T) := by
    rw [totalMass_deleteWeight, weightMass_not w (fun T => s(v, z) ∈ T), htot]
  have hmepos : 0 < totalMass (deleteWeight w s(u, v)) := by rw [hme_eq]; linarith [hpe.2]
  have hmfpos : 0 < totalMass (deleteWeight w s(v, z)) := by rw [hmf_eq]; linarith [hpf.2]
  have hmein : totalMass (contractWeight w s(u, v)) = weightMass w (fun T => s(u, v) ∈ T) :=
    totalMass_contractWeight w _
  have hmfin : totalMass (contractWeight w s(v, z)) = weightMass w (fun T => s(v, z) ∈ T) :=
    totalMass_contractWeight w _
  -- the path masses
  have hPz_eq : weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v z)
      = weightMass w (fun T => OnUVPath T u v z ∧ s(u, v) ∉ T) :=
    weightMass_delete_eq w _ _
  have hPu_eq : weightMass (deleteWeight w s(v, z)) (fun T => OnUVPath T v z u)
      = weightMass w (fun T => OnUVPath T v z u ∧ s(v, z) ∉ T) :=
    weightMass_delete_eq w _ _
  have hPz0 : 0 ≤ weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v z) :=
    weightMass_nonneg (hnn.delete _) _
  have hPu0 : 0 ≤ weightMass (deleteWeight w s(v, z)) (fun T => OnUVPath T v z u) :=
    weightMass_nonneg (hnn.delete _) _
  have hPzm : weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v z)
      ≤ totalMass (deleteWeight w s(u, v)) := weightMass_le_totalMass (hnn.delete _) _
  have hPum : weightMass (deleteWeight w s(v, z)) (fun T => OnUVPath T v z u)
      ≤ totalMass (deleteWeight w s(v, z)) := weightMass_le_totalMass (hnn.delete _) _
  -- the conditional marginals of the other edge
  have haf_eq : weightMass (deleteWeight w s(u, v)) (fun T => s(v, z) ∈ T)
      = weightMass w (fun T => s(v, z) ∈ T ∧ s(u, v) ∉ T) := weightMass_delete_eq w _ _
  have hbe_eq : weightMass (deleteWeight w s(v, z)) (fun T => s(u, v) ∈ T)
      = weightMass w (fun T => s(u, v) ∈ T ∧ s(v, z) ∉ T) := weightMass_delete_eq w _ _
  -- Lemma 2.26 at the punctured degrees
  have hWsub : (cutEdges {z} \ {s(v, z)} : Finset (Sym2 (Fin n))) ⊆ cutEdges {z} :=
    Finset.sdiff_subset
  have hUsub : (cutEdges {u} \ {s(u, v)} : Finset (Sym2 (Fin n))) ⊆ cutEdges {u} :=
    Finset.sdiff_subset
  have hstepW := expCard_delete_le_cut_conditional hst hr hnn htot htree hWsub
    (Ne.symm huz) (Ne.symm hvz) hmepos
  have hstepU := expCard_delete_le_cut_conditional hst hr hnn htot htree hUsub
    huv huz hmfpos
  rw [hmein] at hstepW
  rw [hmfin] at hstepU
  -- the two branches
  by_cases hbranch :
      weightMass (deleteWeight w s(u, v)) (fun T => s(v, z) ∈ T)
          / totalMass (deleteWeight w s(u, v)) ≤ 0.6
        ∨ weightMass (deleteWeight w s(v, z)) (fun T => s(u, v) ∈ T)
          / totalMass (deleteWeight w s(v, z)) ≤ 0.6
  · -- branch 1: the joint mass is large
    have hpath := path_masses_le (v := v) hnn htot htree huz s(u, v) s(v, z)
    have hslackW : weightMass w (fun T => s(u, v) ∈ T)
        * (weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v z)
            / totalMass (deleteWeight w s(u, v)))
        ≤ weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v z) + 2 * ε :=
      cond_path_bound hPz0 hPzm hmepos (by linarith [hme_eq]) (by linarith [hpe.2]) hε0
    have hslackU : weightMass w (fun T => s(v, z) ∈ T)
        * (weightMass (deleteWeight w s(v, z)) (fun T => OnUVPath T v z u)
            / totalMass (deleteWeight w s(v, z)))
        ≤ weightMass (deleteWeight w s(v, z)) (fun T => OnUVPath T v z u) + 2 * ε :=
      cond_path_bound hPu0 hPum hmfpos (by linarith [hmf_eq]) (by linarith [hpf.2]) hε0
    have hjoint : 0.198 ≤ weightMass w (fun T => s(u, v) ∈ T ∧ s(v, z) ∈ T) := by
      rcases hbranch with hb | hb
      · have hcell : weightMass w (fun T => s(v, z) ∈ T ∧ s(u, v) ∉ T)
            = weightMass w (fun T => s(v, z) ∈ T)
              - weightMass w (fun T => s(v, z) ∈ T ∧ s(u, v) ∈ T) :=
          weightMass_and_not w (fun T => s(v, z) ∈ T) (fun T => s(u, v) ∈ T)
        have hcomm : weightMass w (fun T => s(v, z) ∈ T ∧ s(u, v) ∈ T)
            = weightMass w (fun T => s(u, v) ∈ T ∧ s(v, z) ∈ T) :=
          weightMass_congr fun _ => and_comm
        rw [haf_eq] at hb
        have := joint_ge_of_cond_le (pF := weightMass w (fun T => s(v, z) ∈ T))
          (mOut := totalMass (deleteWeight w s(u, v)))
          (aF := weightMass w (fun T => s(v, z) ∈ T ∧ s(u, v) ∉ T))
          hpfL (by linarith [hme_eq, hpe.1]) hmepos hb hε
        linarith
      · have hcell : weightMass w (fun T => s(u, v) ∈ T ∧ s(v, z) ∉ T)
            = weightMass w (fun T => s(u, v) ∈ T)
              - weightMass w (fun T => s(u, v) ∈ T ∧ s(v, z) ∈ T) :=
          weightMass_and_not w (fun T => s(u, v) ∈ T) (fun T => s(v, z) ∈ T)
        rw [hbe_eq] at hb
        have := joint_ge_of_cond_le (pF := weightMass w (fun T => s(u, v) ∈ T))
          (mOut := totalMass (deleteWeight w s(v, z)))
          (aF := weightMass w (fun T => s(u, v) ∈ T ∧ s(v, z) ∉ T))
          hpeL (by linarith [hmf_eq, hpf.1]) hmfpos hb hε
        linarith
    linarith [hPz_eq, hPu_eq]
  · -- branch 2: both conditional marginals exceed 0.6
    obtain ⟨hα, hβ⟩ := not_or.mp hbranch
    rw [not_le] at hα hβ
    have hsideW : expCard (deleteWeight w s(u, v)) (cutEdges {z} \ {s(v, z)})
        / totalMass (deleteWeight w s(u, v))
          ≤ expCard w (cutEdges {z} \ {s(v, z)}) + 0.405 := by
      have hfsub : ({s(v, z)} : Finset (Sym2 (Fin n))) ⊆ cutEdges {z} :=
        Finset.singleton_subset_iff.mpr (mem_cutEdges_right hvz)
      have hfull := expCard_delete_le_cut_conditional hst hr hnn htot htree
        (D := cutEdges {z}) (Finset.Subset.refl _) (Ne.symm huz) (Ne.symm hvz) hmepos
      rw [hmein] at hfull
      have hratio : weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v z)
          / totalMass (deleteWeight w s(u, v)) ≤ 1 :=
        (div_le_one hmepos).mpr hPzm
      have hfull' : expCard (deleteWeight w s(u, v)) (cutEdges {z})
          / totalMass (deleteWeight w s(u, v))
            ≤ expCard w (cutEdges {z}) + weightMass w (fun T => s(u, v) ∈ T) := by
        nlinarith [hfull, hratio, hpe0]
      have hsd := expCard_sdiff_of_subset (deleteWeight w s(u, v)) hfsub
      have hsd' := expCard_sdiff_of_subset w hfsub
      rw [expCard_singleton] at hsd hsd'
      have hdiv : expCard (deleteWeight w s(u, v)) (cutEdges {z} \ {s(v, z)})
          / totalMass (deleteWeight w s(u, v))
            = expCard (deleteWeight w s(u, v)) (cutEdges {z})
                / totalMass (deleteWeight w s(u, v))
              - weightMass (deleteWeight w s(u, v)) (fun T => s(v, z) ∈ T)
                / totalMass (deleteWeight w s(u, v)) := by
        rw [hsd, sub_div]
      have hnum := side_bound_of_cond_gt (pE := weightMass w (fun T => s(u, v) ∈ T))
        (pF := weightMass w (fun T => s(v, z) ∈ T))
        (aF := weightMass (deleteWeight w s(u, v)) (fun T => s(v, z) ∈ T))
        (mOut := totalMass (deleteWeight w s(u, v))) hpeU hpfU (le_of_lt hα) hε
      rw [hdiv, hsd']
      linarith
    have hsideU : expCard (deleteWeight w s(v, z)) (cutEdges {u} \ {s(u, v)})
        / totalMass (deleteWeight w s(v, z))
          ≤ expCard w (cutEdges {u} \ {s(u, v)}) + 0.405 := by
      have hesub : ({s(u, v)} : Finset (Sym2 (Fin n))) ⊆ cutEdges {u} :=
        Finset.singleton_subset_iff.mpr (mem_cutEdges_left huv)
      have hfull := expCard_delete_le_cut_conditional hst hr hnn htot htree
        (D := cutEdges {u}) (Finset.Subset.refl _) huv huz hmfpos
      rw [hmfin] at hfull
      have hratio : weightMass (deleteWeight w s(v, z)) (fun T => OnUVPath T v z u)
          / totalMass (deleteWeight w s(v, z)) ≤ 1 :=
        (div_le_one hmfpos).mpr hPum
      have hfull' : expCard (deleteWeight w s(v, z)) (cutEdges {u})
          / totalMass (deleteWeight w s(v, z))
            ≤ expCard w (cutEdges {u}) + weightMass w (fun T => s(v, z) ∈ T) := by
        nlinarith [hfull, hratio, hpf0]
      have hsd := expCard_sdiff_of_subset (deleteWeight w s(v, z)) hesub
      have hsd' := expCard_sdiff_of_subset w hesub
      rw [expCard_singleton] at hsd hsd'
      have hdiv : expCard (deleteWeight w s(v, z)) (cutEdges {u} \ {s(u, v)})
          / totalMass (deleteWeight w s(v, z))
            = expCard (deleteWeight w s(v, z)) (cutEdges {u})
                / totalMass (deleteWeight w s(v, z))
              - weightMass (deleteWeight w s(v, z)) (fun T => s(u, v) ∈ T)
                / totalMass (deleteWeight w s(v, z)) := by
        rw [hsd, sub_div]
      have hnum := side_bound_of_cond_gt (pE := weightMass w (fun T => s(v, z) ∈ T))
        (pF := weightMass w (fun T => s(u, v) ∈ T))
        (aF := weightMass (deleteWeight w s(v, z)) (fun T => s(u, v) ∈ T))
        (mOut := totalMass (deleteWeight w s(v, z))) hpfU hpeU (le_of_lt hβ) hε
      rw [hdiv, hsd']
      linarith
    linarith

end TSPGap

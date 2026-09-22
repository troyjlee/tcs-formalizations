/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RandomJoinTour
import TSPGap.MaxEntropyExistence
import TSPGap.Theorem61
import TSPGap.Split
import TSPGap.Statement

/-!
# KKO22 §6.2 assembled: a tour of cost `(3/2 − ε) c(x)`

The end-to-end chain is axiom-clean: max-entropy existence, Edmonds–Johnson,
the root-edge reduction, the slack pair, Euler's theorem and shortcutting
are all proved.

1. the slack pair gives the O-join vector `y`, which is feasible
   (`ojoinFeasible_of_slack`) and costs `(1/2 − 0.187 ε_P β) c(x)` in expectation;
2. the probabilistic method picks a tree `T` of the support at most as
   expensive as average (`TreeDist.exists_le_expect`);
3. Edmonds–Johnson turns `y` into an actual join `J` of no greater cost, whose
   degrees make `T ⊎ J` even;
4. Euler's theorem gives a closed walk through every vertex of cost
   `c(T) + c(J)`, and `Tour.lean` shortcuts it to a Hamiltonian cycle without
   raising the cost.

**The constants.**  Theorem B.3 now costs `125ηβxₑ`, using the restored
`44αη` Appendix A bound. The final mixture in `exists_slack_pair_capacity` saves
`0.374 ε_P βxₑ`. We spend half that saving on the repair:
`125 η = 0.187 ε_P`, so `η = 0.374 ε_P / 250`.

The capacity-based probability threshold is `p = 0.02ε₂² = 8·10⁻¹⁰`.
The stronger payment export supplies `epsPCapacity = 500 epsP = 1.25·10⁻¹⁵`;
the foundational `epsP` and its compatibility theorems retain their old value.

The gain is `0.187 epsPCapacity β`, with `β = η/(4 + 2η)`, approximately
`1.09278125·10⁻³⁴`. The stated `kkoEps = 1.08·10⁻³⁴` is checked below by
exact rational arithmetic. This combines the separate improvements to the
Appendix A repair coefficient and the Lemma 5.22 probability threshold.
-/

namespace TSPGap

open Finset

variable {n : ℕ}


/-! ### The constants of equation (9) -/

/-- Spend half the sharpened mixture saving on the restored Appendix A cost:
`125 η = 0.187 ε_P`. -/
noncomputable def kkoEta : ℝ := 0.374 * epsPCapacity / 250

/-- KKO22's `β`, at `η/(4 + 2η)`, saturating the O-join feasibility bound. -/
noncomputable def kkoBeta : ℝ := kkoEta / (4 + 2 * kkoEta)

theorem kkoEta_pos : 0 < kkoEta := by
  unfold kkoEta epsPCapacity epsPRecovered epsP; norm_num

theorem kkoEta_le : kkoEta ≤ 1e-12 := by
  unfold kkoEta epsPCapacity epsPRecovered epsP; norm_num

theorem kkoBeta_pos : 0 < kkoBeta := by
  unfold kkoBeta kkoEta epsPCapacity epsPRecovered epsP; norm_num

/-- At KKO's `β` this is an equality, not merely an inequality. -/
theorem kkoBeta_mul_le : kkoBeta * (4 + 2 * kkoEta) ≤ kkoEta := by
  have h : (0:ℝ) < 4 + 2 * kkoEta := by have := kkoEta_pos; linarith
  rw [kkoBeta, div_mul_cancel₀ _ (ne_of_gt h)]

/-- Equation (9) itself, at this development's constant: the loss from `s*` is
half the gain from `s`. -/
theorem kko_eq_nine : 125 * kkoEta = 0.187 * epsPCapacity := by
  unfold kkoEta epsPCapacity epsPRecovered epsP; norm_num

/-- The gain clears the constant claimed in `kko_gap`. -/
theorem kkoEps_le_gain : kkoEps ≤ 0.187 * epsPCapacity * kkoBeta := by
  unfold kkoEps kkoBeta kkoEta epsPCapacity epsPRecovered epsP; norm_num

/-! ### The tour, for an instance carrying a zero-cost unit edge -/

/-- **KKO22 Theorem 1.1 for a rooted instance.**  If the LP point has an edge
`e₀` of value one and cost zero — KKO's standing assumption, obtained by
splitting a vertex — then there is a Hamiltonian cycle of cost at most
`(3/2 − ε) c(x₀)`.

The proof is KKO's §6.2, using the proved max-entropy distribution and
Edmonds–Johnson theorem, with `Tour.lean` supplying the shortcutting. -/
theorem exists_tour_of_rootEdge (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) (hce₀ : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - kkoEps) * lpCost c x₀ := by
  classical
  have hcnn : ∀ e, 0 ≤ c e := hc.nonneg
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  -- the max-entropy distribution and the slack pair
  obtain ⟨μ, hμ⟩ := exists_maxEntropy_treeDist hx₀ e₀ hx₀e
  obtain ⟨s, s', hs, hs', hsat, hs'exp, hsexp⟩ :=
    exists_slack_pair_capacity (η := kkoEta) (β := kkoBeta) e₀ hx₀ hx₀e (by omega) hμ
      kkoEta_pos kkoEta_le kkoBeta_pos
  -- the cost of the LP point, over the restricted vector
  have hcx : ∑ e ∈ edgeFinset n, c e * e₀.restrict x₀ e = lpCost c x₀ := by
    rw [lpCost]
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases eq_or_ne e e₀.edge with rfl | hne
    · rw [hce₀]; ring
    · rw [RootEdge.restrict, Function.update_of_ne hne]
  have hCnn : 0 ≤ lpCost c x₀ := by
    rw [← hcx]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hcnn e) (hxnn e)
  -- the random cost: the tree plus the O-join vector
  set g : Finset (Sym2 (Fin n)) → ℝ := fun T =>
    (∑ e ∈ T, c e) + ∑ e ∈ edgeFinset n, c e * ojoinVec e₀ x₀ (s T) (s' T) e
    with hgdef
  -- its expectation is below `(3/2 − 0.187 ε_P β) c(x)`
  have hyrewrite : ∀ T : Finset (Sym2 (Fin n)),
      ∑ e ∈ edgeFinset n, c e * ojoinVec e₀ x₀ (s T) (s' T) e
        = ∑ e ∈ edgeFinset n,
            c e * (e₀.restrict x₀ e / 2 + s T e + s' T e) := by
    intro T
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases eq_or_ne e e₀.edge with rfl | hne
    · rw [hce₀]; ring
    · rw [ojoinVec, if_neg hne]
  have hexp : μ.expect g
      = lpCost c x₀ + ∑ e ∈ edgeFinset n,
          (c e * (e₀.restrict x₀ e / 2)
            + c e * μ.expect (fun T => s T e)
            + c e * μ.expect (fun T => s' T e)) := by
    rw [hgdef]
    simp only [hyrewrite]
    rw [TreeDist.expect_add, μ.expect_sum_eq c, hcx, TreeDist.expect_sum]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    have : ∀ T : Finset (Sym2 (Fin n)),
        c e * (e₀.restrict x₀ e / 2 + s T e + s' T e)
          = c e * (e₀.restrict x₀ e / 2) + (c e * s T e + c e * s' T e) := by
      intro T; ring
    simp only [this]
    rw [TreeDist.expect_add, TreeDist.expect_const, TreeDist.expect_add,
      TreeDist.expect_mul_left, TreeDist.expect_mul_left]
    ring
  have hbound : μ.expect g ≤ (3 / 2 - 0.187 * epsPCapacity * kkoBeta) * lpCost c x₀ := by
    rw [hexp]
    have hterm : ∀ e ∈ edgeFinset n,
        c e * (e₀.restrict x₀ e / 2) + c e * μ.expect (fun T => s T e)
            + c e * μ.expect (fun T => s' T e)
          ≤ c e * ((1 / 2 - 0.187 * epsPCapacity * kkoBeta) * e₀.restrict x₀ e) := by
      intro e _
      have h1 := hsexp e
      have h2 := hs'exp e
      have h3 := hcnn e
      have h4 := hxnn e
      have hrw : 125 * kkoEta * kkoBeta * e₀.restrict x₀ e
          = 0.187 * epsPCapacity * kkoBeta * e₀.restrict x₀ e := by
        rw [show (125 : ℝ) * kkoEta * kkoBeta * e₀.restrict x₀ e
            = (125 * kkoEta) * (kkoBeta * e₀.restrict x₀ e) by ring, kko_eq_nine]
        ring
      have h2' : (μ.expect fun T => s' T e)
          ≤ 0.187 * epsPCapacity * kkoBeta * e₀.restrict x₀ e := h2.trans (le_of_eq hrw)
      nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2' h3]
    have hsum := Finset.sum_le_sum hterm
    have hlin : ∑ e ∈ edgeFinset n,
        c e * ((1 / 2 - 0.187 * epsPCapacity * kkoBeta) * e₀.restrict x₀ e)
          = (1 / 2 - 0.187 * epsPCapacity * kkoBeta) * lpCost c x₀ := by
      rw [← hcx, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [hlin] at hsum
    linarith
  -- The same generic random-join argument is used by the layered Song endpoint.
  have hfeas : ∀ T, μ.prob T ≠ 0 →
      OJoinFeasible (oddVerts T) (ojoinVec e₀ x₀ (s T) (s' T)) := by
    intro T hTprob
    exact ojoinFeasible_of_slack e₀ hx₀ (μ.support_spanningTree T hTprob).1
      kkoEta_pos (by have := kkoEta_le; linarith) kkoBeta_pos.le kkoBeta_mul_le
      (fun e => hs T e) (fun e => hs' T e)
      (fun S hS hodd => hsat S T hTprob hS hodd)
  apply exists_tour_of_random_join hn hc μ (fun T => ojoinVec e₀ x₀ (s T) (s' T)) hfeas
  change μ.expect g ≤ (3 / 2 - kkoEps) * lpCost c x₀
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left kkoEps_le_gain _) hCnn

/-! ### The root-edge reduction

KKO's §2.1 "without loss of generality" — split an arbitrary vertex into two
copies joined by a zero-cost edge of LP value one — is carried out in
`TSPGap/Split.lean`, and `gap_of_rooted_gap` there turns the rooted form of
the theorem into the general one. -/

/-- **KKO22 Theorem 1.1** (existential form).  Every metric TSP instance has a
tour of cost at most `(3/2 − ε)` times the cost of any subtour-LP-feasible
point; in particular the integrality gap of the subtour LP is below `3/2`.

The statement is the one `Statement.lean` declares; the proof is the chain of
this file, and its axiom report is clean since 2026-09-10 (`propext`,
`Classical.choice`, `Quot.sound`): the last box on its path, Edmonds–Johnson, is proved
in `EdmondsJoin.lean`. All formerly admitted statements are now proved or retired. -/
theorem kko_gap {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - kkoEps) * lpCost c x :=
  gap_of_rooted_gap
    (fun _ hm _ hc' _ hx' e₀ he₀ hce₀ =>
      exists_tour_of_rootEdge hm hc' hx' e₀ he₀ hce₀)
    hn hc hx

end TSPGap

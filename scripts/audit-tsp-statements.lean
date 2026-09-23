import TSPGap.SongEndToEnd
import TSPGap.EndToEnd
import TSPGap.AxiomCheck
import Lean.Util.FoldConsts

/- Supplementary paper-correspondence checks. Run with:
   lake env lean scripts/audit-tsp-statements.lean
   This file does not change the production theorem interfaces. -/

namespace TSPGap.PaperAudit
open Finset
variable {n : ℕ}

/-- The printed KKO21 Lemma A.1 tail threshold is 5 epsilon. -/
theorem paper_lemma_A1_indexed {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    (hcount : M.TwoAtomCrossData w u v)
    {E A B C : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v)))
    (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : 5 * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  have h := lemma_A1_indexed_budget M hst hr hnn htot hune hvne huv huvp hcount hSC
    hpart hAB hAC hBC hεη hε0 hεcap (ℓ := 4.75) (by norm_num) (by norm_num)
    hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE hdv1 hdv2 hgood
    (by convert htail using 1; norm_num)
  calc 0.005 * ε ^ 2 ≤ 0.00119 * 4.75 * ε ^ 2 := by nlinarith [sq_nonneg ε]
    _ ≤ _ := h


/-- Base-edge version at the paper tail threshold, retaining the existing structural hypotheses. -/
theorem paper_lemma_A1 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    {E A B C : Finset (Sym2 (Fin n))} (hSC : SupportComplete w E u v)
    (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (cutEdges v)) (hdv2 : expCard w (cutEdges v) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau w u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (htail : 5 * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (cutEdges v \ E)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcount : (FiberTreeModel.id n).TwoAtomCrossData w u v :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hune hvne huv huvp
  have h := paper_lemma_A1_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne huv huvp hcount
    (E := E) (A := A) (B := B) (C := C) (FiberTreeModel.supportComplete_id hSC)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε0 hεcap hεηsq
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef) hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE
    (by rw [FiberTreeModel.id_fiberOver]; exact hdv1) (by rw [FiberTreeModel.id_fiberOver]; exact hdv2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgood)
    (by simpa only [FiberTreeModel.id_fiberOver] using htail)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h


/-- Retain the exact finite saving in Song's Lemma 26 through the tour conversion. -/
theorem song_exact_rooted {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) (hce₀ : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤
        (3 / 2 - ThresholdSlack.totalGain Song.H Song.layers Song.kappa) * lpCost c x₀ := by
  obtain ⟨μ, hμ⟩ := exists_maxEntropy_treeDist hx₀ e₀ hx₀e
  obtain ⟨Z, hZ⟩ := Song.exists_thresholdLayers e₀ hx₀ hx₀e (by omega) hμ
  obtain ⟨hlower, hcut, _⟩ :=
    Song.layered_slack_of_certificates (restrict_isRestrictedLP hx₀) Z hZ
  exact exists_tour_of_all_cut_slack hn hc e₀ hce₀ (RootEdge.restrict_nonneg hx₀.1)
    μ (ThresholdSlack.combined Z Song.layers)
    (show ThresholdSlack.beta Song.H ≤ 1 / 2 by norm_num [ThresholdSlack.beta, Song.H])
    hlower hcut (ThresholdSlack.combined_expect hZ)

/-- Song's strict integrality-gap conclusion follows without new probability assumptions. -/
theorem song_strict :
    ∃ ε : ℝ, 2.05522e-30 < ε ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ (c : Sym2 (Fin n) → ℝ), IsMetric c →
        ∀ (x : Sym2 (Fin n) → ℝ), x ∈ subtourLP n →
          ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
            w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - ε) * lpCost c x := by
  refine ⟨ThresholdSlack.totalGain Song.H Song.layers Song.kappa,
    Song.totalGain_gt_target, ?_⟩
  intro n hn c hc x hx
  exact gap_of_rooted_gap
    (fun _ hm _ hc' _ hx' e₀ he₀ hce₀ => song_exact_rooted hm hc' hx' e₀ he₀ hce₀)
    hn hc hx

/-- Additional decimal check of the actual rational reserve. -/
example : (2.0552253e-30 : ℝ) < Song.lowerBound Song.layers := by
  have := Song.final_arithmetic
  norm_num [Song.targetGap] at this ⊢
  exact this

/-- Expected KKO22 Theorem 6.1 coefficients from the recovered producer. -/
theorem paper_slack_pair {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    {η β : ℝ} (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : TreeSlack n,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ -(3.12e-16 * β * e₀.restrict x₀ e / 3)) := by
  obtain ⟨s, s', hlower, hnonneg, hpay, hcost, hgain⟩ :=
    exists_slack_pair_recovered e₀ hx₀ hx₀e hn hμ hη0 hη hβ0
  refine ⟨s, s', hlower, hnonneg, hpay, hcost, ?_⟩
  intro e
  have hnn := mul_nonneg hβ0.le (RootEdge.restrict_nonneg (e₀ := e₀) hx₀.1 e)
  have h := hgain e
  rw [epsPRecovered_eq] at h
  nlinarith only [h, hnn]

/-- Check the exported result against a decimal constant and explicit tour length. -/
example {n : ℕ} (hn : 3 ≤ n) {c x : Sym2 (Fin n) → ℝ}
    (hc : IsMetric c) (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ w.length = n ∧
        (w.edges.map c).sum ≤ (3 / 2 - (205522 : ℝ) / 10 ^ 35) *
          ∑ e ∈ Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag), c e * x e := by
  obtain ⟨v, w, hw, hcost⟩ := song_gap hn hc hx
  refine ⟨v, w, hw, by simpa using hw.length_eq, ?_⟩
  have hgap : Song.targetGap = (205522 : ℝ) / 10 ^ 35 := by
    norm_num [Song.targetGap]
  simpa only [tourCost, lpCost, edgeFinset, hgap] using hcost

/-- Nonvacuity at n = 3, including harmless nonzero diagonal coordinates. -/
theorem triangle_feasible : (fun _ : Sym2 (Fin 3) => (1 : ℝ)) ∈ subtourLP 3 := by
  classical
  refine ⟨fun _ => by norm_num, ?_, ?_⟩
  · intro v
    fin_cases v <;> norm_num [cutSum] <;> norm_cast
  · intro S hS hSu
    fin_cases S
    all_goals first
      | exact False.elim (hS.ne_empty (by decide))
      | exact False.elim (hSu (by decide))
      | (norm_num [cutSum]; norm_cast)

example : IsMetric (fun _ : Sym2 (Fin 3) => (1 : ℝ)) :=
  ⟨fun _ => by norm_num, fun _ _ _ => by norm_num⟩

example : lpCost (fun _ : Sym2 (Fin 3) => (1 : ℝ)) (fun _ => 1) = 3 := by
  norm_num [lpCost]
  norm_cast

example : IsMetric (fun _ : Sym2 (Fin 3) => (0 : ℝ)) :=
  ⟨fun _ => le_rfl, fun _ _ _ => by norm_num⟩

end TSPGap.PaperAudit

#print axioms TSPGap.song_gap
#print axioms TSPGap.kko_gap
#print axioms TSPGap.PaperAudit.paper_lemma_A1
#print axioms TSPGap.PaperAudit.paper_slack_pair
#print axioms TSPGap.PaperAudit.song_strict

#check_tsp_axioms TSPGap.PaperAudit.paper_lemma_A1
#check_tsp_axioms TSPGap.PaperAudit.paper_slack_pair
#check_tsp_axioms TSPGap.PaperAudit.song_strict
#check_tsp_axioms TSPGap.PaperAudit.triangle_feasible

open Lean Elab Command in
elab "#paper_dependency_check" : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := #[``TSPGap.song_gap]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing declaration {name}"
    for dep in info.getUsedConstantsAsSet do
      if (dep.toString.splitOn "TSPGap").length > 1 && !seen.contains dep then
        pending := pending.push dep
  for name in #[``TSPGap.Song.window_happy_indexed,
      ``TSPGap.Song.window_reused_kernel,
      ``TSPGap.three_counts_ge_of_mean_profile,
      ``TSPGap.Song.exists_payment_with_repairs,
      ``TSPGap.gap_of_rooted_gap] do
    unless seen.contains name do throwError "Expected dependency absent: {name}"
    logInfo m!"Verified dependency: {name}"
  for name in #[`TSPGap.Song.window_kernel, `TSPGap.Song.WindowTails,
      `TSPGap.Song.window_product_margin] do
    if seen.contains name then throwError "Unexpected old window route: {name}"
    logInfo m!"Not a dependency: {name}"

#paper_dependency_check

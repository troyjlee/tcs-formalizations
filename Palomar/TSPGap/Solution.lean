/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.EndToEnd
import TSPGap.SongEndToEnd

/-!
# Metric subtour-LP gaps: Palomar proof adapter

Costs are on unordered pairs. Only off-diagonal edges enter the LP objective;
every nonempty proper vertex cut has capacity at least two. The conclusions
assert existence of Hamiltonian tours, without a running-time guarantee.
All decimals denote exact rationals in `ℝ`. Song's final parameters come from
Definitions 2–3, not the preliminary Definition 1. See `Palomar/README.md`.
-/

namespace PalomarTSPGap

open Finset

/-- Unordered, off-diagonal edges of the complete graph. -/
def edgeFinset (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬e.IsDiag

/-- Unordered edges crossing the vertex cut. -/
def cutEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ∃ u ∈ S, ∃ v ∈ Sᶜ, e = s(u, v)

/-- Capacity of a vertex cut. -/
noncomputable def cutSum {n : ℕ} (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ cutEdges S, x e

/-- Nonnegative edge weights, degree two, and all subtour-cut constraints. -/
def subtourLP (n : ℕ) : Set (Sym2 (Fin n) → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : Fin n, cutSum x {v} = 2) ∧
    ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → 2 ≤ cutSum x S}

/-- Nonnegative symmetric costs satisfying the triangle inequality; symmetry is built into `Sym2`. -/
def IsMetric {n : ℕ} (c : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e, 0 ≤ c e) ∧ ∀ u v w : Fin n, c s(u, w) ≤ c s(u, v) + c s(v, w)

/-- The subtour-LP objective, counting each unordered edge once. -/
noncomputable def lpCost {n : ℕ} (c x : Sym2 (Fin n) → ℝ) : ℝ :=
  ∑ e ∈ edgeFinset n, c e * x e

/-- The cost of the edges traversed by a closed walk. -/
noncomputable def tourCost {n : ℕ} (c : Sym2 (Fin n) → ℝ) {v : Fin n}
    (w : (⊤ : SimpleGraph (Fin n)).Walk v v) : ℝ := (w.edges.map c).sum

/-- Song's final base parameter. -/
noncomputable def h : ℝ := 0.0002642163447
/-- Song's radius parameter. -/
noncomputable def r : ℝ := h / 4
/-- Song's final window-probability parameter. -/
noncomputable def p : ℝ := 1.9555663e-9
/-- Song's final saving factor. -/
noncomputable def zeta : ℝ := 0.49307672
/-- Song's final mixture parameter. -/
noncomputable def t : ℝ := 0.57113594779
/-- Song's good-edge loss coefficient. -/
noncomputable def kGood : ℝ := 10.3659382
/-- The maximum layered threshold. -/
noncomputable def H : ℝ := 9.06e-16
/-- The finite number of threshold layers. -/
def layers : ℕ := 1000000
/-- The saving before good-edge loss. -/
noncomputable def a : ℝ := zeta * r * p * t
/-- Retained good-edge mass. -/
noncomputable def g₀ : ℝ := 1 - (kGood + 1) * h
/-- The layer's pre-repair saving. -/
noncomputable def pi (u : ℝ) : ℝ := a * g₀ / (2 + u - a * (2 + u - g₀))
/-- The layer's repair coefficient. -/
noncomputable def repair (u : ℝ) : ℝ := 10 * (2 + u) / (1 - u)
/-- The net saving at a threshold. -/
noncomputable def kappa (u : ℝ) : ℝ := pi u - repair u * u
/-- Threshold-to-weight conversion. -/
noncomputable def beta (u : ℝ) : ℝ := u / (4 + 2 * u)
/-- Equally spaced threshold levels. -/
noncomputable def level (i : ℕ) : ℝ := (i : ℝ) * H / layers
/-- Exact finite-layer saving, uniform over all instances. -/
noncomputable def exactGain : ℝ :=
  ∑ i ∈ Finset.range layers, kappa (level (i + 1)) * (beta (level (i + 1)) - beta (level i))

/-- KKO22's tour-existence conclusion with the improved saving supplied by GKL capacity estimates. -/
theorem kko_gap {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - 1.08e-34) * lpCost c x := by
  exact TSPGap.kko_gap hn ⟨hc.1, hc.2⟩ hx

/-- Song's rounded tour-existence bound. -/
theorem song_gap {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - 2.05522e-30) * lpCost c x := by
  exact TSPGap.song_gap hn ⟨hc.1, hc.2⟩ hx

/-- One saving strictly greater than the rounded target works for every instance. -/
theorem song_gap_strict :
    ∃ ε : ℝ, 2.05522e-30 < ε ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ c : Sym2 (Fin n) → ℝ, IsMetric c →
      ∀ x : Sym2 (Fin n) → ℝ, x ∈ subtourLP n →
        ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
          w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - ε) * lpCost c x := by
  obtain ⟨ε, hε, hgap⟩ := TSPGap.song_gap_strict
  exact ⟨ε, hε, fun n hn c hc x hx => hgap n hn c ⟨hc.1, hc.2⟩ x hx⟩

/-- The exact finite-layer saving, with no additional certificate hypothesis. -/
theorem song_gap_exact {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - exactGain) * lpCost c x := by
  exact TSPGap.song_gap_exact hn ⟨hc.1, hc.2⟩ hx

/-- The exact finite sum certifies the strict numerical improvement. -/
theorem exactGain_gt_target : 2.05522e-30 < exactGain := by
  exact TSPGap.Song.totalGain_gt_target

end PalomarTSPGap

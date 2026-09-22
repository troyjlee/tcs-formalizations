/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SharpPolygonProbability

/-!
# Reading the sharp polygon probabilities in the payment coordinates

The topology is unchanged: this module only identifies finite-index
near-cycle intervals with the rooted polygon's natural-number intervals.
-/

namespace TSPGap.PolygonRep

open Finset NearCycle

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η ε : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}
variable (P : PolygonRep 𝒞) (R : P.Rooted)

/-- The canonical near-cycle reads each atom at its offset from the root. -/
theorem toNearCycle_atom_eq_ivl {k : ℕ} (hk : P.m = k + 3)
    (y : Sym2 (Fin n) → ℝ) (ε : ℝ) (hadj hdeg hmid) (i : Fin (k + 3)) :
    (P.toNearCycle hk R.r y ε R.cover hadj hdeg hmid).atom i = P.ivl R i.val i.val := by
  rw [P.toNearCycle_atom, P.out_eq_ivl R]
  simp [pos]

/-- Identifying atoms identifies every interval; no choice of an arc
endpoint is silently changed by the transfer. -/
theorem nearCycle_interval_eq_ivl (N : NearCycle x ε) (hm : P.m = N.k + 3)
    (hread : ∀ i : Fin (N.k + 3), N.atom i = P.ivl R i.val i.val)
    (a b : Fin (N.k + 3)) : N.interval a b = P.ivl R a.val b.val := by
  classical
  ext v
  change v ∈ (Icc a b).biUnion N.atom ↔ _
  rw [mem_biUnion, P.mem_ivl R]
  constructor
  · rintro ⟨i, hi, hv⟩
    rw [hread i, P.mem_ivl R] at hv
    rw [mem_Icc] at hi
    have hi1 : a.val ≤ i.val := hi.1
    have hi2 : i.val ≤ b.val := hi.2
    omega
  · rintro ⟨ha, hb⟩
    let i : Fin (N.k + 3) := ⟨P.pos R (P.idx R v), by rw [← hm]; exact P.pos_lt R _⟩
    refine ⟨i, mem_Icc.mpr ⟨ha, hb⟩, ?_⟩
    rw [hread i, P.mem_ivl R]
    exact ⟨le_rfl, le_rfl⟩

/-- The endpoint-facing failure bound, with half-weight atoms identified
by singleton intervals. The coordinate premise is supplied when selecting
the intervals for members of the original family. -/
theorem prob_fails_sharp_read (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5)
    (N : NearCycle (e₀.restrict x) ε) (hm : P.m = N.k + 3)
    (hread : ∀ i : Fin (N.k + 3), N.atom i = P.ivl R i.val i.val)
    (hroot : N.root = P.rootAtom)
    {p : Fin (N.k + 3) × Fin (N.k + 3)}
    (hpos : 0 < p.1)
    (hrel : N.interval p.1 p.2 ∈ 𝒞 ∨ p.1 = p.2)
    (hcoords : N.interval p.1 p.2 ∈ 𝒞 →
      P.lo R (N.interval p.1 p.2) = p.1.val ∧ P.hi R (N.interval p.1 p.2) = p.2.val)
    (hnm : IsNearMinCut x η (N.interval p.1 p.2)) :
    μ.probEvent (N.Fails p) ≤ if p.1 = p.2 then 21 * η else 11 * η := by
  classical
  have hI := P.nearCycle_interval_eq_ivl R N hm hread p.1 p.2
  have hlast : N.lastIdx.val = P.m - 1 := by
    change N.k + 2 = P.m - 1
    omega
  have hzero : 0 < p.1.val := hpos
  have hnonatom : p.1 ≠ p.2 → N.interval p.1 p.2 ∈ 𝒞 :=
    fun h => hrel.resolve_right h
  by_cases hend : p.1 = 1 ∨ p.2 = N.lastIdx
  · have hevent : N.Fails p = fun T => ¬ ((cutEdges (N.interval p.1 p.2) \
        betweenEdges (N.interval p.1 p.2) P.rootAtom) ∩ T).card = 1 := by
      funext T
      simp only [Fails, if_pos hend, CutHappy, sideEdges, upEdges, hroot]
    rw [hevent, μ.probEvent_not]
    by_cases hat : p.1 = p.2
    · rw [if_pos hat]
      have hprob : 1 - 12 * η ≤ μ.probEvent
          (fun T => ((cutEdges (N.interval p.1 p.2) \
            betweenEdges (N.interval p.1 p.2) P.rootAtom) ∩ T).card = 1) := by
        rcases hend with h | h
        · have hi : N.interval p.1 p.2 = P.ivl R 1 1 := by
            rw [hI, ← hat, h]
            rfl
          rw [hi]
          exact P.prob_side_one_first_atom R hx μ hcomp hη0 hη (by rwa [← hi])
        · have hi : N.interval p.1 p.2 = P.ivl R (P.m - 1) (P.m - 1) := by
            rw [hI, hat, h, hlast]
          rw [hi]
          exact P.prob_side_one_last_atom R hx μ hcomp hη0 hη (by rwa [← hi])
      linarith
    · rw [if_neg hat]
      have hmem := hnonatom hat
      have hc := hcoords hmem
      have hb : P.lo R (N.interval p.1 p.2) = 1 ∨
          P.hi R (N.interval p.1 p.2) = P.m - 1 := by
        rcases hend with h | h
        · exact Or.inl (by rw [hc.1, h]; rfl)
        · exact Or.inr (by rw [hc.2, h, hlast])
      have hp := P.prob_side_one_member R hx μ hcomp hη0 hη hmem hb
      linarith
  · have hn1 : p.1 ≠ 1 := fun h => hend (Or.inl h)
    have hn2 : p.2 ≠ N.lastIdx := fun h => hend (Or.inr h)
    have hp2 : p.2.val < P.m - 1 := by
      have hne : p.2.val ≠ N.lastIdx.val := fun h => hn2 (Fin.ext h)
      have hle : p.2.val ≤ N.lastIdx.val := Fin.le_last _
      omega
    have hp1 : 1 < p.1.val := by
      have hne : p.1.val ≠ 1 := fun h => hn1 (Fin.ext h)
      omega
    have htwo : 1 - (if p.1 = p.2 then 21 * η else 11 * η) ≤
        μ.probEvent (fun T => (cutEdges (N.interval p.1 p.2) ∩ T).card = 2) := by
      by_cases hat : p.1 = p.2
      · rw [if_pos hat, hI, ← hat]
        exact P.prob_cut_two_atom R hx μ hcomp hη0 hη hp1 (by omega)
          (by rwa [hI, ← hat] at hnm)
      · rw [if_neg hat]
        have hmemb := hnonatom hat
        have hc := hcoords hmemb
        have hp := P.prob_cut_two_member R hx μ hcomp hη0 hη hmemb
          (by rw [hc.1]; exact hp1) (by rw [hc.2]; exact hp2)
        linarith
    have hle : μ.probEvent (N.Fails p) ≤ μ.probEvent
        (fun T => ¬ (cutEdges (N.interval p.1 p.2) ∩ T).card = 2) := by
      refine μ.probEvent_mono fun T hT htwo => ?_
      rw [Fails, if_neg hend, htwo] at hT
      exact (by decide : ¬ Odd (2 : ℕ)) hT
    rw [μ.probEvent_not] at hle
    linarith

end TSPGap.PolygonRep

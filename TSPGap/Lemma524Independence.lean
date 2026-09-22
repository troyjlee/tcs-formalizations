/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Fact28
import TSPGap.FederMihail

/-!
# The independence step of KKO21 Lemma 5.24

Lemma 5.24 conditions on `u`, `v`, `u ∪ v` inducing trees and `C_T = 0`, and
then asserts that "which bundle edge is present" is independent of the events
on the edges leaving `u ∪ v`.  KKO justify it by the product structure of the
conditioned λ-uniform law.  Here it is **four instances of Fact 2.8** at
`S = u ∪ v` (`TreeCondIndep`, available at the max-entropy limit with no side
hypotheses): with `K_in`, `A` inside-determined and `K_out`, `B`
outside-determined, and `C := InducesTreeOn (u ∪ v)`,

`W(K_in ∧ A ∧ K_out ∧ B ∧ C) · W(K_in ∧ K_out ∧ C)
  = W(K_in ∧ A ∧ K_out ∧ C) · W(K_in ∧ K_out ∧ B ∧ C)`

(`condIndep_conditioned`), which is exactly `P_ν[A ∧ B] = P_ν[A] · P_ν[B]`
for `ν := μ | K_in ∧ K_out ∧ C`, cross-multiplied.  Multiplying by `W(C)²`
and rearranging the four identities gives it; when `W(C) = 0` every term
vanishes, so no positivity is needed.

The side conditions are closed under conjunction and are supplied by the
`insideDetermined_inter` / `outsideDetermined_inter` bridges — an event that
only looks at `T ∩ D` is inside-determined when `D` lies inside `S` and
outside-determined when every edge of `D` leaves `S` — and by
`insideDetermined_inducesTree` for the atom-tree events.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Event masses are weight masses -/

theorem eventMass_eq_weightMass (f : Finset (Sym2 (Fin n)) → ℝ)
    (Q : Finset (Sym2 (Fin n)) → Prop) : eventMass f Q = weightMass f Q := by
  classical
  rw [eventMass, weightMass_eq_filter_sum]

theorem eventMass_congr (f : Finset (Sym2 (Fin n)) → ℝ)
    {P Q : Finset (Sym2 (Fin n)) → Prop} (h : ∀ T, P T ↔ Q T) :
    eventMass f P = eventMass f Q := by
  rw [eventMass_eq_weightMass, eventMass_eq_weightMass]
  exact weightMass_congr h

/-! ### Determined events -/

theorem InsideDetermined.and {S : Finset (Fin n)} {A A' : Finset (Sym2 (Fin n)) → Prop}
    (h : InsideDetermined S A) (h' : InsideDetermined S A') :
    InsideDetermined S (fun T => A T ∧ A' T) :=
  fun T T' hTT' => and_congr (h T T' hTT') (h' T T' hTT')

theorem OutsideDetermined.and {S : Finset (Fin n)} {B B' : Finset (Sym2 (Fin n)) → Prop}
    (h : OutsideDetermined S B) (h' : OutsideDetermined S B') :
    OutsideDetermined S (fun T => B T ∧ B' T) :=
  fun T T' hTT' => and_congr (h T T' hTT') (h' T T' hTT')

/-- An event that only looks at `T ∩ D` with `D` inside `S` is
inside-determined. -/
theorem insideDetermined_inter {S : Finset (Fin n)} {D : Finset (Sym2 (Fin n))}
    (hD : ∀ e ∈ D, ∀ v ∈ e, v ∈ S) (P : Finset (Sym2 (Fin n)) → Prop) :
    InsideDetermined S (fun T => P (T ∩ D)) := by
  classical
  have key : ∀ T : Finset (Sym2 (Fin n)), T ∩ D = insidePart S T ∩ D := by
    intro T
    ext e
    simp only [Finset.mem_inter, insidePart, Finset.mem_filter]
    constructor
    · rintro ⟨hT, hDe⟩; exact ⟨⟨hT, hD e hDe⟩, hDe⟩
    · rintro ⟨⟨hT, -⟩, hDe⟩; exact ⟨hT, hDe⟩
  intro T T' hTT'
  show P (T ∩ D) ↔ P (T' ∩ D)
  rw [key T, key T', hTT']

/-- Membership of a single edge inside `S` is inside-determined. -/
theorem insideDetermined_mem {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (he : ∀ w ∈ e, w ∈ S) : InsideDetermined S (fun T => e ∈ T) := by
  classical
  have h := insideDetermined_inter (S := S) (D := {e}) (fun e' he' => by
    rw [Finset.mem_singleton] at he'; rw [he']; exact he) (fun X => e ∈ X)
  intro T T' hTT'
  have := h T T' hTT'
  simpa [Finset.mem_inter] using this

/-- An event that only looks at `T ∩ D` with every edge of `D` leaving `S` is
outside-determined. -/
theorem outsideDetermined_inter {S : Finset (Fin n)} {D : Finset (Sym2 (Fin n))}
    (hD : ∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ S) (P : Finset (Sym2 (Fin n)) → Prop) :
    OutsideDetermined S (fun T => P (T ∩ D)) := by
  classical
  have key : ∀ T : Finset (Sym2 (Fin n)), T ∩ D = outsidePart S T ∩ D := by
    intro T
    ext e
    simp only [Finset.mem_inter, outsidePart, Finset.mem_filter]
    constructor
    · rintro ⟨hT, hDe⟩; exact ⟨⟨hT, hD e hDe⟩, hDe⟩
    · rintro ⟨⟨hT, -⟩, hDe⟩; exact ⟨hT, hDe⟩
  intro T T' hTT'
  show P (T ∩ D) ↔ P (T' ∩ D)
  rw [key T, key T', hTT']

/-- The tree event of a sub-atom is inside-determined. -/
theorem insideDetermined_inducesTree {S u : Finset (Fin n)} (hu : u ⊆ S) :
    InsideDetermined S (InducesTree u) := by
  classical
  have key : ∀ T : Finset (Sym2 (Fin n)), insidePart u T = insidePart u (insidePart S T) := by
    intro T
    ext e
    simp only [insidePart, Finset.mem_filter]
    constructor
    · rintro ⟨hT, hin⟩; exact ⟨⟨hT, fun v hv => hu (hin v hv)⟩, hin⟩
    · rintro ⟨⟨hT, -⟩, hin⟩; exact ⟨hT, hin⟩
  intro T T' hTT'
  unfold InducesTree
  rw [key T, key T', hTT']

/-! ### The conditioned independence -/

/-- **Independence under the conditioned law**, cross-multiplied.  With `K_in`,
`A` inside-determined and `K_out`, `B` outside-determined,

`W(K_in ∧ A ∧ K_out ∧ B ∧ C) · W(K_in ∧ K_out ∧ C)
  = W(K_in ∧ A ∧ K_out ∧ C) · W(K_in ∧ K_out ∧ B ∧ C)`,

where `C := InducesTreeOn S`.  No positivity is assumed. -/
theorem condIndep_conditioned {f : Finset (Sym2 (Fin n)) → ℝ}
    (hnn : WeightNonneg f) (hf : TreeCondIndep f) (S : Finset (Fin n))
    {Kin A Kout B : Finset (Sym2 (Fin n)) → Prop}
    (hKin : InsideDetermined S Kin) (hA : InsideDetermined S A)
    (hKout : OutsideDetermined S Kout) (hB : OutsideDetermined S B) :
    eventMass f (fun T => (Kin T ∧ A T) ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T)
        * eventMass f (fun T => Kin T ∧ Kout T ∧ InducesTreeOn S T)
      = eventMass f (fun T => (Kin T ∧ A T) ∧ Kout T ∧ InducesTreeOn S T)
        * eventMass f (fun T => Kin T ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T) := by
  classical
  have I1 := hf S _ _ (hKin.and hA) (hKout.and hB)
  have I0 := hf S _ _ hKin hKout
  have IA := hf S _ _ (hKin.and hA) hKout
  have IB := hf S _ _ hKin (hKout.and hB)
  unfold CondIndepCross at I1 I0 IA IB
  set c := eventMass f (InducesTreeOn S) with hc
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- every term lives inside `C`, so all vanish
    have hzero : ∀ Q : Finset (Sym2 (Fin n)) → Prop,
        (∀ T, Q T → InducesTreeOn S T) → eventMass f Q = 0 := by
      intro Q hQ
      have hC0 : weightMass f (InducesTreeOn S) = 0 := by
        rw [← eventMass_eq_weightMass, ← hc]; exact hc0
      rw [eventMass_eq_weightMass]
      refine le_antisymm ?_ (weightMass_nonneg hnn Q)
      have := weightMass_mono hnn hQ
      rw [hC0] at this
      exact this
    rw [hzero _ (fun T h => h.2.2), hzero _ (fun T h => h.2.2),
      hzero _ (fun T h => h.2.2), hzero _ (fun T h => h.2.2)]
  · -- cancel `c²`
    have hcc : c * c ≠ 0 := mul_ne_zero hc0 hc0
    apply mul_right_cancel₀ hcc
    calc eventMass f (fun T => (Kin T ∧ A T) ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T)
          * eventMass f (fun T => Kin T ∧ Kout T ∧ InducesTreeOn S T) * (c * c)
        = (eventMass f (fun T => (Kin T ∧ A T) ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T) * c)
          * (eventMass f (fun T => Kin T ∧ Kout T ∧ InducesTreeOn S T) * c) := by ring
      _ = (eventMass f (fun T => (Kin T ∧ A T) ∧ InducesTreeOn S T)
            * eventMass f (fun T => (Kout T ∧ B T) ∧ InducesTreeOn S T))
          * (eventMass f (fun T => Kin T ∧ InducesTreeOn S T)
            * eventMass f (fun T => Kout T ∧ InducesTreeOn S T)) := by rw [I1, I0]
      _ = (eventMass f (fun T => (Kin T ∧ A T) ∧ InducesTreeOn S T)
            * eventMass f (fun T => Kout T ∧ InducesTreeOn S T))
          * (eventMass f (fun T => Kin T ∧ InducesTreeOn S T)
            * eventMass f (fun T => (Kout T ∧ B T) ∧ InducesTreeOn S T)) := by ring
      _ = (eventMass f (fun T => (Kin T ∧ A T) ∧ Kout T ∧ InducesTreeOn S T) * c)
          * (eventMass f (fun T => Kin T ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T) * c) := by
          rw [IA, IB]
      _ = _ := by ring

/-- The export at the max-entropy limit, in `weightMass` form. -/
theorem IsMaxEntropyLimit.condIndep_conditioned {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (h : IsMaxEntropyLimit μ) (S : Finset (Fin n))
    {Kin A Kout B : Finset (Sym2 (Fin n)) → Prop}
    (hKin : InsideDetermined S Kin) (hA : InsideDetermined S A)
    (hKout : OutsideDetermined S Kout) (hB : OutsideDetermined S B) :
    weightMass μ.prob (fun T => (Kin T ∧ A T) ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T)
        * weightMass μ.prob (fun T => Kin T ∧ Kout T ∧ InducesTreeOn S T)
      = weightMass μ.prob (fun T => (Kin T ∧ A T) ∧ Kout T ∧ InducesTreeOn S T)
        * weightMass μ.prob (fun T => Kin T ∧ (Kout T ∧ B T) ∧ InducesTreeOn S T) := by
  have := TSPGap.condIndep_conditioned μ.weightNonneg h.treeCondIndep S hKin hA hKout hB
  simpa only [eventMass_eq_weightMass] using this

end TSPGap

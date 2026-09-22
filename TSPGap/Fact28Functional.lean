/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Fact28

/-!
# Fact 2.8 for determined *functions*

`TreeCondIndep` states the conditional-independence cross identity for `Prop`
events.  The refinement's transport needs it for real-valued functions that
depend only on the inside (resp. outside) part of the tree — because a piece
event, disintegrated over projections, becomes the `q`-mass of the copy choices
that satisfy it: a weight in `[0, 1]`, not an indicator.

Finite linearity closes the gap.  A function determined by `insidePart` is a
finite combination of its level-set indicators, each of which is an
inside-determined event; the cross identity is bilinear; so it extends.
-/

namespace TSPGap

open Finset
open scoped Classical

variable {n : ℕ}

/-- The `f`-weighted integral of `a` over the event `C`. -/
noncomputable def eventInt (f : Finset (Sym2 (Fin n)) → ℝ) (C : Finset (Sym2 (Fin n)) → Prop)
    (a : Finset (Sym2 (Fin n)) → ℝ) : ℝ :=
  ∑ T : Finset (Sym2 (Fin n)), if C T then f T * a T else 0

/-- A function of the tree that depends only on its inside part. -/
def InsideFunctionDetermined (S : Finset (Fin n)) (a : Finset (Sym2 (Fin n)) → ℝ) : Prop :=
  ∀ T T', insidePart S T = insidePart S T' → a T = a T'

/-- A function of the tree that depends only on its outside part. -/
def OutsideFunctionDetermined (S : Finset (Fin n)) (a : Finset (Sym2 (Fin n)) → ℝ) : Prop :=
  ∀ T T', outsidePart S T = outsidePart S T' → a T = a T'

/-- The integral of an indicator is the mass of the conjunction. -/
theorem eventInt_indicator (f : Finset (Sym2 (Fin n)) → ℝ) (C A : Finset (Sym2 (Fin n)) → Prop) :
    eventInt f C (fun T => if A T then 1 else 0) = eventMass f (fun T => A T ∧ C T) := by
  unfold eventInt eventMass
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hC : C T <;> by_cases hA : A T <;> simp [hA]

theorem eventInt_one (f : Finset (Sym2 (Fin n)) → ℝ) (C : Finset (Sym2 (Fin n)) → Prop) :
    eventInt f C (fun _ => 1) = eventMass f C := by
  unfold eventInt eventMass
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun T _ => by split_ifs <;> simp

/-- A level set of an inside-determined function is an inside-determined event. -/
theorem InsideFunctionDetermined.levelSet {S : Finset (Fin n)} {a : Finset (Sym2 (Fin n)) → ℝ}
    (ha : InsideFunctionDetermined S a) (v : ℝ) : InsideDetermined S (fun T => a T = v) :=
  fun T T' h => by show a T = v ↔ a T' = v; rw [ha T T' h]

theorem OutsideFunctionDetermined.levelSet {S : Finset (Fin n)} {a : Finset (Sym2 (Fin n)) → ℝ}
    (ha : OutsideFunctionDetermined S a) (v : ℝ) : OutsideDetermined S (fun T => a T = v) :=
  fun T T' h => by show a T = v ↔ a T' = v; rw [ha T T' h]

/-- **Level-set expansion.**  Any function on a finite type is the sum, over its
finitely many values, of that value times the level-set indicator. -/
theorem eq_sum_levelSets (a : Finset (Sym2 (Fin n)) → ℝ) (T : Finset (Sym2 (Fin n))) :
    a T = ∑ v ∈ Finset.univ.image a, (if a T = v then v else 0) := by
  rw [Finset.sum_ite_eq]
  simp

/-- `eventInt` is linear in the integrand, over a finite sum. -/
theorem eventInt_sum {ι : Type*} (f : Finset (Sym2 (Fin n)) → ℝ) (C : Finset (Sym2 (Fin n)) → Prop)
    (s : Finset ι) (g : ι → Finset (Sym2 (Fin n)) → ℝ) :
    eventInt f C (fun T => ∑ i ∈ s, g i T) = ∑ i ∈ s, eventInt f C (g i) := by
  unfold eventInt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs
  · rw [Finset.mul_sum]
  · simp

theorem eventInt_smul (f : Finset (Sym2 (Fin n)) → ℝ) (C : Finset (Sym2 (Fin n)) → Prop)
    (c : ℝ) (a : Finset (Sym2 (Fin n)) → ℝ) :
    eventInt f C (fun T => c * a T) = c * eventInt f C a := by
  unfold eventInt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> ring

/-- **Fact 2.8 for determined functions.**  From the event form, by expanding
both functions over their level sets and using bilinearity of the cross
identity. -/
theorem TreeCondIndep.functional {f : Finset (Sym2 (Fin n)) → ℝ} (hf : TreeCondIndep f)
    (S : Finset (Fin n)) {a b : Finset (Sym2 (Fin n)) → ℝ}
    (ha : InsideFunctionDetermined S a) (hb : OutsideFunctionDetermined S b) :
    eventInt f (InducesTreeOn S) (fun T => a T * b T)
        * eventInt f (InducesTreeOn S) (fun _ => 1)
      = eventInt f (InducesTreeOn S) a * eventInt f (InducesTreeOn S) b := by
  set Va := Finset.univ.image a with hVa
  set Vb := Finset.univ.image b with hVb
  -- expand `a` and `b` over level sets
  have hexp : ∀ T, a T * b T = ∑ v ∈ Va, ∑ w ∈ Vb,
      (v * w) * (if a T = v ∧ b T = w then 1 else 0) := by
    intro T
    conv_lhs => rw [eq_sum_levelSets a T, eq_sum_levelSets b T]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    by_cases hv : a T = v <;> by_cases hw : b T = w <;> simp [hv, hw]
  have ha' : ∀ T, a T = ∑ v ∈ Va, v * (if a T = v then 1 else 0) := by
    intro T; conv_lhs => rw [eq_sum_levelSets a T]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : a T = v <;> simp [hv]
  have hb' : ∀ T, b T = ∑ w ∈ Vb, w * (if b T = w then 1 else 0) := by
    intro T; conv_lhs => rw [eq_sum_levelSets b T]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : b T = w <;> simp [hw]
  -- rewrite the four integrals as sums of event masses
  have hab : eventInt f (InducesTreeOn S) (fun T => a T * b T)
      = ∑ v ∈ Va, ∑ w ∈ Vb, (v * w) * eventMass f (fun T => (a T = v ∧ b T = w) ∧ InducesTreeOn S T) := by
    simp_rw [hexp]
    rw [eventInt_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [eventInt_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [eventInt_smul]
    congr 1
    unfold eventInt eventMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hC : InducesTreeOn S T <;> by_cases hA : (a T = v ∧ b T = w) <;> simp [hC, hA]
  have haI : eventInt f (InducesTreeOn S) a = ∑ v ∈ Va, v * eventMass f (fun T => a T = v ∧ InducesTreeOn S T) := by
    conv_lhs => rw [show a = fun T => ∑ v ∈ Va, v * (if a T = v then 1 else 0) from funext ha']
    rw [eventInt_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [eventInt_smul, eventInt_indicator f (InducesTreeOn S) (fun T => a T = v)]
  have hbI : eventInt f (InducesTreeOn S) b = ∑ w ∈ Vb, w * eventMass f (fun T => b T = w ∧ InducesTreeOn S T) := by
    conv_lhs => rw [show b = fun T => ∑ w ∈ Vb, w * (if b T = w then 1 else 0) from funext hb']
    rw [eventInt_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [eventInt_smul, eventInt_indicator f (InducesTreeOn S) (fun T => b T = w)]
  rw [hab, haI, hbI, eventInt_one, Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  -- the event-form cross identity at the level sets
  have h := hf S (fun T => a T = v) (fun T => b T = w) (ha.levelSet v) (hb.levelSet w)
  unfold CondIndepCross at h
  have hassoc : (fun T => (a T = v ∧ b T = w) ∧ InducesTreeOn S T)
      = fun T => a T = v ∧ b T = w ∧ InducesTreeOn S T := funext fun T => propext and_assoc
  have h' : eventMass f (fun T => (a T = v ∧ b T = w) ∧ InducesTreeOn S T) * eventMass f (InducesTreeOn S)
      = eventMass f (fun T => a T = v ∧ InducesTreeOn S T) * eventMass f (fun T => b T = w ∧ InducesTreeOn S T) := by
    rw [hassoc]; exact h
  calc (v * w) * eventMass f (fun T => (a T = v ∧ b T = w) ∧ InducesTreeOn S T) * eventMass f (InducesTreeOn S)
      = (v * w) * (eventMass f (fun T => (a T = v ∧ b T = w) ∧ InducesTreeOn S T) * eventMass f (InducesTreeOn S)) := by ring
    _ = (v * w) * (eventMass f (fun T => a T = v ∧ InducesTreeOn S T) * eventMass f (fun T => b T = w ∧ InducesTreeOn S T)) := by rw [h']
    _ = v * eventMass f (fun T => a T = v ∧ InducesTreeOn S T) * (w * eventMass f (fun T => b T = w ∧ InducesTreeOn S T)) := by ring

end TSPGap

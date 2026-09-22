/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma62
import TSPGap.Selected

/-!
# KKO21 §7: the thinning and reduction layer

KKO "subsample" every happy event to probability exactly `p`.  An arbitrary
real fraction of a finite tree distribution is not an event (the same point
as in Proposition 5.6), so the formal replacement is a **thinning**: a
subweight `v ≤ μ.prob`, supported inside the happy event, of total mass
exactly `p` (`IsThinning`).  It exists by proportional scaling whenever the
event has mass at least `p` (`exists_thinning`), and it is read pointwise as
the **density** `ρ(T) = v(T)/μ(T) ∈ [0, 1]` (`density`): the reduction applied
on the tree `T` is `βxₑ ρ(T)`.  Every expectation is then exact:
`E[ρ · f] = ∑_T v(T) f(T)` (`expect_density_mul`), in particular
`E[ρ] = p`.  Scaling a thinning down only lowers every pointwise value
(`density_le_of_le`), which is the monotonicity the feasibility inequalities
use.

⚠️ `IsThinning` alone is too weak for §7: KKO's subsampling is **uniform**
inside the happy event (`P[Q | R] = P[Q | H]`), and an arbitrary subweight can
bias the conditional law.  `IsUniformThinning` (and, for subweights instead of
events, `IsRescaling`) records the proportionality zero-safely, and
`thinWeight` is certified uniform; the reduction data of §7 store these, never
bare `IsThinning`s.

Also here: the paper-facing classification `DegreeCutData` (a cut of the
hierarchy that is not a near-cycle cut, with at least three atoms — KKO define
two-children cuts to be polygon cuts, so this carries what `Hierarchy` does
not encode), good top edges (`IsGoodTopEdge`), the good edge set `E_g`
(`goodEdges`), and the generic pointwise bound on a reduction
`0 ≤ c · xₑ · ρ ≤ c · xₑ` (`reduction_bounds`).
-/

namespace TSPGap
open Finset
open scoped Classical

/-! ### Thinnings -/

section Thinning

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A thinning of the event `E` at mass `p`**: a subweight of `w`, supported
in `E`, of total mass exactly `p`. -/
structure IsThinning (w v : Finset ι → ℝ) (E : Finset ι → Prop) (p : ℝ) : Prop where
  nonneg : WeightNonneg v
  le : ∀ T, v T ≤ w T
  support : ∀ T, v T ≠ 0 → E T
  total : totalMass v = p

/-- The proportional thinning of `E` to mass `p`. -/
noncomputable def thinWeight (w : Finset ι → ℝ) (E : Finset ι → Prop) (p : ℝ) :
    Finset ι → ℝ :=
  fun T => if E T then (p / weightMass w E) * w T else 0

/-- **Every event of mass at least `p ≥ 0` has a thinning at mass `p`.** -/
theorem exists_thinning {w : Finset ι → ℝ} (hnn : WeightNonneg w) (E : Finset ι → Prop)
    {p : ℝ} (hp0 : 0 ≤ p) (hpE : p ≤ weightMass w E) :
    IsThinning w (thinWeight w E p) E p := by
  have hEnn : 0 ≤ weightMass w E := weightMass_nonneg hnn E
  rcases eq_or_lt_of_le hEnn with hE0 | hEpos
  · -- the event is massless, so `p = 0` and the thinning is `0`
    have hp : p = 0 := le_antisymm (by rw [← hE0] at hpE; exact hpE) hp0
    refine ⟨fun T => ?_, fun T => ?_, fun T hT => ?_, ?_⟩
    · unfold thinWeight; split_ifs <;> simp [hp]
    · unfold thinWeight; split_ifs with h
      · rw [hp, zero_div, zero_mul]; exact hnn T
      · exact hnn T
    · unfold thinWeight at hT; split_ifs at hT with h
      · exact h
      · exact absurd rfl hT
    · unfold totalMass thinWeight
      rw [hp]
      exact Finset.sum_eq_zero fun T _ => by split_ifs <;> simp
  · have hratio0 : 0 ≤ p / weightMass w E := div_nonneg hp0 hEpos.le
    have hratio1 : p / weightMass w E ≤ 1 := (div_le_one hEpos).mpr hpE
    refine ⟨fun T => ?_, fun T => ?_, fun T hT => ?_, ?_⟩
    · unfold thinWeight; split_ifs
      · exact mul_nonneg hratio0 (hnn T)
      · exact le_rfl
    · unfold thinWeight; split_ifs
      · calc p / weightMass w E * w T ≤ 1 * w T :=
            mul_le_mul_of_nonneg_right hratio1 (hnn T)
          _ = w T := one_mul _
      · exact hnn T
    · unfold thinWeight at hT; split_ifs at hT with h
      · exact h
      · exact absurd rfl hT
    · unfold totalMass thinWeight
      rw [← Finset.sum_filter, ← Finset.mul_sum, ← weightMass_eq_filter_sum,
        div_mul_cancel₀ _ hEpos.ne']

/-- The **density** of a thinning: the fraction of the tree `T` it keeps. -/
noncomputable def density (w v : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  if w T = 0 then 0 else v T / w T

theorem density_nonneg {w v : Finset ι → ℝ} (hnn : WeightNonneg w) (hv : WeightNonneg v)
    (T : Finset ι) : 0 ≤ density w v T := by
  unfold density
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (hv T) (hnn T)

theorem density_le_one {w v : Finset ι → ℝ} (hnn : WeightNonneg w) (hle : ∀ T, v T ≤ w T)
    (T : Finset ι) : density w v T ≤ 1 := by
  unfold density
  split_ifs with h
  · exact zero_le_one
  · have hpos : 0 < w T := lt_of_le_of_ne (hnn T) (Ne.symm h)
    exact (div_le_one hpos).mpr (hle T)

/-- The density vanishes off the support of the thinning. -/
theorem density_eq_zero_of_not {w v : Finset ι → ℝ} {E : Finset ι → Prop}
    (h : IsThinning w v E p) {T : Finset ι} (hT : ¬ E T) : density w v T = 0 := by
  unfold density
  split_ifs with hw
  · rfl
  · have : v T = 0 := by
      by_contra hv
      exact hT (h.support T hv)
    rw [this, zero_div]

/-- `w(T) · ρ(T) = v(T)`: the density recovers the thinning. -/
theorem mul_density {w v : Finset ι → ℝ} (hle : ∀ T, v T ≤ w T) (hv : WeightNonneg v)
    (T : Finset ι) : w T * density w v T = v T := by
  unfold density
  split_ifs with h
  · have : v T = 0 := le_antisymm (by rw [← h]; exact hle T) (hv T)
    rw [h, this, mul_zero]
  · rw [mul_div_cancel₀ _ h]

/-- **Scaling down**: a smaller thinning has a pointwise smaller density. -/
theorem density_le_of_le {w v v' : Finset ι → ℝ} (hnn : WeightNonneg w)
    (hvv' : ∀ T, v T ≤ v' T) (T : Finset ι) : density w v T ≤ density w v' T := by
  unfold density
  split_ifs with h
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (hvv' T) (hnn T)

end Thinning

/-! ### Uniform thinnings

KKO's subsampling is **uniform** inside the happy event: `R` is a uniformly
random subset of `H` of measure `p`, so that `P[Q | R] = P[Q | H]` for every
event `Q` — the identity Lemma 7.3 and Claims 7.4–7.5 rest on.  An arbitrary
inhabitant of `IsThinning` may bias the conditional law; the proportional
`thinWeight` does not.  `IsUniformThinning` records the proportionality
zero-safely, `W(E) · v(T) = p · w(T) 1_E(T)`, whence
`W(E) · ∑ v f = p · ∑ w 1_E f` (`IsUniformThinning.sum_mul`) and, for events,
`W(E) · W_v(Q) = p · W(E ∧ Q)` (`IsUniformThinning.weightMass_mul`); no
division anywhere, and every conditional identity follows once the event mass
is positive (`IsUniformThinning.weightMass_eq`).

The bottom edges need the same notion relative to a **subweight** rather than
an event: KKO's max-flow "event" `E_S` (Definition 5.8) is Proposition 5.6's
*selected subweight*, not a predicate.  So the proportionality is stated first
for a base subweight (`IsRescaling`), and a uniform thinning of an event is the
rescaling of `w · 1_E` (`eventWeight`).  Downstream reduction data store
uniform thinnings and rescalings, never bare `IsThinning`s. -/

section Uniform

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `w · 1_E`: the weight restricted to the event `E`. -/
noncomputable def eventWeight (w : Finset ι → ℝ) (E : Finset ι → Prop) : Finset ι → ℝ :=
  fun T => if E T then w T else 0

theorem totalMass_eventWeight (w : Finset ι → ℝ) (E : Finset ι → Prop) :
    totalMass (eventWeight w E) = weightMass w E := rfl

theorem eventWeight_nonneg {w : Finset ι → ℝ} (hnn : WeightNonneg w) (E : Finset ι → Prop) :
    WeightNonneg (eventWeight w E) := fun T => by
  unfold eventWeight
  split_ifs
  · exact hnn T
  · exact le_rfl

/-- **A rescaling of the subweight `b` to total mass `p`**, zero-safely:
`(∑ b) · v = p · b` pointwise, and `∑ v = p`. -/
structure IsRescaling (b v : Finset ι → ℝ) (p : ℝ) : Prop where
  nonneg : WeightNonneg v
  proportional : ∀ T, totalMass b * v T = p * b T
  total : totalMass v = p

omit [DecidableEq ι] in
/-- **A relative bound survives a rescaling.**  If an event carries at most a
`c` fraction of `b`, it carries at most `c · p` of the rescaling.  This is what
lets a bound proved at a subweight (Corollaries 5.10, 5.11 at the max-flow
selection) be read at the thinning, whose total mass is `p`. -/
theorem IsRescaling.weightMass_le {b v : Finset ι → ℝ} {p : ℝ} (hr : IsRescaling b v p)
    (hb : 0 < totalMass b) {Q : Finset ι → Prop} {c : ℝ}
    (h : weightMass b Q ≤ c * totalMass b) (hp0 : 0 ≤ p) :
    weightMass v Q ≤ c * p := by
  classical
  have hsum : totalMass b * weightMass v Q = p * weightMass b Q := by
    rw [weightMass, weightMass, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hQ : Q T
    · rw [if_pos hQ, if_pos hQ]; exact hr.proportional T
    · rw [if_neg hQ, if_neg hQ, mul_zero, mul_zero]
  have hle : totalMass b * weightMass v Q ≤ totalMass b * (c * p) := by
    rw [hsum]
    nlinarith [h, hp0]
  exact le_of_mul_le_mul_left hle hb

/-- The proportional rescaling `(p / ∑ b) · b`. -/
noncomputable def rescaleWeight (b : Finset ι → ℝ) (p : ℝ) : Finset ι → ℝ :=
  fun T => (p / totalMass b) * b T

/-- **Every nonnegative subweight of mass at least `p ≥ 0` rescales to `p`.** -/
theorem isRescaling_rescaleWeight {b : Finset ι → ℝ} (hb : WeightNonneg b) {p : ℝ}
    (hp0 : 0 ≤ p) (hpb : p ≤ totalMass b) : IsRescaling b (rescaleWeight b p) p := by
  have hM : 0 ≤ totalMass b := totalMass_nonneg hb
  have htot : totalMass (rescaleWeight b p) = p / totalMass b * totalMass b := by
    show ∑ T, p / totalMass b * b T = p / totalMass b * ∑ T, b T
    rw [Finset.mul_sum]
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · have hp : p = 0 := le_antisymm (by rw [← hM0] at hpb; exact hpb) hp0
    refine ⟨fun T => ?_, fun T => ?_, ?_⟩
    · unfold rescaleWeight
      rw [hp, zero_div, zero_mul]
    · rw [← hM0, zero_mul, hp, zero_mul]
    · rw [htot, hp, zero_div, zero_mul]
  · refine ⟨fun T => ?_, fun T => ?_, ?_⟩
    · unfold rescaleWeight
      exact mul_nonneg (div_nonneg hp0 hMpos.le) (hb T)
    · unfold rescaleWeight
      calc totalMass b * (p / totalMass b * b T)
          = p / totalMass b * totalMass b * b T := by ring
        _ = p * b T := by rw [div_mul_cancel₀ _ hMpos.ne']
    · rw [htot, div_mul_cancel₀ _ hMpos.ne']

/-- **The rescaling identity**: `(∑ b) · ∑ v f = p · ∑ b f`. -/
theorem IsRescaling.sum_mul {b v : Finset ι → ℝ} {p : ℝ} (h : IsRescaling b v p)
    (f : Finset ι → ℝ) : totalMass b * ∑ T, v T * f T = p * ∑ T, b T * f T := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← mul_assoc, h.proportional T, mul_assoc]

/-- The event form: `(∑ b) · W_v(Q) = p · W_b(Q)`. -/
theorem IsRescaling.weightMass_mul {b v : Finset ι → ℝ} {p : ℝ} (h : IsRescaling b v p)
    (Q : Finset ι → Prop) : totalMass b * weightMass v Q = p * weightMass b Q := by
  unfold weightMass
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs
  · exact h.proportional T
  · simp

/-- A rescaling to a mass at most the base mass stays below the base. -/
theorem IsRescaling.le {b v : Finset ι → ℝ} {p : ℝ} (h : IsRescaling b v p)
    (hb : WeightNonneg b) (hp0 : 0 ≤ p) (hpb : p ≤ totalMass b) (T : Finset ι) :
    v T ≤ b T := by
  rcases eq_or_lt_of_le (totalMass_nonneg hb) with hM0 | hMpos
  · have hp : p = 0 := le_antisymm (by rw [← hM0] at hpb; exact hpb) hp0
    have htot : ∑ S : Finset ι, v S = 0 := by rw [← hp]; exact h.total
    have hv : v T = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun S _ => h.nonneg S).mp htot T (Finset.mem_univ T)
    rw [hv]
    exact hb T
  · have hle : totalMass b * v T ≤ totalMass b * b T := by
      rw [h.proportional T]
      exact mul_le_mul_of_nonneg_right hpb (hb T)
    exact le_of_mul_le_mul_left hle hMpos

/-- **A uniform thinning of `E` at mass `p`**: a thinning that is proportional
to `w` on `E` — the rescaling of `w · 1_E` — zero-safely. -/
structure IsUniformThinning (w v : Finset ι → ℝ) (E : Finset ι → Prop) (p : ℝ) : Prop
    extends IsThinning w v E p where
  proportional : ∀ T, weightMass w E * v T = p * eventWeight w E T

theorem IsUniformThinning.isRescaling {w v : Finset ι → ℝ} {E : Finset ι → Prop} {p : ℝ}
    (h : IsUniformThinning w v E p) : IsRescaling (eventWeight w E) v p :=
  ⟨h.nonneg, fun T => by rw [totalMass_eventWeight]; exact h.proportional T, h.total⟩

/-- **The uniform-thinning identity**, zero-safe:
`W(E) · ∑ v f = p · ∑ w 1_E f`. -/
theorem IsUniformThinning.sum_mul {w v : Finset ι → ℝ} {E : Finset ι → Prop} {p : ℝ}
    (h : IsUniformThinning w v E p) (f : Finset ι → ℝ) :
    weightMass w E * ∑ T, v T * f T = p * ∑ T, (if E T then w T * f T else 0) := by
  have key := h.isRescaling.sum_mul f
  rw [totalMass_eventWeight] at key
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold eventWeight
  split_ifs <;> simp

/-- The event form: `W(E) · W_v(Q) = p · W(E ∧ Q)`. -/
theorem IsUniformThinning.weightMass_mul {w v : Finset ι → ℝ} {E : Finset ι → Prop} {p : ℝ}
    (h : IsUniformThinning w v E p) (Q : Finset ι → Prop) :
    weightMass w E * weightMass v Q = p * weightMass w (fun T => E T ∧ Q T) := by
  have key := h.isRescaling.weightMass_mul Q
  rw [totalMass_eventWeight] at key
  rw [key]
  congr 1
  unfold weightMass eventWeight
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hE : E T <;> by_cases hQ : Q T <;> simp [hE, hQ]

/-- The conditional identity at positive event mass: `W_v(Q) = p · P[Q | E]`. -/
theorem IsUniformThinning.weightMass_eq {w v : Finset ι → ℝ} {E : Finset ι → Prop} {p : ℝ}
    (h : IsUniformThinning w v E p) (hE : 0 < weightMass w E) (Q : Finset ι → Prop) :
    weightMass v Q = p * (weightMass w (fun T => E T ∧ Q T) / weightMass w E) := by
  refine mul_left_cancel₀ hE.ne' ?_
  rw [h.weightMass_mul Q, mul_div_assoc', mul_comm (weightMass w E), div_mul_cancel₀ _ hE.ne']

/-- **A conditional bound transfers to the thinning**: `P[Q | E] ≤ c`, in the
cross-multiplied form `W(E ∧ Q) ≤ c · W(E)`, gives `W_v(Q) ≤ p · c` — with no
positivity of `W(E)` needed (a massless event forces `p = 0`). -/
theorem IsUniformThinning.weightMass_le {w v : Finset ι → ℝ} {E : Finset ι → Prop} {p : ℝ}
    (h : IsUniformThinning w v E p) (hnn : WeightNonneg w) {Q : Finset ι → Prop} {c : ℝ}
    (hQ : weightMass w (fun T => E T ∧ Q T) ≤ c * weightMass w E) :
    weightMass v Q ≤ p * c := by
  have hp0 : 0 ≤ p := by rw [← h.total]; exact totalMass_nonneg h.nonneg
  rcases eq_or_lt_of_le (weightMass_nonneg hnn E) with hE0 | hEpos
  · -- the event is massless, so the thinning vanishes and `p = 0`
    have hE0' : ∑ S : Finset ι, (if E S then w S else 0) = 0 := hE0.symm
    have hsum : ∀ S ∈ (Finset.univ : Finset (Finset ι)), 0 ≤ (if E S then w S else 0) := by
      intro S _
      split_ifs
      · exact hnn S
      · exact le_rfl
    have hv : ∀ T, v T = 0 := by
      intro T
      by_cases hT : E T
      · have hw := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp hE0' T (Finset.mem_univ T)
        rw [if_pos hT] at hw
        exact le_antisymm (by rw [← hw]; exact h.le T) (h.nonneg T)
      · by_contra hne
        exact hT (h.support T hne)
    have hp : p = 0 := by
      rw [← h.total]
      exact Finset.sum_eq_zero fun T _ => hv T
    have hvQ : weightMass v Q = 0 := by
      unfold weightMass
      exact Finset.sum_eq_zero fun T _ => by split_ifs <;> simp [hv T]
    rw [hvQ, hp, zero_mul]
  · have hle : weightMass w E * weightMass v Q ≤ weightMass w E * (p * c) := by
      rw [h.weightMass_mul Q]
      calc p * weightMass w (fun T => E T ∧ Q T) ≤ p * (c * weightMass w E) :=
            mul_le_mul_of_nonneg_left hQ hp0
        _ = weightMass w E * (p * c) := by ring
    exact le_of_mul_le_mul_left hle hEpos

/-- **`thinWeight` is a uniform thinning.** -/
theorem isUniformThinning_thinWeight {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (E : Finset ι → Prop) {p : ℝ} (hp0 : 0 ≤ p) (hpE : p ≤ weightMass w E) :
    IsUniformThinning w (thinWeight w E p) E p := by
  refine ⟨exists_thinning hnn E hp0 hpE, fun T => ?_⟩
  unfold thinWeight eventWeight
  have hEnn : 0 ≤ weightMass w E := weightMass_nonneg hnn E
  rcases eq_or_lt_of_le hEnn with hE0 | hEpos
  · have hp : p = 0 := le_antisymm (by rw [← hE0] at hpE; exact hpE) hp0
    rw [← hE0, hp]
    simp
  · split_ifs
    · calc weightMass w E * (p / weightMass w E * w T)
          = p / weightMass w E * weightMass w E * w T := by ring
        _ = p * w T := by rw [div_mul_cancel₀ _ hEpos.ne']
    · simp

end Uniform

/-! ### Thinnings of a tree law -/

section TreeThinning

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- **Exact expectations**: `E_μ[ρ · f] = ∑_T v(T) f(T)`. -/
theorem TreeDist.expect_density_mul (μ : TreeDist n x) {v : Finset (Sym2 (Fin n)) → ℝ}
    (hle : ∀ T, v T ≤ μ.prob T) (hv : WeightNonneg v) (f : Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => density μ.prob v T * f T) = ∑ T, v T * f T := by
  unfold TreeDist.expect
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← mul_assoc, mul_density hle hv]

/-- `E_μ[ρ] = p` for a thinning at mass `p`. -/
theorem TreeDist.expect_density (μ : TreeDist n x) {v : Finset (Sym2 (Fin n)) → ℝ}
    {E : Finset (Sym2 (Fin n)) → Prop} {p : ℝ} (h : IsThinning μ.prob v E p) :
    μ.expect (density μ.prob v) = p := by
  have := μ.expect_density_mul h.le h.nonneg (fun _ => 1)
  simp only [mul_one] at this
  rw [← h.total]
  exact this

/-- A thinning of an event with probability at least `p`. -/
theorem TreeDist.exists_thinning (μ : TreeDist n x) (E : Finset (Sym2 (Fin n)) → Prop)
    {p : ℝ} (hp0 : 0 ≤ p) (hpE : p ≤ μ.probEvent E) :
    IsThinning μ.prob (thinWeight μ.prob E p) E p :=
  _root_.TSPGap.exists_thinning μ.weightNonneg E hp0 (by rwa [weightMass_treeDist])

/-- The canonical thinning is uniform. -/
theorem TreeDist.exists_uniformThinning (μ : TreeDist n x) (E : Finset (Sym2 (Fin n)) → Prop)
    {p : ℝ} (hp0 : 0 ≤ p) (hpE : p ≤ μ.probEvent E) :
    IsUniformThinning μ.prob (thinWeight μ.prob E p) E p :=
  isUniformThinning_thinWeight μ.weightNonneg E hp0 (by rwa [weightMass_treeDist])

/-- `E_μ[ρ · 1_Q] = ∑_{T ∈ Q} v(T)`: the mass the thinning gives to `Q`. -/
theorem TreeDist.expect_density_indicator (μ : TreeDist n x) {v : Finset (Sym2 (Fin n)) → ℝ}
    (hle : ∀ T, v T ≤ μ.prob T) (hv : WeightNonneg v) (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.expect (fun T => density μ.prob v T * if Q T then 1 else 0) = weightMass v Q := by
  rw [μ.expect_density_mul hle hv]
  unfold weightMass
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

/-- **The uniform-thinning identity for expectations**:
`P[E] · E[ρ f] = p · E[f 1_E]`. -/
theorem TreeDist.probEvent_mul_expect_density (μ : TreeDist n x)
    {v : Finset (Sym2 (Fin n)) → ℝ} {E : Finset (Sym2 (Fin n)) → Prop} {p : ℝ}
    (h : IsUniformThinning μ.prob v E p) (f : Finset (Sym2 (Fin n)) → ℝ) :
    μ.probEvent E * μ.expect (fun T => density μ.prob v T * f T)
      = p * μ.expect (fun T => if E T then f T else 0) := by
  rw [μ.expect_density_mul h.le h.nonneg, ← weightMass_treeDist, h.sum_mul f]
  congr 1
  unfold TreeDist.expect
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hE : E T <;> simp [hE]

/-- The event form: `P[E] · E[ρ 1_Q] = p · P[E ∧ Q]`, i.e. `E[ρ 1_Q] = p · P[Q | E]`. -/
theorem TreeDist.probEvent_mul_expect_density_indicator (μ : TreeDist n x)
    {v : Finset (Sym2 (Fin n)) → ℝ} {E : Finset (Sym2 (Fin n)) → Prop} {p : ℝ}
    (h : IsUniformThinning μ.prob v E p) (Q : Finset (Sym2 (Fin n)) → Prop) :
    μ.probEvent E * μ.expect (fun T => density μ.prob v T * if Q T then 1 else 0)
      = p * μ.probEvent (fun T => E T ∧ Q T) := by
  rw [μ.expect_density_indicator h.le h.nonneg, ← weightMass_treeDist, ← weightMass_treeDist,
    h.weightMass_mul]

/-- A conditional bound `P[Q | E] ≤ c` (cross-multiplied) bounds `E[ρ 1_Q] ≤ p · c`. -/
theorem TreeDist.expect_density_indicator_le (μ : TreeDist n x)
    {v : Finset (Sym2 (Fin n)) → ℝ} {E : Finset (Sym2 (Fin n)) → Prop} {p : ℝ}
    (h : IsUniformThinning μ.prob v E p) {Q : Finset (Sym2 (Fin n)) → Prop} {c : ℝ}
    (hQ : μ.probEvent (fun T => E T ∧ Q T) ≤ c * μ.probEvent E) :
    μ.expect (fun T => density μ.prob v T * if Q T then 1 else 0) ≤ p * c := by
  rw [μ.expect_density_indicator h.le h.nonneg]
  refine h.weightMass_le μ.weightNonneg ?_
  rwa [weightMass_treeDist, weightMass_treeDist]

end TreeThinning

/-! ### Degree cuts and good edges -/

section Edges

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-- **A degree cut**, paper-facing: a cut of the hierarchy that is not a
near-cycle cut, with at least three atoms (KKO define a cut with exactly two
children to be a polygon cut). -/
structure DegreeCutData (H : Hierarchy x e₀ εη) (S : Finset (Fin n)) : Prop where
  mem : S ∈ H.cuts
  notNearCycle : ¬ H.IsNearCycleCut S
  three : 3 ≤ (H.children S).card

/-- `e` is a **good top edge**: it lies in a good bundle between two atoms
of a degree cut. -/
def IsGoodTopEdge (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ)
    (e : Sym2 (Fin n)) : Prop :=
  ∃ S, DegreeCutData H S ∧ ∃ u ∈ H.children S, ∃ u' ∈ H.children S,
    u ≠ u' ∧ e ∈ betweenEdges u u' ∧ IsGoodBundle μ ε₂ u u'

/-- `e` is a **bottom edge**: its edge parent is a near-cycle cut. -/
def IsBottomEdge (H : Hierarchy x e₀ εη) (e : Sym2 (Fin n)) : Prop :=
  ∃ S, H.IsEdgeParent e S ∧ H.IsNearCycleCut S

/-- **The good edge set `E_g`**: the bottom edges and the good top edges,
among the genuine edges inside the root. -/
noncomputable def goodEdges (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ) :
    Finset (Sym2 (Fin n)) :=
  (edgeFinset n).filter fun e =>
    EdgeInside e e₀.rootCut ∧ (IsBottomEdge H e ∨ IsGoodTopEdge H μ ε₂ e)

theorem mem_goodEdges {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ : ℝ} {e : Sym2 (Fin n)} :
    e ∈ goodEdges H μ ε₂ ↔ e ∈ edgeFinset n ∧ EdgeInside e e₀.rootCut
      ∧ (IsBottomEdge H e ∨ IsGoodTopEdge H μ ε₂ e) := by
  unfold goodEdges
  rw [Finset.mem_filter]

end Edges

/-! ### Reductions -/

section Reduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The generic pointwise bounds on a reduction** `c · xₑ · ρ(T)`:
between `0` and `c · xₑ`. -/
theorem reduction_bounds {w v : Finset ι → ℝ} (hnn : WeightNonneg w) (hv : WeightNonneg v)
    (hle : ∀ T, v T ≤ w T) {c xe : ℝ} (hc : 0 ≤ c) (hxe : 0 ≤ xe) (T : Finset ι) :
    0 ≤ c * xe * density w v T ∧ c * xe * density w v T ≤ c * xe := by
  have h0 := density_nonneg hnn hv T
  have h1 := density_le_one hnn hle T
  constructor
  · positivity
  · calc c * xe * density w v T ≤ c * xe * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c * xe := mul_one _

/-- Two reductions of the same edge from two thinnings, each with its own
weight `c/2`, stay within `c · xₑ`. -/
theorem reduction_pair_bounds {w v v' : Finset ι → ℝ} (hnn : WeightNonneg w)
    (hv : WeightNonneg v) (hle : ∀ T, v T ≤ w T) (hv' : WeightNonneg v')
    (hle' : ∀ T, v' T ≤ w T) {c xe : ℝ} (hc : 0 ≤ c) (hxe : 0 ≤ xe) (T : Finset ι) :
    0 ≤ c / 2 * xe * (density w v T + density w v' T)
    ∧ c / 2 * xe * (density w v T + density w v' T) ≤ c * xe := by
  have h0 := density_nonneg hnn hv T
  have h1 := density_le_one hnn hle T
  have h0' := density_nonneg hnn hv' T
  have h1' := density_le_one hnn hle' T
  constructor
  · positivity
  · nlinarith [mul_nonneg hc hxe]

end Reduction

end TSPGap

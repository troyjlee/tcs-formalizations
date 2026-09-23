/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Rayleigh

/-!
# Conditioning preserves the Rayleigh condition

Conditioning a coordinate out (`deleteWeight`) or in (`contractWeight`) keeps
`RayleighNonneg`, and the consequence is a family of **cross-multiplied**
conditional pairwise negative-correlation inequalities.

## One family, two ends

Both closures come from a single object: the specialization `Xₖ ↦ t`.  As
weights,

`specializeWeight w k t = deleteWeight w k + t · contractWeight w k`,

so the Rayleigh difference of the specialization is a *quadratic in `t`* whose
constant term is the Rayleigh difference of the deletion and whose leading term
is that of the contraction.  Specialization preserves `RayleighNonneg` for every
real `t` — an algebraic fact, needing no stability — and a quadratic that is
nonnegative on all of `ℝ` has a nonnegative leading coefficient.  So:

* `t = 0` gives conditioning **out**;
* the `t²` coefficient gives conditioning **in**;
* `t = 1` gives the projection that forgets `k`, essentially free.

That the contraction is `pderiv` is not a coincidence:
`genPoly (contractWeight w k) = ∂ₖ (genPoly w)`, so the same theorem is exported
as `RayleighNonneg.pderiv`, with multi-affinity as an explicit hypothesis since
`RayleighNonneg` alone does not imply it.

## Nothing is normalized

The conditional inequalities are stated cross-multiplied,

`P(e ∧ f ∧ C) · P(C) ≤ P(e ∧ C) · P(f ∧ C)`,

and no conditional `TreeDist` is constructed.  Zero-mass conditioning events are
then harmless rather than excluded — the same discipline as `Fact28.lean`, and
for the same reason: the strict hypothesis `P(C) > 0` has no business here.

Feder–Mihail is deliberately *not* in this file.
-/

namespace TSPGap

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### A quadratic nonnegative on all of `ℝ` has nonnegative leading term -/

theorem nonneg_of_quadratic_nonneg {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + b * t + c) :
    0 ≤ a := by
  by_contra ha
  push Not at ha
  have hna : 0 < -a := by linarith
  set t : ℝ := max 1 ((|b| + |c| + 1) / (-a)) with ht
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht2 : (|b| + |c| + 1) / (-a) ≤ t := le_max_right _ _
  rw [div_le_iff₀ hna] at ht2
  have hb : b ≤ |b| := le_abs_self b
  have hc : c ≤ |c| := le_abs_self c
  have h0 : (0 : ℝ) ≤ |b| := abs_nonneg b
  have h1 : (0 : ℝ) ≤ |c| := abs_nonneg c
  nlinarith [h t, ht1, ht2, hb, hc, h0, h1]

/-! ### Deletion, contraction, specialization -/

/-- Condition the coordinate `k` **out**: keep only the sets avoiding `k`.
Unnormalized. -/
noncomputable def deleteWeight (w : Finset ι → ℝ) (k : ι) : Finset ι → ℝ :=
  fun V => if k ∈ V then 0 else w V

/-- Condition the coordinate `k` **in**: keep the sets containing `k`, with `k`
removed.  Unnormalized. -/
noncomputable def contractWeight (w : Finset ι → ℝ) (k : ι) : Finset ι → ℝ :=
  fun V => if k ∈ V then 0 else w (insert k V)

/-- Substitute the constant `t` for `Xₖ`. -/
noncomputable def specializeWeight (w : Finset ι → ℝ) (k : ι) (t : ℝ) : Finset ι → ℝ :=
  fun V => if k ∈ V then 0 else w V + t * w (insert k V)

omit [Fintype ι] in
theorem deleteWeight_vanishes (w : Finset ι → ℝ) (k : ι) :
    ∀ V, k ∈ V → deleteWeight w k V = 0 := fun _ h => if_pos h

omit [Fintype ι] in
theorem contractWeight_vanishes_self (w : Finset ι → ℝ) (k : ι) :
    ∀ V, k ∈ V → contractWeight w k V = 0 := fun _ h => if_pos h

omit [Fintype ι] in
theorem specializeWeight_vanishes (w : Finset ι → ℝ) (k : ι) (t : ℝ) :
    ∀ V, k ∈ V → specializeWeight w k t V = 0 := fun _ h => if_pos h

omit [Fintype ι] in
theorem specializeWeight_zero (w : Finset ι → ℝ) (k : ι) :
    specializeWeight w k 0 = deleteWeight w k := by
  funext V
  by_cases h : k ∈ V <;> simp [specializeWeight, deleteWeight, h]

omit [Fintype ι] in
theorem specializeWeight_add (w : Finset ι → ℝ) (k : ι) (t : ℝ) :
    specializeWeight w k t = fun V => deleteWeight w k V + t * contractWeight w k V := by
  funext V
  by_cases h : k ∈ V <;> simp [specializeWeight, deleteWeight, contractWeight, h]

/-- **Contraction is differentiation.** -/
theorem genPoly_contractWeight (w : Finset ι → ℝ) (k : ι) :
    genPoly (contractWeight w k) = pderiv k (genPoly w) := (pderiv_genPoly w k).symm

/-- A weight vanishing on every set containing `k` has no `Xₖ` to differentiate. -/
theorem pderiv_eq_zero_of_vanishes {v : Finset ι → ℝ} {k : ι}
    (hv : ∀ V, k ∈ V → v V = 0) : pderiv k (genPoly v) = 0 := by
  rw [pderiv_genPoly]
  have hz : (fun U : Finset ι => if k ∈ U then (0 : ℝ) else v (insert k U)) = fun _ => 0 := by
    funext U
    by_cases h : k ∈ U
    · simp [h]
    · simp [h, hv _ (Finset.mem_insert_self k U)]
  rw [hz, genPoly]
  simp

omit [Fintype ι] in
theorem contractWeight_vanishes {v : Finset ι → ℝ} {k : ι}
    (hv : ∀ V, k ∈ V → v V = 0) (i : ι) : ∀ V, k ∈ V → contractWeight v i V = 0 := by
  intro V hk
  by_cases h : i ∈ V
  · simp [contractWeight, h]
  · simp [contractWeight, h, hv _ (Finset.mem_insert_of_mem hk)]

theorem pderiv_genPoly' (v : Finset ι → ℝ) (i : ι) :
    pderiv i (genPoly v) = genPoly (contractWeight v i) := pderiv_genPoly v i

/-! ### Evaluation -/

theorem genPoly_add (a b : Finset ι → ℝ) :
    genPoly (fun S => a S + b S) = genPoly a + genPoly b := by
  rw [genPoly, genPoly, genPoly, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by rw [map_add]; ring

theorem eval_update_of_vanishes_real {v : Finset ι → ℝ} {k : ι}
    (hv : ∀ V, k ∈ V → v V = 0) (x : ι → ℝ) (t : ℝ) :
    eval (Function.update x k t) (genPoly v) = eval x (genPoly v) := by
  rw [eval_genPoly, eval_genPoly]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : k ∈ S
  · rw [hv S hS]
    ring
  · refine congrArg _ (Finset.prod_congr rfl fun i hi => ?_)
    have hik : i ≠ k := fun h => hS (h ▸ hi)
    exact Function.update_of_ne hik _ _

/-- **The specialization is affine in `t`**, with deletion as constant term and
contraction as slope. -/
theorem eval_specializeWeight (v : Finset ι → ℝ) (k : ι) (t : ℝ) (x : ι → ℝ) :
    eval x (genPoly (specializeWeight v k t))
      = eval x (genPoly (deleteWeight v k)) + t * eval x (genPoly (contractWeight v k)) := by
  rw [specializeWeight_add, show (fun V => deleteWeight v k V + t * contractWeight v k V)
      = fun V => deleteWeight v k V + (fun U => t * contractWeight v k U) V from rfl,
    genPoly_add, ← const_mul_genPoly, map_add, map_mul, eval_C]

/-- Specializing `Xₖ` to `t` is evaluating with the `k`-coordinate set to `t`. -/
theorem eval_genPoly_specializeWeight (w : Finset ι → ℝ) (k : ι) (t : ℝ) (x : ι → ℝ) :
    eval x (genPoly (specializeWeight w k t)) = eval (Function.update x k t) (genPoly w) := by
  rw [eval_specializeWeight]
  conv_rhs => rw [genPoly_split w k]
  rw [map_add, map_mul, eval_X, Function.update_self,
    show (fun U : Finset ι => if k ∈ U then (0 : ℝ) else w (insert k U))
      = contractWeight w k from rfl,
    show (fun U : Finset ι => if k ∈ U then (0 : ℝ) else w U) = deleteWeight w k from rfl,
    eval_update_of_vanishes_real (contractWeight_vanishes_self w k),
    eval_update_of_vanishes_real (deleteWeight_vanishes w k)]
  ring

/-! ### Specialization and contraction commute with the sectors

These are pure weight identities: no generating polynomial appears, so `Fintype`
is not needed. -/

section WeightComm

omit [Fintype ι]

/-- The generic commutation: a sector is `w ∘ g` masked by a predicate `P`, and
both are blind to the coordinate `k`. -/
theorem specialize_comm {w : Finset ι → ℝ} {k : ι} (P : Finset ι → Prop) [DecidablePred P]
    (g : Finset ι → Finset ι) (hgmem : ∀ V, k ∈ g V ↔ k ∈ V)
    (hgins : ∀ V, g (insert k V) = insert k (g V)) (hP : ∀ V, P (insert k V) ↔ P V) (t : ℝ) :
    (fun V => if P V then (0 : ℝ) else specializeWeight w k t (g V))
      = specializeWeight (fun V => if P V then 0 else w (g V)) k t := by
  funext V
  by_cases hk : k ∈ V
  · simp [specializeWeight, hk, (hgmem V).mpr hk]
  · by_cases hp : P V
    · simp [specializeWeight, hk, hp, (hP V).mpr hp]
    · have h1 : k ∉ g V := fun h => hk ((hgmem V).mp h)
      have h2 : ¬ P (insert k V) := fun h => hp ((hP V).mp h)
      simp only [specializeWeight, hk, hp, h1, h2, if_false, hgins]

theorem contract_comm {w : Finset ι → ℝ} {k : ι} (P : Finset ι → Prop) [DecidablePred P]
    (g : Finset ι → Finset ι) (hgmem : ∀ V, k ∈ g V ↔ k ∈ V)
    (hgins : ∀ V, g (insert k V) = insert k (g V)) (hP : ∀ V, P (insert k V) ↔ P V) :
    (fun V => if P V then (0 : ℝ) else contractWeight w k (g V))
      = contractWeight (fun V => if P V then 0 else w (g V)) k := by
  funext V
  by_cases hk : k ∈ V
  · simp [contractWeight, hk, (hgmem V).mpr hk]
  · by_cases hp : P V
    · simp [contractWeight, hk, hp, (hP V).mpr hp]
    · have h1 : k ∉ g V := fun h => hk ((hgmem V).mp h)
      have h2 : ¬ P (insert k V) := fun h => hp ((hP V).mp h)
      simp only [contractWeight, hk, hp, h1, h2, if_false, hgins]

section Sectors

variable {w : Finset ι → ℝ} {i j k : ι}

private theorem hPij (hik : i ≠ k) (hjk : j ≠ k) (V : Finset ι) :
    (i ∈ insert k V ∨ j ∈ insert k V) ↔ (i ∈ V ∨ j ∈ V) := by
  simp [Finset.mem_insert, hik, hjk]

theorem sectorA_specialize (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    sectorA (specializeWeight w k t) i j = specializeWeight (sectorA w i j) k t :=
  specialize_comm _ (fun V => insert i (insert j V))
    (fun V => by simp [Finset.mem_insert, Ne.symm hik, Ne.symm hjk])
    (fun V => by rw [Finset.insert_comm j k, Finset.insert_comm i k]) (hPij hik hjk) t

theorem sectorB_specialize (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    sectorB (specializeWeight w k t) i j = specializeWeight (sectorB w i j) k t :=
  specialize_comm _ (fun V => insert i V)
    (fun V => by simp [Finset.mem_insert, Ne.symm hik])
    (fun V => Finset.insert_comm i k V) (hPij hik hjk) t

theorem sectorC_specialize (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    sectorC (specializeWeight w k t) i j = specializeWeight (sectorC w i j) k t :=
  specialize_comm _ (fun V => insert j V)
    (fun V => by simp [Finset.mem_insert, Ne.symm hjk])
    (fun V => Finset.insert_comm j k V) (hPij hik hjk) t

theorem sectorD_specialize (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    sectorD (specializeWeight w k t) i j = specializeWeight (sectorD w i j) k t :=
  specialize_comm _ (fun V => V) (fun _ => Iff.rfl) (fun _ => rfl) (hPij hik hjk) t

theorem sectorA_contract (hik : i ≠ k) (hjk : j ≠ k) :
    sectorA (contractWeight w k) i j = contractWeight (sectorA w i j) k :=
  contract_comm _ (fun V => insert i (insert j V))
    (fun V => by simp [Finset.mem_insert, Ne.symm hik, Ne.symm hjk])
    (fun V => by rw [Finset.insert_comm j k, Finset.insert_comm i k]) (hPij hik hjk)

theorem sectorB_contract (hik : i ≠ k) (hjk : j ≠ k) :
    sectorB (contractWeight w k) i j = contractWeight (sectorB w i j) k :=
  contract_comm _ (fun V => insert i V)
    (fun V => by simp [Finset.mem_insert, Ne.symm hik])
    (fun V => Finset.insert_comm i k V) (hPij hik hjk)

theorem sectorC_contract (hik : i ≠ k) (hjk : j ≠ k) :
    sectorC (contractWeight w k) i j = contractWeight (sectorC w i j) k :=
  contract_comm _ (fun V => insert j V)
    (fun V => by simp [Finset.mem_insert, Ne.symm hjk])
    (fun V => Finset.insert_comm j k V) (hPij hik hjk)

theorem sectorD_contract (hik : i ≠ k) (hjk : j ≠ k) :
    sectorD (contractWeight w k) i j = contractWeight (sectorD w i j) k :=
  contract_comm _ (fun V => V) (fun _ => Iff.rfl) (fun _ => rfl) (hPij hik hjk)

end Sectors

end WeightComm

/-! ### Specialization preserves the Rayleigh condition -/

/-- **Specializing a coordinate to any real value preserves `RayleighNonneg`.**
Purely algebraic: no stability is used. -/
theorem rayleighNonneg_specializeWeight {w : Finset ι → ℝ}
    (hR : RayleighNonneg (genPoly w)) (k : ι) (t : ℝ) :
    RayleighNonneg (genPoly (specializeWeight w k t)) := by
  intro i j x
  by_cases hij : i = j
  · subst hij
    rw [rayleighDiff, pderiv_pderiv_self_genPoly, mul_zero, sub_zero, map_mul]
    exact mul_self_nonneg _
  by_cases hik : i = k
  · subst hik
    rw [rayleighDiff, pderiv_eq_zero_of_vanishes (specializeWeight_vanishes w i t),
      zero_mul, map_zero, mul_zero, sub_zero, map_zero]
  by_cases hjk : j = k
  · subst hjk
    rw [rayleighDiff, pderiv_eq_zero_of_vanishes (specializeWeight_vanishes w j t), mul_zero,
      pderiv_genPoly',
      pderiv_eq_zero_of_vanishes (contractWeight_vanishes (specializeWeight_vanishes w j t) i),
      mul_zero, sub_zero, map_zero]
  · rw [rayleighDiff_genPoly _ hij, map_sub, map_mul, map_mul,
      sectorA_specialize hik hjk, sectorB_specialize hik hjk,
      sectorC_specialize hik hjk, sectorD_specialize hik hjk,
      eval_genPoly_specializeWeight, eval_genPoly_specializeWeight,
      eval_genPoly_specializeWeight, eval_genPoly_specializeWeight]
    have h := hR i j (Function.update x k t)
    rwa [rayleighDiff_genPoly _ hij, map_sub, map_mul, map_mul] at h

/-- **Conditioning out**: the `t = 0` specialization. -/
theorem rayleighNonneg_deleteWeight {w : Finset ι → ℝ}
    (hR : RayleighNonneg (genPoly w)) (k : ι) :
    RayleighNonneg (genPoly (deleteWeight w k)) := by
  rw [← specializeWeight_zero]
  exact rayleighNonneg_specializeWeight hR k 0

/-- **Forgetting `k`**: the `t = 1` specialization, which sums the two branches. -/
theorem rayleighNonneg_projectWeight {w : Finset ι → ℝ}
    (hR : RayleighNonneg (genPoly w)) (k : ι) :
    RayleighNonneg (genPoly (fun V => if k ∈ V then 0 else w V + w (insert k V))) := by
  have heq : (fun V : Finset ι => if k ∈ V then (0 : ℝ) else w V + w (insert k V))
      = specializeWeight w k 1 := by
    funext V
    by_cases h : k ∈ V <;> simp [specializeWeight, h]
  rw [heq]
  exact rayleighNonneg_specializeWeight hR k 1

set_option maxHeartbeats 1000000 in
/-- **Conditioning in**: the leading `t²` coefficient of the specialized Rayleigh
difference is the Rayleigh difference of the contraction, and a quadratic
nonnegative on all of `ℝ` has a nonnegative leading coefficient. -/
theorem rayleighNonneg_contractWeight {w : Finset ι → ℝ}
    (hR : RayleighNonneg (genPoly w)) (k : ι) :
    RayleighNonneg (genPoly (contractWeight w k)) := by
  intro i j x
  by_cases hij : i = j
  · subst hij
    rw [rayleighDiff, pderiv_pderiv_self_genPoly, mul_zero, sub_zero, map_mul]
    exact mul_self_nonneg _
  by_cases hik : i = k
  · subst hik
    rw [rayleighDiff, pderiv_eq_zero_of_vanishes (contractWeight_vanishes_self w i),
      zero_mul, map_zero, mul_zero, sub_zero, map_zero]
  by_cases hjk : j = k
  · subst hjk
    rw [rayleighDiff, pderiv_eq_zero_of_vanishes (contractWeight_vanishes_self w j), mul_zero,
      pderiv_genPoly',
      pderiv_eq_zero_of_vanishes (contractWeight_vanishes (contractWeight_vanishes_self w j) i),
      mul_zero, sub_zero, map_zero]
  · have hquad : ∀ t : ℝ, 0 ≤
        (eval x (genPoly (contractWeight (sectorB w i j) k))
            * eval x (genPoly (contractWeight (sectorC w i j) k))
          - eval x (genPoly (contractWeight (sectorA w i j) k))
            * eval x (genPoly (contractWeight (sectorD w i j) k))) * t ^ 2
        + (eval x (genPoly (deleteWeight (sectorB w i j) k))
              * eval x (genPoly (contractWeight (sectorC w i j) k))
            + eval x (genPoly (contractWeight (sectorB w i j) k))
              * eval x (genPoly (deleteWeight (sectorC w i j) k))
            - eval x (genPoly (deleteWeight (sectorA w i j) k))
              * eval x (genPoly (contractWeight (sectorD w i j) k))
            - eval x (genPoly (contractWeight (sectorA w i j) k))
              * eval x (genPoly (deleteWeight (sectorD w i j) k))) * t
        + (eval x (genPoly (deleteWeight (sectorB w i j) k))
              * eval x (genPoly (deleteWeight (sectorC w i j) k))
            - eval x (genPoly (deleteWeight (sectorA w i j) k))
              * eval x (genPoly (deleteWeight (sectorD w i j) k))) := by
      intro t
      have h := rayleighNonneg_specializeWeight hR k t i j x
      rw [rayleighDiff_genPoly _ hij, map_sub, map_mul, map_mul,
        sectorA_specialize hik hjk, sectorB_specialize hik hjk,
        sectorC_specialize hik hjk, sectorD_specialize hik hjk,
        eval_specializeWeight, eval_specializeWeight, eval_specializeWeight,
        eval_specializeWeight] at h
      exact le_of_le_of_eq h (by ring)
    have hlead := nonneg_of_quadratic_nonneg hquad
    rw [rayleighDiff_genPoly _ hij, map_sub, map_mul, map_mul,
      sectorA_contract hik hjk, sectorB_contract hik hjk,
      sectorC_contract hik hjk, sectorD_contract hik hjk]
    exact hlead

/-- **`RayleighNonneg` survives differentiation.**  Multi-affinity is an explicit
hypothesis: `RayleighNonneg` alone does not imply it. -/
theorem RayleighNonneg.pderiv {p : MvPolynomial ι ℝ} (hR : RayleighNonneg p)
    (hma : IsMultiAffine p) (k : ι) : RayleighNonneg (MvPolynomial.pderiv k p) := by
  rw [← genPoly_coeff_self hma] at hR ⊢
  rw [← genPoly_contractWeight]
  exact rayleighNonneg_contractWeight hR k

/-! ### Cross-multiplied pairwise negative correlation

Unnormalized throughout: no conditional distribution is built, so a
conditioning event of mass zero is harmless rather than excluded.

⚠️ For a **nonnegative** weight — `TreeDist.prob` in the application — zero
conditioning mass forces every sub-sum to vanish too, so both sides are `0` and
the inequality is trivially true.  For a general signed weight that is *not* so:
cancellation can give the conditioning event mass zero while the other sums stay
nonzero.  The statement remains meaningful there, but the degeneracy claim needs
nonnegativity. -/

/-- Pairwise negative correlation for any Rayleigh weight, cross-multiplied and
unnormalized. -/
theorem negCorrelation_of_rayleighNonneg {w : Finset ι → ℝ}
    (hR : RayleighNonneg (genPoly w)) {e f : ι} (hef : e ≠ f) :
    (∑ S : Finset ι, w S) * (∑ S ∈ Finset.univ.filter (fun S => e ∈ S ∧ f ∈ S), w S)
      ≤ (∑ S ∈ Finset.univ.filter (fun S => e ∈ S), w S)
        * ∑ S ∈ Finset.univ.filter (fun S => f ∈ S), w S := by
  have h1 := hR e f (fun _ => (1 : ℝ))
  rw [rayleighDiff, pderiv_pderiv_genPoly _ hef, pderiv_genPoly, pderiv_genPoly,
    map_sub, map_mul, map_mul, eval_one_genPoly, eval_one_genPoly, eval_one_genPoly,
    eval_one_genPoly, sum_pderiv_weight, sum_pderiv_weight, sum_sectorA _ hef] at h1
  linarith

theorem sum_contractWeight (w : Finset ι → ℝ) (k : ι) :
    ∑ V : Finset ι, contractWeight w k V
      = ∑ S ∈ Finset.univ.filter (fun S => k ∈ S), w S := sum_pderiv_weight w k

theorem sum_deleteWeight (w : Finset ι → ℝ) (k : ι) :
    ∑ V : Finset ι, deleteWeight w k V
      = ∑ S ∈ Finset.univ.filter (fun S => k ∉ S), w S := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  by_cases hk : k ∈ V <;> simp [deleteWeight, hk]

/-- Contracting `k` shifts a filtered sum to the sets containing `k`. -/
theorem sum_filter_contractWeight (w : Finset ι → ℝ) (k : ι) (P : Finset ι → Prop)
    [DecidablePred P] (hP : ∀ V : Finset ι, k ∉ V → (P (insert k V) ↔ P V)) :
    ∑ V ∈ Finset.univ.filter P, contractWeight w k V
      = ∑ S ∈ Finset.univ.filter (fun S => k ∈ S ∧ P S), w S := by
  classical
  have hL : ∑ V ∈ Finset.univ.filter P, contractWeight w k V
      = ∑ V ∈ Finset.univ.filter (fun V => k ∉ V ∧ P V), w (insert k V) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun V _ => ?_
    by_cases hk : k ∈ V
    · simp [contractWeight, hk]
    · by_cases hp : P V <;> simp [contractWeight, hk, hp]
  rw [hL]
  refine Finset.sum_nbij' (fun V => insert k V) (fun S => S.erase k) ?_ ?_ ?_ ?_ ?_
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV ⊢
    exact ⟨Finset.mem_insert_self k V, (hP V hV.1).mpr hV.2⟩
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    refine ⟨Finset.notMem_erase k S, ?_⟩
    have hIn : insert k (S.erase k) = S := Finset.insert_erase hS.1
    exact (hP _ (Finset.notMem_erase k S)).mp (by rw [hIn]; exact hS.2)
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
    exact Finset.erase_insert hV.1
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.insert_erase hS.1
  · intro V _
    rfl

/-- Deleting `k` restricts a filtered sum to the sets avoiding `k`. -/
theorem sum_filter_deleteWeight (w : Finset ι → ℝ) (k : ι) (P : Finset ι → Prop)
    [DecidablePred P] :
    ∑ V ∈ Finset.univ.filter P, deleteWeight w k V
      = ∑ S ∈ Finset.univ.filter (fun S => k ∉ S ∧ P S), w S := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  by_cases hk : k ∈ V
  · simp [deleteWeight, hk]
  · by_cases hp : P V <;> simp [deleteWeight, hk, hp]

/-- **Conditional pairwise negative correlation, conditioned in.**  Cross
multiplied, so a conditioning event of mass zero is harmless. -/
theorem negCorrelation_contract {w : Finset ι → ℝ} (hR : RayleighNonneg (genPoly w))
    {e f k : ι} (hef : e ≠ f) (hek : e ≠ k) (hfk : f ≠ k) :
    (∑ S ∈ Finset.univ.filter (fun S => k ∈ S), w S)
        * (∑ S ∈ Finset.univ.filter (fun S => k ∈ S ∧ (e ∈ S ∧ f ∈ S)), w S)
      ≤ (∑ S ∈ Finset.univ.filter (fun S => k ∈ S ∧ e ∈ S), w S)
        * ∑ S ∈ Finset.univ.filter (fun S => k ∈ S ∧ f ∈ S), w S := by
  classical
  have h := negCorrelation_of_rayleighNonneg (rayleighNonneg_contractWeight hR k) hef
  rw [sum_contractWeight,
    sum_filter_contractWeight w k (fun S => e ∈ S ∧ f ∈ S)
      (fun V _ => by simp [Finset.mem_insert, hek, hfk]),
    sum_filter_contractWeight w k (fun S => e ∈ S)
      (fun V _ => by simp [Finset.mem_insert, hek]),
    sum_filter_contractWeight w k (fun S => f ∈ S)
      (fun V _ => by simp [Finset.mem_insert, hfk])] at h
  exact h

/-- **Conditional pairwise negative correlation, conditioned out.** -/
theorem negCorrelation_delete {w : Finset ι → ℝ} (hR : RayleighNonneg (genPoly w))
    {e f k : ι} (hef : e ≠ f) :
    (∑ S ∈ Finset.univ.filter (fun S => k ∉ S), w S)
        * (∑ S ∈ Finset.univ.filter (fun S => k ∉ S ∧ (e ∈ S ∧ f ∈ S)), w S)
      ≤ (∑ S ∈ Finset.univ.filter (fun S => k ∉ S ∧ e ∈ S), w S)
        * ∑ S ∈ Finset.univ.filter (fun S => k ∉ S ∧ f ∈ S), w S := by
  classical
  have h := negCorrelation_of_rayleighNonneg (rayleighNonneg_deleteWeight hR k) hef
  rw [sum_deleteWeight, sum_filter_deleteWeight w k (fun S => e ∈ S ∧ f ∈ S),
    sum_filter_deleteWeight w k (fun S => e ∈ S),
    sum_filter_deleteWeight w k (fun S => f ∈ S)] at h
  exact h

/-! ### The exports -/

open Classical in
/-- **Conditional pairwise negative correlation at the max-entropy limit**,
conditioned on an edge being *in* the tree.  Cross-multiplied: no conditional
distribution is built and no positivity is assumed. -/
theorem IsMaxEntropyLimit.negCorrelation_contract {n : ℕ} {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (h : IsMaxEntropyLimit μ) {e f k : Sym2 (Fin n)}
    (hef : e ≠ f) (hek : e ≠ k) (hfk : f ≠ k) :
    μ.probEvent (fun T => k ∈ T) * μ.probEvent (fun T => k ∈ T ∧ (e ∈ T ∧ f ∈ T))
      ≤ μ.probEvent (fun T => k ∈ T ∧ e ∈ T) * μ.probEvent (fun T => k ∈ T ∧ f ∈ T) := by
  rw [probEvent_filter, probEvent_filter, probEvent_filter, probEvent_filter]
  exact _root_.TSPGap.negCorrelation_contract
    (rayleighNonneg_genPoly h.treeRealStable) hef hek hfk

open Classical in
/-- The same, conditioned on an edge being *out* of the tree. -/
theorem IsMaxEntropyLimit.negCorrelation_delete {n : ℕ} {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (h : IsMaxEntropyLimit μ) {e f k : Sym2 (Fin n)} (hef : e ≠ f) :
    μ.probEvent (fun T => k ∉ T) * μ.probEvent (fun T => k ∉ T ∧ (e ∈ T ∧ f ∈ T))
      ≤ μ.probEvent (fun T => k ∉ T ∧ e ∈ T) * μ.probEvent (fun T => k ∉ T ∧ f ∈ T) := by
  rw [probEvent_filter, probEvent_filter, probEvent_filter, probEvent_filter]
  exact _root_.TSPGap.negCorrelation_delete (rayleighNonneg_genPoly h.treeRealStable) hef

end TSPGap

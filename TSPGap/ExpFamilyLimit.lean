/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The exponential-family limit: every marginal vector is a limit of Gibbs distributions

For a finite family `Ω` of configurations — subsets of a finite type `ι` — and a parameter
`θ : ι → ℝ`, the **Gibbs distribution** gives `ω ∈ Ω` probability proportional to
`exp (∑ e ∈ ω, θ e) = ∏ e ∈ ω, exp (θ e)`; its **marginal** at `e` is the probability that
`e ∈ ω`.  `IsMarginalOf Ω p x` says `p` is a probability vector on `Ω` with marginals `x`.

`exists_gibbs_limit`: if `x` is the marginal vector of *some* probability vector on `Ω`, it
is the marginal vector of one that is a pointwise limit of Gibbs distributions.  This is the
closure of the exponential family; on the boundary of the marginal polytope no exact
Gibbs representation need exist, and none is claimed.

The proof needs no relative interior.  With `f θ := log Z(θ) − ⟨θ, x⟩ ≥ 0` (Jensen-free: each
`⟨θ, 1_ω⟩ ≤ log Z`), the penalized `g_k θ := f θ + (1/k)‖θ‖²` has a global minimizer `θ_k`,
bounded by `‖θ_k‖_∞² ≤ k log|Ω| + 1` because outside that ball `g_k > log|Ω| = g_k 0`.  Its
coordinate derivatives vanish, which reads `marginal θ_k = x − (2/k) θ_k`, and the
correction tends to `0`.  A convergent subsequence of the Gibbs vectors in the compact cube
`[0,1]^Ω` is the required limit.
-/

namespace TSPGap
namespace ExpFamily

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Gibbs distributions -/

/-- The weight `exp (∑ e ∈ ω, θ e)` of a configuration. -/
noncomputable def expWeight (θ : ι → ℝ) (ω : Finset ι) : ℝ := Real.exp (∑ e ∈ ω, θ e)

/-- The partition function. -/
noncomputable def partition (Ω : Finset (Finset ι)) (θ : ι → ℝ) : ℝ := ∑ ω ∈ Ω, expWeight θ ω

/-- The Gibbs distribution on `Ω`, extended by `0`. -/
noncomputable def gibbs (Ω : Finset (Finset ι)) (θ : ι → ℝ) (ω : Finset ι) : ℝ :=
  if ω ∈ Ω then expWeight θ ω / partition Ω θ else 0

/-- The marginal of the Gibbs distribution at `e`. -/
noncomputable def marginal (Ω : Finset (Finset ι)) (θ : ι → ℝ) (e : ι) : ℝ :=
  ∑ ω ∈ Ω.filter (fun ω => e ∈ ω), gibbs Ω θ ω

/-- A probability vector on `Ω` with marginals `x`. -/
structure IsMarginalOf (Ω : Finset (Finset ι)) (p : Finset ι → ℝ) (x : ι → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ p ω
  support : ∀ ω, p ω ≠ 0 → ω ∈ Ω
  total : ∑ ω ∈ Ω, p ω = 1
  marginal : ∀ e, ∑ ω ∈ Ω.filter (fun ω => e ∈ ω), p ω = x e

variable {Ω : Finset (Finset ι)}

theorem expWeight_pos (θ : ι → ℝ) (ω : Finset ι) : 0 < expWeight θ ω := Real.exp_pos _

theorem partition_pos (hΩ : Ω.Nonempty) (θ : ι → ℝ) : 0 < partition Ω θ :=
  sum_pos (fun ω _ => expWeight_pos θ ω) hΩ

theorem expWeight_le_partition {ω : Finset ι} (hω : ω ∈ Ω) (θ : ι → ℝ) :
    expWeight θ ω ≤ partition Ω θ :=
  single_le_sum (fun ω _ => (expWeight_pos θ ω).le) hω

theorem gibbs_nonneg (hΩ : Ω.Nonempty) (θ : ι → ℝ) (ω : Finset ι) : 0 ≤ gibbs Ω θ ω := by
  unfold gibbs
  split_ifs
  · exact div_nonneg (expWeight_pos θ ω).le (partition_pos hΩ θ).le
  · exact le_rfl

theorem gibbs_le_one (hΩ : Ω.Nonempty) (θ : ι → ℝ) (ω : Finset ι) : gibbs Ω θ ω ≤ 1 := by
  unfold gibbs
  split_ifs with h
  · exact (div_le_one (partition_pos hΩ θ)).mpr (expWeight_le_partition h θ)
  · exact zero_le_one

theorem gibbs_of_notMem (θ : ι → ℝ) {ω : Finset ι} (hω : ω ∉ Ω) : gibbs Ω θ ω = 0 := by
  simp [gibbs, hω]

theorem gibbs_of_mem (θ : ι → ℝ) {ω : Finset ι} (hω : ω ∈ Ω) :
    gibbs Ω θ ω = expWeight θ ω / partition Ω θ := by
  simp [gibbs, hω]

theorem sum_gibbs (hΩ : Ω.Nonempty) (θ : ι → ℝ) : ∑ ω ∈ Ω, gibbs Ω θ ω = 1 := by
  rw [sum_congr rfl fun ω hω => gibbs_of_mem θ hω, ← sum_div]
  exact div_self (partition_pos hΩ θ).ne'

/-- The Gibbs distribution is a probability vector on `Ω` with its own marginals. -/
theorem gibbs_isMarginalOf (hΩ : Ω.Nonempty) (θ : ι → ℝ) :
    IsMarginalOf Ω (gibbs Ω θ) (marginal Ω θ) where
  nonneg := gibbs_nonneg hΩ θ
  support := fun ω h => by
    by_contra hω
    exact h (gibbs_of_notMem θ hω)
  total := sum_gibbs hΩ θ
  marginal := fun _ => rfl

/-! ### The log-partition function bounds the inner product -/

/-- `log Z`. -/
noncomputable def logPart (Ω : Finset (Finset ι)) (θ : ι → ℝ) : ℝ := Real.log (partition Ω θ)

theorem sum_le_logPart (hΩ : Ω.Nonempty) (θ : ι → ℝ) {ω : Finset ι} (hω : ω ∈ Ω) :
    ∑ e ∈ ω, θ e ≤ logPart Ω θ := by
  rw [logPart, Real.le_log_iff_exp_le (partition_pos hΩ θ)]
  exact expWeight_le_partition hω θ

theorem inner_eq_sum (θ : ι → ℝ) {q : Finset ι → ℝ} {x : ι → ℝ} (hq : IsMarginalOf Ω q x) :
    ∑ e, θ e * x e = ∑ ω ∈ Ω, q ω * ∑ e ∈ ω, θ e := by
  calc ∑ e, θ e * x e = ∑ e, ∑ ω ∈ Ω, (if e ∈ ω then θ e * q ω else 0) := by
        refine sum_congr rfl fun e _ => ?_
        rw [← hq.marginal e, mul_sum, sum_filter]
    _ = ∑ ω ∈ Ω, ∑ e, (if e ∈ ω then θ e * q ω else 0) := sum_comm
    _ = ∑ ω ∈ Ω, q ω * ∑ e ∈ ω, θ e := by
        refine sum_congr rfl fun ω _ => ?_
        rw [mul_sum, ← sum_filter]
        rw [show (univ.filter fun e => e ∈ ω) = ω from by ext; simp]
        exact sum_congr rfl fun e _ => mul_comm _ _

/-- For a marginal vector `x`, `⟨θ, x⟩ ≤ log Z(θ)`. -/
theorem inner_le_logPart (hΩ : Ω.Nonempty) {q : Finset ι → ℝ} {x : ι → ℝ}
    (hq : IsMarginalOf Ω q x) (θ : ι → ℝ) : ∑ e, θ e * x e ≤ logPart Ω θ := by
  rw [inner_eq_sum θ hq]
  calc ∑ ω ∈ Ω, q ω * ∑ e ∈ ω, θ e ≤ ∑ ω ∈ Ω, q ω * logPart Ω θ :=
        sum_le_sum fun ω hω =>
          mul_le_mul_of_nonneg_left (sum_le_logPart hΩ θ hω) (hq.nonneg ω)
    _ = logPart Ω θ := by rw [← sum_mul, hq.total, one_mul]

/-! ### The penalized objective and its minimizers -/

/-- `log Z(θ) − ⟨θ, x⟩ + (1/k)‖θ‖²`. -/
noncomputable def obj (Ω : Finset (Finset ι)) (x : ι → ℝ) (k : ℕ) (θ : ι → ℝ) : ℝ :=
  logPart Ω θ - ∑ e, θ e * x e + (1 / k) * ∑ e, θ e ^ 2

theorem continuous_partition (Ω : Finset (Finset ι)) : Continuous (partition Ω) := by
  unfold partition expWeight
  exact continuous_finsetSum _ fun ω _ =>
    Real.continuous_exp.comp (continuous_finsetSum _ fun e _ => continuous_apply e)

theorem continuous_logPart (hΩ : Ω.Nonempty) : Continuous (logPart Ω) :=
  (continuous_partition Ω).log fun θ => (partition_pos hΩ θ).ne'

theorem continuous_obj (hΩ : Ω.Nonempty) (x : ι → ℝ) (k : ℕ) : Continuous (obj Ω x k) := by
  unfold obj
  refine ((continuous_logPart hΩ).sub ?_).add (continuous_const.mul ?_)
  · exact continuous_finsetSum _ fun e _ => (continuous_apply e).mul continuous_const
  · exact continuous_finsetSum _ fun e _ => (continuous_apply e).pow 2

theorem obj_zero (Ω : Finset (Finset ι)) (x : ι → ℝ) (k : ℕ) :
    obj Ω x k 0 = Real.log (Ω.card : ℝ) := by
  simp [obj, logPart, partition, expWeight]

theorem le_obj (hΩ : Ω.Nonempty) {q : Finset ι → ℝ} {x : ι → ℝ} (hq : IsMarginalOf Ω q x)
    (k : ℕ) (θ : ι → ℝ) : (1 / k) * ∑ e, θ e ^ 2 ≤ obj Ω x k θ := by
  have := inner_le_logPart hΩ hq θ
  unfold obj
  linarith

/-- The penalized objective has a global minimizer, in the sup-norm ball of radius
`√(k log|Ω| + 1)`. -/
theorem exists_isMinOn_obj (hΩ : Ω.Nonempty) {q : Finset ι → ℝ} {x : ι → ℝ}
    (hq : IsMarginalOf Ω q x) {k : ℕ} (hk : 0 < k) :
    ∃ θ : ι → ℝ, IsMinOn (obj Ω x k) Set.univ θ ∧
      ∀ e, θ e ^ 2 ≤ k * Real.log (Ω.card : ℝ) + 1 := by
  set L := Real.log (Ω.card : ℝ) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hΩ.card_pos)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set R := Real.sqrt (k * L + 1) with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = k * L + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨θ, hθmem, hθmin⟩ := (isCompact_closedBall (0 : ι → ℝ) R).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hR0⟩ (continuous_obj hΩ x k).continuousOn
  have hball : ∀ ψ : ι → ℝ, ψ ∈ Metric.closedBall (0 : ι → ℝ) R ↔ ∀ e, |ψ e| ≤ R := by
    intro ψ
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
    simp [Real.norm_eq_abs]
  refine ⟨θ, isMinOn_iff.mpr fun ψ _ => ?_, fun e => ?_⟩
  · by_cases hψ : ψ ∈ Metric.closedBall (0 : ι → ℝ) R
    · exact isMinOn_iff.mp hθmin ψ hψ
    · rw [hball, not_forall] at hψ
      obtain ⟨e, he⟩ := hψ
      rw [not_le] at he
      have h1 : R ^ 2 < ψ e ^ 2 := by
        have := mul_self_lt_mul_self hR0 he
        rw [abs_mul_abs_self] at this
        nlinarith
      have h2 : ψ e ^ 2 ≤ ∑ e', ψ e' ^ 2 :=
        single_le_sum (fun e' _ => sq_nonneg (ψ e')) (mem_univ e)
      have h3 : L < (1 / k) * ∑ e', ψ e' ^ 2 := by
        rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hk']
        nlinarith
      have h4 := le_obj hΩ hq k ψ
      have h5 : obj Ω x k θ ≤ obj Ω x k 0 :=
        isMinOn_iff.mp hθmin 0 (Metric.mem_closedBall_self hR0)
      rw [obj_zero] at h5
      linarith
  · have h := (hball θ).mp hθmem e
    have h' := mul_self_le_mul_self (abs_nonneg _) h
    rw [abs_mul_abs_self] at h'
    nlinarith

/-! ### Stationarity: the coordinate derivatives -/

/-- The objective along the coordinate line through `θ` in direction `e`, in explicit form. -/
theorem obj_line_eq (Ω : Finset (Finset ι)) (x : ι → ℝ) (k : ℕ) (θ : ι → ℝ) (e : ι) (t : ℝ) :
    obj Ω x k (θ + t • Pi.single e 1) =
      Real.log (∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + t * (if e ∈ ω then 1 else 0)))
        - (∑ e', θ e' * x e' + t * x e)
        + (1 / k) * (∑ e', θ e' ^ 2 + 2 * θ e * t + t ^ 2) := by
  have h1 : ∀ ω : Finset ι, ∑ e' ∈ ω, (θ + t • Pi.single e 1 : ι → ℝ) e' =
      ∑ e' ∈ ω, θ e' + t * (if e ∈ ω then 1 else 0) := by
    intro ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, sum_add_distrib,
      mul_ite, mul_one, mul_zero, sum_ite_eq']
  have h2 : ∑ e', (θ + t • Pi.single e 1 : ι → ℝ) e' * x e' = ∑ e', θ e' * x e' + t * x e := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, add_mul,
      sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ,
      if_true]
  have h3 : ∑ e', (θ + t • Pi.single e 1 : ι → ℝ) e' ^ 2 =
      ∑ e', θ e' ^ 2 + 2 * θ e * t + t ^ 2 := by
    have : ∀ e', (θ + t • Pi.single e 1 : ι → ℝ) e' ^ 2 =
        θ e' ^ 2 + (if e' = e then 2 * θ e * t + t ^ 2 else 0) := by
      intro e'
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [this, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    ring
  have h4 : ∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, (θ + t • Pi.single e 1 : ι → ℝ) e') =
      ∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + t * (if e ∈ ω then 1 else 0)) :=
    sum_congr rfl fun ω _ => by rw [h1 ω]
  unfold obj logPart partition expWeight
  rw [h2, h3, h4]

/-- The derivative of the objective along a coordinate line, at the base point. -/
theorem hasDerivAt_obj_line (hΩ : Ω.Nonempty) (x : ι → ℝ) (k : ℕ) (θ : ι → ℝ) (e : ι) :
    HasDerivAt (fun t : ℝ => obj Ω x k (θ + t • Pi.single e 1))
      (marginal Ω θ e - x e + (1 / k) * (2 * θ e)) 0 := by
  simp_rw [obj_line_eq]
  set ind : Finset ι → ℝ := fun ω => if e ∈ ω then 1 else 0 with hind
  have hsum : HasDerivAt (fun t : ℝ => ∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + t * ind ω))
      (∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + 0 * ind ω) * (1 * ind ω)) 0 :=
    HasDerivAt.fun_sum fun ω _ => (((hasDerivAt_id' (0 : ℝ)).mul_const (ind ω)).const_add _).exp
  have hpos : ∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + 0 * ind ω) ≠ 0 := by
    refine (sum_pos (fun ω _ => Real.exp_pos _) hΩ).ne'
  have hlog := hsum.log hpos
  have hlin : HasDerivAt (fun t : ℝ => ∑ e', θ e' * x e' + t * x e) (1 * x e) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).mul_const (x e)).const_add _
  have hquad := (((hasDerivAt_id' (0 : ℝ)).const_mul (2 * θ e)).const_add
    (∑ e', θ e' ^ 2)).add (hasDerivAt_pow 2 (0 : ℝ))
  refine ((hlog.sub hlin).add (hquad.const_mul ((1 : ℝ) / k))).congr_deriv ?_
  -- the derivative is the marginal
  have hm : marginal Ω θ e = (∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + 0 * ind ω) * (1 * ind ω)) /
      ∑ ω ∈ Ω, Real.exp (∑ e' ∈ ω, θ e' + 0 * ind ω) := by
    simp only [zero_mul, add_zero, one_mul]
    rw [marginal, sum_congr rfl fun ω hω => gibbs_of_mem θ (mem_filter.mp hω).1, ← sum_div]
    unfold partition expWeight
    congr 1
    rw [sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    rw [hind]
    split_ifs with h <;> simp [h]
  rw [hm]
  simp

/-- At a global minimizer of the penalized objective, `marginal θ = x − (2/k) θ`. -/
theorem marginal_eq_of_isMinOn (hΩ : Ω.Nonempty) (x : ι → ℝ) {k : ℕ} (hk : 0 < k)
    {θ : ι → ℝ} (hmin : IsMinOn (obj Ω x k) Set.univ θ) (e : ι) :
    marginal Ω θ e = x e - (2 / k) * θ e := by
  have hloc : IsLocalMin (obj Ω x k) θ := hmin.isLocalMin univ_mem
  have hg : Continuous (fun t : ℝ => θ + t • Pi.single e 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hf' : IsLocalMin (obj Ω x k) ((fun t : ℝ => θ + t • Pi.single e 1) 0) := by
    simpa using hloc
  have hline : IsLocalMin (fun t : ℝ => obj Ω x k (θ + t • Pi.single e 1)) 0 :=
    IsLocalMin.comp_continuous (f := obj Ω x k) (g := fun t : ℝ => θ + t • Pi.single e 1)
      (b := 0) hf' hg.continuousAt
  have h := hline.hasDerivAt_eq_zero (hasDerivAt_obj_line hΩ x k θ e)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp at h ⊢
  linarith

/-! ### The limit -/

/-- **The exponential-family limit.**  Every marginal vector of a probability vector on `Ω`
is the marginal vector of a pointwise limit of Gibbs distributions. -/
theorem exists_gibbs_limit (hΩ : Ω.Nonempty) {x : ι → ℝ} (hx : ∃ q, IsMarginalOf Ω q x) :
    ∃ p : Finset ι → ℝ, IsMarginalOf Ω p x ∧
      ∀ δ : ℝ, 0 < δ → ∃ θ : ι → ℝ, ∀ ω, |gibbs Ω θ ω - p ω| ≤ δ := by
  obtain ⟨q, hq⟩ := hx
  set L := Real.log (Ω.card : ℝ) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hΩ.card_pos)
  -- the minimizers, one per `k + 1`
  have hmin : ∀ k : ℕ, ∃ θ : ι → ℝ,
      (∀ e, marginal Ω θ e = x e - (2 / ((k + 1 : ℕ) : ℝ)) * θ e) ∧
      ∀ e, θ e ^ 2 ≤ ((k + 1 : ℕ) : ℝ) * L + 1 := by
    intro k
    obtain ⟨θ, hθ, hb⟩ := exists_isMinOn_obj hΩ hq (k := k + 1) (Nat.succ_pos k)
    exact ⟨θ, fun e => marginal_eq_of_isMinOn hΩ x (Nat.succ_pos k) hθ e, hb⟩
  choose θ hθm hθb using hmin
  -- the Gibbs vectors live in the compact cube
  set P : ℕ → (Finset ι → ℝ) := fun k => gibbs Ω (θ k) with hP
  have hcube : ∀ k, P k ∈ Set.pi Set.univ (fun _ : Finset ι => Set.Icc (0 : ℝ) 1) := by
    intro k ω _
    exact ⟨gibbs_nonneg hΩ _ _, gibbs_le_one hΩ _ _⟩
  obtain ⟨p, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : Finset ι => isCompact_Icc).tendsto_subseq hcube
  have hcoord : ∀ ω, Tendsto (fun k => P (φ k) ω) atTop (𝓝 (p ω)) := fun ω =>
    tendsto_pi_nhds.mp hlim ω
  -- the correction `(2/k) θ_k e` tends to `0`
  have hcorr : ∀ e, Tendsto (fun k => (2 / ((φ k + 1 : ℕ) : ℝ)) * θ (φ k) e) atTop (𝓝 0) := by
    intro e
    have hφ' : Tendsto (fun k => φ k + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
    have h1 : Tendsto (fun k => (L + 1) / ((φ k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (L + 1)).comp hφ'
    have h2 : Tendsto (fun k => 2 * Real.sqrt ((L + 1) / ((φ k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul 2
      simpa [Real.sqrt_zero] using this
    refine squeeze_zero_norm (fun k => ?_) h2
    set m : ℝ := ((φ k + 1 : ℕ) : ℝ) with hm
    have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
    have hb := hθb (φ k) e
    rw [Real.norm_eq_abs]
    have hsq : (2 / m * θ (φ k) e) ^ 2 ≤ 4 * ((L + 1) / m) := by
      rw [show (2 / m * θ (φ k) e) ^ 2 = 4 * (θ (φ k) e ^ 2 / m ^ 2) by ring]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [div_le_div_iff₀ (by positivity) hm0]
      have : θ (φ k) e ^ 2 ≤ m * L + 1 := hb
      have hmm : m ≤ m ^ 2 := by nlinarith
      have h5 : θ (φ k) e ^ 2 * m ≤ (m * L + 1) * m := mul_le_mul_of_nonneg_right this hm0.le
      nlinarith
    calc |2 / m * θ (φ k) e| ≤ Real.sqrt (4 * ((L + 1) / m)) := Real.abs_le_sqrt hsq
      _ = 2 * Real.sqrt ((L + 1) / m) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  refine ⟨p, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ω
    exact ge_of_tendsto' (hcoord ω) fun k => gibbs_nonneg hΩ _ _
  · intro ω hne
    by_contra hω
    have h0 : Tendsto (fun k => P (φ k) ω) atTop (𝓝 0) := by
      have : (fun k => P (φ k) ω) = fun _ => 0 := funext fun k => gibbs_of_notMem _ hω
      rw [this]
      exact tendsto_const_nhds
    exact hne (tendsto_nhds_unique (hcoord ω) h0)
  · have h1 : Tendsto (fun k => ∑ ω ∈ Ω, P (φ k) ω) atTop (𝓝 (∑ ω ∈ Ω, p ω)) :=
      tendsto_finsetSum _ fun ω _ => hcoord ω
    have h2 : (fun k => ∑ ω ∈ Ω, P (φ k) ω) = fun _ => 1 :=
      funext fun k => sum_gibbs hΩ (θ (φ k))
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · intro e
    have h1 : Tendsto (fun k => ∑ ω ∈ Ω.filter (fun ω => e ∈ ω), P (φ k) ω) atTop
        (𝓝 (∑ ω ∈ Ω.filter (fun ω => e ∈ ω), p ω)) :=
      tendsto_finsetSum _ fun ω _ => hcoord ω
    have h2 : (fun k => ∑ ω ∈ Ω.filter (fun ω => e ∈ ω), P (φ k) ω) =
        fun k => x e - (2 / ((φ k + 1 : ℕ) : ℝ)) * θ (φ k) e :=
      funext fun k => hθm (φ k) e
    rw [h2] at h1
    have h3 : Tendsto (fun k => x e - (2 / ((φ k + 1 : ℕ) : ℝ)) * θ (φ k) e) atTop
        (𝓝 (x e - 0)) := tendsto_const_nhds.sub (hcorr e)
    rw [sub_zero] at h3
    exact tendsto_nhds_unique h1 h3
  · intro δ hδ
    have hev : ∀ᶠ k in atTop, ∀ ω, dist (P (φ k) ω) (p ω) < δ :=
      eventually_all.mpr fun ω => Metric.tendsto_nhds.mp (hcoord ω) δ hδ
    obtain ⟨k, hk⟩ := hev.exists
    refine ⟨θ (φ k), fun ω => ?_⟩
    have := hk ω
    rw [Real.dist_eq] at this
    exact this.le

end ExpFamily
end TSPGap

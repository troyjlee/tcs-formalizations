/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Bernoulli

/-!
# Hoeffding's extremal theorem for Bernoulli sums (KKO21 Theorem 2.15)

**[Hoe56, Corollary 2.1]**: among all vectors `q ∈ [0,1]^ι` of success
probabilities with fixed total `∑ q i = s`, the minimum (resp. maximum) of
`E[g(B₁ + ⋯ + Bₙ)]` over independent Bernoullis `Bᵢ ~ Ber(q i)` is attained
at a vector all of whose entries lie in `{0, x, 1}` for a single `x ∈ (0,1)`.

This is the workhorse behind the Poisson lower bounds KKO21 Lemma 2.21/2.22:
it reduces any Bernoulli-sum estimate at fixed mean to the i.i.d. case (after
discarding the 0-entries and shifting by the 1-entries).

* `expect` — `E[g(#successes)]` for the product Bernoulli measure `atomProb`.
* `expect_update_affine` — `expect` is affine in each coordinate.
* `expect_pair` — for `i ≠ j`, `expect` at the doubly-updated vector is
  `A + B(u + v) + C·uv`; the coefficient of `u` and `v` agree by the
  relabeling symmetry `expect_comp_equiv`.
* `exists_min_three_valued`, `exists_max_three_valued` — **KKO21 Thm 2.15**.

## Proof sketch

The constraint set `K = {q ∈ [0,1]^ι : ∑ q = s}` is compact and `expect g`
is continuous, so minimizers exist; among them pick `q` maximizing `∑ qᵢ²`
(again by compactness).  If `q i ≠ q j` were both interior, write the
expectation along the segment `qᵢ + qⱼ = c` as `A + Bc + C·qᵢqⱼ`:

* `C < 0`: the midpoint `qᵢ = qⱼ = c/2` strictly increases the product
  `qᵢqⱼ`, hence strictly decreases the expectation — contradicting
  minimality;
* `C > 0`: the segment endpoint (`qᵢ = 0`, or `qⱼ = 1`) strictly decreases
  the product, again strictly decreasing the expectation — contradiction;
* `C = 0`: the expectation is constant along the segment, but the endpoint
  strictly increases `∑ qᵢ²` — contradicting the secondary maximality.

Hence all interior entries of `q` are equal.
-/

namespace TSPGap
namespace Bernoulli

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The expectation `E[g(#successes)]` of a function of the number of
successes of independent Bernoullis with success probabilities `q`. -/
def expect (g : ℕ → ℝ) (q : ι → ℝ) : ℝ :=
  ∑ t : Finset ι, g t.card * atomProb q t

theorem expect_def (g : ℕ → ℝ) (q : ι → ℝ) :
    expect g q = ∑ t : Finset ι, g t.card * atomProb q t := rfl

/-- `expect` as a sum over `univ.powerset`, matching the sums used for the
parity estimates in `TSPGap.Bernoulli`. -/
theorem expect_eq_powerset (g : ℕ → ℝ) (q : ι → ℝ) :
    expect g q = ∑ t ∈ Finset.univ.powerset, g t.card * atomProb q t := by
  rw [Finset.powerset_univ, expect_def]

theorem expect_neg (g : ℕ → ℝ) (q : ι → ℝ) :
    expect (fun k => -(g k)) q = - expect g q := by
  rw [expect_def, expect_def, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-! ### Relabeling invariance -/

theorem atomProb_comp_equiv (e : ι ≃ ι) (q : ι → ℝ) (t : Finset ι) :
    atomProb (q ∘ e) t = atomProb q (t.map e.toEmbedding) := by
  unfold atomProb
  conv_rhs => rw [← Finset.map_univ_equiv e, ← Finset.map_sdiff]
  rw [Finset.prod_map, Finset.prod_map]
  rfl

/-- The expectation is invariant under relabeling the Bernoullis. -/
theorem expect_comp_equiv (g : ℕ → ℝ) (e : ι ≃ ι) (q : ι → ℝ) :
    expect g (q ∘ e) = expect g q := by
  rw [expect_def, expect_def]
  conv_rhs => rw [← Equiv.sum_comp e.finsetCongr
    (fun t : Finset ι => g t.card * atomProb q t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, atomProb_comp_equiv]

/-! ### Affinity in each coordinate -/

/-- The expectation is an affine function of each single success
probability. -/
theorem expect_update_affine (g : ℕ → ℝ) (q : ι → ℝ) (i : ι) :
    ∃ a b : ℝ, ∀ u : ℝ, expect g (Function.update q i u) = a + b * u := by
  classical
  refine ⟨∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t),
      g t.card * ((∏ k ∈ t, q k) * ∏ k ∈ (Finset.univ \ t).erase i, (1 - q k)),
    (∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∈ t),
      g t.card * ((∏ k ∈ t.erase i, q k) * ∏ k ∈ Finset.univ \ t, (1 - q k)))
    - ∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t),
      g t.card * ((∏ k ∈ t, q k) * ∏ k ∈ (Finset.univ \ t).erase i, (1 - q k)),
    fun u => ?_⟩
  have hsplit : expect g (Function.update q i u)
      = (∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∈ t),
          g t.card * atomProb (Function.update q i u) t)
        + ∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t),
          g t.card * atomProb (Function.update q i u) t := by
    rw [expect_def, Finset.sum_filter_add_sum_filter_not]
  have h1 : ∀ t ∈ Finset.univ.filter (fun t : Finset ι => i ∈ t),
      g t.card * atomProb (Function.update q i u) t
        = u * (g t.card *
            ((∏ k ∈ t.erase i, q k) * ∏ k ∈ Finset.univ \ t, (1 - q k))) := by
    intro t ht
    have hit : i ∈ t := (Finset.mem_filter.mp ht).2
    have hp1 : ∏ k ∈ t, Function.update q i u k
        = u * ∏ k ∈ t.erase i, q k := by
      rw [← Finset.mul_prod_erase t _ hit, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun k hk =>
        Function.update_of_ne (Finset.mem_erase.mp hk).1 _ _
    have hp2 : ∏ k ∈ Finset.univ \ t, (1 - Function.update q i u k)
        = ∏ k ∈ Finset.univ \ t, (1 - q k) :=
      Finset.prod_congr rfl fun k hk => by
        have hki : k ≠ i := fun h => (Finset.mem_sdiff.mp hk).2 (h ▸ hit)
        rw [Function.update_of_ne hki]
    unfold atomProb
    rw [hp1, hp2]; ring
  have h0 : ∀ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t),
      g t.card * atomProb (Function.update q i u) t
        = (1 - u) * (g t.card *
            ((∏ k ∈ t, q k) * ∏ k ∈ (Finset.univ \ t).erase i, (1 - q k))) := by
    intro t ht
    have hit : i ∉ t := (Finset.mem_filter.mp ht).2
    have hp1 : ∏ k ∈ t, Function.update q i u k = ∏ k ∈ t, q k :=
      Finset.prod_congr rfl fun k hk => by
        have hki : k ≠ i := fun h => hit (h ▸ hk)
        rw [Function.update_of_ne hki]
    have hmem : i ∈ Finset.univ \ t :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩
    have hp2 : ∏ k ∈ Finset.univ \ t, (1 - Function.update q i u k)
        = (1 - u) * ∏ k ∈ (Finset.univ \ t).erase i, (1 - q k) := by
      rw [← Finset.mul_prod_erase _ _ hmem, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
    unfold atomProb
    rw [hp1, hp2]; ring
  rw [hsplit, Finset.sum_congr rfl h1, Finset.sum_congr rfl h0,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- An affine function interpolates linearly between its values at `0`
and `1`. -/
theorem affine_interp {f : ℝ → ℝ} (h : ∃ a b : ℝ, ∀ u, f u = a + b * u) :
    ∀ u, f u = f 0 + u * (f 1 - f 0) := by
  obtain ⟨a, b, hf⟩ := h
  intro u; rw [hf, hf, hf]; ring

/-! ### The two-coordinate perturbation -/

/-- Swapping the values at two coordinates does not change the
expectation. -/
theorem expect_update_swap (g : ℕ → ℝ) (q : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (u v : ℝ) :
    expect g (Function.update (Function.update q i u) j v)
      = expect g (Function.update (Function.update q i v) j u) := by
  have key : Function.update (Function.update q i v) j u ∘ (Equiv.swap i j)
      = Function.update (Function.update q i u) j v := by
    funext k
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, Function.update_of_ne hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [Equiv.swap_apply_right, Function.update_of_ne hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj,
        Function.update_of_ne hki, Function.update_of_ne hkj]
  rw [← key, expect_comp_equiv]

/-- **Pair perturbation identity**: for `i ≠ j` the expectation at the
doubly-updated vector is `A + B (u + v) + C (u v)`; in particular, along a
segment `u + v = const` it is an affine function of the product `u v`. -/
theorem expect_pair (g : ℕ → ℝ) (q : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    ∃ A B C : ℝ, ∀ u v : ℝ,
      expect g (Function.update (Function.update q i u) j v)
        = A + B * (u + v) + C * (u * v) := by
  classical
  set F : ℝ → ℝ → ℝ :=
    fun u v => expect g (Function.update (Function.update q i u) j v) with hF
  have haffv : ∀ u w : ℝ, F u w = F u 0 + w * (F u 1 - F u 0) := by
    intro u w
    simpa only [hF] using
      affine_interp (expect_update_affine g (Function.update q i u) j) w
  have hcomm : ∀ u w : ℝ,
      F u w = expect g (Function.update (Function.update q j w) i u) := by
    intro u w
    simp only [hF]
    rw [Function.update_comm hij]
  have haffu : ∀ w u : ℝ, F u w = F 0 w + u * (F 1 w - F 0 w) := by
    intro w
    obtain ⟨a, b, hab⟩ := expect_update_affine g (Function.update q j w) i
    intro u
    rw [hcomm u w, hcomm 0 w, hcomm 1 w, hab, hab, hab]; ring
  have hsym : F 1 0 = F 0 1 := by
    simp only [hF]
    exact expect_update_swap g q hij 1 0
  refine ⟨F 0 0, F 1 0 - F 0 0, F 1 1 - 2 * F 1 0 + F 0 0, fun u v => ?_⟩
  change F u v = F 0 0 + (F 1 0 - F 0 0) * (u + v)
    + (F 1 1 - 2 * F 1 0 + F 0 0) * (u * v)
  rw [haffv u v, haffu 0 u, haffu 1 u, ← hsym]; ring

/-! ### Bookkeeping for the doubly-updated vector -/

/-- Summing any composition over a doubly-updated vector replaces the two
old contributions by the two new ones. -/
theorem sum_comp_update_pair (h : ℝ → ℝ) (q : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (u v : ℝ) :
    ∑ k, h (Function.update (Function.update q i u) j v k)
      = ((∑ k, h (q k)) - (h (q i) + h (q j))) + (h u + h v) := by
  classical
  have hsub : ({i, j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have e1 := Finset.sum_sdiff
    (f := fun k => h (Function.update (Function.update q i u) j v k)) hsub
  have e2 := Finset.sum_sdiff (f := fun k => h (q k)) hsub
  have hagree : ∑ k ∈ Finset.univ \ ({i, j} : Finset ι),
        h (Function.update (Function.update q i u) j v k)
      = ∑ k ∈ Finset.univ \ ({i, j} : Finset ι), h (q k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := (Finset.mem_sdiff.mp hk).2
    have hki : k ≠ i := fun hh => hk' (by simp [hh])
    have hkj : k ≠ j := fun hh => hk' (by simp [hh])
    rw [Function.update_of_ne hkj, Function.update_of_ne hki]
  have hpair1 : ∑ k ∈ ({i, j} : Finset ι),
        h (Function.update (Function.update q i u) j v k) = h u + h v := by
    rw [Finset.sum_pair hij]
    rw [Function.update_of_ne hij, Function.update_self, Function.update_self]
  have hpair2 : ∑ k ∈ ({i, j} : Finset ι), h (q k) = h (q i) + h (q j) :=
    Finset.sum_pair hij
  rw [hagree, hpair1] at e1
  rw [hpair2] at e2
  linarith

theorem sum_update_pair (q : ι → ℝ) {i j : ι} (hij : i ≠ j) (u v : ℝ) :
    ∑ k, Function.update (Function.update q i u) j v k
      = ((∑ k, q k) - (q i + q j)) + (u + v) :=
  sum_comp_update_pair id q hij u v

theorem sum_sq_update_pair (q : ι → ℝ) {i j : ι} (hij : i ≠ j) (u v : ℝ) :
    ∑ k, (Function.update (Function.update q i u) j v k) ^ 2
      = ((∑ k, (q k) ^ 2) - ((q i) ^ 2 + (q j) ^ 2)) + (u ^ 2 + v ^ 2) :=
  sum_comp_update_pair (fun x => x ^ 2) q hij u v

/-! ### Compactness of the constraint polytope -/

theorem continuous_expect (g : ℕ → ℝ) :
    Continuous fun q : ι → ℝ => expect g q := by
  unfold expect atomProb
  exact continuous_finsetSum _ fun t _ =>
    continuous_const.mul
      ((continuous_finsetProd _ fun k _ => continuous_apply k).mul
        (continuous_finsetProd _ fun k _ =>
          continuous_const.sub (continuous_apply k)))

omit [DecidableEq ι] in
theorem isCompact_constraint (s : ℝ) :
    IsCompact {p : ι → ℝ | (∀ i, p i ∈ Set.Icc (0:ℝ) 1) ∧ (∑ i, p i) = s} := by
  have h1 : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have h2 : IsClosed {p : ι → ℝ | (∑ i, p i) = s} :=
    isClosed_eq (continuous_finsetSum _ fun k _ => continuous_apply k)
      continuous_const
  have heq : {p : ι → ℝ | (∀ i, p i ∈ Set.Icc (0:ℝ) 1) ∧ (∑ i, p i) = s}
      = (Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1)
        ∩ {p : ι → ℝ | (∑ i, p i) = s} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_univ_pi]
  rw [heq]
  exact h1.inter_right h2

omit [DecidableEq ι] in
theorem constraint_nonempty (s : ℝ) (hs0 : 0 ≤ s)
    (hsn : s ≤ (Fintype.card ι : ℝ)) :
    Set.Nonempty
      {p : ι → ℝ | (∀ i, p i ∈ Set.Icc (0:ℝ) 1) ∧ (∑ i, p i) = s} := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc | hc
  · have hs : s = 0 := by
      rw [hc] at hsn
      exact le_antisymm (by exact_mod_cast hsn) hs0
    exact ⟨fun _ => 0, fun i => ⟨le_rfl, zero_le_one⟩,
      by rw [Finset.sum_const_zero]; exact hs.symm⟩
  · have hcpos : (0:ℝ) < Fintype.card ι := by exact_mod_cast hc
    have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcpos
    refine ⟨fun _ => s / Fintype.card ι,
      fun i => ⟨div_nonneg hs0 hcpos.le, ?_⟩, ?_⟩
    · rw [div_le_one hcpos]; exact hsn
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

/-! ### The extremal theorem -/

/-- **KKO21 Theorem 2.15** ([Hoe56, Corollary 2.1], minimization form).
Among all vectors of success probabilities in `[0,1]` with total `s`, the
expectation `E[g(#successes)]` is minimized by a vector all of whose entries
lie in `{0, x, 1}` for a single `x ∈ (0,1)`. -/
theorem exists_min_three_valued (g : ℕ → ℝ) (s : ℝ) (hs0 : 0 ≤ s)
    (hsn : s ≤ (Fintype.card ι : ℝ)) :
    ∃ q : ι → ℝ, (∀ i, q i ∈ Set.Icc (0:ℝ) 1) ∧ (∑ i, q i) = s ∧
      (∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∀ i, q i = 0 ∨ q i = x ∨ q i = 1) ∧
      ∀ p : ι → ℝ, (∀ i, p i ∈ Set.Icc (0:ℝ) 1) → (∑ i, p i) = s →
        expect g q ≤ expect g p := by
  classical
  set K : Set (ι → ℝ) :=
    {p | (∀ i, p i ∈ Set.Icc (0:ℝ) 1) ∧ (∑ i, p i) = s} with hKdef
  have hKc : IsCompact K := isCompact_constraint s
  have hKne : K.Nonempty := constraint_nonempty s hs0 hsn
  obtain ⟨p₀, hp₀K, hp₀min⟩ :=
    hKc.exists_isMinOn hKne (continuous_expect g).continuousOn
  set M : Set (ι → ℝ) := K ∩ {p | expect g p = expect g p₀} with hMdef
  have hMc : IsCompact M :=
    hKc.inter_right (isClosed_eq (continuous_expect g) continuous_const)
  have hMne : M.Nonempty := ⟨p₀, hp₀K, rfl⟩
  have hΨc : Continuous fun p : ι → ℝ => ∑ k, (p k) ^ 2 :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).pow 2
  obtain ⟨q, hqM, hqmax⟩ := hMc.exists_isMaxOn hMne hΨc.continuousOn
  obtain ⟨⟨hqIcc, hqsum⟩, hqE⟩ := hqM
  have hqE' : expect g q = expect g p₀ := hqE
  have hqmin : ∀ p ∈ K, expect g q ≤ expect g p := by
    intro p hp
    calc expect g q = expect g p₀ := hqE'
      _ ≤ expect g p := isMinOn_iff.mp hp₀min p hp
  -- any two interior coordinates of `q` agree
  have key : ∀ i j, i ≠ j → 0 < q i → q i < 1 → 0 < q j → q j < 1 →
      q i = q j := by
    intro i j hij hi0 hi1 hj0 hj1
    by_contra hne
    obtain ⟨A, B, C, hABC⟩ := expect_pair g q hij
    have hqself : Function.update (Function.update q i (q i)) j (q j) = q := by
      rw [Function.update_eq_self, Function.update_eq_self]
    have hEq : expect g q = A + B * (q i + q j) + C * (q i * q j) := by
      have h := hABC (q i) (q j)
      rwa [hqself] at h
    -- perturbed points along the segment stay in `K`
    have hPK : ∀ t v : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ v → v ≤ 1 →
        t + v = q i + q j →
        Function.update (Function.update q i t) j v ∈ K := by
      intro t v ht0 ht1 hv0 hv1 htv
      refine ⟨fun k => ?_, ?_⟩
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Function.update_self]; exact ⟨hv0, hv1⟩
        rw [Function.update_of_ne hkj]
        rcases eq_or_ne k i with rfl | hki
        · rw [Function.update_self]; exact ⟨ht0, ht1⟩
        · rw [Function.update_of_ne hki]; exact hqIcc k
      · rw [sum_update_pair q hij t v, htv, hqsum]; ring
    -- a segment endpoint with strictly smaller product
    obtain ⟨t, v, ht0, ht1, hv0, hv1, htv, hlt⟩ :
        ∃ t v : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ t + v = q i + q j ∧
          t * v < q i * q j := by
      rcases le_or_gt (q i + q j) 1 with hc | hc
      · exact ⟨0, q i + q j, le_rfl, zero_le_one, by linarith, hc,
          by ring, by simpa using mul_pos hi0 hj0⟩
      · refine ⟨q i + q j - 1, 1, by linarith, by linarith, zero_le_one,
          le_rfl, by ring, ?_⟩
        nlinarith [mul_pos (sub_pos.mpr hi1) (sub_pos.mpr hj1)]
    have hPmem := hPK t v ht0 ht1 hv0 hv1 htv
    have hEP : expect g (Function.update (Function.update q i t) j v)
        = A + B * (q i + q j) + C * (t * v) := by
      have h := hABC t v
      rwa [htv] at h
    rcases lt_trichotomy C 0 with hC | hC | hC
    · -- `C < 0`: the midpoint strictly decreases the expectation
      have hm0 : (0:ℝ) ≤ (q i + q j) / 2 := by linarith
      have hm1 : (q i + q j) / 2 ≤ 1 := by linarith
      have hmmem := hPK ((q i + q j) / 2) ((q i + q j) / 2) hm0 hm1 hm0 hm1
        (by ring)
      have hEm : expect g (Function.update
            (Function.update q i ((q i + q j) / 2)) j ((q i + q j) / 2))
          = A + B * (q i + q j)
            + C * (((q i + q j) / 2) * ((q i + q j) / 2)) := by
        have h := hABC ((q i + q j) / 2) ((q i + q j) / 2)
        rwa [show (q i + q j) / 2 + (q i + q j) / 2 = q i + q j by ring] at h
      have hmin := hqmin _ hmmem
      have hsq : 0 < (q i - q j) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
      nlinarith [mul_neg_of_neg_of_pos hC hsq]
    · -- `C = 0`: flat expectation, but the endpoint beats `q` for `∑ qᵢ²`
      have hEPq : expect g (Function.update (Function.update q i t) j v)
          = expect g p₀ := by
        rw [hEP, hC]
        rw [hC] at hEq
        rw [← hqE']; linarith [hEq]
      have hPM : Function.update (Function.update q i t) j v ∈ M :=
        ⟨hPmem, hEPq⟩
      have hΨle : ∑ k, (Function.update (Function.update q i t) j v k) ^ 2
          ≤ ∑ k, (q k) ^ 2 := isMaxOn_iff.mp hqmax _ hPM
      have hΨP := sum_sq_update_pair q hij t v
      have htv2 : (t + v) ^ 2 = (q i + q j) ^ 2 := by rw [htv]
      nlinarith [hΨle, hΨP, htv2, hlt]
    · -- `C > 0`: the endpoint strictly decreases the expectation
      have hmin := hqmin _ hPmem
      nlinarith [hEP, hEq, hmin, mul_pos hC (sub_pos.mpr hlt)]
  refine ⟨q, hqIcc, hqsum, ?_, fun p hp hps => hqmin p ⟨hp, hps⟩⟩
  by_cases hex : ∃ i₀, 0 < q i₀ ∧ q i₀ < 1
  · obtain ⟨i₀, hi₀0, hi₀1⟩ := hex
    refine ⟨q i₀, hi₀0, hi₀1, fun i => ?_⟩
    rcases eq_or_lt_of_le (hqIcc i).1 with h0 | h0
    · exact Or.inl h0.symm
    rcases eq_or_lt_of_le (hqIcc i).2 with h1 | h1
    · exact Or.inr (Or.inr h1)
    rcases eq_or_ne i i₀ with rfl | hne'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl (key i i₀ hne' h0 h1 hi₀0 hi₀1))
  · push Not at hex
    refine ⟨1 / 2, by norm_num, by norm_num, fun i => ?_⟩
    rcases eq_or_lt_of_le (hqIcc i).1 with h0 | h0
    · exact Or.inl h0.symm
    · exact Or.inr (Or.inr (le_antisymm (hqIcc i).2 (hex i h0)))

/-- **KKO21 Theorem 2.15** ([Hoe56, Corollary 2.1], maximization form). -/
theorem exists_max_three_valued (g : ℕ → ℝ) (s : ℝ) (hs0 : 0 ≤ s)
    (hsn : s ≤ (Fintype.card ι : ℝ)) :
    ∃ q : ι → ℝ, (∀ i, q i ∈ Set.Icc (0:ℝ) 1) ∧ (∑ i, q i) = s ∧
      (∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∀ i, q i = 0 ∨ q i = x ∨ q i = 1) ∧
      ∀ p : ι → ℝ, (∀ i, p i ∈ Set.Icc (0:ℝ) 1) → (∑ i, p i) = s →
        expect g p ≤ expect g q := by
  obtain ⟨q, h1, h2, h3, h4⟩ :=
    exists_min_three_valued (fun k => -(g k)) s hs0 hsn
  refine ⟨q, h1, h2, h3, fun p hp hps => ?_⟩
  have h := h4 p hp hps
  rw [expect_neg, expect_neg] at h
  linarith

end Bernoulli
end TSPGap

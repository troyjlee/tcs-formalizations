/-
# BCW Lemma 4: the spread condition of Theorem 3 is essentially optimal

The note's closing observation: Theorem 3's requirement `r ≳ δ⁻¹·log(k/ε)` cannot be
weakened. For any `0 < δ, ε ≤ 1/2` and `r ≤ ¼·δ⁻¹·log(k/ε)` there is an `r`-spread family
of `k`-sets with `r^k` members that a `δ`-biased set fails to cover with probability more
than `ε` — so the `ε`-dependence of the satisfying theorem is genuinely necessary.

The construction is the one behind every sunflower lower bound (ALWZ §3 builds on the same
Erdős–Rado example): partition the ground set `Fin k × Fin r` into `k` blocks of size `r`
and take **all** `r^k` transversals. `LowerBound` already has the transversal/block
machinery (`tset`, `blk`) — there it is pruned to a code for the robust-sunflower lower
bound; here the *full* family is what is `r`-spread, exactly: the members through a partial
transversal `T` number `r^{k−|T|}`, and through an inconsistent `T` number `0`.

A covering `δ`-biased set must hit every block, which happens with probability
`(1 − (1−δ)^r)^k` by independence (`BlockProb.pBiased_forall_not_disjoint`), and the note's
"elementary considerations" close the chase:

  `(1 − (1−δ)^r)^k ≤ exp(−(1−δ)^r·k) ≤ exp(−e^{−2δr}·k) ≤ exp(−√(εk)) ≤ exp(−√ε) < 1 − ε`.

The last inequality is tight enough at `ε = 1/2` (margin `≈ 0.007`) to need the cubic Taylor
lower bound on `exp` (`Real.sum_le_exp_of_nonneg` with four terms); the second needs
`1 − δ ≥ e^{−2δ}` for `δ ≤ 1/2`.
-/
import Sunflower.LowerBound
import Sunflower.RaoSpread

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace BCWLower

open LowerBound

variable {k r : ℕ}

/-! ## The full transversal family -/

/-- All `r^k` transversals of the `k` blocks of `Fin k × Fin r`. -/
def transversals (k r : ℕ) : Finset (Finset (Fin k × Fin r)) :=
  (Finset.univ : Finset (Fin k → Fin r)).image tset

lemma mem_transversals {S : Finset (Fin k × Fin r)} :
    S ∈ transversals k r ↔ ∃ f : Fin k → Fin r, tset f = S := by
  simp [transversals]

lemma card_transversals : (transversals k r).card = r ^ k := by
  rw [transversals, Finset.card_image_of_injective _ tset_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

lemma isUniform_transversals : IsUniform k (transversals k r) := by
  intro S hS
  obtain ⟨f, rfl⟩ := mem_transversals.mp hS
  exact card_tset f

/-! ## Exact spreadness

The transversals through `T` are the functions pinned on the blocks `T` touches: through a
partial transversal there are exactly `r^{k−|T|}` of them, through an inconsistent `T`
none. -/

/-- **The count through a core.** At most `r^{k−|T|}` transversals contain `T`: the
functions whose transversal contains `T` form a `piFinset` — on each block the value is
constrained to agree with every pair of `T` there. -/
lemma card_filter_tset_superset_le (T : Finset (Fin k × Fin r)) :
    ((Finset.univ : Finset (Fin k → Fin r)).filter fun f => T ⊆ tset f).card
      ≤ r ^ (k - T.card) := by
  classical
  have hset : ((Finset.univ : Finset (Fin k → Fin r)).filter fun f => T ⊆ tset f)
      = Fintype.piFinset fun i : Fin k =>
          (Finset.univ : Finset (Fin r)).filter fun j => ∀ x ∈ T, x.1 = i → x.2 = j := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hT i x hx hxi
      have h := mem_tset.mp (hT hx)
      rw [hxi] at h
      exact h.symm
    · intro hf x hx
      rw [mem_tset]
      exact (hf x.1 x hx rfl).symm
  rw [hset, Fintype.card_piFinset]
  by_cases hfun : ∀ x ∈ T, ∀ y ∈ T, x.1 = y.1 → x = y
  · -- `T` is a partial transversal: touched blocks are pinned, the rest free
    have himg : (T.image Prod.fst).card = T.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy => hfun x hx y hy hxy
    have hbound : ∀ i : Fin k,
        ((Finset.univ : Finset (Fin r)).filter fun j => ∀ x ∈ T, x.1 = i → x.2 = j).card
          ≤ if i ∈ T.image Prod.fst then 1 else r := by
      intro i
      by_cases hi : i ∈ T.image Prod.fst
      · rw [if_pos hi]
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
        refine Finset.card_le_one.mpr fun j1 h1 j2 h2 => ?_
        have e1 := (Finset.mem_filter.mp h1).2 x hx hxi
        have e2 := (Finset.mem_filter.mp h2).2 x hx hxi
        rw [← e1, ← e2]
      · rw [if_neg hi]
        calc ((Finset.univ : Finset (Fin r)).filter
              fun j => ∀ x ∈ T, x.1 = i → x.2 = j).card
            ≤ (Finset.univ : Finset (Fin r)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = r := by rw [Finset.card_univ, Fintype.card_fin]
    calc ∏ i : Fin k, ((Finset.univ : Finset (Fin r)).filter
          fun j => ∀ x ∈ T, x.1 = i → x.2 = j).card
        ≤ ∏ i : Fin k, (if i ∈ T.image Prod.fst then 1 else r) :=
          Finset.prod_le_prod' fun i _ => hbound i
      _ = r ^ (k - T.card) := by
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
          congr 1
          have hsplit := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin k))) (p := fun i => i ∈ T.image Prod.fst)
          have hmem : ((Finset.univ : Finset (Fin k)).filter
              fun i => i ∈ T.image Prod.fst).card = (T.image Prod.fst).card := by
            congr 1
            rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          rw [Finset.card_univ, Fintype.card_fin] at hsplit
          omega
  · -- two pairs share a block with different values: no transversal contains `T`
    push Not at hfun
    obtain ⟨x, hx, y, hy, hxy1, hxyne⟩ := hfun
    have hempty : ((Finset.univ : Finset (Fin r)).filter
        fun j => ∀ z ∈ T, z.1 = x.1 → z.2 = j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ hall
      have e1 := hall x hx rfl
      have e2 := hall y hy hxy1.symm
      exact hxyne (Prod.ext hxy1 (e1.trans e2.symm))
    calc ∏ i : Fin k, ((Finset.univ : Finset (Fin r)).filter
          fun j => ∀ x ∈ T, x.1 = i → x.2 = j).card
        = 0 := Finset.prod_eq_zero (Finset.mem_univ x.1) (by rw [hempty]; rfl)
      _ ≤ r ^ (k - T.card) := Nat.zero_le _

/-- The full transversal family is absolutely `r`-spread — with equality on partial
transversals, which is the sense in which Theorem 3's hypothesis is exactly met. -/
lemma isRaoSpread_transversals : IsRaoSpread (r : ℝ) k (transversals k r) := by
  intro T _
  rw [card_link]
  have heq : (transversals k r).filter (fun S => T ⊆ S)
      = ((Finset.univ : Finset (Fin k → Fin r)).filter fun f => T ⊆ tset f).image tset := by
    ext S
    simp only [transversals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨f, rfl⟩, hT⟩
      exact ⟨f, hT, rfl⟩
    · rintro ⟨f, hT, rfl⟩
      exact ⟨⟨f, rfl⟩, hT⟩
  rw [heq, Finset.card_image_of_injective _ tset_injective]
  have h := card_filter_tset_superset_le T
  have hcast : ((((Finset.univ : Finset (Fin k → Fin r)).filter
      fun f => T ⊆ tset f).card : ℕ) : ℝ) ≤ ((r ^ (k - T.card) : ℕ) : ℝ) := by
    exact_mod_cast h
  rwa [Nat.cast_pow] at hcast

/-! ## The covering probability -/

/-- A covering set hits every block, so the covering probability is at most
`(1 − (1−δ)^r)^k`. -/
lemma pBiased_covered_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    pBiased (Finset.univ : Finset (Fin k × Fin r)) δ
        (fun R => ∃ S ∈ transversals k r, S ⊆ R)
      ≤ (1 - (1 - δ) ^ r) ^ k := by
  classical
  have himp : ∀ R : Finset (Fin k × Fin r), (∃ S ∈ transversals k r, S ⊆ R) →
      ∀ i ∈ (Finset.univ : Finset (Fin k)), ¬ Disjoint R (blk r i) := by
    rintro R ⟨S, hS, hSR⟩ i _
    obtain ⟨f, rfl⟩ := mem_transversals.mp hS
    intro hdisj
    have h1 : ((i, f i) : Fin k × Fin r) ∈ tset f := mem_tset.mpr rfl
    have h2 : ((i, f i) : Fin k × Fin r) ∈ blk r i := mem_blk.mpr rfl
    exact Finset.disjoint_left.mp hdisj (hSR h1) h2
  calc pBiased (Finset.univ : Finset (Fin k × Fin r)) δ
        (fun R => ∃ S ∈ transversals k r, S ⊆ R)
      ≤ pBiased (Finset.univ : Finset (Fin k × Fin r)) δ
        (fun R => ∀ i ∈ (Finset.univ : Finset (Fin k)), ¬ Disjoint R (blk r i)) :=
        pBiased_mono hδ0 hδ1 _ himp
    _ = ∏ i ∈ (Finset.univ : Finset (Fin k)), (1 - (1 - δ) ^ (blk r i).card) :=
        pBiased_forall_not_disjoint δ (blk r) Finset.univ
          (fun i _ => Finset.subset_univ _) (fun i _ j _ hij => blk_disjoint hij)
    _ = (1 - (1 - δ) ^ r) ^ k := by
        rw [Finset.prod_congr rfl fun i _ => by rw [card_blk], Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]

/-! ## The elementary considerations -/

/-- `e^{−√ε} < 1 − ε` for `0 < ε ≤ 1/2` — tight at `ε = 1/2` (margin `≈ 0.007`), which is
why the cubic Taylor lower bound on `exp` is needed. -/
lemma exp_neg_sqrt_lt_one_sub {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Real.exp (-Real.sqrt ε) < 1 - ε := by
  set x := Real.sqrt ε with hxdef
  have hx0 : 0 < x := Real.sqrt_pos.mpr hε0
  have hx2 : x ^ 2 = ε := Real.sq_sqrt hε0.le
  have hx12 : x ^ 2 ≤ 1 / 2 := by rw [hx2]; exact hε1
  have hpoly : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx0.le 4
    have hsum : ∑ i ∈ Finset.range 4, x ^ i / (Nat.factorial i : ℝ)
        = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      norm_num [Nat.factorial]
    rwa [hsum] at h
  have hx707 : x ≤ 0.708 := by nlinarith [hx12, hx0]
  have hx3 : x ^ 3 ≤ x / 2 := by nlinarith [hx12, hx0]
  have hx4 : x ^ 4 ≤ x ^ 2 / 2 := by nlinarith [hx12, sq_nonneg x]
  have hx5 : x ^ 5 ≤ x / 4 := by nlinarith [hx12, hx3, pow_nonneg hx0.le 3]
  have hkey : 1 < Real.exp x * (1 - x ^ 2) := by
    have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx12]
    have h1 : (1 + x + x ^ 2 / 2 + x ^ 3 / 6) * (1 - x ^ 2)
        ≤ Real.exp x * (1 - x ^ 2) := mul_le_mul_of_nonneg_right hpoly hpos.le
    nlinarith [h1, hx0, hx3, hx4, hx5, hx12, mul_pos hx0 hx0,
      mul_nonneg (sub_nonneg.mpr hx707) hx0.le]
  have hEinv : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [← hx2]
  nlinarith [hkey, hEinv, Real.exp_pos x, Real.exp_pos (-x)]

end BCWLower

open BCWLower in
/-- **BCW Lemma 4.** For `0 < δ, ε ≤ 1/2`, `k, r ≥ 1` and `r ≤ ¼·δ⁻¹·log(k/ε)`, there is an
absolutely `r`-spread family of `k`-element subsets of a ground set of size `rk` — the full
transversal family of `k` blocks of size `r` — with exactly `r^k` members whose covering
probability at density `δ` is *less* than `1 − ε`. So the spread requirement of Theorem 3
(`bcw_theorem3`) is essentially optimal, `ε`-dependence included. -/
theorem bcw_lemma4 {k r : ℕ} {δ ε : ℝ} (hk : 1 ≤ k) (_hr : 1 ≤ r)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hrb : (r : ℝ) ≤ 4⁻¹ * δ⁻¹ * Real.log ((k : ℝ) / ε)) :
    ∃ 𝓢 : Finset (Finset (Fin k × Fin r)),
      IsUniform k 𝓢 ∧ IsRaoSpread (r : ℝ) k 𝓢 ∧ 𝓢.card = r ^ k ∧
      pBiased (Finset.univ : Finset (Fin k × Fin r)) δ (fun R => ∃ S ∈ 𝓢, S ⊆ R)
        < 1 - ε := by
  refine ⟨transversals k r, isUniform_transversals, isRaoSpread_transversals,
    card_transversals, lt_of_le_of_lt (pBiased_covered_le hδ0.le (by linarith)) ?_⟩
  set q : ℝ := (1 - δ) ^ r with hqdef
  have hq0 : (0 : ℝ) ≤ q := pow_nonneg (by linarith) r
  have hq1 : q ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkε : (2 : ℝ) ≤ (k : ℝ) / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hε1, hkR]
  set L : ℝ := Real.log ((k : ℝ) / ε) with hLdef
  have hL0 : 0 < L := Real.log_pos (by linarith)
  -- (a) `exp(−2δr) ≤ (1−δ)^r`
  have hexp2δ : Real.exp (-(2 * δ)) ≤ 1 - δ := by
    have h2 : (1 : ℝ) + 2 * δ ≤ Real.exp (2 * δ) := by
      linarith [Real.add_one_le_exp (2 * δ)]
    have hEinv : Real.exp (-(2 * δ)) * Real.exp (2 * δ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h2, Real.exp_pos (2 * δ), hEinv, hδ0, hδ1, Real.exp_pos (-(2 * δ))]
  have hqa : Real.exp (-(2 * δ * r)) ≤ q := by
    have h := pow_le_pow_left₀ (Real.exp_pos _).le hexp2δ r
    have he : Real.exp (-(2 * δ)) ^ r = Real.exp (-(2 * δ * r)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rwa [he] at h
  -- (b) `√ε ≤ q·k`
  have h2δr : 2 * δ * (r : ℝ) ≤ L / 2 := by
    have h1 : 2 * δ * (r : ℝ) ≤ 2 * δ * (4⁻¹ * δ⁻¹ * L) := by
      nlinarith [hrb, hδ0]
    have h2 : 2 * δ * (4⁻¹ * δ⁻¹ * L) = L / 2 * (δ * δ⁻¹) := by ring
    rw [h2, mul_inv_cancel₀ (ne_of_gt hδ0), mul_one] at h1
    exact h1
  have hqk : Real.sqrt ε ≤ q * k := by
    have h1 : Real.exp (-(L / 2)) ≤ q :=
      le_trans (Real.exp_le_exp.mpr (by linarith)) hqa
    have h2 : Real.exp (-(L / 2)) * k ≤ q * k :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have hexpL : Real.exp (-L) = ε / (k : ℝ) := by
      rw [hLdef, Real.exp_neg, Real.exp_log (by positivity), inv_div]
    have hsq : (Real.exp (-(L / 2)) * k) ^ 2 = ε * k := by
      have hhalf : Real.exp (-(L / 2)) ^ 2 = Real.exp (-L) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
      calc (Real.exp (-(L / 2)) * k) ^ 2
          = Real.exp (-(L / 2)) ^ 2 * (k : ℝ) ^ 2 := by ring
        _ = (ε / (k : ℝ)) * (k : ℝ) ^ 2 := by rw [hhalf, hexpL]
        _ = ε * k := by
            field_simp
    have h3 : Real.sqrt ε ≤ Real.exp (-(L / 2)) * k := by
      have hbase : ε ≤ (Real.exp (-(L / 2)) * k) ^ 2 := by
        rw [hsq]
        nlinarith [hε0, hkR]
      calc Real.sqrt ε ≤ Real.sqrt ((Real.exp (-(L / 2)) * k) ^ 2) :=
            Real.sqrt_le_sqrt hbase
        _ = Real.exp (-(L / 2)) * k := Real.sqrt_sq (by positivity)
    linarith
  -- (c) the chain
  have hchain : (1 - q) ^ k ≤ Real.exp (-(q * k)) := by
    have h1q : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 - q) h1q k
    have he : Real.exp (-q) ^ k = Real.exp (-(q * k)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rwa [he] at h
  have hlast : Real.exp (-(q * k)) < 1 - ε :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr (by linarith [hqk]))
      (exp_neg_sqrt_lt_one_sub hε0 hε1)
  linarith [hchain, hlast]

end Sunflower

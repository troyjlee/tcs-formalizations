/-
# The final step: second moment for the heaviest size class

This file proves the ALWZ "final step" (their Lemma 2.10) in the fixed-size
counting model, replacing Janson's inequality by a bare second-moment
(Chebyshev) bound — affordable because our κ-budget dwarfs the requirement at
the final width.

**Uniformization without padding.** The paper makes its bottom system uniform
by padding every multiset copy with fresh dummy elements; that device is
incompatible with the fixed-size-`W` model (dummies dilute the density). This
file replaces it: restrict to the **heaviest size class** `σ_u` (members of one
fixed size `u`), which is automatically uniform, inherits all link bounds, and
carries at least a `1/v` fraction of the mass. The class restriction costs only
a factor `v` in the failure bound, which the κ-budget absorbs. Consequently the
earlier design note suggesting a p-biased detour is obsolete: everything stays
in the fixed-size model.

For a `u`-uniform system the second moment is exact:
`E[Z] = N·ρ'` with `ρ' = C(n-u, m-u)`, and the pair terms are controlled by the
purely binomial inequality (`choose_pair_le`)
`C(n,m)·C(n-2u+c, m-2u+c)·(m-u)^c ≤ C(n-u, m-u)²·n^c`,
giving `failfrac ≤ 2uR·M/(κN)` with `R = n/(m-u)` whenever `uR/κ ≤ 1/2`.
The main results:

* `chebyshev_uniform` — the uniform-class bound.
* `bottom_le` — the final step for a `≤ v`-bounded system:
  `failCount · A · κ ≤ 2v²·R·M·C(n,m)`.
-/
import Sunflower.SpreadCore
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Intervals

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

namespace SpreadCore

open scoped Classical

variable {α : Type*} [DecidableEq α]

/-! ## Counting lemmas (proved in scratch files, integrated below) -/

/-- The number of `m`-subsets of `X` containing a fixed `S ⊆ X` with `|S| ≤ m`
is `C(n - |S|, m - |S|)`. -/
lemma card_filter_superset {X S : Finset α} {m : ℕ} (hS : S ⊆ X) (hm : S.card ≤ m) :
    ((X.powersetCard m).filter (fun W => S ⊆ W)).card
      = (X.card - S.card).choose (m - S.card) := by
  have key : ((X.powersetCard m).filter (fun W => S ⊆ W)).card
      = ((X \ S).powersetCard (m - S.card)).card := by
    apply Finset.card_nbij' (fun W => W \ S) (fun V => V ∪ S)
    · intro W hW
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hW ⊢
      obtain ⟨⟨hWX, hWcard⟩, hSW⟩ := hW
      constructor
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hWX hx.1, hx.2⟩
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSW, hWcard]
    · intro V hV
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hV
      obtain ⟨hVX, hVcard⟩ := hV
      have hdisj : Disjoint V S := by
        rw [Finset.disjoint_left]
        intro a haV haS
        exact (Finset.mem_sdiff.mp (hVX haV)).2 haS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact (Finset.mem_sdiff.mp (hVX h)).1
        · exact hS h
      · rw [Finset.card_union_of_disjoint hdisj, hVcard]
        omega
      · exact Finset.subset_union_right
    · intro W hW
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hW
      exact Finset.sdiff_union_of_subset hW.2
    · intro V hV
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hV
      have hdisj : Disjoint V S := by
        rw [Finset.disjoint_left]
        intro a haV haS
        exact (Finset.mem_sdiff.mp (hV.1 haV)).2 haS
      show (V ∪ S) \ S = V
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hns⟩
        · exact h
        · exact absurd h hns
      · intro hx
        exact ⟨Or.inl hx, fun hxS => Finset.disjoint_left.mp hdisj hx hxS⟩
  rw [key, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hS]

/-- Inequality version, no hypotheses. -/
lemma card_filter_superset_le {X S : Finset α} {m : ℕ} :
    ((X.powersetCard m).filter (fun W => S ⊆ W)).card
      ≤ (X.card - S.card).choose (m - S.card) := by
  by_cases hS : S ⊆ X
  · by_cases hm : S.card ≤ m
    · exact le_of_eq (card_filter_superset hS hm)
    · have hempty : ((X.powersetCard m).filter (fun W => S ⊆ W)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro W hW
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hW
        have h1 := Finset.card_le_card hW.2
        have h2 := hW.1.2
        omega
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  · have hempty : ((X.powersetCard m).filter (fun W => S ⊆ W)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro W hW
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hW
      exact hS (hW.2.trans hW.1.1)
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- If `|S| > m` no `m`-set contains `S`. -/
lemma card_filter_superset_eq_zero {X S : Finset α} {m : ℕ} (h : m < S.card) :
    ((X.powersetCard m).filter (fun W => S ⊆ W)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro W hW
  simp only [Finset.mem_filter, Finset.mem_powersetCard] at hW
  have h1 := Finset.card_le_card hW.2
  have h2 := hW.1.2
  omega

/-- Shift identity: `C(n,m)·∏_{j<k}(m-j) = C(n-k, m-k)·∏_{j<k}(n-j)`. -/
lemma choose_shift_prod {n m k : ℕ} (hk : k ≤ m) (hmn : m ≤ n) :
    n.choose m * ∏ j ∈ range k, (m - j) =
      (n - k).choose (m - k) * ∏ j ∈ range k, (n - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hIH := ih hk'
    have hkey : (n - k).choose (m - k) * (m - k) =
        (n - (k + 1)).choose (m - (k + 1)) * (n - k) := by
      have h1 : n - k = (n - (k + 1)) + 1 := by omega
      have h2 : m - k = (m - (k + 1)) + 1 := by omega
      rw [h1, h2]
      have hs := Nat.add_one_mul_choose_eq (n - (k + 1)) (m - (k + 1))
      calc (n - (k + 1) + 1).choose (m - (k + 1) + 1) * (m - (k + 1) + 1)
          = (n - (k + 1) + 1) * (n - (k + 1)).choose (m - (k + 1)) := by
            rw [← hs]
        _ = (n - (k + 1)).choose (m - (k + 1)) * (n - (k + 1) + 1) := by
            ring
    calc n.choose m * ∏ j ∈ range (k + 1), (m - j)
        = (n.choose m * ∏ j ∈ range k, (m - j)) * (m - k) := by
          rw [Finset.prod_range_succ]
          ring
      _ = ((n - k).choose (m - k) * ∏ j ∈ range k, (n - j)) * (m - k) := by
          rw [hIH]
      _ = ((n - k).choose (m - k) * (m - k)) * ∏ j ∈ range k, (n - j) := by
          ring
      _ = ((n - (k + 1)).choose (m - (k + 1)) * (n - k)) * ∏ j ∈ range k, (n - j) := by
          rw [hkey]
      _ = (n - (k + 1)).choose (m - (k + 1)) * ∏ j ∈ range (k + 1), (n - j) := by
          rw [Finset.prod_range_succ]
          ring

/-- The binomial pair bound behind the second moment. Proof: reduce via
`choose_shift_prod` to the ℕ product inequality
`Pm(u+d)·Pn(u)²·(m-u)^c ≤ Pm(u)²·Pn(u+d)·n^c` (`c = u-d`), which splits into
term-wise inequalities `(m-u-i)(n-i) ≤ (m-i)(n-u-i)` and
`(n-d-i)(m-u) ≤ (m-d-i)·n`. -/
lemma choose_pair_le {n m u d : ℕ} (hu : 1 ≤ u) (hum : u < m) (hmn : m ≤ n)
    (hd : d ≤ u) (hs : u + d ≤ m) :
    (n.choose m : ℝ) * ((n - (u + d)).choose (m - (u + d)) : ℝ) *
        (((m - u : ℕ) : ℝ)) ^ (u - d) ≤
      (((n - u).choose (m - u) : ℝ)) ^ 2 * ((n : ℝ)) ^ (u - d) := by
  set c := u - d with hc
  have hcd : d + c = u := by omega
  have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  -- term-wise inequality families
  have hT1 : (∏ i ∈ range d, (m - (u + i))) * (∏ i ∈ range d, (n - i)) ≤
      (∏ i ∈ range d, (m - i)) * (∏ i ∈ range d, (n - (u + i))) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun i hi => ?_
    rw [Finset.mem_range] at hi
    zify [show u + i ≤ m from by omega, show i ≤ n from by omega,
      show i ≤ m from by omega, show u + i ≤ n from by omega]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmn')
      (show (0:ℤ) ≤ (u : ℤ) from by positivity)]
  have hT2 : (∏ i ∈ range c, (n - (d + i))) * (m - u) ^ c ≤
      (∏ i ∈ range c, (m - (d + i))) * n ^ c := by
    have e1 : (m - u) ^ c = ∏ _i ∈ range c, (m - u) := by
      rw [Finset.prod_const, Finset.card_range]
    have e2 : n ^ c = ∏ _i ∈ range c, n := by
      rw [Finset.prod_const, Finset.card_range]
    rw [e1, e2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hdiu : d + i < u := by omega
    zify [show d + i ≤ n from by omega, show u ≤ m from by omega,
      show d + i ≤ m from by omega]
    have h1 : (d : ℤ) + i ≤ u := by exact_mod_cast hdiu.le
    have h2 : (n : ℤ) - m ≤ (n : ℤ) - ((d : ℤ) + i) := by
      have : (d : ℤ) + i ≤ m := by exact_mod_cast (by omega : d + i ≤ m)
      linarith
    have h3 : (0:ℤ) ≤ (n : ℤ) - m := sub_nonneg.mpr hmn'
    have h4 : (0:ℤ) ≤ (u : ℤ) := by positivity
    nlinarith [mul_le_mul h1 h2 h3 h4]
  -- the ℕ core inequality
  have hcore' : (∏ i ∈ range d, (m - (u + i))) * (∏ j ∈ range u, (n - j)) *
      (m - u) ^ c ≤
      (∏ j ∈ range u, (m - j)) * (∏ i ∈ range d, (n - (u + i))) * n ^ c := by
    have hPn : (∏ j ∈ range u, (n - j)) =
        (∏ j ∈ range d, (n - j)) * ∏ i ∈ range c, (n - (d + i)) := by
      have h := Finset.prod_range_add (fun j => n - j) d c
      rw [hcd] at h
      exact h
    have hPm : (∏ j ∈ range u, (m - j)) =
        (∏ j ∈ range d, (m - j)) * ∏ i ∈ range c, (m - (d + i)) := by
      have h := Finset.prod_range_add (fun j => m - j) d c
      rw [hcd] at h
      exact h
    calc (∏ i ∈ range d, (m - (u + i))) * (∏ j ∈ range u, (n - j)) * (m - u) ^ c
        = ((∏ i ∈ range d, (m - (u + i))) * (∏ i ∈ range d, (n - i))) *
            ((∏ i ∈ range c, (n - (d + i))) * (m - u) ^ c) := by
          rw [hPn]
          ring
      _ ≤ ((∏ i ∈ range d, (m - i)) * (∏ i ∈ range d, (n - (u + i)))) *
            ((∏ i ∈ range c, (m - (d + i))) * n ^ c) :=
          Nat.mul_le_mul hT1 hT2
      _ = (∏ j ∈ range u, (m - j)) * (∏ i ∈ range d, (n - (u + i))) * n ^ c := by
          rw [hPm]
          ring
  have hcoreN : (∏ j ∈ range (u + d), (m - j)) *
      ((∏ j ∈ range u, (n - j)) ^ 2) * (m - u) ^ c ≤
      ((∏ j ∈ range u, (m - j)) ^ 2) * (∏ j ∈ range (u + d), (n - j)) * n ^ c := by
    have hQm : (∏ j ∈ range (u + d), (m - j)) =
        (∏ j ∈ range u, (m - j)) * ∏ i ∈ range d, (m - (u + i)) :=
      Finset.prod_range_add _ u d
    have hQn : (∏ j ∈ range (u + d), (n - j)) =
        (∏ j ∈ range u, (n - j)) * ∏ i ∈ range d, (n - (u + i)) :=
      Finset.prod_range_add _ u d
    calc (∏ j ∈ range (u + d), (m - j)) *
          ((∏ j ∈ range u, (n - j)) ^ 2) * (m - u) ^ c
        = ((∏ j ∈ range u, (m - j)) * (∏ j ∈ range u, (n - j))) *
            ((∏ i ∈ range d, (m - (u + i))) * (∏ j ∈ range u, (n - j)) *
              (m - u) ^ c) := by
          rw [hQm]
          ring
      _ ≤ ((∏ j ∈ range u, (m - j)) * (∏ j ∈ range u, (n - j))) *
            ((∏ j ∈ range u, (m - j)) * (∏ i ∈ range d, (n - (u + i))) *
              n ^ c) := Nat.mul_le_mul_left _ hcore'
      _ = ((∏ j ∈ range u, (m - j)) ^ 2) * (∏ j ∈ range (u + d), (n - j)) *
            n ^ c := by
          rw [hQn]
          ring
  -- transfer to ℝ via the shift identity
  have hI1 := choose_shift_prod (n := n) (m := m) (k := u + d) hs hmn
  have hI2 := choose_shift_prod (n := n) (m := m) (k := u) (by omega) hmn
  have hI1R : (n.choose m : ℝ) * ((∏ j ∈ range (u + d), (m - j) : ℕ) : ℝ) =
      ((n - (u + d)).choose (m - (u + d)) : ℝ) *
        ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) := by
    exact_mod_cast hI1
  have hI2R : (n.choose m : ℝ) * ((∏ j ∈ range u, (m - j) : ℕ) : ℝ) =
      ((n - u).choose (m - u) : ℝ) * ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) := by
    exact_mod_cast hI2
  have hcoreR : ((∏ j ∈ range (u + d), (m - j) : ℕ) : ℝ) *
      ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2 * (((m - u : ℕ) : ℝ)) ^ c ≤
      ((∏ j ∈ range u, (m - j) : ℕ) : ℝ) ^ 2 *
        ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ c := by
    exact_mod_cast hcoreN
  have hPnud_pos : 0 < ∏ j ∈ range (u + d), (n - j) :=
    Finset.prod_pos fun j hj => by
      rw [Finset.mem_range] at hj
      omega
  have hPnu_pos : 0 < ∏ j ∈ range u, (n - j) :=
    Finset.prod_pos fun j hj => by
      rw [Finset.mem_range] at hj
      omega
  have hmult : (0:ℝ) < ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) *
      ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2 :=
    mul_pos (by exact_mod_cast hPnud_pos)
      (pow_pos (by exact_mod_cast hPnu_pos) 2)
  refine le_of_mul_le_mul_right ?_ hmult
  calc (n.choose m : ℝ) * ((n - (u + d)).choose (m - (u + d)) : ℝ) *
        (((m - u : ℕ) : ℝ)) ^ c *
        (((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) *
          ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2)
      = (((n - (u + d)).choose (m - (u + d)) : ℝ) *
          ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ)) *
          ((n.choose m : ℝ) * (((m - u : ℕ) : ℝ)) ^ c *
            ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2) := by ring
    _ = ((n.choose m : ℝ) * ((∏ j ∈ range (u + d), (m - j) : ℕ) : ℝ)) *
          ((n.choose m : ℝ) * (((m - u : ℕ) : ℝ)) ^ c *
            ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2) := by rw [← hI1R]
    _ = (n.choose m : ℝ) ^ 2 *
          (((∏ j ∈ range (u + d), (m - j) : ℕ) : ℝ) *
            ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2 *
            (((m - u : ℕ) : ℝ)) ^ c) := by ring
    _ ≤ (n.choose m : ℝ) ^ 2 *
          (((∏ j ∈ range u, (m - j) : ℕ) : ℝ) ^ 2 *
            ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ c) := by
        refine mul_le_mul_of_nonneg_left hcoreR (by positivity)
    _ = ((n.choose m : ℝ) * ((∏ j ∈ range u, (m - j) : ℕ) : ℝ)) ^ 2 *
          ((n : ℕ) : ℝ) ^ c * ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) := by
        ring
    _ = (((n - u).choose (m - u) : ℝ) * ((∏ j ∈ range u, (n - j) : ℕ) : ℝ)) ^ 2 *
          ((n : ℕ) : ℝ) ^ c * ((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) := by
        rw [hI2R]
    _ = (((n - u).choose (m - u) : ℝ)) ^ 2 * ((n : ℝ)) ^ c *
          (((∏ j ∈ range (u + d), (n - j) : ℕ) : ℝ) *
            ((∏ j ∈ range u, (n - j) : ℕ) : ℝ) ^ 2) := by
        push_cast
        ring

/-- Closed form for the partial sums of the geometric series with ratio `1/2`. -/
private lemma sum_half_pow (n : ℕ) :
    ∑ j ∈ range n, (1 / 2 : ℝ) ^ j = 2 - 2 * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- Factor `y` out of a geometric sum over `Icc 1 u`. -/
private lemma sum_Icc_pow_eq (y : ℝ) (u : ℕ) :
    ∑ c ∈ Icc 1 u, y ^ c = y * ∑ j ∈ range u, y ^ j := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 u), ih, Finset.sum_range_succ]
    ring

/-- Truncated binomial-geometric bound: for `0 ≤ x` with `u·x ≤ 1/2`,
`∑_{c=1}^{u} C(u,c)·x^c ≤ 2·u·x`. -/
lemma sum_choose_mul_pow_le {u : ℕ} {x : ℝ} (hx : 0 ≤ x) (hux : (u : ℝ) * x ≤ 1 / 2) :
    ∑ c ∈ Icc 1 u, (u.choose c : ℝ) * x ^ c ≤ 2 * u * x := by
  have hy0 : 0 ≤ (u : ℝ) * x := mul_nonneg (Nat.cast_nonneg u) hx
  -- Step 1: bound each term by a power of `u·x`.
  have h1 : ∑ c ∈ Icc 1 u, (u.choose c : ℝ) * x ^ c ≤ ∑ c ∈ Icc 1 u, ((u : ℝ) * x) ^ c := by
    refine Finset.sum_le_sum fun c _ => ?_
    have hc : (u.choose c : ℝ) ≤ (u : ℝ) ^ c := by
      exact_mod_cast Nat.choose_le_pow u c
    calc (u.choose c : ℝ) * x ^ c
        ≤ (u : ℝ) ^ c * x ^ c := mul_le_mul_of_nonneg_right hc (pow_nonneg hx c)
      _ = ((u : ℝ) * x) ^ c := (mul_pow _ _ _).symm
  -- Step 2: the geometric tail sum is at most `2`.
  have h2 : ∑ j ∈ range u, ((u : ℝ) * x) ^ j ≤ 2 := by
    have hhalf : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ u := by positivity
    calc ∑ j ∈ range u, ((u : ℝ) * x) ^ j
        ≤ ∑ j ∈ range u, (1 / 2 : ℝ) ^ j :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hy0 hux j
      _ = 2 - 2 * (1 / 2 : ℝ) ^ u := sum_half_pow u
      _ ≤ 2 := by linarith
  -- Combine.
  calc ∑ c ∈ Icc 1 u, (u.choose c : ℝ) * x ^ c
      ≤ ∑ c ∈ Icc 1 u, ((u : ℝ) * x) ^ c := h1
    _ = (u : ℝ) * x * ∑ j ∈ range u, ((u : ℝ) * x) ^ j := sum_Icc_pow_eq _ u
    _ ≤ (u : ℝ) * x * 2 := mul_le_mul_of_nonneg_left h2 hy0
    _ = 2 * u * x := by ring

/-! ## The hit weight and its two moments -/

/-- The σ-mass of members contained in `W` — the counting variable `Z(W)`. -/
noncomputable def hitWeight (X : Finset α) (σ : Finset α → ℕ) (W : Finset α) : ℕ :=
  ∑ S ∈ X.powerset.filter (fun S => S ⊆ W), σ S

lemma hitWeight_eq_zero {X : Finset α} {σ : Finset α → ℕ} {W : Finset α}
    (h : ¬ WCovered σ W) : hitWeight X σ W = 0 := by
  refine Finset.sum_eq_zero fun S hS => ?_
  rw [Finset.mem_filter] at hS
  by_contra hσ
  exact h ⟨S, hσ, hS.2⟩

/-- First moment, general form. -/
lemma sum_hitWeight (X : Finset α) (σ : Finset α → ℕ) (m : ℕ) :
    ∑ W ∈ X.powersetCard m, hitWeight X σ W =
      ∑ S ∈ X.powerset,
        σ S * ((X.powersetCard m).filter (fun W => S ⊆ W)).card := by
  calc ∑ W ∈ X.powersetCard m, hitWeight X σ W
      = ∑ W ∈ X.powersetCard m, ∑ S ∈ X.powerset,
          (if S ⊆ W then σ S else 0) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [hitWeight, Finset.sum_filter]
    _ = ∑ S ∈ X.powerset, ∑ W ∈ X.powersetCard m,
          (if S ⊆ W then σ S else 0) := Finset.sum_comm
    _ = ∑ S ∈ X.powerset,
          σ S * ((X.powersetCard m).filter (fun W => S ⊆ W)).card := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

/-- First moment for a `u`-uniform system: exactly `N · C(n-u, m-u)`. -/
lemma sum_hitWeight_uniform {X : Finset α} {σ : Finset α → ℕ} {u m : ℕ}
    (hbu : ∀ S, σ S ≠ 0 → S ⊆ X ∧ S.card = u) (hum : u ≤ m) :
    ∑ W ∈ X.powersetCard m, hitWeight X σ W =
      wTotal X σ * (X.card - u).choose (m - u) := by
  rw [sum_hitWeight, wTotal, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hσ : σ S = 0
  · rw [hσ, zero_mul, zero_mul]
  · obtain ⟨hSX, hSu⟩ := hbu S hσ
    rw [card_filter_superset hSX (hSu ▸ hum), hSu]

/-- Second moment, expanded over pairs. -/
lemma sum_hitWeight_sq (X : Finset α) (σ : Finset α → ℕ) (m : ℕ) :
    ∑ W ∈ X.powersetCard m, hitWeight X σ W ^ 2 =
      ∑ S ∈ X.powerset, ∑ T ∈ X.powerset, σ S * σ T *
        ((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card := by
  calc ∑ W ∈ X.powersetCard m, hitWeight X σ W ^ 2
      = ∑ W ∈ X.powersetCard m, ∑ S ∈ X.powerset, ∑ T ∈ X.powerset,
          (if S ∪ T ⊆ W then σ S * σ T else 0) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [hitWeight, sq, Finset.sum_filter, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
        by_cases hS : S ⊆ W <;> by_cases hT : T ⊆ W <;>
          simp [hS, hT, Finset.union_subset_iff]
    _ = ∑ S ∈ X.powerset, ∑ W ∈ X.powersetCard m, ∑ T ∈ X.powerset,
          (if S ∪ T ⊆ W then σ S * σ T else 0) := Finset.sum_comm
    _ = ∑ S ∈ X.powerset, ∑ T ∈ X.powerset, σ S * σ T *
          ((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## The Chebyshev counting inequality -/

/-- Second-moment (Chebyshev) bound in counting form: with `C = C(n,m)`,
`fail · (ΣZ)² ≤ C · (C·ΣZ² − (ΣZ)²)`, because every failing `W` has `Z(W) = 0`
and contributes `(ΣZ)²` to the variance sum `Σ_W (C·Z(W) − ΣZ)²`. -/
lemma chebyshev_count {X : Finset α} {σ : Finset α → ℕ} {m : ℕ} :
    (failCount X σ m : ℝ) * (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ)) ^ 2 ≤
      (X.card.choose m : ℝ) *
        ((X.card.choose m : ℝ) *
            (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) ^ 2) -
          (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ)) ^ 2) := by
  classical
  set C : ℝ := (X.card.choose m : ℝ) with hC
  set Sz : ℝ := ∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) with hSz
  set Sz2 : ℝ := ∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) ^ 2 with hSz2
  have hcard : ((X.powersetCard m).card : ℝ) = C := by
    rw [Finset.card_powersetCard]
  have hexp : ∑ W ∈ X.powersetCard m, (C * (hitWeight X σ W : ℝ) - Sz) ^ 2 =
      C ^ 2 * Sz2 - C * Sz ^ 2 := by
    have hterm : ∀ W, (C * (hitWeight X σ W : ℝ) - Sz) ^ 2 =
        C ^ 2 * (hitWeight X σ W : ℝ) ^ 2 -
          2 * C * Sz * (hitWeight X σ W : ℝ) + Sz ^ 2 := fun W => by ring
    rw [Finset.sum_congr rfl fun W _ => hterm W, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard, ← hSz, ← hSz2]
    ring
  have hlow : (failCount X σ m : ℝ) * Sz ^ 2 ≤
      ∑ W ∈ X.powersetCard m, (C * (hitWeight X σ W : ℝ) - Sz) ^ 2 := by
    have hfc : (failCount X σ m : ℝ) =
        (((X.powersetCard m).filter (fun W => ¬ WCovered σ W)).card : ℝ) := by
      simp only [failCount]
    calc (failCount X σ m : ℝ) * Sz ^ 2
        = ∑ _W ∈ (X.powersetCard m).filter (fun W => ¬ WCovered σ W), Sz ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hfc]
      _ = ∑ W ∈ (X.powersetCard m).filter (fun W => ¬ WCovered σ W),
            (C * (hitWeight X σ W : ℝ) - Sz) ^ 2 := by
          refine Finset.sum_congr rfl fun W hW => ?_
          rw [Finset.mem_filter] at hW
          rw [hitWeight_eq_zero hW.2]
          norm_num
      _ ≤ ∑ W ∈ X.powersetCard m, (C * (hitWeight X σ W : ℝ) - Sz) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun W _ _ => sq_nonneg _
  calc (failCount X σ m : ℝ) * Sz ^ 2
      ≤ ∑ W ∈ X.powersetCard m, (C * (hitWeight X σ W : ℝ) - Sz) ^ 2 := hlow
    _ = C ^ 2 * Sz2 - C * Sz ^ 2 := hexp
    _ = C * (C * Sz2 - Sz ^ 2) := by ring

/-! ## The pair bound and the second-moment estimate -/

/-- Per-pair count bound: for members `S, T` of a `u`-uniform system,
`C(n,m) · #{W ⊇ S ∪ T} · (m-u)^{|S∩T|} ≤ C(n-u, m-u)² · n^{|S∩T|}`. -/
lemma pair_count_le {X : Finset α} {u m : ℕ} {S T : Finset α}
    (hu : 1 ≤ u) (hum : u < m) (hmn : m ≤ X.card)
    (_hSX : S ⊆ X) (hSu : S.card = u) (_hTX : T ⊆ X) (hTu : T.card = u) :
    (X.card.choose m : ℝ) *
        (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ) *
        (((m - u : ℕ) : ℝ)) ^ (S ∩ T).card ≤
      (((X.card - u).choose (m - u) : ℝ)) ^ 2 * ((X.card : ℝ)) ^ (S ∩ T).card := by
  classical
  set c := (S ∩ T).card with hc
  have hcu : c ≤ u := by
    rw [hc, ← hSu]
    exact Finset.card_le_card Finset.inter_subset_left
  set d := u - c with hd
  have hdu : d ≤ u := Nat.sub_le _ _
  have hcard : (S ∪ T).card = u + d := by
    have := Finset.card_union_add_card_inter S T
    rw [hSu, hTu, ← hc] at this
    omega
  by_cases hs : u + d ≤ m
  · have hcnt : (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ) ≤
        (((X.card - (u + d)).choose (m - (u + d)) : ℕ) : ℝ) := by
      have := card_filter_superset_le (X := X) (S := S ∪ T) (m := m)
      rw [hcard] at this
      exact_mod_cast this
    have hkey := choose_pair_le (n := X.card) (m := m) (u := u) (d := d)
      hu hum hmn hdu hs
    have hcexp : u - d = c := by omega
    rw [hcexp] at hkey
    calc (X.card.choose m : ℝ) *
          (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ) *
          (((m - u : ℕ) : ℝ)) ^ c
        ≤ (X.card.choose m : ℝ) *
            (((X.card - (u + d)).choose (m - (u + d)) : ℕ) : ℝ) *
            (((m - u : ℕ) : ℝ)) ^ c := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcnt (Nat.cast_nonneg _)) (by positivity)
      _ ≤ (((X.card - u).choose (m - u) : ℝ)) ^ 2 * ((X.card : ℝ)) ^ c := hkey
  · have hcnt0 : ((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card = 0 := by
      refine card_filter_superset_eq_zero ?_
      omega
    rw [hcnt0]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    positivity

/-- **The second-moment estimate** for a `u`-uniform system:
`C·ΣZ² ≤ (ΣZ)² + N·ρ'²·M·∑_{c=1}^{u} C(u,c)(R/κ)^c` where `ρ' = C(n-u,m-u)`,
`R = n/(m-u)`. The `c = 0` fiber reassembles exactly to `(ΣZ)²`; each nonempty
intersection fiber is controlled by the link bound and the pair bound. -/
lemma sum_pair_le {X : Finset α} {σ : Finset α → ℕ} {u m : ℕ} {M κ : ℝ}
    (hκ0 : 0 < κ) (hM : 0 ≤ M)
    (hbu : ∀ S, σ S ≠ 0 → S ⊆ X ∧ S.card = u)
    (hl : WLinkBounded X σ M κ)
    (hu : 1 ≤ u) (hum : u < m) (hmn : m ≤ X.card) :
    (X.card.choose m : ℝ) *
        (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) ^ 2) ≤
      (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ)) ^ 2 +
        (wTotal X σ : ℝ) * (((X.card - u).choose (m - u) : ℕ) : ℝ) ^ 2 * M *
          ∑ c ∈ Icc 1 u, (u.choose c : ℝ) *
            ((X.card : ℝ) / (((m - u : ℕ) : ℝ)) / κ) ^ c := by
  classical
  set n := X.card with hn
  set ρ : ℝ := (((n - u).choose (m - u) : ℕ) : ℝ) with hρ
  set q : ℝ := (((m - u : ℕ) : ℝ)) with hq
  set R : ℝ := (n : ℝ) / q with hR
  have hq0 : (0:ℝ) < q := by
    rw [hq]
    exact_mod_cast Nat.sub_pos_of_lt hum
  have hR0 : (0:ℝ) ≤ R := by positivity
  have hρ0 : (0:ℝ) ≤ ρ := Nat.cast_nonneg _
  set Ntot : ℝ := (wTotal X σ : ℝ) with hNtot
  have hNtot0 : (0:ℝ) ≤ Ntot := Nat.cast_nonneg _
  set G : ℝ := ∑ c ∈ Icc 1 u, (u.choose c : ℝ) * (R / κ) ^ c with hG
  -- the per-member inner bound
  have hinner : ∀ S, σ S ≠ 0 →
      ∑ T ∈ X.powerset, (σ T : ℝ) * R ^ (S ∩ T).card ≤ Ntot + M * G := by
    intro S hσS
    obtain ⟨hSX, hSu⟩ := hbu S hσS
    have hmaps : ∀ T ∈ X.powerset, S ∩ T ∈ S.powerset := fun T _ =>
      Finset.mem_powerset.mpr Finset.inter_subset_left
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun T => (σ T : ℝ) * R ^ (S ∩ T).card)]
    have hfib : ∀ A ∈ S.powerset,
        ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A),
          (σ T : ℝ) * R ^ (S ∩ T).card =
        R ^ A.card * ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ) := by
      intro A _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [Finset.mem_filter] at hT
      rw [hT.2, mul_comm]
    rw [Finset.sum_congr rfl hfib]
    have hemp : ∅ ∈ S.powerset := Finset.empty_mem_powerset _
    rw [← Finset.sum_erase_add _ _ hemp]
    have hEmp : R ^ (∅ : Finset α).card *
        ∑ T ∈ X.powerset.filter (fun T => S ∩ T = ∅), (σ T : ℝ) ≤ Ntot := by
      rw [Finset.card_empty, pow_zero, one_mul, hNtot]
      have : ∑ T ∈ X.powerset.filter (fun T => S ∩ T = ∅), (σ T : ℝ) ≤
          ∑ T ∈ X.powerset, (σ T : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun T _ _ => Nat.cast_nonneg _
      calc ∑ T ∈ X.powerset.filter (fun T => S ∩ T = ∅), (σ T : ℝ)
          ≤ ∑ T ∈ X.powerset, (σ T : ℝ) := this
        _ = (wTotal X σ : ℝ) := by rw [wTotal]; push_cast; rfl
    have hne : ∑ A ∈ (S.powerset).erase ∅,
        R ^ A.card * ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ) ≤
        M * G := by
      have hterm : ∀ A ∈ (S.powerset).erase ∅,
          R ^ A.card * ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ) ≤
          M * (R / κ) ^ A.card := by
        intro A hA
        rw [Finset.mem_erase] at hA
        obtain ⟨hAne, hApow⟩ := hA
        have hAne' : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAne
        have hlink : ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ) ≤
            (wLink X σ A : ℝ) := by
          rw [wLink]
          push_cast
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun T _ _ => Nat.cast_nonneg _
          intro T hT
          rw [Finset.mem_filter] at hT ⊢
          exact ⟨hT.1, hT.2 ▸ Finset.inter_subset_right⟩
        have hlM : (wLink X σ A : ℝ) ≤ M / κ ^ A.card := by
          rw [le_div_iff₀ (pow_pos hκ0 _)]
          exact hl A hAne'
        calc R ^ A.card *
              ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ)
            ≤ R ^ A.card * (M / κ ^ A.card) := by
              exact mul_le_mul_of_nonneg_left (hlink.trans hlM) (by positivity)
          _ = M * (R / κ) ^ A.card := by
              rw [div_pow]
              ring
      calc ∑ A ∈ (S.powerset).erase ∅,
            R ^ A.card * ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ)
          ≤ ∑ A ∈ (S.powerset).erase ∅, M * (R / κ) ^ A.card :=
            Finset.sum_le_sum hterm
        _ ≤ M * G := by
            rw [hG, Finset.mul_sum]
            have hmaps2 : ∀ A ∈ (S.powerset).erase ∅, A.card ∈ Icc 1 u := by
              intro A hA
              rw [Finset.mem_erase] at hA
              rw [Finset.mem_Icc]
              constructor
              · exact Finset.card_pos.mpr
                  (Finset.nonempty_iff_ne_empty.mpr hA.1)
              · rw [← hSu]
                exact Finset.card_le_card (Finset.mem_powerset.mp hA.2)
            rw [← Finset.sum_fiberwise_of_maps_to hmaps2
              (fun A => M * (R / κ) ^ A.card)]
            refine Finset.sum_le_sum fun c hc => ?_
            have hfibc : ∀ A ∈ ((S.powerset).erase ∅).filter
                (fun A => A.card = c), M * (R / κ) ^ A.card = M * (R / κ) ^ c := by
              intro A hA
              rw [Finset.mem_filter] at hA
              rw [hA.2]
            rw [Finset.sum_congr rfl hfibc, Finset.sum_const, nsmul_eq_mul]
            have hcardc : (((S.powerset).erase ∅).filter
                (fun A => A.card = c)).card ≤ u.choose c := by
              calc (((S.powerset).erase ∅).filter (fun A => A.card = c)).card
                  ≤ (S.powersetCard c).card := by
                    refine Finset.card_le_card fun A hA => ?_
                    rw [Finset.mem_filter, Finset.mem_erase] at hA
                    rw [Finset.mem_powersetCard]
                    exact ⟨Finset.mem_powerset.mp hA.1.2, hA.2⟩
                _ = u.choose c := by rw [Finset.card_powersetCard, hSu]
            calc (((S.powerset).erase ∅).filter (fun A => A.card = c)).card *
                  (M * (R / κ) ^ c)
                ≤ (u.choose c : ℝ) * (M * (R / κ) ^ c) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact_mod_cast hcardc
              _ = M * ((u.choose c : ℝ) * (R / κ) ^ c) := by ring
    calc (∑ A ∈ (S.powerset).erase ∅,
          R ^ A.card * ∑ T ∈ X.powerset.filter (fun T => S ∩ T = A), (σ T : ℝ)) +
          R ^ (∅ : Finset α).card *
            ∑ T ∈ X.powerset.filter (fun T => S ∩ T = ∅), (σ T : ℝ)
        ≤ M * G + Ntot := add_le_add hne hEmp
      _ = Ntot + M * G := by ring
  -- assemble: cast the ℕ second moment and bound pairwise
  have hsq : (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) ^ 2) =
      ∑ S ∈ X.powerset, ∑ T ∈ X.powerset, (σ S : ℝ) * (σ T : ℝ) *
        (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ) := by
    have := sum_hitWeight_sq X σ m
    calc (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) ^ 2)
        = ((∑ W ∈ X.powersetCard m, hitWeight X σ W ^ 2 : ℕ) : ℝ) := by
          push_cast
          rfl
      _ = _ := by rw [this]; push_cast; rfl
  rw [hsq, Finset.mul_sum]
  have hpairR : ∀ S ∈ X.powerset, (X.card.choose m : ℝ) *
      ∑ T ∈ X.powerset, (σ S : ℝ) * (σ T : ℝ) *
        (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ) ≤
      (σ S : ℝ) * ρ ^ 2 * (Ntot + M * G) := by
    intro S _
    by_cases hσS : σ S = 0
    · rw [hσS]
      simp only [Nat.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]
      positivity
    · obtain ⟨hSX, hSu⟩ := hbu S hσS
      have hTbound : ∀ T ∈ X.powerset, (X.card.choose m : ℝ) *
          ((σ S : ℝ) * (σ T : ℝ) *
            (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ)) ≤
          (σ S : ℝ) * ((σ T : ℝ) * (ρ ^ 2 * R ^ (S ∩ T).card)) := by
        intro T _
        by_cases hσT : σ T = 0
        · rw [hσT]
          simp only [Nat.cast_zero, zero_mul, mul_zero]
          positivity
        · obtain ⟨hTX, hTu⟩ := hbu T hσT
          have hpc := pair_count_le (X := X) hu hum hmn hSX hSu hTX hTu
          have hCcnt : (X.card.choose m : ℝ) *
              (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ) ≤
              ρ ^ 2 * R ^ (S ∩ T).card := by
            have hqpow : (0:ℝ) < q ^ (S ∩ T).card := pow_pos hq0 _
            rw [hρ, hR, div_pow, ← mul_div_assoc]
            rw [le_div_iff₀ hqpow]
            exact hpc
          calc (X.card.choose m : ℝ) *
                ((σ S : ℝ) * (σ T : ℝ) *
                  (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ))
              = (σ S : ℝ) * (σ T : ℝ) *
                  ((X.card.choose m : ℝ) *
                    (((X.powersetCard m).filter
                      (fun W => S ∪ T ⊆ W)).card : ℝ)) := by ring
            _ ≤ (σ S : ℝ) * (σ T : ℝ) * (ρ ^ 2 * R ^ (S ∩ T).card) := by
                refine mul_le_mul_of_nonneg_left hCcnt (by positivity)
            _ = (σ S : ℝ) * ((σ T : ℝ) * (ρ ^ 2 * R ^ (S ∩ T).card)) := by ring
      calc (X.card.choose m : ℝ) *
            ∑ T ∈ X.powerset, (σ S : ℝ) * (σ T : ℝ) *
              (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ)
          = ∑ T ∈ X.powerset, (X.card.choose m : ℝ) *
              ((σ S : ℝ) * (σ T : ℝ) *
                (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ T ∈ X.powerset,
              (σ S : ℝ) * ((σ T : ℝ) * (ρ ^ 2 * R ^ (S ∩ T).card)) :=
            Finset.sum_le_sum hTbound
        _ = (σ S : ℝ) * ρ ^ 2 *
              ∑ T ∈ X.powerset, (σ T : ℝ) * R ^ (S ∩ T).card := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun T _ => by ring
        _ ≤ (σ S : ℝ) * ρ ^ 2 * (Ntot + M * G) := by
            refine mul_le_mul_of_nonneg_left (hinner S hσS) (by positivity)
  calc ∑ S ∈ X.powerset, (X.card.choose m : ℝ) *
        ∑ T ∈ X.powerset, (σ S : ℝ) * (σ T : ℝ) *
          (((X.powersetCard m).filter (fun W => S ∪ T ⊆ W)).card : ℝ)
      ≤ ∑ S ∈ X.powerset, (σ S : ℝ) * ρ ^ 2 * (Ntot + M * G) :=
        Finset.sum_le_sum hpairR
    _ = Ntot * ρ ^ 2 * (Ntot + M * G) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hNtot, wTotal]
        push_cast
        rfl
    _ = (Ntot * ρ) ^ 2 + Ntot * ρ ^ 2 * M * G := by ring
    _ = (∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ)) ^ 2 +
          Ntot * ρ ^ 2 * M * G := by
        congr 2
        have := sum_hitWeight_uniform hbu (le_of_lt hum)
        calc Ntot * ρ = ((wTotal X σ * (n - u).choose (m - u) : ℕ) : ℝ) := by
              rw [hNtot, hρ]; push_cast; ring
          _ = ((∑ W ∈ X.powersetCard m, hitWeight X σ W : ℕ) : ℝ) := by
              rw [this]
          _ = _ := by push_cast; rfl

/-! ## The uniform-class Chebyshev bound and the final step -/

/-- **Uniform-class Chebyshev bound**: a `u`-uniform link-bounded system fails at
budget `m` with `fail · N · κ ≤ 2uR·M·C(n,m)`, `R = n/(m-u)`, provided
`uR/κ ≤ 1/2`. -/
theorem chebyshev_uniform {X : Finset α} {σ : Finset α → ℕ} {u m : ℕ} {M κ : ℝ}
    (hκ0 : 0 < κ) (hM : 0 ≤ M)
    (hbu : ∀ S, σ S ≠ 0 → S ⊆ X ∧ S.card = u)
    (hl : WLinkBounded X σ M κ)
    (hu : 1 ≤ u) (hum : u < m) (hmn : m ≤ X.card)
    (hgeo : (u : ℝ) * ((X.card : ℝ) / (((m - u : ℕ) : ℝ)) / κ) ≤ 1 / 2)
    (hpos : 0 < wTotal X σ) :
    (failCount X σ m : ℝ) * (wTotal X σ : ℝ) * κ ≤
      2 * u * ((X.card : ℝ) / (((m - u : ℕ) : ℝ))) * M * (X.card.choose m : ℝ) := by
  classical
  set n := X.card with hn
  set q : ℝ := (((m - u : ℕ) : ℝ)) with hq
  set R : ℝ := (n : ℝ) / q with hR
  set C : ℝ := (n.choose m : ℝ) with hC
  set ρ : ℝ := (((n - u).choose (m - u) : ℕ) : ℝ) with hρ
  set Ntot : ℝ := (wTotal X σ : ℝ) with hNtot
  set Sz : ℝ := ∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) with hSz
  set Sz2 : ℝ := ∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ) ^ 2 with hSz2
  have hq0 : (0:ℝ) < q := by
    rw [hq]
    exact_mod_cast Nat.sub_pos_of_lt hum
  have hR0 : (0:ℝ) ≤ R := by positivity
  have hNtot0 : (0:ℝ) < Ntot := by
    rw [hNtot]
    exact_mod_cast hpos
  have hρ0 : (0:ℝ) < ρ := by
    rw [hρ]
    have : 0 < (n - u).choose (m - u) := Nat.choose_pos (by omega)
    exact_mod_cast this
  -- first moment: `Sz = Ntot · ρ`
  have hfirst : Sz = Ntot * ρ := by
    rw [hSz, hNtot, hρ]
    have := sum_hitWeight_uniform hbu (le_of_lt hum)
    calc ∑ W ∈ X.powersetCard m, (hitWeight X σ W : ℝ)
        = ((∑ W ∈ X.powersetCard m, hitWeight X σ W : ℕ) : ℝ) := by
          push_cast; rfl
      _ = ((wTotal X σ * (n - u).choose (m - u) : ℕ) : ℝ) := by rw [this]
      _ = _ := by push_cast; rfl
  -- geometric factor
  set G : ℝ := ∑ c ∈ Icc 1 u, (u.choose c : ℝ) * (R / κ) ^ c with hG
  have hGle : G ≤ 2 * u * (R / κ) :=
    sum_choose_mul_pow_le (by positivity) hgeo
  -- second moment
  have hsm := sum_pair_le (X := X) (σ := σ) (u := u) (m := m)
    hκ0 hM hbu hl hu hum hmn
  -- Chebyshev
  have hch := chebyshev_count (X := X) (σ := σ) (m := m)
  rw [← hSz, ← hSz2, ← hC] at hch
  rw [← hSz, ← hSz2, ← hC, ← hNtot, ← hρ, ← hq, ← hR, ← hG] at hsm
  -- combine: fail·Sz² ≤ C·(Ntot·ρ²·M·G)
  have hvar : C * Sz2 - Sz ^ 2 ≤ Ntot * ρ ^ 2 * M * G := by linarith
  have hmain : (failCount X σ m : ℝ) * Sz ^ 2 ≤ C * (Ntot * ρ ^ 2 * M * G) := by
    calc (failCount X σ m : ℝ) * Sz ^ 2 ≤ C * (C * Sz2 - Sz ^ 2) := hch
      _ ≤ C * (Ntot * ρ ^ 2 * M * G) := by
          refine mul_le_mul_of_nonneg_left hvar ?_
          rw [hC]
          exact Nat.cast_nonneg _
  -- cancel `Ntot·ρ²` and `κ`
  have hcancel : (failCount X σ m : ℝ) * Ntot ≤ C * M * G := by
    have hpos2 : (0:ℝ) < Ntot * ρ ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos2
    calc (failCount X σ m : ℝ) * Ntot * (Ntot * ρ ^ 2)
        = (failCount X σ m : ℝ) * Sz ^ 2 := by rw [hfirst]; ring
      _ ≤ C * (Ntot * ρ ^ 2 * M * G) := hmain
      _ = C * M * G * (Ntot * ρ ^ 2) := by ring
  calc (failCount X σ m : ℝ) * Ntot * κ
      ≤ (C * M * G) * κ := by
        refine mul_le_mul_of_nonneg_right hcancel hκ0.le
    _ ≤ (C * M * (2 * u * (R / κ))) * κ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGle (by positivity)) hκ0.le
    _ = 2 * u * R * M * C * (κ / κ) := by ring
    _ = 2 * u * R * M * C := by rw [div_self hκ0.ne', mul_one]

/-- **The final step** (replacing paper Lemma 2.10): a `≤ v`-bounded
link-bounded system with mass `≥ A` fails at budget `m` with
`fail · A · κ ≤ 2v²R·M·C(n,m)`, `R = n/(m-v)`, provided `vR/κ ≤ 1/2`.
Proof: if `∅` is a member nothing fails; otherwise restrict to the heaviest
size class (mass `≥ A/v`, automatically uniform) and apply `chebyshev_uniform`. -/
theorem bottom_le {X : Finset α} {σ : Finset α → ℕ} {v m : ℕ} {M κ A : ℝ}
    (hκ0 : 0 < κ) (hM : 0 ≤ M) (hA : 0 < A)
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (htot : A ≤ (wTotal X σ : ℝ))
    (hv : 1 ≤ v) (hvm : v < m) (hmn : m ≤ X.card)
    (hgeo : (v : ℝ) * ((X.card : ℝ) / (((m - v : ℕ) : ℝ)) / κ) ≤ 1 / 2) :
    (failCount X σ m : ℝ) * A * κ ≤
      2 * v ^ 2 * ((X.card : ℝ) / (((m - v : ℕ) : ℝ))) * M * (X.card.choose m : ℝ) := by
  classical
  set n := X.card with hn
  have hqv0 : (0:ℝ) < (((m - v : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hvm
  by_cases hE : σ ∅ ≠ 0
  · rw [failCount_eq_zero_of_empty_mem X σ m hE]
    simp only [Nat.cast_zero, zero_mul]
    positivity
  · rw [not_not] at hE
    -- size classes
    set σu : ℕ → Finset α → ℕ := fun u S => if S.card = u then σ S else 0 with hσu
    have hsplit : (wTotal X σ : ℝ) = ∑ u ∈ Icc 1 v, (wTotal X (σu u) : ℝ) := by
      have : ∀ u ∈ Icc 1 v, (wTotal X (σu u) : ℝ) =
          ∑ S ∈ X.powerset, (if S.card = u then (σ S : ℝ) else 0) := by
        intro u _
        rw [wTotal]
        push_cast
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases h : S.card = u <;> simp [hσu, h]
      rw [Finset.sum_congr rfl this, Finset.sum_comm]
      rw [wTotal]
      push_cast
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases hσS : σ S = 0
      · rw [hσS]
        simp
      · have h1 : 1 ≤ S.card := by
          rcases Finset.eq_empty_or_nonempty S with rfl | hne
          · exact absurd hE hσS
          · exact Finset.card_pos.mpr hne
        have h2 : S.card ≤ v := (hb S hσS).2
        rw [Finset.sum_ite_eq (Icc 1 v) S.card (fun _ => (σ S : ℝ))]
        rw [if_pos (Finset.mem_Icc.mpr ⟨h1, h2⟩)]
    -- pigeonhole: some class carries mass ≥ A / v
    have hpigeon : ∃ u ∈ Icc 1 v, A ≤ (v : ℝ) * (wTotal X (σu u) : ℝ) := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hlt : ∑ u ∈ Icc 1 v, (wTotal X (σu u) : ℝ) <
          ∑ _u ∈ Icc 1 v, A / v := by
        refine Finset.sum_lt_sum_of_nonempty ?_ ?_
        · exact Finset.nonempty_Icc.mpr hv
        · intro u hu
          have := hcon u hu
          rw [lt_div_iff₀ (by exact_mod_cast hv : (0:ℝ) < (v:ℝ))]
          linarith [this]
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at hlt
      have hIccc : ((v + 1 - 1 : ℕ) : ℝ) = (v : ℝ) := by
        push_cast [Nat.add_sub_cancel]
        rfl
      rw [hIccc] at hlt
      rw [mul_div_cancel₀ A (by exact_mod_cast hv : (0:ℝ) < (v:ℝ)).ne'] at hlt
      linarith [hsplit ▸ htot]
    obtain ⟨u, huIcc, hAu⟩ := hpigeon
    rw [Finset.mem_Icc] at huIcc
    obtain ⟨hu1, huv⟩ := huIcc
    -- the class is uniform, link-bounded, and covers failures of σ
    have hbu : ∀ S, σu u S ≠ 0 → S ⊆ X ∧ S.card = u := by
      intro S hS
      simp only [hσu] at hS
      by_cases h : S.card = u
      · rw [if_pos h] at hS
        exact ⟨(hb S hS).1, h⟩
      · rw [if_neg h] at hS
        exact absurd rfl hS
    have hlu : WLinkBounded X (σu u) M κ := by
      intro T hT
      refine le_trans ?_ (hl T hT)
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hκ0.le _)
      have : wLink X (σu u) T ≤ wLink X σ T := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [hσu]
        by_cases h : S.card = u <;> simp [h]
      exact_mod_cast this
    have hfail : failCount X σ m ≤ failCount X (σu u) m := by
      simp only [failCount]
      refine Finset.card_le_card fun W hW => ?_
      rw [Finset.mem_filter] at hW ⊢
      refine ⟨hW.1, fun hcov => hW.2 ?_⟩
      obtain ⟨S, hS0, hSW⟩ := hcov
      simp only [hσu] at hS0
      by_cases h : S.card = u
      · rw [if_pos h] at hS0
        exact ⟨S, hS0, hSW⟩
      · rw [if_neg h] at hS0
        exact absurd rfl hS0
    have hposu : 0 < wTotal X (σu u) := by
      by_contra hcon
      have h0 : wTotal X (σu u) = 0 := by omega
      rw [h0] at hAu
      simp only [Nat.cast_zero, mul_zero] at hAu
      linarith
    have hgeou : (u : ℝ) * ((n : ℝ) / (((m - u : ℕ) : ℝ)) / κ) ≤ 1 / 2 := by
      have hqu0 : (0:ℝ) < (((m - u : ℕ) : ℝ)) := by
        exact_mod_cast Nat.sub_pos_of_lt (lt_of_le_of_lt huv hvm)
      have hqle : (((m - v : ℕ) : ℝ)) ≤ (((m - u : ℕ) : ℝ)) := by
        exact_mod_cast Nat.sub_le_sub_left huv m
      have hRle : (n : ℝ) / (((m - u : ℕ) : ℝ)) ≤ (n : ℝ) / (((m - v : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqv0 hqle
      calc (u : ℝ) * ((n : ℝ) / (((m - u : ℕ) : ℝ)) / κ)
          ≤ (v : ℝ) * ((n : ℝ) / (((m - v : ℕ) : ℝ)) / κ) := by
            refine mul_le_mul (by exact_mod_cast huv) ?_ (by positivity)
              (Nat.cast_nonneg _)
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hRle (inv_nonneg.mpr hκ0.le)
        _ ≤ 1 / 2 := hgeo
    have hcheb := chebyshev_uniform (X := X) (σ := σu u) (u := u) (m := m)
      hκ0 hM hbu hlu hu1 (lt_of_le_of_lt huv hvm) hmn hgeou hposu
    -- assemble
    have hRle : (n : ℝ) / (((m - u : ℕ) : ℝ)) ≤ (n : ℝ) / (((m - v : ℕ) : ℝ)) := by
      have hqle : (((m - v : ℕ) : ℝ)) ≤ (((m - u : ℕ) : ℝ)) := by
        exact_mod_cast Nat.sub_le_sub_left huv m
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqv0 hqle
    calc (failCount X σ m : ℝ) * A * κ
        ≤ (failCount X (σu u) m : ℝ) * ((v : ℝ) * (wTotal X (σu u) : ℝ)) * κ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul (by exact_mod_cast hfail) hAu hA.le (Nat.cast_nonneg _))
            hκ0.le
      _ = (v : ℝ) * ((failCount X (σu u) m : ℝ) * (wTotal X (σu u) : ℝ) * κ) := by
          ring
      _ ≤ (v : ℝ) * (2 * u * ((n : ℝ) / (((m - u : ℕ) : ℝ))) * M *
            (n.choose m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcheb (Nat.cast_nonneg _)
      _ ≤ (v : ℝ) * (2 * v * ((n : ℝ) / (((m - v : ℕ) : ℝ))) * M *
            (n.choose m : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM)
            (Nat.cast_nonneg _)
          refine mul_le_mul (by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact_mod_cast huv) hRle (by positivity) (by positivity)
      _ = 2 * v ^ 2 * ((n : ℝ) / (((m - v : ℕ) : ℝ))) * M * (n.choose m : ℝ) := by
          ring

end SpreadCore

end Sunflower

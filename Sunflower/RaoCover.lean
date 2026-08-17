/-
# Iterating the contraction

`RaoLengths.contraction` bounds one round: for a *fixed* `U`, sampling `V` contracts the summed
residual by `2/3`. Rao then iterates it, sampling `W = U₁ ∪ ⋯ ∪ U_m` in `m` rounds and
concluding `E|χ(X,W)| ≤ k·(2/3)^m`.

Turning "one round" into "`m` rounds" needs the exact decomposition of a uniform `(u+v)`-set
into a uniform pair `(U,V)`:

  `∑_{|U|=u} ∑_{|V|=v, V ⊆ X\U} f(U ∪ V) = C(u+v, u) · ∑_{|W|=u+v} f(W)`,

since every `W` arises from exactly `C(u+v,u)` pairs. `SpreadCore.failCount_compose` is the
same double count specialized to `failCount` and stated as an inequality; the iteration needs
it as an identity for an arbitrary summand, so it is proved here in that form.
-/
import Sunflower.RaoLengths
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α]

/-- **The decomposition identity.** Summing over disjoint pairs `(U,V)` of sizes `u` and `v` is
summing over `(u+v)`-sets, each counted `C(u+v,u)` times — once per way of splitting it. -/
theorem sum_pair_union {X : Finset α} (u v : ℕ) (f : Finset α → ℝ) :
    ∑ U ∈ X.powersetCard u, ∑ V ∈ (X \ U).powersetCard v, f (U ∪ V)
      = ((u + v).choose u : ℝ) * ∑ W ∈ X.powersetCard (u + v), f W := by
  classical
  -- the right side, as a double sum over `(W, U)` with `U ⊆ W`
  have hRHS : ((u + v).choose u : ℝ) * ∑ W ∈ X.powersetCard (u + v), f W
      = ∑ W ∈ X.powersetCard (u + v), ∑ _U ∈ W.powersetCard u, f W := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Finset.sum_const, Finset.card_powersetCard, (Finset.mem_powersetCard.mp hW).2,
      nsmul_eq_mul]
  rw [hRHS, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x => (⟨x.1 ∪ x.2, x.1⟩ : (_ : Finset α) × Finset α))
    (j := fun y => (⟨y.2, y.1 \ y.2⟩ : (_ : Finset α) × Finset α)) ?_ ?_ ?_ ?_ ?_
  · -- `(U,V) ↦ (U ∪ V, U)` lands in the right set
    rintro ⟨U, V⟩ hx
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard] at hx
    obtain ⟨⟨hUX, hUcard⟩, hVXU, hVcard⟩ := hx
    have hdisj : Disjoint U V := by
      refine Finset.disjoint_left.mpr fun x hxU hxV => ?_
      exact (Finset.mem_sdiff.mp (hVXU hxV)).2 hxU
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨Finset.union_subset hUX (le_trans hVXU Finset.sdiff_subset), ?_⟩,
      Finset.subset_union_left, hUcard⟩
    rw [Finset.card_union_of_disjoint hdisj, hUcard, hVcard]
  · -- and `(W,U) ↦ (U, W \ U)` comes back
    rintro ⟨W, U⟩ hy
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard] at hy
    obtain ⟨⟨hWX, hWcard⟩, hUW, hUcard⟩ := hy
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨le_trans hUW hWX, hUcard⟩, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      exact Finset.mem_sdiff.mpr ⟨hWX hx.1, hx.2⟩
    · rw [Finset.card_sdiff_of_subset hUW, hWcard, hUcard]
      omega
  · -- the two maps are mutually inverse
    rintro ⟨U, V⟩ hx
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard] at hx
    obtain ⟨⟨hUX, hUcard⟩, hVXU, hVcard⟩ := hx
    have hdisj : Disjoint V U := by
      refine Finset.disjoint_left.mpr fun x hxV hxU => ?_
      exact (Finset.mem_sdiff.mp (hVXU hxV)).2 hxU
    have : (U ∪ V) \ U = V := by
      rw [Finset.union_sdiff_left]
      exact Finset.sdiff_eq_self_of_disjoint hdisj
    rw [Sigma.mk.injEq]
    exact ⟨rfl, by rw [this]⟩
  · rintro ⟨W, U⟩ hy
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard] at hy
    obtain ⟨⟨hWX, hWcard⟩, hUW, hUcard⟩ := hy
    have h1 : U ∪ (W \ U) = W := Finset.union_sdiff_of_subset hUW
    simp only [Sigma.mk.injEq, heq_eq_eq]
    exact ⟨h1, trivial⟩
  · rintro ⟨U, V⟩ _
    rfl

/-- The specialisation the iteration uses: the summed residual at level `u + v`, summed over
all splits, is the residual summed over `(u+v)`-sets. -/
theorem sum_pair_chiSum {X : Finset α} (𝓕 : Finset (Finset α)) (u v : ℕ) :
    ∑ U ∈ X.powersetCard u, ∑ V ∈ (X \ U).powersetCard v,
        ∑ S ∈ 𝓕, ((chi 𝓕 S (U ∪ V)).card : ℝ)
      = ((u + v).choose u : ℝ) * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) := by
  classical
  have h := sum_pair_union (X := X) u v (fun W => ∑ S ∈ 𝓕, ((chi 𝓕 S W).card : ℝ))
  rw [h]
  congr 1
  rw [chiSum]
  push_cast
  rfl

/-- And the other side: for fixed `U` the inner sum does not depend on `V`. -/
theorem sum_pair_chiSum_fixed {X : Finset α} (𝓕 : Finset (Finset α)) (u v : ℕ) :
    ∑ U ∈ X.powersetCard u, ∑ _V ∈ (X \ U).powersetCard v, ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ)
      = ∑ U ∈ X.powersetCard u,
          (((X.card - u).choose v : ℕ) : ℝ) * ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ) := by
  classical
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_sdiff_of_subset
    (Finset.mem_powersetCard.mp hU).1, (Finset.mem_powersetCard.mp hU).2, nsmul_eq_mul]

/-! ## One round, over all `U`

Summing `contraction` over the `u`-sets and re-assembling with `sum_pair_union` gives a
recursion between consecutive slices. The `U`s that already cover a member contribute `0` to
both sides — that is the `chi_pos_or_all_covered` dichotomy doing its work — and the rest
satisfy the contraction's hypotheses. -/

theorem chiSum_eq_sum {X : Finset α} (𝓕 : Finset (Finset α)) (m : ℕ) :
    ((chiSum X 𝓕 m : ℕ) : ℝ)
      = ∑ W ∈ X.powersetCard m, ∑ S ∈ 𝓕, ((chi 𝓕 S W).card : ℝ) := by
  rw [chiSum]; push_cast; rfl

/-- **One round.** `3·chiSum(u+v)·C(n,u) ≤ 2·chiSum(u)·C(n,u+v)`: after normalising by the
number of slices, the summed residual drops by `2/3`. -/
theorem chiSum_step {X : Finset α} {𝓕 : Finset (Finset α)} {u v w : ℕ} {R ρ vn : ℝ}
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hFle : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hFge : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 1 ≤ R) (hρ : 0 < ρ) (hne𝓕 : 𝓕.Nonempty)
    (hvn : vn = (v : ℝ) / (((X.card - u : ℕ)) : ℝ))
    (hv1 : 1 ≤ v) (hvX : v ≤ X.card - u) (hwv : w ≤ v) (hwn : w < X.card - u)
    (h3 : (((X.card - u : ℕ)) : ℝ) ≤ 3 * (((X.card - u - w : ℕ)) : ℝ))
    (hRx : 1 ≤ R * ((v : ℝ) / (((X.card - u : ℕ)) : ℝ)))
    (hρ23 : 23 ≤ Real.logb 2 ρ)
    (hκ : Real.logb 2 R + Real.logb 2 vn = 2 * Real.logb 2 ρ - 1) :
    3 * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)
      ≤ 2 * ((chiSum X 𝓕 u : ℕ) : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ) := by
  classical
  -- the per-`U` bound
  have hper : ∀ U ∈ X.powersetCard u,
      3 * (∑ V ∈ (X \ U).powersetCard v, ∑ S ∈ 𝓕, ((chi 𝓕 S (U ∪ V)).card : ℝ))
        ≤ 2 * ((((X.card - u).choose v : ℕ)) : ℝ) * ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ) := by
    intro U hU
    obtain ⟨hUX, hUcard⟩ := Finset.mem_powersetCard.mp hU
    have hsdiff : (X \ U).card = X.card - u := by
      rw [Finset.card_sdiff_of_subset hUX, hUcard]
    rcases chi_pos_or_all_covered 𝓕 U with hcov | hpos
    · -- `U` already covers a member: both sides vanish
      have hzero : ∀ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ) = 0 := by
        intro S hS
        rw [(chi_eq_empty_iff hS).mpr hcov]
        simp
      have hzero' : ∀ V ∈ (X \ U).powersetCard v,
          ∑ S ∈ 𝓕, ((chi 𝓕 S (U ∪ V)).card : ℝ) = 0 := by
        intro V _
        refine Finset.sum_eq_zero fun S hS => ?_
        rw [chi_eq_empty_of_covered hS hcov V]
        simp
      rw [Finset.sum_congr rfl hzero', Finset.sum_congr rfl hzero]
      simp
    · -- otherwise the contraction applies
      have hnepairs : (pairs 𝓕 X U v).Nonempty := by
        obtain ⟨S, hS⟩ := hne𝓕
        obtain ⟨V, hV⟩ : ((X \ U).powersetCard v).Nonempty :=
          Finset.powersetCard_nonempty.mpr (by omega)
        exact ⟨(V, S), mem_pairs.mpr ⟨hV, hS⟩⟩
      have hcon := contraction (U := U) (vn := vn) (ρ := ρ) hu hsp hSX hFle hFge hR hρ
        (by rw [hsdiff]; exact hvn) hv1 (by omega) hwv (by omega)
        (by rw [hsdiff]; exact h3) (by rw [hsdiff]; exact hRx) hpos hρ23 hκ hnepairs
      -- rewrite the sums over pairs as double sums
      rw [pairs, Finset.sum_product, Finset.sum_product] at hcon
      calc 3 * (∑ V ∈ (X \ U).powersetCard v, ∑ S ∈ 𝓕, ((chi 𝓕 S (U ∪ V)).card : ℝ))
          ≤ 2 * ∑ V ∈ (X \ U).powersetCard v, ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ) := hcon
        _ = 2 * ((((X.card - u).choose v : ℕ)) : ℝ) * ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ) := by
            rw [Finset.sum_const, Finset.card_powersetCard, hsdiff, nsmul_eq_mul]
            ring
  -- sum over `U`, then re-assemble with the decomposition identity
  have hstep : (∑ U ∈ X.powersetCard u,
        3 * (∑ V ∈ (X \ U).powersetCard v, ∑ S ∈ 𝓕, ((chi 𝓕 S (U ∪ V)).card : ℝ)))
      ≤ ∑ U ∈ X.powersetCard u,
        (2 * ((((X.card - u).choose v : ℕ)) : ℝ) * ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ)) :=
    Finset.sum_le_sum hper
  rw [← Finset.mul_sum] at hstep
  have hR' : ∑ U ∈ X.powersetCard u,
        (2 * ((((X.card - u).choose v : ℕ)) : ℝ) * ∑ S ∈ 𝓕, ((chi 𝓕 S U).card : ℝ))
      = 2 * ((((X.card - u).choose v : ℕ)) : ℝ) * ((chiSum X 𝓕 u : ℕ) : ℝ) := by
    rw [chiSum_eq_sum, Finset.mul_sum]
  rw [hR', sum_pair_chiSum] at hstep
  -- `hstep : 3 * (C(u+v,u) * chiSum(u+v)) ≤ 2 * C(n−u,v) * chiSum(u)`
  have hun : u ≤ X.card := by omega
  have hidR : ((X.card.choose (u + v) : ℕ) : ℝ) * (((u + v).choose u : ℕ) : ℝ)
      = ((X.card.choose u : ℕ) : ℝ) * ((((X.card - u).choose v : ℕ)) : ℝ) := by
    have hid := Nat.choose_mul (n := X.card) (k := u + v) (s := u) (Nat.le_add_right _ _)
    have h' : u + v - u = v := by omega
    rw [h'] at hid
    exact_mod_cast hid
  have hposc : (0 : ℝ) < (((u + v).choose u : ℕ) : ℝ) := by
    have : 0 < (u + v).choose u := Nat.choose_pos (Nat.le_add_right _ _)
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ ((chiSum X 𝓕 u : ℕ) : ℝ) := by positivity
  -- multiply by `C(n,u)`, then cancel `C(u+v,u)`
  have hmul := mul_le_mul_of_nonneg_right hstep
    (by positivity : (0 : ℝ) ≤ ((X.card.choose u : ℕ) : ℝ))
  have hgoal : 3 * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)
      * (((u + v).choose u : ℕ) : ℝ)
      ≤ 2 * ((chiSum X 𝓕 u : ℕ) : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ)
      * (((u + v).choose u : ℕ) : ℝ) := by
    calc 3 * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)
          * (((u + v).choose u : ℕ) : ℝ)
        = (3 * ((((u + v).choose u : ℕ)) : ℝ) * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ))
            * ((X.card.choose u : ℕ) : ℝ) := by ring
      _ ≤ (2 * ((((X.card - u).choose v : ℕ)) : ℝ) * ((chiSum X 𝓕 u : ℕ) : ℝ))
            * ((X.card.choose u : ℕ) : ℝ) := by
          have h := hmul
          linarith [h]
      _ = 2 * ((chiSum X 𝓕 u : ℕ) : ℝ)
            * (((X.card.choose u : ℕ) : ℝ) * ((((X.card - u).choose v : ℕ)) : ℝ)) := by ring
      _ = 2 * ((chiSum X 𝓕 u : ℕ) : ℝ)
            * (((X.card.choose (u + v) : ℕ) : ℝ) * (((u + v).choose u : ℕ) : ℝ)) := by
          rw [hidR]
      _ = 2 * ((chiSum X 𝓕 u : ℕ) : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ)
            * (((u + v).choose u : ℕ) : ℝ) := by ring
  exact le_of_mul_le_mul_right hgoal hposc

/-! ## Iterating

Normalised by the number of slices, `chiSum_step` reads `avg(u+v) ≤ (2/3)·avg(u)`. Iterating
from `avg(0) ≤ w·|𝓕|` gives Rao's `E|χ(X,W_j)| ≤ k·(2/3)^j`.

The step is taken as a hypothesis here rather than re-derived: its analytic side conditions
(`v ≤ n−u`, `n−u ≤ 3(n−u−w)`, and the choice of `ρ`, `vn` for that round) depend on `u`, and
supplying them is the schedule chase. Note that `vn` and `ρ` are parameters of the *encoding*
and may differ from round to round — the contraction's conclusion mentions neither. -/

/-- The residual averaged over the slices of a given size. -/
noncomputable def chiAvg (X : Finset α) (𝓕 : Finset (Finset α)) (m : ℕ) : ℝ :=
  ((chiSum X 𝓕 m : ℕ) : ℝ) / ((X.card.choose m : ℕ) : ℝ)

theorem chiAvg_nonneg (X : Finset α) (𝓕 : Finset (Finset α)) (m : ℕ) :
    0 ≤ chiAvg X 𝓕 m := by
  rw [chiAvg]; positivity

/-- `chiSum_step`, normalised. -/
theorem chiAvg_step {X : Finset α} {𝓕 : Finset (Finset α)} {u v : ℕ}
    (huv : u + v ≤ X.card)
    (h : 3 * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)
      ≤ 2 * ((chiSum X 𝓕 u : ℕ) : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ)) :
    chiAvg X 𝓕 (u + v) ≤ (2 / 3) * chiAvg X 𝓕 u := by
  have h1 : (0 : ℝ) < ((X.card.choose u : ℕ) : ℝ) := by
    have : 0 < X.card.choose u := Nat.choose_pos (by omega)
    exact_mod_cast this
  have h2 : (0 : ℝ) < ((X.card.choose (u + v) : ℕ) : ℝ) := by
    have : 0 < X.card.choose (u + v) := Nat.choose_pos huv
    exact_mod_cast this
  have hkey : ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) / ((X.card.choose (u + v) : ℕ) : ℝ)
      ≤ (2 * ((chiSum X 𝓕 u : ℕ) : ℝ)) / (3 * ((X.card.choose u : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ h2 (by positivity)]
    linarith [h]
  calc chiAvg X 𝓕 (u + v)
      = ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) / ((X.card.choose (u + v) : ℕ) : ℝ) := rfl
    _ ≤ (2 * ((chiSum X 𝓕 u : ℕ) : ℝ)) / (3 * ((X.card.choose u : ℕ) : ℝ)) := hkey
    _ = (2 / 3) * chiAvg X 𝓕 u := by rw [chiAvg]; field_simp

/-- **The iteration.** `j` rounds of size `v` leave average residual `(2/3)^j` of the start. -/
theorem chiAvg_iter {X : Finset α} {𝓕 : Finset (Finset α)} {v : ℕ} :
    ∀ j : ℕ, (∀ i, i < j → chiAvg X 𝓕 (i * v + v) ≤ (2 / 3) * chiAvg X 𝓕 (i * v)) →
      chiAvg X 𝓕 (j * v) ≤ (2 / 3) ^ j * chiAvg X 𝓕 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hstep
      have h1 : chiAvg X 𝓕 ((j + 1) * v) ≤ (2 / 3) * chiAvg X 𝓕 (j * v) := by
        have h := hstep j (by omega)
        rwa [show j * v + v = (j + 1) * v by ring] at h
      have h2 := ih fun i hi => hstep i (by omega)
      calc chiAvg X 𝓕 ((j + 1) * v)
          ≤ (2 / 3) * chiAvg X 𝓕 (j * v) := h1
        _ ≤ (2 / 3) * ((2 / 3) ^ j * chiAvg X 𝓕 0) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = (2 / 3) ^ (j + 1) * chiAvg X 𝓕 0 := by ring

/-- The starting point: with nothing sampled, the average residual is at most `w` per member. -/
theorem chiAvg_zero_le {X : Finset α} {𝓕 : Finset (Finset α)} {w : ℕ} (hu : IsUniform w 𝓕) :
    chiAvg X 𝓕 0 ≤ ((𝓕.card : ℕ) : ℝ) * (w : ℝ) := by
  have h := chiSum_le (X := X) (m := 0) hu
  have hc : X.card.choose 0 = 1 := Nat.choose_zero_right _
  rw [chiAvg, hc]
  have hR : ((chiSum X 𝓕 0 : ℕ) : ℝ) ≤ ((𝓕.card * w : ℕ) : ℝ) := by
    rw [hc] at h
    exact_mod_cast le_trans h (le_of_eq (by ring))
  simpa using le_trans hR (le_of_eq (by push_cast; ring))

/-- **Rao's `k·(2/3)^j`.** -/
theorem chiAvg_iter_le {X : Finset α} {𝓕 : Finset (Finset α)} {v w : ℕ} (hu : IsUniform w 𝓕)
    (j : ℕ) (hstep : ∀ i, i < j → chiAvg X 𝓕 (i * v + v) ≤ (2 / 3) * chiAvg X 𝓕 (i * v)) :
    chiAvg X 𝓕 (j * v) ≤ (2 / 3) ^ j * (((𝓕.card : ℕ) : ℝ) * (w : ℝ)) := by
  refine le_trans (chiAvg_iter j hstep) ?_
  exact mul_le_mul_of_nonneg_left (chiAvg_zero_le hu) (by positivity)

/-! ## The schedule

Two things are needed to turn the iteration into a covering statement: enough rounds that
`(2/3)^j·w` falls below `ε`, and a per-round hypothesis that a single condition on `R` can
discharge.

For the first, `log(3/2) ≥ 1/3` (i.e. `e ≤ (3/2)³`), so `j > 3·log(w/ε)` suffices — Rao's
`⌊α log(k/ε)/κ⌋` rounds, with the constant made explicit.

For the second, note that `ρ` is determined: `branch2_fits_trimmed` wants `log₂κ ≤ 2log₂ρ − 1`
and the `2/3` ratio wants `3(log₂ρ + 7) ≤ 2log₂κ`, and both hold exactly when `ρ = √(2κ)` and
`log₂κ ≥ 45`. So the round needs only `45 ≤ log₂(R·v/(n−u))`, and `ρ` can be built from it. -/

/-- `e ≤ (3/2)³`, hence `log(3/2) ≥ 1/3`. -/
theorem log_three_halves_ge : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  have he : Real.exp 1 < 3.375 := by
    have := Real.exp_one_lt_d9
    linarith
  have hcube : (Real.exp (1 / 3 : ℝ)) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpos : (0 : ℝ) < Real.exp (1 / 3 : ℝ) := Real.exp_pos _
  have hle : Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
    nlinarith [hcube, he, hpos, sq_nonneg (Real.exp (1 / 3 : ℝ) - 3 / 2),
      sq_nonneg (Real.exp (1 / 3 : ℝ) + 3 / 2)]
  have := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp] at this

/-- **The round count.** `j > 3·log(w/ε)` rounds bring `(2/3)^j·w` below `ε`. -/
theorem two_thirds_pow_lt {j : ℕ} {W ε : ℝ} (hW : 0 < W) (hε : 0 < ε)
    (hj : 3 * Real.log (W / ε) < (j : ℝ)) : (2 / 3 : ℝ) ^ j * W < ε := by
  have h1 : (2 / 3 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log (2 / 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h2 : Real.log (2 / 3 : ℝ) = - Real.log (3 / 2 : ℝ) := by
    rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have h3 : (2 / 3 : ℝ) ^ j ≤ Real.exp (-(j : ℝ) / 3) := by
    rw [h1, h2]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [log_three_halves_ge, hjnn]
  have h4 : Real.exp (-(j : ℝ) / 3) < ε / W := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < ε / W)]
    refine Real.exp_lt_exp.mpr ?_
    have hlog : Real.log (ε / W) = - Real.log (W / ε) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hlog]
    linarith
  calc (2 / 3 : ℝ) ^ j * W ≤ Real.exp (-(j : ℝ) / 3) * W :=
        mul_le_mul_of_nonneg_right h3 (le_of_lt hW)
    _ < (ε / W) * W := mul_lt_mul_of_pos_right h4 hW
    _ = ε := by field_simp

/-- **The round, from a condition on `κ` alone.** `ρ` is not a free parameter: `ρ = √(2κ)` is
what makes both `branch2_fits_trimmed` and the `2/3` ratio hold, so the round needs only
`log₂κ ≥ 45`. -/
theorem chiSum_step_of_kappa {X : Finset α} {𝓕 : Finset (Finset α)} {u v w : ℕ} {R : ℝ}
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hFle : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hFge : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 1 ≤ R) (hne𝓕 : 𝓕.Nonempty)
    (hv1 : 1 ≤ v) (hvX : v ≤ X.card - u) (hwv : w ≤ v) (hwn : w < X.card - u)
    (h3 : (((X.card - u : ℕ)) : ℝ) ≤ 3 * (((X.card - u - w : ℕ)) : ℝ))
    (hRx : 1 ≤ R * ((v : ℝ) / (((X.card - u : ℕ)) : ℝ)))
    (hκ45 : 45 ≤ Real.logb 2 R + Real.logb 2 ((v : ℝ) / (((X.card - u : ℕ)) : ℝ))) :
    3 * ((chiSum X 𝓕 (u + v) : ℕ) : ℝ) * ((X.card.choose u : ℕ) : ℝ)
      ≤ 2 * ((chiSum X 𝓕 u : ℕ) : ℝ) * ((X.card.choose (u + v) : ℕ) : ℝ) := by
  set vn : ℝ := (v : ℝ) / (((X.card - u : ℕ)) : ℝ) with hvndef
  set L : ℝ := Real.logb 2 R + Real.logb 2 vn with hLdef
  refine chiSum_step (ρ := (2 : ℝ) ^ ((L + 1) / 2)) (vn := vn) hu hsp hSX hFle hFge hR ?_ hne𝓕
    hvndef hv1 hvX hwv hwn h3 hRx ?_ ?_
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]
    linarith [hκ45]
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]
    ring

/-- **The schedule.** `j` rounds of size `v` drive the average residual below `ε` per member.

The per-round hypotheses are discharged from conditions stated at the two extremes: the
geometric ones (`v` fits, `w` is small against what is left, `3w ≤ 2(n−u)`) are hardest at the
*end* of the schedule, so they are required at `u = jv`; the `κ`-condition is hardest at the
*start*, since `v/(n−u)` only grows as `u` does, so it is required at `u = 0`. That the two
pull in opposite directions is exactly why the total sampled has to stay below a constant
fraction of `n`. -/
theorem chiAvg_schedule {X : Finset α} {𝓕 : Finset (Finset α)} {v w j : ℕ} {R ε : ℝ}
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hFle : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hFge : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 1 ≤ R) (hne𝓕 : 𝓕.Nonempty) (hw1 : 1 ≤ w)
    (hv1 : 1 ≤ v) (hwv : w ≤ v)
    (hjv : j * v + v ≤ X.card) (_hw3 : 3 * w ≤ 2 * (X.card - j * v))
    (_hwn : w < X.card - j * v)
    (hRv : 1 ≤ R * ((v : ℝ) / (((X.card : ℕ)) : ℝ)))
    (hκ : 45 ≤ Real.logb 2 R + Real.logb 2 ((v : ℝ) / (((X.card : ℕ)) : ℝ)))
    (hε : 0 < ε) (hj : 3 * Real.log ((w : ℝ) / ε) < (j : ℝ)) :
    chiAvg X 𝓕 (j * v) < ε * ((𝓕.card : ℕ) : ℝ) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hn0 : 0 < X.card := by omega
  have hnR : (0 : ℝ) < (((X.card : ℕ)) : ℝ) := by exact_mod_cast hn0
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hF0 : (0 : ℝ) < ((𝓕.card : ℕ) : ℝ) := by
    have : 0 < 𝓕.card := Finset.card_pos.mpr hne𝓕
    exact_mod_cast this
  -- every round satisfies the step's hypotheses
  have hstep : ∀ i, i < j → chiAvg X 𝓕 (i * v + v) ≤ (2 / 3) * chiAvg X 𝓕 (i * v) := by
    intro i hi
    have hiv : i * v + v ≤ j * v := by
      have h := Nat.mul_le_mul_right v (show i + 1 ≤ j by omega)
      simpa [Nat.succ_mul] using h
    have hivn : i * v + v ≤ X.card := by omega
    have hA0 : 0 < X.card - i * v := by omega
    have hA0R : (0 : ℝ) < (((X.card - i * v : ℕ)) : ℝ) := by exact_mod_cast hA0
    have hAn : (((X.card - i * v : ℕ)) : ℝ) ≤ (((X.card : ℕ)) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    -- `v/(n−u)` only grows with `u`, so the `κ`-condition at `u = 0` is the strongest
    have hdiv : (v : ℝ) / (((X.card : ℕ)) : ℝ) ≤ (v : ℝ) / (((X.card - i * v : ℕ)) : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hvR) hA0R hAn
    refine chiAvg_step hivn ?_
    refine chiSum_step_of_kappa hu hsp hSX hFle hFge hR hne𝓕 hv1 (by omega) hwv (by omega)
      ?_ ?_ ?_
    · -- `n−u ≤ 3(n−u−w)`
      have hnat : X.card - i * v ≤ 3 * (X.card - i * v - w) := by omega
      exact_mod_cast hnat
    · -- `1 ≤ R·v/(n−u)`
      calc (1 : ℝ) ≤ R * ((v : ℝ) / (((X.card : ℕ)) : ℝ)) := hRv
        _ ≤ R * ((v : ℝ) / (((X.card - i * v : ℕ)) : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiv (le_of_lt hR0)
    · -- `45 ≤ log₂R + log₂(v/(n−u))`
      have hmono : Real.logb 2 ((v : ℝ) / (((X.card : ℕ)) : ℝ))
          ≤ Real.logb 2 ((v : ℝ) / (((X.card - i * v : ℕ)) : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hdiv
      linarith [hκ, hmono]
  -- iterate, then apply the round count
  have hiter := chiAvg_iter_le hu j hstep
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw1
  have hpow := two_thirds_pow_lt (W := (w : ℝ)) (ε := ε) hwR hε hj
  calc chiAvg X 𝓕 (j * v)
      ≤ (2 / 3) ^ j * (((𝓕.card : ℕ) : ℝ) * (w : ℝ)) := hiter
    _ = ((𝓕.card : ℕ) : ℝ) * ((2 / 3) ^ j * (w : ℝ)) := by ring
    _ < ((𝓕.card : ℕ) : ℝ) * ε := mul_lt_mul_of_pos_left hpow hF0
    _ = ε * ((𝓕.card : ℕ) : ℝ) := by ring

/-! ## From residual to coverage

`RaoChi.fixedCount_mul_card_le_chiSum` says every uncovered `W` contributes at least `|𝓕|` to
`chiSum`. So a small average residual means few uncovered slices — which is the statement
Rao's Lemma 4 is for. -/

/-- A small average residual bounds the uncovered slices. -/
theorem fixedCount_lt_of_chiAvg {X : Finset α} {𝓕 : Finset (Finset α)} {m : ℕ} {ε : ℝ}
    (hne𝓕 : 𝓕.Nonempty) (hm : m ≤ X.card) (h : chiAvg X 𝓕 m < ε * ((𝓕.card : ℕ) : ℝ)) :
    ((fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) m : ℕ) : ℝ)
      < ε * ((X.card.choose m : ℕ) : ℝ) := by
  have hF0 : (0 : ℝ) < ((𝓕.card : ℕ) : ℝ) := by
    have : 0 < 𝓕.card := Finset.card_pos.mpr hne𝓕
    exact_mod_cast this
  have hC0 : (0 : ℝ) < ((X.card.choose m : ℕ) : ℝ) := by
    have : 0 < X.card.choose m := Nat.choose_pos hm
    exact_mod_cast this
  -- `chiSum = chiAvg · C(n,m)`
  have hchi : ((chiSum X 𝓕 m : ℕ) : ℝ) = chiAvg X 𝓕 m * ((X.card.choose m : ℕ) : ℝ) := by
    rw [chiAvg]
    field_simp
  have hcount : ((fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) m : ℕ) : ℝ)
      * ((𝓕.card : ℕ) : ℝ) ≤ ((chiSum X 𝓕 m : ℕ) : ℝ) := by
    exact_mod_cast fixedCount_mul_card_le_chiSum X 𝓕 m
  have hlt : ((fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) m : ℕ) : ℝ) * ((𝓕.card : ℕ) : ℝ)
      < (ε * ((X.card.choose m : ℕ) : ℝ)) * ((𝓕.card : ℕ) : ℝ) := by
    calc ((fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) m : ℕ) : ℝ) * ((𝓕.card : ℕ) : ℝ)
        ≤ ((chiSum X 𝓕 m : ℕ) : ℝ) := hcount
      _ = chiAvg X 𝓕 m * ((X.card.choose m : ℕ) : ℝ) := hchi
      _ < (ε * ((𝓕.card : ℕ) : ℝ)) * ((X.card.choose m : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_right h hC0
      _ = (ε * ((X.card.choose m : ℕ) : ℝ)) * ((𝓕.card : ℕ) : ℝ) := by ring
  exact lt_of_mul_lt_mul_right (le_of_lt hlt |>.lt_of_ne (by
    intro hEq
    exact absurd hEq (ne_of_lt hlt))) (le_of_lt hF0)

/-- **Rao's covering estimate** (his Lemma 4, in the fixed-size model). For an absolutely
`R`-spread `w`-uniform family, a uniformly random `m`-subset of the ground set contains a
member except with probability `< ε`, once the schedule fits:

  `#{W : |W| = m, no member of 𝓕 inside W} < ε·C(n,m)`.

This is the endpoint of Phase C — the statement Phase D transfers to the `p`-biased model. -/
theorem rao_fixed_cover {X : Finset α} {𝓕 : Finset (Finset α)} {v w j : ℕ} {R ε : ℝ}
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hFle : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hFge : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 1 ≤ R) (hne𝓕 : 𝓕.Nonempty) (hw1 : 1 ≤ w)
    (hv1 : 1 ≤ v) (hwv : w ≤ v)
    (hjv : j * v + v ≤ X.card) (hw3 : 3 * w ≤ 2 * (X.card - j * v))
    (hwn : w < X.card - j * v)
    (hRv : 1 ≤ R * ((v : ℝ) / (((X.card : ℕ)) : ℝ)))
    (hκ : 45 ≤ Real.logb 2 R + Real.logb 2 ((v : ℝ) / (((X.card : ℕ)) : ℝ)))
    (hε : 0 < ε) (hj : 3 * Real.log ((w : ℝ) / ε) < (j : ℝ)) :
    ((fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) (j * v) : ℕ) : ℝ)
      < ε * ((X.card.choose (j * v) : ℕ) : ℝ) :=
  fixedCount_lt_of_chiAvg hne𝓕 (by omega)
    (chiAvg_schedule hu hsp hSX hFle hFge hR hne𝓕 hw1 hv1 hwv hjv hw3 hwn hRv hκ hε hj)

end Rao

end Sunflower

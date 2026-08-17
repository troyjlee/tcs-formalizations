/-
# The probabilistic core of ALWZ, in counting form

This file develops the proof of the spread lemma (`Sunflower.spread_lemma` in
`Sunflower/ALWZ.lean`) following ALWZ §2 (arXiv:1908.08483v3), with two deliberate
departures that make the argument fully finitary:

* **Fixed-size random subsets throughout.** The paper's own encoding argument
  (their Lemma 2.8) is stated for a uniformly random subset `W` of size exactly
  `p·n`; the paper then transfers to the `p`-biased model by a limiting argument
  (their Corollary 2.9) because its final step uses Janson's inequality. We never
  leave the fixed-size model: "probability" is always `(number of m-subsets with
  the property) / (n choose m)`, and the composition `W ∼ U(X, m₁)` followed by
  `W' ∼ U(X \ W, m₂)` is *exactly* a uniform `(m₁+m₂)`-subset with a uniformly
  chosen `m₁`-sub-block — a bijection of finite sets, not an approximation.

* **Chebyshev instead of Janson.** The final step (their Lemma 2.10) needs only
  that a κ-spread system of `v`-bounded sets with `κ ≫ v/α`-ish is likely hit;
  Janson gives failure `exp(−q/4)`, but a bare second-moment bound gives failure
  `O(v/(ακ) + 1/μ)`, which suffices because our κ-budget `C r³ lg w lg lg w`
  dwarfs the requirement `O(w* r²)` at the final width `w* = O(log log w)`.

Everything here is weighted with **integer** weights `σ : Finset α → ℕ` (the paper
scales its rational weights to integers in every proof anyway) and phrased as
counting inequalities over `Finset.powersetCard`.

## Structure

* `wTotal`, `wLink`, `WBounded`, `WLinkBounded` — weighted set systems and the
  spread condition, multiplicative form (`wLink · κ^|T| ≤ M`).
* `WCovered`, `failCount` — the satisfying/containment event, counted.
* `IsBad`, `badWeight`, `sum_badWeight_le` — the **encoding argument** (paper
  Lemma 2.8): the σ-mass of bad pairs `(W, S)` is exponentially small.
* the reduction round (paper Lemma 2.6): from a not-too-bad `W`, a new system on
  `X \ W` with width `v' < v`, the same link bounds, and slightly less mass.
* `failCount_compose`, `round_le` — the **reduction round** (paper Lemma 2.6):
  splitting an uncovered `(m₁+m₂)`-set as `W ⊔ rest` replaces the paper's
  independent sampling; Markov + the encoding bound control bad `W`'s.
* `sum_failCount_sdiff`, `coveredTuples`, … — the random-partition
  **disjointness step** (paper Lemma 1.6), fixed-size form.

## Where the rest of the argument lives

Everything here is sorry-free, and so is the sequel: `Sunflower.spread_lemma` is a
**theorem**, with the explicit constant `C = 2^41`. The two pieces this file leaves
open are discharged as follows.

1. **The final step** (paper Lemma 2.10) — `Sunflower.SpreadBottom.bottom_le`. The
   paper uses Janson; a bare second-moment (Chebyshev) bound suffices for our
   κ-budget. The second-moment computation (like the paper's Janson one) needs
   *uniform* member sizes — for mixed sizes the `h(a)h(b)`-vs-`h(a∪b)` bookkeeping
   loses `(n/m)^{v-a}` factors. The paper fixes this with its dummy-padding sentence
   ("We may also assume that all sets in F′ have size exactly w…", nontrivial to
   justify for weighted systems); our formalization instead restricts to the
   **heaviest size class**, which is uniform for free, keeps the link bounds, and
   holds `A/v` of the mass — so no padding, no p-biased model, no size bridge.
   (The paper's *other*, elementary padding sentence — the §1 one, which uniformizes
   a `w`-set system at the level of the statement — is formalized separately in
   `Sunflower.Padding` and is unrelated to this one.)

2. **The schedule** (paper §2.3) — `Sunflower.SpreadIterate.iterate_le`, instantiated
   arithmetically in `Sunflower.SpreadAssemble`. The implementation departs from the
   sketch this file was originally written against: rather than a round count `T` and
   a strong induction on the width, it runs a **fuel induction** with invariant
   `v ≤ 2L·Q^t` for `Q = 2L/(2L-1)`, and gives the round at width `v` the geometric
   budgets `ε(1/2)^v` (failure) and `A₀(1/2)^{v+1}` (bad mass), which telescope
   using only `v' + 1 ≤ v`. The round count therefore never enters the failure
   accounting — the reason the naive "at most `v` rounds" bound, which would have
   cost an extra `w^{1/log log w}`-type factor, is not needed. The κ-requirements
   are isolated as three hypotheses (`hK1`, `hK2`, `hK3`) and reduce, under
   `L := Nat.log 2 ⌈κ⌉₊ + Nat.log 2 r + 4` and fuel `t₀ = (2L-1)(Nat.log 2 w + 1)`,
   to the two master inequalities `1024·r·t₀ ≤ κ` and `1024·r²·L² ≤ κ` — both
   comfortably inside the `C r³ lg w lg lg w` budget.
-/
import Sunflower.Spread
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

namespace SpreadCore

open scoped Classical

variable {α : Type*} [DecidableEq α]

/-! ## Weighted set systems -/

/-- Total weight of the system `σ` (all weight lives on subsets of `X`). -/
def wTotal (X : Finset α) (σ : Finset α → ℕ) : ℕ := ∑ S ∈ X.powerset, σ S

/-- Weight of the link at `T`: the σ-mass sitting above `T`. -/
def wLink (X : Finset α) (σ : Finset α → ℕ) (T : Finset α) : ℕ :=
  ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), σ S

/-- The system is supported on subsets of `X` of size at most `v`. -/
def WBounded (X : Finset α) (v : ℕ) (σ : Finset α → ℕ) : Prop :=
  ∀ S, σ S ≠ 0 → S ⊆ X ∧ S.card ≤ v

/-- The spread condition, multiplicative form: every nonempty link carries mass at
most `M / κ^|T|`. (Compare `Sunflower.IsSpread`.) -/
def WLinkBounded (X : Finset α) (σ : Finset α → ℕ) (M κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty → (wLink X σ T : ℝ) * κ ^ T.card ≤ M

/-- `W` contains a member of the (support of the) system. -/
def WCovered (σ : Finset α → ℕ) (W : Finset α) : Prop :=
  ∃ S, σ S ≠ 0 ∧ S ⊆ W

/-- The number of `m`-subsets of `X` containing no member: the failure count for
the satisfying property, in counting form. -/
noncomputable def failCount (X : Finset α) (σ : Finset α → ℕ) (m : ℕ) : ℕ :=
  open scoped Classical in
  ((X.powersetCard m).filter (fun W => ¬ WCovered σ W)).card

/-! ### Basic facts -/

lemma wLink_le_wTotal (X : Finset α) (σ : Finset α → ℕ) (T : Finset α) :
    wLink X σ T ≤ wTotal X σ :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

@[simp] lemma wLink_empty (X : Finset α) (σ : Finset α → ℕ) :
    wLink X σ ∅ = wTotal X σ := by
  unfold wLink wTotal
  rw [Finset.filter_true_of_mem fun _ _ => Finset.empty_subset _]

omit [DecidableEq α] in
lemma failCount_le_choose (X : Finset α) (σ : Finset α → ℕ) (m : ℕ) :
    failCount X σ m ≤ X.card.choose m := by
  classical
  calc failCount X σ m ≤ (X.powersetCard m).card := Finset.card_filter_le _ _
    _ = X.card.choose m := Finset.card_powersetCard m X

omit [DecidableEq α] in
/-- If some member of the system lies inside every `W` we count, failures vanish;
in particular a system containing `∅` never fails. -/
lemma failCount_eq_zero_of_empty_mem (X : Finset α) (σ : Finset α → ℕ) (m : ℕ)
    (h : σ ∅ ≠ 0) : failCount X σ m = 0 := by
  classical
  unfold failCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro W _
  simp only [not_not]
  exact ⟨∅, h, Finset.empty_subset _⟩

omit [DecidableEq α] in
/-- Covering is monotone in the covering set. -/
lemma WCovered.mono {σ : Finset α → ℕ} {W W' : Finset α} (h : WCovered σ W)
    (hWW : W ⊆ W') : WCovered σ W' := by
  obtain ⟨S, hS, hSW⟩ := h
  exact ⟨S, hS, hSW.trans hWW⟩

/-! ## The encoding argument (paper Lemma 2.8)

Fix a width target `v' < v`. For an `m`-subset `W`, a member `S` is **bad** if no
member `S'` has both `S' \ W ⊆ S \ W` and `|S' \ W| ≤ v'`. The paper's encoding:
a bad pair `(W, S)` is determined by the data
`(U := W ∪ S, A := S ∩ can U, S, D := S ∩ W)` where `can U` is a canonical member
contained in `U` (which exists — `S` itself qualifies), and crucially
`|A| > v'` (badness of `S` applied to `S' := can U`), so the σ-mass of possible
`S`'s is controlled by the link bound at `A`. Counting the four data pieces gives
the bound below; `(8n/m)^v` absorbs `(2n/m)^v` for the `U`-count and `2^v` each
for `A` and `D`. -/

/-- `(W, S)` is a bad pair: `S` is a member, and no member's `W`-residual fits
inside `S`'s with size at most `v'`. -/
def IsBad (σ : Finset α → ℕ) (v' : ℕ) (W S : Finset α) : Prop :=
  σ S ≠ 0 ∧ ∀ S', σ S' ≠ 0 → S' \ W ⊆ S \ W → v' < (S' \ W).card

/-- A canonical member of the system contained in `U` (junk value `∅` if none). -/
noncomputable def canMem (X : Finset α) (σ : Finset α → ℕ) (U : Finset α) :
    Finset α :=
  open scoped Classical in
  if h : ∃ S, (σ S ≠ 0 ∧ S ⊆ X) ∧ S ⊆ U then h.choose else ∅

omit [DecidableEq α] in
lemma canMem_spec {X : Finset α} {σ : Finset α → ℕ} {U S₀ : Finset α}
    (h0 : σ S₀ ≠ 0) (hX : S₀ ⊆ X) (hU : S₀ ⊆ U) :
    σ (canMem X σ U) ≠ 0 ∧ canMem X σ U ⊆ X ∧ canMem X σ U ⊆ U := by
  classical
  have h : ∃ S, (σ S ≠ 0 ∧ S ⊆ X) ∧ S ⊆ U := ⟨S₀, ⟨h0, hX⟩, hU⟩
  rw [canMem, dif_pos h]
  exact ⟨h.choose_spec.1.1, h.choose_spec.1.2, h.choose_spec.2⟩

/-- **Recovery count**: for fixed `S` and `U`, a subset `W` with `W ∪ S = U` is
determined by `W ∩ S` (indeed `W = (U \ S) ∪ (W ∩ S)`), so there are at most
`2^{|S|}` of them — piece 4 of the paper's encoding. -/
lemma card_union_eq_le {m : ℕ} {X S U : Finset α} :
    ((X.powersetCard m).filter (fun W => W ∪ S = U)).card ≤ 2 ^ S.card := by
  have key : ∀ W : Finset α, W ∪ S = U → W = (U \ S) ∪ (W ∩ S) := by
    intro W hWU
    ext a
    simp only [← hWU, mem_union, mem_sdiff, mem_inter]
    tauto
  calc ((X.powersetCard m).filter (fun W => W ∪ S = U)).card
      ≤ S.powerset.card := by
        refine Finset.card_le_card_of_injOn (fun W => W ∩ S)
          (fun W _ => mem_powerset.mpr inter_subset_right) ?_
        intro W hW W' hW' h
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hW)).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hW')).2
        have h' : W ∩ S = W' ∩ S := h
        rw [key W h1, key W' h2, h']
    _ = 2 ^ S.card := card_powerset S

/-- **Fiber bound**: the σ-mass of bad pairs `(W, S)` with `W ∪ S = U`, weighted
and multiplied by `κ^{v'}`, is at most `2^v · 2^v · M`: `2^{|S|} ≤ 2^v` recovery
choices for `W`, at most `2^{|canMem U|} ≤ 2^v` choices for `A = S ∩ canMem U`
(which has `|A| > v'` by badness applied to `S' := canMem U`), and the σ-mass of
members above a fixed `A` is at most `M/κ^{|A|} ≤ M/κ^{v'}` by the link bound. -/
lemma fiber_badWeight_le {X : Finset α} {σ : Finset α → ℕ} {v v' m : ℕ}
    {M κ : ℝ} (hκ : 1 ≤ κ) (hM : 0 ≤ M) (hb : WBounded X v σ)
    (hl : WLinkBounded X σ M κ) (U : Finset α) :
    (∑ p ∈ (((X.powersetCard m) ×ˢ X.powerset).filter
        (fun p => IsBad σ v' p.1 p.2 ∧ p.1 ∪ p.2 = U)), σ p.2 : ℝ) * κ ^ v' ≤
      2 ^ v * 2 ^ v * M := by
  set F := (((X.powersetCard m) ×ˢ X.powerset).filter
    (fun p => IsBad σ v' p.1 p.2 ∧ p.1 ∪ p.2 = U)) with hF
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le one_pos hκ
  rcases Finset.eq_empty_or_nonempty F with hFe | hFne
  · rw [hFe]
    simp only [Finset.sum_empty, zero_mul]
    positivity
  -- a witness bad pair gives the canonical member `K ⊆ U`
  obtain ⟨⟨W₀, S₀⟩, hp₀⟩ := hFne
  rw [hF, Finset.mem_filter, Finset.mem_product] at hp₀
  obtain ⟨⟨hW₀, hS₀X⟩, hbad₀, hU₀⟩ := hp₀
  have hS₀U : S₀ ⊆ U := hU₀ ▸ Finset.subset_union_right
  obtain ⟨hK0, hKX, hKU⟩ :=
    canMem_spec (X := X) (U := U) hbad₀.1 (Finset.mem_powerset.mp hS₀X) hS₀U
  set K := canMem X σ U with hKdef
  have hKv : K.card ≤ v := (hb K hK0).2
  -- Step A: reshape the pair-sum, summing over `S` first
  have hre : (∑ p ∈ F, σ p.2) =
      ∑ S ∈ X.powerset, ((X.powersetCard m).filter
        (fun W => IsBad σ v' W S ∧ W ∪ S = U)).card * σ S := by
    rw [hF, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  -- Step B/C: the count is ≤ 2^v, and contributing `S` have `|S ∩ K| > v'`
  set cnt : Finset α → ℕ := fun S => ((X.powersetCard m).filter
    (fun W => IsBad σ v' W S ∧ W ∪ S = U)).card with hcnt
  have hcnt_le : ∀ S, σ S ≠ 0 → cnt S ≤ 2 ^ v := by
    intro S hS
    calc cnt S ≤ ((X.powersetCard m).filter (fun W => W ∪ S = U)).card := by
          refine Finset.card_le_card (fun W hW => ?_)
          rw [Finset.mem_filter] at hW ⊢
          exact ⟨hW.1, hW.2.2⟩
      _ ≤ 2 ^ S.card := card_union_eq_le
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by omega) (hb S hS).2
  have hcnt_mem : ∀ S, cnt S ≠ 0 → σ S ≠ 0 → v' < (S ∩ K).card := by
    intro S hcS hσS
    have : ((X.powersetCard m).filter
        (fun W => IsBad σ v' W S ∧ W ∪ S = U)).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hcS)
    obtain ⟨W, hW⟩ := this
    rw [Finset.mem_filter] at hW
    obtain ⟨-, hWbad, hWU⟩ := hW
    -- badness applied to `S' := K`
    have hKW : K \ W ⊆ S \ W := by
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      have hxU : x ∈ U := hKU hx.1
      rw [← hWU, Finset.mem_union] at hxU
      exact ⟨hxU.resolve_left hx.2, hx.2⟩
    have hgt : v' < (K \ W).card := hWbad.2 K hK0 hKW
    refine lt_of_lt_of_le hgt (Finset.card_le_card ?_)
    intro x hx
    rw [Finset.mem_inter]
    exact ⟨Finset.mem_sdiff.mp (hKW hx) |>.1, Finset.mem_sdiff.mp hx |>.1⟩
  -- the σ-mass with `|S ∩ K| > v'`, grouped by `A = S ∩ K`, is link-bounded
  set AF := X.powerset.filter (fun S => v' < (S ∩ K).card) with hAF
  have hsum_le : (∑ p ∈ F, σ p.2) ≤ 2 ^ v * ∑ S ∈ AF, σ S := by
    rw [hre]
    have h1 : ∑ S ∈ X.powerset, cnt S * σ S =
        ∑ S ∈ X.powerset.filter (fun S => cnt S * σ S ≠ 0), cnt S * σ S :=
      (Finset.sum_filter_ne_zero _).symm
    rw [h1]
    have h2 : X.powerset.filter (fun S => cnt S * σ S ≠ 0) ⊆ AF := by
      intro S hS
      rw [Finset.mem_filter] at hS ⊢
      have hc : cnt S ≠ 0 := fun h => hS.2 (by rw [h, zero_mul])
      have hσ : σ S ≠ 0 := fun h => hS.2 (by rw [h, mul_zero])
      exact ⟨hS.1, hcnt_mem S hc hσ⟩
    calc ∑ S ∈ X.powerset.filter (fun S => cnt S * σ S ≠ 0), cnt S * σ S
        ≤ ∑ S ∈ X.powerset.filter (fun S => cnt S * σ S ≠ 0), 2 ^ v * σ S := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [Finset.mem_filter] at hS
          have hσ : σ S ≠ 0 := fun h => hS.2 (by rw [h, mul_zero])
          exact Nat.mul_le_mul_right _ (hcnt_le S hσ)
      _ ≤ ∑ S ∈ AF, 2 ^ v * σ S :=
          Finset.sum_le_sum_of_subset h2
      _ = 2 ^ v * ∑ S ∈ AF, σ S := by rw [Finset.mul_sum]
  -- Step D: group by `A = S ∩ K`
  set KF := K.powerset.filter (fun A => v' < A.card) with hKF
  have hgroup : (∑ S ∈ AF, σ S) ≤ ∑ A ∈ KF, wLink X σ A := by
    have hmaps : ∀ S ∈ AF, S ∩ K ∈ KF := by
      intro S hS
      rw [hAF, Finset.mem_filter] at hS
      rw [hKF, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, hS.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun A hA => ?_
    refine Finset.sum_le_sum_of_subset ?_
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨hSAF, hSA⟩ := hS
    rw [hAF, Finset.mem_filter] at hSAF
    rw [Finset.mem_filter]
    exact ⟨hSAF.1, hSA ▸ Finset.inter_subset_left⟩
  -- Step E: each link is `≤ M/κ^{v'}`, and there are at most `2^v` of them
  have hlink : ∀ A ∈ KF, (wLink X σ A : ℝ) * κ ^ v' ≤ M := by
    intro A hA
    rw [hKF, Finset.mem_filter] at hA
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    calc (wLink X σ A : ℝ) * κ ^ v' ≤ (wLink X σ A : ℝ) * κ ^ A.card := by
          have hnn : (0:ℝ) ≤ (wLink X σ A : ℝ) := Nat.cast_nonneg _
          have hple : κ ^ v' ≤ κ ^ A.card :=
            pow_le_pow_right₀ hκ (by omega)
          exact mul_le_mul_of_nonneg_left hple hnn
      _ ≤ M := hl A hAne
  have hKFcard : (KF.card : ℝ) ≤ 2 ^ v := by
    calc (KF.card : ℝ) ≤ (K.powerset.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ K.card := by rw [Finset.card_powerset]; push_cast; rfl
      _ ≤ 2 ^ v := by
          have : (2:ℝ) ^ K.card ≤ 2 ^ v := pow_le_pow_right₀ one_le_two hKv
          exact this
  -- assemble
  calc (∑ p ∈ F, σ p.2 : ℝ) * κ ^ v'
      ≤ (2 ^ v * ∑ S ∈ AF, σ S : ℕ) * κ ^ v' := by
        have := hsum_le
        have hpow : (0:ℝ) < κ ^ v' := pow_pos hκ0 _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hpow.le
    _ ≤ (2 ^ v * ∑ A ∈ KF, wLink X σ A : ℕ) * κ ^ v' := by
        have hpow : (0:ℝ) < κ ^ v' := pow_pos hκ0 _
        refine mul_le_mul_of_nonneg_right ?_ hpow.le
        exact_mod_cast Nat.mul_le_mul_left _ hgroup
    _ = 2 ^ v * ∑ A ∈ KF, (wLink X σ A : ℝ) * κ ^ v' := by
        push_cast
        rw [mul_assoc, Finset.sum_mul]
    _ ≤ 2 ^ v * (KF.card * M) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ A ∈ KF, (wLink X σ A : ℝ) * κ ^ v' ≤ ∑ _A ∈ KF, M :=
              Finset.sum_le_sum hlink
          _ = KF.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ v * (2 ^ v * M) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hKFcard hM
    _ = 2 ^ v * 2 ^ v * M := by ring

/-- **Binomial ratio bound**: `C(n, m+i) ≤ C(n,m) · (n/m)^i` for `m ≥ 1`. -/
lemma choose_add_le {n m i : ℕ} (hm : 1 ≤ m) (_hmn : m ≤ n) :
    (n.choose (m + i) : ℝ) ≤ (n.choose m : ℝ) * (n / m) ^ i := by
  have hm' : 0 < m := by omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm'
  induction i with
  | zero => simp
  | succ i ih =>
    show (n.choose (m + i + 1) : ℝ) ≤ (n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ (i + 1)
    rcases Nat.lt_or_ge (m + i) n with h | h
    · have hpos : (0 : ℝ) < (m : ℝ) + (i : ℝ) + 1 := by positivity
      have h2 : ((n.choose (m + i + 1) * (m + i + 1) : ℕ) : ℝ)
          = ((n.choose (m + i) * (n - (m + i)) : ℕ) : ℝ) := by
        rw [Nat.choose_succ_right_eq]
      push_cast [Nat.cast_sub h.le] at h2
      have heq : (n.choose (m + i + 1) : ℝ)
          = (n.choose (m + i) : ℝ) *
            (((n : ℝ) - ((m : ℝ) + (i : ℝ))) / ((m : ℝ) + (i : ℝ) + 1)) := by
        rw [← mul_div_assoc, eq_div_iff hpos.ne']
        linear_combination h2
      have hcast : ((m : ℝ) + (i : ℝ)) ≤ (n : ℝ) := by exact_mod_cast h.le
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hb : (0 : ℝ) ≤ ((n : ℝ) - ((m : ℝ) + (i : ℝ))) / ((m : ℝ) + (i : ℝ) + 1) :=
        div_nonneg (by linarith) hpos.le
      have hdiv : ((n : ℝ) - ((m : ℝ) + (i : ℝ))) / ((m : ℝ) + (i : ℝ) + 1)
          ≤ (n : ℝ) / (m : ℝ) := by
        rw [div_le_div_iff₀ hpos hm0]
        nlinarith [mul_nonneg hn0 hi0, mul_nonneg hi0 hm0.le, mul_self_nonneg (m : ℝ)]
      calc (n.choose (m + i + 1) : ℝ)
          = (n.choose (m + i) : ℝ) *
              (((n : ℝ) - ((m : ℝ) + (i : ℝ))) / ((m : ℝ) + (i : ℝ) + 1)) := heq
        _ ≤ ((n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ i) * ((n : ℝ) / (m : ℝ)) :=
            mul_le_mul ih hdiv hb (by positivity)
        _ = (n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ (i + 1) := by ring
    · have hz : n.choose (m + i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, Nat.cast_zero]
      positivity

/-- **Union count**: the number of subsets of `X` with size in `[m, m+v]` is at
most `C(n,m) · (2n/m)^v` for `1 ≤ v`, `1 ≤ m ≤ n`. -/
lemma card_unions_le {n m v : ℕ} {X : Finset α} (hn : X.card = n) (hm : 1 ≤ m)
    (hmn : m ≤ n) (_hv : 1 ≤ v) :
    ((X.powerset.filter (fun U => m ≤ U.card ∧ U.card ≤ m + v)).card : ℝ) ≤
      (n.choose m : ℝ) * (2 * n / m) ^ v := by
  have hm' : 0 < m := by omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm'
  have hset : X.powerset.filter (fun U => m ≤ U.card ∧ U.card ≤ m + v)
      = (range (v + 1)).biUnion (fun i => X.powersetCard (m + i)) := by
    ext U
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hU, h1, h2⟩
      exact ⟨U.card - m, by omega, hU, by omega⟩
    · rintro ⟨i, hi, hU, hcardU⟩
      exact ⟨hU, by omega, by omega⟩
  have hdisj : ∀ a ∈ range (v + 1), ∀ b ∈ range (v + 1), a ≠ b →
      Disjoint (X.powersetCard (m + a)) (X.powersetCard (m + b)) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro U hUa hUb
    rw [mem_powersetCard] at hUa hUb
    obtain ⟨-, ha2⟩ := hUa
    obtain ⟨-, hb2⟩ := hUb
    exact hab (by omega)
  have hcard : (X.powerset.filter (fun U => m ≤ U.card ∧ U.card ≤ m + v)).card
      = ∑ i ∈ range (v + 1), n.choose (m + i) := by
    rw [hset, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_powersetCard, hn]
  rw [hcard]
  push_cast
  have hnm : (1 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
    rw [one_le_div hm0]
    exact_mod_cast hmn
  have h2p : ((v + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ v := by
    have hnat : ∀ w : ℕ, w + 1 ≤ 2 ^ w := by
      intro w
      induction w with
      | zero => simp
      | succ k ihk => rw [pow_succ]; omega
    exact_mod_cast hnat v
  calc ∑ i ∈ range (v + 1), (n.choose (m + i) : ℝ)
      ≤ ∑ i ∈ range (v + 1), (n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ i :=
        Finset.sum_le_sum fun i _ => choose_add_le hm hmn
    _ ≤ ∑ i ∈ range (v + 1), (n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ v := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiv : i ≤ v := by
          have := Finset.mem_range.mp hi
          omega
        have hpow : ((n : ℝ) / (m : ℝ)) ^ i ≤ ((n : ℝ) / (m : ℝ)) ^ v :=
          pow_le_pow_right₀ hnm hiv
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((v + 1 : ℕ) : ℝ) * ((n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ v) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ v * ((n.choose m : ℝ) * ((n : ℝ) / (m : ℝ)) ^ v) :=
        mul_le_mul_of_nonneg_right h2p (by positivity)
    _ = (n.choose m : ℝ) * (2 * (n : ℝ) / (m : ℝ)) ^ v := by
        rw [mul_div_assoc, mul_pow]
        ring

/-- Total σ-mass of bad members for a given `W`. -/
noncomputable def badWeight (X : Finset α) (σ : Finset α → ℕ) (v' : ℕ)
    (W : Finset α) : ℕ :=
  open scoped Classical in
  ∑ S ∈ X.powerset.filter (fun S => IsBad σ v' W S), σ S

/-- **The encoding bound** (paper Lemma 2.8, fixed-size model, constant `8`).
Summed over all `m`-subsets `W`, the bad mass is at most
`C(n,m) · (8n/m)^v · M / κ^{v'}`. -/
theorem sum_badWeight_le {X : Finset α} {σ : Finset α → ℕ} {v v' m : ℕ}
    {M κ : ℝ} (hκ : 1 ≤ κ) (hM : 0 ≤ M) (hb : WBounded X v σ)
    (hl : WLinkBounded X σ M κ) (hv : 1 ≤ v) (hm : 1 ≤ m) (hmn : m ≤ X.card) :
    (∑ W ∈ X.powersetCard m, badWeight X σ v' W : ℝ) * κ ^ v' ≤
      (X.card.choose m : ℝ) * (8 * X.card / m) ^ v * M := by
  classical
  set P := ((X.powersetCard m) ×ˢ X.powerset).filter
    (fun p => IsBad σ v' p.1 p.2) with hP
  set cands := X.powerset.filter (fun U => m ≤ U.card ∧ U.card ≤ m + v) with hcands
  -- the double sum over bad pairs
  have hpair : ∑ p ∈ P, σ p.2 = ∑ W ∈ X.powersetCard m, badWeight X σ v' W := by
    rw [hP, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun W _ => ?_
    dsimp only
    rw [← Finset.sum_filter]
    rfl
  -- fiber over `U = W ∪ S`, which has size in `[m, m+v]`
  have hmaps : ∀ p ∈ P, p.1 ∪ p.2 ∈ cands := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hW, hS⟩, hbad⟩ := hp
    rw [Finset.mem_powersetCard] at hW
    rw [Finset.mem_powerset] at hS
    rw [hcands, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset hW.1 hS, ?_, ?_⟩
    · rw [← hW.2]
      exact Finset.card_le_card Finset.subset_union_left
    · calc (p.1 ∪ p.2).card ≤ p.1.card + p.2.card := Finset.card_union_le _ _
        _ ≤ m + v := by
            have h1 := hW.2
            have h2 := (hb p.2 hbad.1).2
            omega
  have hfib : ∑ p ∈ P, σ p.2 =
      ∑ U ∈ cands, ∑ p ∈ P.filter (fun p => p.1 ∪ p.2 = U), σ p.2 :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hfe : ∀ U, P.filter (fun p => p.1 ∪ p.2 = U) =
      ((X.powersetCard m) ×ˢ X.powerset).filter
        (fun p => IsBad σ v' p.1 p.2 ∧ p.1 ∪ p.2 = U) := by
    intro U
    rw [hP, Finset.filter_filter]
  -- assemble over ℝ
  have hmain : (∑ W ∈ X.powersetCard m, (badWeight X σ v' W : ℝ)) =
      ∑ U ∈ cands, ∑ p ∈ P.filter (fun p => p.1 ∪ p.2 = U), (σ p.2 : ℝ) := by
    rw [← Nat.cast_sum, ← hpair, hfib]
    push_cast
    rfl
  rw [hmain, Finset.sum_mul]
  have hstep : ∀ U ∈ cands,
      (∑ p ∈ P.filter (fun p => p.1 ∪ p.2 = U), (σ p.2 : ℝ)) * κ ^ v' ≤
        2 ^ v * 2 ^ v * M := by
    intro U _
    have hfb := fiber_badWeight_le (m := m) (v' := v') hκ hM hb hl U
    rw [← hfe U] at hfb
    exact hfb
  calc ∑ U ∈ cands,
        (∑ p ∈ P.filter (fun p => p.1 ∪ p.2 = U), (σ p.2 : ℝ)) * κ ^ v'
      ≤ ∑ _U ∈ cands, (2 ^ v * 2 ^ v * M : ℝ) := Finset.sum_le_sum hstep
    _ = (cands.card : ℝ) * (2 ^ v * 2 ^ v * M) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (X.card.choose m : ℝ) * (2 * X.card / m) ^ v * (2 ^ v * 2 ^ v * M) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact card_unions_le rfl hm hmn hv
    _ = (X.card.choose m : ℝ) *
          ((2 * X.card / m) ^ v * (2 ^ v * 2 ^ v)) * M := by ring
    _ = (X.card.choose m : ℝ) * (8 * X.card / m) ^ v * M := by
        congr 2
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring

/-! ## The reduction round (paper Lemma 2.6)

For a `W` whose bad mass is small, every good member `S` is *replaced* by
`repl S \ W` where `repl S` is a member with `repl S \ W ⊆ S \ W` and
`|repl S \ W| ≤ v'`; the weight of `S` is pushed onto the replacement. The
resulting system on `X \ W` has width `≤ v'`, the *same* link bounds (weights
only move down onto subsets), and loses only the bad mass. If a further random
`W' ⊆ X \ W` covers a replacement, then `W ∪ W'` covers the original member. -/

/-- A canonical replacement witness for a good pair (junk `∅` for bad pairs). -/
noncomputable def repl (σ : Finset α → ℕ) (v' : ℕ) (W S : Finset α) : Finset α :=
  open scoped Classical in
  if h : ∃ S', σ S' ≠ 0 ∧ S' \ W ⊆ S \ W ∧ (S' \ W).card ≤ v' then h.choose else ∅

lemma repl_spec {σ : Finset α → ℕ} {v' : ℕ} {W S : Finset α}
    (h : ∃ S', σ S' ≠ 0 ∧ S' \ W ⊆ S \ W ∧ (S' \ W).card ≤ v') :
    σ (repl σ v' W S) ≠ 0 ∧ repl σ v' W S \ W ⊆ S \ W ∧
      (repl σ v' W S \ W).card ≤ v' := by
  classical
  rw [repl, dif_pos h]
  exact h.choose_spec

/-- A member that is not bad admits a replacement. -/
lemma not_isBad_iff {σ : Finset α → ℕ} {v' : ℕ} {W S : Finset α} (hS : σ S ≠ 0) :
    ¬ IsBad σ v' W S ↔
      ∃ S', σ S' ≠ 0 ∧ S' \ W ⊆ S \ W ∧ (S' \ W).card ≤ v' := by
  unfold IsBad
  constructor
  · intro h
    rcases not_and_or.mp h with h1 | h2
    · exact absurd hS h1
    · push Not at h2
      obtain ⟨S', h1, h2, h3⟩ := h2
      exact ⟨S', h1, h2, by omega⟩
  · rintro ⟨S', h1, h2, h3⟩ ⟨-, hall⟩
    exact absurd (hall S' h1 h2) (by omega)

/-- The reduced system on `X \ W`: mass of `S` moves to `repl S \ W`. -/
noncomputable def reduce (X : Finset α) (σ : Finset α → ℕ) (v' : ℕ)
    (W : Finset α) : Finset α → ℕ :=
  open scoped Classical in
  fun P => ∑ S ∈ X.powerset.filter
    (fun S => σ S ≠ 0 ∧ ¬ IsBad σ v' W S ∧ repl σ v' W S \ W = P), σ S

/-- The reduced system has width `≤ v'` and lives on `X \ W`. -/
lemma reduce_bounded {X : Finset α} {σ : Finset α → ℕ} {v v' : ℕ} {W : Finset α}
    (hb : WBounded X v σ) : WBounded (X \ W) v' (reduce X σ v' W) := by
  classical
  intro P hP
  rw [reduce] at hP
  obtain ⟨S, hS, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  rw [Finset.mem_filter] at hS
  obtain ⟨-, hσS, hnb, hPeq⟩ := hS
  obtain ⟨hr0, hrsub, hrcard⟩ := repl_spec ((not_isBad_iff hσS).mp hnb)
  constructor
  · rw [← hPeq]
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨(hb _ hr0).1 hx.1, hx.2⟩
  · rw [← hPeq]
    exact hrcard

/-- **Mass transport**: summing the reduced system over any collection `F₁` of
subsets of `X \ W` collects exactly the original mass of the good members whose
replacement lands in `F₁`. -/
lemma sum_reduce_eq {X : Finset α} {σ : Finset α → ℕ} {v' : ℕ} {W : Finset α}
    (F₁ : Finset (Finset α)) :
    ∑ P ∈ F₁, reduce X σ v' W P =
      ∑ S ∈ X.powerset.filter (fun S => (σ S ≠ 0 ∧ ¬ IsBad σ v' W S) ∧
        repl σ v' W S \ W ∈ F₁), σ S := by
  classical
  have hmaps : ∀ S ∈ X.powerset.filter (fun S => (σ S ≠ 0 ∧ ¬ IsBad σ v' W S) ∧
      repl σ v' W S \ W ∈ F₁), repl σ v' W S \ W ∈ F₁ :=
    fun S hS => (Finset.mem_filter.mp hS).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [reduce]
  congr 1
  ext S
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hS, hσ, hnb, hgP⟩
    exact ⟨⟨hS, ⟨hσ, hnb⟩, hgP ▸ hP⟩, hgP⟩
  · rintro ⟨⟨hS, ⟨hσ, hnb⟩, -⟩, hgP⟩
    exact ⟨hS, hσ, hnb, hgP⟩

/-- Link bounds are inherited: mass only moves onto subsets, so every link of the
reduced system is dominated by the corresponding link of the original. -/
lemma wLink_reduce_le {X : Finset α} {σ : Finset α → ℕ} {v' : ℕ}
    {W : Finset α} (T : Finset α) :
    wLink (X \ W) (reduce X σ v' W) T ≤ wLink X σ T := by
  classical
  unfold wLink
  rw [sum_reduce_eq]
  refine Finset.sum_le_sum_of_subset fun S hS => ?_
  rw [Finset.mem_filter] at hS ⊢
  obtain ⟨hS, ⟨hσ, hnb⟩, hgF⟩ := hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hgF
  obtain ⟨hrsub, -⟩ := repl_spec ((not_isBad_iff hσ).mp hnb) |>.2
  refine ⟨hS, ?_⟩
  calc T ⊆ repl σ v' W S \ W := hgF.2
    _ ⊆ S \ W := hrsub
    _ ⊆ S := Finset.sdiff_subset

lemma reduce_linkBounded {X : Finset α} {σ : Finset α → ℕ} {v' : ℕ}
    {W : Finset α} {M κ : ℝ} (hκ0 : 0 ≤ κ) (hl : WLinkBounded X σ M κ) :
    WLinkBounded (X \ W) (reduce X σ v' W) M κ := by
  intro T hT
  refine le_trans ?_ (hl T hT)
  have h := wLink_reduce_le (X := X) (σ := σ) (v' := v') (W := W) T
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (pow_nonneg hκ0 _)

/-- Total mass drops exactly by the bad mass. -/
lemma reduce_total {X : Finset α} {σ : Finset α → ℕ} {v v' : ℕ} {W : Finset α}
    (hb : WBounded X v σ) :
    wTotal X σ = wTotal (X \ W) (reduce X σ v' W) + badWeight X σ v' W := by
  classical
  have h1 : wTotal (X \ W) (reduce X σ v' W) =
      ∑ S ∈ X.powerset.filter (fun S => σ S ≠ 0 ∧ ¬ IsBad σ v' W S), σ S := by
    unfold wTotal
    rw [sum_reduce_eq]
    refine Finset.sum_congr (Finset.filter_congr fun S hS => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨⟨hσ, hnb⟩, -⟩
      exact ⟨hσ, hnb⟩
    · rintro ⟨hσ, hnb⟩
      refine ⟨⟨hσ, hnb⟩, ?_⟩
      rw [Finset.mem_powerset]
      obtain ⟨hr0, -, -⟩ := repl_spec ((not_isBad_iff hσ).mp hnb)
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨(hb _ hr0).1 hx.1, hx.2⟩
  have h2 : ∑ S ∈ X.powerset.filter (fun S => ¬ IsBad σ v' W S), σ S =
      ∑ S ∈ X.powerset.filter (fun S => σ S ≠ 0 ∧ ¬ IsBad σ v' W S), σ S := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      exact ⟨hS.1, hS.2.2⟩
    · intro S hS hS'
      rw [Finset.mem_filter] at hS
      by_contra hne
      exact hS' (Finset.mem_filter.mpr ⟨hS.1, hne, hS.2⟩)
  have h3 := Finset.sum_filter_add_sum_filter_not X.powerset
    (fun S => IsBad σ v' W S) σ
  unfold wTotal badWeight
  unfold wTotal at h1
  rw [← h3, h1, h2]
  ring

/-- Covering transfers back: a covered replacement means the original member is
covered by `W ∪ W'`. -/
lemma reduce_covered {X : Finset α} {σ : Finset α → ℕ} {v' : ℕ}
    {W W' : Finset α} (h : WCovered (reduce X σ v' W) W') :
    WCovered σ (W ∪ W') := by
  classical
  obtain ⟨P, hP0, hPW'⟩ := h
  rw [reduce] at hP0
  obtain ⟨S, hS, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP0
  rw [Finset.mem_filter] at hS
  obtain ⟨-, hσS, hnb, hPeq⟩ := hS
  obtain ⟨hr0, hrsub, -⟩ := repl_spec ((not_isBad_iff hσS).mp hnb)
  refine ⟨repl σ v' W S, hr0, ?_⟩
  intro x hx
  rw [Finset.mem_union]
  by_cases hxW : x ∈ W
  · exact Or.inl hxW
  · refine Or.inr (hPW' ?_)
    rw [← hPeq, Finset.mem_sdiff]
    exact ⟨hx, hxW⟩

/-! ## Composing a round with the remaining randomness

An uncovered `(m₁+m₂)`-set `U` splits as an `m₁`-block `W` plus the rest `U \ W`
in exactly `C(m₁+m₂, m₁)` ways. For every split, either `W` fails the `good`
predicate, or — since covering the reduced system would cover `U` — the rest is
an uncovered `m₂`-set for the reduced system on `X \ W`. This is the fixed-size
replacement for the paper's independent sampling of `W' ∼ U(X \ W, α')`. -/

lemma failCount_compose {X : Finset α} {σ : Finset α → ℕ} (v' : ℕ)
    (good : Finset α → Prop) {m₁ m₂ : ℕ} :
    failCount X σ (m₁ + m₂) * (m₁ + m₂).choose m₁ ≤
      ((X.powersetCard m₁).filter (fun W => ¬ good W)).card *
          (X.card - m₁).choose m₂ +
        ∑ W ∈ (X.powersetCard m₁).filter (fun W => good W),
          failCount (X \ W) (reduce X σ v' W) m₂ := by
  classical
  set BadU := (X.powersetCard (m₁ + m₂)).filter (fun U => ¬ WCovered σ U) with hBadU
  set A := ((X.powersetCard m₁).filter (fun W => ¬ good W)).sigma
    (fun W => (X \ W).powersetCard m₂) with hA
  set B := ((X.powersetCard m₁).filter (fun W => good W)).sigma
    (fun W => ((X \ W).powersetCard m₂).filter
      (fun V => ¬ WCovered (reduce X σ v' W) V)) with hB
  -- left side counts splits of uncovered sets
  have hL : (BadU.sigma (fun U => U.powersetCard m₁)).card =
      failCount X σ (m₁ + m₂) * (m₁ + m₂).choose m₁ := by
    rw [Finset.card_sigma]
    have hcong : ∀ U ∈ BadU, (U.powersetCard m₁).card = (m₁ + m₂).choose m₁ := by
      intro U hU
      rw [hBadU, Finset.mem_filter, Finset.mem_powersetCard] at hU
      rw [Finset.card_powersetCard, hU.1.2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, smul_eq_mul]
    simp only [failCount, hBadU]
  -- the split map is injective into `A ∪ B`
  have hcard : (BadU.sigma (fun U => U.powersetCard m₁)).card ≤ (A ∪ B).card := by
    refine Finset.card_le_card_of_injOn
      (fun p => ⟨p.2, p.1 \ p.2⟩) ?_ ?_
    · rintro ⟨U, W⟩ hp
      have hp' : U ∈ BadU ∧ W ∈ U.powersetCard m₁ := Finset.mem_sigma.mp hp
      obtain ⟨hU, hW⟩ := hp'
      rw [hBadU, Finset.mem_filter, Finset.mem_powersetCard] at hU
      obtain ⟨⟨hUX, hUcard⟩, hUuncov⟩ := hU
      rw [Finset.mem_powersetCard] at hW
      obtain ⟨hWU, hWcard⟩ := hW
      have hWX : W ∈ X.powersetCard m₁ :=
        Finset.mem_powersetCard.mpr ⟨hWU.trans hUX, hWcard⟩
      have hUWmem : U \ W ∈ (X \ W).powersetCard m₂ := by
        rw [Finset.mem_powersetCard]
        constructor
        · intro x hx
          rw [Finset.mem_sdiff] at hx ⊢
          exact ⟨hUX hx.1, hx.2⟩
        · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hWU, hUcard, hWcard]
          omega
      have hUW : W ∪ (U \ W) = U := by
        ext x
        rw [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hx | ⟨hx, -⟩)
          · exact hWU hx
          · exact hx
        · intro hx
          by_cases hxW : x ∈ W
          · exact Or.inl hxW
          · exact Or.inr ⟨hx, hxW⟩
      rw [Finset.mem_coe, Finset.mem_union]
      by_cases hgood : good W
      · refine Or.inr (Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hWX, hgood⟩, ?_⟩)
        rw [Finset.mem_filter]
        refine ⟨hUWmem, fun hcov => hUuncov ?_⟩
        have := reduce_covered (v' := v') (X := X) hcov
        rwa [hUW] at this
      · exact Or.inl (Finset.mem_sigma.mpr
          ⟨Finset.mem_filter.mpr ⟨hWX, hgood⟩, hUWmem⟩)
    · rintro ⟨U, W⟩ hp ⟨U', W'⟩ hp' heq
      rw [Finset.mem_coe] at hp hp'
      have h1 : U ∈ BadU ∧ W ∈ U.powersetCard m₁ := Finset.mem_sigma.mp hp
      have h2 : U' ∈ BadU ∧ W' ∈ U'.powersetCard m₁ := Finset.mem_sigma.mp hp'
      have hWU : W ⊆ U := (Finset.mem_powersetCard.mp h1.2).1
      have hWU' : W' ⊆ U' := (Finset.mem_powersetCard.mp h2.2).1
      simp only [Sigma.mk.injEq, heq_eq_eq] at heq
      obtain ⟨hWW, hUU⟩ := heq
      subst hWW
      have hU : U = U' := by
        calc U = W ∪ (U \ W) := by
              ext x
              rw [Finset.mem_union, Finset.mem_sdiff]
              constructor
              · intro hx
                by_cases hxW : x ∈ W
                · exact Or.inl hxW
                · exact Or.inr ⟨hx, hxW⟩
              · rintro (hx | ⟨hx, -⟩)
                · exact hWU hx
                · exact hx
          _ = W ∪ (U' \ W) := by rw [hUU]
          _ = U' := by
              ext x
              rw [Finset.mem_union, Finset.mem_sdiff]
              constructor
              · rintro (hx | ⟨hx, -⟩)
                · exact hWU' hx
                · exact hx
              · intro hx
                by_cases hxW : x ∈ W
                · exact Or.inl hxW
                · exact Or.inr ⟨hx, hxW⟩
      simp only [Sigma.mk.injEq, heq_eq_eq]
      exact ⟨hU, trivial⟩
  -- count the target
  have hAcard : A.card = ((X.powersetCard m₁).filter (fun W => ¬ good W)).card *
      (X.card - m₁).choose m₂ := by
    rw [hA, Finset.card_sigma]
    have hcong : ∀ W ∈ (X.powersetCard m₁).filter (fun W => ¬ good W),
        ((X \ W).powersetCard m₂).card = (X.card - m₁).choose m₂ := by
      intro W hW
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hW
      rw [Finset.card_powersetCard, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hW.1.1, hW.1.2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, smul_eq_mul]
  have hBcard : B.card = ∑ W ∈ (X.powersetCard m₁).filter (fun W => good W),
      failCount (X \ W) (reduce X σ v' W) m₂ := by
    rw [hB, Finset.card_sigma]
    refine Finset.sum_congr rfl fun W _ => ?_
    simp only [failCount]
  calc failCount X σ (m₁ + m₂) * (m₁ + m₂).choose m₁
      = (BadU.sigma (fun U => U.powersetCard m₁)).card := hL.symm
    _ ≤ (A ∪ B).card := hcard
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ = _ := by rw [hAcard, hBcard]

/-- **Monotonicity of the failure fraction in the budget**: a larger random set
covers more, so `failCount(m₁+m₂)/C(n,m₁+m₂) ≤ failCount(m₂)/C(n,m₂)`, stated
multiplied out. (Each uncovered `(m₁+m₂)`-set has all `C(m₁+m₂,m₂)` of its
`m₂`-subsets uncovered; each uncovered `m₂`-set has at most `C(n-m₂,m₁)`
supersets of size `m₁+m₂`.) Needed for the p-biased ↔ fixed-size bridge of the
final step. -/
lemma failCount_mono_mul {X : Finset α} {σ : Finset α → ℕ} (m₁ m₂ : ℕ) :
    failCount X σ (m₁ + m₂) * (m₁ + m₂).choose m₂ ≤
      failCount X σ m₂ * (X.card - m₂).choose m₁ := by
  classical
  set BadU := (X.powersetCard (m₁ + m₂)).filter (fun U => ¬ WCovered σ U) with hBadU
  set BadV := (X.powersetCard m₂).filter (fun V => ¬ WCovered σ V) with hBadV
  have hL : (BadU.sigma (fun U => U.powersetCard m₂)).card =
      failCount X σ (m₁ + m₂) * (m₁ + m₂).choose m₂ := by
    rw [Finset.card_sigma]
    have hcong : ∀ U ∈ BadU, (U.powersetCard m₂).card = (m₁ + m₂).choose m₂ := by
      intro U hU
      rw [hBadU, Finset.mem_filter, Finset.mem_powersetCard] at hU
      rw [Finset.card_powersetCard, hU.1.2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, smul_eq_mul]
    simp only [failCount, hBadU]
  have hR : (BadV.sigma (fun V => (X \ V).powersetCard m₁)).card =
      failCount X σ m₂ * (X.card - m₂).choose m₁ := by
    rw [Finset.card_sigma]
    have hcong : ∀ V ∈ BadV, ((X \ V).powersetCard m₁).card =
        (X.card - m₂).choose m₁ := by
      intro V hV
      rw [hBadV, Finset.mem_filter, Finset.mem_powersetCard] at hV
      rw [Finset.card_powersetCard, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hV.1.1, hV.1.2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, smul_eq_mul]
    simp only [failCount, hBadV]
  rw [← hL, ← hR]
  refine Finset.card_le_card_of_injOn (fun p => ⟨p.2, p.1 \ p.2⟩) ?_ ?_
  · rintro ⟨U, V⟩ hp
    obtain ⟨hU, hV⟩ := Finset.mem_sigma.mp hp
    rw [hBadU, Finset.mem_filter, Finset.mem_powersetCard] at hU
    obtain ⟨⟨hUX, hUcard⟩, hUuncov⟩ := hU
    rw [Finset.mem_powersetCard] at hV
    obtain ⟨hVU, hVcard⟩ := hV
    rw [Finset.mem_coe]
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · rw [hBadV, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨hVU.trans hUX, hVcard⟩, fun hcov => hUuncov (hcov.mono hVU)⟩
    · rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hUX hx.1, hx.2⟩
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hVU, hUcard, hVcard]
        omega
  · rintro ⟨U, V⟩ hp ⟨U', V'⟩ hp' heq
    rw [Finset.mem_coe] at hp hp'
    have hVU : V ⊆ U := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp).2).1
    have hVU' : V' ⊆ U' := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp').2).1
    simp only [Sigma.mk.injEq, heq_eq_eq] at heq
    obtain ⟨hVV, hUU⟩ := heq
    subst hVV
    have hU : U = U' := by
      calc U = V ∪ (U \ V) := by
            ext x
            rw [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · intro hx
              by_cases hxV : x ∈ V
              · exact Or.inl hxV
              · exact Or.inr ⟨hx, hxV⟩
            · rintro (hx | ⟨hx, -⟩)
              · exact hVU hx
              · exact hx
        _ = V ∪ (U' \ V) := by rw [hUU]
        _ = U' := by
            ext x
            rw [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · rintro (hx | ⟨hx, -⟩)
              · exact hVU' hx
              · exact hx
            · intro hx
              by_cases hxV : x ∈ V
              · exact Or.inl hxV
              · exact Or.inr ⟨hx, hxV⟩
    simp only [Sigma.mk.injEq, heq_eq_eq]
    exact ⟨hU, trivial⟩

/-- **The reduction round** (paper Lemma 2.6, fixed-size form). If every good `W`
— one whose bad mass is at most `δ·A` — admits the failure bound `β'` for its
reduced system on `X \ W` at budget `m₂`, then the failure fraction of the
original system at budget `m₁ + m₂` is at most
`(8n/m₁)^v · M / (κ^{v'} δ A) + β'`: Markov plus the encoding bound control the
probability of a bad `W`. -/
theorem round_le {X : Finset α} {σ : Finset α → ℕ} {v v' m₁ m₂ : ℕ}
    {M κ A δ β' : ℝ} (hκ : 1 ≤ κ) (hM : 0 ≤ M) (hA : 0 < A) (hδ : 0 < δ)
    (hβ' : 0 ≤ β') (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ)
    (hv : 1 ≤ v) (hm : 1 ≤ m₁) (hmn : m₁ + m₂ ≤ X.card)
    (hIH : ∀ W ∈ X.powersetCard m₁, (badWeight X σ v' W : ℝ) ≤ δ * A →
      (failCount (X \ W) (reduce X σ v' W) m₂ : ℝ) ≤
        β' * ((X.card - m₁).choose m₂ : ℝ)) :
    (failCount X σ (m₁ + m₂) : ℝ) ≤
      ((8 * X.card / m₁) ^ v * M / (κ ^ v' * δ * A) + β') *
        (X.card.choose (m₁ + m₂) : ℝ) := by
  classical
  have hκ0 : (0:ℝ) < κ := lt_of_lt_of_le one_pos hκ
  have hκp : (0:ℝ) < κ ^ v' := pow_pos hκ0 _
  have hδA : (0:ℝ) < δ * A := mul_pos hδ hA
  set n := X.card with hn
  have hCpos : (0:ℝ) < ((m₁ + m₂).choose m₁ : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  set badS := (X.powersetCard m₁).filter
    (fun W => ¬ ((badWeight X σ v' W : ℝ) ≤ δ * A)) with hbadS
  set goodS := (X.powersetCard m₁).filter
    (fun W => (badWeight X σ v' W : ℝ) ≤ δ * A) with hgoodS
  -- Markov: few W's carry more than `δ·A` bad mass
  have hmarkov : (badS.card : ℝ) * (δ * A) ≤
      (n.choose m₁ : ℝ) * (8 * n / m₁) ^ v * M / κ ^ v' := by
    have h1 : (badS.card : ℝ) * (δ * A) ≤
        ∑ W ∈ X.powersetCard m₁, (badWeight X σ v' W : ℝ) := by
      calc (badS.card : ℝ) * (δ * A) = ∑ _W ∈ badS, (δ * A) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ W ∈ badS, (badWeight X σ v' W : ℝ) := by
            refine Finset.sum_le_sum fun W hW => ?_
            rw [hbadS, Finset.mem_filter] at hW
            exact (not_le.mp hW.2).le
        _ ≤ ∑ W ∈ X.powersetCard m₁, (badWeight X σ v' W : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) fun W _ _ => Nat.cast_nonneg _
    have h2 := sum_badWeight_le (v' := v') hκ hM hb hl hv hm (by omega)
    rw [le_div_iff₀ hκp]
    calc (badS.card : ℝ) * (δ * A) * κ ^ v'
        ≤ (∑ W ∈ X.powersetCard m₁, (badWeight X σ v' W : ℝ)) * κ ^ v' :=
          mul_le_mul_of_nonneg_right h1 hκp.le
      _ ≤ _ := h2
  have hbadcard : (badS.card : ℝ) * (κ ^ v' * δ * A) ≤
      (n.choose m₁ : ℝ) * ((8 * n / m₁) ^ v * M) := by
    have h := (le_div_iff₀ hκp).mp hmarkov
    calc (badS.card : ℝ) * (κ ^ v' * δ * A)
        = (badS.card : ℝ) * (δ * A) * κ ^ v' := by ring
      _ ≤ (n.choose m₁ : ℝ) * (8 * n / m₁) ^ v * M := h
      _ = (n.choose m₁ : ℝ) * ((8 * n / m₁) ^ v * M) := by ring
  set Γ := (8 * (n:ℝ) / m₁) ^ v * M / (κ ^ v' * δ * A) with hΓ
  have hbad2 : (badS.card : ℝ) ≤ (n.choose m₁ : ℝ) * Γ := by
    have hD : (0:ℝ) < κ ^ v' * δ * A := by positivity
    rw [hΓ, ← mul_div_assoc, le_div_iff₀ hD]
    exact hbadcard
  -- the composition inequality, cast to ℝ
  have hcomp := failCount_compose (X := X) (σ := σ) v'
    (fun W => (badWeight X σ v' W : ℝ) ≤ δ * A) (m₁ := m₁) (m₂ := m₂)
  have hcompR : (failCount X σ (m₁ + m₂) : ℝ) * (((m₁ + m₂).choose m₁ : ℕ) : ℝ) ≤
      (badS.card : ℝ) * (((n - m₁).choose m₂ : ℕ) : ℝ) +
        ∑ W ∈ goodS, (failCount (X \ W) (reduce X σ v' W) m₂ : ℝ) := by
    rw [hgoodS, hbadS]
    exact_mod_cast hcomp
  -- the IH bound over good W's
  have hIHsum : ∑ W ∈ goodS, (failCount (X \ W) (reduce X σ v' W) m₂ : ℝ) ≤
      (n.choose m₁ : ℝ) * (β' * (((n - m₁).choose m₂ : ℕ) : ℝ)) := by
    calc ∑ W ∈ goodS, (failCount (X \ W) (reduce X σ v' W) m₂ : ℝ)
        ≤ ∑ _W ∈ goodS, β' * (((n - m₁).choose m₂ : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun W hW => ?_
          rw [hgoodS, Finset.mem_filter] at hW
          exact hIH W hW.1 hW.2
      _ = (goodS.card : ℝ) * (β' * (((n - m₁).choose m₂ : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n.choose m₁ : ℝ) * (β' * (((n - m₁).choose m₂ : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : goodS.card ≤ (X.powersetCard m₁).card :=
            Finset.card_filter_le _ _
          rw [Finset.card_powersetCard] at this
          exact_mod_cast this
  -- assemble and cancel `C(m₁+m₂, m₁)`
  refine le_of_mul_le_mul_right ?_ hCpos
  calc (failCount X σ (m₁ + m₂) : ℝ) * (((m₁ + m₂).choose m₁ : ℕ) : ℝ)
      ≤ (badS.card : ℝ) * (((n - m₁).choose m₂ : ℕ) : ℝ) +
        ∑ W ∈ goodS, (failCount (X \ W) (reduce X σ v' W) m₂ : ℝ) := hcompR
    _ ≤ ((n.choose m₁ : ℝ) * Γ) * (((n - m₁).choose m₂ : ℕ) : ℝ) +
        (n.choose m₁ : ℝ) * (β' * (((n - m₁).choose m₂ : ℕ) : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hbad2 (Nat.cast_nonneg _)) hIHsum
    _ = (Γ + β') * ((n.choose m₁ : ℝ) * (((n - m₁).choose m₂ : ℕ) : ℝ)) := by
        ring
    _ = (Γ + β') * ((n.choose (m₁ + m₂) : ℝ) * (((m₁ + m₂).choose m₁ : ℕ) : ℝ)) := by
        congr 1
        have hid := Nat.choose_mul (n := n) (k := m₁ + m₂) (s := m₁)
          (Nat.le_add_right _ _)
        have h' : m₁ + m₂ - m₁ = m₂ := by omega
        rw [h'] at hid
        exact_mod_cast hid.symm
    _ = ((Γ + β') * (n.choose (m₁ + m₂) : ℝ)) * (((m₁ + m₂).choose m₁ : ℕ) : ℝ) := by
        ring

/-! ## The disjointness step (paper Lemma 1.6, fixed-size form)

A uniform partition of a `⌊n/r⌋·r`-subset into `r` blocks makes each block a
uniform `m`-subset; if the failure fraction is below `1/r`, a union bound
leaves a tuple of pairwise disjoint covered blocks, whose covering members
are distinct (they are nonempty and live in disjoint blocks). Formalized via
the recursion `coveredTuples` and the exact double count
`sum_failCount_sdiff`. -/

private lemma filter_powersetCard_sdiff (X W : Finset α) (σ : Finset α → ℕ) (m : ℕ) :
    ((X \ W).powersetCard m).filter (fun V => ¬ WCovered σ V)
      = (X.powersetCard m).filter (fun V => Disjoint V W ∧ ¬ WCovered σ V) := by
  ext V
  simp only [mem_filter, mem_powersetCard, Finset.subset_sdiff]
  tauto

/-- Symmetric double count: pairs of disjoint m-sets with the second uncovered. -/
lemma sum_failCount_sdiff (X : Finset α) (σ : Finset α → ℕ) (m : ℕ) :
    ∑ W ∈ X.powersetCard m, failCount (X \ W) σ m
      = failCount X σ m * (X.card - m).choose m := by
  have key : ∀ V ∈ (X.powersetCard m).filter (fun V => ¬ WCovered σ V),
      ((X.powersetCard m).filter (fun W => Disjoint V W)).card
        = (X.card - m).choose m := by
    intro V hV
    rw [mem_filter, mem_powersetCard] at hV
    have hset : (X.powersetCard m).filter (fun W => Disjoint V W)
        = (X \ V).powersetCard m := by
      ext W
      simp only [mem_filter, mem_powersetCard, Finset.subset_sdiff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h3.symm⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩
        exact ⟨⟨h1, h2⟩, h3.symm⟩
    rw [hset, card_powersetCard]
    have h1 := Finset.card_sdiff_add_card_eq_card hV.1.1
    have h2 := hV.1.2
    congr 1
    omega
  calc ∑ W ∈ X.powersetCard m, failCount (X \ W) σ m
      = ∑ W ∈ X.powersetCard m, ∑ V ∈ X.powersetCard m,
          (if Disjoint V W ∧ ¬ WCovered σ V then 1 else 0) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        unfold failCount
        rw [filter_powersetCard_sdiff, Finset.card_filter]
    _ = ∑ V ∈ X.powersetCard m, ∑ W ∈ X.powersetCard m,
          (if Disjoint V W ∧ ¬ WCovered σ V then 1 else 0) := Finset.sum_comm
    _ = ∑ V ∈ X.powersetCard m,
          (if ¬ WCovered σ V then
            ((X.powersetCard m).filter (fun W => Disjoint V W)).card else 0) := by
        refine Finset.sum_congr rfl fun V _ => ?_
        by_cases h : WCovered σ V
        · simp [h]
        · simp only [h, not_false_eq_true, and_true, if_true]
          rw [Finset.card_filter]
    _ = ∑ V ∈ (X.powersetCard m).filter (fun V => ¬ WCovered σ V),
          ((X.powersetCard m).filter (fun W => Disjoint V W)).card := by
        rw [Finset.sum_filter]
    _ = ∑ V ∈ (X.powersetCard m).filter (fun V => ¬ WCovered σ V),
          (X.card - m).choose m := Finset.sum_congr rfl key
    _ = failCount X σ m * (X.card - m).choose m := by
        rw [Finset.sum_const, smul_eq_mul]
        rfl

/-- Number of r-tuples of pairwise disjoint covered m-blocks, as a recursion. -/
noncomputable def coveredTuples (σ : Finset α → ℕ) (m : ℕ) :
    Finset α → ℕ → ℕ
  | _, 0 => 1
  | X, (r+1) => ∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
      coveredTuples σ m (X \ W) r

/-- Lower bound: coveredTuples ≥ (∏ C(n - i·m, m)) · (1 - r·failfrac), stated
multiplied out over ℝ. -/
lemma coveredTuples_lower (σ : Finset α → ℕ) (m : ℕ) :
    ∀ (r : ℕ) (X : Finset α), r * m ≤ X.card →
    ((∏ i ∈ range r, (X.card - i * m).choose m : ℕ) : ℝ)
        * (1 - r * (failCount X σ m : ℝ) / (X.card.choose m : ℝ))
      ≤ (coveredTuples σ m X r : ℝ) := by
  intro r
  induction r with
  | zero =>
      intro X _
      simp [coveredTuples]
  | succ r ih =>
      intro X hcard
      have hmul : (r + 1) * m = r * m + m := by ring
      have hrm : r * m + m ≤ X.card := by rw [← hmul]; exact hcard
      have hm : m ≤ X.card := le_trans (Nat.le_add_left m (r * m)) hrm
      have hCpos : 0 < X.card.choose m := Nat.choose_pos hm
      have hCne : ((X.card.choose m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hCpos.ne'
      -- the covered filter has cardinality (choose) − failCount
      have hcovcard : ((X.powersetCard m).filter (fun W => WCovered σ W)).card
          + failCount X σ m = X.card.choose m := by
        unfold failCount
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
          ← Finset.card_powersetCard m X, Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun W _ => ?_
        by_cases h : WCovered σ W <;> simp [h]
      have hcovR : ((((X.powersetCard m).filter (fun W => WCovered σ W)).card : ℕ) : ℝ)
          = (X.card.choose m : ℝ) - (failCount X σ m : ℝ) := by
        have h2 : ((((X.powersetCard m).filter (fun W => WCovered σ W)).card : ℕ) : ℝ)
            + (failCount X σ m : ℝ) = (X.card.choose m : ℝ) := by
          exact_mod_cast hcovcard
        linarith
      -- card of X \ W for covered W
      have hXWcard : ∀ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
          (X \ W).card = X.card - m := by
        intro W hW
        rw [mem_filter, mem_powersetCard] at hW
        have h1 := Finset.card_sdiff_add_card_eq_card hW.1.1
        have h2 := hW.1.2
        omega
      -- induction hypothesis, specialized to X \ W
      have hIH : ∀ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
          ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            * (1 - r * (failCount (X \ W) σ m : ℝ) / ((X.card - m).choose m : ℝ))
          ≤ (coveredTuples σ m (X \ W) r : ℝ) := by
        intro W hW
        have hc := hXWcard W hW
        have h0 : r * m ≤ (X \ W).card := by
          rw [hc]; exact Nat.le_sub_of_add_le hrm
        have h1 := ih (X \ W) h0
        rwa [hc] at h1
      -- product reindexing
      have hprod : (∏ i ∈ range (r + 1), (X.card - i * m).choose m)
          = (∏ i ∈ range r, (X.card - m - i * m).choose m) * X.card.choose m := by
        rw [Finset.prod_range_succ']
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          show (X.card - (i + 1) * m).choose m = (X.card - m - i * m).choose m
          congr 1
          rw [Nat.sub_sub]
          congr 1
          ring
        · show (X.card - 0 * m).choose m = X.card.choose m
          norm_num
      -- C' is nonzero as soon as r ≠ 0
      have hC'ne : r ≠ 0 → (((X.card - m).choose m : ℕ) : ℝ) ≠ 0 := by
        intro hr
        have h1r : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
        have h2 : m ≤ r * m := by
          have := Nat.mul_le_mul h1r (le_refl m)
          simpa using this
        have h4 : m + m ≤ X.card := le_trans (Nat.add_le_add_right h2 m) hrm
        have h5 : m ≤ X.card - m := Nat.le_sub_of_add_le h4
        exact Nat.cast_ne_zero.mpr (Nat.choose_pos h5).ne'
      -- the key cancellation
      have hkey : (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            / ((X.card - m).choose m : ℝ)
            * ((failCount X σ m : ℝ) * ((X.card - m).choose m : ℝ))
          = (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            * (failCount X σ m : ℝ) := by
        rcases eq_or_ne r 0 with hr | hr
        · subst hr; simp
        · have hC' := hC'ne hr
          have hre : (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                / ((X.card - m).choose m : ℝ)
                * ((failCount X σ m : ℝ) * ((X.card - m).choose m : ℝ))
              = (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                * (failCount X σ m : ℝ)
                * (((X.card - m).choose m : ℝ) / ((X.card - m).choose m : ℝ)) := by
            ring
          rw [hre, div_self hC', mul_one]
      -- summed form of lemma (1)
      have hsum1 : (∑ W ∈ X.powersetCard m, (failCount (X \ W) σ m : ℝ))
          = (failCount X σ m : ℝ) * ((X.card - m).choose m : ℝ) := by
        rw [← Nat.cast_sum, sum_failCount_sdiff, Nat.cast_mul]
      -- the recursion, cast to ℝ
      have hcast : (coveredTuples σ m X (r + 1) : ℝ)
          = ∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
              (coveredTuples σ m (X \ W) r : ℝ) := by
        simp only [coveredTuples]
        rw [Nat.cast_sum]
      -- normalize the cast of (r+1)
      rw [Nat.cast_add, Nat.cast_one]
      calc ((∏ i ∈ range (r + 1), (X.card - i * m).choose m : ℕ) : ℝ)
            * (1 - ((r : ℝ) + 1) * (failCount X σ m : ℝ) / (X.card.choose m : ℝ))
          = ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
              * (X.card.choose m : ℝ)
              - ((r : ℝ) + 1)
                * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                * (failCount X σ m : ℝ) := by
            rw [hprod, Nat.cast_mul]
            have hre : ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                  * ((X.card.choose m : ℕ) : ℝ)
                  * (1 - ((r : ℝ) + 1) * (failCount X σ m : ℝ) / (X.card.choose m : ℝ))
                = ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                    * (X.card.choose m : ℝ)
                  - ((r : ℝ) + 1)
                    * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                    * (failCount X σ m : ℝ)
                    * ((X.card.choose m : ℝ) / (X.card.choose m : ℝ)) := by
              ring
            rw [hre, div_self hCne, mul_one]
        _ = ((X.card.choose m : ℝ) - (failCount X σ m : ℝ))
              * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            - (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
              * (failCount X σ m : ℝ) := by ring
        _ = ((((X.powersetCard m).filter (fun W => WCovered σ W)).card : ℕ) : ℝ)
              * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            - (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
              * (failCount X σ m : ℝ) := by rw [hcovR]
        _ = ((((X.powersetCard m).filter (fun W => WCovered σ W)).card : ℕ) : ℝ)
              * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            - (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                / ((X.card - m).choose m : ℝ)
              * ((failCount X σ m : ℝ) * ((X.card - m).choose m : ℝ)) := by rw [hkey]
        _ = ((((X.powersetCard m).filter (fun W => WCovered σ W)).card : ℕ) : ℝ)
              * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            - (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                / ((X.card - m).choose m : ℝ)
              * (∑ W ∈ X.powersetCard m, (failCount (X \ W) σ m : ℝ)) := by rw [hsum1]
        _ ≤ ((((X.powersetCard m).filter (fun W => WCovered σ W)).card : ℕ) : ℝ)
              * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
            - (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                / ((X.card - m).choose m : ℝ)
              * (∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
                  (failCount (X \ W) σ m : ℝ)) := by
            have hq : 0 ≤ (r : ℝ)
                * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                / ((X.card - m).choose m : ℝ) := by positivity
            have hss : (∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
                  (failCount (X \ W) σ m : ℝ))
                ≤ ∑ W ∈ X.powersetCard m, (failCount (X \ W) σ m : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun i _ _ => Nat.cast_nonneg _)
            have := mul_le_mul_of_nonneg_left hss hq
            linarith
        _ = ∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
              (((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                - (r : ℝ) * ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                    / ((X.card - m).choose m : ℝ)
                  * (failCount (X \ W) σ m : ℝ)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        _ = ∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
              ((∏ i ∈ range r, (X.card - m - i * m).choose m : ℕ) : ℝ)
                * (1 - (r : ℝ) * (failCount (X \ W) σ m : ℝ)
                    / ((X.card - m).choose m : ℝ)) :=
            Finset.sum_congr rfl fun W _ => by ring
        _ ≤ ∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
              (coveredTuples σ m (X \ W) r : ℝ) := Finset.sum_le_sum hIH
        _ = (coveredTuples σ m X (r + 1) : ℝ) := hcast.symm

/-- Extraction: positive tuple count yields r pairwise disjoint nonempty members. -/
lemma exists_disjoint_of_coveredTuples_pos (σ : Finset α → ℕ) (m : ℕ)
    (hne : ∀ S, σ S ≠ 0 → S.Nonempty) :
    ∀ (r : ℕ) (X : Finset α), 0 < coveredTuples σ m X r →
    ∃ 𝒟 : Finset (Finset α), 𝒟.card = r ∧ (∀ S ∈ 𝒟, σ S ≠ 0 ∧ S ⊆ X) ∧
      (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  intro r
  induction r with
  | zero =>
      intro X _
      refine ⟨∅, by simp, by simp, ?_⟩
      simp only [Finset.coe_empty]
      exact Set.pairwiseDisjoint_empty
  | succ r ih =>
      intro X hpos
      have hpos' : (∑ W ∈ (X.powersetCard m).filter (fun W => WCovered σ W),
          coveredTuples σ m (X \ W) r) ≠ 0 := by
        simpa only [coveredTuples] using hpos.ne'
      obtain ⟨W, hWmem, hWne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos'
      rw [mem_filter, mem_powersetCard] at hWmem
      obtain ⟨⟨hWX, _hWcard⟩, hWcov⟩ := hWmem
      obtain ⟨𝒟', hcard', hmem', hdisj'⟩ := ih (X \ W) (Nat.pos_of_ne_zero hWne)
      obtain ⟨S, hSne, hSW⟩ := hWcov
      have hSX : S ⊆ X := hSW.trans hWX
      have hSnotin : S ∉ 𝒟' := by
        intro hS
        obtain ⟨x, hx⟩ := hne S hSne
        have hxXW : x ∈ X \ W := (hmem' S hS).2 hx
        exact (Finset.mem_sdiff.mp hxXW).2 (hSW hx)
      refine ⟨insert S 𝒟', ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hSnotin, hcard']
      · intro T hT
        rcases Finset.mem_insert.mp hT with rfl | hT'
        · exact ⟨hSne, hSX⟩
        · exact ⟨(hmem' T hT').1, (hmem' T hT').2.trans Finset.sdiff_subset⟩
      · rw [Finset.coe_insert]
        refine hdisj'.insert fun T hT hTS => ?_
        have hTsub : T ⊆ X \ W := (hmem' T (Finset.mem_coe.mp hT)).2
        simp only [id_eq]
        rw [Finset.disjoint_left]
        intro x hxS hxT
        exact (Finset.mem_sdiff.mp (hTsub hxT)).2 (hSW hxS)

end SpreadCore

end Sunflower

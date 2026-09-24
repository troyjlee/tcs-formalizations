/-
# The Bell–Chueluecha–Warnke improvement: `2r` colours

ALWZ's Lemma 1.6 (`Robust.exists_pairwiseDisjoint_of_isSatisfying`) colours the ground set
with `r` colours and needs **every** class to swallow a member — hence the failure budget
`b = 1/r`, which is what puts the `log r` into the final bound.

The note's observation: colour with `q = 2r` colours instead and ask only that **at least
`r` of the `q`** classes succeed. Linearity of expectation replaces the union bound: each
class succeeds with probability more than `1 − b`, so the expected number of successful
classes exceeds `q(1 − b)`, and some colouring realises at least `⌈q(1−b)⌉ ≥ r` successes.
Now `b = 1/2` suffices, the `log r` disappears, and the sunflower bound drops to
`(C r log w)^w`.

`exists_pairwiseDisjoint_of_many_colours` is that argument for any `(q, r, b)` with
`r ≤ q(1 − b)`; it double-counts successful `(colouring, colour)` pairs through
`card_colourings_eq_pBiased`, exactly as Lemma 1.6 did, and swaps the union bound for the
average. `exists_pairwiseDisjoint_of_raoSpread` is the note's specialization
`q = 2r, δ = 1/(2r), b = 1/2`, fed by the Rao-route satisfying theorem: an absolutely
`R`-spread `w`-uniform family with `R ≥ 2⁵⁶·r·(log(2w) + 1)` and at least `R^w` members
contains `r` pairwise disjoint members.

The closing section exports the note's statements source-shaped: `bcw_theorem3` is
Theorem 3 verbatim (existential absolute `B`, `k ≥ 2`, `0 < δ, ε ≤ 1/2`, natural log, and
only the lower bound `|𝓕| ≥ r^k` — the trimming is composed in); `bcw_disjoint` is the
generalized corollary giving `⌊δ⁻¹⌋(1 − ε)` disjoint sets; and `rao_disjoint_original`
preserves Rao's own `δ = ε = 1/r` union-bound route (ALWZ Lemma 1.6) independently of the
`2r`-colour improvement. Lemma 4, the matching lower bound, is `Sunflower.BCWLower`.
-/
import Sunflower.RaoSchedule

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- **The `q`-colour extraction.** If `𝓕` is `(1/q, b)`-satisfying on `X` and
`r ≤ q(1 − b)`, then `𝓕` contains `r` pairwise disjoint members: colour `X` with `q`
colours; by linearity of expectation some colouring has at least `r` successful classes,
and members inside distinct classes are disjoint. ALWZ's Lemma 1.6 is the case `q = r`,
`b = 1/r`, where "at least `r` of `r`" degenerates to the union bound. -/
theorem exists_pairwiseDisjoint_of_many_colours {q r : ℕ} (hq : 0 < q) {X : Finset α}
    {𝓕 : Finset (Finset α)} {b : ℝ} (hemp : ∅ ∉ 𝓕)
    (h : IsSatisfying (1 / (q : ℝ)) b X 𝓕) (hrate : (r : ℝ) ≤ (q : ℝ) * (1 - b)) :
    ∃ 𝒟 ⊆ 𝓕, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  classical
  have hpow : (0 : ℝ) < (q : ℝ) ^ X.card := by
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    positivity
  -- each colour class succeeds on more than a `(1−b)`-fraction of the colourings
  have hsucc : ∀ i : Fin q,
      (q : ℝ) ^ X.card * (1 - b)
        < (((Finset.univ : Finset ({x // x ∈ X} → Fin q)).filter
            (fun c => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ) := by
    intro i
    rw [card_colourings_eq_pBiased hq X i (fun R => ∃ S ∈ 𝓕, S ⊆ R)]
    exact mul_lt_mul_of_pos_left h hpow
  -- double count successful `(colouring, colour)` pairs
  have hswap : ∑ c : {x // x ∈ X} → Fin q,
        ((Finset.univ : Finset (Fin q)).filter
          (fun i => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card
      = ∑ i : Fin q, (((Finset.univ : Finset ({x // x ∈ X} → Fin q)).filter
          (fun c => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- linearity of expectation: some colouring has at least `r` successful classes
  have hexists : ∃ c : {x // x ∈ X} → Fin q,
      r ≤ ((Finset.univ : Finset (Fin q)).filter
        (fun i => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card := by
    by_contra hcon
    push Not at hcon
    have hcardu : ((Finset.univ : Finset ({x // x ∈ X} → Fin q)).card : ℝ)
        = (q : ℝ) ^ X.card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
      push_cast
      ring
    -- upper bound: every colouring contributes at most `r − 1`
    have hub : ∑ c : {x // x ∈ X} → Fin q,
        (((Finset.univ : Finset (Fin q)).filter
          (fun i => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ)
        ≤ (q : ℝ) ^ X.card * ((r : ℝ) - 1) := by
      calc ∑ c : {x // x ∈ X} → Fin q,
            (((Finset.univ : Finset (Fin q)).filter
              (fun i => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ)
          ≤ ∑ _c : {x // x ∈ X} → Fin q, ((r : ℝ) - 1) := by
            refine Finset.sum_le_sum fun c _ => ?_
            have hlt := hcon c
            have h1 : (((Finset.univ : Finset (Fin q)).filter
                (fun i => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ) + 1 ≤ (r : ℝ) := by
              exact_mod_cast hlt
            linarith
        _ = ((Finset.univ : Finset ({x // x ∈ X} → Fin q)).card : ℝ) * ((r : ℝ) - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (q : ℝ) ^ X.card * ((r : ℝ) - 1) := by rw [hcardu]
    -- lower bound: the column sums each exceed `q^n(1−b)`
    have hlb : (q : ℝ) ^ X.card * ((q : ℝ) * (1 - b))
        < ∑ i : Fin q, (((Finset.univ : Finset ({x // x ∈ X} → Fin q)).filter
            (fun c => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ) := by
      have hsum := Finset.sum_lt_sum_of_nonempty
        (s := (Finset.univ : Finset (Fin q))) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
        (f := fun _ : Fin q => (q : ℝ) ^ X.card * (1 - b))
        (g := fun i : Fin q => (((Finset.univ : Finset ({x // x ∈ X} → Fin q)).filter
            (fun c => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ))
        (fun i _ => hsucc i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      calc (q : ℝ) ^ X.card * ((q : ℝ) * (1 - b))
          = (q : ℝ) * ((q : ℝ) ^ X.card * (1 - b)) := by ring
        _ < _ := hsum
    -- combine through the swap
    have hswapR : ∑ c : {x // x ∈ X} → Fin q,
          (((Finset.univ : Finset (Fin q)).filter
            (fun i => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ)
        = ∑ i : Fin q, (((Finset.univ : Finset ({x // x ∈ X} → Fin q)).filter
            (fun c => ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hswap
    have hrq : (q : ℝ) ^ X.card * (r : ℝ) ≤ (q : ℝ) ^ X.card * ((q : ℝ) * (1 - b)) :=
      mul_le_mul_of_nonneg_left hrate hpow.le
    rw [← hswapR] at hlb
    linarith [hub, hlb, hrq, hpow]
  -- select `r` successful classes and one member inside each
  obtain ⟨c, hc⟩ := hexists
  obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hc
  have hIsucc : ∀ i ∈ I, ∃ S ∈ 𝓕, S ⊆ colourClass X c i := fun i hi =>
    (Finset.mem_filter.mp (hIsub hi)).2
  choose S hS hSsub using hIsucc
  have hSne : ∀ i (hi : i ∈ I), S i hi ≠ ∅ := fun i hi h0 => hemp (h0 ▸ hS i hi)
  have hdisj : ∀ i (hi : i ∈ I) j (hj : j ∈ I), i ≠ j → Disjoint (S i hi) (S j hj) :=
    fun i hi j hj hij => (colourClass_disjoint hij).mono (hSsub i hi) (hSsub j hj)
  have hinj : ∀ i (hi : i ∈ I) j (hj : j ∈ I), S i hi = S j hj → i = j := by
    intro i hi j hj heq
    by_contra hne
    have hd := hdisj i hi j hj hne
    rw [heq] at hd
    exact hSne j hj (Finset.eq_empty_iff_forall_notMem.mpr fun x hx =>
      Finset.disjoint_left.mp hd hx hx)
  have hinj' : Function.Injective (fun i : {i // i ∈ I} => S i.1 i.2) := by
    intro i j heq
    exact Subtype.ext (hinj i.1 i.2 j.1 j.2 heq)
  refine ⟨I.attach.image (fun i => S i.1 i.2), ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hT
    exact hS i.1 i.2
  · rw [Finset.card_image_of_injective _ hinj', Finset.card_attach, hIcard]
  · intro T hT U hU hTU
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hU)
    refine hdisj i.1 i.2 j.1 j.2 fun hij => hTU ?_
    have hij' : i = j := Subtype.ext hij
    rw [hij']

open Rao in
/-- **The note's disjointness lemma.** An absolutely `R`-spread `w`-uniform family with at
least `R^w` members contains `r` pairwise disjoint members once

  `R ≥ 2⁵⁶ · r · (log(2w) + 1)`.

This is Rao's spread-to-disjoint estimate with the `2r`-colour improvement: trimming reduces
to the threshold, `rao_isSatisfying_of_kappa` at `δ = 1/(2r), ε = 1/2` makes the family
satisfying, and `exists_pairwiseDisjoint_of_many_colours` at `q = 2r, b = 1/2` extracts the
disjoint members — the rate condition `r ≤ 2r·(1 − 1/2)` holding with equality. -/
theorem exists_pairwiseDisjoint_of_raoSpread {w r : ℕ} {R : ℝ} {X : Finset α}
    {𝓕 : Finset (Finset α)} (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : IsUniform w 𝓕)
    (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 2 ^ 56 * (r : ℝ) * (Real.log (2 * (w : ℝ)) + 1) ≤ R) :
    ∃ 𝒟 ⊆ 𝓕, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  classical
  have hq : 0 < 2 * r := by omega
  have hq0 : (0 : ℝ) < ((2 * r : ℕ) : ℝ) := by exact_mod_cast hq
  -- the family is `(1/(2r), 1/2)`-satisfying, via trimming and the schedule
  have hsat : IsSatisfying (1 / ((2 * r : ℕ) : ℝ)) (1 / 2) X 𝓕 := by
    refine isSatisfying_of_raoSpread hw hu hsp hSX hcard
      (one_div_pos.mpr hq0) ?_ (by norm_num) (by norm_num) ?_
    · rw [div_le_one hq0]
      exact_mod_cast hq
    · -- `2⁵⁵·(1/(2r))⁻¹·(log(w/(1/2)) + 1) = 2⁵⁶·r·(log(2w) + 1)`
      rw [one_div, inv_inv, one_div, div_inv_eq_mul, mul_comm (w : ℝ) 2]
      push_cast
      linarith [hR]
  -- extract via the `2r`-colour argument
  have hemp : ∅ ∉ 𝓕 := fun h0 => by
    have hc := hu h0
    rw [Finset.card_empty] at hc
    omega
  have hrate : (r : ℝ) ≤ ((2 * r : ℕ) : ℝ) * (1 - 1 / 2) := by
    push_cast
    linarith
  exact exists_pairwiseDisjoint_of_many_colours hq hemp hsat hrate

/-! ## The note's statements, source-shaped -/

open Rao in
/-- **BCW Theorem 3, as stated in the note.** There is a `B ≥ 1` such that for every integer
`k ≥ 2`, reals `0 < δ, ε ≤ 1/2` and `r ≥ B·δ⁻¹·log(k/ε)`, every `r`-spread family of
`k`-element subsets of `X` with at least `r^k` members is `(δ, ε)`-satisfying. (Here
`w`, `R` play the note's `k`, `r`, and the trimming to `⌈R^w⌉` is composed in — only the
lower bound `|𝓕| ≥ R^w` remains.) The proved statement is stronger — `w ≥ 1` and
`0 < δ, ε ≤ 1` suffice, see `Rao.isSatisfying_of_raoSpread` — but this is the note's
shape. -/
theorem bcw_theorem3_explicit : ∀ (w : ℕ) (R δ ε : ℝ)
    (X : Finset α) (𝓕 : Finset (Finset α)),
    2 ≤ w → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ 1 / 2 →
    IsUniform w 𝓕 → IsRaoSpread R w 𝓕 → (∀ T ∈ 𝓕, T ⊆ X) →
    2 ^ 56 * δ⁻¹ * Real.log ((w : ℝ) / ε) ≤ R → R ^ w ≤ ((𝓕.card : ℕ) : ℝ) →
    IsSatisfying δ ε X 𝓕 := by
  intro w R δ ε X 𝓕 hw hδ0 hδ1 hε0 hε1 hu hsp hSX hR hcard
  refine isSatisfying_of_raoSpread (by omega) hu hsp hSX hcard
    hδ0 (by linarith) hε0 (by linarith) ?_
  -- `log(w/ε) ≥ log 4 ≥ 1`, so `L + 1 ≤ 2L` and `2⁵⁵·δ⁻¹·(L+1) ≤ 2⁵⁶·δ⁻¹·L ≤ R`
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hwε4 : (4 : ℝ) ≤ (w : ℝ) / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hw2R, hε1]
  have hL1 : (1 : ℝ) ≤ Real.log ((w : ℝ) / ε) := by
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hwε4
    have h4e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
      ring
    nlinarith [Real.log_two_gt_d9]
  have hδinv0 : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ0
  nlinarith [hR, hδinv0, hL1]

/-- Existential form of `bcw_theorem3_explicit`. -/
theorem bcw_theorem3 : ∃ B : ℝ, 1 ≤ B ∧ ∀ (w : ℕ) (R δ ε : ℝ)
    (X : Finset α) (𝓕 : Finset (Finset α)),
    2 ≤ w → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ 1 / 2 →
    IsUniform w 𝓕 → IsRaoSpread R w 𝓕 → (∀ T ∈ 𝓕, T ⊆ X) →
    B * δ⁻¹ * Real.log ((w : ℝ) / ε) ≤ R → R ^ w ≤ ((𝓕.card : ℕ) : ℝ) →
    IsSatisfying δ ε X 𝓕 := by
  exact ⟨2 ^ 56, by norm_num, bcw_theorem3_explicit⟩

open Rao in
/-- **Rao's spread-to-disjoint estimate, preserved as its own route.** At `δ = ε = 1/r` and
the union bound (`exists_pairwiseDisjoint_of_isSatisfying` — ALWZ Lemma 1.6, `r` colours),
an absolutely `R`-spread family with `R ≥ 2⁵⁵·r·(log(rw) + 1)` contains `r` disjoint
members. This is the `O(r·log(rw))` estimate of *Coding for Sunflowers*, independent of the
note's `2r`-colour improvement — the two routes to disjointness share only the satisfying
theorem. -/
theorem rao_disjoint_original {w r : ℕ} {R : ℝ} {X : Finset α} {𝓕 : Finset (Finset α)}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕)
    (hSX : ∀ S ∈ 𝓕, S ⊆ X) (hcard : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 2 ^ 55 * (r : ℝ) * (Real.log ((r : ℝ) * (w : ℝ)) + 1) ≤ R) :
    ∃ 𝒟 ⊆ 𝓕, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  have hr0R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsat : IsSatisfying (1 / (r : ℝ)) (1 / (r : ℝ)) X 𝓕 := by
    refine isSatisfying_of_raoSpread hw hu hsp hSX hcard
      (one_div_pos.mpr hr0R) ?_ (one_div_pos.mpr hr0R) ?_ ?_
    · rw [div_le_one hr0R]
      exact_mod_cast hr
    · rw [div_le_one hr0R]
      exact_mod_cast hr
    · -- both `δ` and `ε` are `1/r`, so one `one_div` pass rewrites the pair at once
      rw [one_div, inv_inv, div_inv_eq_mul, mul_comm (w : ℝ) (r : ℝ)]
      linarith [hR]
  have hemp : ∅ ∉ 𝓕 := fun h0 => by
    have hc := hu h0
    rw [Finset.card_empty] at hc
    omega
  exact exists_pairwiseDisjoint_of_isSatisfying hr hemp hsat

open Rao in
/-- **The note's generalized disjointness corollary**: Theorem 3's hypotheses at `(δ, ε)`
yield `⌊δ⁻¹⌋·(1 − ε)` pairwise disjoint members — any `r` up to that rate. The colouring uses
`q = ⌊δ⁻¹⌋` classes of density `1/q ≥ δ`, so the satisfying theorem is invoked at `1/q`
directly, where its condition on `R` is weaker than at `δ` — no monotonicity of the
`p`-biased measure in the density is needed. `δ = ε = 1/r` recovers the rate of
`rao_disjoint_original` (there via the union bound), and `δ = 1/(2r)`, `ε = 1/2` is
`exists_pairwiseDisjoint_of_raoSpread`. -/
theorem bcw_disjoint {w r : ℕ} {R δ ε : ℝ} {X : Finset α} {𝓕 : Finset (Finset α)}
    (hw : 1 ≤ w) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hrate : (r : ℝ) ≤ (⌊δ⁻¹⌋₊ : ℝ) * (1 - ε))
    (hR : 2 ^ 55 * δ⁻¹ * (Real.log ((w : ℝ) / ε) + 1) ≤ R) :
    ∃ 𝒟 ⊆ 𝓕, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := by
    nlinarith [mul_inv_cancel₀ (ne_of_gt hδ0), inv_pos.mpr hδ0, hδ1]
  have hq1 : 1 ≤ ⌊δ⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hδinv1)
  have hqR : (0 : ℝ) < ((⌊δ⁻¹⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq1
  have hqle : ((⌊δ⁻¹⌋₊ : ℕ) : ℝ) ≤ δ⁻¹ := Nat.floor_le (by positivity)
  have hw1R : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hwε1 : (1 : ℝ) ≤ (w : ℝ) / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hw1R, hε1]
  have hL1 : (0 : ℝ) ≤ Real.log ((w : ℝ) / ε) + 1 := by
    linarith [Real.log_nonneg hwε1]
  have hsat : IsSatisfying (1 / ((⌊δ⁻¹⌋₊ : ℕ) : ℝ)) ε X 𝓕 := by
    refine isSatisfying_of_raoSpread hw hu hsp hSX hcard
      (one_div_pos.mpr hqR) ?_ hε0 hε1 ?_
    · rw [div_le_one hqR]
      exact_mod_cast hq1
    · rw [one_div, inv_inv]
      nlinarith [hR, mul_nonneg (sub_nonneg.mpr hqle) hL1]
  have hemp : ∅ ∉ 𝓕 := fun h0 => by
    have hc := hu h0
    rw [Finset.card_empty] at hc
    omega
  exact exists_pairwiseDisjoint_of_many_colours hq1 hemp hsat hrate

end Sunflower

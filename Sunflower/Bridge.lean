/-
# The `p`-biased ↔ fixed-size bridge

`Sunflower.Janson` proves Janson's inequality in the **`p`-biased** model. The combinatorial
iteration (`SpreadCore`, `SpreadBottom`, `SpreadIterate`) lives in the **fixed-size** model:
"probability" is `#{m-subsets with the property} / C(n, m)`. Formalization note A2 records
that the development makes the transition explicit, replacing ALWZ's limiting argument
(their Corollary 2.9) with exact splitting.

The product-measure Harris/Janson argument used here does not transfer verbatim to the slice,
whose coordinates have negative rather than the positive dependence used by this proof. This
file supplies the required direction: a `p`-biased upper bound yields a fixed-size upper bound.

The argument is elementary and avoids concentration inequalities entirely:

* **Layering** (`pBiased_eq_sum_layers`): `Pr_p[P] = ∑_m C(n,m)·p^m(1-p)^{n-m}·f(m)` where
  `f(m)` is the fixed-size probability at size `m`.
* **Monotonicity** (`fixedCount_antitone_mul`): for a *decreasing* event `P`, `f` is
  non-increasing in `m`. Proved by the double count over pairs `V ⊆ U` with `|V| = m`,
  `|U| = m'`.
* Hence `f(m₀)·Pr[|R| ≤ m₀] ≤ Pr_p[P]` (`fixedCount_mul_lowerTail_le`), and it remains to
  keep `Pr[|R| ≤ m₀]` bounded below. **Markov suffices**: `E|R| = p·n` exactly
  (`expected_card`), so taking `p = m₀/(2n)` gives `Pr[|R| > m₀] ≤ 1/2`. No Chernoff bound,
  no concentration machinery.

Everything is stated multiplicatively, without division.
-/
import Sunflower.Robust

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## The fixed-size counts -/

/-- The number of `m`-element subsets of `X` satisfying `P`. The fixed-size "probability" is
`fixedCount X P m / C(|X|, m)`; we never form the quotient. -/
def fixedCount (X : Finset α) (P : Finset α → Prop) [DecidablePred P] (m : ℕ) : ℕ :=
  ((Finset.powersetCard m X).filter P).card

/-- **Layering.** The `p`-biased probability is the binomial average of the fixed-size ones. -/
lemma pBiased_eq_sum_layers (X : Finset α) (p : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    pBiased X p P
      = ∑ m ∈ Finset.range (X.card + 1),
          (fixedCount X P m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m)) := by
  rw [pBiased_eq_sum_wt, Finset.powerset_card_biUnion,
    Finset.sum_biUnion (X.pairwise_disjoint_powersetCard.set_pairwise _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  calc ∑ R ∈ Finset.powersetCard m X, wt X p R * (if P R then (1 : ℝ) else 0)
      = ∑ R ∈ Finset.powersetCard m X,
          (if P R then (1 : ℝ) else 0) * (p ^ m * (1 - p) ^ (X.card - m)) := by
        refine Finset.sum_congr rfl fun R hR => ?_
        obtain ⟨hRX, hRm⟩ := Finset.mem_powersetCard.mp hR
        rw [wt_of_subset hRX, hRm]
        ring
    _ = (∑ R ∈ Finset.powersetCard m X, (if P R then (1 : ℝ) else 0))
          * (p ^ m * (1 - p) ^ (X.card - m)) := by rw [Finset.sum_mul]
    _ = (fixedCount X P m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m)) := by
        rw [Finset.sum_boole, fixedCount]

/-! ## Monotonicity of the fixed-size probability for a decreasing event -/

/-- For a decreasing event, every `m`-subset of a good `m'`-set is good. The double count over
pairs `V ⊆ U`, `|V| = m`, `|U| = m'` gives that the fixed-size probability is non-increasing
in the size, in the division-free form
`f(m')·C(m',m) ≤ f(m)·C(n-m, m'-m)`. -/
lemma fixedCount_mono_mul {X : Finset α} {P : Finset α → Prop} [DecidablePred P]
    (hP : Decreasing P) {m m' : ℕ} (_hmm : m ≤ m') (_hm'n : m' ≤ X.card) :
    fixedCount X P m' * m'.choose m ≤ fixedCount X P m * (X.card - m).choose (m' - m) := by
  classical
  set Bad : ℕ → Finset (Finset α) := fun k => (Finset.powersetCard k X).filter P with hBad
  -- the pair set `{(U, V) : U good of size m', V ⊆ U of size m}`
  set L : Finset ((Finset α) × (Finset α)) :=
    (Bad m').biUnion fun U => (Finset.powersetCard m U).image fun V => (U, V) with hL
  have hcardL : L.card = fixedCount X P m' * m'.choose m := by
    rw [hL, Finset.card_biUnion]
    · have hterm : ∀ U ∈ Bad m',
          ((Finset.powersetCard m U).image fun V => (U, V)).card = m'.choose m := by
        intro U hU
        rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2),
          Finset.card_powersetCard]
        have : U.card = m' := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).2
        rw [this]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, fixedCount, hBad]
    · intro U hU V hV hne
      simp only [Finset.disjoint_left, Finset.mem_image]
      rintro z ⟨a, -, rfl⟩ ⟨b, -, hb⟩
      exact hne (congrArg Prod.fst hb).symm
  -- project onto the second coordinate
  have hsnd : ∀ z ∈ L, z.2 ∈ Bad m := by
    intro z hz
    rw [hL, Finset.mem_biUnion] at hz
    obtain ⟨U, hU, hzU⟩ := hz
    rw [Finset.mem_image] at hzU
    obtain ⟨V, hV, rfl⟩ := hzU
    rw [Finset.mem_powersetCard] at hV
    rw [hBad, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨hV.1.trans (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).1, hV.2⟩, ?_⟩
    exact hP hV.1 (Finset.mem_filter.mp hU).2
  -- each fibre injects into the `(m'-m)`-subsets of `X \ V`
  have hsubfst : ∀ z ∈ L, z.2 ⊆ z.1 := by
    intro z hz
    rw [hL, Finset.mem_biUnion] at hz
    obtain ⟨U, -, hzU⟩ := hz
    rw [Finset.mem_image] at hzU
    obtain ⟨W, hW, rfl⟩ := hzU
    exact (Finset.mem_powersetCard.mp hW).1
  have hfibre : ∀ V ∈ Bad m,
      (L.filter fun z => z.2 = V).card ≤ (X.card - m).choose (m' - m) := by
    intro V hV
    have hVdata : V ⊆ X ∧ V.card = m := by
      rw [hBad, Finset.mem_filter, Finset.mem_powersetCard] at hV
      exact hV.1
    refine le_trans (Finset.card_le_card_of_injOn (fun z => z.1 \ V)
      (t := Finset.powersetCard (m' - m) (X \ V)) ?_ ?_) ?_
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz
      obtain ⟨hzL, hzV⟩ := hz
      have hz1 : z.1 ⊆ X ∧ z.1.card = m' := by
        rw [hL, Finset.mem_biUnion] at hzL
        obtain ⟨U, hU, hzU⟩ := hzL
        rw [Finset.mem_image] at hzU
        obtain ⟨W, -, rfl⟩ := hzU
        exact Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1
      have hVz : V ⊆ z.1 := hzV ▸ hsubfst z hzL
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hz1.1 hx.1, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hVz, hz1.2, hVdata.2]
    · intro z hz z' hz' heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hz hz'
      obtain ⟨hzL, hzV⟩ := hz
      obtain ⟨hz'L, hz'V⟩ := hz'
      have hVz : V ⊆ z.1 := hzV ▸ hsubfst z hzL
      have hVz' : V ⊆ z'.1 := hz'V ▸ hsubfst z' hz'L
      have e1 : z.1 \ V ∪ V = z.1 := Finset.sdiff_union_of_subset hVz
      have e2 : z'.1 \ V ∪ V = z'.1 := Finset.sdiff_union_of_subset hVz'
      refine Prod.ext ?_ (hzV.trans hz'V.symm)
      rw [← e1, ← e2]
      exact congrArg (fun s => s ∪ V) heq
    · rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hVdata.1, hVdata.2]
  calc fixedCount X P m' * m'.choose m = L.card := hcardL.symm
    _ = ∑ V ∈ Bad m, (L.filter fun z => z.2 = V).card :=
        Finset.card_eq_sum_card_fiberwise hsnd
    _ ≤ ∑ _V ∈ Bad m, (X.card - m).choose (m' - m) :=
        Finset.sum_le_sum fun V hV => hfibre V hV
    _ = fixedCount X P m * (X.card - m).choose (m' - m) := by
        rw [Finset.sum_const, smul_eq_mul, fixedCount, hBad]

/-- The fixed-size probability is antitone in the size, in cross-multiplied form. -/
lemma fixedCount_antitone_mul {X : Finset α} {P : Finset α → Prop} [DecidablePred P]
    (hP : Decreasing P) {m m' : ℕ} (hmm : m ≤ m') (hm'n : m' ≤ X.card) :
    fixedCount X P m' * X.card.choose m ≤ fixedCount X P m * X.card.choose m' := by
  have hkey := fixedCount_mono_mul hP hmm hm'n
  have hchoose : X.card.choose m' * m'.choose m
      = X.card.choose m * (X.card - m).choose (m' - m) := Nat.choose_mul hmm
  have hpos : 0 < m'.choose m := Nat.choose_pos hmm
  have hmul : fixedCount X P m' * X.card.choose m * m'.choose m
      ≤ fixedCount X P m * X.card.choose m' * m'.choose m := by
    calc fixedCount X P m' * X.card.choose m * m'.choose m
        = (fixedCount X P m' * m'.choose m) * X.card.choose m := by ring
      _ ≤ (fixedCount X P m * (X.card - m).choose (m' - m)) * X.card.choose m :=
          Nat.mul_le_mul_right _ hkey
      _ = fixedCount X P m * (X.card.choose m * (X.card - m).choose (m' - m)) := by ring
      _ = fixedCount X P m * (X.card.choose m' * m'.choose m) := by rw [hchoose]
      _ = fixedCount X P m * X.card.choose m' * m'.choose m := by ring
  exact Nat.le_of_mul_le_mul_right hmul hpos

/-! ## Expected size and Markov -/

/-- `E|R| = p·|X|`, exactly. -/
lemma expected_card (X : Finset α) (p : ℝ) :
    ∑ R ∈ X.powerset, wt X p R * (R.card : ℝ) = p * X.card := by
  classical
  have h1 : ∀ R ∈ X.powerset, (R.card : ℝ) = ∑ i ∈ X, (if i ∈ R then (1 : ℝ) else 0) := by
    intro R hR
    rw [Finset.mem_powerset] at hR
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hR]
  calc ∑ R ∈ X.powerset, wt X p R * (R.card : ℝ)
      = ∑ R ∈ X.powerset, ∑ i ∈ X, wt X p R * (if i ∈ R then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun R hR => ?_
        rw [h1 R hR, Finset.mul_sum]
    _ = ∑ i ∈ X, ∑ R ∈ X.powerset, wt X p R * (if i ∈ R then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ _i ∈ X, p := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hm := pBiased_mem hi p
        rw [pBiased_eq_sum_wt] at hm
        exact hm
    _ = p * X.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Markov's inequality for the size**: `Pr[|R| > m₀] · m₀ ≤ p·|X|`. This is all the
concentration the bridge needs — no Chernoff bound. -/
lemma markov_card (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m₀ : ℕ) :
    pBiased X p (fun R => m₀ < R.card) * m₀ ≤ p * X.card := by
  rw [pBiased_eq_sum_wt, ← expected_card X p, Finset.sum_mul]
  refine Finset.sum_le_sum fun R _ => ?_
  by_cases h : m₀ < R.card
  · rw [if_pos h, mul_one]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h.le) (wt_nonneg hp0 hp1 R)
  · rw [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (wt_nonneg hp0 hp1 R) (Nat.cast_nonneg _)

/-! ## The bridge -/

omit [DecidableEq α] in
/-- The count of "small" sets in a layer: everything if `m ≤ m₀`, nothing otherwise. -/
lemma fixedCount_card_le (X : Finset α) (m₀ m : ℕ) :
    fixedCount X (fun R => R.card ≤ m₀) m = if m ≤ m₀ then X.card.choose m else 0 := by
  classical
  rw [fixedCount]
  by_cases h : m ≤ m₀
  · rw [if_pos h, Finset.filter_true_of_mem, Finset.card_powersetCard]
    exact fun R hR => (Finset.mem_powersetCard.mp hR).2 ▸ h
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun R hR => by rw [(Finset.mem_powersetCard.mp hR).2]; exact h

/-- **The bridge.** For a decreasing event `P`, the fixed-size probability at `m₀` is
controlled by the `p`-biased probability, up to the lower tail `Pr[|R| ≤ m₀]`:

`f(m₀) · Pr[|R| ≤ m₀] ≤ Pr_p[P]`,

stated multiplied out by `C(|X|, m₀)`. The proof is termwise across the layers: below `m₀`
the antitonicity of `f` applies, above `m₀` the left-hand layer vanishes. -/
theorem fixedCount_mul_lowerTail_le {X : Finset α} {P : Finset α → Prop} [DecidablePred P]
    (hP : Decreasing P) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m₀ : ℕ} (hm₀ : m₀ ≤ X.card) :
    (fixedCount X P m₀ : ℝ) * pBiased X p (fun R => R.card ≤ m₀)
      ≤ pBiased X p P * (X.card.choose m₀ : ℝ) := by
  classical
  rw [pBiased_eq_sum_layers X p P, pBiased_eq_sum_layers X p (fun R => R.card ≤ m₀),
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  have hwnn : (0 : ℝ) ≤ p ^ m * (1 - p) ^ (X.card - m) :=
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  rw [fixedCount_card_le]
  by_cases hmm : m ≤ m₀
  · rw [if_pos hmm]
    have hanti := fixedCount_antitone_mul hP hmm hm₀
    have hcast : (fixedCount X P m₀ : ℝ) * (X.card.choose m : ℝ)
        ≤ (fixedCount X P m : ℝ) * (X.card.choose m₀ : ℝ) := by exact_mod_cast hanti
    calc (fixedCount X P m₀ : ℝ) * ((X.card.choose m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m)))
        = ((fixedCount X P m₀ : ℝ) * (X.card.choose m : ℝ))
            * (p ^ m * (1 - p) ^ (X.card - m)) := by ring
      _ ≤ ((fixedCount X P m : ℝ) * (X.card.choose m₀ : ℝ))
            * (p ^ m * (1 - p) ^ (X.card - m)) := mul_le_mul_of_nonneg_right hcast hwnn
      _ = (fixedCount X P m : ℝ) * (p ^ m * (1 - p) ^ (X.card - m))
            * (X.card.choose m₀ : ℝ) := by ring
  · rw [if_neg hmm]
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    positivity

/-- **The bridge, with the tail discharged by Markov.** Choosing `p` with `2·p·|X| ≤ m₀`
makes `Pr[|R| ≤ m₀] ≥ 1/2`, so a `p`-biased bound costs only a factor `2`. -/
theorem fixedCount_le_two_mul_pBiased {X : Finset α} {P : Finset α → Prop} [DecidablePred P]
    (hP : Decreasing P) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hm₀n : m₀ ≤ X.card) (hsmall : 2 * (p * X.card) ≤ m₀) :
    (fixedCount X P m₀ : ℝ) ≤ 2 * (pBiased X p P * (X.card.choose m₀ : ℝ)) := by
  classical
  have hm₀R : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  -- Markov: the upper tail has mass at most `1/2`
  have hmk := markov_card X hp0 hp1 m₀
  have htail : pBiased X p (fun R => m₀ < R.card) ≤ 1 / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [hmk, hsmall, hm₀R]
  -- hence the lower tail has mass at least `1/2`
  have hcompl : pBiased X p (fun R => R.card ≤ m₀)
      + pBiased X p (fun R => m₀ < R.card) = 1 := by
    have h := pBiased_add_not X p (fun R => R.card ≤ m₀)
    rw [show pBiased X p (fun R => ¬ R.card ≤ m₀) = pBiased X p (fun R => m₀ < R.card) from
      pBiased_congr X p fun R => not_le] at h
    exact h
  have hlow : (1 : ℝ) / 2 ≤ pBiased X p (fun R => R.card ≤ m₀) := by linarith
  have hbridge := fixedCount_mul_lowerTail_le hP hp0 hp1 hm₀n
  have hfnn : (0 : ℝ) ≤ (fixedCount X P m₀ : ℝ) := Nat.cast_nonneg _
  nlinarith [hbridge, hlow, hfnn]

end Sunflower

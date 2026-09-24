/-
# Robust sunflowers (ALWZ §1.1)

The definitions the paper's Theorem 1.9 is stated in: satisfying set systems (their
Definition 1.5), robust sunflowers (their Definition 1.7), and the two lemmas that connect
them to ordinary sunflowers (their Lemmas 1.6 and 1.8).

**The `p`-biased distribution, without measure theory.** Definition 1.5 is a statement about
`R ∼ U(X, α)`, the distribution on subsets of `X` including each element independently with
probability `α`. Many of the combinatorial counts in this development stay in the
*fixed-size* model (see `docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md`, note A2), so the
`p`-biased model appears here for the first time — but it needs no probability theory either:
for a finite ground set the probability is literally the finite sum

  `pBiased X p P = ∑_{R ⊆ X} p^|R| (1-p)^{|X|-|R|} · [P R]`,

and the fact that it is a probability (`sum_pBiasedWeight`) is `(p + (1-p))^{|X|} = 1` read
through `Finset.prod_add`.

**Notation.** The paper's parameters `α, β` are written `a, b` here, since `α` is already the
ambient type variable.

**Status.** Definitions 1.5 and 1.7 and Lemmas 1.6 and 1.8 are proved, sorry-free. Theorem
1.9 is assembled in downstream modules; the note at the end records that route.
-/
import Sunflower.Spread
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## The `p`-biased distribution as a finite sum -/

/-- `pBiased X p P` — the probability that a `p`-biased random subset `R ⊆ X` (each element
included independently with probability `p`) satisfies `P`. A finite sum over `X.powerset`;
no measure theory is involved. -/
noncomputable def pBiased (X : Finset α) (p : ℝ) (P : Finset α → Prop) : ℝ :=
  open scoped Classical in
  ∑ R ∈ X.powerset, if P R then p ^ R.card * (1 - p) ^ (X.card - R.card) else 0

/-- The `p`-biased weights sum to `1`: this is `(p + (1 - p))^{|X|} = 1`, read through
`Finset.prod_add`. -/
lemma sum_pBiasedWeight (X : Finset α) (p : ℝ) :
    ∑ R ∈ X.powerset, p ^ R.card * (1 - p) ^ (X.card - R.card) = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) X
  simp only [Finset.prod_const] at h
  have hp : p + (1 - p) = (1 : ℝ) := by ring
  rw [hp, one_pow] at h
  refine Eq.trans (Finset.sum_congr rfl fun R hR => ?_) h.symm
  rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hR)]

/-- A `p`-biased probability and that of the negated predicate are complementary. -/
lemma pBiased_add_not (X : Finset α) (p : ℝ) (P : Finset α → Prop) :
    pBiased X p P + pBiased X p (fun R => ¬ P R) = 1 := by
  classical
  rw [pBiased, pBiased, ← Finset.sum_add_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun R _ => ?_) (sum_pBiasedWeight X p)
  by_cases h : P R <;> simp [h]

omit [DecidableEq α] in
/-- Each `p`-biased weight is nonnegative when `0 ≤ p ≤ 1`. -/
lemma pBiasedWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : Finset α) (n : ℕ) :
    0 ≤ p ^ R.card * (1 - p) ^ (n - R.card) :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma pBiased_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset α) (P : Finset α → Prop) :
    0 ≤ pBiased X p P := by
  classical
  refine Finset.sum_nonneg fun R _ => ?_
  by_cases h : P R
  · simpa [h] using pBiasedWeight_nonneg hp0 hp1 R X.card
  · simp [h]

omit [DecidableEq α] in
/-- Monotone in the predicate. -/
lemma pBiased_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset α) {P Q : Finset α → Prop}
    (h : ∀ R, P R → Q R) : pBiased X p P ≤ pBiased X p Q := by
  classical
  refine Finset.sum_le_sum fun R _ => ?_
  by_cases hP : P R
  · rw [if_pos hP, if_pos (h R hP)]
  · rw [if_neg hP]
    by_cases hQ : Q R
    · rw [if_pos hQ]; exact pBiasedWeight_nonneg hp0 hp1 R X.card
    · rw [if_neg hQ]

/-! ## The `p`-biased weight, and monotone events

Generic vocabulary shared by every consumer of `pBiased` — the fixed-size bridge, the Janson
chain, and the Rao route alike. `wt` extends the weight by zero off `X.powerset`, which is
what makes log-supermodularity hold on all of `Finset α` when `Janson` feeds it to the four
functions theorem; here it is just a convenient closed form for `pBiased` sums. -/

/-- The `p`-biased weight of `R`, extended by zero off `X.powerset`. -/
noncomputable def wt (X : Finset α) (p : ℝ) (R : Finset α) : ℝ :=
  if R ⊆ X then p ^ R.card * (1 - p) ^ (X.card - R.card) else 0

lemma wt_of_subset {X : Finset α} {p : ℝ} {R : Finset α} (h : R ⊆ X) :
    wt X p R = p ^ R.card * (1 - p) ^ (X.card - R.card) := if_pos h

lemma wt_nonneg {X : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : Finset α) :
    0 ≤ wt X p R := by
  rw [wt]
  split
  · exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  · exact le_rfl

/-- The weights sum to `1` over `X.powerset`. -/
lemma sum_wt (X : Finset α) (p : ℝ) : ∑ R ∈ X.powerset, wt X p R = 1 := by
  rw [← sum_pBiasedWeight X p]
  exact Finset.sum_congr rfl fun R hR => wt_of_subset (Finset.mem_powerset.mp hR)

/-- `P` is **increasing**: closed under supersets. -/
def Increasing (P : Finset α → Prop) : Prop := ∀ ⦃a b⦄, a ⊆ b → P a → P b

/-- `P` is **decreasing**: closed under subsets. -/
def Decreasing (P : Finset α → Prop) : Prop := ∀ ⦃a b⦄, a ⊆ b → P b → P a

lemma pBiased_eq_sum_wt (X : Finset α) (p : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    pBiased X p P = ∑ R ∈ X.powerset, wt X p R * (if P R then (1 : ℝ) else 0) := by
  rw [pBiased]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [wt_of_subset (Finset.mem_powerset.mp hR)]
  split <;> ring

/-! ## Definition 1.5: satisfying set systems -/

/-- **ALWZ Definition 1.5.** `𝓕` on the ground set `X` is `(a, b)`-*satisfying* if a
`p`-biased random subset with `p = a` contains a member of `𝓕` with probability more than
`1 - b`. (The paper writes `α, β` for `a, b`.)

Read as a DNF: the formula `⋁_{S ∈ 𝓕} ⋀_{x ∈ S} x` is satisfied with probability more than
`1 - b` on `a`-biased inputs. -/
def IsSatisfying (a b : ℝ) (X : Finset α) (𝓕 : Finset (Finset α)) : Prop :=
  1 - b < pBiased X a (fun R => ∃ S ∈ 𝓕, S ⊆ R)

omit [DecidableEq α] in
/-- Satisfying is monotone in the family. -/
lemma IsSatisfying.mono {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {X : Finset α}
    {𝓕 𝓖 : Finset (Finset α)} (h : IsSatisfying a b X 𝓕) (hsub : 𝓕 ⊆ 𝓖) :
    IsSatisfying a b X 𝓖 :=
  lt_of_lt_of_le h (pBiased_mono ha0 ha1 X fun _ ⟨S, hS, hSR⟩ => ⟨S, hsub hS, hSR⟩)

/-! ## The kernel of a family -/

/-- The **kernel** `⋂_{S ∈ 𝓕} S` of a family (`∅` for the empty family). -/
noncomputable def kernel (𝓕 : Finset (Finset α)) : Finset α :=
  if h : 𝓕.Nonempty then 𝓕.inf' h id else ∅

lemma kernel_subset {𝓕 : Finset (Finset α)} {S : Finset α} (hS : S ∈ 𝓕) : kernel 𝓕 ⊆ S := by
  rw [kernel, dif_pos ⟨S, hS⟩]
  exact Finset.inf'_le id hS

lemma subset_kernel {𝓕 : Finset (Finset α)} (h : 𝓕.Nonempty) {T : Finset α}
    (hT : ∀ S ∈ 𝓕, T ⊆ S) : T ⊆ kernel 𝓕 := by
  rw [kernel, dif_pos h]
  exact Finset.le_inf' h id hT

lemma mem_kernel {𝓕 : Finset (Finset α)} (h : 𝓕.Nonempty) {x : α} :
    x ∈ kernel 𝓕 ↔ ∀ S ∈ 𝓕, x ∈ S := by
  constructor
  · exact fun hx S hS => kernel_subset hS hx
  · intro hx
    exact subset_kernel h (fun S hS => Finset.singleton_subset_iff.mpr (hx S hS))
      (Finset.mem_singleton_self x)

/-! ## Definition 1.7: robust sunflowers -/

/-- **ALWZ Definition 1.7.** `𝓕` on the ground set `X` is an `(a, b)`-*robust sunflower* if
its kernel `K = ⋂_{S ∈ 𝓕} S` is not itself a member, and the link `𝓕_K` is `(a, b)`-satisfying
on `X \ K`.

The paper excludes `K ∈ 𝓕` "for technical reasons; we do not want a set system consisting of
a single set to be a robust sunflower". -/
def IsRobustSunflower (a b : ℝ) (X : Finset α) (𝓕 : Finset (Finset α)) : Prop :=
  kernel 𝓕 ∉ 𝓕 ∧ IsSatisfying a b (X \ kernel 𝓕) (link 𝓕 (kernel 𝓕))

/-- Every member of the link of a family at its kernel is nonempty — this is exactly what
`K ∉ 𝓕` buys, and it is the hypothesis `∅ ∉ 𝓕` of Lemma 1.6. -/
lemma empty_notMem_link_kernel {a b : ℝ} {X : Finset α} {𝓕 : Finset (Finset α)}
    (h : IsRobustSunflower a b X 𝓕) : ∅ ∉ link 𝓕 (kernel 𝓕) := by
  intro hmem
  rw [mem_link] at hmem
  obtain ⟨S, hS, hsub, hdiff⟩ := hmem
  exact h.1 (by rwa [show kernel 𝓕 = S from
    Finset.Subset.antisymm hsub (by
      intro x hx
      by_contra hxK
      exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxK⟩) (by rw [hdiff]; exact notMem_empty x))])

/-! ## Lemma 1.6: the disjointness step, via random colourings

The paper's proof: colour `X` uniformly at random with `r` colours; each colour class is
distributed as `U(X, 1/r)`, so each fails to contain a member with probability less than
`1/r`; by the union bound some colouring succeeds on all `r` classes at once, and members
inside distinct classes are disjoint.

All three steps are finitary here. Colourings are the finite type `↥X → Fin r`; the
distributional claim is the fibre count `card_colourClass_fiber`; and the union bound is a
sum of `r` cardinalities.
-/

/-- The `i`-th colour class of a colouring of `X` by `r` colours. -/
def colourClass {r : ℕ} (X : Finset α) (c : {x // x ∈ X} → Fin r) (i : Fin r) : Finset α :=
  (X.attach.filter fun x => c x = i).image Subtype.val

lemma mem_colourClass {r : ℕ} {X : Finset α} {c : {x // x ∈ X} → Fin r} {i : Fin r} {y : α} :
    y ∈ colourClass X c i ↔ ∃ h : y ∈ X, c ⟨y, h⟩ = i := by
  classical
  simp only [colourClass, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, by simpa using hx⟩
  · rintro ⟨h, hc⟩; exact ⟨⟨y, h⟩, hc, rfl⟩

lemma colourClass_subset {r : ℕ} {X : Finset α} {c : {x // x ∈ X} → Fin r} {i : Fin r} :
    colourClass X c i ⊆ X := fun _ hy => (mem_colourClass.mp hy).1

lemma colourClass_disjoint {r : ℕ} {X : Finset α} {c : {x // x ∈ X} → Fin r} {i j : Fin r}
    (hij : i ≠ j) : Disjoint (colourClass X c i) (colourClass X c j) := by
  rw [Finset.disjoint_left]
  intro y hi hj
  obtain ⟨h, hci⟩ := mem_colourClass.mp hi
  obtain ⟨h', hcj⟩ := mem_colourClass.mp hj
  exact hij (hci.symm.trans (by rw [show (⟨y, h⟩ : {x // x ∈ X}) = ⟨y, h'⟩ from rfl]; exact hcj))

/-- **The distributional step**: the colour class `i` equals a given `R ⊆ X` for exactly
`(r-1)^{|X|-|R|}` of the `r^{|X|}` colourings — i.e. it is distributed as `U(X, 1/r)`. -/
lemma card_colourClass_fiber {r : ℕ} (X : Finset α) (i : Fin r) {R : Finset α} (hR : R ⊆ X) :
    ((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
        (fun c => colourClass X c i = R)).card = (r - 1) ^ (X.card - R.card) := by
  classical
  have hset : (Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
      (fun c => colourClass X c i = R)
      = Fintype.piFinset (fun x : {x // x ∈ X} =>
          if (x : α) ∈ R then ({i} : Finset (Fin r)) else ({i} : Finset (Fin r))ᶜ) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hc x
      by_cases hx : (x : α) ∈ R
      · rw [if_pos hx, Finset.mem_singleton]
        have hmem : (x : α) ∈ colourClass X c i := by rw [hc]; exact hx
        obtain ⟨h', hc'⟩ := mem_colourClass.mp hmem
        simpa using hc'
      · rw [if_neg hx, Finset.mem_compl, Finset.mem_singleton]
        intro hcx
        exact hx (by rw [← hc]; exact mem_colourClass.mpr ⟨x.2, by simpa using hcx⟩)
    · intro hc
      ext y
      rw [mem_colourClass]
      constructor
      · rintro ⟨hy, hcy⟩
        by_contra hyR
        have hx := hc ⟨y, hy⟩
        rw [if_neg hyR, Finset.mem_compl, Finset.mem_singleton] at hx
        exact hx hcy
      · intro hyR
        refine ⟨hR hyR, ?_⟩
        have hx := hc ⟨y, hR hyR⟩
        rw [if_pos hyR, Finset.mem_singleton] at hx
        exact hx
  rw [hset, Fintype.card_piFinset]
  have hcard : ∀ x : {x // x ∈ X},
      (if (x : α) ∈ R then ({i} : Finset (Fin r)) else ({i} : Finset (Fin r))ᶜ).card
        = if (x : α) ∈ R then 1 else r - 1 := by
    intro x
    by_cases hx : (x : α) ∈ R
    · simp [hx]
    · simp [hx, Finset.card_compl]
  rw [Finset.prod_congr rfl fun x _ => hcard x]
  rw [Finset.prod_coe_sort (f := fun y : α => if y ∈ R then 1 else r - 1)]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset hR]

/-- **The distribution of a colour class is `U(X, 1/r)`**, in the form needed: the number of
colourings whose `i`-th class satisfies `P` is `r^{|X|}` times the `1/r`-biased probability
of `P`. -/
lemma card_colourings_eq_pBiased {r : ℕ} (hr : 0 < r) (X : Finset α) (i : Fin r)
    (P : Finset α → Prop) [DecidablePred P] :
    (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
        (fun c => P (colourClass X c i))).card : ℝ)
      = (r : ℝ) ^ X.card * pBiased X (1 / r) P := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun c : {x // x ∈ X} → Fin r => colourClass X c i)
    (s := (Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter fun c => P (colourClass X c i))
    (t := X.powerset) (fun c _ => Finset.mem_powerset.mpr colourClass_subset)
  rw [hfib]
  push_cast
  rw [pBiased, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hRX : R ⊆ X := Finset.mem_powerset.mp hR
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  by_cases hP : P R
  · rw [if_pos hP]
    have hfilter : (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
        fun c => P (colourClass X c i)).filter fun c => colourClass X c i = R)
        = (Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
            fun c => colourClass X c i = R := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      exact fun hc => by rw [hc]; exact hP
    rw [hfilter, card_colourClass_fiber X i hRX]
    -- `(r-1)^{n-k} = r^n · (1/r)^k · (1 - 1/r)^{n-k}`, using `k + (n-k) = n`
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
    have hk : R.card ≤ X.card := Finset.card_le_card hRX
    have hsplit : R.card + (X.card - R.card) = X.card := by omega
    have hcast : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ r := hr
      push_cast [h1]
      ring
    have hone : (1 : ℝ) - 1 / r = ((r : ℝ) - 1) / r := by field_simp
    have hrn : ((r : ℝ) ^ X.card) = (r : ℝ) ^ R.card * (r : ℝ) ^ (X.card - R.card) := by
      rw [← pow_add, hsplit]
    rw [Nat.cast_pow, hcast, hone, div_pow, div_pow, one_pow, hrn]
    field_simp
  · rw [if_neg hP]
    have hempty : (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
        fun c => P (colourClass X c i)).filter fun c => colourClass X c i = R) = ∅ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      exact fun hc hcR => hP (hcR ▸ hc)
    rw [hempty]
    simp

/-- The complementary form of `IsSatisfying`: the failure probability is less than `b`. -/
lemma pBiased_not_lt {X : Finset α} {p b : ℝ} {𝓕 : Finset (Finset α)}
    (h : IsSatisfying p b X 𝓕) :
    pBiased X p (fun R => ¬ ∃ S ∈ 𝓕, S ⊆ R) < b := by
  have hsum : pBiased X p (fun R => ∃ S ∈ 𝓕, S ⊆ R)
      + pBiased X p (fun R => ¬ ∃ S ∈ 𝓕, S ⊆ R) = 1 := pBiased_add_not X p _
  have h' : 1 - b < pBiased X p (fun R => ∃ S ∈ 𝓕, S ⊆ R) := h
  linarith

/-- **ALWZ Lemma 1.6.** A `(1/r, 1/r)`-satisfying set system not containing `∅` contains `r`
pairwise disjoint sets.

The paper's proof, finitarily: colour `X` uniformly with `r` colours
(`card_colourings_eq_pBiased` is the statement that each class is distributed as `U(X,1/r)`),
union-bound the `r` failure events, and take members inside distinct classes. -/
theorem exists_pairwiseDisjoint_of_isSatisfying {r : ℕ} (hr : 0 < r) {X : Finset α}
    {𝓕 : Finset (Finset α)} (hemp : ∅ ∉ 𝓕)
    (h : IsSatisfying (1 / r) (1 / r) X 𝓕) :
    ∃ 𝒟 ⊆ 𝓕, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hfail : ∀ i : Fin r,
      (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
        (fun c => ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ) < (r : ℝ) ^ X.card / r := by
    intro i
    have hkey : (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
        (fun c => ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i)).card : ℝ)
        = (r : ℝ) ^ X.card * pBiased X (1 / r) (fun R => ¬ ∃ S ∈ 𝓕, S ⊆ R) :=
      card_colourings_eq_pBiased hr X i (fun R => ¬ ∃ S ∈ 𝓕, S ⊆ R)
    have hpow : (0 : ℝ) < (r : ℝ) ^ X.card := by positivity
    rw [hkey]
    calc (r : ℝ) ^ X.card * pBiased X (1 / r) (fun R => ¬ ∃ S ∈ 𝓕, S ⊆ R)
        < (r : ℝ) ^ X.card * (1 / r) := mul_lt_mul_of_pos_left (pBiased_not_lt h) hpow
      _ = (r : ℝ) ^ X.card / r := by ring
  -- union bound: some colouring succeeds on every colour at once
  have hexists : ∃ c : {x // x ∈ X} → Fin r, ∀ i, ∃ S ∈ 𝓕, S ⊆ colourClass X c i := by
    by_contra hcon
    have hcon' : ∀ c : {x // x ∈ X} → Fin r,
        ∃ i, ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i := by
      intro c
      by_contra hc2
      exact hcon ⟨c, fun i => not_not.mp fun hni => hc2 ⟨i, hni⟩⟩
    have hcover : (Finset.univ : Finset ({x // x ∈ X} → Fin r)) ⊆
        (Finset.univ : Finset (Fin r)).biUnion fun i =>
          (Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
            fun c => ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i := by
      intro c _
      obtain ⟨i, hi⟩ := hcon' c
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hi⟩⟩
    have hnat : (Finset.univ : Finset ({x // x ∈ X} → Fin r)).card
        ≤ ∑ i : Fin r, ((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
            fun c => ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    have hreal : ((Finset.univ : Finset ({x // x ∈ X} → Fin r)).card : ℝ)
        ≤ ∑ i : Fin r, (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
            fun c => ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i).card : ℝ) := by
      exact_mod_cast hnat
    have hlt : ∑ i : Fin r, (((Finset.univ : Finset ({x // x ∈ X} → Fin r)).filter
            fun c => ¬ ∃ S ∈ 𝓕, S ⊆ colourClass X c i).card : ℝ)
        < ∑ _i : Fin r, (r : ℝ) ^ X.card / r :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, hr⟩, Finset.mem_univ _⟩ fun i _ => hfail i
    have hval : ∑ _i : Fin r, (r : ℝ) ^ X.card / r = (r : ℝ) ^ X.card := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hcardu : ((Finset.univ : Finset ({x // x ∈ X} → Fin r)).card : ℝ)
        = (r : ℝ) ^ X.card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
      push_cast
      ring
    linarith
  obtain ⟨c, hc⟩ := hexists
  choose S hS hSsub using hc
  have hSne : ∀ i, S i ≠ ∅ := fun i hi => hemp (hi ▸ hS i)
  have hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j) := fun i j hij =>
    (colourClass_disjoint hij).mono (hSsub i) (hSsub j)
  have hinj : Function.Injective S := by
    intro i j hij
    by_contra hne
    have hd : Disjoint (S i) (S j) := hdisj i j hne
    rw [hij] at hd
    refine hSne j (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
    exact Finset.disjoint_left.mp hd hx hx
  refine ⟨Finset.univ.image S, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hT
    exact hS i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro T hT U hU hTU
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hU)
    exact hdisj i j fun hij => hTU (by rw [hij])

/-- **ALWZ Lemma 1.8.** Any `(1/r, 1/r)`-robust sunflower contains an `r`-sunflower.

The kernel `K` supplies the core; `K ∉ 𝓕` gives `∅ ∉ 𝓕_K` (`empty_notMem_link_kernel`), so
Lemma 1.6 yields `r` pairwise disjoint petals in the link, and
`hasSunflower_of_pairwiseDisjoint_link` reattaches `K`. -/
theorem hasSunflower_of_isRobustSunflower {r : ℕ} (hr : 0 < r) {X : Finset α}
    {𝓕 : Finset (Finset α)} (h : IsRobustSunflower (1 / r) (1 / r) X 𝓕) :
    HasSunflower r 𝓕 := by
  obtain ⟨𝒟, h𝒟sub, h𝒟card, h𝒟pd⟩ :=
    exists_pairwiseDisjoint_of_isSatisfying hr (empty_notMem_link_kernel h) h.2
  exact hasSunflower_of_pairwiseDisjoint_link h𝒟sub h𝒟card h𝒟pd

/-! ## Splitting the `p`-biased measure across disjoint coordinates

The bijection `R ↦ (R ∩ Y, R \ Y)` factorises the weight, giving the exact marginals the
fixed-size bridge needs (`pBiased_superset`, `pBiased_mem`, `pBiased_mem_pair`). The
full independence statement `pBiased_and_of_indep`, and everything Harris/FKG, stay in
`Sunflower.Janson`. -/

omit [DecidableEq α] in
/-- `pBiased` respects pointwise equivalence of events. -/
lemma pBiased_congr (X : Finset α) (p : ℝ) {P Q : Finset α → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ R, P R ↔ Q R) :
    pBiased X p P = pBiased X p Q := by
  rw [pBiased, pBiased]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases hP : P R
  · rw [if_pos hP, if_pos ((h R).mp hP)]
  · rw [if_neg hP, if_neg fun hc => hP ((h R).mpr hc)]

/-- Splitting a subset of `X` along `Y ⊆ X`: `R ↦ (R ∩ Y, R \ Y)` is a bijection from
`X.powerset` onto `Y.powerset ×ˢ (X \ Y).powerset`, with inverse `(A, B) ↦ A ∪ B`. -/
lemma sum_powerset_split {X Y : Finset α} (hY : Y ⊆ X) (F : Finset α → Finset α → ℝ) :
    ∑ R ∈ X.powerset, F (R ∩ Y) (R \ Y)
      = ∑ A ∈ Y.powerset, ∑ B ∈ (X \ Y).powerset, F A B := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun R => (R ∩ Y, R \ Y)) (fun q => q.1 ∪ q.2) ?_ ?_ ?_ ?_ ?_
  · intro R hR
    rw [Finset.mem_powerset] at hR
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    refine ⟨Finset.inter_subset_right, fun x hx => ?_⟩
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hR hx.1, hx.2⟩
  · rintro ⟨A, B⟩ hq
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hq
    rw [Finset.mem_powerset]
    exact Finset.union_subset (hq.1.trans hY) fun x hx => (Finset.mem_sdiff.mp (hq.2 hx)).1
  · intro R _
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  · rintro ⟨A, B⟩ hq
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hq
    obtain ⟨hA, hB⟩ := hq
    have hBY : ∀ x ∈ B, x ∉ Y := fun x hx => (Finset.mem_sdiff.mp (hB hx)).2
    simp only [Prod.mk.injEq]
    constructor
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hx, hxY⟩ => hx.elim id fun hxB => absurd hxY (hBY x hxB),
        fun hx => ⟨Or.inl hx, hA hx⟩⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun ⟨hx, hxY⟩ => hx.elim (fun hxA => absurd (hA hxA) hxY) id,
        fun hx => ⟨Or.inr hx, hBY x hx⟩⟩
  · intro R _
    rfl

/-- The `p`-biased weight factorises along `Y ⊆ X`. -/
lemma wt_split {X Y : Finset α} (hY : Y ⊆ X) {p : ℝ} {R : Finset α} (hR : R ⊆ X) :
    wt X p R = wt Y p (R ∩ Y) * wt (X \ Y) p (R \ Y) := by
  have h1 : R ∩ Y ⊆ Y := Finset.inter_subset_right
  have h2 : R \ Y ⊆ X \ Y := fun x hx => by
    rw [Finset.mem_sdiff] at hx ⊢; exact ⟨hR hx.1, hx.2⟩
  rw [wt_of_subset hR, wt_of_subset h1, wt_of_subset h2]
  have hcR : (R \ Y).card + (R ∩ Y).card = R.card := Finset.card_sdiff_add_card_inter R Y
  have hcX : (X \ Y).card + Y.card = X.card := Finset.card_sdiff_add_card_eq_card hY
  have hb1 : (R ∩ Y).card ≤ Y.card := Finset.card_le_card h1
  have hb2 : (R \ Y).card ≤ (X \ Y).card := Finset.card_le_card h2
  have e1 : R.card = (R ∩ Y).card + (R \ Y).card := by omega
  have e2 : X.card - R.card
      = (Y.card - (R ∩ Y).card) + ((X \ Y).card - (R \ Y).card) := by omega
  rw [e2, e1, pow_add, pow_add]
  ring

/-- The probability that a fixed `Y ⊆ X` is contained in a `p`-biased random set is `p^|Y|`.
Proved by the splitting bijection: the `Y`-marginal forces `R ∩ Y = Y`, and the `X \ Y`
marginal sums to `1`. -/
lemma pBiased_superset {X Y : Finset α} (hY : Y ⊆ X) (p : ℝ) :
    pBiased X p (fun R => Y ⊆ R) = p ^ Y.card := by
  classical
  rw [pBiased_eq_sum_wt]
  have hiff : ∀ R : Finset α, Y ⊆ R ↔ R ∩ Y = Y := by
    intro R
    exact ⟨fun h => Finset.Subset.antisymm Finset.inter_subset_right
        (Finset.subset_inter h Finset.Subset.rfl),
      fun h x hx => by rw [← h] at hx; exact (Finset.mem_inter.mp hx).1⟩
  have h1 : ∑ R ∈ X.powerset, wt X p R * (if Y ⊆ R then (1 : ℝ) else 0)
      = ∑ R ∈ X.powerset, (wt Y p (R ∩ Y) * (if R ∩ Y = Y then (1 : ℝ) else 0))
          * wt (X \ Y) p (R \ Y) := by
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [wt_split hY (Finset.mem_powerset.mp hR)]
    by_cases h : Y ⊆ R
    · rw [if_pos h, if_pos ((hiff R).mp h)]; ring
    · rw [if_neg h, if_neg fun hc => h ((hiff R).mpr hc)]; ring
  rw [h1, sum_powerset_split hY fun A B =>
    (wt Y p A * (if A = Y then (1 : ℝ) else 0)) * wt (X \ Y) p B]
  have h2 : ∀ A : Finset α,
      (∑ B ∈ (X \ Y).powerset, (wt Y p A * (if A = Y then (1 : ℝ) else 0)) * wt (X \ Y) p B)
        = wt Y p A * (if A = Y then (1 : ℝ) else 0) := by
    intro A; rw [← Finset.mul_sum, sum_wt, mul_one]
  rw [Finset.sum_congr rfl fun A _ => h2 A]
  rw [Finset.sum_eq_single Y]
  · rw [if_pos rfl, mul_one, wt_of_subset (Finset.Subset.refl Y)]
    simp
  · intro A _ hA; rw [if_neg hA, mul_zero]
  · intro h; exact absurd (Finset.mem_powerset.mpr Finset.Subset.rfl) h

/-- Membership of a single element: `Pr[i ∈ T] = q`. -/
lemma pBiased_mem {ι : Type*} [DecidableEq ι] {V : Finset ι} {i : ι} (hi : i ∈ V) (q : ℝ) :
    pBiased V q (fun T => i ∈ T) = q := by
  have h := pBiased_superset (Finset.singleton_subset_iff.mpr hi) q
  rw [Finset.card_singleton, pow_one] at h
  exact Eq.trans (pBiased_congr V q (P := fun T => i ∈ T)
    (Q := fun T => ({i} : Finset ι) ⊆ T) fun T => Finset.singleton_subset_iff.symm) h

/-- Membership of two distinct elements: `Pr[i ∈ T ∧ j ∈ T] = q²`. -/
lemma pBiased_mem_pair {ι : Type*} [DecidableEq ι] {V : Finset ι} {i j : ι}
    (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j) (q : ℝ) :
    pBiased V q (fun T => i ∈ T ∧ j ∈ T) = q ^ 2 := by
  have hsub : ({i, j} : Finset ι) ⊆ V := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hi
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hj
  have h := pBiased_superset hsub q
  rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton] at h
  exact Eq.trans (pBiased_congr V q (P := fun T => i ∈ T ∧ j ∈ T)
    (Q := fun T => ({i, j} : Finset ι) ⊆ T) fun T => by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]) h

/-! ## The spread/link dichotomy: assembling Theorem 1.9's structure

Both routes to Theorem 1.9 — the ALWZ iteration and the Rao coding argument — end the same
way: a core `Z` with a spread, satisfying link is packaged as a robust sunflower. The two
lemmas live here, at the level of their content, so that neither route has to import the
other's machinery to use them. -/

/-- **A spread family has empty kernel.** If `κ > 1` and `𝓖` is nonempty and `κ`-spread, no
element lies in every member: a common element `x` would make the link at `{x}` as large as
`𝓖` itself, and spreadness at `{x}` then forces `κ ≤ 1`.

This is what makes the kernel of the subfamily above a spread core equal that core exactly —
the fact Theorem 1.9's assembly turns on. -/
lemma kernel_eq_empty_of_isSpread {κ : ℝ} (hκ : 1 < κ) {𝓖 : Finset (Finset α)}
    (hne : 𝓖.Nonempty) (hsp : IsSpread κ 𝓖) : kernel 𝓖 = ∅ := by
  classical
  by_contra hK
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hK
  -- every member contains `x`, so the link at `{x}` has the same size as `𝓖`
  have hall : ∀ S ∈ 𝓖, x ∈ S := (mem_kernel hne).mp hx
  have hfilter : 𝓖.filter (fun S => ({x} : Finset α) ⊆ S) = 𝓖 := by
    refine Finset.filter_true_of_mem fun S hS => ?_
    rw [Finset.singleton_subset_iff]
    exact hall S hS
  have hcard : (link 𝓖 ({x} : Finset α)).card = 𝓖.card := by
    rw [card_link, hfilter]
  have hspx := hsp ({x} : Finset α)
  rw [hcard, Finset.card_singleton, pow_one] at hspx
  have hpos : (0 : ℝ) < (𝓖.card : ℝ) := by
    have : 0 < 𝓖.card := Finset.card_pos.mpr hne
    exact_mod_cast this
  nlinarith [hspx, hpos, hκ]

/-- **The robust sunflower sitting above a spread core.** If `Z` is not itself a member, the
subfamily `{S ∈ 𝓕 : Z ⊆ S}` has kernel exactly `Z` (by `kernel_eq_empty_of_isSpread` applied
to the link), so it is an `(a,b)`-robust sunflower as soon as its link `𝓕_Z` is
`(a,b)`-satisfying on `X \ Z`.

This is Theorem 1.9's closing structure on both routes: `exists_spread_link` (or, on the Rao
route, `exists_rao_spread_link`) produces such a `Z`, the iteration (or the coding argument)
makes `𝓕_Z` satisfying, and this lemma packages the result as a robust sunflower inside
`𝓕`. -/
theorem isRobustSunflower_above_spread_core {a b κ : ℝ} {X : Finset α} {Z : Finset α}
    {𝓕 : Finset (Finset α)} (hκ : 1 < κ)
    (hZ : Z ∉ 𝓕) (hne : (link 𝓕 Z).Nonempty) (hsp : IsSpread κ (link 𝓕 Z))
    (hsat : IsSatisfying a b (X \ Z) (link 𝓕 Z)) :
    IsRobustSunflower a b X (𝓕.filter fun S => Z ⊆ S) := by
  classical
  set 𝒢 : Finset (Finset α) := 𝓕.filter fun S => Z ⊆ S with h𝒢
  have hmem : ∀ S, S ∈ 𝒢 ↔ S ∈ 𝓕 ∧ Z ⊆ S := by
    intro S; rw [h𝒢, Finset.mem_filter]
  have h𝒢ne : 𝒢.Nonempty := by
    obtain ⟨P, hP⟩ := hne
    rw [mem_link] at hP
    obtain ⟨S, hS, hZS, -⟩ := hP
    exact ⟨S, (hmem S).mpr ⟨hS, hZS⟩⟩
  -- the link of `𝒢` at `Z` is the link of `𝓕` at `Z`
  have hlink : link 𝒢 Z = link 𝓕 Z := by
    ext P
    rw [mem_link, mem_link]
    constructor
    · rintro ⟨S, hS, hZS, hPS⟩
      exact ⟨S, ((hmem S).mp hS).1, hZS, hPS⟩
    · rintro ⟨S, hS, hZS, hPS⟩
      exact ⟨S, (hmem S).mpr ⟨hS, hZS⟩, hZS, hPS⟩
  -- the kernel of `𝒢` is exactly `Z`
  have hkernel : kernel 𝒢 = Z := by
    refine Finset.Subset.antisymm ?_ (subset_kernel h𝒢ne fun S hS => ((hmem S).mp hS).2)
    intro x hx
    by_contra hxZ
    -- `x` would lie in every member of the link, contradicting spreadness
    have hempty : kernel (link 𝓕 Z) = ∅ := kernel_eq_empty_of_isSpread hκ hne hsp
    have hxlink : x ∈ kernel (link 𝓕 Z) := by
      rw [mem_kernel hne]
      intro P hP
      rw [← hlink, mem_link] at hP
      obtain ⟨S, hS, hZS, rfl⟩ := hP
      rw [Finset.mem_sdiff]
      exact ⟨(mem_kernel h𝒢ne).mp hx S hS, hxZ⟩
    rw [hempty] at hxlink
    exact absurd hxlink (Finset.notMem_empty x)
  refine ⟨?_, ?_⟩
  · rw [hkernel]
    intro hZ𝒢
    exact hZ ((hmem Z).mp hZ𝒢).1
  · rw [hkernel, hlink]
    exact hsat

/-!
## Theorem 1.9 — proved

**Theorem 1.9** (ALWZ): for `0 < a, b ≤ 1`, every `w`-uniform set system of size at least
`κ(w,a,b)^w` contains an `(a,b)`-robust sunflower.

This is now `Sunflower.exists_isRobustSunflower_pad` (`KappaZeroPad.lean`), with the explicit
constant

  `κ₀ = (2^20/a)·(lg(1/a) + lg(16/b) + lg lg w + 40)·(lg w + lg(16/b))`,

which for fixed admissible `a, b` has `O(log w·log log w)` dependence on `w`. An earlier and
weaker constant, `κ₀ = (2^20/a)·(lg(16/b) + lg w + lg(1/a) + 20)³`, is kept as
`Sunflower.exists_isRobustSunflower` (`KappaZero.lean`); for fixed `a,b` that displayed
constant is `Θ((log w)³)`. The two constructions differ at the bottom estimate.

The route, in the order the files were built:

* the definitions and the two easy lemmas are above (Definitions 1.5, 1.7; Lemmas 1.6, 1.8);
* `Janson` proves Janson's inequality from mathlib's four functions theorem, and `JansonMass`
  turns it into ALWZ's Lemma 2.10 by indexing the events by *copies* of the members — which is
  what makes the mass-spread hypothesis the right one (`failCount_le_janson_mass_budget`);
* `BridgeBack` supplies the `p`-biased ⇐ fixed-size direction, whose only real content is a
  lower tail for `|R|` (`mgf_card` plus Chernoff); `Satisfying` connects it to Definition 1.5
  and re-runs the assembly at free `(a,b)` (Theorem 2.5, schedule form) and derives Theorem 1.9
  from it (the paper's Lemma 2.4);
* `Schedule` picks the schedule and `KappaZero` verifies its conditions at the cubic `κ₀`;
* `DummyPad` and `PadBottom` then supply ALWZ's dummy-element padding (formalization note A3),
  weakening the relevant bottom condition from quadratic to linear in the width parameter `L`;
  `SchedulePad`/`KappaZeroPad` re-run the chase and give the constant above.

The Janson route supplies the source-shaped logarithmic bottom dependence, while the padding
supplies the fixed-`a,b` `O(log w·log log w)` dependence stated above. No claim is made here
that this prose asymptotic comparison captures the full joint dependence on `a,b,w`.
-/

end Sunflower

/-
# Rao's case 2: the double count

Case 2 applies when some `A ⊆ χ(S,U)` of size `|χ(S,W)|` has `|τ(A,·,a)| > φ`. The encoder
then writes `S` and `A` outright and spends its bits locating `V` among the *exceptional*
sets — those for which the class is oversized. For that to be cheap there must be few of them,
which is Rao's estimate

  `#{V : |τ(A,V,a)| > φ} ≤ C(n−u,v)·(6/ρ)^{|χ(S,U)|}`.

He proves it with a random experiment over `(B,V)`. The plan asks for the double count
instead, and that is what this file does — no probability notation, everything a cardinality.

The count runs: sum the class sizes over all `V`; swap the order to sum over *members* `T`
and count the `V`s that put `T` in the class; note that `T ∈ τ(A, V ∪ χ(S,U), a)` says exactly
that `V` swallows `χ(T,U) \ χ(S,U)`, so `card_filter_superset` counts those `V`s exactly;
then group the members by `B = χ(T,U) ∩ χ(S,U)` and bound each group by spreadness.

This file does the first three steps, which are exact; the grouping and the geometric sum
follow.
-/
import Sunflower.RaoCase1
import Sunflower.RaoSpread

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)} {X U S A T : Finset α} {v a : ℕ}

/-! ## Swapping the order of summation -/

/-- `τ` is a subfamily of `𝓕`, so its size is a count over `𝓕`. -/
lemma card_tau_eq_filter (D : Finset α) :
    (tau 𝓕 U A D a).card = (𝓕.filter fun T => T ∈ tau 𝓕 U A D a).card := by
  congr 1
  ext T
  simp only [Finset.mem_filter, mem_tau]
  tauto

/-- **The swap**: summing the class sizes over `V` is the same as summing, over members, the
number of `V`s that put the member in the class. -/
theorem sum_card_tau_eq (𝓕 : Finset (Finset α)) (X U S A : Finset α) (v a : ℕ) :
    ∑ V ∈ (X \ U).powersetCard v, (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card
      = ∑ T ∈ 𝓕, (((X \ U).powersetCard v).filter
          fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card := by
  classical
  have hL : ∀ V ∈ (X \ U).powersetCard v,
      (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card
        = ∑ T ∈ 𝓕, if T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a then 1 else 0 := by
    intro V _
    rw [card_tau_eq_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hR : ∀ T ∈ 𝓕,
      (((X \ U).powersetCard v).filter fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card
        = ∑ V ∈ (X \ U).powersetCard v,
            if T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a then 1 else 0 := by
    intro T _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  exact Finset.sum_comm

/-! ## The `V`s that put a member in the class

Given `A ⊆ χ(T,U)` and `|χ(T,U)| = a` — the two conditions on `T` that do not mention `V` —
membership in `τ(A, V ∪ χ(S,U), a)` says exactly that `V ⊇ χ(T,U) \ χ(S,U)`. -/

theorem filter_tau_eq (hT : T ∈ 𝓕) (hA : A ⊆ chi 𝓕 T U) (hcard : (chi 𝓕 T U).card = a) :
    ((X \ U).powersetCard v).filter (fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a)
      = ((X \ U).powersetCard v).filter (fun V => chi 𝓕 T U \ chi 𝓕 S U ⊆ V) := by
  classical
  refine Finset.filter_congr fun V _ => ?_
  simp only [mem_tau]
  constructor
  · rintro ⟨-, -, hsub, -⟩
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp (hsub hx.1) with h | h
    · exact h
    · exact absurd h hx.2
  · intro hsub
    refine ⟨hT, hA, fun x hx => ?_, hcard⟩
    by_cases hxS : x ∈ chi 𝓕 S U
    · exact Finset.mem_union_right _ hxS
    · exact Finset.mem_union_left _ (hsub (Finset.mem_sdiff.mpr ⟨hx, hxS⟩))

/-- Hence that number of `V`s is exactly a binomial coefficient. -/
theorem card_filter_tau (hT : T ∈ 𝓕) (hA : A ⊆ chi 𝓕 T U) (hcard : (chi 𝓕 T U).card = a)
    (hTX : T ⊆ X) (hv : (chi 𝓕 T U \ chi 𝓕 S U).card ≤ v) :
    (((X \ U).powersetCard v).filter fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card
      = ((X \ U).card - (chi 𝓕 T U \ chi 𝓕 S U).card).choose
          (v - (chi 𝓕 T U \ chi 𝓕 S U).card) := by
  classical
  rw [filter_tau_eq hT hA hcard]
  have hsub : chi 𝓕 T U \ chi 𝓕 S U ⊆ X \ U :=
    le_trans Finset.sdiff_subset (chi_subset_sdiff hT hTX)
  have := card_filter_superset (X := X \ U) (Y := chi 𝓕 T U \ chi 𝓕 S U) hsub (v := v) hv
  -- `powersetCard` is the `powerset` filtered by size; rewrite the counting lemma into it
  simpa [Finset.powersetCard_eq_filter, Finset.filter_filter, and_comm] using this

/-- **The per-member bound**, division-free: the number of `V`s that put `T` in the class,
times `(n−u−t)^t`, is at most `C(n−u,v)·v^t`, where `t = |χ(T,U) \ χ(S,U)|`. -/
theorem card_filter_tau_le (hT : T ∈ 𝓕) (hA : A ⊆ chi 𝓕 T U) (hcard : (chi 𝓕 T U).card = a)
    (hTX : T ⊆ X) (hv : (chi 𝓕 T U \ chi 𝓕 S U).card ≤ v) (hvX : v ≤ (X \ U).card) :
    (((((X \ U).powersetCard v).filter
        fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℕ) : ℝ)
        * (((X \ U).card - (chi 𝓕 T U \ chi 𝓕 S U).card : ℕ) : ℝ)
            ^ (chi 𝓕 T U \ chi 𝓕 S U).card
      ≤ (((X \ U).card.choose v : ℕ) : ℝ) * (v : ℝ) ^ (chi 𝓕 T U \ chi 𝓕 S U).card := by
  classical
  have hsub : chi 𝓕 T U \ chi 𝓕 S U ⊆ X \ U :=
    le_trans Finset.sdiff_subset (chi_subset_sdiff hT hTX)
  have hcount := card_filter_tau hT hA hcard hTX hv
  rw [hcount]
  have := card_filter_superset_le (X := X \ U) (Y := chi 𝓕 T U \ chi 𝓕 S U) hsub hv hvX
  rwa [card_filter_superset hsub hv] at this

/-! ## Grouping the members by their trace, and where spreadness enters

Rao groups the members `y` by `B = χ(y,U) ∩ χ(X,U)`: "the sequence of sets is `r`-spread, so
there are at most `r^{k−|B|}` sets of the form `χ(y,U)` … that intersect `χ(X,U)` in `B`".
That is the only use of the spread hypothesis in case 2. -/

/-- The members whose residual meets `χ(S,U)` in exactly `B` (and which could belong to the
class at all). -/
noncomputable def traceFiber (𝓕 : Finset (Finset α)) (U S A B : Finset α) (a : ℕ) :
    Finset (Finset α) :=
  𝓕.filter fun T => A ⊆ chi 𝓕 T U ∧ (chi 𝓕 T U).card = a ∧ chi 𝓕 T U ∩ chi 𝓕 S U = B

lemma mem_traceFiber {B : Finset α} :
    T ∈ traceFiber 𝓕 U S A B a ↔
      T ∈ 𝓕 ∧ A ⊆ chi 𝓕 T U ∧ (chi 𝓕 T U).card = a ∧ chi 𝓕 T U ∩ chi 𝓕 S U = B := by
  rw [traceFiber, Finset.mem_filter]

/-- **Spreadness bounds a fiber.** Every member of the fiber contains `B` — through its own
residual — so the fiber sits inside the link at `B`. -/
theorem card_traceFiber_le {R : ℝ} {w : ℕ} {B : Finset α} (hsp : IsRaoSpread R w 𝓕)
    (hB : B.Nonempty) :
    ((traceFiber 𝓕 U S A B a).card : ℝ) ≤ R ^ (w - B.card) := by
  classical
  refine le_trans ?_ (hsp.filter_card_le hB)
  have hsub : traceFiber 𝓕 U S A B a ⊆ 𝓕.filter fun T => B ⊆ T := by
    intro T hT
    rw [mem_traceFiber] at hT
    refine Finset.mem_filter.mpr ⟨hT.1, ?_⟩
    intro x hx
    rw [← hT.2.2.2] at hx
    exact chi_subset hT.1 (Finset.mem_inter.mp hx).1
  exact_mod_cast Finset.card_le_card hsub

/-- **The empty trace too.** Spreadness says nothing about the empty core, but the whole family
is bounded there — which is the hypothesis Rao gets from `ℓ = ⌈r^k⌉`. Trimming lands at `⌈R^w⌉`,
so the bound arrives as `R^w + 1`; the `+1` is absorbed into a factor `2`, uniform over the
traces. With this the count needs no `A ≠ ∅`, so the `b = 0` boundary disappears. -/
theorem card_traceFiber_le' {R : ℝ} {w : ℕ} {B : Finset α} (hsp : IsRaoSpread R w 𝓕)
    (hR : 1 ≤ R) (hFcard : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) :
    ((traceFiber 𝓕 U S A B a).card : ℝ) ≤ 2 * R ^ (w - B.card) := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have hsub : ((traceFiber 𝓕 U S A ∅ a).card : ℝ) ≤ ((𝓕.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h1 : (1 : ℝ) ≤ R ^ w := one_le_pow₀ hR
    have h2 : ((traceFiber 𝓕 U S A ∅ a).card : ℝ) ≤ 2 * R ^ w := by
      linarith [le_trans hsub hFcard]
    simpa using h2
  · have h := card_traceFiber_le (U := U) (S := S) (A := A) (a := a) hsp hB
    have hpow : (0 : ℝ) ≤ R ^ (w - B.card) := by
      have : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
      positivity
    linarith

/-- In a fiber, the part of the residual that `V` must swallow has size exactly `a − |B|`. -/
theorem card_sdiff_of_mem_traceFiber {B : Finset α} (hT : T ∈ traceFiber 𝓕 U S A B a) :
    (chi 𝓕 T U \ chi 𝓕 S U).card + B.card = a := by
  rw [mem_traceFiber] at hT
  have hpart : (chi 𝓕 T U \ chi 𝓕 S U).card + (chi 𝓕 T U ∩ chi 𝓕 S U).card
      = (chi 𝓕 T U).card := Finset.card_sdiff_add_card_inter _ _
  rw [hT.2.2.2, hT.2.2.1] at hpart
  exact hpart

/-- The traces that can occur: subsets of `χ(S,U)` containing `A`. -/
noncomputable def traces (𝓕 : Finset (Finset α)) (U S A : Finset α) : Finset (Finset α) :=
  (chi 𝓕 S U).powerset.filter fun B => A ⊆ B

lemma mem_traces {B : Finset α} :
    B ∈ traces 𝓕 U S A ↔ B ⊆ chi 𝓕 S U ∧ A ⊆ B := by
  rw [traces, Finset.mem_filter, Finset.mem_powerset]

/-- Every member that can contribute has its trace among `traces`, so the fibers cover: this
is the `maps_to` side condition of the fiberwise count. -/
theorem trace_mem_traces (hA : A ⊆ chi 𝓕 T U) (hAS : A ⊆ chi 𝓕 S U) :
    chi 𝓕 T U ∩ chi 𝓕 S U ∈ traces 𝓕 U S A := by
  refine mem_traces.mpr ⟨Finset.inter_subset_right, ?_⟩
  intro x hx
  exact Finset.mem_inter.mpr ⟨hA hx, hAS hx⟩

/-! ## Summing over the traces, exactly

Rao bounds the sum over traces by `2^{|χ(X,U)|}·max`. The sum is geometric, so it can be done
exactly, and doing so replaces his constant `6` by `4`. -/

/-- `∑_{C ⊆ Z} y^{|C|} = (1+y)^{|Z|}` — the binomial theorem, from `Finset.prod_add`. -/
theorem sum_powerset_pow (Z : Finset α) (y : ℝ) :
    ∑ C ∈ Z.powerset, y ^ C.card = (1 + y) ^ Z.card := by
  classical
  have h := Finset.prod_add (fun _ : α => y) (fun _ : α => (1 : ℝ)) Z
  simp only [Finset.prod_const, one_pow, mul_one] at h
  rw [← h]
  ring

/-- The traces of `A` in `χ(S,U)` are the complements of the subsets of `χ(S,U) \ A`, so the
geometric sum over them is exact. -/
theorem sum_traces_pow (hAS : A ⊆ chi 𝓕 S U) (y : ℝ) :
    ∑ B ∈ traces 𝓕 U S A, y ^ ((chi 𝓕 S U).card - B.card)
      = (1 + y) ^ ((chi 𝓕 S U).card - A.card) := by
  classical
  rw [← Finset.card_sdiff_of_subset hAS, ← sum_powerset_pow (chi 𝓕 S U \ A) y]
  refine Finset.sum_nbij' (i := fun B => chi 𝓕 S U \ B) (j := fun C => chi 𝓕 S U \ C)
    ?_ ?_ ?_ ?_ ?_
  · intro B hB
    rw [mem_traces] at hB
    exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hB.2)
  · intro C hC
    rw [Finset.mem_powerset] at hC
    refine mem_traces.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨hAS hx, ?_⟩
    intro hxC
    exact (Finset.mem_sdiff.mp (hC hxC)).2 hx
  · intro B hB
    rw [mem_traces] at hB
    exact Finset.sdiff_sdiff_eq_self hB.1
  · intro C hC
    rw [Finset.mem_powerset] at hC
    exact Finset.sdiff_sdiff_eq_self (le_trans hC Finset.sdiff_subset)
  · intro B hB
    rw [mem_traces] at hB
    rw [Finset.card_sdiff_of_subset hB.1]

/-- `R^{w−c}·x^{a−c} = R^{w−a}·(R·x)^{a−c}`: the form in which the trace sum is geometric. -/
theorem pow_regroup {R x : ℝ} {a c w : ℕ} (hca : c ≤ a) (haw : a ≤ w) :
    R ^ (w - c) * x ^ (a - c) = R ^ (w - a) * (R * x) ^ (a - c) := by
  rw [mul_pow, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- `R^{w−a}·(1+Rx)^{a−b} = R^{w−b}·(x + 1/R)^{a−b}`. -/
theorem pow_geom_regroup {R x : ℝ} (hR : 0 < R) {a b w : ℕ} (hba : b ≤ a) (haw : a ≤ w) :
    R ^ (w - a) * (1 + R * x) ^ (a - b) = R ^ (w - b) * (x + 1 / R) ^ (a - b) := by
  have h1 : (1 : ℝ) + R * x = R * (x + 1 / R) := by field_simp; ring
  rw [h1, mul_pow, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-! ## Assembling the count

Per member, per fiber, then over the traces. Rao bounds the sum over traces by
`2^{|χ(X,U)|}·max` ("`B` takes each value with probability at least `2^{−|χ(X,U)|}`"); the
same crude step is taken here, and it is what produces his constant `6`. (Summing the
geometric series exactly instead gives `R^{w−b}(x + 1/R)^{a−b}` and a constant `4`; the slack
is not worth the extra bookkeeping.) -/

variable {R : ℝ} {w b : ℕ} {B : Finset α}

/-- The `V`-count for a member of a fiber, in terms of `a − |B|`. -/
theorem count_le_of_mem_traceFiber (hTf : T ∈ traceFiber 𝓕 U S A B a) (hTX : T ⊆ X)
    (hav : a ≤ v) (hvX : v ≤ (X \ U).card) (han : a < (X \ U).card) :
    ((((X \ U).powersetCard v).filter
        fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℝ)
        * (((X \ U).card - a : ℕ) : ℝ) ^ (a - B.card)
      ≤ (((X \ U).card.choose v : ℕ) : ℝ) * (v : ℝ) ^ (a - B.card) := by
  classical
  obtain ⟨hT, hA, hcard, -⟩ := mem_traceFiber.mp hTf
  have ht : (chi 𝓕 T U \ chi 𝓕 S U).card + B.card = a := card_sdiff_of_mem_traceFiber hTf
  have hteq : (chi 𝓕 T U \ chi 𝓕 S U).card = a - B.card := by omega
  have hv : (chi 𝓕 T U \ chi 𝓕 S U).card ≤ v := by omega
  have hbase := card_filter_tau_le hT hA hcard hTX hv hvX
  rw [hteq] at hbase
  refine le_trans ?_ hbase
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have hle : ((X \ U).card - a : ℕ) ≤ ((X \ U).card - (a - B.card) : ℕ) := by omega
  exact_mod_cast hle

/-- Rao's `R^{w−|B|}x^{a−|B|} ≤ R^{w−b}x^{a−b}` for `|B| ≥ b`, whenever `R·x ≥ 1`: the shift
from `|B|` down to `b` costs a factor `(Rx)^{|B|−b} ≥ 1`. -/
theorem pow_shift_le {x : ℝ} (hR : 0 < R) (hx : 0 < x) (hRx : 1 ≤ R * x)
    {c : ℕ} (hbc : b ≤ c) (hca : c ≤ a) (haw : a ≤ w) :
    R ^ (w - c) * x ^ (a - c) ≤ R ^ (w - b) * x ^ (a - b) := by
  have hsplit : R ^ (w - c) * x ^ (a - c) * (R * x) ^ (c - b)
      = R ^ (w - b) * x ^ (a - b) := by
    rw [mul_pow]
    calc R ^ (w - c) * x ^ (a - c) * (R ^ (c - b) * x ^ (c - b))
        = (R ^ (w - c) * R ^ (c - b)) * (x ^ (a - c) * x ^ (c - b)) := by ring
      _ = R ^ ((w - c) + (c - b)) * x ^ ((a - c) + (c - b)) := by rw [← pow_add, ← pow_add]
      _ = R ^ (w - b) * x ^ (a - b) := by congr 2 <;> omega
  rw [← hsplit]
  have hge : (1 : ℝ) ≤ (R * x) ^ (c - b) := one_le_pow₀ hRx
  exact le_mul_of_one_le_right (by positivity) hge

/-- **The sum over all `V` of the class sizes.** Members are grouped by their trace `B`;
spreadness caps each group at `R^{w−|B|}`, the `V`-count contributes `C(n−u,v)·x^{a−|B|}` with
`x = v/(n−u−a)`, and the number of traces is at most `2^a`. -/
theorem sum_card_tau_le (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hAS : A ⊆ chi 𝓕 S U) (hFcard : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hv0 : 0 < v)
    (hAb : A.card = b)
    (hSa : (chi 𝓕 S U).card = a) (hR : 1 ≤ R)
    (hav : a ≤ v) (hvX : v ≤ (X \ U).card) (han : a < (X \ U).card) (haw : a ≤ w)
    (_hRx : 1 ≤ R * ((v : ℝ) / (((X \ U).card - a : ℕ) : ℝ))) :
    ((∑ V ∈ (X \ U).powersetCard v, (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℕ) : ℝ)
      ≤ (((X \ U).card.choose v : ℕ) : ℝ)
          * (2 * (R ^ (w - b)
            * (((v : ℝ) / (((X \ U).card - a : ℕ) : ℝ)) + 1 / R) ^ (a - b))) := by
  classical
  set n' : ℕ := (X \ U).card with hn'
  set x : ℝ := (v : ℝ) / ((n' - a : ℕ) : ℝ) with hx
  have hAa : A.card ≤ a := by rw [← hSa]; exact Finset.card_le_card hAS
  have hba : b ≤ a := by omega
  have hxpos : 0 < x := by
    rw [hx]
    have h1 : (0 : ℝ) < ((n' - a : ℕ) : ℝ) := by
      have : 0 < n' - a := by omega
      exact_mod_cast this
    have h2 : (0 : ℝ) < (v : ℝ) := by
      have : 0 < v := by omega
      exact_mod_cast this
    positivity
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set f : Finset α → ℕ := fun T =>
    (((X \ U).powersetCard v).filter fun V => T ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card with hf
  -- the sum over `V` is a sum over members
  rw [sum_card_tau_eq]
  -- members outside the fibers contribute nothing
  set 𝓕' : Finset (Finset α) :=
    𝓕.filter (fun T => A ⊆ chi 𝓕 T U ∧ (chi 𝓕 T U).card = a) with h𝓕'
  have hzero : ∀ T ∈ 𝓕, T ∉ 𝓕' → f T = 0 := by
    intro T hT hT'
    rw [hf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro V _ hmem
    obtain ⟨-, hA, -, hcard⟩ := mem_tau.mp hmem
    exact hT' (Finset.mem_filter.mpr ⟨hT, hA, hcard⟩)
  have hrestrict : ∑ T ∈ 𝓕, f T = ∑ T ∈ 𝓕', f T :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  rw [hrestrict]
  -- group by trace
  have hmaps : ∀ T ∈ 𝓕', chi 𝓕 T U ∩ chi 𝓕 S U ∈ traces 𝓕 U S A := by
    intro T hT
    rw [h𝓕', Finset.mem_filter] at hT
    exact trace_mem_traces hT.2.1 hAS
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  -- each fiber
  have hfiber : ∀ B' ∈ traces 𝓕 U S A,
      ((∑ T ∈ 𝓕'.filter (fun T => chi 𝓕 T U ∩ chi 𝓕 S U = B'), f T : ℕ) : ℝ)
        ≤ ((n'.choose v : ℕ) : ℝ) * (2 * (R ^ (w - B'.card) * x ^ (a - B'.card))) := by
    intro B' hB'
    have hBsub : B' ⊆ chi 𝓕 S U := (mem_traces.mp hB').1
    have hAB : A ⊆ B' := (mem_traces.mp hB').2
    have hBcard : B'.card ≤ a := by
      rw [← hSa]; exact Finset.card_le_card hBsub
    have hbB : b ≤ B'.card := by
      rw [← hAb]; exact Finset.card_le_card hAB
    -- the fiber is `traceFiber`
    have hfibeq : 𝓕'.filter (fun T => chi 𝓕 T U ∩ chi 𝓕 S U = B')
        = traceFiber 𝓕 U S A B' a := by
      ext T
      rw [h𝓕', Finset.mem_filter, Finset.mem_filter, mem_traceFiber]
      tauto
    rw [hfibeq]
    -- per member, then times the fiber size
    have hper : ∀ T ∈ traceFiber 𝓕 U S A B' a,
        ((f T : ℕ) : ℝ) ≤ ((n'.choose v : ℕ) : ℝ) * x ^ (a - B'.card) := by
      intro T hTf
      have hTX : T ⊆ X := hSX T (mem_traceFiber.mp hTf).1
      have hmul := count_le_of_mem_traceFiber hTf hTX hav hvX han
      have hpos : (0 : ℝ) < ((n' - a : ℕ) : ℝ) := by
        have hlt : 0 < n' - a := Nat.sub_pos_of_lt han
        exact_mod_cast hlt
      have hden : (0 : ℝ) < ((n' - a : ℕ) : ℝ) ^ (a - B'.card) := by positivity
      rw [hx, div_pow, ← mul_div_assoc, le_div_iff₀ hden]
      exact hmul
    calc ((∑ T ∈ traceFiber 𝓕 U S A B' a, f T : ℕ) : ℝ)
        = ∑ T ∈ traceFiber 𝓕 U S A B' a, ((f T : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ∑ _T ∈ traceFiber 𝓕 U S A B' a, ((n'.choose v : ℕ) : ℝ) * x ^ (a - B'.card) :=
          Finset.sum_le_sum hper
      _ = ((traceFiber 𝓕 U S A B' a).card : ℝ)
            * (((n'.choose v : ℕ) : ℝ) * x ^ (a - B'.card)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * R ^ (w - B'.card) * (((n'.choose v : ℕ) : ℝ) * x ^ (a - B'.card)) := by
          refine mul_le_mul_of_nonneg_right (card_traceFiber_le' hsp hR hFcard) (by positivity)
      _ = ((n'.choose v : ℕ) : ℝ) * (2 * (R ^ (w - B'.card) * x ^ (a - B'.card))) := by ring
  -- sum over the traces: the series is geometric, so sum it exactly
  have hgeom : ∑ B' ∈ traces 𝓕 U S A, (R ^ (w - B'.card) * x ^ (a - B'.card))
      = R ^ (w - a) * (1 + R * x) ^ (a - b) := by
    have hre : ∀ B' ∈ traces 𝓕 U S A,
        R ^ (w - B'.card) * x ^ (a - B'.card) = R ^ (w - a) * (R * x) ^ (a - B'.card) := by
      intro B' hB'
      have hBa : B'.card ≤ a := by
        rw [← hSa]; exact Finset.card_le_card (mem_traces.mp hB').1
      exact pow_regroup hBa haw
    rw [Finset.sum_congr rfl hre, ← Finset.mul_sum]
    congr 1
    have := sum_traces_pow (𝓕 := 𝓕) (U := U) (S := S) (A := A) hAS (R * x)
    rw [hSa, hAb] at this
    exact this
  calc ((∑ B' ∈ traces 𝓕 U S A, ∑ T ∈ 𝓕'.filter (fun T => chi 𝓕 T U ∩ chi 𝓕 S U = B'),
        f T : ℕ) : ℝ)
      = ∑ B' ∈ traces 𝓕 U S A,
          ((∑ T ∈ 𝓕'.filter (fun T => chi 𝓕 T U ∩ chi 𝓕 S U = B'), f T : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ B' ∈ traces 𝓕 U S A,
          ((n'.choose v : ℕ) : ℝ) * (2 * (R ^ (w - B'.card) * x ^ (a - B'.card))) :=
        Finset.sum_le_sum hfiber
    _ = ((n'.choose v : ℕ) : ℝ) * 2
          * ∑ B' ∈ traces 𝓕 U S A, (R ^ (w - B'.card) * x ^ (a - B'.card)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun B' _ => by ring
    _ = ((n'.choose v : ℕ) : ℝ) * 2 * (R ^ (w - a) * (1 + R * x) ^ (a - b)) := by rw [hgeom]
    _ = ((n'.choose v : ℕ) : ℝ) * (2 * (R ^ (w - b) * (x + 1 / R) ^ (a - b))) := by
        rw [← pow_geom_regroup hR0 hba haw]
        ring

/-! ## The exceptional `V`s

`φ` is Rao's threshold `r^k·(ρv/n)^{|χ(X,U)|}·(vr/n)^{−|χ(X,W)|}`, written with `vn = v/(n−u)`
and without negative exponents. A `V` is exceptional when its class exceeds `φ`; those are the
`V`s case 2's encoder has to locate, and there are few of them. -/

/-- Rao's `φ`, as `R^{w−b}·(ρ·vn)^a·vn^{−b}`. -/
noncomputable def phi (R ρ vn : ℝ) (w a b : ℕ) : ℝ :=
  R ^ (w - b) * ((ρ * vn) ^ a * (vn⁻¹) ^ b)

/-- The `V`s whose class is oversized. -/
noncomputable def exceptional (𝓕 : Finset (Finset α)) (X U S A : Finset α) (v a : ℕ)
    (φ : ℝ) : Finset (Finset α) :=
  ((X \ U).powersetCard v).filter fun V => φ < ((tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℝ)

/-- **Markov**: each exceptional `V` contributes more than `φ` to the sum of class sizes. -/
theorem card_exceptional_mul_le (𝓕 : Finset (Finset α)) (X U S A : Finset α) (v a : ℕ)
    {φ : ℝ} (_hφ : 0 ≤ φ) :
    ((exceptional 𝓕 X U S A v a φ).card : ℝ) * φ
      ≤ ((∑ V ∈ (X \ U).powersetCard v, (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℕ) : ℝ) := by
  classical
  have hcast : ((∑ V ∈ (X \ U).powersetCard v, (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℕ) : ℝ)
      = ∑ V ∈ (X \ U).powersetCard v, ((tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℝ) := by
    push_cast; rfl
  rw [hcast]
  calc ((exceptional 𝓕 X U S A v a φ).card : ℝ) * φ
      = ∑ _V ∈ exceptional 𝓕 X U S A v a φ, φ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ V ∈ exceptional 𝓕 X U S A v a φ, ((tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℝ) := by
        refine Finset.sum_le_sum fun V hV => ?_
        rw [exceptional, Finset.mem_filter] at hV
        exact le_of_lt hV.2
    _ ≤ ∑ V ∈ (X \ U).powersetCard v, ((tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro V _ _
        positivity

/-- The arithmetic of case 2: dividing the count by `φ` leaves `(8/ρ)^a`. The `8` is
`2·(3 + 1)` — `3` from `n−u−a ≥ (n−u)/3` and `1` from `1/R ≤ v/(n−u)`, the two terms of the
geometric sum's ratio `x + 1/R`, and the `2` from the trimming slack `|𝓕| ≤ R^w + 1`, absorbed
into the base using `a ≥ 1`. -/
private lemma exceptional_arith {E C P y ρ vn : ℝ} {b k : ℕ} (h1 : 1 ≤ b + k)
    (hC : 0 ≤ C) (hP : 0 < P) (hρ : 0 < ρ) (hvn : 0 < vn) (hy : 0 ≤ y) (hy4 : y ≤ 4 * vn)
    (hE : E * (P * ((ρ * vn) ^ (b + k) * (vn⁻¹) ^ b)) ≤ C * (2 * (P * y ^ k))) :
    E ≤ C * (8 / ρ) ^ (b + k) := by
  have hvnne : vn ≠ 0 := ne_of_gt hvn
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hden : (0 : ℝ) < P * ((ρ * vn) ^ (b + k) * (vn⁻¹) ^ b) := by positivity
  rw [← le_div_iff₀ hden] at hE
  refine le_trans hE ?_
  rw [div_le_iff₀ hden]
  have hyk : y ^ k ≤ (4 * vn) ^ k := pow_le_pow_left₀ hy hy4 k
  have hid : (8 / ρ) ^ (b + k) * ((ρ * vn) ^ (b + k) * (vn⁻¹) ^ b) = (8 : ℝ) ^ (b + k) * vn ^ k := by
    rw [div_pow, mul_pow, inv_pow, pow_add vn b k]
    field_simp
  -- `2·4^k ≤ 2·4^{b+k} ≤ 8^{b+k}`: the trimming factor rides on the base once `b + k ≥ 1`
  have h48 : 2 * (4 : ℝ) ^ k ≤ (8 : ℝ) ^ (b + k) := by
    have h4 : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ (b + k) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (b + k) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (b + k) := pow_le_pow_right₀ (by norm_num) h1
    have h8 : (8 : ℝ) ^ (b + k) = (2 : ℝ) ^ (b + k) * (4 : ℝ) ^ (b + k) := by
      rw [← mul_pow]; norm_num
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4) (b + k),
      pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (b + k)]
  calc C * (2 * (P * y ^ k))
      ≤ C * (2 * (P * ((4 : ℝ) ^ k * vn ^ k))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ (le_of_lt hP)) (by norm_num)) hC
        calc y ^ k ≤ (4 * vn) ^ k := hyk
          _ = (4 : ℝ) ^ k * vn ^ k := by rw [mul_pow]
    _ = C * ((2 * (4 : ℝ) ^ k) * vn ^ k) * P := by ring
    _ ≤ C * ((8 : ℝ) ^ (b + k) * vn ^ k) * P := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (le_of_lt hP)
        exact mul_le_mul_of_nonneg_right h48 (by positivity)
    _ = C * (8 / ρ) ^ (b + k) * (P * ((ρ * vn) ^ (b + k) * (vn⁻¹) ^ b)) := by
        rw [← hid]; ring

/-- **Rao's case-2 estimate.** Few `V` are exceptional:

  `#{V : |τ(A, V ∪ χ(S,U), a)| > φ} ≤ C(n−u, v)·(8/ρ)^a`.

Everything feeding this is a cardinality: the swap, the exact `V`-count, spreadness on the
fibers, `2^a` traces, and Markov. Rao's `6` is `2·3`, from the trace count and from
`n−u−a ≥ (n−u)/3`; here the trace count is summed exactly (a `4`) and the trimming slack
`|𝓕| ≤ R^w + 1` costs a factor `2`, absorbed into the base via `a ≥ 1`. -/
theorem card_exceptional_le {R ρ : ℝ} {w b : ℕ} (hsp : IsRaoSpread R w 𝓕)
    (hSX : ∀ T ∈ 𝓕, T ⊆ X) (hAS : A ⊆ chi 𝓕 S U)
    (hFcard : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hv0 : 0 < v) (hAb : A.card = b)
    (hSa : (chi 𝓕 S U).card = a) (ha1 : 1 ≤ a) (hR : 1 ≤ R) (hρ : 0 < ρ)
    (hav : a ≤ v) (hvX : v ≤ (X \ U).card) (han : a < (X \ U).card) (haw : a ≤ w)
    (h3 : (((X \ U).card : ℕ) : ℝ) ≤ 3 * ((((X \ U).card - a : ℕ)) : ℝ))
    (hRx : 1 ≤ R * ((v : ℝ) / ((((X \ U).card - a : ℕ)) : ℝ)))
    (hRvn : 1 ≤ R * ((v : ℝ) / (((X \ U).card : ℕ) : ℝ))) :
    ((exceptional 𝓕 X U S A v a
        (phi R ρ ((v : ℝ) / (((X \ U).card : ℕ) : ℝ)) w a b)).card : ℝ)
      ≤ ((((X \ U).card.choose v : ℕ)) : ℝ) * (8 / ρ) ^ a := by
  classical
  set n' : ℕ := (X \ U).card with hn'
  set vn : ℝ := (v : ℝ) / ((n' : ℕ) : ℝ) with hvndef
  set x : ℝ := (v : ℝ) / (((n' - a : ℕ)) : ℝ) with hxdef
  -- basic positivity
  have hba : b ≤ a := by
    rw [← hAb, ← hSa]; exact Finset.card_le_card hAS
  have hn'0 : 0 < n' := by omega
  have hn'a : 0 < n' - a := by omega
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv0
  have hn'R : (0 : ℝ) < ((n' : ℕ) : ℝ) := by exact_mod_cast hn'0
  have hn'aR : (0 : ℝ) < (((n' - a : ℕ)) : ℝ) := by exact_mod_cast hn'a
  have hvnpos : 0 < vn := by rw [hvndef]; positivity
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  -- `x ≤ 3·vn`, i.e. `n' ≤ 3(n'−a)`
  have hx3 : x ≤ 3 * vn := by
    have h1 : (3 : ℝ) * vn = (3 * (v : ℝ)) / (((n' : ℕ)) : ℝ) := by rw [hvndef]; ring
    rw [hxdef, h1, div_le_div_iff₀ hn'aR hn'R]
    nlinarith [h3, hvR]
  -- the two halves
  have hφ0 : 0 ≤ phi R ρ vn w a b := by
    rw [phi]; positivity
  have hE := card_exceptional_mul_le 𝓕 X U S A v a (φ := phi R ρ vn w a b) hφ0
  have hsum := sum_card_tau_le hsp hSX hAS hFcard hv0 hAb hSa hR hav hvX han haw hRx
  have hcomb : ((exceptional 𝓕 X U S A v a (phi R ρ vn w a b)).card : ℝ)
      * (R ^ (w - b) * ((ρ * vn) ^ a * (vn⁻¹) ^ b))
      ≤ (((n'.choose v : ℕ)) : ℝ) * (2 * (R ^ (w - b) * (x + 1 / R) ^ (a - b))) := by
    have := le_trans hE hsum
    rwa [phi] at this
  -- the geometric ratio is at most `4·vn`
  have hy4 : x + 1 / R ≤ 4 * vn := by
    have hinv : 1 / R ≤ vn := by
      rw [div_le_iff₀ hR0]
      rw [hvndef] at hRvn ⊢
      nlinarith [hRvn]
    linarith [hx3, hinv]
  -- write `a = b + k` and finish by the arithmetic lemma
  obtain ⟨k, hk⟩ : ∃ k, a = b + k := ⟨a - b, by omega⟩
  subst hk
  rw [show b + k - b = k from by omega] at hcomb
  exact exceptional_arith ha1 (by positivity) (by positivity) hρ hvnpos
    (by positivity) hy4 hcomb

/-! ## Case 2's encoder

Rao's case 2 (his p. 5–6) writes: the case bit, then `S` outright, then `A`, then `V` among
the exceptional sets. Unlike case 1, this list *is* decodable as given — after `S` and `A` the
decoder knows `a = |χ(S,U)|` and `b = |A|`, hence `φ`, hence the exceptional set to index into.
This is the contrast recorded in formalization note R1: under the sequential field-by-field
reading used here, the case-2 list determines each width from previously decoded data.

The three fields cost `k_𝓕 + |χ(S,U)| + k_E`, with `k_E ≈ log(C(n−u,v)·(6/ρ)^a) + 1` supplied
by `card_exceptional_le`. -/

variable {R ρ vn : ℝ} {w : ℕ}

/-- The case-2 branch: some `A` of the right size overflows the class. -/
def Case2 (𝓕 : Finset (Finset α)) (X U S V : Finset α) (v w : ℕ) (R ρ vn : ℝ) : Prop :=
  ∃ A, A ⊆ chi 𝓕 S U ∧ A.card = (chi 𝓕 S (U ∪ V)).card ∧
    V ∈ exceptional 𝓕 X U S A v (chi 𝓕 S U).card
      (phi R ρ vn w (chi 𝓕 S U).card A.card)

/-- The record case 2 writes. -/
abbrev Case2Fields (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ) (R ρ vn : ℝ) : Type _ :=
  Σ S : {S // S ∈ 𝓕}, Σ A : {A // A ∈ (chi 𝓕 S.1 U).powerset},
    {V // V ∈ exceptional 𝓕 X U S.1 A.1 v (chi 𝓕 S.1 U).card
      (phi R ρ vn w (chi 𝓕 S.1 U).card A.1.card)}

/-- The case-2 code. -/
noncomputable def case2Code (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ) (kF : ℕ) (hF : 𝓕.card ≤ 2 ^ kF) (kE : Finset α → Finset α → ℕ)
    (hE : ∀ S A : Finset α, (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
        (phi R ρ vn w (chi 𝓕 S U).card A.card)).card ≤ 2 ^ kE S A) :
    Coding.Code (Case2Fields 𝓕 X U v w R ρ vn) :=
  (Coding.Code.memCode 𝓕 kF hF).sigma fun S =>
    (Coding.Code.powersetCode (chi 𝓕 S.1 U)).sigma fun A =>
      Coding.Code.memCode _ (kE S.1 A.1) (hE S.1 A.1)

/-- Its length: the three field widths. -/
theorem case2Code_length (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ) (kF : ℕ) (hF : 𝓕.card ≤ 2 ^ kF) (kE : Finset α → Finset α → ℕ)
    (hE : ∀ S A : Finset α, (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
        (phi R ρ vn w (chi 𝓕 S U).card A.card)).card ≤ 2 ^ kE S A)
    (p : Case2Fields 𝓕 X U v w R ρ vn) :
    ((case2Code 𝓕 X U v w R ρ vn kF hF kE hE).enc p).length
      = kF + (chi 𝓕 p.1.1 U).card + kE p.1.1 p.2.1.1 := by
  rw [case2Code, Coding.Code.length_sigma, Coding.Code.length_sigma,
    Coding.Code.length_memCode, Coding.Code.length_powersetCode, Coding.Code.length_memCode]
  ring

/-- The decoder: `S` and `V` are fields. -/
noncomputable def case2Decode (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ) (p : Case2Fields 𝓕 X U v w R ρ vn) : Finset α × Finset α :=
  (p.2.2.1, p.1.1)

/-- The encoder, on the pairs that fall in case 2. -/
noncomputable def case2Encode (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ)
    (p : {p : Finset α × Finset α // p.2 ∈ 𝓕 ∧ Case2 𝓕 X U p.2 p.1 v w R ρ vn}) :
    Case2Fields 𝓕 X U v w R ρ vn :=
  let hA := Classical.choose_spec p.2.2
  ⟨⟨p.1.2, p.2.1⟩,
   ⟨Classical.choose p.2.2, Finset.mem_powerset.mpr hA.1⟩,
   ⟨p.1.1, hA.2.2⟩⟩

/-- **The encoding decodes.** -/
theorem case2Decode_encode (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ) (R ρ vn : ℝ)
    (p : {p : Finset α × Finset α // p.2 ∈ 𝓕 ∧ Case2 𝓕 X U p.2 p.1 v w R ρ vn}) :
    case2Decode 𝓕 X U v w R ρ vn (case2Encode 𝓕 X U v w R ρ vn p) = p.1 := by
  rw [case2Decode, case2Encode]

theorem case2Encode_injective (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ) :
    Function.Injective (case2Encode 𝓕 X U v w R ρ vn) := by
  intro p q hpq
  have h : case2Decode 𝓕 X U v w R ρ vn (case2Encode 𝓕 X U v w R ρ vn p)
      = case2Decode 𝓕 X U v w R ρ vn (case2Encode 𝓕 X U v w R ρ vn q) := by rw [hpq]
  rw [case2Decode_encode, case2Decode_encode] at h
  exact Subtype.ext h

/-- **The case-2 code on pairs.** -/
noncomputable def case2PairCode (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ) (kF : ℕ) (hF : 𝓕.card ≤ 2 ^ kF) (kE : Finset α → Finset α → ℕ)
    (hE : ∀ S A : Finset α, (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
        (phi R ρ vn w (chi 𝓕 S U).card A.card)).card ≤ 2 ^ kE S A) :
    Coding.Code {p : Finset α × Finset α // p.2 ∈ 𝓕 ∧ Case2 𝓕 X U p.2 p.1 v w R ρ vn} :=
  (case2Code 𝓕 X U v w R ρ vn kF hF kE hE).comap (case2Encode 𝓕 X U v w R ρ vn)
    (case2Encode_injective 𝓕 X U v w R ρ vn)

end Rao

end Sunflower

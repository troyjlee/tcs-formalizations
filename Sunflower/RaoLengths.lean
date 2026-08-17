/-
# Instantiating the field widths

`RaoWidths` shows that a `⌈log₂N⌉`-bit field indexes a set of size `N` at a cost of
`log₂N + 1`. What remains is to *use* that: define each field's width as the width its own set
demands, which makes the `card ≤ 2^k` side conditions trivial, and then bound the widths — per
pair, where the counting lemmas apply — to reach the two shapes `branch1_fits`/`branch2_fits`
consume.

The design point: `width n = ⌈log₂ n⌉` for the **actual** cardinality, not for the bound. The
code is then always well-defined, and the estimates enter only in the length calculation. That
matters for case 1, whose `τ`-field is bounded by `φ` *only on case-1 pairs* — a width defined
from `φ` would not give a code at all.
-/
import Sunflower.RaoWidths

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)} {X U S V : Finset α}
variable {v w : ℕ} {R ρ vn : ℝ}

/-! ## Widths -/

/-- The width of an "index into this set" field: as many bits as its size demands. -/
noncomputable def width (n : ℕ) : ℕ := ⌈Real.logb 2 (n : ℝ)⌉₊

/-- The width always suffices — so the code is defined unconditionally. -/
theorem card_le_two_pow_width (n : ℕ) : n ≤ 2 ^ width n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [width]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact card_le_two_pow_ceil_logb hn' le_rfl

/-- And it costs `log₂N + 1` for any bound `N` on the size: Rao's "+1". -/
theorem width_le {n : ℕ} {N : ℝ} (hn : 1 ≤ n) (h : (n : ℝ) ≤ N) :
    ((width n : ℕ) : ℝ) ≤ Real.logb 2 N + 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : ((width n : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) + 1 := ceil_logb_le hn1
  have h2 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 N :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) h
  linarith

/-! ## What the case-1 branch knows

Being outside case 2 says precisely that the class of the transmitted `A` does not overflow
`φ` — which is what bounds the width of case 1's fifth field. -/

/-- **Case 1's `τ`-bound.** If `(V,S)` is not in case 2, then for any `A` of the right size the
class is within `φ`. -/
theorem tau_card_le_phi_of_not_case2 {A : Finset α} (hAS : A ⊆ chi 𝓕 S U)
    (hAb : A.card = (chi 𝓕 S (U ∪ V)).card) (hV : V ∈ (X \ U).powersetCard v)
    (h : ¬ Case2 𝓕 X U S V v w R ρ vn) :
    ((tau 𝓕 U A (V ∪ chi 𝓕 S U) (chi 𝓕 S U).card).card : ℝ)
      ≤ phi R ρ vn w (chi 𝓕 S U).card A.card := by
  by_contra hlt
  push Not at hlt
  exact h ⟨A, hAS, hAb, by
    rw [exceptional, Finset.mem_filter]
    exact ⟨hV, hlt⟩⟩

/-- `S` itself is in the class, so the class is nonempty — which `width_le` needs. -/
theorem one_le_tau_card {A : Finset α} (hS : S ∈ 𝓕) (hAS : A ⊆ chi 𝓕 S U) :
    1 ≤ (tau 𝓕 U A (V ∪ chi 𝓕 S U) (chi 𝓕 S U).card).card :=
  Finset.card_pos.mpr ⟨S, by
    have := mem_tau_self (W := V) hS hAS
    rw [show V ∪ chi 𝓕 S U = V ∪ chi 𝓕 S U from rfl]
    exact mem_tau.mpr ⟨hS, hAS, Finset.subset_union_right, rfl⟩⟩

/-- Likewise `D = V ∪ χ(S,U)` is among its own candidates. -/
theorem one_le_Dcands_card {X : Finset α} (hS : S ∈ 𝓕) (hSX : S ⊆ X)
    (hV : V ∈ (X \ U).powersetCard v) :
    1 ≤ (Dcands X U v (chi 𝓕 S U).card).card := by
  obtain ⟨hVX, hVcard⟩ := Finset.mem_powersetCard.mp hV
  exact Finset.card_pos.mpr ⟨V ∪ chi 𝓕 S U, mem_Dcands_of_pair hS hSX hVX hVcard⟩

/-! ## Expanding `log₂ φ`

`φ = R^{w−b}·(ρ·vn)^a·vn^{−b}`, so its logarithm is linear in `a` and `b`, and the `a·log₂vn`
inside it is exactly what cancels the `a·log₂(n'/v)` that field (3) costs. That cancellation is
why case 1's bound has no `vn` in it at all. -/

theorem logb_phi (hR : 0 < R) (hρ : 0 < ρ) (hvn : 0 < vn) {a b : ℕ} (hbw : b ≤ w) :
    Real.logb 2 (phi R ρ vn w a b)
      = (w : ℝ) * Real.logb 2 R + (a : ℝ) * (Real.logb 2 ρ + Real.logb 2 vn)
        - (b : ℝ) * (Real.logb 2 R + Real.logb 2 vn) := by
  have hρvn : 0 < ρ * vn := mul_pos hρ hvn
  rw [phi]
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
    (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_inv,
    Real.logb_mul (ne_of_gt hρ) (ne_of_gt hvn)]
  have hsub : ((w - b : ℕ) : ℝ) = (w : ℝ) - (b : ℝ) := by
    have : (b : ℝ) ≤ (w : ℝ) := by exact_mod_cast hbw
    push_cast [Nat.cast_sub hbw]
    ring
  rw [hsub]
  ring

/-- The reciprocal form used by field (3): `log₂(n'/v) = −log₂ vn` for `vn = v/n'`. -/
theorem logb_inv_vn (hv : 0 < v) {n' : ℕ} (hn' : 0 < n') :
    Real.logb 2 ((n' : ℝ) / (v : ℝ)) = - Real.logb 2 ((v : ℝ) / (n' : ℝ)) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hn'R : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'
  rw [← Real.logb_inv]
  congr 1
  field_simp

/-! ## Case 2's length, instantiated

With the widths taken from the actual cardinalities, case 2's three fields cost
`log₂(R^w·C) + a·(1 + log₂6 − log₂ρ) + 2` — the shape `branch2_fits` consumes. -/

/-- The case-2 code with its widths instantiated. -/
noncomputable def case2Code' (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ)
    (R ρ vn : ℝ) : Coding.Code (Case2Fields 𝓕 X U v w R ρ vn) :=
  case2Code 𝓕 X U v w R ρ vn (width 𝓕.card) (card_le_two_pow_width _)
    (fun S A => width (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
      (phi R ρ vn w (chi 𝓕 S U).card A.card)).card)
    (fun _ _ => card_le_two_pow_width _)

/-- **Case 2's length bound.** The three fields cost
`log₂(R^w·C(n−u,v)) + a·(4 − log₂ρ) + 3`: the trimming slack `|𝓕| ≤ R^w + 1` costs one bit in
the `k_𝓕` width and one more `a` in the exceptional count's `(8/ρ)^a`. -/
theorem case2Code'_length_le {A : Finset α} {a b : ℕ}
    (hsp : IsRaoSpread R w 𝓕) (hSX : ∀ T ∈ 𝓕, T ⊆ X) (hS : S ∈ 𝓕)
    (hAS : A ⊆ chi 𝓕 S U) (hFcard : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hv0 : 0 < v)
    (hAb : A.card = b) (hSa : (chi 𝓕 S U).card = a) (ha1 : 1 ≤ a) (hR : 1 ≤ R) (hρ : 0 < ρ)
    (hav : a ≤ v) (hvX : v ≤ (X \ U).card) (han : a < (X \ U).card) (haw : a ≤ w)
    (h3 : (((X \ U).card : ℕ) : ℝ) ≤ 3 * ((((X \ U).card - a : ℕ)) : ℝ))
    (hRx : 1 ≤ R * ((v : ℝ) / ((((X \ U).card - a : ℕ)) : ℝ)))
    (hRvn : 1 ≤ R * ((v : ℝ) / (((X \ U).card : ℕ) : ℝ)))
    (hVmem : V ∈ exceptional 𝓕 X U S A v a (phi R ρ vn w a b))
    (hvn : vn = (v : ℝ) / (((X \ U).card : ℕ) : ℝ)) (_hab : b = a ∨ b ≤ a) :
    ((width 𝓕.card : ℕ) : ℝ) + (a : ℝ)
        + ((width (exceptional 𝓕 X U S A v a (phi R ρ vn w a b)).card : ℕ) : ℝ)
      ≤ ((w : ℝ) * Real.logb 2 R
            + Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ))
          + (a : ℝ) * (4 - Real.logb 2 ρ) + 3 := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  -- field (2): `S` among the members — `R^w + 1 ≤ 2R^w` costs the extra bit
  have hF1 : 1 ≤ 𝓕.card := Finset.card_pos.mpr ⟨S, hS⟩
  have hkF : ((width 𝓕.card : ℕ) : ℝ) ≤ (w : ℝ) * Real.logb 2 R + 2 := by
    have h2Rw : ((𝓕.card : ℕ) : ℝ) ≤ 2 * R ^ w := by
      have h1 : (1 : ℝ) ≤ R ^ w := one_le_pow₀ hR
      linarith
    have hwl := width_le hF1 h2Rw
    have hsplit : Real.logb 2 (2 * R ^ w) = 1 + (w : ℝ) * Real.logb 2 R := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
    rw [hsplit] at hwl
    linarith
  -- field (4): `V` among the exceptional sets
  have hE1 : 1 ≤ (exceptional 𝓕 X U S A v a (phi R ρ vn w a b)).card :=
    Finset.card_pos.mpr ⟨V, hVmem⟩
  have hEbound := card_exceptional_le (b := b) hsp hSX hAS hFcard hv0 hAb hSa ha1 hR hρ hav hvX
    han haw h3 hRx hRvn
  rw [← hvn] at hEbound
  have hCpos : (0 : ℝ) < (((X \ U).card.choose v : ℕ) : ℝ) := by
    have : 0 < (X \ U).card.choose v := Nat.choose_pos hvX
    exact_mod_cast this
  have hkE : ((width (exceptional 𝓕 X U S A v a (phi R ρ vn w a b)).card : ℕ) : ℝ)
      ≤ Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ)
          + (a : ℝ) * (3 - Real.logb 2 ρ) + 1 := by
    have hb := width_le hE1 hEbound
    have h8 : Real.logb 2 8 = 3 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    have hsplit : Real.logb 2 (((((X \ U).card.choose v : ℕ)) : ℝ) * (8 / ρ) ^ a)
        = Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ)
            + (a : ℝ) * (3 - Real.logb 2 ρ) := by
      rw [Real.logb_mul (ne_of_gt hCpos) (by positivity), Real.logb_pow,
        Real.logb_div (by norm_num) (ne_of_gt hρ), h8]
    rw [hsplit] at hb
    linarith
  linarith

/-! ## Case 1's length, instantiated

The five fields cost `log₂(R^w·C) + a·(log₂ρ + 3) − b·log₂κ + 3`. The cancellation to watch:
field (3) costs `a·log₂(n'/v) = −a·log₂vn`, and `log₂φ` contributes `+a·log₂vn` — so `vn`
disappears from the total, leaving only `a·log₂ρ` and the `−b·log₂κ` that pays for the
contraction. -/

/-- The case-1 code with its widths instantiated. -/
noncomputable def case1Code' (𝓕 : Finset (Finset α)) (X U : Finset α) (v : ℕ) :
    Coding.Code (Case1Fields 𝓕 X U v) :=
  case1Code 𝓕 X U v (fun a => width (Dcands X U v a).card) (fun _ => card_le_two_pow_width _)
    (fun a D A => width (tau 𝓕 U A D a).card) (fun _ _ _ => card_le_two_pow_width _)

/-- **Case 1's length bound.** -/
theorem case1_length_le {A : Finset α} {a b : ℕ}
    (hS : S ∈ 𝓕) (hSX : S ⊆ X) (hV : V ∈ (X \ U).powersetCard v)
    (hAS : A ⊆ chi 𝓕 S U) (hAb : A.card = b)
    (hAb' : A.card = (chi 𝓕 S (U ∪ V)).card) (hSa : (chi 𝓕 S U).card = a)
    (hnot2 : ¬ Case2 𝓕 X U S V v w R ρ vn)
    (hR : 0 < R) (hρ : 0 < ρ) (hvn : vn = (v : ℝ) / (((X \ U).card : ℕ) : ℝ))
    (hv1 : 1 ≤ v) (hvX : v ≤ (X \ U).card) (hbw : b ≤ w) :
    ((a : ℝ) + 1) + ((width (Dcands X U v a).card : ℕ) : ℝ)
        + (((chi 𝓕 (jWitness 𝓕 U (V ∪ chi 𝓕 S U)) U).card : ℕ) : ℝ)
        + ((width (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℕ) : ℝ) + (a : ℝ)
      ≤ ((w : ℝ) * Real.logb 2 R
            + Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ))
          + (a : ℝ) * (Real.logb 2 ρ + 3)
          - (b : ℝ) * (Real.logb 2 R + Real.logb 2 vn) + 3 := by
  have hn'0 : 0 < (X \ U).card := lt_of_lt_of_le hv1 hvX
  have hn'R : (0 : ℝ) < (((X \ U).card : ℕ) : ℝ) := by exact_mod_cast hn'0
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hvnpos : 0 < vn := by rw [hvn]; positivity
  have hCpos : (0 : ℝ) < (((X \ U).card.choose v : ℕ) : ℝ) := by
    have : 0 < (X \ U).card.choose v := Nat.choose_pos hvX
    exact_mod_cast this
  obtain ⟨hVX, hVcard⟩ := Finset.mem_powersetCard.mp hV
  -- field (3): the candidates for `D`
  have hD1 : 1 ≤ (Dcands X U v a).card := by
    have := one_le_Dcands_card (𝓕 := 𝓕) (V := V) hS hSX hV
    rwa [hSa] at this
  have hDb : ((width (Dcands X U v a).card : ℕ) : ℝ)
      ≤ Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ) - (a : ℝ) * Real.logb 2 vn + 1 := by
    have hbound := card_Dcands_le (X := X) (U := U) hv1 hvX a
    have hb := width_le hD1 hbound
    have hsplit : Real.logb 2 (((((X \ U).card.choose v : ℕ)) : ℝ)
          * ((((X \ U).card : ℕ) : ℝ) / (v : ℝ)) ^ a)
        = Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ) - (a : ℝ) * Real.logb 2 vn := by
      rw [Real.logb_mul (ne_of_gt hCpos) (by positivity), Real.logb_pow, hvn,
        logb_inv_vn (n' := (X \ U).card) hv1 hn'0]
      ring
    rw [hsplit] at hb
    exact hb
  -- field (4): `|χ(j,U)| ≤ a`
  have hj : (((chi 𝓕 (jWitness 𝓕 U (V ∪ chi 𝓕 S U)) U).card : ℕ) : ℝ) ≤ (a : ℝ) := by
    have := jWitness_card_le (𝓕 := 𝓕) (U := U) (W := V) (S := S) hS
    rw [hSa] at this
    exact_mod_cast this
  -- field (5): the class, bounded by `φ` because we are not in case 2
  have hτ1 : 1 ≤ (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card := by
    have := one_le_tau_card (𝓕 := 𝓕) (U := U) (V := V) hS hAS
    rwa [hSa] at this
  have hτb : ((width (tau 𝓕 U A (V ∪ chi 𝓕 S U) a).card : ℕ) : ℝ)
      ≤ ((w : ℝ) * Real.logb 2 R + (a : ℝ) * (Real.logb 2 ρ + Real.logb 2 vn)
          - (b : ℝ) * (Real.logb 2 R + Real.logb 2 vn)) + 1 := by
    have hbound := tau_card_le_phi_of_not_case2 (X := X) (v := v) hAS hAb' hV hnot2
    rw [hSa, hAb] at hbound
    have hb := width_le hτ1 hbound
    rwa [logb_phi hR hρ hvnpos hbw] at hb
  linarith

/-! ## Rao's Lemma 4

Both branch bounds are now unconditional, so the contraction is too. -/

open scoped Classical in
/-- Rao's encoding with every width instantiated. -/
noncomputable def raoCode' (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ) (R ρ vn : ℝ)
    (hSX : ∀ T ∈ 𝓕, T ⊆ X) : Coding.Code {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v} :=
  raoCode (w := w) (R := R) (ρ := ρ) (vn := vn) hSX
    (fun a => width (Dcands X U v a).card) (fun _ => card_le_two_pow_width _)
    (fun a D A => width (tau 𝓕 U A D a).card) (fun _ _ _ => card_le_two_pow_width _)
    (width 𝓕.card) (card_le_two_pow_width _)
    (fun S A => width (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
      (phi R ρ vn w (chi 𝓕 S U).card A.card)).card) (fun _ _ => card_le_two_pow_width _)

/-- **Rao's Lemma 4**: one round of sampling contracts the summed residual by `2/3`. -/
theorem contraction (hu : IsUniform w 𝓕) (hsp : IsRaoSpread R w 𝓕)
    (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (hFle : ((𝓕.card : ℕ) : ℝ) ≤ R ^ w + 1) (hFge : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hR : 1 ≤ R) (hρ : 0 < ρ) (hvn : vn = (v : ℝ) / (((X \ U).card : ℕ) : ℝ))
    (hv1 : 1 ≤ v) (hvX : v ≤ (X \ U).card) (hwv : w ≤ v) (hwn : w < (X \ U).card)
    (h3 : (((X \ U).card : ℕ) : ℝ) ≤ 3 * ((((X \ U).card - w : ℕ)) : ℝ))
    (hRx : 1 ≤ R * ((v : ℝ) / (((X \ U).card : ℕ) : ℝ)))
    (hane : ∀ T ∈ 𝓕, 1 ≤ (chi 𝓕 T U).card)
    (hρ23 : 23 ≤ Real.logb 2 ρ)
    (hκ : Real.logb 2 R + Real.logb 2 vn = 2 * Real.logb 2 ρ - 1)
    (hne : (pairs 𝓕 X U v).Nonempty) :
    3 * ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 (U ∪ p.1)).card : ℝ)
      ≤ 2 * ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 U).card : ℝ) := by
  classical
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hn'0 : 0 < (X \ U).card := lt_of_lt_of_le hv1 hvX
  have hn'R : (0 : ℝ) < (((X \ U).card : ℕ) : ℝ) := by exact_mod_cast hn'0
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hvnpos : 0 < vn := by rw [hvn]; positivity
  have hCpos : (0 : ℝ) < (((X \ U).card.choose v : ℕ) : ℝ) := by
    have : 0 < (X \ U).card.choose v := Nat.choose_pos hvX
    exact_mod_cast this
  set C := raoCode' 𝓕 X U v w R ρ vn hSX with hC
  set N : ℝ := R ^ w * (((X \ U).card.choose v : ℕ) : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; positivity
  have hlogN : Real.logb 2 N
      = (w : ℝ) * Real.logb 2 R + Real.logb 2 ((((X \ U).card.choose v : ℕ)) : ℝ) := by
    rw [hNdef, Real.logb_mul (by positivity) (ne_of_gt hCpos), Real.logb_pow]
  -- the pair set is big enough
  have hcard : N ≤ ((pairs 𝓕 X U v).card : ℝ) := by
    have hpc : (pairs 𝓕 X U v).card = ((X \ U).card.choose v) * 𝓕.card := by
      rw [pairs, Finset.card_product, Finset.card_powersetCard]
    rw [hNdef, hpc]
    push_cast
    calc R ^ w * (((X \ U).card.choose v : ℕ) : ℝ)
        ≤ ((𝓕.card : ℕ) : ℝ) * (((X \ U).card.choose v : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hFge (le_of_lt hCpos)
      _ = (((X \ U).card.choose v : ℕ) : ℝ) * ((𝓕.card : ℕ) : ℝ) := by ring
  -- residuals: positive, and shrinking in `W`
  have ha : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      1 ≤ (chi 𝓕 p.1.2 U).card := fun p => hane _ (mem_pairs.mp p.2).2
  have hb : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      (chi 𝓕 p.1.2 (U ∪ p.1.1)).card ≤ (chi 𝓕 p.1.2 U).card := fun p =>
    chi_card_mono (mem_pairs.mp p.2).2 Finset.subset_union_left
  -- the per-pair length bound, branch by branch
  have hlen : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      ((C.enc p).length : ℝ)
        ≤ 1 + (Real.logb 2 N + ((chi 𝓕 p.1.2 U).card : ℝ) * (Real.logb 2 ρ + 3)
            - ((chi 𝓕 p.1.2 (U ∪ p.1.1)).card : ℝ) * (Real.logb 2 R + Real.logb 2 vn) + 3)
      ∨ ((C.enc p).length : ℝ)
        ≤ 1 + (Real.logb 2 N + ((chi 𝓕 p.1.2 U).card : ℝ)
            * (4 - Real.logb 2 ρ) + 3) := by
    intro p
    obtain ⟨hV, hS⟩ := mem_pairs.mp p.2
    set S := p.1.2 with hSdef
    set V := p.1.1 with hVdef
    have hSXm : S ⊆ X := hSX S hS
    have haw : (chi 𝓕 S U).card ≤ w := by
      calc (chi 𝓕 S U).card ≤ S.card := Finset.card_le_card (chi_subset hS)
        _ = w := hu hS
    have hbw : (chi 𝓕 S (U ∪ V)).card ≤ w :=
      le_trans (chi_card_mono hS Finset.subset_union_left) haw
    have hlength := Coding.Code.length_byCases (IsCase2 𝓕 X U v w R ρ vn)
      (branch1 hSX (fun a => width (Dcands X U v a).card) (fun _ => card_le_two_pow_width _)
        (fun a D A => width (tau 𝓕 U A D a).card) (fun _ _ _ => card_le_two_pow_width _))
      (branch2 (width 𝓕.card) (card_le_two_pow_width _)
        (fun S A => width (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
          (phi R ρ vn w (chi 𝓕 S U).card A.card)).card) (fun _ _ => card_le_two_pow_width _)) p
    by_cases hcase : IsCase2 𝓕 X U v w R ρ vn p
    · -- case 2
      refine Or.inr ?_
      rw [hC, raoCode', raoCode, hlength, dif_pos hcase]
      have hlen2 : ((branch2 (𝓕 := 𝓕) (X := X) (U := U) (v := v) (w := w) (R := R) (ρ := ρ)
          (vn := vn) (width 𝓕.card) (card_le_two_pow_width _)
          (fun S A => width (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
            (phi R ρ vn w (chi 𝓕 S U).card A.card)).card)
          (fun _ _ => card_le_two_pow_width _)).enc ⟨p, hcase⟩).length
          = width 𝓕.card + (chi 𝓕 S U).card
            + width (exceptional 𝓕 X U S (Classical.choose hcase) v (chi 𝓕 S U).card
                (phi R ρ vn w (chi 𝓕 S U).card (Classical.choose hcase).card)).card := by
        exact case2Code_length 𝓕 X U v w R ρ vn (width 𝓕.card) (card_le_two_pow_width _)
          (fun S A => width (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
            (phi R ρ vn w (chi 𝓕 S U).card A.card)).card) (fun _ _ => card_le_two_pow_width _)
          (case2Encode 𝓕 X U v w R ρ vn ⟨p.1, (mem_pairs.mp p.2).2, hcase⟩)
      rw [hlen2]
      obtain ⟨hAS, hAb, hAmem⟩ := Classical.choose_spec hcase
      push_cast
      have := case2Code'_length_le (V := V) (A := Classical.choose hcase)
        (a := (chi 𝓕 S U).card) (b := (Classical.choose hcase).card)
        hsp hSX hS hAS hFle (by omega) rfl rfl (hane S hS) hR hρ (le_trans haw hwv) hvX
        (lt_of_le_of_lt haw hwn) haw
        (by
          have hmono : ((((X \ U).card - w : ℕ)) : ℝ)
              ≤ ((((X \ U).card - (chi 𝓕 S U).card : ℕ)) : ℝ) := by
            have : ((X \ U).card - w : ℕ) ≤ ((X \ U).card - (chi 𝓕 S U).card : ℕ) := by omega
            exact_mod_cast this
          linarith)
        (by
          have hmono : ((((X \ U).card : ℕ)) : ℝ)
              ≥ ((((X \ U).card - (chi 𝓕 S U).card : ℕ)) : ℝ) := by
            have : ((X \ U).card - (chi 𝓕 S U).card : ℕ) ≤ (X \ U).card := by omega
            exact_mod_cast this
          have hden : (0 : ℝ) < ((((X \ U).card - (chi 𝓕 S U).card : ℕ)) : ℝ) := by
            have : 0 < ((X \ U).card - (chi 𝓕 S U).card : ℕ) := by omega
            exact_mod_cast this
          have hdiv : (v : ℝ) / (((X \ U).card : ℕ) : ℝ)
              ≤ (v : ℝ) / ((((X \ U).card - (chi 𝓕 S U).card : ℕ)) : ℝ) := by
            apply div_le_div_of_nonneg_left (le_of_lt hvR) hden hmono
          nlinarith [hRx, hdiv, hR0])
        hRx hAmem hvn (Or.inr (by rw [hAb]; exact chi_card_mono hS Finset.subset_union_left))
      rw [hlogN]
      linarith [this]
    · -- case 1
      refine Or.inl ?_
      rw [hC, raoCode', raoCode, hlength, dif_neg hcase]
      have hlen1 : ((branch1 (𝓕 := 𝓕) (X := X) (U := U) (v := v) (w := w) (R := R) (ρ := ρ)
          (vn := vn) hSX (fun a => width (Dcands X U v a).card)
          (fun _ => card_le_two_pow_width _)
          (fun a D A => width (tau 𝓕 U A D a).card)
          (fun _ _ _ => card_le_two_pow_width _)).enc ⟨p, hcase⟩).length
          = ((chi 𝓕 S U).card + 1) + width (Dcands X U v (chi 𝓕 S U).card).card
            + (chi 𝓕 (jWitness 𝓕 U (V ∪ chi 𝓕 S U)) U).card
            + width (tau 𝓕 U (Classical.choose
                (exists_A_field (𝓕 := 𝓕) (U := U) (V := V) (S := S) hS))
                (V ∪ chi 𝓕 S U) (chi 𝓕 S U).card).card
            + (chi 𝓕 S U).card := by
        exact case1PairCode_length 𝓕 X U v hSX (fun a => width (Dcands X U v a).card)
          (fun _ => card_le_two_pow_width _) (fun a D A => width (tau 𝓕 U A D a).card)
          (fun _ _ _ => card_le_two_pow_width _) ⟨p.1, p.2⟩
      rw [hlen1]
      obtain ⟨hAj, hAb, hAtau⟩ := Classical.choose_spec
        (exists_A_field (𝓕 := 𝓕) (U := U) (V := V) (S := S) hS)
      have hAS : Classical.choose
          (exists_A_field (𝓕 := 𝓕) (U := U) (V := V) (S := S) hS) ⊆ chi 𝓕 S U :=
        (mem_tau.mp hAtau).2.1
      push_cast
      have := case1_length_le (A := Classical.choose
          (exists_A_field (𝓕 := 𝓕) (U := U) (V := V) (S := S) hS))
        (a := (chi 𝓕 S U).card) (b := (chi 𝓕 S (U ∪ V)).card)
        hS hSXm hV hAS hAb hAb rfl hcase hR0 hρ hvn hv1 hvX hbw
      rw [hlogN]
      linarith [this]
  exact contraction_of_branch_bounds C hN hne hcard
    (fun p => raoCode_enc_ne_nil hSX _ _ _ _ _ _ _ _ p) ha hb
    (by rw [hκ]; linarith) (by rw [hκ]) hρ23 hκ hlen

end Rao

end Sunflower

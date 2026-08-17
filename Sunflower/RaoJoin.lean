/-
# Joining Rao's two cases

Both branches are now codes on pairs `(V,S)`: `case1PairCode` (five fields with the dependency
in formalization note R1 made explicit) and `case2PairCode` (three directly transcribed fields).
Rao's
"the first bit of the encoding is set to 0/1" is `Code.byCases`, and what comes out is a
single code on the pairs.

The point of having one code is `Coding.sum_le_of_code`: if every pair is encoded in

  `log₂(R^w·C(n−u,v)) + A·|χ(S,U)| − B·|χ(S,U∪V)|`

bits, then `B·∑|χ(S,U∪V)| ≤ A·∑|χ(S,U)|`, and `A/B ≤ 2/3` is the contraction. This file
builds the code and reduces the contraction to two per-branch length bounds; supplying those
bounds is the constant chase (`ρ`, `κ`), which is arithmetic on the widths already computed.

## The `a = 0` boundary

The target length has no constant term, while any encoding of a pair costs at least the tag
bit. So pairs with `|χ(S,U)| = 0` cannot be charged — there is nothing to charge them
against. They are harmless: `RaoChi.chi_eq_empty_congr` says that if one residual is empty
then all of them are, so either every pair has `a ≥ 1`, or `U` already covers a member and
both sides of the contraction are `0`. `contraction_of_lengths` therefore assumes `a ≥ 1` on
the pair set, and `chi_pos_or_all_covered` records the dichotomy that discharges it.
-/
import Sunflower.RaoCase2

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)} {X U : Finset α} {v w : ℕ}
variable {R ρ vn : ℝ}

/-- **The dichotomy at `a = 0`.** Either some member is already covered by `U` — in which case
every residual at `U` is empty and the contraction is trivial — or every member has a nonempty
residual. -/
theorem chi_pos_or_all_covered (𝓕 : Finset (Finset α)) (U : Finset α) :
    (∃ T ∈ 𝓕, T ⊆ U) ∨ ∀ S ∈ 𝓕, 0 < (chi 𝓕 S U).card := by
  classical
  by_cases h : ∃ T ∈ 𝓕, T ⊆ U
  · exact Or.inl h
  · refine Or.inr fun S hS => ?_
    rcases Nat.eq_zero_or_pos (chi 𝓕 S U).card with h0 | hpos
    · exact absurd ((chi_eq_empty_iff hS).mp (Finset.card_eq_zero.mp h0)) h
    · exact hpos

/-- If `U` already covers a member, every residual at `U` vanishes — so the sums on both sides
of the contraction are zero, whatever `V` is. -/
theorem chi_eq_empty_of_covered {S : Finset α} (hS : S ∈ 𝓕) (h : ∃ T ∈ 𝓕, T ⊆ U)
    (V : Finset α) : chi 𝓕 S (U ∪ V) = ∅ := by
  obtain ⟨T, hT, hTU⟩ := h
  exact (chi_eq_empty_iff hS).mpr ⟨T, hT, le_trans hTU Finset.subset_union_left⟩

/-! ## The joined code -/

/-- The pairs `(V,S)` the encoding ranges over. -/
noncomputable def pairs (𝓕 : Finset (Finset α)) (X U : Finset α) (v : ℕ) :
    Finset (Finset α × Finset α) :=
  ((X \ U).powersetCard v) ×ˢ 𝓕

lemma mem_pairs {p : Finset α × Finset α} :
    p ∈ pairs 𝓕 X U v ↔ p.1 ∈ (X \ U).powersetCard v ∧ p.2 ∈ 𝓕 := by
  rw [pairs, Finset.mem_product]

/-- Case 2 of the split, as a predicate on a pair of the index type. -/
def IsCase2 (𝓕 : Finset (Finset α)) (X U : Finset α) (v w : ℕ) (R ρ vn : ℝ)
    (p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}) : Prop :=
  Case2 𝓕 X U p.1.2 p.1.1 v w R ρ vn

/-- The case-1 branch, restricted to the pairs that are not in case 2. -/
noncomputable def branch1 (hSX : ∀ T ∈ 𝓕, T ⊆ X) (kD : ℕ → ℕ)
    (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A) :
    Coding.Code {p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v} //
      ¬ IsCase2 𝓕 X U v w R ρ vn p} :=
  (case1PairCode 𝓕 X U v hSX kD hD kt ht).comap (fun p => ⟨p.1.1, p.1.2⟩)
    (by
      intro p q hpq
      have h : p.1.1 = q.1.1 := congrArg Subtype.val hpq
      exact Subtype.ext (Subtype.ext h))

/-- The case-2 branch. -/
noncomputable def branch2 (kF : ℕ) (hF : 𝓕.card ≤ 2 ^ kF)
    (kE : Finset α → Finset α → ℕ)
    (hE : ∀ S A : Finset α, (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
        (phi R ρ vn w (chi 𝓕 S U).card A.card)).card ≤ 2 ^ kE S A) :
    Coding.Code {p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v} //
      IsCase2 𝓕 X U v w R ρ vn p} :=
  (case2PairCode 𝓕 X U v w R ρ vn kF hF kE hE).comap
    (fun p => ⟨p.1.1, (mem_pairs.mp p.1.2).2, p.2⟩)
    (by
      intro p q hpq
      have h := congrArg
        (fun z : {r : Finset α × Finset α // r.2 ∈ 𝓕 ∧ Case2 𝓕 X U r.2 r.1 v w R ρ vn} =>
          z.val) hpq
      exact Subtype.ext (Subtype.ext h))

open scoped Classical in
/-- **Rao's encoding**: the tag bit, then whichever branch applies. -/
noncomputable def raoCode (hSX : ∀ T ∈ 𝓕, T ⊆ X) (kD : ℕ → ℕ)
    (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A)
    (kF : ℕ) (hF : 𝓕.card ≤ 2 ^ kF) (kE : Finset α → Finset α → ℕ)
    (hE : ∀ S A : Finset α, (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
        (phi R ρ vn w (chi 𝓕 S U).card A.card)).card ≤ 2 ^ kE S A) :
    Coding.Code {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v} :=
  Coding.Code.byCases (IsCase2 𝓕 X U v w R ρ vn)
    (branch1 hSX kD hD kt ht) (branch2 kF hF kE hE)

/-- Codewords are nonempty: the tag bit alone guarantees it. -/
theorem raoCode_enc_ne_nil (hSX : ∀ T ∈ 𝓕, T ⊆ X) (kD : ℕ → ℕ)
    (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A)
    (kF : ℕ) (hF : 𝓕.card ≤ 2 ^ kF) (kE : Finset α → Finset α → ℕ)
    (hE : ∀ S A : Finset α, (exceptional 𝓕 X U S A v (chi 𝓕 S U).card
        (phi R ρ vn w (chi 𝓕 S U).card A.card)).card ≤ 2 ^ kE S A)
    (p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}) :
    (raoCode hSX kD hD kt ht kF hF kE hE).enc p ≠ [] := by
  classical
  exact Coding.Code.byCases_enc_ne_nil _ _ _ p

/-! ## From lengths to the contraction

`Coding.sum_le_of_code` does the rest: with `N = R^w·C(n−u,v)` objects and lengths
`log₂ N + A·a − B·b`, the sums satisfy `B·∑b ≤ A·∑a`. -/

/-- **The contraction, given the per-branch length bounds.** This is Rao's "applying Lemma 5,
we conclude … and so `E|χ(X,W)| ≤ (2/3)·E|χ(X,U)|`", with the two branches supplying the
hypothesis. -/
theorem contraction_of_lengths (C : Coding.Code {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v})
    {N A B : ℝ} (hN : 0 < N) (hne : (pairs 𝓕 X U v).Nonempty)
    (hcard : N ≤ ((pairs 𝓕 X U v).card : ℝ))
    (hnil : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}, C.enc p ≠ [])
    (hlen : ∀ p : {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v},
      ((C.enc p).length : ℝ)
        ≤ Real.logb 2 N + A * ((chi 𝓕 p.1.2 U).card : ℝ)
            - B * ((chi 𝓕 p.1.2 (U ∪ p.1.1)).card : ℝ)) :
    B * ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 (U ∪ p.1)).card : ℝ)
      ≤ A * ∑ p ∈ pairs 𝓕 X U v, ((chi 𝓕 p.2 U).card : ℝ) := by
  classical
  have hcardι : (Finset.univ : Finset {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}).card
      = (pairs 𝓕 X U v).card := by
    rw [Finset.card_univ, Fintype.card_coe]
  have huniv :
      (Finset.univ : Finset {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}).Nonempty := by
    rw [← Finset.card_pos, hcardι]
    exact Finset.card_pos.mpr hne
  have hsum : ∀ g : Finset α × Finset α → ℝ,
      ∑ p ∈ (Finset.univ : Finset {p : Finset α × Finset α // p ∈ pairs 𝓕 X U v}), g p.1
        = ∑ p ∈ pairs 𝓕 X U v, g p := by
    intro g
    rw [← Finset.sum_attach (pairs 𝓕 X U v) g]
    rfl
  have hmain := Coding.sum_le_of_code C huniv (A := A) (B := B)
    (f := fun p => ((chi 𝓕 p.1.2 U).card : ℝ))
    (g := fun p => ((chi 𝓕 p.1.2 (U ∪ p.1.1)).card : ℝ)) hN
    (by rw [hcardι]; exact hcard) (fun p _ => hnil p) (fun p _ => hlen p)
  rw [hsum (fun p => ((chi 𝓕 p.2 U).card : ℝ)),
    hsum (fun p => ((chi 𝓕 p.2 (U ∪ p.1)).card : ℝ))] at hmain
  exact hmain

end Rao

end Sunflower

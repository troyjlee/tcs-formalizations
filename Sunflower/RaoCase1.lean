/-
# Rao's case 1: the encoder

Case 1 of Rao's Lemma 4 (his p. 4–5) uses a case tag plus five payload fields:

  (1) `a = |χ(S,U)|`, in unary;
  (2) `D = V ∪ χ(S,U)`;
  (3) `A` — see below;
  (4) `S`, inside the class `τ(A,D,a)`;
  (5) `V ∩ χ(S,U)`.

`RaoJoin.Code.byCases` adds the case tag when the two branches are combined.

The `A` field contains the implicit dependency discussed in formalization note **R1**: Rao
encodes `χ(j,U) ∩ χ(S,U)` and *defines* `A` from it as the lex-first subset of size
`|χ(S,W)|` — but the width of the following field is `log φ + 1` and `φ` depends on `|χ(S,W)|`, which is
not yet available on the sequential reading used here. Transmitting `A` itself, as a subset of
`χ(j,U)`, fits the target budget and determines `|χ(S,W)| = |A|`.

This file builds that encoder. The three facts it needs first:

* `card_Dcands` — how many candidates field (3) has, exactly `∑_{i≤a} C(n−u, v+i)`, which
  `sum_choose_le_pow` then bounds;
* `union_sdiff_union_inter` — the decoding identity for field (6): `S` and `D` and `V ∩ χ(S,U)`
  put `V` back together;
* `jWitness_union_U` — `j` may be recomputed from `D` alone. Rao takes `j` to depend on
  `W ∪ χ(S,U)`, which mentions `U`; since residuals never meet `U`, dropping it changes
  nothing, and the decoder is not sent `U` twice.
-/
import Sunflower.RaoEncoding

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)} {S U V : Finset α}

/-! ## Residuals never meet `U` -/

lemma chi_disjoint_U : Disjoint (chi 𝓕 S U) U := Finset.sdiff_disjoint

lemma chi_subset_sdiff {X : Finset α} (hS : S ∈ 𝓕) (hSX : S ⊆ X) : chi 𝓕 S U ⊆ X \ U := by
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨hSX (chi_subset hS hx), ?_⟩
  exact Finset.disjoint_left.mp chi_disjoint_U hx

/-- Adjoining `U` to the encoded set changes no candidate for `j`: a residual `χ(T,U)` sits
inside `D ∪ U` exactly when it sits inside `D`. -/
lemma jCands_union_U (D : Finset α) : jCands 𝓕 U (D ∪ U) = jCands 𝓕 U D := by
  ext T
  simp only [mem_jCands]
  constructor
  · rintro ⟨hT, hsub⟩
    refine ⟨hT, fun x hx => ?_⟩
    rcases Finset.mem_union.mp (hsub hx) with h | h
    · exact h
    · exact absurd h (Finset.disjoint_left.mp chi_disjoint_U hx)
  · rintro ⟨hT, hsub⟩
    exact ⟨hT, le_trans hsub Finset.subset_union_left⟩

/-- Hence `j` itself is a function of `D` alone. -/
lemma jWitness_union_U (D : Finset α) :
    jWitness 𝓕 U (D ∪ U) = jWitness 𝓕 U D := by
  simp only [jWitness, jCands_union_U]

/-- …and so is Rao's `W ∪ χ(S,U)` version, since `W = U ∪ V`. -/
lemma union_assoc_U (D : Finset α) : (U ∪ V) ∪ D = (V ∪ D) ∪ U := by
  ext x
  simp only [Finset.mem_union]
  tauto

lemma jWitness_W :
    jWitness 𝓕 U ((U ∪ V) ∪ chi 𝓕 S U) = jWitness 𝓕 U (V ∪ chi 𝓕 S U) := by
  rw [union_assoc_U, jWitness_union_U]

/-! ## Field (3): the candidates, and how many -/

/-- The sets field (3) may hold: subsets of `X \ U` of size between `v` and `v + a`. The
decoder can enumerate these from `U`, `v` and the already-decoded `a`. -/
noncomputable def Dcands (X U : Finset α) (v a : ℕ) : Finset (Finset α) :=
  (X \ U).powerset.filter fun D => v ≤ D.card ∧ D.card ≤ v + a

lemma mem_Dcands {X U D : Finset α} {v a : ℕ} :
    D ∈ Dcands X U v a ↔ D ⊆ X \ U ∧ v ≤ D.card ∧ D.card ≤ v + a := by
  rw [Dcands, Finset.mem_filter, Finset.mem_powerset]

/-- **Exactly `∑_{i ≤ a} C(n−u, v+i)` candidates**, by splitting on the size. -/
theorem card_Dcands (X U : Finset α) (v a : ℕ) :
    (Dcands X U v a).card = ∑ i ∈ Finset.range (a + 1), ((X \ U).card).choose (v + i) := by
  classical
  have hsplit : Dcands X U v a
      = (Finset.range (a + 1)).biUnion fun i => (X \ U).powersetCard (v + i) := by
    ext D
    simp only [mem_Dcands, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hDX, hv, hva⟩
      exact ⟨D.card - v, by omega, hDX, by omega⟩
    · rintro ⟨i, hi, hDX, hcard⟩
      exact ⟨hDX, by omega, by omega⟩
  rw [hsplit, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ => Finset.card_powersetCard _ _
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun D hD hD' => ?_
    rw [Finset.mem_powersetCard] at hD hD'
    exact hij (by omega)

/-- The size bound field (3) is budgeted against. -/
theorem card_Dcands_le {X U : Finset α} {v : ℕ} (hv : 1 ≤ v) (hvX : v ≤ (X \ U).card) (a : ℕ) :
    ((Dcands X U v a).card : ℝ)
      ≤ (((X \ U).card.choose v : ℕ) : ℝ) * (((X \ U).card : ℝ) / v) ^ a := by
  rw [card_Dcands]
  push_cast
  exact sum_choose_le_pow hv hvX a

/-! ## Field (6): decoding `V`

`D` and `V ∩ χ(S,U)` determine `V`, once `S` — hence `χ(S,U)` — is known from field (5). -/

/-- `V = (D \ χ(S,U)) ∪ (V ∩ χ(S,U))` for `D = V ∪ χ(S,U)`: the decoding identity. -/
theorem union_sdiff_union_inter (V C : Finset α) : ((V ∪ C) \ C) ∪ (V ∩ C) = V := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- The membership facts field (3) needs: `D = V ∪ χ(S,U)` really is a candidate. -/
theorem mem_Dcands_of_pair {X : Finset α} {v : ℕ} (hS : S ∈ 𝓕) (hSX : S ⊆ X)
    (hV : V ⊆ X \ U) (hVcard : V.card = v) :
    V ∪ chi 𝓕 S U ∈ Dcands X U v (chi 𝓕 S U).card := by
  refine mem_Dcands.mpr ⟨Finset.union_subset hV (chi_subset_sdiff hS hSX), ?_, ?_⟩
  · rw [← hVcard]
    exact Finset.card_le_card Finset.subset_union_left
  · rw [← hVcard]
    exact le_trans (Finset.card_union_le _ _) le_rfl

/-- `τ`, like `jCands`, does not see `U`. -/
lemma tau_union_U (A D : Finset α) (a : ℕ) :
    tau 𝓕 U A (D ∪ U) a = tau 𝓕 U A D a := by
  ext T
  simp only [mem_tau]
  constructor
  · rintro ⟨hT, hA, hsub, hcard⟩
    refine ⟨hT, hA, fun x hx => ?_, hcard⟩
    rcases Finset.mem_union.mp (hsub hx) with h | h
    · exact h
    · exact absurd h (Finset.disjoint_left.mp chi_disjoint_U hx)
  · rintro ⟨hT, hA, hsub, hcard⟩
    exact ⟨hT, hA, le_trans hsub Finset.subset_union_left, hcard⟩

/-- Step (d), packaged in the form the encoder writes: `A` is a subset of `χ(j,U)` — where `j`
is computed from field (3) alone — of size exactly `|χ(S,W)|`, and `S` lies in the class it
names. This is the explicit field (4) used in formalization note R1. -/
theorem exists_A_field (hS : S ∈ 𝓕) :
    ∃ A : Finset α,
      A ⊆ chi 𝓕 (jWitness 𝓕 U (V ∪ chi 𝓕 S U)) U ∧
      A.card = (chi 𝓕 S (U ∪ V)).card ∧
      S ∈ tau 𝓕 U A (V ∪ chi 𝓕 S U) (chi 𝓕 S U).card := by
  obtain ⟨A, hAj, _hAS, hAcard, hAtau⟩ :=
    exists_A_for_encoding (W := U ∪ V) hS Finset.subset_union_left
  refine ⟨A, ?_, hAcard, ?_⟩
  · rwa [jWitness_W (𝓕 := 𝓕) (V := V) (S := S)] at hAj
  · rw [union_assoc_U, tau_union_U] at hAtau
    exact hAtau

/-! ## The encoder

The record type, the code, and — the content — the decoder, exhibited as an explicit left
inverse. Injectivity of the encoding is then immediate, and no dependent-equality reasoning is
needed anywhere. -/

variable (𝓕) (X U : Finset α) (v : ℕ)

/-- The record case 1 writes: `a`, then `D`, then `A ⊆ χ(j,U)` with `j` computed from `D`, then
`S` inside `τ(A,D,a)`, then `V ∩ χ(S,U)`. Each field's *type* — hence its width — depends only
on the fields before it. -/
abbrev Case1Fields : Type _ :=
  Σ a : ℕ, Σ D : {D // D ∈ Dcands X U v a},
    Σ A : {A // A ∈ (chi 𝓕 (jWitness 𝓕 U D.1) U).powerset},
      Σ S : {S // S ∈ tau 𝓕 U A.1 D.1 a}, {Y // Y ∈ (chi 𝓕 S.1 U).powerset}

/-- The case-1 code, given widths for the two "index into a set" fields. -/
noncomputable def case1Code (kD : ℕ → ℕ) (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A) :
    Coding.Code (Case1Fields 𝓕 X U v) :=
  Coding.Code.unaryCode.sigma fun a =>
    (Coding.Code.memCode (Dcands X U v a) (kD a) (hD a)).sigma fun D =>
      (Coding.Code.powersetCode (chi 𝓕 (jWitness 𝓕 U D.1) U)).sigma fun A =>
        (Coding.Code.memCode (tau 𝓕 U A.1 D.1 a) (kt a D.1 A.1) (ht a D.1 A.1)).sigma fun S =>
          Coding.Code.powersetCode (chi 𝓕 S.1 U)

/-- **The length is the sum of the field widths**, by construction. -/
theorem case1Code_length (kD : ℕ → ℕ) (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A) (p : Case1Fields 𝓕 X U v) :
    ((case1Code 𝓕 X U v kD hD kt ht).enc p).length
      = (p.1 + 1) + kD p.1 + (chi 𝓕 (jWitness 𝓕 U p.2.1.1) U).card
          + kt p.1 p.2.1.1 p.2.2.1.1 + (chi 𝓕 p.2.2.2.1.1 U).card := by
  rw [case1Code]
  rw [Coding.Code.length_sigma, Coding.Code.length_sigma, Coding.Code.length_sigma,
    Coding.Code.length_sigma, Coding.Code.length_unaryCode, Coding.Code.length_memCode,
    Coding.Code.length_powersetCode, Coding.Code.length_memCode,
    Coding.Code.length_powersetCode]
  ring

/-- **The decoder**: `S` is field (5); `V` is put back together from fields (3) and (6). -/
noncomputable def case1Decode (p : Case1Fields 𝓕 X U v) : Finset α × Finset α :=
  ((p.2.1.1 \ chi 𝓕 p.2.2.2.1.1 U) ∪ p.2.2.2.2.1, p.2.2.2.1.1)

/-- The encoder: the fields of a pair `(V,S)`. -/
noncomputable def case1Encode (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (p : {p : Finset α × Finset α // p ∈ ((X \ U).powersetCard v) ×ˢ 𝓕}) :
    Case1Fields 𝓕 X U v :=
  let V := p.1.1
  let S := p.1.2
  let hmem := Finset.mem_product.mp p.2
  let hV := Finset.mem_powersetCard.mp hmem.1
  let hS := hmem.2
  let A := Classical.choose (exists_A_field (𝓕 := 𝓕) (U := U) (V := V) (S := S) hS)
  let hA := Classical.choose_spec (exists_A_field (𝓕 := 𝓕) (U := U) (V := V) (S := S) hS)
  ⟨(chi 𝓕 S U).card,
   ⟨V ∪ chi 𝓕 S U, mem_Dcands_of_pair hS (hSX S hS) hV.1 hV.2⟩,
   ⟨A, Finset.mem_powerset.mpr hA.1⟩,
   ⟨S, hA.2.2⟩,
   ⟨V ∩ chi 𝓕 S U, Finset.mem_powerset.mpr Finset.inter_subset_right⟩⟩

/-- **The encoding decodes**, which is what makes it an encoding. -/
theorem case1Decode_encode (hSX : ∀ T ∈ 𝓕, T ⊆ X)
    (p : {p : Finset α × Finset α // p ∈ ((X \ U).powersetCard v) ×ˢ 𝓕}) :
    case1Decode 𝓕 X U v (case1Encode 𝓕 X U v hSX p) = p.1 := by
  rw [case1Decode, case1Encode]
  refine Prod.ext ?_ rfl
  exact union_sdiff_union_inter _ _

/-- Hence the encoder is injective, and `comap` turns the field code into a code on the pairs
themselves. -/
theorem case1Encode_injective (hSX : ∀ T ∈ 𝓕, T ⊆ X) :
    Function.Injective (case1Encode 𝓕 X U v hSX) := by
  intro p q hpq
  have h : case1Decode 𝓕 X U v (case1Encode 𝓕 X U v hSX p)
      = case1Decode 𝓕 X U v (case1Encode 𝓕 X U v hSX q) := by rw [hpq]
  rw [case1Decode_encode, case1Decode_encode] at h
  exact Subtype.ext h

/-- **The case-1 code on pairs `(V,S)`.** -/
noncomputable def case1PairCode (hSX : ∀ T ∈ 𝓕, T ⊆ X) (kD : ℕ → ℕ)
    (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A) :
    Coding.Code {p : Finset α × Finset α // p ∈ ((X \ U).powersetCard v) ×ˢ 𝓕} :=
  (case1Code 𝓕 X U v kD hD kt ht).comap (case1Encode 𝓕 X U v hSX)
    (case1Encode_injective 𝓕 X U v hSX)

/-- Its length, in terms of the pair: `(a+1) + k_D(a) + |χ(j,U)| + k_τ + |χ(S,U)|`, with
`|χ(j,U)| ≤ |χ(S,U)| = a`, so at most `2a + 1 + k_D(a) + k_τ + a`. -/
theorem case1PairCode_length (hSX : ∀ T ∈ 𝓕, T ⊆ X) (kD : ℕ → ℕ)
    (hD : ∀ a, (Dcands X U v a).card ≤ 2 ^ kD a)
    (kt : ℕ → Finset α → Finset α → ℕ)
    (ht : ∀ a D A, (tau 𝓕 U A D a).card ≤ 2 ^ kt a D A)
    (p : {p : Finset α × Finset α // p ∈ ((X \ U).powersetCard v) ×ˢ 𝓕}) :
    (((case1PairCode 𝓕 X U v hSX kD hD kt ht).enc p).length)
      = ((chi 𝓕 p.1.2 U).card + 1) + kD (chi 𝓕 p.1.2 U).card
          + (chi 𝓕 (jWitness 𝓕 U (p.1.1 ∪ chi 𝓕 p.1.2 U)) U).card
          + kt (chi 𝓕 p.1.2 U).card (p.1.1 ∪ chi 𝓕 p.1.2 U)
              (Classical.choose (exists_A_field (𝓕 := 𝓕) (U := U) (V := p.1.1) (S := p.1.2)
                (Finset.mem_product.mp p.2).2))
          + (chi 𝓕 p.1.2 U).card := by
  rw [case1PairCode, Coding.Code.length_comap, case1Code_length]
  rfl

end Rao

end Sunflower

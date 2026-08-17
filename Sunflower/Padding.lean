/-
# Uniformization by private dummy elements

Both `Sunflower.erdos_rado` and `Sunflower.alwz` are proved for *`w`-uniform* families —
every member has cardinality exactly `w`. ALWZ state their theorems for **`w`-set systems**:

> "We call `F` a `w`-set system if each set in `F` has size at most `w`." (§1)

and both their Lemma 1.2 (Erdős–Rado) and their Theorem 1.4 (the main theorem) carry that
hypothesis, in *every* arXiv version. Uniformity enters only in the proof — arXiv v2 changed
the *robust*-sunflower theorem (1.9) to "`w`-uniform set system" — and is bridged by one
sentence of §1, which v2 also added:

> "Any `w`-set system can be turned into a `w`-uniform system by adding `w − |S|` distinct
> dummy elements to the sets `S` of the system with `|S| < w` so that no dummy element
> appears in more than one set."

This file supplies exactly that construction, so that the paper's own "at most `w`"
statement is exported rather than assumed away. The padded universe is

  `Padded α := α ⊕ (Finset α × ℕ)`,

and `S` is padded with the `w - |S|` dummies `(S, 0), …, (S, w - |S| - 1)` — tagged by `S`
itself, hence **private to `S`**: distinct members receive disjoint dummy sets. Privacy is
what makes the reduction faithful in both directions (`pad_inter`): for `S ≠ T`,

  `pad w S ∩ pad w T = (S ∩ T).image Sum.inl`,

so intersections — and therefore sunflower cores — are transported exactly.

**Scope note.** This is the §1 *set-system* padding, and it is elementary: the family is a
`Finset (Finset α)`, so distinct members are distinct sets, and tagging each dummy by the
member it belongs to already realizes "no dummy element appears in more than one set".

It is **not** the second, superficially similar padding sentence discussed in formalization
note A3 (`SUNFLOWER_FORMALIZATION_NOTES.md`) — the one inside ALWZ's Lemma 2.10 ("we may also
assume that all sets in `F′` have size exactly `w`, by adding different dummy elements … we
take care to scale by a large enough factor so that a negligible amount of weight falls on
each dummy element, and so the spreadness hypothesis is preserved"). That one pads a
*weighted multiset* system and must preserve *spreadness*; it is load-bearing and its
justification is unstated. The formalization avoids it entirely by restricting to the
heaviest size class (`SpreadBottom.bottom_le`). What is padded here is only the top-level
statement, where nothing but cardinalities and intersections has to survive — and both are
preserved exactly (`card_padFamily`, `pad_inter`).
-/
import Sunflower.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## The padded universe -/

/-- The ground set used to uniformize a `w`-set system over `α`: the original points, plus
one private dummy `(S, i)` for each set `S` and index `i`. Same universe as `α`, so the
uniform theorems apply verbatim. -/
abbrev Padded (α : Type*) := α ⊕ (Finset α × ℕ)

/-- The dummies assigned to `S` when padding to width `w`: the `w - |S|` points
`(S, 0), …, (S, w - |S| - 1)`. Tagging by `S` makes them private to `S`. -/
def dummies (w : ℕ) (S : Finset α) : Finset (Padded α) :=
  (range (w - S.card)).image fun i => Sum.inr (S, i)

/-- `S` padded to width `w`: `S` itself, together with its private dummies. -/
def pad (w : ℕ) (S : Finset α) : Finset (Padded α) :=
  S.image Sum.inl ∪ dummies w S

/-- Undo padding: keep the original points, discard the dummies. -/
def unpad (T : Finset (Padded α)) : Finset α :=
  T.biUnion (Sum.elim (fun a => {a}) fun _ => ∅)

/-- A `w`-set system padded to a `w`-uniform one. -/
def padFamily (w : ℕ) (𝓕 : Finset (Finset α)) : Finset (Finset (Padded α)) :=
  𝓕.image (pad w)

/-! ## Membership -/

@[simp] lemma inr_mem_dummies {w : ℕ} {S U : Finset α} {i : ℕ} :
    (Sum.inr (U, i) : Padded α) ∈ dummies w S ↔ U = S ∧ i < w - S.card := by
  simp only [dummies, mem_image, mem_range, Sum.inr.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨rfl, hj⟩
  · rintro ⟨rfl, hi⟩; exact ⟨i, hi, rfl, rfl⟩

@[simp] lemma inl_notMem_dummies {w : ℕ} {S : Finset α} {a : α} :
    (Sum.inl a : Padded α) ∉ dummies w S := by
  simp [dummies]

@[simp] lemma inl_mem_pad {w : ℕ} {S : Finset α} {a : α} :
    (Sum.inl a : Padded α) ∈ pad w S ↔ a ∈ S := by
  simp [pad]

@[simp] lemma inr_mem_pad {w : ℕ} {S U : Finset α} {i : ℕ} :
    (Sum.inr (U, i) : Padded α) ∈ pad w S ↔ U = S ∧ i < w - S.card := by
  simp [pad]

@[simp] lemma mem_unpad {T : Finset (Padded α)} {a : α} :
    a ∈ unpad T ↔ (Sum.inl a : Padded α) ∈ T := by
  simp only [unpad, mem_biUnion]
  constructor
  · rintro ⟨x, hx, hax⟩
    cases x with
    | inl b => rw [Sum.elim_inl, mem_singleton] at hax; exact hax ▸ hx
    | inr p => simp at hax
  · exact fun h => ⟨Sum.inl a, h, by simp⟩

/-! ## Padding is a bijection onto its image, preserving size and intersections -/

lemma card_dummies (w : ℕ) (S : Finset α) : (dummies w S).card = w - S.card :=
  (card_image_of_injective _ fun _ _ h => by simpa using h).trans (card_range _)

/-- Padding to width `w` makes every set of size at most `w` have size exactly `w`. -/
lemma card_pad {w : ℕ} {S : Finset α} (h : S.card ≤ w) : (pad w S).card = w := by
  have hd : Disjoint (S.image Sum.inl) (dummies w S) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    obtain ⟨a, -, rfl⟩ := mem_image.mp hx
    exact inl_notMem_dummies hx'
  rw [pad, card_union_of_disjoint hd, card_image_of_injective _ Sum.inl_injective,
    card_dummies]
  omega

@[simp] lemma unpad_pad (w : ℕ) (S : Finset α) : unpad (pad w S) = S := by
  ext a; simp

/-- `unpad` commutes with intersection: it is a preimage. -/
lemma unpad_inter (T₁ T₂ : Finset (Padded α)) :
    unpad (T₁ ∩ T₂) = unpad T₁ ∩ unpad T₂ := by
  ext a; simp

lemma pad_injective (w : ℕ) : Function.Injective (pad w (α := α)) :=
  Function.LeftInverse.injective (unpad_pad w)

/-- **Privacy of the dummies.** Distinct sets share no dummy, so padding transports
intersections exactly. This is what makes the reduction faithful in both directions. -/
lemma pad_inter {w : ℕ} {S T : Finset α} (h : S ≠ T) :
    pad w S ∩ pad w T = (S ∩ T).image Sum.inl := by
  ext x
  cases x with
  | inl a => simp
  | inr p =>
    obtain ⟨U, i⟩ := p
    -- no dummy is an original point, and `(U, i)` cannot be private to both `S` and `T`
    refine iff_of_false (fun hx => ?_) (by simp)
    rw [mem_inter, inr_mem_pad, inr_mem_pad] at hx
    exact h (hx.1.1.symm.trans hx.2.1)

/-! ## The padded family -/

@[simp] lemma mem_padFamily {w : ℕ} {𝓕 : Finset (Finset α)} {T : Finset (Padded α)} :
    T ∈ padFamily w 𝓕 ↔ ∃ S ∈ 𝓕, pad w S = T := by
  simp [padFamily]

@[simp] lemma card_padFamily (w : ℕ) (𝓕 : Finset (Finset α)) :
    (padFamily w 𝓕).card = 𝓕.card :=
  card_image_of_injective _ (pad_injective w)

/-- Padding a `w`-set system yields a `w`-uniform family. -/
lemma isUniform_padFamily {w : ℕ} {𝓕 : Finset (Finset α)} (h : IsBounded w 𝓕) :
    IsUniform w (padFamily w 𝓕) := by
  rintro T hT
  obtain ⟨S, hS, rfl⟩ := mem_padFamily.mp hT
  exact card_pad (h hS)

/-- If `T` is in the padded family, `unpad T` is in the original one. -/
lemma unpad_mem_of_mem_padFamily {w : ℕ} {𝓕 : Finset (Finset α)} {T : Finset (Padded α)}
    (hT : T ∈ padFamily w 𝓕) : unpad T ∈ 𝓕 := by
  obtain ⟨S, hS, rfl⟩ := mem_padFamily.mp hT
  rwa [unpad_pad]

/-- `unpad` is injective on the padded family: it inverts `pad` there. -/
lemma unpad_injOn_padFamily {w : ℕ} {𝓕 : Finset (Finset α)} :
    Set.InjOn unpad (padFamily w 𝓕 : Set (Finset (Padded α))) := by
  intro T₁ h₁ T₂ h₂ h
  obtain ⟨S₁, -, rfl⟩ := mem_padFamily.mp (mem_coe.mp h₁)
  obtain ⟨S₂, -, rfl⟩ := mem_padFamily.mp (mem_coe.mp h₂)
  rw [unpad_pad, unpad_pad] at h
  exact h ▸ rfl

/-! ## Transfer of sunflowers -/

/-- **Pullback.** A sunflower in the padded family is a sunflower in the original one:
`unpad` is injective there and commutes with intersections, so the core `K` pulls back to
`unpad K`. -/
theorem hasSunflower_of_padFamily {r w : ℕ} {𝓕 : Finset (Finset α)}
    (h : HasSunflower r (padFamily w 𝓕)) : HasSunflower r 𝓕 := by
  obtain ⟨𝒮', hsub, hcard, K, hK⟩ := h
  refine ⟨𝒮'.image unpad, ?_, ?_, unpad K, ?_⟩
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
    exact unpad_mem_of_mem_padFamily (hsub hT)
  · rw [card_image_of_injOn (unpad_injOn_padFamily.mono (by exact_mod_cast hsub)), hcard]
  · intro S hS T hT hne
    obtain ⟨S', hS', rfl⟩ := mem_image.mp hS
    obtain ⟨T', hT', rfl⟩ := mem_image.mp hT
    rw [← unpad_inter, hK hS' hT' (fun h => hne (h ▸ rfl))]

/-- **Pushforward.** A sunflower in the original family is a sunflower in the padded one,
with core `K` padded by inclusion. This direction is where *privacy* of the dummies is
needed (`pad_inter`): shared dummies would inflate the intersections. -/
theorem hasSunflower_padFamily {r w : ℕ} {𝓕 : Finset (Finset α)}
    (h : HasSunflower r 𝓕) : HasSunflower r (padFamily w 𝓕) := by
  obtain ⟨𝒮, hsub, hcard, K, hK⟩ := h
  refine ⟨𝒮.image (pad w), image_subset_image hsub, ?_, K.image Sum.inl, ?_⟩
  · rw [card_image_of_injective _ (pad_injective w), hcard]
  · intro S hS T hT hne
    obtain ⟨S', hS', rfl⟩ := mem_image.mp hS
    obtain ⟨T', hT', rfl⟩ := mem_image.mp hT
    have hne' : S' ≠ T' := fun h => hne (h ▸ rfl)
    rw [pad_inter hne', hK hS' hT' hne']

/-- The padding reduction is **faithful**: `𝓕` contains an `r`-sunflower iff its padding
does. Together with `card_padFamily` and `isUniform_padFamily` this is the whole content of
the paper's "we may assume all sets have size exactly `w`". -/
theorem hasSunflower_padFamily_iff {r w : ℕ} {𝓕 : Finset (Finset α)} :
    HasSunflower r (padFamily w 𝓕) ↔ HasSunflower r 𝓕 :=
  ⟨hasSunflower_of_padFamily, hasSunflower_padFamily⟩

/-- **The uniform-to-bounded transfer.** Any sunflower theorem of the shape "a `w`-uniform
family whose cardinality satisfies `P` contains an `r`-sunflower" upgrades, *with no loss in
the size requirement `P`*, to the same statement for `w`-set systems: padding changes
neither the width nor the number of members. Both `erdos_rado_bounded` and `alwz_bounded`
are instances. -/
theorem hasSunflower_of_bounded {r w : ℕ} {P : ℕ → Prop} {𝓕 : Finset (Finset α)}
    (huniform : ∀ {𝓖 : Finset (Finset (Padded α))}, IsUniform w 𝓖 → P 𝓖.card →
      HasSunflower r 𝓖)
    (hb : IsBounded w 𝓕) (hcard : P 𝓕.card) : HasSunflower r 𝓕 :=
  hasSunflower_of_padFamily
    (huniform (isUniform_padFamily hb) (by rwa [card_padFamily]))

end Sunflower

/-
# Sunflowers: definitions

A **sunflower** with `r` petals is a family of `r` sets whose pairwise intersections all
coincide with the intersection of the whole family. The common intersection is the *core*;
the set differences are the *petals*.

Mathlib has no notion of a sunflower — not even the definition — so this file supplies one.
(The classical Erdős–Rado lemma *is* formalized in Isabelle/HOL's AFP, by René Thiemann,
2021; nothing about sunflowers exists in Lean.)

This development targets, in three stages:

1. `Sunflower.ErdosRado` — the classical bound: a `w`-uniform family with more than
   `(r-1)^w * w!` sets contains an `r`-sunflower (Erdős–Rado, 1960).
2. `Sunflower.Spread` — the *robust sunflower* / *spread* framework of Alweiss, Lovett, Wu
   and Zhang, which is also the machinery Frankston–Kahn–Narayanan–Park reused for
   Talagrand's conjecture.
3. `Sunflower.ALWZ` — the improved bound `(C r³ log w log log w)^w`
   (Alweiss–Lovett–Wu–Zhang, STOC 2020 / *Annals of Mathematics* 194 (2021) 795–815).

**Why base-1.9 logarithms** (see `Sunflower.ALWZ`): under a literal base-2 reading of the
pre-v3 statement, `log₂ log₂ 2 = 0` makes the required family size `0` at `w = 2` — asserting
that every nonempty family of 2-element sets contains an `r`-sunflower. ArXiv v3 explicitly
interprets `log` as base `1.9` for this boundary case, and we follow that convention. It gives
the positivity needed by the subsequent divisions and inequalities. See
`docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- `IsSunflowerWith 𝒮 K` : the family `𝒮` is a sunflower with core `K`, i.e. any two
distinct members meet exactly in `K`. -/
def IsSunflowerWith (𝒮 : Finset (Finset α)) (K : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒮 → ∀ ⦃T⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = K

/-- `IsSunflower r 𝒮` : `𝒮` is a sunflower with `r` petals. -/
def IsSunflower (r : ℕ) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧ ∃ K, IsSunflowerWith 𝒮 K

/-- A family `𝓕` *contains* an `r`-sunflower. This is the conclusion of every sunflower
theorem. -/
def HasSunflower (r : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∃ 𝒮 ⊆ 𝓕, IsSunflower r 𝒮

/-- A `w`-uniform family: every member has exactly `w` elements. Erdős–Rado and ALWZ are
both stated for uniform families; ALWZ made the uniformity hypothesis explicit only in its
second arXiv version. -/
def IsUniform (w : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝓕 → S.card = w

/-- A **`w`-set system**: every member has *at most* `w` elements. ALWZ's own definition
("each set in `F` has size at most `w`"), and the hypothesis of both their Lemma 1.2
(Erdős–Rado) and their Theorem 1.4. The uniform version is what the proofs establish;
`Sunflower.Padding` bridges the two by the paper's private-dummy padding. -/
def IsBounded (w : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝓕 → S.card ≤ w

/-! ## Basic facts -/

omit [DecidableEq α] in
/-- A `w`-uniform family is a `w`-set system. -/
theorem IsUniform.isBounded {w : ℕ} {𝓕 : Finset (Finset α)} (h : IsUniform w 𝓕) :
    IsBounded w 𝓕 := fun _ hS => (h hS).le

omit [DecidableEq α] in
/-- `w`-set systems are monotone in `w`. -/
theorem IsBounded.mono {w w' : ℕ} {𝓕 : Finset (Finset α)} (h : IsBounded w 𝓕)
    (hw : w ≤ w') : IsBounded w' 𝓕 := fun _ hS => (h hS).trans hw

omit [DecidableEq α] in
/-- A subfamily of a `w`-set system is a `w`-set system. -/
theorem IsBounded.subset {w : ℕ} {𝓕 𝓖 : Finset (Finset α)} (h : IsBounded w 𝓖)
    (hsub : 𝓕 ⊆ 𝓖) : IsBounded w 𝓕 := fun _ hS => h (hsub hS)

/-- Any family of at most one set is vacuously a sunflower, with any core. -/
theorem isSunflowerWith_of_card_le_one {𝒮 : Finset (Finset α)} (h : 𝒮.card ≤ 1)
    (K : Finset α) : IsSunflowerWith 𝒮 K := by
  intro S hS T hT hne
  exact absurd (Finset.card_le_one.mp h S hS T hT) hne

/-- A pairwise disjoint family is a sunflower with empty core. -/
theorem isSunflowerWith_empty_of_pairwiseDisjoint {𝒮 : Finset (Finset α)}
    (h : (𝒮 : Set (Finset α)).PairwiseDisjoint id) : IsSunflowerWith 𝒮 ∅ := by
  intro S hS T hT hne
  exact Finset.disjoint_iff_inter_eq_empty.mp (h hS hT hne)

/-- In a sunflower with at least two members, the core is forced: it is the intersection of
any two distinct members, hence determined by the family. -/
theorem IsSunflowerWith.core_unique {𝒮 : Finset (Finset α)} {K K' : Finset α}
    (hK : IsSunflowerWith 𝒮 K) (hK' : IsSunflowerWith 𝒮 K') (h2 : 2 ≤ 𝒮.card) :
    K = K' := by
  obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp h2
  rw [← hK hS hT hne, ← hK' hS hT hne]

/-- The core is contained in every member of a sunflower with at least two members. -/
theorem IsSunflowerWith.core_subset {𝒮 : Finset (Finset α)} {K : Finset α}
    (hK : IsSunflowerWith 𝒮 K) (h2 : 2 ≤ 𝒮.card) {S : Finset α} (hS : S ∈ 𝒮) :
    K ⊆ S := by
  obtain ⟨A, hA, B, hB, hne⟩ := Finset.one_lt_card.mp h2
  by_cases hSA : S = A
  · subst hSA
    rw [← hK hS hB (fun h => hne (h ▸ rfl) )]
    exact Finset.inter_subset_left
  · rw [← hK hS hA (fun h => hSA h)]
    exact Finset.inter_subset_left

/-- Petals are pairwise disjoint: outside the core, distinct members share nothing. -/
theorem IsSunflowerWith.petals_disjoint {𝒮 : Finset (Finset α)} {K : Finset α}
    (hK : IsSunflowerWith 𝒮 K) {S T : Finset α} (hS : S ∈ 𝒮) (hT : T ∈ 𝒮) (hne : S ≠ T) :
    Disjoint (S \ K) (T \ K) := by
  rw [Finset.disjoint_left]
  intro a haS haT
  rw [Finset.mem_sdiff] at haS haT
  exact haS.2 (hK hS hT hne ▸ Finset.mem_inter.mpr ⟨haS.1, haT.1⟩)

/-- A subfamily of a sunflower is a sunflower with the same core. -/
theorem IsSunflowerWith.subset {𝒮 𝒯 : Finset (Finset α)} {K : Finset α}
    (hK : IsSunflowerWith 𝒮 K) (h : 𝒯 ⊆ 𝒮) : IsSunflowerWith 𝒯 K :=
  fun _ hS _ hT hne => hK (h hS) (h hT) hne

/-- Monotonicity in the family: a larger family still contains any sunflower a subfamily
contains. -/
theorem HasSunflower.mono {r : ℕ} {𝓕 𝓖 : Finset (Finset α)} (h : 𝓕 ⊆ 𝓖)
    (hs : HasSunflower r 𝓕) : HasSunflower r 𝓖 := by
  obtain ⟨𝒮, h𝒮, hsun⟩ := hs
  exact ⟨𝒮, h𝒮.trans h, hsun⟩

end Sunflower

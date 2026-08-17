/-
# Towards Theorem 1.9 on the Rao route

`RaoSatisfying.rao_isSatisfying` says an absolutely `R`-spread family is satisfying. To get a
*robust sunflower* out of an arbitrary large family, one first has to find a core whose link is
absolutely spread — the structured/pseudorandom dichotomy, in the absolute rather than the
normalized sense.

`Spread.exists_spread_link` does this for ALWZ's normalized `IsSpread`. Rao's condition is
absolute (`RaoSpread`), so the extraction is different: take a core `Z` of **maximum size**
among those whose link is still large in absolute terms. Maximality is then exactly absolute
spreadness of that link — every proper extension has a link that fell below the threshold,
which is the bound `IsRaoSpread` asks for.

The boundary case is the one ALWZ handle with a parenthetical ("we cannot have `|K| = w`, as
otherwise `|F_K| = 1 < κ^{−w}|F|`): an extension reaching width `w` has a link of size at most
one, and `R^0 = 1`, so it is covered without appealing to maximality at all.
-/
import Sunflower.RaoSatisfying

open Finset

set_option maxHeartbeats 1600000

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α]

/-- The link of a link is the link at the union: `(𝓕_Z)_Y = 𝓕_{Z ∪ Y}`. -/
theorem link_link {𝓕 : Finset (Finset α)} {Z Y : Finset α} (hYZ : Disjoint Y Z) :
    link (link 𝓕 Z) Y = link 𝓕 (Z ∪ Y) := by
  classical
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ, hYQ, rfl⟩ := mem_link.mp hP
    obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hQ
    refine mem_link.mpr ⟨S, hS, Finset.union_subset hZS (le_trans hYQ Finset.sdiff_subset), ?_⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  · intro hP
    obtain ⟨S, hS, hZY, rfl⟩ := mem_link.mp hP
    refine mem_link.mpr ⟨S \ Z,
      mem_link.mpr ⟨S, hS, le_trans Finset.subset_union_left hZY, rfl⟩, ?_, ?_⟩
    · intro x hx
      exact Finset.mem_sdiff.mpr ⟨hZY (Finset.mem_union_right _ hx),
        Finset.disjoint_left.mp hYZ hx⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto

/-- A link at a core meeting `Z` is empty: members of `𝓕_Z` avoid `Z`. -/
theorem link_link_eq_empty {𝓕 : Finset (Finset α)} {Z Y : Finset α} (h : ¬ Disjoint Y Z) :
    link (link 𝓕 Z) Y = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  obtain ⟨Q, hQ, hYQ, -⟩ := mem_link.mp hP
  obtain ⟨S, -, -, rfl⟩ := mem_link.mp hQ
  refine h ?_
  refine Finset.disjoint_left.mpr fun x hxY hxZ => ?_
  exact (Finset.mem_sdiff.mp (hYQ hxY)).2 hxZ

/-- **The absolute-spread dichotomy.** A family with at least `R^w` members has a core `Z` of
size `< w` whose link is still large — at least `R^{w−|Z|}` — and is absolutely `R`-spread at
width `w − |Z|`.

Take `Z` of maximum size among the cores whose link is large. Every extension `Z ∪ Y` either
reaches width `w`, where the link has size at most one, or fails the largeness test by
maximality; both give the bound `IsRaoSpread` wants. -/
theorem exists_rao_spread_link {X : Finset α} {𝓕 : Finset (Finset α)} {w : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (hw : 1 ≤ w) (hu : IsUniform w 𝓕) (hSX : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : R ^ w ≤ ((𝓕.card : ℕ) : ℝ)) :
    ∃ Z ⊆ X, Z.card < w ∧ R ^ (w - Z.card) ≤ (((link 𝓕 Z).card : ℕ) : ℝ)
      ∧ IsRaoSpread R (w - Z.card) (link 𝓕 Z) := by
  classical
  set G : Finset (Finset α) := X.powerset.filter
    (fun Z => Z.card < w ∧ R ^ (w - Z.card) ≤ (((link 𝓕 Z).card : ℕ) : ℝ)) with hG
  have hmemG : ∀ Z, Z ∈ G ↔ Z ⊆ X ∧ Z.card < w ∧ R ^ (w - Z.card)
      ≤ (((link 𝓕 Z).card : ℕ) : ℝ) := by
    intro Z
    rw [hG, Finset.mem_filter, Finset.mem_powerset]
  have hGne : G.Nonempty := by
    refine ⟨∅, (hmemG ∅).mpr ⟨Finset.empty_subset _, ?_, ?_⟩⟩
    · rw [Finset.card_empty]; omega
    · rw [Finset.card_empty, Nat.sub_zero, link_empty]
      exact hcard
  obtain ⟨Z, hZG, hZmax⟩ := Finset.exists_max_image G Finset.card hGne
  obtain ⟨hZX, hZw, hZlarge⟩ := (hmemG Z).mp hZG
  refine ⟨Z, hZX, hZw, hZlarge, ?_⟩
  intro Y hYne
  by_cases hdisj : Disjoint Y Z
  · rw [link_link hdisj]
    have hcardZY : (Z ∪ Y).card = Z.card + Y.card := by
      have hdz : Disjoint Z Y := Finset.disjoint_left.mpr fun x hxZ hxY =>
        Finset.disjoint_left.mp hdisj hxY hxZ
      rw [Finset.card_union_of_disjoint hdz]
    by_cases hYlink : (link 𝓕 (Z ∪ Y)).Nonempty
    · obtain ⟨P, hP⟩ := hYlink
      obtain ⟨S, hS, hZYS, -⟩ := mem_link.mp hP
      have hZYX : Z ∪ Y ⊆ X := le_trans hZYS (hSX S hS)
      by_cases hbig : w ≤ (Z ∪ Y).card
      · -- the extension reaches width `w`: at most one member sits above it
        have h1 : ((link 𝓕 (Z ∪ Y)).card : ℕ) ≤ 1 := card_link_le_one hu hbig
        have h2 : (((link 𝓕 (Z ∪ Y)).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
        have h3 : w - Z.card - Y.card = 0 := by omega
        rw [h3, pow_zero]
        exact h2
      · -- otherwise maximality of `Z` applies
        push Not at hbig
        have hnot : ¬ (R ^ (w - (Z ∪ Y).card) ≤ (((link 𝓕 (Z ∪ Y)).card : ℕ) : ℝ)) := by
          intro hle
          have hmem : Z ∪ Y ∈ G := (hmemG _).mpr ⟨hZYX, hbig, hle⟩
          have hle' := hZmax _ hmem
          have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
          omega
        push Not at hnot
        have heq : w - Z.card - Y.card = w - (Z ∪ Y).card := by omega
        rw [heq]
        exact le_of_lt hnot
    · -- no member sits above the extension at all
      rw [Finset.not_nonempty_iff_eq_empty] at hYlink
      rw [hYlink]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  · -- `Y` meets `Z`, so the link is empty
    rw [link_link_eq_empty hdisj]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-! ## From a satisfying link to a robust sunflower

The last two steps of the route. Both pieces already exist — `isSpread_of_isRaoSpread` turns
Rao's absolute condition into ALWZ's normalized one, and
`isRobustSunflower_above_spread_core` is the assembly — so what remains is to check the side
conditions the extraction supplies: the link is nonempty (its size is at least `R^{w−|Z|} ≥ 1`)
and `Z` itself is not a member (it is too small, by `|Z| < w` and uniformity). -/

/-- The extracted link is nonempty. -/
theorem link_nonempty_of_large {𝓕 : Finset (Finset α)} {Z : Finset α} {w : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (h : R ^ (w - Z.card) ≤ (((link 𝓕 Z).card : ℕ) : ℝ)) :
    (link 𝓕 Z).Nonempty := by
  rw [← Finset.card_pos]
  have h1 : (1 : ℝ) ≤ R ^ (w - Z.card) := one_le_pow₀ hR
  have h2 : (1 : ℝ) ≤ (((link 𝓕 Z).card : ℕ) : ℝ) := le_trans h1 h
  have : 1 ≤ (link 𝓕 Z).card := by exact_mod_cast h2
  omega

omit [DecidableEq α] in
/-- A core smaller than the uniform width is not itself a member. -/
theorem notMem_of_card_lt {𝓕 : Finset (Finset α)} {Z : Finset α} {w : ℕ}
    (hu : IsUniform w 𝓕) (hZw : Z.card < w) : Z ∉ 𝓕 := by
  intro hZ
  have := hu hZ
  omega

/-- **The assembly.** Given the core extracted by `exists_rao_spread_link` and the satisfying
property of its link, the members above the core form an `(a,b)`-robust sunflower. -/
theorem isRobustSunflower_of_link_satisfying {X Z : Finset α} {𝓕 : Finset (Finset α)}
    {w : ℕ} {R a b : ℝ} (hR : 1 < R) (hu : IsUniform w 𝓕) (hZw : Z.card < w)
    (hlarge : R ^ (w - Z.card) ≤ (((link 𝓕 Z).card : ℕ) : ℝ))
    (hsp : IsRaoSpread R (w - Z.card) (link 𝓕 Z))
    (hsat : IsSatisfying a b (X \ Z) (link 𝓕 Z)) :
    IsRobustSunflower a b X (𝓕.filter fun S => Z ⊆ S) := by
  have hR1 : (1 : ℝ) ≤ R := le_of_lt hR
  -- the link is `(w − |Z|)`-uniform
  have hulink : IsUniform (w - Z.card) (link 𝓕 Z) := by
    intro P hP
    obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hP
    rw [Finset.card_sdiff_of_subset hZS, hu hS]
  refine isRobustSunflower_above_spread_core hR (notMem_of_card_lt hu hZw)
    (link_nonempty_of_large hR1 hlarge) ?_ hsat
  exact isSpread_of_isRaoSpread hR1 hulink hsp (by exact_mod_cast hlarge)

/-- **Theorem 1.9 on the Rao route, modulo the schedule.** A large enough `w`-uniform family
contains an `(a,b)`-robust sunflower, provided the extracted link is satisfying.

Supplying that last hypothesis is the constant chase: it is `rao_isSatisfying` at `δ = a`,
`ε = b`, applied to the link, with the schedule `(v, j)` chosen so that
`κ₀ = (C/a)·lg(w/b)` clears its conditions. -/
theorem exists_isRobustSunflower_of_link {X : Finset α} {𝓕 : Finset (Finset α)} {w : ℕ}
    {R a b : ℝ} (hR : 1 < R) (hw : 1 ≤ w) (hu : IsUniform w 𝓕) (hSX : ∀ S ∈ 𝓕, S ⊆ X)
    (hcard : R ^ w ≤ ((𝓕.card : ℕ) : ℝ))
    (hlink : ∀ Z ⊆ X, Z.card < w → R ^ (w - Z.card) ≤ (((link 𝓕 Z).card : ℕ) : ℝ) →
      IsRaoSpread R (w - Z.card) (link 𝓕 Z) → IsSatisfying a b (X \ Z) (link 𝓕 Z)) :
    ∃ 𝒢 ⊆ 𝓕, IsRobustSunflower a b X 𝒢 := by
  obtain ⟨Z, hZX, hZw, hlarge, hsp⟩ :=
    exists_rao_spread_link (le_of_lt hR) hw hu hSX hcard
  exact ⟨𝓕.filter fun S => Z ⊆ S, Finset.filter_subset _ _,
    isRobustSunflower_of_link_satisfying hR hu hZw hlarge hsp
      (hlink Z hZX hZw hlarge hsp)⟩

/-! ## Trimming the family to size

`rao_isSatisfying` wants `|𝓕| ≤ R^w` as well as `R^w ≤ |𝓕|` — the family must be *at* the
threshold, not merely above it. That is Rao's `ℓ = ⌈r^k⌉`.

He gets there with "removing sets from the sequence can only increase the expectation". The
plan flags that sentence as one not to rely on: after the uniform law of `S` changes, deleting
sets is not a pointwise monotonicity statement. The sound route is to pass to a subfamily of
the required size, apply the covering theorem there, and come back by monotonicity of the
covering *event* — which is `IsSatisfying.mono`, and is genuinely monotone.

Trimming lands at `⌈R^w⌉`, so the upper bound comes back as `R^w + 1` rather than `R^w`. -/

omit [DecidableEq α] in
/-- A subfamily at the threshold: `R^{w} ≤ |𝓗'| ≤ R^{w} + 1`, inheriting uniformity and
absolute spreadness. -/
theorem exists_trimmed_subfamily {𝓗 : Finset (Finset α)} {w' : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (hcard : R ^ w' ≤ (((𝓗.card : ℕ)) : ℝ)) :
    ∃ 𝓗' ⊆ 𝓗, R ^ w' ≤ (((𝓗'.card : ℕ)) : ℝ)
      ∧ (((𝓗'.card : ℕ)) : ℝ) ≤ R ^ w' + 1 := by
  classical
  have hR0 : (0 : ℝ) ≤ R ^ w' := by positivity
  have hceil : ⌈R ^ w'⌉₊ ≤ 𝓗.card := Nat.ceil_le.mpr hcard
  obtain ⟨𝓗', hsub, hcard'⟩ := Finset.exists_subset_card_eq hceil
  refine ⟨𝓗', hsub, ?_, ?_⟩
  · rw [hcard']
    exact Nat.le_ceil _
  · rw [hcard']
    exact le_of_lt (Nat.ceil_lt_add_one hR0)

omit [DecidableEq α] in
/-- Coverage is monotone in the family, so satisfying a subfamily is enough. This is the step
Rao's "removing sets can only increase the expectation" is doing, in the form where it is
actually true. -/
theorem isSatisfying_of_subset {X : Finset α} {𝓗' 𝓗 : Finset (Finset α)} {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hsub : 𝓗' ⊆ 𝓗) (h : IsSatisfying a b X 𝓗') :
    IsSatisfying a b X 𝓗 :=
  h.mono ha0 ha1 hsub

omit [DecidableEq α] in
/-- **The reduction to a trimmed family.** To show a link is satisfying it suffices to show it
for a subfamily at the threshold — which is the shape `rao_isSatisfying` consumes, once its
`|𝓕| ≤ R^w` is relaxed to `≤ R^w + 1`. -/
theorem isSatisfying_of_trimmed {X : Finset α} {𝓗 : Finset (Finset α)} {w' : ℕ} {R a b : ℝ}
    (hR : 1 ≤ R) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcard : R ^ w' ≤ (((𝓗.card : ℕ)) : ℝ))
    (hsat : ∀ 𝓗' ⊆ 𝓗, R ^ w' ≤ (((𝓗'.card : ℕ)) : ℝ) →
      (((𝓗'.card : ℕ)) : ℝ) ≤ R ^ w' + 1 → IsSatisfying a b X 𝓗') :
    IsSatisfying a b X 𝓗 := by
  obtain ⟨𝓗', hsub, hge, hle⟩ := exists_trimmed_subfamily hR hcard
  exact isSatisfying_of_subset ha0 ha1 hsub (hsat 𝓗' hsub hge hle)

end Rao

end Sunflower

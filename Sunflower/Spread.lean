/-
# The spread framework of Alweiss–Lovett–Wu–Zhang

The ALWZ proof of the improved sunflower bound factors into two parts:

1. **Reduction** (this file, fully proved): if a `w`-uniform family `𝓕` has
   `|𝓕| ≥ κ^w`, then some *link* `𝓕_Z = {S \ Z : Z ⊆ S ∈ 𝓕}` with `|Z| < w` is
   `κ`-spread and still large (`|𝓕_Z| ≥ κ^{w-|Z|}`). Moreover `r` pairwise-disjoint
   members of a link lift to an `r`-sunflower of `𝓕` with core `Z`.
2. **Spread lemma** (probabilistic core, `Sunflower.spread_lemma`, fully proved with the
   explicit constant `C = 2^41` in `Sunflower.SpreadCore`/`SpreadBottom`/`SpreadIterate`/
   `SpreadAssemble`): a `(C r³ log w log log w)`-spread family of nonempty sets contains
   `r` pairwise disjoint members.

`IsSpread` is stated multiplicatively — `|𝓕_Z| · R^{|Z|} ≤ |𝓕|` for every `Z` — to
avoid division; taking `Z = ∅` makes it an equality, so the condition is only about
nonempty `Z`, as in the paper.

The choice of `Z` in the reduction is the standard one: maximize `|𝓕_Z| · κ^{|Z|}`
over `|Z| < w`. Maximality gives spreadness at every `Y` with `|Z ∪ Y| < w`;
`|Z ∪ Y| = w` links have at most one member (uniformity), which the size lower
bound absorbs; `|Z ∪ Y| > w` links are empty.
-/
import Sunflower.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## Links -/

/-- The **link** of `Z` in `𝓕`: the petals `S \ Z` of the members `S ⊇ Z`. Written
`𝓕_Z` in the ALWZ paper. -/
def link (𝓕 : Finset (Finset α)) (Z : Finset α) : Finset (Finset α) :=
  (𝓕.filter fun S => Z ⊆ S).image fun S => S \ Z

lemma mem_link {𝓕 : Finset (Finset α)} {Z P : Finset α} :
    P ∈ link 𝓕 Z ↔ ∃ S ∈ 𝓕, Z ⊆ S ∧ S \ Z = P := by
  constructor
  · intro h
    rw [link, Finset.mem_image] at h
    obtain ⟨S, hS, rfl⟩ := h
    rw [Finset.mem_filter] at hS
    exact ⟨S, hS.1, hS.2, rfl⟩
  · rintro ⟨S, hS, hZS, rfl⟩
    rw [link, Finset.mem_image]
    exact ⟨S, Finset.mem_filter.mpr ⟨hS, hZS⟩, rfl⟩

/-- Members of a link are disjoint from `Z`. -/
lemma disjoint_of_mem_link {𝓕 : Finset (Finset α)} {Z P : Finset α}
    (h : P ∈ link 𝓕 Z) : Disjoint P Z := by
  obtain ⟨S, -, -, rfl⟩ := mem_link.mp h
  exact Finset.sdiff_disjoint

/-- Reattaching the core recovers a member of `𝓕`. -/
lemma union_mem_of_mem_link {𝓕 : Finset (Finset α)} {Z P : Finset α}
    (h : P ∈ link 𝓕 Z) : P ∪ Z ∈ 𝓕 := by
  obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp h
  rwa [Finset.sdiff_union_of_subset hZS]

@[simp] lemma link_empty (𝓕 : Finset (Finset α)) : link 𝓕 ∅ = 𝓕 := by
  rw [link, Finset.filter_true_of_mem fun _ _ => Finset.empty_subset _]
  simp only [Finset.sdiff_empty]
  exact Finset.image_id

/-- `S ↦ S \ Z` is injective on sets containing `Z`, so the link is exactly as large
as the subfamily above `Z`. -/
lemma card_link (𝓕 : Finset (Finset α)) (Z : Finset α) :
    (link 𝓕 Z).card = (𝓕.filter fun S => Z ⊆ S).card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hA hB
  calc A = A \ Z ∪ Z := (Finset.sdiff_union_of_subset hA.2).symm
    _ = B \ Z ∪ Z := by rw [show A \ Z = B \ Z from h]
    _ = B := Finset.sdiff_union_of_subset hB.2

/-- The link of a `w`-uniform family is `(w - |Z|)`-uniform. -/
lemma IsUniform.link {w : ℕ} {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕)
    (Z : Finset α) : IsUniform (w - Z.card) (Sunflower.link 𝓕 Z) := by
  intro P hP
  obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hP
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hZS, hu hS]

/-- In a `w`-uniform family, the link of a set larger than `w` is empty. -/
lemma link_eq_empty {w : ℕ} {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕)
    {Z : Finset α} (h : w < Z.card) : link 𝓕 Z = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  obtain ⟨S, hS, hZS, -⟩ := mem_link.mp hP
  have := Finset.card_le_card hZS
  rw [hu hS] at this
  omega

/-- In a `w`-uniform family, the link of a `w`-element set has at most one member:
the only possible member above `Z` is `Z` itself. -/
lemma card_link_le_one {w : ℕ} {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕)
    {Z : Finset α} (h : w ≤ Z.card) : (link 𝓕 Z).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro P hP Q hQ
  obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hP
  obtain ⟨T, hT, hZT, rfl⟩ := mem_link.mp hQ
  have hSZ : Z = S := Finset.eq_of_subset_of_card_le hZS (by rw [hu hS]; exact h)
  have hTZ : Z = T := Finset.eq_of_subset_of_card_le hZT (by rw [hu hT]; exact h)
  rw [← hSZ, ← hTZ]

/-- Composition: a link of a link is a link, `(𝓕_Z)_Y = 𝓕_{Z ∪ Y}` for `Y` disjoint
from `Z`. -/
lemma link_link (𝓕 : Finset (Finset α)) {Z Y : Finset α} (hd : Disjoint Y Z) :
    link (link 𝓕 Z) Y = link 𝓕 (Z ∪ Y) := by
  ext P
  rw [mem_link, mem_link]
  constructor
  · rintro ⟨Q, hQ, hYQ, rfl⟩
    obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hQ
    refine ⟨S, hS, Finset.union_subset hZS (hYQ.trans Finset.sdiff_subset), ?_⟩
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  · rintro ⟨S, hS, hZYS, rfl⟩
    rw [Finset.union_subset_iff] at hZYS
    refine ⟨S \ Z, mem_link.mpr ⟨S, hS, hZYS.1, rfl⟩, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_sdiff]
      exact ⟨hZYS.2 ha, fun haZ => Finset.disjoint_left.mp hd ha haZ⟩
    · ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto

/-- If `Y` meets `Z`, no member of `𝓕_Z` contains `Y`, so `(𝓕_Z)_Y = ∅`. -/
lemma link_link_of_not_disjoint (𝓕 : Finset (Finset α)) {Z Y : Finset α}
    (hd : ¬ Disjoint Y Z) : link (link 𝓕 Z) Y = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  obtain ⟨Q, hQ, hYQ, -⟩ := mem_link.mp hP
  exact hd (Finset.disjoint_of_subset_left hYQ (disjoint_of_mem_link hQ))

/-! ## Spread families -/

/-- `𝓖` is **`R`-spread** if no restriction is too popular: `|𝓖_Z| · R^{|Z|} ≤ |𝓖|`
for every `Z`. (At `Z = ∅` this is an equality, so only nonempty `Z` constrain.)
Stated multiplicatively to avoid division. -/
def IsSpread (R : ℝ) (𝓖 : Finset (Finset α)) : Prop :=
  ∀ Z : Finset α, ((link 𝓖 Z).card : ℝ) * R ^ Z.card ≤ (𝓖.card : ℝ)

/-- Spreadness is antitone in `R`: an `R`-spread family is `R'`-spread for
`0 ≤ R' ≤ R`. -/
lemma IsSpread.mono {R R' : ℝ} {𝓖 : Finset (Finset α)} (h : IsSpread R 𝓖)
    (hR' : 0 ≤ R') (hle : R' ≤ R) : IsSpread R' 𝓖 := by
  intro Z
  refine le_trans ?_ (h Z)
  gcongr

/-! ## The reduction: a large uniform family has a large spread link -/

/-- **Reduction to a spread link.** If `𝓕` is `w`-uniform with `|𝓕| ≥ κ^w`, there is
a core `Z` with `|Z| < w` whose link is `κ`-spread and still large:
`|𝓕_Z| · κ^{|Z|} ≥ κ^w`. Choose `Z` maximizing `|𝓕_Z| · κ^{|Z|}` over `|Z| < w`. -/
theorem exists_spread_link {κ : ℝ} (hκ : 1 ≤ κ) {w : ℕ} (hw : 1 ≤ w)
    {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕) (hcard : κ ^ w ≤ (𝓕.card : ℝ)) :
    ∃ Z : Finset α, Z.card < w ∧ IsSpread κ (link 𝓕 Z) ∧
      κ ^ w ≤ ((link 𝓕 Z).card : ℝ) * κ ^ Z.card := by
  classical
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le one_pos hκ
  have hne : ((𝓕.biUnion id).powerset.filter fun Z => Z.card < w).Nonempty :=
    ⟨∅, by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.empty_subset _, by simp only [Finset.card_empty]; omega⟩⟩
  obtain ⟨Z, hZmem, hZmax⟩ := Finset.exists_max_image
    ((𝓕.biUnion id).powerset.filter fun Z => Z.card < w)
    (fun Z => ((link 𝓕 Z).card : ℝ) * κ ^ Z.card) hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hZmem
  obtain ⟨-, hZlt⟩ := hZmem
  -- maximality holds against *every* small core, not just subsets of the union:
  -- a core outside the union has empty link.
  have key : ∀ Z' : Finset α, Z'.card < w →
      ((link 𝓕 Z').card : ℝ) * κ ^ Z'.card ≤ ((link 𝓕 Z).card : ℝ) * κ ^ Z.card := by
    intro Z' hZ'
    by_cases hsub : Z' ⊆ 𝓕.biUnion id
    · exact hZmax Z' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hZ'⟩)
    · have hempty : link 𝓕 Z' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro P hP
        obtain ⟨S, hS, hZS, -⟩ := mem_link.mp hP
        exact hsub (hZS.trans (Finset.subset_biUnion_of_mem id hS))
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
  have hsize : κ ^ w ≤ ((link 𝓕 Z).card : ℝ) * κ ^ Z.card := by
    have hkey := key ∅ (by simp only [Finset.card_empty]; omega)
    simp only [link_empty, Finset.card_empty, pow_zero, mul_one] at hkey
    exact hcard.trans hkey
  refine ⟨Z, hZlt, ?_, hsize⟩
  intro Y
  by_cases hd : Disjoint Y Z
  · rw [link_link 𝓕 hd]
    have hcardU : (Z ∪ Y).card = Z.card + Y.card := Finset.card_union_of_disjoint hd.symm
    rcases lt_trichotomy (Z ∪ Y).card w with hlt | heq | hgt
    · -- small joint core: directly from maximality of `Z`, cancelling `κ^{|Z|}`
      refine le_of_mul_le_mul_right ?_ (pow_pos hκ0 Z.card)
      calc ((link 𝓕 (Z ∪ Y)).card : ℝ) * κ ^ Y.card * κ ^ Z.card
          = ((link 𝓕 (Z ∪ Y)).card : ℝ) * κ ^ (Z ∪ Y).card := by
            rw [hcardU, pow_add]; ring
        _ ≤ ((link 𝓕 Z).card : ℝ) * κ ^ Z.card := key _ hlt
    · -- joint core of full size `w`: the link has ≤ 1 member, and `κ^{|Y|} = κ^{w-|Z|}`
      -- is absorbed by the size lower bound on `|𝓕_Z|`.
      have hle1 : ((link 𝓕 (Z ∪ Y)).card : ℝ) ≤ 1 := by
        exact_mod_cast card_link_le_one hu heq.ge
      have hpow : κ ^ Y.card * κ ^ Z.card ≤ ((link 𝓕 Z).card : ℝ) * κ ^ Z.card := by
        calc κ ^ Y.card * κ ^ Z.card = κ ^ w := by
              rw [← pow_add]; congr 1; omega
          _ ≤ _ := hsize
      have h2 : κ ^ Y.card ≤ ((link 𝓕 Z).card : ℝ) :=
        le_of_mul_le_mul_right hpow (pow_pos hκ0 _)
      calc ((link 𝓕 (Z ∪ Y)).card : ℝ) * κ ^ Y.card
          ≤ 1 * κ ^ Y.card := mul_le_mul_of_nonneg_right hle1 (by positivity)
        _ = κ ^ Y.card := one_mul _
        _ ≤ _ := h2
    · -- oversized joint core: empty link
      rw [link_eq_empty hu hgt]
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
  · rw [link_link_of_not_disjoint 𝓕 hd]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity

/-! ## From disjoint petals in a link to a sunflower -/

/-- Removing a disjoint `Z` undoes attaching it. -/
private lemma union_sdiff_self {P Z : Finset α} (h : Disjoint P Z) : (P ∪ Z) \ Z = P := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · exact absurd h1 h2
  · intro ha
    exact ⟨Or.inl ha, fun haZ => Finset.disjoint_left.mp h ha haZ⟩

/-- **Lifting disjoint petals.** `r` pairwise-disjoint members of the link `𝓕_Z`
reattach to an `r`-sunflower of `𝓕` with core `Z`. -/
theorem hasSunflower_of_pairwiseDisjoint_link {𝓕 : Finset (Finset α)} {Z : Finset α}
    {r : ℕ} {𝒟 : Finset (Finset α)} (hsub : 𝒟 ⊆ link 𝓕 Z) (hcard : 𝒟.card = r)
    (hpd : (𝒟 : Set (Finset α)).PairwiseDisjoint id) : HasSunflower r 𝓕 := by
  classical
  have hdisjZ : ∀ ⦃P⦄, P ∈ 𝒟 → Disjoint P Z := fun P hP =>
    disjoint_of_mem_link (hsub hP)
  have hinj : Set.InjOn (fun P => P ∪ Z) (𝒟 : Set (Finset α)) := by
    intro A hA B hB h
    calc A = (A ∪ Z) \ Z := (union_sdiff_self (hdisjZ hA)).symm
      _ = (B ∪ Z) \ Z := by rw [show A ∪ Z = B ∪ Z from h]
      _ = B := union_sdiff_self (hdisjZ hB)
  refine ⟨𝒟.image (fun P => P ∪ Z), ?_, ?_, Z, ?_⟩
  · intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨P, hP, rfl⟩ := hS
    exact union_mem_of_mem_link (hsub hP)
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · intro S hS T hT hne
    rw [Finset.mem_image] at hS hT
    obtain ⟨P, hP, rfl⟩ := hS
    obtain ⟨Q, hQ, rfl⟩ := hT
    have hPQ : P ≠ Q := fun h => hne (by rw [h])
    have hdisj : Disjoint P Q :=
      hpd (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hPQ
    ext a
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hP' | hZ', hQ' | hZ''⟩
      · exact absurd hQ' (Finset.disjoint_left.mp hdisj hP')
      · exact hZ''
      · exact hZ'
      · exact hZ'
    · intro hZ'
      exact ⟨Or.inr hZ', Or.inr hZ'⟩

end Sunflower

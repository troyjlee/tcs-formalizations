/-
# The Erdős–Rado sunflower lemma

Any `w`-uniform family with more than `(r-1)^w * w!` members contains an `r`-sunflower
(Erdős–Rado, 1960). This is the classical bound that Alweiss–Lovett–Wu–Zhang improved to
`(C r³ log w log log w)^w`; it also supplies the induction skeleton that the ALWZ argument
reuses.

The proof is the standard one, by induction on `w`. Take a *maximal* pairwise-disjoint
subfamily `𝒟`.

* If `|𝒟| ≥ r`, any `r` of its members are pairwise disjoint, hence a sunflower with empty
  core.
* Otherwise `|𝒟| ≤ r - 1`, so `Y = ⋃ 𝒟` has at most `(r-1)·w` elements. By maximality every
  member of `𝓕` meets `Y`, so pigeonhole gives a `y ∈ Y` lying in at least `|𝓕|/|Y|` members.
  Delete `y` from those, apply the induction hypothesis at `w - 1`, and reinsert `y`.
-/
import Sunflower.Defs
import Sunflower.Padding
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## Lifting a sunflower along a common new element -/

/-- Inserting a common element `y`, absent from every member, into each member of a
sunflower yields a sunflower whose core has gained `y`. -/
theorem IsSunflowerWith.insert_common {𝒮 : Finset (Finset α)} {K : Finset α} {y : α}
    (hK : IsSunflowerWith 𝒮 K) (hy : ∀ ⦃S⦄, S ∈ 𝒮 → y ∉ S) :
    IsSunflowerWith (𝒮.image (insert y)) (insert y K) := by
  intro S hS T hT hne
  rw [Finset.mem_image] at hS hT
  obtain ⟨A, hA, rfl⟩ := hS
  obtain ⟨B, hB, rfl⟩ := hT
  have hAB : A ≠ B := fun h => hne (by rw [h])
  rw [← hK hA hB hAB]
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨hL, hR⟩
    rcases hL with rfl | hA'
    · exact Or.inl rfl
    · rcases hR with rfl | hB'
      · exact Or.inl rfl
      · exact Or.inr ⟨hA', hB'⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr h1, Or.inr h2⟩

/-- `insert y` is injective on families of sets avoiding `y`. -/
theorem insert_injOn_of_notMem {𝒮 : Finset (Finset α)} {y : α}
    (hy : ∀ ⦃S⦄, S ∈ 𝒮 → y ∉ S) : Set.InjOn (insert y) (𝒮 : Set (Finset α)) := by
  intro A hA B hB h
  have : (insert y A).erase y = (insert y B).erase y := by rw [h]
  rwa [Finset.erase_insert (hy hA), Finset.erase_insert (hy hB)] at this

/-- `Finset.erase · y` is injective on families of sets containing `y`. -/
theorem erase_injOn_of_mem {𝓖 : Finset (Finset α)} {y : α}
    (hy : ∀ ⦃S⦄, S ∈ 𝓖 → y ∈ S) : Set.InjOn (fun S => Finset.erase S y) (𝓖 : Set (Finset α)) := by
  intro A hA B hB h
  have h' : insert y (A.erase y) = insert y (B.erase y) := by
    show insert y ((fun S => Finset.erase S y) A) = insert y ((fun S => Finset.erase S y) B)
    rw [h]
  rwa [Finset.insert_erase (hy hA), Finset.insert_erase (hy hB)] at h'

/-! ## The theorem -/

/-- The Erdős–Rado bound `(r-1)^w · w!`. -/
def erBound (r w : ℕ) : ℕ := (r - 1) ^ w * Nat.factorial w

@[simp] lemma erBound_zero (r : ℕ) : erBound r 0 = 1 := by simp [erBound]

lemma erBound_succ (r w : ℕ) :
    erBound r (w + 1) = (r - 1) * (w + 1) * erBound r w := by
  simp only [erBound, Nat.factorial_succ, pow_succ]
  ring

/-- **Erdős–Rado (1960).** A `w`-uniform family with more than `(r-1)^w * w!` members
contains an `r`-sunflower. -/
theorem erdos_rado : ∀ (w r : ℕ) {𝓕 : Finset (Finset α)}, IsUniform w 𝓕 →
    erBound r w < 𝓕.card → HasSunflower r 𝓕 := by
  intro w
  induction w with
  | zero =>
    -- every member is `∅`, so the family has at most one member, contradicting `1 < card`
    intro r 𝓕 hu hcard
    exfalso
    have hsub : 𝓕 ⊆ {(∅ : Finset α)} := by
      intro S hS
      rw [Finset.mem_singleton, ← Finset.card_eq_zero]
      exact hu hS
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    rw [erBound_zero] at hcard
    omega
  | succ w ih =>
    intro r 𝓕 hu hcard
    classical
    -- `r = 0` and `r = 1` are immediate; the real argument needs `2 ≤ r`.
    rcases Nat.lt_or_ge r 2 with hr | hr
    · have hr01 : r = 0 ∨ r = 1 := by omega
      rcases hr01 with rfl | rfl
      · exact ⟨∅, Finset.empty_subset _, Finset.card_empty, ∅, by
          intro S hS; simp at hS⟩
      · have hne : 𝓕.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨S, hS⟩ := hne
        refine ⟨{S}, by simpa using hS, Finset.card_singleton _, ∅, ?_⟩
        intro A hA B hB hAB
        rw [Finset.mem_singleton] at hA hB
        exact absurd (hA.trans hB.symm) hAB
    -- A maximal pairwise-disjoint subfamily `𝒟`.
    obtain ⟨𝒟, h𝒟mem, h𝒟max⟩ :=
      Finset.exists_max_image (𝓕.powerset.filter
        (fun D : Finset (Finset α) => ((D : Set (Finset α)).PairwiseDisjoint id)))
        Finset.card ⟨∅, by simp⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at h𝒟mem
    obtain ⟨h𝒟sub, h𝒟pd⟩ := h𝒟mem
    rcases Nat.lt_or_ge 𝒟.card r with hsmall | hbig
    case _ =>
      -- Case 2: `𝒟` is small, so its union `Y` is small; pigeonhole on `Y`.
      set Y : Finset α := 𝒟.biUnion id with hY
      -- every member of `𝓕` meets `Y`, by maximality of `𝒟`
      have hmeet : ∀ S ∈ 𝓕, ∃ y ∈ Y, y ∈ S := by
        intro S hS
        by_contra hcon
        push Not at hcon
        have hdisj : ∀ T ∈ 𝒟, Disjoint S T := by
          intro T hT
          rw [Finset.disjoint_left]
          intro a haS haT
          exact hcon a (Finset.mem_biUnion.mpr ⟨T, hT, haT⟩) haS
        by_cases hSD : S ∈ 𝒟
        · -- `S ⊆ Y` and `S ≠ ∅`, so `S` meets `Y`
          have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hu hS]; omega)
          obtain ⟨a, ha⟩ := hSne
          exact hcon a (Finset.mem_biUnion.mpr ⟨S, hSD, ha⟩) ha
        · -- otherwise `insert S 𝒟` is a strictly larger pairwise-disjoint subfamily
          have hmem : insert S 𝒟 ∈ (𝓕.powerset.filter
              (fun D : Finset (Finset α) => ((D : Set (Finset α)).PairwiseDisjoint id))) := by
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨Finset.insert_subset hS h𝒟sub, ?_⟩
            rw [Finset.coe_insert]
            refine h𝒟pd.insert ?_
            intro T hT _
            exact hdisj T hT
          have := h𝒟max _ hmem
          rw [Finset.card_insert_of_notMem hSD] at this
          omega
      -- `|Y| ≤ (r-1)(w+1)`
      have hYcard : Y.card ≤ (r - 1) * (w + 1) := by
        calc Y.card ≤ ∑ S ∈ 𝒟, (id S).card := Finset.card_biUnion_le
          _ = ∑ S ∈ 𝒟, (w + 1) := Finset.sum_congr rfl (fun S hS => hu (h𝒟sub hS))
          _ = 𝒟.card * (w + 1) := by simp [Finset.sum_const]
          _ ≤ (r - 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      -- pigeonhole: some `y ∈ Y` lies in many members
      have hYne : Y.Nonempty := by
        have hFne : 𝓕.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨S, hS⟩ := hFne
        obtain ⟨y, hyY, -⟩ := hmeet S hS
        exact ⟨y, hyY⟩
      obtain ⟨y, hyY, hymax⟩ :=
        Finset.exists_max_image Y (fun y => (𝓕.filter (fun S => y ∈ S)).card) hYne
      have hcover : 𝓕 ⊆ Y.biUnion (fun y => 𝓕.filter (fun S => y ∈ S)) := by
        intro S hS
        obtain ⟨z, hzY, hzS⟩ := hmeet S hS
        exact Finset.mem_biUnion.mpr ⟨z, hzY, Finset.mem_filter.mpr ⟨hS, hzS⟩⟩
      have hpigeon : 𝓕.card ≤ Y.card * (𝓕.filter (fun S => y ∈ S)).card := by
        calc 𝓕.card ≤ (Y.biUnion (fun y => 𝓕.filter (fun S => y ∈ S))).card :=
              Finset.card_le_card hcover
          _ ≤ ∑ z ∈ Y, (𝓕.filter (fun S => z ∈ S)).card := Finset.card_biUnion_le
          _ ≤ Y.card * (𝓕.filter (fun S => y ∈ S)).card := by
              have := Finset.sum_le_card_nsmul Y
                (fun z => (𝓕.filter (fun S => z ∈ S)).card)
                ((𝓕.filter (fun S => y ∈ S)).card) hymax
              simpa using this
      -- delete `y`, apply the induction hypothesis, reinsert `y`
      set 𝓖 : Finset (Finset α) :=
        (𝓕.filter (fun S => y ∈ S)).image (fun S => S.erase y) with h𝓖
      have hymem : ∀ ⦃S⦄, S ∈ 𝓕.filter (fun S => y ∈ S) → y ∈ S :=
        fun S hS => (Finset.mem_filter.mp hS).2
      have h𝓖card : 𝓖.card = (𝓕.filter (fun S => y ∈ S)).card := by
        rw [h𝓖]
        exact Finset.card_image_of_injOn (erase_injOn_of_mem hymem)
      have h𝓖unif : IsUniform w 𝓖 := by
        intro S hS
        rw [h𝓖, Finset.mem_image] at hS
        obtain ⟨T, hT, rfl⟩ := hS
        rw [Finset.card_erase_of_mem (hymem hT), hu (Finset.mem_filter.mp hT).1]
        omega
      have h𝓖bound : erBound r w < 𝓖.card := by
        have h1 : (r - 1) * (w + 1) * erBound r w < (r - 1) * (w + 1) * 𝓖.card := by
          rw [← erBound_succ]
          calc erBound r (w + 1) < 𝓕.card := hcard
            _ ≤ Y.card * (𝓕.filter (fun S => y ∈ S)).card := hpigeon
            _ = Y.card * 𝓖.card := by rw [h𝓖card]
            _ ≤ ((r - 1) * (w + 1)) * 𝓖.card := Nat.mul_le_mul_right _ hYcard
        have hpos : 0 < (r - 1) * (w + 1) := by
          have : 1 ≤ r - 1 := by omega
          positivity
        exact Nat.lt_of_mul_lt_mul_left h1
      obtain ⟨𝒮', h𝒮'sub, h𝒮'card, K', h𝒮'sun⟩ := ih r h𝓖unif h𝓖bound
      have hynot : ∀ ⦃A⦄, A ∈ 𝒮' → y ∉ A := by
        intro A hA
        have := h𝒮'sub hA
        rw [h𝓖, Finset.mem_image] at this
        obtain ⟨T, -, rfl⟩ := this
        exact Finset.notMem_erase y T
      refine ⟨𝒮'.image (insert y), ?_, ?_, insert y K', h𝒮'sun.insert_common hynot⟩
      · -- the lifted family sits inside `𝓕`
        intro S hS
        rw [Finset.mem_image] at hS
        obtain ⟨A, hA, rfl⟩ := hS
        have := h𝒮'sub hA
        rw [h𝓖, Finset.mem_image] at this
        obtain ⟨T, hT, hTA⟩ := this
        rw [← hTA, Finset.insert_erase (hymem hT)]
        exact (Finset.mem_filter.mp hT).1
      · rw [Finset.card_image_of_injOn (insert_injOn_of_notMem hynot)]
        exact h𝒮'card
    case _ =>
      -- Case 1: `𝒟` already has `r` pairwise-disjoint members
      obtain ⟨𝒮, h𝒮sub, h𝒮card⟩ := Finset.exists_subset_card_eq hbig
      exact ⟨𝒮, h𝒮sub.trans h𝒟sub, h𝒮card, ∅,
        isSunflowerWith_empty_of_pairwiseDisjoint
          (h𝒟pd.subset (Finset.coe_subset.mpr h𝒮sub))⟩

/-- **Erdős–Rado for `w`-set systems.** The same bound, with the hypothesis weakened from
"every member has exactly `w` elements" to "at most `w`" — the form in which the lemma is
usually quoted, and the form ALWZ quote it in (their Lemma 1.2). Proved from the uniform
version by private-dummy padding (`Sunflower.hasSunflower_of_bounded`), which costs nothing:
padding preserves the number of members exactly. -/
theorem erdos_rado_bounded (w r : ℕ) {𝓕 : Finset (Finset α)} (hb : IsBounded w 𝓕)
    (hcard : erBound r w < 𝓕.card) : HasSunflower r 𝓕 :=
  hasSunflower_of_bounded (P := fun n => erBound r w < n)
    (fun hu hc => erdos_rado w r hu hc) hb hcard

end Sunflower

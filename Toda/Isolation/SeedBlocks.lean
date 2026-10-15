import Toda.Isolation.Affine

/-!
# Explicit flat seeds for independent variable-width blocks

Block decoding reads coordinate `offset(block)+position` of the flat seed.
Offsets are prefix sums of block lengths. The proof of bijectivity uses exact
finite cardinalities, while the decoder itself is this explicit coordinate
map and needs no enumeration or choice of seed values.
-/

namespace Toda.Isolation

open Complexity

def blockOffset (size : ℕ → ℕ) (blocks : ℕ) : ℕ :=
  ∑ index ∈ Finset.range blocks, size index

theorem blockOffset_mono (size : ℕ → ℕ) : Monotone (blockOffset size) := by
  intro first second h
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (by intros; omega)

theorem blockOffset_succ (size : ℕ → ℕ) (index : ℕ) :
    blockOffset size (index + 1) = blockOffset size index + size index := by
  exact Finset.sum_range_succ size index

/-- The explicit flat coordinate occupied by one bit in a block. -/
def blockPosition (size : ℕ → ℕ) (blocks : ℕ)
    (position : Σ index : Fin blocks, Fin (size index.val)) :
    Fin (∑ index : Fin blocks, size index.val) :=
  ⟨blockOffset size position.1.val + position.2.val, by
    have hnext := blockOffset_mono size (Nat.succ_le_of_lt position.1.isLt)
    rw [blockOffset_succ] at hnext
    rw [Fin.sum_univ_eq_sum_range]
    change _ < blockOffset size blocks
    have hbit := position.2.isLt
    omega⟩

theorem blockPosition_injective (size : ℕ → ℕ) (blocks : ℕ) :
    Function.Injective (blockPosition size blocks) := by
  rintro ⟨first, firstBit⟩ ⟨second, secondBit⟩ heq
  have hvalue := congrArg Fin.val heq
  change blockOffset size first.val + firstBit.val =
    blockOffset size second.val + secondBit.val at hvalue
  have hfirst := firstBit.isLt
  have hsecond := secondBit.isLt
  have hnotlt : ¬ first.val < second.val := by
    intro hlt
    have hprefix := blockOffset_mono size (Nat.succ_le_of_lt hlt)
    rw [blockOffset_succ] at hprefix
    omega
  have hnotgt : ¬ second.val < first.val := by
    intro hlt
    have hprefix := blockOffset_mono size (Nat.succ_le_of_lt hlt)
    rw [blockOffset_succ] at hprefix
    omega
  have hindex : first = second := Fin.ext (by omega)
  cases hindex
  have hbit : firstBit = secondBit := Fin.ext (by omega)
  cases hbit
  rfl

theorem blockPosition_bijective (size : ℕ → ℕ) (blocks : ℕ) :
    Function.Bijective (blockPosition size blocks) := by
  refine ⟨blockPosition_injective size blocks, ?_⟩
  by_contra hnot
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (blockPosition size blocks) (blockPosition_injective size blocks) hnot
  simp at hlt

/-- Decode each block by explicit prefix-sum indexing into the flat seed. -/
def decodeBlocks (size : ℕ → ℕ) (blocks : ℕ)
    (seed : BitString (∑ index : Fin blocks, size index.val)) :
    (index : Fin blocks) → BitString (size index.val) :=
  fun index bit => seed (blockPosition size blocks ⟨index, bit⟩)

/-- Flat bits and their block tuple are in exact bijection. The forward map is
the explicit decoder; the inverse is used only for this finite identity. -/
noncomputable def decodeBlocksEquiv (size : ℕ → ℕ) (blocks : ℕ) :
    BitString (∑ index : Fin blocks, size index.val) ≃
      ((index : Fin blocks) → BitString (size index.val)) :=
  (Equiv.arrowCongr
    (Equiv.ofBijective (blockPosition size blocks) (blockPosition_bijective size blocks)).symm
    (Equiv.refl Bool)).trans (Equiv.piCurry fun _ _ => Bool)

@[simp] theorem decodeBlocksEquiv_apply (size : ℕ → ℕ) (blocks : ℕ)
    (seed : BitString (∑ index : Fin blocks, size index.val)) :
    decodeBlocksEquiv size blocks seed = decodeBlocks size blocks seed := rfl

/-- Decode the independent affine blocks for every attempted output width. -/
def decodeAllWidths (domainWidth : ℕ) (seed : BitString (allWidthSeedWidth domainWidth)) :
    AllWidthSeeds domainWidth :=
  decodeBlocks (fun index => PairwiseIndependentHash.affineSeedWidth domainWidth (index + 2))
    (domainWidth + 1) seed

noncomputable def decodeAllWidthsEquiv (domainWidth : ℕ) :
    BitString (allWidthSeedWidth domainWidth) ≃ AllWidthSeeds domainWidth :=
  decodeBlocksEquiv
    (fun index => PairwiseIndependentHash.affineSeedWidth domainWidth (index + 2))
    (domainWidth + 1)

@[simp] theorem decodeAllWidthsEquiv_apply (domainWidth : ℕ)
    (seed : BitString (allWidthSeedWidth domainWidth)) :
    decodeAllWidthsEquiv domainWidth seed = decodeAllWidths domainWidth seed := rfl

/-- The all-width success event on an ordinary flat bit-string seed. -/
def flatAllWidthSuccess {domainWidth : ℕ} (witnesses : Finset (BitString domainWidth)) :
    Finset (BitString (allWidthSeedWidth domainWidth)) :=
  Finset.univ.filter fun seed => decodeAllWidths domainWidth seed ∈ allWidthSuccess witnesses

/-- Flattening preserves the success probability exactly. -/
theorem flatAllWidthSuccess_probability {domainWidth : ℕ}
    (witnesses : Finset (BitString domainWidth)) :
    eventProb (flatAllWidthSuccess witnesses) =
      (allWidthSuccess witnesses).card / (Fintype.card (AllWidthSeeds domainWidth) : ℚ) := by
  classical
  have hevent := Fintype.card_congr
    ((decodeAllWidthsEquiv domainWidth).subtypeEquiv
      (p := fun seed => decodeAllWidths domainWidth seed ∈ allWidthSuccess witnesses)
      (q := fun seeds => seeds ∈ allWidthSuccess witnesses) (fun _ => Iff.rfl))
  have htotal := Fintype.card_congr (decodeAllWidthsEquiv domainWidth)
  simp only [Fintype.card_subtype] at hevent
  have hcard : (flatAllWidthSuccess witnesses).card = (allWidthSuccess witnesses).card := by
    simpa [flatAllWidthSuccess] using hevent
  rw [card_finArrowBool] at htotal
  rw [eventProb, hcard, ← htotal]
  norm_cast

/-- Every nonempty witness set is isolated by at least one eighth of the
polynomial-width flat affine seeds. -/
theorem flatAllWidthSuccess_probability_ge_one_eighth {domainWidth : ℕ}
    (witnesses : Finset (BitString domainWidth)) (hwitnesses : witnesses.Nonempty) :
    (1 : ℚ) / 8 ≤ eventProb (flatAllWidthSuccess witnesses) := by
  rw [flatAllWidthSuccess_probability]
  exact allWidthSuccess_probability_ge_one_eighth witnesses hwitnesses

@[simp] theorem flatAllWidthSuccess_empty (domainWidth : ℕ) :
    flatAllWidthSuccess (∅ : Finset (BitString domainWidth)) = ∅ := by
  simp [flatAllWidthSuccess]

end Toda.Isolation

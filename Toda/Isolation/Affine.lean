import Toda.Isolation.Finite
import Toda.Isolation.Finite.Amplification
import Complexitylib.Classes.Randomized.Hashing.Affine

/-!
# Singleton isolation by the concrete affine hash family

The pinned Boolean affine family supplies the exact marginal and pairwise
probabilities required by finite isolation. Trying every possible useful
output width in independent seed blocks avoids computing the unknown witness
count. The tuple experiment has success probability at least one eighth for
every nonempty witness set, and its total number of random bits is polynomial.

These statements concern finite seed experiments. Explicit serialization and
polynomial-time evaluation are proved in `SeedBlocks` and `AffineEval`.
-/

namespace Toda.Isolation

open Complexity

/-- Keep precisely the witnesses landing in the requested hash cell. -/
def hashKeep {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (target : BitString rangeWidth) : BitString seedWidth → BitString domainWidth → Bool :=
  fun seed witness => decide (hash.eval seed witness = target)

/-- The finite isolation bound for any exactly pairwise-independent bit hash. -/
theorem hash_isolation_probability_ge_one_eighth
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (witnesses : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (hlower : (1 : ℚ) / 4 ≤ (witnesses.card : ℚ) / 2 ^ rangeWidth)
    (hupper : (witnesses.card : ℚ) / (2 : ℚ) ^ rangeWidth ≤ 1 / 2) :
    (1 : ℚ) / 8 ≤ eventProb (isolatingSeeds (hashKeep hash target) witnesses) := by
  suffices h : (1 : ℚ) / 8 ≤ (isolatingSeeds (hashKeep hash target) witnesses).card /
      (Fintype.card (BitString seedWidth) : ℚ) by
    simpa [eventProb, card_finArrowBool] using h
  apply isolation_probability_ge_one_eighth (hashKeep hash target) witnesses
    (1 / (2 : ℚ) ^ rangeWidth)
  · intro witness _
    simpa [retainingSeeds, hashKeep, eventProb, card_finArrowBool] using
      hash.uniform witness target
  · intro first _ second _ hne
    have hpair := hash.pairwise hne target target
    have hpower : (1 / (2 : ℚ) ^ rangeWidth) ^ 2 = 1 / (2 : ℚ) ^ (2 * rangeWidth) := by
      rw [pow_mul', div_pow, one_pow]
    rw [hpower]
    exact le_of_eq (by
      simpa [jointlyRetainingSeeds, hashKeep, eventProb, card_finArrowBool] using hpair)
  · simpa [div_eq_mul_inv] using hlower
  · simpa [div_eq_mul_inv] using hupper

/-- In particular the concrete affine matrix hash isolates at the appropriate
output width, using exactly `rangeWidth*(domainWidth+1)` random bits. -/
theorem affine_isolation_probability_ge_one_eighth
    {domainWidth rangeWidth : ℕ} (witnesses : Finset (BitString domainWidth))
    (hlower : (1 : ℚ) / 4 ≤ (witnesses.card : ℚ) / 2 ^ rangeWidth)
    (hupper : (witnesses.card : ℚ) / (2 : ℚ) ^ rangeWidth ≤ 1 / 2) :
    (1 : ℚ) / 8 ≤ eventProb (isolatingSeeds
      (hashKeep (PairwiseIndependentHash.affine domainWidth rangeWidth) (fun _ => false))
      witnesses) :=
  hash_isolation_probability_ge_one_eighth _ _ _ hlower hupper

/-- A uniformly sampled dependent tuple has a uniform marginal at each index. -/
theorem coordinate_probability {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Values : Index → Type*} [∀ index, Fintype (Values index)]
    [∀ index, DecidableEq (Values index)]
    [∀ index, Nonempty (Values index)] (index : Index) (event : Finset (Values index)) :
    ((Finset.univ.filter fun values : ∀ i, Values i => values index ∈ event).card : ℚ) /
        Fintype.card (∀ i, Values i) =
      (event.card : ℚ) / Fintype.card (Values index) := by
  classical
  let split := Equiv.piSplitAt index Values
  let restricted : {values : ∀ i, Values i // values index ∈ event} ≃
      {value : Values index // value ∈ event} ×
        (∀ i : {i // i ≠ index}, Values i) :=
    (split.subtypeEquiv (q := fun values => values.1 ∈ event) (fun _ => Iff.rfl)).trans
      Equiv.prodSubtypeFstEquivSubtypeProd
  have hselected := Fintype.card_congr restricted
  have htotal := Fintype.card_congr split
  simp only [Fintype.card_prod, Fintype.card_subtype] at hselected
  simp only [Fintype.card_prod] at htotal
  rw [hselected, htotal]
  push_cast
  have hrest : (Fintype.card (∀ i : {i // i ≠ index}, Values i) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp

/-- One independent affine seed for each output width `2,...,domainWidth+2`. -/
abbrev AllWidthSeeds (domainWidth : ℕ) :=
  (index : Fin (domainWidth + 1)) →
    BitString (PairwiseIndependentHash.affineSeedWidth domainWidth (index.val + 2))

/-- The zero-cell keep predicate at one of the attempted widths. -/
def allWidthKeep (domainWidth : ℕ) (index : Fin (domainWidth + 1)) :=
  hashKeep (PairwiseIndependentHash.affine domainWidth (index.val + 2)) (fun _ => false)

/-- Success means that at least one attempted width isolates one witness. -/
def allWidthSuccess {domainWidth : ℕ} (witnesses : Finset (BitString domainWidth)) :
    Finset (AllWidthSeeds domainWidth) :=
  Finset.univ.filter fun seeds => ∃ index : Fin (domainWidth + 1),
    (survivors (allWidthKeep domainWidth index) witnesses (seeds index)).card = 1

@[simp] theorem allWidthSuccess_empty (domainWidth : ℕ) :
    allWidthSuccess (∅ : Finset (BitString domainWidth)) = ∅ := by
  simp [allWidthSuccess, survivors]

/-- The all-width affine experiment has constant success for every nonempty
witness set, without knowing its size when sampling the seed. -/
theorem allWidthSuccess_probability_ge_one_eighth {domainWidth : ℕ}
    (witnesses : Finset (BitString domainWidth)) (hwitnesses : witnesses.Nonempty) :
    (1 : ℚ) / 8 ≤ (allWidthSuccess witnesses).card /
      (Fintype.card (AllWidthSeeds domainWidth) : ℚ) := by
  classical
  obtain ⟨width, hwidth, hmax, hlower, hupper⟩ :=
    exists_dyadic_isolation_width (Finset.card_pos.mpr hwitnesses) (card_le_pow witnesses)
  let index : Fin (domainWidth + 1) := ⟨width - 2, by omega⟩
  have hindex : index.val + 2 = width := by dsimp [index]; omega
  let event := isolatingSeeds (allWidthKeep domainWidth index) witnesses
  have hgood : (1 : ℚ) / 8 ≤
      (event.card : ℚ) /
        Fintype.card (BitString (PairwiseIndependentHash.affineSeedWidth domainWidth
          (index.val + 2))) := by
    have h := affine_isolation_probability_ge_one_eighth
      (rangeWidth := index.val + 2) witnesses
      (by simpa [hindex] using hlower) (by simpa [hindex] using hupper)
    simpa [event, allWidthKeep, eventProb, card_finArrowBool] using h
  have hprojection := coordinate_probability
    (Values := fun i : Fin (domainWidth + 1) =>
      BitString (PairwiseIndependentHash.affineSeedWidth domainWidth (i.val + 2)))
    index event
  rw [← hprojection] at hgood
  apply hgood.trans
  apply div_le_div_of_nonneg_right
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro seeds hseeds
    have hmember := (Finset.mem_filter.mp hseeds).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, index, (Finset.mem_filter.mp hmember).2⟩
  · positivity

/-- Total number of random bits in all the independent affine blocks. -/
def allWidthSeedWidth (domainWidth : ℕ) : ℕ :=
  ∑ index : Fin (domainWidth + 1),
    PairwiseIndependentHash.affineSeedWidth domainWidth (index.val + 2)

/-- The all-width experiment needs at most a cubic number of random bits. -/
theorem allWidthSeedWidth_le (domainWidth : ℕ) :
    allWidthSeedWidth domainWidth ≤ (domainWidth + 2) * (domainWidth + 1) ^ 2 := by
  unfold allWidthSeedWidth PairwiseIndependentHash.affineSeedWidth
  calc
    _ ≤ ∑ _index : Fin (domainWidth + 1), (domainWidth + 2) * (domainWidth + 1) := by
      apply Finset.sum_le_sum
      intro index _
      apply Nat.mul_le_mul_right
      have hindex := index.isLt
      omega
    _ = _ := by simp; ring

end Toda.Isolation

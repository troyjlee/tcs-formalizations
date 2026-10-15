import Toda.Isolation.SeedBlocks
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.BoundedQuant
import Complexitylib.Classes.P.Pairing

/-!
# Polynomial-time affine hashing on serialized seeds

The evaluator reads one coefficient and one witness bit at a time. It counts
the true products in a row and takes their parity, then checks all requested
rows. Every numerical intermediate is bounded by the dimensions or a seed
position; no represented binary value is expanded into unary.
-/

namespace Toda.Isolation

open Complexity

def affineTerm (domainWidth : ℕ) (seed witness : List Bool)
    (offset row column : ℕ) : Bool :=
  seed[offset + row * (domainWidth + 1) + column]?.getD false &&
    (if column < domainWidth then witness[column]?.getD false else true)

def affineRowParity (domainWidth : ℕ) (seed witness : List Bool)
    (offset row : ℕ) : ℕ :=
  (∑ column ∈ Finset.range (domainWidth + 1),
    (affineTerm domainWidth seed witness offset row column).toNat) % 2

/-- A total zero-cell test on arbitrary strings and unary dimensions. -/
def affineZero (domainWidth rows : ℕ) (seed witness : List Bool) (offset : ℕ) : Prop :=
  ∀ row < rows, affineRowParity domainWidth seed witness offset row = 0

instance (domainWidth rows : ℕ) (seed witness : List Bool) (offset : ℕ) :
    Decidable (affineZero domainWidth rows seed witness offset) :=
  inferInstanceAs (Decidable (∀ row < rows, _))

/-- One affine product bit is computable by actual polynomial-time access to
the seed and witness strings. -/
theorem affineTerm_unary {n offset row column : List Bool → ℕ}
    {seed witness : List Bool → List Bool} (hn : UnaryFn n)
    (hoffset : UnaryFn offset) (hrow : UnaryFn row) (hcolumn : UnaryFn column)
    (hseed : seed ∈ FP) (hwitness : witness ∈ FP) :
    UnaryFn fun z => (affineTerm (n z) (seed z) (witness z)
      (offset z) (row z) (column z)).toNat := by
  have hcoefficient := FPPred.getBit hseed
    ((hoffset.add (hrow.mul (hn.add (UnaryFn.const 1)))).add hcolumn)
  have hvalue := (FPPred.lt hcolumn hn).not.or (FPPred.getBit hwitness hcolumn)
  apply (UnaryFn.ite (hcoefficient.and hvalue) (UnaryFn.const 1) (UnaryFn.const 0)).of_eq
  intro z
  simp only [affineTerm]
  by_cases hcolumn : column z < n z <;>
    cases hc : (seed z)[offset z + row z * (n z + 1) + column z]?.getD false <;>
    cases hv : (witness z)[column z]?.getD false <;> simp [hcolumn]

/-- The parity of one row is unary polynomial-time computable; its numerical
answer is only zero or one. -/
theorem affineRowParity_unary {n offset row : List Bool → ℕ}
    {seed witness : List Bool → List Bool} (hn : UnaryFn n)
    (hoffset : UnaryFn offset) (hrow : UnaryFn row)
    (hseed : seed ∈ FP) (hwitness : witness ∈ FP) :
    UnaryFn fun z => affineRowParity (n z) (seed z) (witness z) (offset z) (row z) := by
  have hterm := affineTerm_unary hn.lift hoffset.lift hrow.lift UnaryFn.index
    (mem_FP_comp pairFst_mem_FP hseed) (mem_FP_comp pairFst_mem_FP hwitness)
  apply (((hn.add (UnaryFn.const 1)).sum hterm).mod (UnaryFn.const 2)).of_eq
  intro z
  simp [affineRowParity]

/-- All rows of an affine matrix can be checked in polynomial time when their
number and the input dimension are unary polynomial-time functions. -/
theorem affineZero_fppred {n rows offset : List Bool → ℕ}
    {seed witness : List Bool → List Bool} (hn : UnaryFn n) (hrows : UnaryFn rows)
    (hoffset : UnaryFn offset) (hseed : seed ∈ FP) (hwitness : witness ∈ FP) :
    FPPred fun z => affineZero (n z) (rows z) (seed z) (witness z) (offset z) := by
  have hrow := affineRowParity_unary hn.lift hoffset.lift UnaryFn.index
    (mem_FP_comp pairFst_mem_FP hseed) (mem_FP_comp pairFst_mem_FP hwitness)
  apply (FPPred.forall_lt hrows (FPPred.eq hrow (UnaryFn.const 0))).of_iff
  intro z
  simp [affineZero]

/-- Boolean-ring sums are the parity of the number of true summands. -/
theorem bool_sum_toNat {Index : Type*} (indices : Finset Index) (bits : Index → Bool) :
    (∑ index ∈ indices, bits index).toNat =
      (∑ index ∈ indices, (bits index).toNat) % 2 := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert index indices hnot ih =>
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
    change (bits index ^^ (∑ index ∈ indices, bits index)).toNat =
      ((bits index).toNat + ∑ index ∈ indices, (bits index).toNat) % 2
    cases hbit : bits index <;> cases hsum : ∑ index ∈ indices, bits index <;>
      simp only [hsum] at ih <;> norm_num [Bool.xor] at ih ⊢ <;> omega

/-- On a correctly placed coefficient block, the string evaluator agrees
with the concrete affine matrix map for every row. -/
theorem affineRowParity_eq {domainWidth rows : ℕ}
    (coefficients : BitString (PairwiseIndependentHash.affineSeedWidth domainWidth rows))
    (witness : BitString domainWidth) (seed : List Bool) (offset : ℕ)
    (hcoefficients : ∀ bit, seed[offset + bit.val]?.getD false = coefficients bit)
    (row : Fin rows) :
    affineRowParity domainWidth seed (List.ofFn witness) offset row.val =
      (PairwiseIndependentHash.affineEval coefficients witness row).toNat := by
  have hterm (column : Fin (domainWidth + 1)) :
      affineTerm domainWidth seed (List.ofFn witness) offset row.val column.val =
        PairwiseIndependentHash.affineRows coefficients row column *
          PairwiseIndependentHash.affineAugment witness column := by
    unfold affineTerm PairwiseIndependentHash.affineRows
    have hposition : offset + row.val * (domainWidth + 1) + column.val =
        offset + (finProdFinEquiv (row, column)).val := by
      change offset + row.val * (domainWidth + 1) + column.val =
        offset + (column.val + (domainWidth + 1) * row.val)
      ring
    rw [hposition, hcoefficients (finProdFinEquiv (row, column))]
    change (_ && _) = (_ && _)
    congr 1
    unfold PairwiseIndependentHash.affineAugment Fin.snoc
    by_cases hcolumn : column.val < domainWidth <;> simp [hcolumn, Fin.castLT]
  unfold affineRowParity
  rw [← Fin.sum_univ_eq_sum_range]
  have hnat : (∑ column : Fin (domainWidth + 1),
      (affineTerm domainWidth seed (List.ofFn witness) offset row.val column.val).toNat) =
      ∑ column : Fin (domainWidth + 1),
        (PairwiseIndependentHash.affineRows coefficients row column *
          PairwiseIndependentHash.affineAugment witness column).toNat := by
    apply Finset.sum_congr rfl
    intro column _
    rw [hterm]
  rw [hnat, ← bool_sum_toNat]
  rfl

/-- The serialized zero-cell predicate agrees with the actual affine hash. -/
theorem affineZero_iff {domainWidth rows : ℕ}
    (coefficients : BitString (PairwiseIndependentHash.affineSeedWidth domainWidth rows))
    (witness : BitString domainWidth) (seed : List Bool) (offset : ℕ)
    (hcoefficients : ∀ bit, seed[offset + bit.val]?.getD false = coefficients bit) :
    affineZero domainWidth rows seed (List.ofFn witness) offset ↔
      PairwiseIndependentHash.affineEval coefficients witness = fun _ => false := by
  constructor
  · intro h
    funext row
    have hzero := h row.val row.isLt
    rw [affineRowParity_eq coefficients witness seed offset hcoefficients row] at hzero
    simpa using hzero
  · intro h row hrow
    rw [affineRowParity_eq coefficients witness seed offset hcoefficients ⟨row, hrow⟩, h]
    rfl

/-- Starting position of the affine block for output width `index+2`. -/
def affineBlockOffset (domainWidth index : ℕ) : ℕ :=
  blockOffset (fun j => PairwiseIndependentHash.affineSeedWidth domainWidth (j + 2)) index

/-- Affine block offsets are unary polynomial-time functions of the dimension
and block index. -/
theorem affineBlockOffset_unary {n index : List Bool → ℕ}
    (hn : UnaryFn n) (hindex : UnaryFn index) :
    UnaryFn fun z => affineBlockOffset (n z) (index z) := by
  have hbody := (UnaryFn.index.add (UnaryFn.const 2)).mul (hn.lift.add (UnaryFn.const 1))
  apply (hindex.sum hbody).of_eq
  intro z
  simp [affineBlockOffset, blockOffset, PairwiseIndependentHash.affineSeedWidth]

/-- The complete all-width random seed length is unary polynomial-time
computable from a unary polynomial-time input dimension. -/
theorem allWidthSeedWidth_unary {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun z => allWidthSeedWidth (n z) := by
  apply (affineBlockOffset_unary hn (hn.add (UnaryFn.const 1))).of_eq
  intro z
  unfold affineBlockOffset allWidthSeedWidth blockOffset
  exact (Fin.sum_univ_eq_sum_range
    (fun index => PairwiseIndependentHash.affineSeedWidth (n z) (index + 2)) (n z + 1)).symm

/-- Explicit list indexing retrieves precisely the coefficient decoded from
the flat all-width random seed. -/
theorem getD_affineBlock (domainWidth : ℕ)
    (seed : BitString (allWidthSeedWidth domainWidth))
    (index : Fin (domainWidth + 1))
    (bit : Fin (PairwiseIndependentHash.affineSeedWidth domainWidth (index.val + 2))) :
    (List.ofFn seed)[affineBlockOffset domainWidth index.val + bit.val]?.getD false =
      decodeAllWidths domainWidth seed index bit := by
  have hread : (List.ofFn seed)[(blockPosition
      (fun j => PairwiseIndependentHash.affineSeedWidth domainWidth (j + 2))
      (domainWidth + 1) ⟨index, bit⟩).val]?.getD false =
      seed (blockPosition
        (fun j => PairwiseIndependentHash.affineSeedWidth domainWidth (j + 2))
        (domainWidth + 1) ⟨index, bit⟩) := by
    have hbound : (blockPosition
        (fun j => PairwiseIndependentHash.affineSeedWidth domainWidth (j + 2))
        (domainWidth + 1) ⟨index, bit⟩).val < allWidthSeedWidth domainWidth :=
      (blockPosition
        (fun j => PairwiseIndependentHash.affineSeedWidth domainWidth (j + 2))
        (domainWidth + 1) ⟨index, bit⟩).isLt
    simp [hbound]
    congr 1
  exact hread

/-- The total polynomial-time string test is the same zero-cell predicate as
the affine hash used in the flat-seed isolation probability theorem. -/
theorem affineZero_allWidths_iff (domainWidth : ℕ)
    (seed : BitString (allWidthSeedWidth domainWidth)) (witness : BitString domainWidth)
    (index : Fin (domainWidth + 1)) :
    affineZero domainWidth (index.val + 2) (List.ofFn seed) (List.ofFn witness)
      (affineBlockOffset domainWidth index.val) ↔
      allWidthKeep domainWidth index (decodeAllWidths domainWidth seed index) witness = true := by
  simpa [allWidthKeep, hashKeep, PairwiseIndependentHash.affine_eval] using
    affineZero_iff (decodeAllWidths domainWidth seed index) witness (List.ofFn seed)
      (affineBlockOffset domainWidth index.val) (getD_affineBlock domainWidth seed index)

end Toda.Isolation

import Toda.Counting.VerifierWitness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact counts for an array of fixed-width witnesses

A word of length `n * r` has exactly one decomposition into `n` blocks of
length `r`. This includes zero blocks and zero-width blocks.
-/

namespace Toda.Counting.BoundedProduct

open Complexity

/-- Read the block at index `i` from a flattened word. -/
def block {n r : ℕ} (w : Fin (n * r) → Bool) (i : Fin n) : Fin r → Bool :=
  fun j => w (finProdFinEquiv (i, j))

/-- Flatten a rectangular array of bits in increasing block order. -/
def flatten {n r : ℕ} (v : Fin n → Fin r → Bool) : Fin (n * r) → Bool :=
  fun k => v (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem block_flatten {n r : ℕ} (v : Fin n → Fin r → Bool) :
    block (flatten v) = v := by
  funext i j
  simp [block, flatten]

@[simp] theorem flatten_block {n r : ℕ} (w : Fin (n * r) → Bool) :
    flatten (block w) = w := by
  funext k
  change w (finProdFinEquiv (finProdFinEquiv.symm k)) = w k
  rw [Equiv.apply_symm_apply]

theorem flatten_injective {n r : ℕ} :
    Function.Injective (flatten (n := n) (r := r)) := by
  intro u v h
  simpa using congrArg block h

/-- The machine-accessible slice agrees with the finite-array block. -/
theorem slice_eq_ofFn_block {n r : ℕ} (w : Fin (n * r) → Bool) (i : Fin n) :
    ((List.ofFn w).drop (i.val * r)).take r = List.ofFn (block w i) := by
  have hi : (i.val + 1) * r ≤ n * r := Nat.mul_le_mul_right r i.isLt
  rw [Nat.add_mul, Nat.one_mul] at hi
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro j hj hj'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, block]
    congr 1
    apply Fin.ext
    change i.val * r + j = j + r * i.val
    ac_rfl

/-- Arrays with the prescribed admissible set at every index, flattened. -/
def witnesses {n r : ℕ} (S : Fin n → Finset (Fin r → Bool)) :
    Finset (Fin (n * r) → Bool) :=
  (Fintype.piFinset S).image flatten

@[simp] theorem mem_witnesses {n r : ℕ} (S : Fin n → Finset (Fin r → Bool))
    (w : Fin (n * r) → Bool) :
    w ∈ witnesses S ↔ ∀ i, block w i ∈ S i := by
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa using (Fintype.mem_piFinset.mp hv)
  · intro hw
    exact Finset.mem_image.mpr ⟨block w, Fintype.mem_piFinset.mpr hw, flatten_block w⟩

theorem card_witnesses {n r : ℕ} (S : Fin n → Finset (Fin r → Bool)) :
    (witnesses S).card = ∏ i, (S i).card := by
  rw [witnesses, Finset.card_image_of_injective _ flatten_injective,
    Fintype.card_piFinset]

/-- Check every block against the corresponding unary-indexed verifier input.
Pair projections and slicing give a total definition on arbitrary inputs. -/
def language (L : Language) (q r : List Bool → ℕ) : Language :=
  {z | ∀ i < q (pairFst z),
    pair (pair (pairFst z) (List.replicate i true))
      (((pairSnd z).drop (i * r (pairFst z))).take (r (pairFst z))) ∈ L}

theorem pair_mem_language (L : Language) (q r : List Bool → ℕ) (x : List Bool)
    (w : Fin (q x * r x) → Bool) :
    pair x (List.ofFn w) ∈ language L q r ↔
      ∀ i : Fin (q x), pair (pair x (List.replicate i.val true))
        (List.ofFn (block w i)) ∈ L := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
  constructor
  · intro h i
    simpa only [slice_eq_ofFn_block] using h i.val i.isLt
  · intro h i hi
    rw [slice_eq_ofFn_block w ⟨i, hi⟩]
    exact h ⟨i, hi⟩

/-- The count is a product with no extra multiplicity from block encoding. -/
theorem card_verifierWitnesses (L : Language) (q r : List Bool → ℕ) (x : List Bool) :
    (verifierWitnesses (language L q r) x (q x * r x)).card =
      ∏ i : Fin (q x), (verifierWitnesses L
        (pair x (List.replicate i.val true)) (r x)).card := by
  rw [← card_witnesses]
  congr 1
  ext w
  simp [pair_mem_language]

end Toda.Counting.BoundedProduct

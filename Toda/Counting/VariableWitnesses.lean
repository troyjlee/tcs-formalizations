import Toda.Counting.VerifierWitness
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.List.OfFn

/-!
# Exact witnesses with variable prefix widths

False padding preserves a witness count when its width is enlarged. Splitting
a witness into two arbitrary blocks expresses its count as a sum over the
first block. These are exact finite identities, including zero-width blocks;
polynomial-time implementation of the languages is proved separately.
-/

namespace Toda.Counting.VariableWitnesses

open Complexity

/-- Enlarge a witness by appending false bits. -/
def padEncode {q T : ℕ} (_hq : q ≤ T) (u : Fin q → Bool) : Fin T → Bool :=
  fun i => if h : i.val < q then u ⟨i.val, h⟩ else false

/-- Extract the initial block of a longer witness. -/
def padPrefix {q T : ℕ} (hq : q ≤ T) (w : Fin T → Bool) : Fin q → Bool :=
  fun i => w ⟨i.val, by omega⟩

/-- All positions after the prefix must be false. -/
def falsePadding {q T : ℕ} (w : Fin T → Bool) : Prop :=
  ∀ i : Fin T, q ≤ i.val → w i = false

@[simp] theorem padPrefix_encode {q T : ℕ} (hq : q ≤ T) (u : Fin q → Bool) :
    padPrefix hq (padEncode hq u) = u := by
  funext i
  simp [padPrefix, padEncode, i.isLt]

@[simp] theorem falsePadding_encode {q T : ℕ} (hq : q ≤ T) (u : Fin q → Bool) :
    falsePadding (q := q) (padEncode hq u) := by
  intro i hi
  simp [padEncode, show ¬i.val < q by omega]

theorem padEncode_decode {q T : ℕ} (hq : q ≤ T) (w : Fin T → Bool)
    (hw : falsePadding (q := q) w) : padEncode hq (padPrefix hq w) = w := by
  funext i
  simp only [padEncode]
  split_ifs with hi
  · rfl
  · exact (hw i (by omega)).symm

theorem padEncode_injective {q T : ℕ} (hq : q ≤ T) :
    Function.Injective (padEncode hq) := by
  intro u v huv
  simpa using congrArg (padPrefix hq) huv

theorem take_ofFn_padPrefix {q T : ℕ} (hq : q ≤ T) (w : Fin T → Bool) :
    (List.ofFn w).take q = List.ofFn (padPrefix hq w) := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hq]
  · intro i hi hi'
    simp [padPrefix]

theorem falsePadding_iff_list {q T : ℕ} (w : Fin T → Bool) :
    falsePadding (q := q) w ↔ ∀ b ∈ (List.ofFn w).drop q, b = false := by
  constructor
  · intro hw b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    simp only [List.length_drop, List.length_ofFn] at hi
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact hw ⟨q + i, by omega⟩ (show q ≤ q + i by omega)
  · intro hw i hi
    apply hw (w i)
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val - q, ?_, ?_⟩
    · simp only [List.length_drop, List.length_ofFn]
      omega
    · simp only [List.getElem_drop, List.getElem_ofFn]
      congr 1
      apply Fin.ext
      change q + (i.val - q) = i.val
      omega

/-- Check a variable-width payload and require unique false padding. -/
def paddingLanguage (L : Language) (q : List Bool → ℕ) : Language :=
  {z | (∀ b ∈ (pairSnd z).drop (q (pairFst z)), b = false) ∧
    pair (pairFst z) ((pairSnd z).take (q (pairFst z))) ∈ L}

theorem pair_mem_paddingLanguage (L : Language) (q : List Bool → ℕ)
    (x : List Bool) {T : ℕ} (hq : q x ≤ T) (w : Fin T → Bool) :
    pair x (List.ofFn w) ∈ paddingLanguage L q ↔
      falsePadding (q := q x) w ∧ pair x (List.ofFn (padPrefix hq w)) ∈ L := by
  simp only [paddingLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
  rw [← falsePadding_iff_list, take_ofFn_padPrefix hq]

theorem card_verifierWitnesses_paddingLanguage (L : Language) (q : List Bool → ℕ)
    (x : List Bool) {T : ℕ} (hq : q x ≤ T) :
    (verifierWitnesses (paddingLanguage L q) x T).card =
      (verifierWitnesses L x (q x)).card := by
  classical
  have hset : verifierWitnesses (paddingLanguage L q) x T =
      (verifierWitnesses L x (q x)).image (padEncode hq) := by
    ext w
    rw [mem_verifierWitnesses, pair_mem_paddingLanguage L q x hq]
    constructor
    · rintro ⟨hpad, hmem⟩
      exact Finset.mem_image.mpr ⟨padPrefix hq w,
        (mem_verifierWitnesses L x (q x) _).mpr hmem, padEncode_decode hq w hpad⟩
    · intro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      simpa using And.intro (falsePadding_encode hq u)
        ((mem_verifierWitnesses L x (q x) u).mp hu)
  rw [hset, Finset.card_image_of_injective _ (padEncode_injective hq)]

/-- Concatenate witnesses of arbitrary, possibly unequal, widths. -/
def splitEncode {q r : ℕ} (u : Fin q → Bool) (v : Fin r → Bool) :
    Fin (q + r) → Bool :=
  fun i => if h : i.val < q then u ⟨i.val, h⟩ else v ⟨i.val - q, by omega⟩

def splitLeft {q r : ℕ} (w : Fin (q + r) → Bool) : Fin q → Bool :=
  fun i => w ⟨i.val, by omega⟩

def splitRight {q r : ℕ} (w : Fin (q + r) → Bool) : Fin r → Bool :=
  fun i => w ⟨q + i.val, by omega⟩

@[simp] theorem splitLeft_encode {q r : ℕ} (u : Fin q → Bool) (v : Fin r → Bool) :
    splitLeft (splitEncode u v) = u := by
  funext i
  simp [splitLeft, splitEncode, i.isLt]

@[simp] theorem splitRight_encode {q r : ℕ} (u : Fin q → Bool) (v : Fin r → Bool) :
    splitRight (splitEncode u v) = v := by
  funext i
  simp [splitRight, splitEncode]

@[simp] theorem splitEncode_decode {q r : ℕ} (w : Fin (q + r) → Bool) :
    splitEncode (splitLeft w) (splitRight w) = w := by
  funext i
  simp only [splitEncode]
  split_ifs with h
  · rfl
  · simp only [splitRight]
    congr 1
    apply Fin.ext
    change q + (i.val - q) = i.val
    omega

theorem ofFn_splitEncode {q r : ℕ} (u : Fin q → Bool) (v : Fin r → Bool) :
    List.ofFn (splitEncode u v) = List.ofFn u ++ List.ofFn v := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, splitEncode]

theorem take_ofFn_splitLeft {q r : ℕ} (w : Fin (q + r) → Bool) :
    (List.ofFn w).take q = List.ofFn (splitLeft w) := by
  rw [← splitEncode_decode w, ofFn_splitEncode]
  simp

theorem drop_ofFn_splitRight {q r : ℕ} (w : Fin (q + r) → Bool) :
    (List.ofFn w).drop q = List.ofFn (splitRight w) := by
  rw [← splitEncode_decode w, ofFn_splitEncode]
  simp

theorem splitEncode_sigma_injective (q r : ℕ) :
    Function.Injective (fun uv : (_u : Fin q → Bool) × (Fin r → Bool) =>
      splitEncode uv.1 uv.2) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ huv
  have hleft : u = u' := by simpa using congrArg splitLeft huv
  have hright : v = v' := by simpa using congrArg splitRight huv
  cases hleft
  cases hright
  rfl

/-- The first witness block is appended to the input; the second is checked
as the witness for that extended input. -/
def sumLanguage (L : Language) (q : List Bool → ℕ) : Language :=
  {z | pair (pair (pairFst z) ((pairSnd z).take (q (pairFst z))))
    ((pairSnd z).drop (q (pairFst z))) ∈ L}

theorem pair_mem_sumLanguage (L : Language) (q : List Bool → ℕ)
    (x : List Bool) (r : ℕ) (w : Fin (q x + r) → Bool) :
    pair x (List.ofFn w) ∈ sumLanguage L q ↔
      pair (pair x (List.ofFn (splitLeft w))) (List.ofFn (splitRight w)) ∈ L := by
  simp [sumLanguage, take_ofFn_splitLeft, drop_ofFn_splitRight]

theorem card_verifierWitnesses_sumLanguage (L : Language) (q : List Bool → ℕ)
    (x : List Bool) (r : ℕ) :
    (verifierWitnesses (sumLanguage L q) x (q x + r)).card =
      ∑ y : Fin (q x) → Bool,
        (verifierWitnesses L (pair x (List.ofFn y)) r).card := by
  classical
  let S := Finset.univ.sigma (fun y : Fin (q x) → Bool =>
    verifierWitnesses L (pair x (List.ofFn y)) r)
  have hset : verifierWitnesses (sumLanguage L q) x (q x + r) =
      S.image (fun uv => splitEncode uv.1 uv.2) := by
    ext w
    rw [mem_verifierWitnesses, pair_mem_sumLanguage]
    constructor
    · intro hw
      apply Finset.mem_image.mpr
      refine ⟨⟨splitLeft w, splitRight w⟩, ?_, splitEncode_decode w⟩
      simpa [S] using hw
    · intro hw
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      simpa [S] using huv
  rw [hset, Finset.card_image_of_injective _ (splitEncode_sigma_injective (q x) r)]
  exact Finset.card_sigma _ _

end Toda.Counting.VariableWitnesses

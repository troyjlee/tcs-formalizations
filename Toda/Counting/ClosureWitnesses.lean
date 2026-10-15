import Toda.Counting.VerifierWitness
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.OfFn

/-!
# Exact witnesses for binary counting operations

Two width-`T` witnesses fit into width `2 * T`. Products concatenate both
witnesses. Sums use one tag, one width-`T` payload, and `T - 1` false bits;
the latter layout requires `1 ≤ T`. The false-padding check gives exactly
one encoding of each tagged payload. These are finite counting identities;
polynomial-time implementation of the predicates is a separate obligation.
-/

namespace Toda.Counting.ClosureWitnesses

open Complexity

/-- Concatenation of two equal-width witnesses. -/
def productEncode {T : ℕ} (u v : Fin T → Bool) : Fin (2 * T) → Bool :=
  fun i => if h : i.val < T then u ⟨i.val, h⟩ else v ⟨i.val - T, by omega⟩

/-- The first width-`T` block. -/
def productLeft {T : ℕ} (w : Fin (2 * T) → Bool) : Fin T → Bool :=
  fun i => w ⟨i.val, by omega⟩

/-- The second width-`T` block. -/
def productRight {T : ℕ} (w : Fin (2 * T) → Bool) : Fin T → Bool :=
  fun i => w ⟨T + i.val, by omega⟩

@[simp] theorem productLeft_encode {T : ℕ} (u v : Fin T → Bool) :
    productLeft (productEncode u v) = u := by
  funext i
  simp [productLeft, productEncode, i.isLt]

@[simp] theorem productRight_encode {T : ℕ} (u v : Fin T → Bool) :
    productRight (productEncode u v) = v := by
  funext i
  simp [productRight, productEncode]

@[simp] theorem productEncode_decode {T : ℕ} (w : Fin (2 * T) → Bool) :
    productEncode (productLeft w) (productRight w) = w := by
  funext i
  simp only [productEncode]
  split_ifs with h
  · rfl
  · simp only [productRight]
    congr 1
    apply Fin.ext
    change T + (i.val - T) = i.val
    omega

theorem ofFn_productEncode {T : ℕ} (u v : Fin T → Bool) :
    List.ofFn (productEncode u v) = List.ofFn u ++ List.ofFn v := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append]
    omega
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, productEncode]

theorem take_ofFn_productLeft {T : ℕ} (w : Fin (2 * T) → Bool) :
    (List.ofFn w).take T = List.ofFn (productLeft w) := by
  rw [← productEncode_decode w, ofFn_productEncode]
  simp

theorem drop_ofFn_productRight {T : ℕ} (w : Fin (2 * T) → Bool) :
    (List.ofFn w).drop T = List.ofFn (productRight w) := by
  rw [← productEncode_decode w, ofFn_productEncode]
  simp

theorem productEncode_injective {T : ℕ} :
    Function.Injective (fun uv : (Fin T → Bool) × (Fin T → Bool) =>
      productEncode uv.1 uv.2) := by
  intro uv uv' h
  exact Prod.ext (by simpa using congrArg productLeft h)
    (by simpa using congrArg productRight h)

/-- Product witnesses are precisely the words whose two blocks lie in the
specified finite sets. -/
def productWitnesses {T : ℕ} (S R : Finset (Fin T → Bool)) :
    Finset (Fin (2 * T) → Bool) :=
  (S ×ˢ R).image (fun uv => productEncode uv.1 uv.2)

@[simp] theorem mem_productWitnesses {T : ℕ} (S R : Finset (Fin T → Bool))
    (w : Fin (2 * T) → Bool) :
    w ∈ productWitnesses S R ↔ productLeft w ∈ S ∧ productRight w ∈ R := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp h
    simpa using huv
  · rintro ⟨hu, hv⟩
    exact Finset.mem_image.mpr ⟨(productLeft w, productRight w),
      Finset.mem_product.mpr ⟨hu, hv⟩, productEncode_decode w⟩

theorem card_productWitnesses {T : ℕ} (S R : Finset (Fin T → Bool)) :
    (productWitnesses S R).card = S.card * R.card := by
  rw [productWitnesses, Finset.card_image_of_injective _ productEncode_injective,
    Finset.card_product]

/-- Sum encoding: false selects the left set and true selects the right set.
All remaining positions beyond the payload are false. -/
def taggedEncode {T : ℕ} (tag : Bool) (u : Fin T → Bool) : Fin (2 * T) → Bool :=
  fun i => if i.val = 0 then tag else
    if h : i.val ≤ T then u ⟨i.val - 1, by omega⟩ else false

/-- The initial branch tag. -/
def taggedTag {T : ℕ} (hT : 1 ≤ T) (w : Fin (2 * T) → Bool) : Bool :=
  w ⟨0, by omega⟩

/-- The width-`T` payload immediately following the tag. -/
def taggedPayload {T : ℕ} (hT : 1 ≤ T) (w : Fin (2 * T) → Bool) : Fin T → Bool :=
  fun i => w ⟨i.val + 1, by omega⟩

/-- Every bit beyond the tag and the payload must be false. -/
def taggedPadding {T : ℕ} (w : Fin (2 * T) → Bool) : Prop :=
  ∀ i : Fin (2 * T), T < i.val → w i = false

@[simp] theorem taggedTag_encode {T : ℕ} (hT : 1 ≤ T) (tag : Bool)
    (u : Fin T → Bool) : taggedTag hT (taggedEncode tag u) = tag := by
  simp [taggedTag, taggedEncode]

@[simp] theorem taggedPayload_encode {T : ℕ} (hT : 1 ≤ T) (tag : Bool)
    (u : Fin T → Bool) : taggedPayload hT (taggedEncode tag u) = u := by
  funext i
  simp [taggedPayload, taggedEncode, show i.val + 1 ≤ T by omega]

@[simp] theorem taggedPadding_encode {T : ℕ} (tag : Bool) (u : Fin T → Bool) :
    taggedPadding (taggedEncode tag u) := by
  intro i hi
  simp [taggedEncode, show i.val ≠ 0 by omega, show ¬i.val ≤ T by omega]

theorem taggedEncode_decode {T : ℕ} (hT : 1 ≤ T) (w : Fin (2 * T) → Bool)
    (hw : taggedPadding w) :
    taggedEncode (taggedTag hT w) (taggedPayload hT w) = w := by
  funext i
  simp only [taggedEncode]
  split_ifs with hzero hle
  · simp only [taggedTag]
    congr 1
    exact Fin.ext hzero.symm
  · simp only [taggedPayload]
    congr 1
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  · exact (hw i (by omega)).symm

theorem taggedEncode_injective {T : ℕ} (hT : 1 ≤ T) (tag : Bool) :
    Function.Injective (taggedEncode (T := T) tag) := by
  intro u v h
  simpa using congrArg (taggedPayload hT) h

theorem ofFn_taggedEncode {T : ℕ} (hT : 1 ≤ T) (tag : Bool) (u : Fin T → Bool) :
    List.ofFn (taggedEncode tag u) = tag :: (List.ofFn u ++ List.replicate (T - 1) false) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_cons, List.length_append, List.length_replicate]
    omega
  · intro i hi hi'
    cases i with
    | zero => simp [taggedEncode]
    | succ i =>
      simp only [List.getElem_ofFn, List.getElem_cons_succ, List.getElem_append,
        List.length_ofFn]
      split_ifs with h
      · simp [taggedEncode, show i + 1 ≤ T by omega]
      · simp [taggedEncode, show ¬i + 1 ≤ T by omega]

/-- Decode the two half-sized blocks of the second component of an ordinary
pair. The language is total even on malformed inputs. -/
def productLanguage (L R : Language) : Language :=
  {z | pair (pairFst z) ((pairSnd z).take ((pairSnd z).length / 2)) ∈ L ∧
    pair (pairFst z) ((pairSnd z).drop ((pairSnd z).length / 2)) ∈ R}

theorem pair_mem_productLanguage (L R : Language) (x : List Bool) {T : ℕ}
    (w : Fin (2 * T) → Bool) :
    pair x (List.ofFn w) ∈ productLanguage L R ↔
      pair x (List.ofFn (productLeft w)) ∈ L ∧
      pair x (List.ofFn (productRight w)) ∈ R := by
  simp [productLanguage, take_ofFn_productLeft, drop_ofFn_productRight]

theorem card_verifierWitnesses_productLanguage (L R : Language) (x : List Bool) (T : ℕ) :
    (verifierWitnesses (productLanguage L R) x (2 * T)).card =
      (verifierWitnesses L x T).card * (verifierWitnesses R x T).card := by
  rw [← card_productWitnesses]
  congr 1
  ext w
  simp [pair_mem_productLanguage]

/-- A tagged-sum verifier language on ordinary paired input, including the
false-padding test. False chooses `L` and true chooses `R`. -/
def taggedLanguage (L R : Language) : Language :=
  {z | (∀ b ∈ (pairSnd z).drop ((pairSnd z).length / 2 + 1), b = false) ∧
    if (pairSnd z)[0]?.getD false then
      pair (pairFst z) (((pairSnd z).drop 1).take ((pairSnd z).length / 2)) ∈ R
    else
      pair (pairFst z) (((pairSnd z).drop 1).take ((pairSnd z).length / 2)) ∈ L}

theorem getD_ofFn_taggedTag {T : ℕ} (hT : 1 ≤ T) (w : Fin (2 * T) → Bool) :
    (List.ofFn w)[0]?.getD false = taggedTag hT w := by
  simp [taggedTag, show 0 < 2 * T by omega]

theorem take_drop_ofFn_taggedPayload {T : ℕ} (hT : 1 ≤ T)
    (w : Fin (2 * T) → Bool) :
    ((List.ofFn w).drop 1).take T = List.ofFn (taggedPayload hT w) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hi'
    simp [taggedPayload]

theorem taggedPadding_iff_list {T : ℕ} (w : Fin (2 * T) → Bool) :
    taggedPadding w ↔ ∀ b ∈ (List.ofFn w).drop (T + 1), b = false := by
  constructor
  · intro hw b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    simp only [List.length_drop, List.length_ofFn] at hi
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact hw ⟨T + 1 + i, by omega⟩ (show T < T + 1 + i by omega)
  · intro hw i hi
    apply hw (w i)
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val - (T + 1), ?_, ?_⟩
    · simp only [List.length_drop, List.length_ofFn]
      omega
    · simp only [List.getElem_drop, List.getElem_ofFn]
      congr 1
      apply Fin.ext
      change T + 1 + (i.val - (T + 1)) = i.val
      omega

theorem pair_mem_taggedLanguage (L R : Language) (x : List Bool) {T : ℕ}
    (hT : 1 ≤ T) (w : Fin (2 * T) → Bool) :
    pair x (List.ofFn w) ∈ taggedLanguage L R ↔ taggedPadding w ∧
      (if taggedTag hT w then pair x (List.ofFn (taggedPayload hT w)) ∈ R
        else pair x (List.ofFn (taggedPayload hT w)) ∈ L) := by
  have hhalf : 2 * T / 2 = T := by omega
  simp only [taggedLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair,
    List.length_ofFn, hhalf]
  rw [getD_ofFn_taggedTag hT, take_drop_ofFn_taggedPayload hT, ← taggedPadding_iff_list]

/-- Disjoint tagged copies of two witness sets. The membership theorem below
includes rejection of every word with nonzero padding. -/
def taggedWitnesses {T : ℕ} (S R : Finset (Fin T → Bool)) :
    Finset (Fin (2 * T) → Bool) :=
  S.image (taggedEncode false) ∪ R.image (taggedEncode true)

@[simp] theorem mem_taggedWitnesses {T : ℕ} (hT : 1 ≤ T)
    (S R : Finset (Fin T → Bool)) (w : Fin (2 * T) → Bool) :
    w ∈ taggedWitnesses S R ↔ taggedPadding w ∧
      (if taggedTag hT w then taggedPayload hT w ∈ R else taggedPayload hT w ∈ S) := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
      simp [hu]
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
      simp [hu]
  · rintro ⟨hpad, hmem⟩
    cases htag : taggedTag hT w
    · apply Finset.mem_union.mpr
      left
      refine Finset.mem_image.mpr ⟨taggedPayload hT w, ?_, ?_⟩
      · simpa [htag] using hmem
      · simpa [htag] using taggedEncode_decode hT w hpad
    · apply Finset.mem_union.mpr
      right
      refine Finset.mem_image.mpr ⟨taggedPayload hT w, ?_, ?_⟩
      · simpa [htag] using hmem
      · simpa [htag] using taggedEncode_decode hT w hpad

theorem not_mem_taggedWitnesses_of_nonzero_padding {T : ℕ} (hT : 1 ≤ T)
    (S R : Finset (Fin T → Bool)) (w : Fin (2 * T) → Bool)
    (i : Fin (2 * T)) (hi : T < i.val) (hbit : w i = true) :
    w ∉ taggedWitnesses S R := by
  intro hw
  have hfalse := ((mem_taggedWitnesses hT S R w).mp hw).1 i hi
  simp [hbit] at hfalse

theorem taggedImages_disjoint {T : ℕ} (hT : 1 ≤ T) (S R : Finset (Fin T → Bool)) :
    Disjoint (S.image (taggedEncode false)) (R.image (taggedEncode true)) := by
  apply Finset.disjoint_left.mpr
  intro w hS hR
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hS
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hR
  have h := congrArg (taggedTag hT) (hu.trans hv.symm)
  simp at h

theorem card_taggedWitnesses {T : ℕ} (hT : 1 ≤ T) (S R : Finset (Fin T → Bool)) :
    (taggedWitnesses S R).card = S.card + R.card := by
  rw [taggedWitnesses, Finset.card_union_of_disjoint (taggedImages_disjoint hT S R),
    Finset.card_image_of_injective _ (taggedEncode_injective hT false),
    Finset.card_image_of_injective _ (taggedEncode_injective hT true)]

theorem card_verifierWitnesses_taggedLanguage (L R : Language) (x : List Bool)
    {T : ℕ} (hT : 1 ≤ T) :
    (verifierWitnesses (taggedLanguage L R) x (2 * T)).card =
      (verifierWitnesses L x T).card + (verifierWitnesses R x T).card := by
  rw [← card_taggedWitnesses hT]
  congr 1
  ext w
  simp [mem_taggedWitnesses hT, pair_mem_taggedLanguage L R x hT]

end Toda.Counting.ClosureWitnesses

import Toda.Counting.BoundedProduct.Witnesses
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity

/-!
# Exact signed products of witness counts

Each block has one sign bit and a payload. False selects a positive witness;
true selects a negative witness. The parity of the number of true sign bits
separates the positive and negative terms in the product expansion. Every
array has one flattened representation, including empty arrays and payloads.
-/

namespace Toda.Counting.SignedProductWitnesses

open Complexity BoundedProduct

def tag {r : ℕ} (w : Fin (r + 1) → Bool) : Bool := w 0

def payload {r : ℕ} (w : Fin (r + 1) → Bool) : Fin r → Bool :=
  fun i => w i.succ

def encode {r : ℕ} (b : Bool) (w : Fin r → Bool) : Fin (r + 1) → Bool :=
  Fin.cons b w

@[simp] theorem tag_encode {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    tag (encode b w) = b := by simp [tag, encode]

@[simp] theorem payload_encode {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    payload (encode b w) = w := by
  funext i
  simp [payload, encode]

@[simp] theorem encode_decode {r : ℕ} (w : Fin (r + 1) → Bool) :
    encode (tag w) (payload w) = w := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [encode, tag, payload]

theorem encode_injective {r : ℕ} (b : Bool) : Function.Injective (encode (r := r) b) := by
  intro u v h
  simpa using congrArg payload h

/-- Disjoint tagged copies of the positive and negative payload sets. -/
def signedBlock {r : ℕ} (S R : Finset (Fin r → Bool)) : Finset (Fin (r + 1) → Bool) :=
  S.image (encode false) ∪ R.image (encode true)

@[simp] theorem mem_signedBlock {r : ℕ} (S R : Finset (Fin r → Bool))
    (w : Fin (r + 1) → Bool) :
    w ∈ signedBlock S R ↔ if tag w then payload w ∈ R else payload w ∈ S := by
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      simpa using hu
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      simpa using hu
  · intro hw
    cases htag : tag w
    · apply Finset.mem_union.mpr
      left
      refine Finset.mem_image.mpr ⟨payload w, by simpa [htag] using hw, ?_⟩
      simpa [htag] using encode_decode w
    · apply Finset.mem_union.mpr
      right
      refine Finset.mem_image.mpr ⟨payload w, by simpa [htag] using hw, ?_⟩
      simpa [htag] using encode_decode w

theorem tagged_images_disjoint {r : ℕ} (S R : Finset (Fin r → Bool)) :
    Disjoint (S.image (encode false)) (R.image (encode true)) := by
  apply Finset.disjoint_left.mpr
  intro w hS hR
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hS
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hR
  have h := congrArg tag (hu.trans hv.symm)
  simp at h

def sign {r : ℕ} (w : Fin (r + 1) → Bool) : ℤ := if tag w then -1 else 1

theorem sum_sign_signedBlock {r : ℕ} (S R : Finset (Fin r → Bool)) :
    ∑ w ∈ signedBlock S R, sign w = (S.card : ℤ) - R.card := by
  rw [signedBlock, Finset.sum_union (tagged_images_disjoint S R)]
  rw [Finset.sum_image (fun _ _ _ _ h => encode_injective false h),
    Finset.sum_image (fun _ _ _ _ h => encode_injective true h)]
  simp [sign, sub_eq_add_neg]

/-- The number of negative tags in an array. -/
def tagCount {n r : ℕ} (v : Fin n → Fin (r + 1) → Bool) : ℕ :=
  (Finset.univ.filter fun i => tag (v i) = true).card

theorem prod_sign_eq {n r : ℕ} (v : Fin n → Fin (r + 1) → Bool) :
    ∏ i, sign (v i) = if tagCount v % 2 = 0 then (1 : ℤ) else -1 := by
  have hprod : ∏ i, sign (v i) = (-1 : ℤ) ^ tagCount v := by
    simp [sign, tagCount, Finset.prod_ite]
  rw [hprod, neg_one_pow_eq_pow_mod_two]
  have hmod := Nat.mod_lt (tagCount v) (by omega : 0 < 2)
  by_cases h : tagCount v % 2 = 0
  · simp [h]
  · have h' : tagCount v % 2 = 1 := by omega
    simp [h']

/-- The difference between the two parity-filtered array counts is exactly
the product of the signed payload counts. -/
theorem signed_pi_card {n r : ℕ} (S R : Fin n → Finset (Fin r → Bool)) :
    (((Fintype.piFinset fun i => signedBlock (S i) (R i)).filter
      fun v => tagCount v % 2 = 0).card : ℤ) -
    ((Fintype.piFinset fun i => signedBlock (S i) (R i)).filter
      fun v => tagCount v % 2 = 1).card =
      ∏ i, (((S i).card : ℤ) - (R i).card) := by
  classical
  let V := Fintype.piFinset fun i => signedBlock (S i) (R i)
  have hsign : (∑ v ∈ V, ∏ i, sign (v i)) =
      ((V.filter fun v => tagCount v % 2 = 0).card : ℤ) -
        (V.filter fun v => tagCount v % 2 = 1).card := by
    simp_rw [prod_sign_eq]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg, sub_eq_add_neg]
    have hfilter : V.filter (fun v => ¬tagCount v % 2 = 0) =
        V.filter (fun v => tagCount v % 2 = 1) := by
      ext v
      simp only [Finset.mem_filter]
      have hmod := Nat.mod_lt (tagCount v) (by omega : 0 < 2)
      exact and_congr_right fun _ => by omega
    rw [hfilter]
  rw [← hsign, ← Finset.prod_univ_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact sum_sign_signedBlock (S i) (R i)

/-- Flattened arrays with valid signed payloads and the specified parity. -/
def signedWitnesses {n r : ℕ} (S R : Fin n → Finset (Fin r → Bool)) (negative : Bool) :
    Finset (Fin (n * (r + 1)) → Bool) :=
  ((Fintype.piFinset fun i => signedBlock (S i) (R i)).filter
    fun v => tagCount v % 2 = negative.toNat).image flatten

@[simp] theorem mem_signedWitnesses {n r : ℕ} (S R : Fin n → Finset (Fin r → Bool))
    (negative : Bool) (w : Fin (n * (r + 1)) → Bool) :
    w ∈ signedWitnesses S R negative ↔
      (∀ i, if tag (block w i) then payload (block w i) ∈ R i
        else payload (block w i) ∈ S i) ∧ tagCount (block w) % 2 = negative.toNat := by
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa [Fintype.mem_piFinset] using hv
  · rintro ⟨hmem, hsign⟩
    exact Finset.mem_image.mpr ⟨block w, by simpa [Fintype.mem_piFinset] using
      (And.intro hmem hsign), flatten_block w⟩

theorem card_signedWitnesses {n r : ℕ} (S R : Fin n → Finset (Fin r → Bool)) :
    ((signedWitnesses S R false).card : ℤ) - (signedWitnesses S R true).card =
      ∏ i, (((S i).card : ℤ) - (R i).card) := by
  simp only [signedWitnesses, Finset.card_image_of_injective _ flatten_injective,
    Bool.toNat_false, Bool.toNat_true]
  exact signed_pi_card S R

/-- Check each indexed signed block and the parity of its sign tags. The
definition is total on arbitrary strings and arbitrary bounds. -/
def language (L R : Language) (q r : List Bool → ℕ) (negative : Bool) : Language :=
  {z | (∀ i < q (pairFst z),
    if (pairSnd z)[i * (r (pairFst z) + 1)]?.getD false then
      pair (pair (pairFst z) (List.replicate i true))
        (((pairSnd z).drop (i * (r (pairFst z) + 1) + 1)).take (r (pairFst z))) ∈ R
    else
      pair (pair (pairFst z) (List.replicate i true))
        (((pairSnd z).drop (i * (r (pairFst z) + 1) + 1)).take (r (pairFst z))) ∈ L) ∧
    ((Finset.range (q (pairFst z))).filter fun i =>
      (pairSnd z)[i * (r (pairFst z) + 1)]?.getD false = true).card % 2 = negative.toNat}

theorem getD_tag {n r : ℕ} (w : Fin (n * (r + 1)) → Bool) (i : Fin n) :
    (List.ofFn w)[i.val * (r + 1)]?.getD false = tag (block w i) := by
  have hi : i.val * (r + 1) < n * (r + 1) := Nat.mul_lt_mul_of_pos_right i.isLt (by omega)
  simp only [List.getElem?_ofFn, hi, dite_true, Option.getD_some, tag, block]
  congr 1
  apply Fin.ext
  change i.val * (r + 1) = 0 + (r + 1) * i.val
  simp [Nat.mul_comm]

theorem slice_payload {n r : ℕ} (w : Fin (n * (r + 1)) → Bool) (i : Fin n) :
    ((List.ofFn w).drop (i.val * (r + 1) + 1)).take r =
      List.ofFn (payload (block w i)) := by
  have hi : (i.val + 1) * (r + 1) ≤ n * (r + 1) :=
    Nat.mul_le_mul_right (r + 1) i.isLt
  rw [Nat.add_mul, Nat.one_mul] at hi
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro j hj hj'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, payload, block]
    congr 1
    apply Fin.ext
    change i.val * (r + 1) + 1 + j = j + 1 + (r + 1) * i.val
    ac_rfl

theorem tagCount_eq_range {n r : ℕ} (w : Fin (n * (r + 1)) → Bool) :
    tagCount (block w) = ((Finset.range n).filter fun i =>
      (List.ofFn w)[i * (r + 1)]?.getD false = true).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_range, getD_tag]
    exact ⟨i.isLt, hi⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← getD_tag w ⟨i, hi.1⟩]
    exact hi.2

theorem pair_mem_language (L R : Language) (q r : List Bool → ℕ) (negative : Bool)
    (x : List Bool) (w : Fin (q x * (r x + 1)) → Bool) :
    pair x (List.ofFn w) ∈ language L R q r negative ↔
      (∀ i : Fin (q x), if tag (block w i) then
        pair (pair x (List.replicate i.val true)) (List.ofFn (payload (block w i))) ∈ R
      else
        pair (pair x (List.replicate i.val true)) (List.ofFn (payload (block w i))) ∈ L) ∧
      tagCount (block w) % 2 = negative.toNat := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
  rw [← tagCount_eq_range]
  apply and_congr_left
  intro _
  constructor
  · intro h i
    simpa only [getD_tag, slice_payload] using h i.val i.isLt
  · intro h i hi
    simpa only [getD_tag w ⟨i, hi⟩, slice_payload w ⟨i, hi⟩] using h ⟨i, hi⟩

/-- The two verifier counts realize the signed product exactly. -/
theorem card_verifierWitnesses (L R : Language) (q r : List Bool → ℕ) (x : List Bool) :
    ((verifierWitnesses (language L R q r false) x (q x * (r x + 1))).card : ℤ) -
      (verifierWitnesses (language L R q r true) x (q x * (r x + 1))).card =
    ∏ i : Fin (q x),
      (((verifierWitnesses L (pair x (List.replicate i.val true)) (r x)).card : ℤ) -
        (verifierWitnesses R (pair x (List.replicate i.val true)) (r x)).card) := by
  classical
  have hset (b : Bool) : verifierWitnesses (language L R q r b) x (q x * (r x + 1)) =
      signedWitnesses
        (fun i : Fin (q x) => verifierWitnesses L (pair x (List.replicate i.val true)) (r x))
        (fun i : Fin (q x) => verifierWitnesses R (pair x (List.replicate i.val true)) (r x)) b := by
    ext w
    simp [pair_mem_language]
  rw [hset false, hset true, card_signedWitnesses]

end Toda.Counting.SignedProductWitnesses

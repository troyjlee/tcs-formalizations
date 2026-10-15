import Toda.Counting.GapPClosure
import Toda.Counting.FPSubstitution
import Toda.Counting.GapPBoundedProduct
import Toda.Counting.BoundedSum
import Toda.Counting.DeterministicBranch
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Canonical parity counting and its uniform closure

`ParityP` is defined through odd accepting-leaf counts of the canonical #P
machines. Differences of counts give the same class. Uniform XOR ranges over
all strings of a polynomial-time unary width; uniform conjunction and
disjunction range over only polynomially many unary indices.
-/

namespace Toda.Parity

open Complexity Counting

/-- Languages recognized by odd accepting-leaf counts of polynomial-time
nondeterministic machines. -/
def ParityP : Set Language :=
  {L | ∃ f : List Bool → ℕ, f ∈ SharpP ∧ ∀ x, x ∈ L ↔ f x % 2 = 1}

/-- The canonical #P definition, with `Odd` in place of its remainder test. -/
theorem mem_parityP_iff_sharpP_odd {L : Language} :
    L ∈ ParityP ↔ ∃ f : List Bool → ℕ, f ∈ SharpP ∧ ∀ x, x ∈ L ↔ Odd (f x) := by
  simp only [ParityP, Set.mem_ofPred_eq, Nat.odd_iff]

/-- GapP has exactly the same parity power: subtraction and addition have
identical remainders modulo two. -/
theorem mem_parityP_iff_gapP {L : Language} :
    L ∈ ParityP ↔ ∃ f : List Bool → ℤ, f ∈ GapP ∧ ∀ x, x ∈ L ↔ f x % 2 = 1 := by
  constructor
  · rintro ⟨f, hf, hL⟩
    refine ⟨fun x => (f x : ℤ), sharpP_cast_mem_gapP hf, fun x => ?_⟩
    rw [hL x]
    change f x % 2 = 1 ↔ (f x : ℤ) % 2 = 1
    exact_mod_cast (Iff.rfl : f x % 2 = 1 ↔ f x % 2 = 1)
  · rintro ⟨f, ⟨a, b, ha, hb, hab⟩, hL⟩
    refine ⟨fun x => a x + b x, sharpP_add ha hb, fun x => ?_⟩
    rw [hL x, hab x]
    dsimp
    omega

theorem mem_parityP_iff_gapP_odd {L : Language} :
    L ∈ ParityP ↔ ∃ f : List Bool → ℤ, f ∈ GapP ∧ ∀ x, x ∈ L ↔ Odd (f x) := by
  simp only [mem_parityP_iff_gapP, Int.odd_iff]

/-- Deterministic polynomial time embeds using the exact zero/one accepting
leaf indicator. -/
theorem P_subset_parityP : Complexity.P ⊆ ParityP := by
  intro L hL
  refine ⟨DeterministicBranch.indicator L,
    DeterministicBranch.indicator_mem_sharpP L hL, fun x => ?_⟩
  classical
  by_cases hx : x ∈ L <;> simp [DeterministicBranch.indicator, hx]

/-- Flipping parity needs one additional accepting leaf. -/
theorem compl_mem_parityP {L : Language} (hL : L ∈ ParityP) : Lᶜ ∈ ParityP := by
  obtain ⟨f, hf, hL⟩ := hL
  refine ⟨fun x => f x + 1, sharpP_add hf (sharpP_const 1), fun x => ?_⟩
  change ¬ x ∈ L ↔ _
  rw [hL x]
  dsimp
  omega

@[simp] theorem compl_mem_parityP_iff {L : Language} : Lᶜ ∈ ParityP ↔ L ∈ ParityP :=
  ⟨fun h => by simpa using compl_mem_parityP h, compl_mem_parityP⟩

/-- Products of counts implement conjunction. -/
theorem inter_mem_parityP {L R : Language} (hL : L ∈ ParityP) (hR : R ∈ ParityP) :
    L ∩ R ∈ ParityP := by
  obtain ⟨f, hf, hL⟩ := mem_parityP_iff_sharpP_odd.mp hL
  obtain ⟨g, hg, hR⟩ := mem_parityP_iff_sharpP_odd.mp hR
  apply mem_parityP_iff_sharpP_odd.mpr
  exact ⟨fun x => f x * g x, sharpP_mul hf hg, fun x => by
    simp only [Set.mem_inter_iff, hL x, hR x, Nat.odd_mul]⟩

/-- De Morgan duality implements disjunction. -/
theorem union_mem_parityP {L R : Language} (hL : L ∈ ParityP) (hR : R ∈ ParityP) :
    L ∪ R ∈ ParityP := by
  simpa only [Set.compl_inter, compl_compl] using
    compl_mem_parityP (inter_mem_parityP (compl_mem_parityP hL) (compl_mem_parityP hR))

/-- Addition of counts implements exclusive-or. -/
theorem xor_mem_parityP {L R : Language} (hL : L ∈ ParityP) (hR : R ∈ ParityP) :
    {x | Xor (x ∈ L) (x ∈ R)} ∈ ParityP := by
  obtain ⟨f, hf, hL⟩ := hL
  obtain ⟨g, hg, hR⟩ := hR
  refine ⟨fun x => f x + g x, sharpP_add hf hg, fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, hL x, hR x, Xor]
  omega

/-- Actual polynomial-time input preprocessing preserves canonical parity
counting; no counting-valued composition is assumed. -/
theorem preimage_mem_parityP {L : Language} {h : List Bool → List Bool}
    (hL : L ∈ ParityP) (hh : h ∈ FP) : h ⁻¹' L ∈ ParityP := by
  obtain ⟨f, hf, hL⟩ := hL
  exact ⟨fun x => f (h x), sharpP_comp_fp hf hh, fun x => hL (h x)⟩

/-- An odd number of successful exact-width witnesses. -/
noncomputable def xorBitsLanguage (L : Language) (q : List Bool → ℕ) : Language := by
  classical
  exact {x | ((Finset.univ.filter fun y : Fin (q x) → Bool =>
    pair x (List.ofFn y) ∈ L).card) % 2 = 1}

/-- Uniform parity quantification over all strings of a unary-computable
width preserves the canonical class. This may contain exponentially many
summands; the counting machine guesses the summation string. -/
theorem xorBitsLanguage_mem_parityP {L : Language} {q : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) : xorBitsLanguage L q ∈ ParityP := by
  classical
  obtain ⟨f, hf, hL⟩ := mem_parityP_iff_sharpP_odd.mp hL
  apply mem_parityP_iff_sharpP_odd.mpr
  refine ⟨fun x => ∑ y : Fin (q x) → Bool, f (pair x (List.ofFn y)),
    sharpP_sum_bits hf hq, fun x => ?_⟩
  rw [Finset.odd_sum_iff_odd_card_odd]
  simp only [xorBitsLanguage, Set.mem_ofPred_eq, ← Nat.odd_iff, ← hL]

/-- Conjunction over a polynomially bounded family indexed in unary. -/
def forallIndexLanguage (L : Language) (q : List Bool → ℕ) : Language :=
  {x | ∀ i : Fin (q x), pair x (List.replicate i.val true) ∈ L}

/-- Disjunction over a polynomially bounded family indexed in unary. -/
def existsIndexLanguage (L : Language) (q : List Bool → ℕ) : Language :=
  {x | ∃ i : Fin (q x), pair x (List.replicate i.val true) ∈ L}

/-- A finite integer product is odd exactly when every factor is odd. -/
theorem odd_finset_prod_iff {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert hi, Int.odd_mul, ih]

/-- Uniform conjunction over polynomially many factors follows from the
proved canonical GapP product compiler. -/
theorem forallIndexLanguage_mem_parityP {L : Language} {q : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) : forallIndexLanguage L q ∈ ParityP := by
  obtain ⟨f, hf, hL⟩ := mem_parityP_iff_gapP_odd.mp hL
  apply mem_parityP_iff_gapP_odd.mpr
  refine ⟨fun x => ∏ i : Fin (q x), f (pair x (List.replicate i.val true)),
    gapP_bounded_prod hf hq, fun x => ?_⟩
  simp only [forallIndexLanguage, Set.mem_ofPred_eq, odd_finset_prod_iff,
    Finset.mem_univ, forall_const, hL]

/-- Uniform disjunction over polynomially many indices follows by complement.
The empty family is false, while the empty conjunction is true. -/
theorem existsIndexLanguage_mem_parityP {L : Language} {q : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) : existsIndexLanguage L q ∈ ParityP := by
  have h := compl_mem_parityP
    (forallIndexLanguage_mem_parityP (compl_mem_parityP hL) hq)
  convert h using 1
  ext x
  simp [existsIndexLanguage, forallIndexLanguage]

end Toda.Parity

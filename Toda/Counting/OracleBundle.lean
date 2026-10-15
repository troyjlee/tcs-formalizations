import Toda.Counting.AmplifiedCount
import Toda.Counting.FPSubstitution
import Toda.Counting.GapPConditional
import Complexitylib.Classes.P.StringAccess

/-!
# One #P function for two counting queries

Tagging the ordinary input selects either constituent of a GapP difference.
The bundled function is itself in canonical #P, and each query constructor is
an actual polynomial-time string function. The definitions are total on every
string; the round-trip identities only use the two well-formed query encodings.

This is a counting-function interface. It does not assert an oracle-machine
simulation or the runtime of subsequent arithmetic on binary oracle answers.
-/

namespace Toda.Counting

open Complexity

/-- Encode one of two oracle queries, preserving the source input as the first
component of the ordinary pairing codec. -/
def taggedInput (bit : Bool) (x : List Bool) : List Bool := pair x [bit]

/-- Each query has length linear in the original input length. -/
@[simp] theorem taggedInput_length (bit : Bool) (x : List Bool) :
    (taggedInput bit x).length = 2 * x.length + 3 := by
  simp [taggedInput, Nat.add_assoc]

/-- The first query component recovers the original input exactly. -/
@[simp] theorem pairFst_taggedInput (bit : Bool) (x : List Bool) :
    pairFst (taggedInput bit x) = x := by
  simp [taggedInput]

/-- The second query component recovers the one-bit tag exactly. -/
@[simp] theorem pairSnd_taggedInput (bit : Bool) (x : List Bool) :
    pairSnd (taggedInput bit x) = [bit] := by
  simp [taggedInput]

/-- Preparing a query for either fixed tag is polynomial-time computable. -/
theorem taggedInput_mem_FP (bit : Bool) : taggedInput bit ∈ FP :=
  mem_FP_pair id_mem_FP (constFn_mem_FP [bit])

/-- One total counting function serves both queries. An absent tag defaults to
the false branch; extra tag bits are ignored. -/
def taggedCounting (a b : List Bool → ℕ) (z : List Bool) : ℕ :=
  if (pairSnd z)[0]?.getD false then b (pairFst z) else a (pairFst z)

/-- The false tag selects the first counting function. -/
@[simp] theorem taggedCounting_false (a b : List Bool → ℕ) (x : List Bool) :
    taggedCounting a b (taggedInput false x) = a x := by
  simp [taggedCounting]

/-- The true tag selects the second counting function. -/
@[simp] theorem taggedCounting_true (a b : List Bool → ℕ) (x : List Bool) :
    taggedCounting a b (taggedInput true x) = b x := by
  simp [taggedCounting]

/-- Bundling two canonical #P functions preserves canonical #P. Both the
projection and the branch predicate have actual polynomial-time machines. -/
theorem taggedCounting_mem_sharpP {a b : List Bool → ℕ}
    (ha : a ∈ SharpP) (hb : b ∈ SharpP) : taggedCounting a b ∈ SharpP :=
  sharpP_ite (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0))
    (sharpP_comp_fp hb pairFst_mem_FP) (sharpP_comp_fp ha pairFst_mem_FP)

/-- Every GapP function is the difference of two tagged queries to one #P
function. False selects the positive constituent and true the negative one. -/
theorem gapP_exists_single_sharpP_difference {f : List Bool → ℤ}
    (hf : f ∈ GapP) :
    ∃ F : List Bool → ℕ, F ∈ SharpP ∧ ∀ x,
      f x = (F (taggedInput false x) : ℤ) - (F (taggedInput true x) : ℤ) := by
  obtain ⟨a, b, ha, hb, hcount⟩ := hf
  exact ⟨taggedCounting a b, taggedCounting_mem_sharpP ha hb,
    fun x => by simpa using hcount x⟩

/-- Conversely, the difference of the two fixed tagged queries is GapP. -/
theorem gapP_single_sharpP_difference {F : List Bool → ℕ} (hF : F ∈ SharpP) :
    (fun x => (F (taggedInput false x) : ℤ) - (F (taggedInput true x) : ℤ)) ∈
      GapP :=
  ⟨(fun x => F (taggedInput false x)), (fun x => F (taggedInput true x)),
    sharpP_comp_fp hF (taggedInput_mem_FP false),
    sharpP_comp_fp hF (taggedInput_mem_FP true), fun _ => rfl⟩

/-- The two-query representation characterizes canonical GapP. -/
theorem gapP_iff_exists_single_sharpP_difference {f : List Bool → ℤ} :
    f ∈ GapP ↔ ∃ F : List Bool → ℕ, F ∈ SharpP ∧ ∀ x,
      f x = (F (taggedInput false x) : ℤ) - (F (taggedInput true x) : ℤ) := by
  refine ⟨gapP_exists_single_sharpP_difference, ?_⟩
  rintro ⟨F, hF, heq⟩
  have hf := gapP_single_sharpP_difference hF
  convert hf using 1
  exact funext heq

/-- One canonical #P oracle function supplies the exact odd-value count via
two fixed tagged queries, integer subtraction, and a power-of-two remainder. -/
theorem exists_single_sharpP_odd_count_encoding
    {f : List Bool → ℤ} {q : List Bool → ℕ} (hf : f ∈ GapP) (hq : UnaryFn q) :
    ∃ F : List Bool → ℕ, F ∈ SharpP ∧ ∀ x,
      ((F (taggedInput false x) : ℤ) - (F (taggedInput true x) : ℤ)) %
          (2 ^ (q x + 1)) =
        ((Finset.univ.filter fun y : Fin (q x) → Bool =>
          f (pair x (List.ofFn y)) % 2 = 1).card : ℤ) := by
  obtain ⟨a, b, ha, hb, hcount⟩ :=
    exists_sharpP_difference_odd_count_encoding hf hq
  exact ⟨taggedCounting a b, taggedCounting_mem_sharpP ha hb,
    fun x => by simpa using hcount x⟩

end Toda.Counting

import Toda.Oracle.BitOracle
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.Cobham.Internal.StringOps

/-!
# Polynomial-time access to a binary oracle answer

An index may have exponentially large value relative to its encoded length.
Decode it only up to the answer length, and check its canonical encoding at
that bounded value. If the cap binds, the requested bit is false regardless
of canonicality. This gives a total FP implementation of the bit interface
from an already supplied binary answer, including malformed queries.
-/

namespace Toda.Oracle

open Complexity

/-- Equality of two polynomial-time string outputs is polynomial-time. -/
theorem string_eq_fpPred {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    FPPred fun z => a z = b z := by
  have hflag : (fun z => [decide (a z = b z)]) ∈ FP := by
    refine mem_FP_of_eq (eqFlagFn_mem_FP ha hb) fun z => ?_
    by_cases h : a z = b z
    · simpa only [decide_eq_true h] using (Cobham.eqFlag_eq_true_iff _ _).mpr h
    · rw [decide_eq_false h]
      exact (Cobham.eqFlag_flag _ _).resolve_left
        (fun heq => h ((Cobham.eqFlag_eq_true_iff _ _).mp heq))
  exact (FPPred.of_flag hflag).of_iff fun _ => by simp

/-- Read a bit using a capped index and an efficient canonicality check. -/
def readAnswer (query answer : List Bool) : Bool :=
  let index := min (Nat.fromBitsLE (pairSnd query)) answer.length
  if query = pair (pairFst query) (pairSnd query) ∧
      pairSnd query = index.bits then
    answer[index]?.getD false
  else false

/-- The cap changes no observable result, including for invalid encodings. -/
theorem readAnswer_eq (query answer : List Bool) :
    readAnswer query answer =
      if ValidBitQuery query then
        answer[Nat.fromBitsLE (pairSnd query)]?.getD false
      else false := by
  by_cases hindex : Nat.fromBitsLE (pairSnd query) ≤ answer.length
  · simp only [readAnswer, min_eq_left hindex, ValidBitQuery]
    rfl
  · have hlength : answer.length ≤ Nat.fromBitsLE (pairSnd query) := by omega
    simp [readAnswer, min_eq_right hlength,
      List.getElem?_eq_none hlength]

/-- With a correct binary answer, this is exactly the specified Boolean
oracle, on every query string. The answer need not have minimal width. -/
theorem readAnswer_eq_bitOracle (F : List Bool → ℕ) (query answer : List Bool)
    (hanswer : Nat.fromBitsLE answer = F (pairFst query)) :
    readAnswer query answer = bitOracle F query := by
  rw [readAnswer_eq]
  simp only [bitOracle, getD_eq_decide_fromBitsLE, hanswer]

/-- Reading from FP-prepared query and answer strings is an actual FP
computation. Only an index bounded by the answer length is written in unary. -/
theorem readAnswer_mem_FP {query answer : List Bool → List Bool}
    (hquery : query ∈ FP) (hanswer : answer ∈ FP) :
    (fun z => [readAnswer (query z) (answer z)]) ∈ FP := by
  have hfirst := mem_FP_comp hquery pairFst_mem_FP
  have hsecond := mem_FP_comp hquery pairSnd_mem_FP
  have hindex := UnaryFn.fromBitsLE_min hsecond (UnaryFn.length hanswer)
  have hpair := string_eq_fpPred hquery (mem_FP_pair hfirst hsecond)
  have hcanonical := string_eq_fpPred hsecond (bits_mem_FP hindex)
  refine mem_FP_of_eq ((hpair.and hcanonical).ite_mem_FP
    (getBit_mem_FP hanswer hindex) (constFn_mem_FP [false])) fun z => ?_
  simp only [readAnswer, Function.comp_apply]
  split <;> rfl

/-- Ordinary paired-input version for use as a machine subroutine. -/
def encodedReadAnswer (input : List Bool) : List Bool :=
  [readAnswer (pairFst input) (pairSnd input)]

theorem encodedReadAnswer_mem_FP : encodedReadAnswer ∈ FP :=
  readAnswer_mem_FP pairFst_mem_FP pairSnd_mem_FP

@[simp] theorem encodedReadAnswer_pair (query answer : List Bool) :
    encodedReadAnswer (pair query answer) = [readAnswer query answer] := by
  simp [encodedReadAnswer]

end Toda.Oracle

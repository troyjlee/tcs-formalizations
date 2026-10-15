import Toda.Parity.Class.Postprocessing

/-!
# Uniform strict majority of parity predicates

The postprocessor counts true bits by a bounded ordinary polynomial-time loop.
The transcript theorem then realizes a strict majority of polynomially many
uniformly indexed parity predicates in the same canonical counting class.
-/

namespace Toda.Parity

open Complexity

/-- Number of true bits in a total binary string. -/
def trueBitCount (bits : List Bool) : ℕ :=
  ((Finset.range bits.length).filter fun i => bits[i]?.getD false = true).card

theorem trueBitCount_ofFn {n : ℕ} (bits : Fin n → Bool) :
    trueBitCount (List.ofFn bits) = popCount bits := by
  simp only [trueBitCount, popCount, List.length_ofFn, Finset.card_filter]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Counting true bits is actual unary polynomial-time computation. -/
theorem trueBitCount_unary {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    UnaryFn fun x => trueBitCount (bits x) := by
  refine ((UnaryFn.length hb).count
    (FPPred.getBit (mem_FP_comp pairFst_mem_FP hb) UnaryFn.index)).of_eq fun x => ?_
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  rfl

/-- Strict-majority postprocessor on a paired ordinary input and answer vector. -/
def majorityPostprocessor : Language :=
  {z | (pairSnd z).length < 2 * trueBitCount (pairSnd z)}

theorem majorityPostprocessor_mem_P : majorityPostprocessor ∈ Complexity.P :=
  (FPPred.lt (UnaryFn.length pairSnd_mem_FP)
    ((UnaryFn.const 2).mul (trueBitCount_unary pairSnd_mem_FP))).mem_P

@[simp] theorem pair_mem_majorityPostprocessor {n : ℕ} (x : List Bool)
    (bits : Fin n → Bool) :
    pair x (List.ofFn bits) ∈ majorityPostprocessor ↔ majority bits = true := by
  simp [majorityPostprocessor, trueBitCount_ofFn, majority]

/-- The strict majority of the unary-indexed parity answers. -/
noncomputable def majorityIndexLanguage (L : Language) (q : List Bool → ℕ) : Language :=
  {x | majority (parityAnswers L x (q x)) = true}

/-- Polynomially many uniformly indexed parity queries admit a canonical
parity machine for their strict majority. Ties and the empty vector reject. -/
theorem majorityIndexLanguage_mem_parityP {L : Language} {q : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) : majorityIndexLanguage L q ∈ ParityP := by
  have h := booleanPostprocessLanguage_mem_parityP hL majorityPostprocessor_mem_P hq
  convert h using 1
  ext x
  simp [majorityIndexLanguage, booleanPostprocessLanguage]

end Toda.Parity

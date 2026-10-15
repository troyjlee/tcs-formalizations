import Toda.Counting.VerifierCharacterization
import Toda.Counting.ClosureWitnesses
import Toda.Counting.SharpPAdd.CommonClock
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Verdict

/-!
# Multiplication in the canonical counting class

Split a word of width `2T` into two words of width `T`, and run the two
ordinary polynomial-time verifiers on those words. The splitting and both
verifier calls are compiled by the machine-based `FP` and `P` closure
theorems. Concatenation gives exactly one combined witness for each pair
of accepted witnesses, including when the common width is zero.
-/

namespace Toda.Counting

open Complexity

namespace ClosureWitnesses

/-- The product witness predicate has an actual polynomial-time decider.
Total pair projections and slicing define its behavior on every input. -/
theorem productLanguage_mem_P (L R : Language)
    (hL : L ∈ Complexity.P) (hR : R ∈ Complexity.P) :
    productLanguage L R ∈ Complexity.P := by
  have hhalf : UnaryFn fun z => (pairSnd z).length / 2 :=
    (UnaryFn.length pairSnd_mem_FP).div (UnaryFn.const 2)
  have hleft : (fun z => pair (pairFst z)
      ((pairSnd z).take ((pairSnd z).length / 2))) ∈ FP :=
    mem_FP_pair pairFst_mem_FP (take_mem_FP pairSnd_mem_FP hhalf)
  have hright : (fun z => pair (pairFst z)
      ((pairSnd z).drop ((pairSnd z).length / 2))) ∈ FP :=
    mem_FP_pair pairFst_mem_FP (drop_mem_FP pairSnd_mem_FP hhalf)
  have hLp : FPPred fun z => z ∈ L := mem_P_iff_exists_decisionFn.mp hL
  have hRp : FPPred fun z => z ∈ R := mem_P_iff_exists_decisionFn.mp hR
  exact ((hLp.comp hleft).and (hRp.comp hright)).mem_P

end ClosureWitnesses

/-- Pointwise multiplication preserves the unchanged machine-based #P class. -/
theorem sharpP_mul {f g : List Bool → ℕ} (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    (fun x => f x * g x) ∈ SharpP := by
  obtain ⟨L, R, A, B, _, hL, hR, hcountL, hcountR⟩ :=
    sharpP_pair_exists_positive_polytime_verifiers hf hg
  apply sharpP_iff_exists_polytime_verifier.mpr
  refine ⟨ClosureWitnesses.productLanguage L R, 2 * A, B,
    ClosureWitnesses.productLanguage_mem_P L R hL hR, fun x => ?_⟩
  rw [show polynomialClock (2 * A) B x.length =
    2 * polynomialClock A B x.length by simp only [polynomialClock, Nat.mul_assoc]]
  rw [ClosureWitnesses.card_verifierWitnesses_productLanguage, hcountL x, hcountR x]

end Toda.Counting

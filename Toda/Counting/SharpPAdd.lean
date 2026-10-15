import Toda.Counting.SharpPAdd.CommonClock
import Toda.Counting.ClosureWitnesses
import Toda.Counting.VerifierCharacterization
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Verdict

/-!
# Addition in the canonical machine-based counting class

The sum verifier reads a branch tag, a common-width witness, and uniquely
determined false padding. Every string operation and predicate is compiled
by the upstream polynomial-time function algebra. The witness compiler then
produces a canonical #P machine with exactly the sum of the accepting leaves.
-/

namespace Toda.Counting

open Complexity

private theorem all_false_fppred {bits : List Bool → List Bool}
    (hbits : bits ∈ FP) : FPPred fun z => ∀ b ∈ bits z, b = false := by
  have hone : FPPred fun z => z ∈ Language.containsOne :=
    mem_P_iff_exists_decisionFn.mp containsOne_mem_P
  refine ((hone.comp hbits).not).of_iff fun z => ?_
  change (¬ ∃ b ∈ bits z, b = true) ↔ ∀ b ∈ bits z, b = false
  constructor
  · intro h b hb
    cases b
    · rfl
    · exact False.elim (h ⟨true, hb, rfl⟩)
  · intro h ⟨b, hb, htrue⟩
    have hfalse := h b hb
    simp [htrue] at hfalse

/-- The tagged sum predicate has an actual polynomial-time decider, including
the payload extraction and the false-padding check. -/
theorem taggedLanguage_mem_P {L R : Language}
    (hL : L ∈ Complexity.P) (hR : R ∈ Complexity.P) :
    ClosureWitnesses.taggedLanguage L R ∈ Complexity.P := by
  have hhalf : UnaryFn fun z => (pairSnd z).length / 2 :=
    (UnaryFn.length pairSnd_mem_FP).div (UnaryFn.const 2)
  have hpayload :
      (fun z => ((pairSnd z).drop 1).take ((pairSnd z).length / 2)) ∈ FP :=
    take_mem_FP (drop_mem_FP pairSnd_mem_FP (UnaryFn.const 1)) hhalf
  have hquery := mem_FP_pair pairFst_mem_FP hpayload
  have hleft : FPPred fun z => z ∈ L := mem_P_iff_exists_decisionFn.mp hL
  have hright : FPPred fun z => z ∈ R := mem_P_iff_exists_decisionFn.mp hR
  have htag := FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)
  have hchoice := (htag.and (hright.comp hquery)).or
    (htag.not.and (hleft.comp hquery))
  have hselected : FPPred fun z =>
      if (pairSnd z)[0]?.getD false then
        pair (pairFst z) (((pairSnd z).drop 1).take ((pairSnd z).length / 2)) ∈ R
      else
        pair (pairFst z) (((pairSnd z).drop 1).take ((pairSnd z).length / 2)) ∈ L :=
    hchoice.of_iff fun z => by
      by_cases ht : (pairSnd z)[0]?.getD false = true <;> simp [ht]
  have hpadding := all_false_fppred
    (drop_mem_FP pairSnd_mem_FP (hhalf.add (UnaryFn.const 1)))
  exact (hpadding.and hselected).mem_P

/-- The canonical machine-based class #P is closed under pointwise addition. -/
theorem sharpP_add {f g : List Bool → ℕ} (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    (fun x => f x + g x) ∈ SharpP := by
  obtain ⟨L, R, A, B, hA, hL, hR, hfval, hgval⟩ :=
    sharpP_pair_exists_positive_polytime_verifiers hf hg
  apply sharpP_iff_exists_polytime_verifier.mpr
  refine ⟨ClosureWitnesses.taggedLanguage L R, 2 * A, B,
    taggedLanguage_mem_P hL hR, fun x => ?_⟩
  have hpositive : 1 ≤ polynomialClock A B x.length := by
    unfold polynomialClock
    exact Nat.mul_pos hA (Nat.pow_pos (by omega))
  rw [show polynomialClock (2 * A) B x.length =
      2 * polynomialClock A B x.length by simp [polynomialClock, Nat.mul_assoc],
    ClosureWitnesses.card_verifierWitnesses_taggedLanguage L R x hpositive,
    ← hfval x, ← hgval x]

end Toda.Counting

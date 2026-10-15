import Toda.Counting.VariableWitnesses
import Toda.Counting.VerifierConverse
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Verdict
import Complexitylib.Classes.P.Cobham.Internal

/-!
# Verifiers with a uniformly computable witness width

A unary polynomial-time function may choose the witness width from the whole
input. Its output-length bound supplies a fixed polynomial clock. Unique false
padding embeds the chosen witnesses into that clock without changing their
count, so the existing machine compiler realizes the resulting function in #P.
-/

namespace Toda.Counting

open Complexity

/-- A unary polynomial-time number is bounded by one fixed polynomial clock
in the length of its input. -/
theorem unaryFn_exists_polynomialClock_majorant {q : List Bool → ℕ}
    (hq : UnaryFn q) :
    ∃ A B : ℕ, ∀ x, q x ≤ polynomialClock A B x.length := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hq.mem_FP
  obtain ⟨A, B, hbound⟩ := (PolyBound.eval p).exists_mul_pow_bound
  exact ⟨A, B, fun x => by
    have hx : q x ≤ p.eval x.length := by simpa using hp x
    exact hx.trans (hbound x.length)⟩

/-- A polynomial-time string can be checked for uniquely false padding. -/
theorem allFalse_fppred {bits : List Bool → List Bool}
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

/-- Computing the requested width, slicing the payload, and checking its
false padding are all performed by an ordinary polynomial-time decider. -/
theorem paddingLanguage_mem_P (L : Language) (hL : L ∈ Complexity.P)
    {q : List Bool → ℕ} (hq : UnaryFn q) :
    VariableWitnesses.paddingLanguage L q ∈ Complexity.P := by
  have hwidth := hq.comp pairFst_mem_FP
  have hpadding := allFalse_fppred (drop_mem_FP pairSnd_mem_FP hwidth)
  have hquery := mem_FP_pair pairFst_mem_FP
    (take_mem_FP pairSnd_mem_FP hwidth)
  have htest : FPPred fun z => z ∈ L := mem_P_iff_exists_decisionFn.mp hL
  exact (hpadding.and (htest.comp hquery)).mem_P

/-- Counts of witnesses whose width is computable in unary polynomial time
belong to the unchanged machine-based class #P. -/
theorem verifierWitnesses_count_mem_sharpP_of_unaryFn (L : Language)
    (hL : L ∈ Complexity.P) {q : List Bool → ℕ} (hq : UnaryFn q) :
    (fun x => (verifierWitnesses L x (q x)).card) ∈ SharpP := by
  obtain ⟨A, B, hbound⟩ := unaryFn_exists_polynomialClock_majorant hq
  have hcount := verifierWitnesses_count_mem_sharpP
    (VariableWitnesses.paddingLanguage L q) (paddingLanguage_mem_P L hL hq) A B
  have heq : (fun x => (verifierWitnesses (VariableWitnesses.paddingLanguage L q)
      x (polynomialClock A B x.length)).card) =
      fun x => (verifierWitnesses L x (q x)).card := by
    funext x
    exact VariableWitnesses.card_verifierWitnesses_paddingLanguage L q x (hbound x)
  rw [heq] at hcount
  exact hcount

/-- The verifier for a bounded sum splits off a uniformly computable prefix
and passes the remaining witness to the original verifier. -/
theorem sumLanguage_mem_P (L : Language) (hL : L ∈ Complexity.P)
    {q : List Bool → ℕ} (hq : UnaryFn q) :
    VariableWitnesses.sumLanguage L q ∈ Complexity.P := by
  have hwidth := hq.comp pairFst_mem_FP
  have hinput := mem_FP_pair pairFst_mem_FP
    (take_mem_FP pairSnd_mem_FP hwidth)
  have hquery := mem_FP_pair hinput (drop_mem_FP pairSnd_mem_FP hwidth)
  exact mem_P_preimage hquery hL

end Toda.Counting

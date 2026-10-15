import Toda.Parity.Class
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Verdict

/-!
# Polynomial-time Boolean postprocessing of parity predicates

Guess a vector of proposed answers, verify every position with a canonical
parity predicate, and apply the ordinary P postprocessor to that vector.
Exactly one proposed vector is consistent. Uniform conjunction and parity
quantification therefore realize any polynomial-time Boolean postprocessing
of polynomially many uniformly indexed parity queries.
-/

namespace Toda.Parity

open Complexity Counting

/-- The exact answer vector for the polynomially many unary-indexed queries. -/
noncomputable def parityAnswers (L : Language) (x : List Bool) (width : ℕ) :
    Fin width → Bool := fun i => @decide (pair x (List.replicate i.val true) ∈ L)
      (Classical.propDecidable _)

/-- Apply a Boolean postprocessor to the indexed parity answers. -/
noncomputable def booleanPostprocessLanguage (L B : Language) (q : List Bool → ℕ) :
    Language := {x | pair x (List.ofFn (parityAnswers L x (q x))) ∈ B}

/-- From an input, proposed answer vector, and unary index, recover the
original indexed parity query. -/
def transcriptQuery (w : List Bool) : List Bool :=
  pair (pairFst (pairFst w)) (pairSnd w)

theorem transcriptQuery_mem_FP : transcriptQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

/-- Check that one claimed answer agrees with the actual parity language. -/
def agreementLanguage (L : Language) : Language :=
  {w | ((pairSnd (pairFst w))[(pairSnd w).length]?.getD false = true ↔
    transcriptQuery w ∈ L)}

theorem agreementLanguage_mem_parityP {L : Language} (hL : L ∈ ParityP) :
    agreementLanguage L ∈ ParityP := by
  have hbit : {w | (pairSnd (pairFst w))[(pairSnd w).length]?.getD false = true} ∈
      ParityP := P_subset_parityP ((FPPred.getBit
        (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) UnaryFn.index).mem_P)
  have hquery := preimage_mem_parityP hL transcriptQuery_mem_FP
  have h := compl_mem_parityP (xor_mem_parityP hbit hquery)
  convert h using 1
  ext w
  simp only [agreementLanguage, Set.mem_ofPred_eq, Set.mem_compl_iff,
    Set.mem_preimage, Xor]
  tauto

/-- Every claimed position agrees, with the original input's bound. -/
def validAnswersLanguage (L : Language) (q : List Bool → ℕ) : Language :=
  forallIndexLanguage (agreementLanguage L) (fun z => q (pairFst z))

theorem validAnswersLanguage_mem_parityP {L : Language} {q : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) : validAnswersLanguage L q ∈ ParityP :=
  forallIndexLanguage_mem_parityP (agreementLanguage_mem_parityP hL) hq.lift

/-- There is precisely one consistent answer vector, including at width zero. -/
theorem pair_mem_validAnswersLanguage_iff (L : Language) (q : List Bool → ℕ)
    (x : List Bool) (answers : Fin (q x) → Bool) :
    pair x (List.ofFn answers) ∈ validAnswersLanguage L q ↔
      answers = parityAnswers L x (q x) := by
  classical
  simp only [validAnswersLanguage, forallIndexLanguage, agreementLanguage,
    Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, List.length_replicate,
    transcriptQuery]
  rw [pairFst_pair]
  constructor
  · intro h
    funext i
    have hi := h i
    have hi' : answers i = true ↔ pair x (List.replicate i.val true) ∈ L := by
      simpa using hi
    apply Bool.eq_iff_iff.mpr
    simpa only [parityAnswers, decide_eq_true_eq] using hi'
  · rintro rfl i
    simp [parityAnswers]

/-- Any ordinary polynomial-time Boolean postprocessor of polynomially many
uniformly indexed parity answers is again in canonical ParityP. -/
theorem booleanPostprocessLanguage_mem_parityP {L B : Language} {q : List Bool → ℕ}
    (hL : L ∈ ParityP) (hB : B ∈ Complexity.P) (hq : UnaryFn q) :
    booleanPostprocessLanguage L B q ∈ ParityP := by
  classical
  have h := xorBitsLanguage_mem_parityP
    (inter_mem_parityP (validAnswersLanguage_mem_parityP hL hq) (P_subset_parityP hB)) hq
  convert h using 1
  ext x
  simp only [booleanPostprocessLanguage, xorBitsLanguage, Set.mem_ofPred_eq]
  simp only [Set.mem_inter_iff, pair_mem_validAnswersLanguage_iff]
  simp only [Finset.filter_and, Finset.filter_eq']
  by_cases hb : pair x (List.ofFn (parityAnswers L x (q x))) ∈ B <;> simp [hb]

end Toda.Parity

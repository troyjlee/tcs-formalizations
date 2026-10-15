import Toda.Counting.SignedProductWitnesses
import Toda.Counting.VariableVerifier
import Toda.Counting.UniformClock
import Toda.Counting.FPSubstitution
import Complexitylib.Classes.P.BoundedQuant

/-!
# Uniform products of polynomially many GapP factors

Each factor supplies a tagged positive or negative counting witness. An
ordinary polynomial-time verifier checks all blocks and counts their negative
tags modulo two. Even and odd tag counts give two #P functions; their
difference is the product of the signed factors, including the empty product.
-/

namespace Toda.Counting

open Complexity

namespace SignedProductWitnesses

/-- The selected block checks and parity of negative tags can all be decided
in ordinary polynomial time. -/
theorem language_mem_P (L R : Language) (hL : L ∈ Complexity.P)
    (hR : R ∈ Complexity.P) {q r : List Bool → ℕ} (hq : UnaryFn q)
    (hr : UnaryFn r) (negative : Bool) :
    language L R q r negative ∈ Complexity.P := by
  have hx : (fun u => pairFst (pairFst u)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hw : (fun u => pairSnd (pairFst u)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hwidth : UnaryFn fun u => r (pairFst (pairFst u)) := hr.comp hx
  have hposition := UnaryFn.index.mul (hwidth.add (UnaryFn.const 1))
  have htag := FPPred.getBit hw hposition
  have hinput := mem_FP_pair hx UnaryFn.index.mem_FP
  have hcert := take_mem_FP
    (drop_mem_FP hw (hposition.add (UnaryFn.const 1))) hwidth
  have hquery := mem_FP_pair hinput hcert
  have hLp : FPPred fun u => u ∈ L := mem_P_iff_exists_decisionFn.mp hL
  have hRp : FPPred fun u => u ∈ R := mem_P_iff_exists_decisionFn.mp hR
  have hchoice := (htag.and (hRp.comp hquery)).or (htag.not.and (hLp.comp hquery))
  have hselected : FPPred fun u =>
      if (pairSnd (pairFst u))[(pairSnd u).length *
          (r (pairFst (pairFst u)) + 1)]?.getD false then
        pair (pair (pairFst (pairFst u)) (List.replicate (pairSnd u).length true))
          (((pairSnd (pairFst u)).drop ((pairSnd u).length *
            (r (pairFst (pairFst u)) + 1) + 1)).take (r (pairFst (pairFst u)))) ∈ R
      else
        pair (pair (pairFst (pairFst u)) (List.replicate (pairSnd u).length true))
          (((pairSnd (pairFst u)).drop ((pairSnd u).length *
            (r (pairFst (pairFst u)) + 1) + 1)).take (r (pairFst (pairFst u)))) ∈ L :=
    hchoice.of_iff fun u => by
      by_cases ht : (pairSnd (pairFst u))[(pairSnd u).length *
        (r (pairFst (pairFst u)) + 1)]?.getD false = true <;> simp [ht]
  have hall := FPPred.forall_lt hq.lift hselected
  have hcount := hq.lift.count htag
  have hparity := FPPred.eq (hcount.mod (UnaryFn.const 2))
    (UnaryFn.const negative.toNat)
  exact ((hall.and hparity).of_iff fun z => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    rfl).mem_P

end SignedProductWitnesses

/-- Canonical GapP is closed under a polynomially bounded number of uniformly
indexed factors, with negative values handled by parity of the witness tags. -/
theorem gapP_bounded_prod {f : List Bool → ℤ} {q : List Bool → ℕ}
    (hf : f ∈ GapP) (hq : UnaryFn q) :
    (fun x => ∏ i : Fin (q x), f (pair x (List.replicate i.val true))) ∈ GapP := by
  obtain ⟨a, b, ha, hb, hcount⟩ := hf
  obtain ⟨n, m, N, M, A, B, hN, hM, hacount, hbcount⟩ :=
    sharpP_pair_exists_polynomialClock ha hb
  let L := EncodedVerifier.canonicalLanguage N
  let R := EncodedVerifier.canonicalLanguage M
  let r := pairedClock A B q
  have hL : L ∈ Complexity.P := EncodedVerifier.canonicalLanguage_mem_P N
  have hR : R ∈ Complexity.P := EncodedVerifier.canonicalLanguage_mem_P M
  have hr : UnaryFn r := unaryFn_pairedClock A B hq
  have hwidth := hq.mul (hr.add (UnaryFn.const 1))
  have hpositive := verifierWitnesses_count_mem_sharpP_of_unaryFn
    (SignedProductWitnesses.language L R q r false)
    (SignedProductWitnesses.language_mem_P L R hL hR hq hr false) hwidth
  have hnegative := verifierWitnesses_count_mem_sharpP_of_unaryFn
    (SignedProductWitnesses.language L R q r true)
    (SignedProductWitnesses.language_mem_P L R hL hR hq hr true) hwidth
  refine ⟨(fun x => (verifierWitnesses
      (SignedProductWitnesses.language L R q r false) x (q x * (r x + 1))).card),
    (fun x => (verifierWitnesses
      (SignedProductWitnesses.language L R q r true) x (q x * (r x + 1))).card),
    hpositive, hnegative, fun x => ?_⟩
  dsimp only
  rw [SignedProductWitnesses.card_verifierWitnesses]
  apply Finset.prod_congr rfl
  intro i _
  rw [hcount]
  congr 1
  · exact congrArg (fun z : ℕ => (z : ℤ))
      (canonical_pair_verifier_count N A B hN hacount q x
        (List.replicate i.val true) (by simpa only [List.length_replicate] using i.isLt.le))
  · exact congrArg (fun z : ℕ => (z : ℤ))
      (canonical_pair_verifier_count M A B hM hbcount q x
        (List.replicate i.val true) (by simpa only [List.length_replicate] using i.isLt.le))

/-- The same uniform GapP product written over a natural-number range. -/
theorem gapP_range_prod {f : List Bool → ℤ} {q : List Bool → ℕ}
    (hf : f ∈ GapP) (hq : UnaryFn q) :
    (fun x => ∏ i ∈ Finset.range (q x), f (pair x (List.replicate i true))) ∈ GapP := by
  convert gapP_bounded_prod hf hq using 1
  funext x
  exact Finset.prod_range _

/-- Raising a GapP function to an input-dependent unary polynomial-time
exponent preserves GapP. -/
theorem gapP_pow_unaryFn {f : List Bool → ℤ} {q : List Bool → ℕ}
    (hf : f ∈ GapP) (hq : UnaryFn q) :
    (fun x => f x ^ q x) ∈ GapP := by
  simpa only [pairFst_pair, Fin.prod_const] using
    gapP_bounded_prod (gapP_comp_fp hf pairFst_mem_FP) hq

end Toda.Counting

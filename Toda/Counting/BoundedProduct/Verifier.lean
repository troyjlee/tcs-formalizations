import Toda.Counting.BoundedProduct.Witnesses
import Complexitylib.Classes.P.BoundedQuant
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Verdict

/-!
# Polynomial-time verification of polynomially many witness blocks

The loop bounds, block positions, slices, and verifier calls are all compiled
through the machine-based FP and P closure theorems.
-/

namespace Toda.Counting.BoundedProduct

open Complexity

/-- A uniformly bounded conjunction of indexed verifier checks is in P. -/
theorem language_mem_P (L : Language) (hL : L ∈ Complexity.P)
    {q r : List Bool → ℕ} (hq : UnaryFn q) (hr : UnaryFn r) :
    language L q r ∈ Complexity.P := by
  have hx : (fun u => pairFst (pairFst u)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hw : (fun u => pairSnd (pairFst u)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hwidth : UnaryFn fun u => r (pairFst (pairFst u)) := hr.comp hx
  have hinput : (fun u => pair (pairFst (pairFst u))
      (List.replicate (pairSnd u).length true)) ∈ FP :=
    mem_FP_pair hx UnaryFn.index.mem_FP
  have hcert : (fun u => ((pairSnd (pairFst u)).drop
      ((pairSnd u).length * r (pairFst (pairFst u)))).take
      (r (pairFst (pairFst u)))) ∈ FP :=
    take_mem_FP (drop_mem_FP hw (UnaryFn.index.mul hwidth)) hwidth
  have hLp : FPPred fun u => u ∈ L := mem_P_iff_exists_decisionFn.mp hL
  have hbody := hLp.comp (mem_FP_pair hinput hcert)
  exact ((FPPred.forall_lt hq.lift hbody).of_iff fun z => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    rfl).mem_P

end Toda.Counting.BoundedProduct

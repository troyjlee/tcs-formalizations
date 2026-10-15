import Toda.Counting.GapPBoundedProduct
import Toda.Counting.BoundedSum
import Toda.Counting.GapPConditional
import Toda.Counting.AmplificationResources
import Toda.Counting.AmplificationChoices
import Toda.Counting.AmplificationTreeResources
import Toda.Counting.AmplificationIndexing

/-!
# Uniform amplification in GapP

The signed expansion of an amplification tree is a sum of products of local
weights. Polynomial-time predicates select the active nodes, leaves, and term
choices. Uniform counting closure compiles that expansion into one counting
machine, even when the number of amplification rounds depends on the input.
-/

namespace Toda.Counting

open Complexity

/-- The weights used by a pruned amplification tree are GapP functions whenever
the node classification and term-choice predicates are polynomial-time.
An unused choice bit must be false, giving each pruned subtree one encoding. -/
theorem gapP_amplificationLocalFactor {f : List Bool → ℤ}
    {active leaf bit : List Bool → Prop}
    [DecidablePred active] [DecidablePred leaf] [DecidablePred bit]
    (hf : f ∈ GapP) (ha : FPPred active) (hl : FPPred leaf) (hb : FPPred bit) :
    (fun x => if active x then
      if leaf x then (if bit x then 0 else f x)
      else (if bit x then -2 else 3)
      else (if bit x then 0 else 1)) ∈ GapP :=
  gapP_ite ha (gapP_ite hl
    (gapP_ite hb (gapP_const 0) hf)
    (gapP_ite hb (gapP_const (-2)) (gapP_const 3)))
    (gapP_ite hb (gapP_const 0) (gapP_const 1))

/-- The concrete signed factor is a GapP function when its activity and leaf
tests have polynomial-time implementations. Bit access is implemented by the
ordinary string-operation machines. -/
theorem amplificationLocalFactor_mem_gapP {f : List Bool → ℤ}
    {k i : List Bool → ℕ} {bits : List Bool → List Bool}
    (hf : f ∈ GapP) (hi : UnaryFn i) (hbits : bits ∈ FP)
    (ha : FPPred fun z => AmplificationChoices.nodeActive (k z) true (bits z) (i z) = true)
    (hl : FPPred fun z => AmplificationChoices.nodeLeaf (k z) (i z) = true) :
    (fun z => AmplificationChoices.localFactor (k z) true (f z) (bits z) (i z)) ∈ GapP := by
  simpa only [AmplificationChoices.localFactor] using
    gapP_amplificationLocalFactor hf ha hl (FPPred.getBit hbits hi)

namespace UniformAmplification

/-- The total machine-level factor guards its node tests by the tree size.
Only valid indices occur in the product. On other inputs the bit is treated
as an inactive-node choice. -/
def indexedFactor (k : ℕ) (m : ℤ) (bits : List Bool) (i : ℕ) : ℤ :=
  if i < AmplificationChoices.nodeCount k ∧
      AmplificationChoices.nodeActive k true bits i = true then
    if i < AmplificationChoices.nodeCount k ∧
        AmplificationChoices.nodeLeaf k i = true then
      (if bits[i]?.getD false then 0 else m)
    else (if bits[i]?.getD false then -2 else 3)
  else (if bits[i]?.getD false then 0 else 1)

/-- The guard does not change any factor used in the finite tree expansion. -/
theorem indexedFactor_eq (k : ℕ) (m : ℤ) (bits : List Bool) (i : ℕ)
    (hi : i < AmplificationChoices.nodeCount k) :
    indexedFactor k m bits i = AmplificationChoices.localFactor k true m bits i := by
  simp only [indexedFactor, AmplificationChoices.localFactor, hi, true_and]

/-- Guarded polynomial-time node classifiers suffice for the concrete factor
used by the bounded product compiler. -/
theorem indexedFactor_mem_gapP {f : List Bool → ℤ}
    {k i : List Bool → ℕ} {bits : List Bool → List Bool}
    (hf : f ∈ GapP) (hi : UnaryFn i) (hbits : bits ∈ FP)
    (ha : FPPred fun z => i z < AmplificationChoices.nodeCount (k z) ∧
      AmplificationChoices.nodeActive (k z) true (bits z) (i z) = true)
    (hl : FPPred fun z => i z < AmplificationChoices.nodeCount (k z) ∧
      AmplificationChoices.nodeLeaf (k z) (i z) = true) :
    (fun z => indexedFactor (k z) (f z) (bits z) (i z)) ∈ GapP := by
  simpa only [indexedFactor] using
    gapP_amplificationLocalFactor hf ha hl (FPPred.getBit hbits hi)

/-- Assemble one uniform product machine and then one uniform summation
machine from the encoded local factor. The inner pairing carries the choices;
the outer pairing carries the unary node index. -/
theorem sum_prod_indexedFactor_mem_gapP {f : List Bool → ℤ}
    {k : List Bool → ℕ}
    (hn : UnaryFn fun x => AmplificationChoices.nodeCount (k x))
    (hfactor : (fun z => indexedFactor (k (pairFst (pairFst z)))
      (f (pairFst (pairFst z))) (pairSnd (pairFst z)) (pairSnd z).length) ∈ GapP) :
    (fun x => ∑ bits : Fin (AmplificationChoices.nodeCount (k x)) → Bool,
      ∏ i : Fin (AmplificationChoices.nodeCount (k x)),
        indexedFactor (k x) (f x) (List.ofFn bits) i.val) ∈ GapP := by
  have hprod := gapP_bounded_prod hfactor hn.lift
  have hsum := gapP_sum_bits hprod hn
  convert hsum using 1
  funext x
  apply Finset.sum_congr rfl
  intro bits _
  rw [pairFst_pair]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

end UniformAmplification

/-- The complete signed tree expansion is a uniform GapP function. Both the
tree depth and total node count are computed in unary polynomial time. -/
theorem gapP_amplificationTreeExpansion {f : List Bool → ℤ} {k : List Bool → ℕ}
    (hf : f ∈ GapP) (hk : UnaryFn k)
    (hn : UnaryFn fun x => AmplificationChoices.nodeCount (k x)) :
    (fun x => ∑ bits : Fin (AmplificationChoices.nodeCount (k x)) → Bool,
      ∏ i : Fin (AmplificationChoices.nodeCount (k x)),
        AmplificationChoices.localFactor (k x) true (f x) (List.ofFn bits) i.val)
      ∈ GapP := by
  have hx : (fun z => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hbits : (fun z => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have ha := AmplificationIndexing.nodeActive_fppred (hn.comp hx) (hk.comp hx)
    UnaryFn.index hbits
  have hl := AmplificationIndexing.nodeLeaf_fppred (hn.comp hx) (hk.comp hx)
    UnaryFn.index hbits
  have hfactor := UniformAmplification.indexedFactor_mem_gapP
    (gapP_comp_fp hf hx) UnaryFn.index hbits ha hl
  have hsum := UniformAmplification.sum_prod_indexedFactor_mem_gapP hn hfactor
  convert hsum using 1
  funext x
  apply Finset.sum_congr rfl
  intro bits _
  apply Finset.prod_congr rfl
  intro i _
  exact (UniformAmplification.indexedFactor_eq _ _ _ _ i.isLt).symm

/-- An input-dependent number of amplification rounds preserves GapP when
the depth and the size of its complete ternary tree are unary polynomial-time
functions. This constructs one counting machine for the varying-depth family. -/
theorem gapP_amplifyIterate_unaryFn {f : List Bool → ℤ} {k : List Bool → ℕ}
    (hf : f ∈ GapP) (hk : UnaryFn k)
    (hn : UnaryFn fun x => AmplificationChoices.nodeCount (k x)) :
    (fun x => Arithmetic.amplifyIterate (k x) (f x)) ∈ GapP := by
  simpa only [AmplificationChoices.sum_prod_localFactor] using
    gapP_amplificationTreeExpansion hf hk hn

/-- The logarithmic depth needed for Toda's modular count recovery is uniform
GapP amplification. The tree has polynomial size in the unary width `q x`. -/
theorem gapP_amplifyRounds {f : List Bool → ℤ} {q : List Bool → ℕ}
    (hf : f ∈ GapP) (hq : UnaryFn q) :
    (fun x => Arithmetic.amplifyIterate (Arithmetic.amplificationRounds (q x)) (f x))
      ∈ GapP :=
  gapP_amplifyIterate_unaryFn hf (unaryFn_amplificationRounds hq)
    (unaryFn_amplificationTreeNodes_rounds hq)

end Toda.Counting

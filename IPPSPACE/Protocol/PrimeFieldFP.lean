/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.P.BoundedQuant
import Complexitylib.Classes.P.NatCodes
import IPPSPACE.Protocol.PrimeField

/-!
# Machine-based polynomial-time certificates for prime fields

The certificates below use the imported `Complexity.FP`, `UnaryFn`, and
`FPPred` definitions, whose witnesses are actual upstream Turing machines.
Trial division and bounded search suffice because the protocol modulus is
polynomially bounded numerically. The existing prime selector is preserved.

The result applies to every unary-computable size parameter, with an unconditional
instance for input length. It does not yet certify QBF parsing or computation of
its node count, message parsing, Horner iteration, or the complete verifier.
-/

namespace IPPSPACE

open Complexity

/-- Trial division gives an actual polynomial-time primality test when the
candidate itself can be written in unary in polynomial time. -/
theorem prime_fppred {n : List Bool → ℕ} (hn : UnaryFn n) :
    FPPred fun z => (n z).Prime := by
  have htrial : FPPred fun w => ¬ 2 ≤ (pairSnd w).length ∨
      ¬ n (pairFst w) % (pairSnd w).length = 0 :=
    ((FPPred.le (UnaryFn.const 2) UnaryFn.index).not).or
      ((FPPred.eq (hn.lift.mod UnaryFn.index) (UnaryFn.const 0)).not)
  refine ((FPPred.le (UnaryFn.const 2) hn).and
    (FPPred.forall_lt hn htrial)).of_iff (fun z => ?_)
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, htrial⟩
    exact ⟨h2, fun d hd hdn hdvd =>
      (htrial d hdn).elim (fun h => h hd) (fun h => h (Nat.mod_eq_zero_of_dvd hdvd))⟩
  · rintro ⟨h2, hprime⟩
    refine ⟨h2, fun d hdn => ?_⟩
    by_cases hd : 2 ≤ d
    · exact Or.inr (fun hmod => hprime d hd hdn (Nat.dvd_of_mod_eq_zero hmod))
    · exact Or.inl hd

private theorem find_range_getD_eq (bound fallback : ℕ) (test : ℕ → Bool) :
    ((List.range bound).find? test).getD fallback =
      if (List.range bound).findIdx test < bound then (List.range bound).findIdx test
      else fallback := by
  rw [List.find?_eq_getElem?_findIdx]
  by_cases h : (List.range bound).findIdx test < bound
  · simp [h]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    simp [h]

/-- The exact `find?`-based executable selector is polynomial-time on unary
computable bounds, including its default value when the interval is empty. -/
theorem boundedPrime_unaryFn {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun z => boundedPrime (n z) := by
  have hbound : UnaryFn fun z => 2 * n z + 1 :=
    ((UnaryFn.const 2).mul hn).add (UnaryFn.const 1)
  have htest : FPPred fun w => n (pairFst w) < (pairSnd w).length ∧
      ((pairSnd w).length).Prime :=
    (FPPred.lt hn.lift UnaryFn.index).and (prime_fppred UnaryFn.index)
  have hindex : UnaryFn fun z => (List.range (2 * n z + 1)).findIdx
      (fun p => decide (n z < p ∧ p.Prime)) :=
    (hbound.find htest).of_eq (fun z => by simp only [pairFst_pair, pairSnd_pair, List.length_replicate])
  refine (UnaryFn.ite (FPPred.lt hindex hbound) hindex (UnaryFn.const 2)).of_eq (fun z => ?_)
  exact (find_range_getD_eq _ _ _).symm

/-- The chosen modulus has an actual uniform machine-time certificate. -/
theorem protocolPrime_unaryFn {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun z => protocolPrime (n z) :=
  boundedPrime_unaryFn ((UnaryFn.const 6).mul ((hn.add (UnaryFn.const 1)).pow_const 3))

theorem protocolPrime_length_unaryFn : UnaryFn fun z : List Bool => protocolPrime z.length :=
  protocolPrime_unaryFn unaryLength_mem_FP

theorem protocolPrime_bits_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => (protocolPrime (n z)).bits) ∈ FP :=
  bits_mem_FP (protocolPrime_unaryFn hn)

theorem residueWidth_unaryFn {p : List Bool → ℕ} (hp : UnaryFn p) :
    UnaryFn fun z => residueWidth (p z) :=
  (((UnaryFn.const 2).log hp).add (UnaryFn.const 1)).of_eq
    (fun z => by simp only [residueWidth, Nat.log2_eq_log_two])

/-- Uniform binary output for the bounded search result. -/
theorem boundedPrime_bits_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => (boundedPrime (n z)).bits) ∈ FP :=
  bits_mem_FP (boundedPrime_unaryFn hn)

/-- The actual Boolean primality verdict is polynomial-time. -/
theorem primeFlag_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => [decide (n z).Prime]) ∈ FP :=
  (prime_fppred hn).flag_mem_FP

theorem protocolResidueWidth_unaryFn {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun z => residueWidth (protocolPrime (n z)) :=
  residueWidth_unaryFn (protocolPrime_unaryFn hn)

end IPPSPACE

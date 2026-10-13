/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.SyntaxParsingFP
import IPPSPACE.Protocol.PrimeFieldFP

/-!
# Field selection from the decoded input formula

The exact syntax-node count, with zero as the invalid-input default, supplies
the existing prime selector and residue width. A separate raw output rejects
invalid syntax. These certificates do not require unary-bounded variable names.
-/

namespace IPPSPACE

open Complexity

theorem decodedProtocolPrime_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => protocolPrime (((decodeQBF (bits z)).map nodeCount).getD 0) :=
  protocolPrime_unaryFn (decodeQBF_nodeCount_unaryFn hbits)

theorem decodedProtocolResidueWidth_unaryFn {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => residueWidth (protocolPrime (((decodeQBF (bits z)).map nodeCount).getD 0)) :=
  residueWidth_unaryFn (decodedProtocolPrime_unaryFn hbits)

/-- Select the existing protocol prime for a decoded formula; reject malformed syntax. -/
def decodeProtocolPrimeBits (bits : List Bool) : List Bool :=
  match decodeQBF bits with
  | none => []
  | some formula => (protocolPrime (nodeCount formula)).bits

@[simp] theorem decodeProtocolPrimeBits_encode (formula : QBF) :
    decodeProtocolPrimeBits (encodeQBF formula) = (protocolPrime (nodeCount formula)).bits := by
  simp [decodeProtocolPrimeBits]

theorem decodeProtocolPrimeBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodeProtocolPrimeBits (bits z)) ∈ FP := by
  have h := (decodeQBF_success_fppred hbits).ite_mem_FP
    (bits_mem_FP (decodedProtocolPrime_unaryFn hbits)) (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro z
  cases hparse : decodeQBF (bits z) <;> simp [decodeProtocolPrimeBits, hparse]

end IPPSPACE

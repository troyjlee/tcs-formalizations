/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE

/-!
# Review checks for the public theorem statements

Typed assignments require the exact unconditional public interfaces. They do
not establish that the definitions express the intended informal theorem;
that is a separate task for mathematical reviewers.
-/

example : Complexity.PSPACE ⊆ Complexity.IP := IPPSPACE.pspace_subset_ip

example : Complexity.IP = Complexity.PSPACE := IPPSPACE.ip_eq_pspace

example : {input | IPPSPACE.EncodedTrueQBF input} ∈ Complexity.IP :=
  IPPSPACE.encodedTrueQBF_mem_IP

example {language : Complexity.Language} (hL : language ∈ Complexity.PSPACE) :
    ∃ encode : List Bool → List Bool, encode ∈ Complexity.FP ∧
      ∀ input, IPPSPACE.EncodedTrueQBF (encode input) ↔ input ∈ language :=
  IPPSPACE.pspace_has_FP_closedQBF_encoding hL

example : IPPSPACE.prenexReduction ∈ Complexity.FP :=
  IPPSPACE.prenexReduction_mem_FP

example : IPPSPACE.reducedViewVerifierMessage ∈ Complexity.FP ∧
    {bits | IPPSPACE.reducedViewTranscriptVerdict bits = true} ∈ Complexity.P :=
  IPPSPACE.closedQBFVerifier_runtime

example {f : List Bool → List Bool} {language : Complexity.Language}
    (hf : f ∈ Complexity.FP) (hL : language ∈ Complexity.IP) :
    f ⁻¹' language ∈ Complexity.IP := IPPSPACE.mem_IP_preimage hf hL

#print axioms IPPSPACE.pspace_subset_ip
#print axioms IPPSPACE.ip_eq_pspace

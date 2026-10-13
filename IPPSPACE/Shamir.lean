/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.UpstreamProtocol
import IPPSPACE.Protocol.ReductionClosure
import Complexitylib.Classes.Containments.IPSubsetPSPACE

/-!
# Shamir's theorem: IP = PSPACE

The hard inclusion composes the polynomial-time machine-to-closed-QBF reduction
with the certified algebraic interactive protocol and closure of actual upstream
IP under FP preimages. The reverse inclusion is the unchanged upstream theorem.
Both classes, their machine model, and their probability convention are the
original Complexitylib definitions.
-/

namespace IPPSPACE

/-- Every actual polynomial-space language has an actual polynomial-time
interactive proof, with no hypothesis for a missing reduction or runtime bound. -/
theorem pspace_subset_ip : Complexity.PSPACE ⊆ Complexity.IP := by
  intro language hlanguage
  obtain ⟨encode, hencode, hcorrect⟩ := pspace_has_FP_closedQBF_encoding hlanguage
  exact mem_IP_of_FP_reduction hencode (fun input => (hcorrect input).symm)
    encodedTrueQBF_mem_IP

/-- **Shamir's theorem**, for the unchanged upstream complexity classes. -/
theorem ip_eq_pspace : Complexity.IP = Complexity.PSPACE :=
  Set.Subset.antisymm Complexity.IP_subset_PSPACE pspace_subset_ip

end IPPSPACE

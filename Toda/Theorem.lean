import Toda.Randomized.Hierarchy
import Toda.Oracle.Reduction
import Toda.Oracle.FunctionModel.Cost

/-!
# Toda's theorem

The polynomial hierarchy is the unchanged certificate-quantifier hierarchy
over machine-based P. The endpoint is a finite-control deterministic multitape
machine using a canonical #P function oracle with complete binary answers.
All query construction, answer reading, and ordinary postprocessing are charged.
The second statement also charges the entire returned answer at each query.
-/

namespace Toda

/-- **Toda's theorem:** the polynomial hierarchy is contained in P^#P. -/
theorem toda : Complexity.PH ⊆ Oracle.PSharpP :=
  Set.Subset.trans Randomized.PH_subset_bpParityP Randomized.bpParityP_subset_pSharpP

/-- Toda's inclusion remains valid when the oracle transition is charged for
every supplied answer bit in addition to all ordinary machine steps. -/
theorem toda_charged {language : Complexity.Language} (hlanguage : language ∈ Complexity.PH) :
    ∃ oracle : Oracle.FunctionOracle, oracle ∈ Complexity.SharpP ∧
      language ∈ Oracle.PWithFunctionOracleCharged oracle :=
  Oracle.mem_pSharpP_iff_charged.mp (toda hlanguage)

end Toda

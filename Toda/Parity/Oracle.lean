import Toda.Parity.Class
import Toda.Oracle.Preprocess

/-! Canonical parity counting is decided by a costed bit-zero oracle query. -/

namespace Toda.Parity

open Complexity Toda.Oracle

/-- ParityP embeds into the explicit #P bit-oracle class with actual FP query
preparation and a proved ordinary-input oracle-machine runtime. -/
theorem parityP_subset_pSharpPBits : ParityP ⊆ PSharpPBits := by
  rintro language ⟨F, hF, hparity⟩
  refine ⟨F, hF, ?_⟩
  have hprepare := bitQuery_mem_FP id_mem_FP (UnaryFn.const 0)
  have hrun := oracle_preimage_mem_pWithOracle (bitOracle F) hprepare
  have hlanguage : {input | bitOracle F (bitQuery input 0) = true} = language := by
    ext input
    simp [hparity input]
  simpa only [id_eq, hlanguage] using hrun

end Toda.Parity

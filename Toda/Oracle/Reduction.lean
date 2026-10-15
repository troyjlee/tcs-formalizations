import Toda.Oracle.FunctionPrepareBatch
import Toda.Oracle.FunctionPostprocess
import Toda.Oracle.FullCount

/-! # Executing the randomized parity reduction with full #P answers -/

namespace Toda.Oracle

open Complexity

/-- Prepare a finite query stream, execute it on a full-answer oracle machine,
and run an ordinary FP Boolean postprocessor. All three phases are costed. -/
theorem prepared_function_batch_decide_mem_pWithFunctionOracle
    {oracle : FunctionOracle} {prepare post : List Bool → List Bool} {language : Language}
    (horacle : oracle ∈ SharpP) (hprepare : prepare ∈ FP) (hpost : post ∈ FP)
    (hyes : ∀ input, input ∈ language →
      post (FunctionBatch.answers oracle (prepare input)) = [true])
    (hno : ∀ input, input ∉ language →
      post (FunctionBatch.answers oracle (prepare input)) = [false]) :
    language ∈ PWithFunctionOracle oracle := by
  obtain ⟨tapes, machine, time, htime, hrun⟩ :=
    FunctionPrepareBatch.exists_polynomial_machine hprepare horacle
  exact FunctionPostprocess.mem_pWithFunctionOracle oracle machine htime hrun hpost hyes hno

end Toda.Oracle

namespace Toda.Randomized

open Complexity Toda.Oracle

/-- Bounded-error canonical parity predicates admit deterministic polynomial-
time simulation with one canonical #P oracle returning full binary answers. -/
theorem bpParityP_subset_pSharpP : BPParityP ⊆ PSharpP := by
  intro language hlanguage
  obtain ⟨oracle, horacle, hdecide⟩ := bpParityP_exists_fullCountVerdict hlanguage
  refine ⟨oracle, horacle,
    prepared_function_batch_decide_mem_pWithFunctionOracle horacle
      encoded_fullCountQueries_mem_FP fullCountVerdict_mem_FP ?_ ?_⟩
  · intro input hin
    simpa only [FunctionBatch.answers, Batch.decode_encode] using (hdecide input).mp hin
  · intro input hin
    have hfalse : fullCountVerdict (FunctionBatch.answers oracle
        (Batch.encode (fullCountQueries input))) ≠ [true] := by
      simpa only [FunctionBatch.answers, Batch.decode_encode] using
        mt (hdecide input).mpr hin
    exact (fullCountVerdict_boolean _).resolve_left hfalse

end Toda.Randomized

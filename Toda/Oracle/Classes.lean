import Toda.Oracle.BitOracle
import Toda.Oracle.Machine
import Toda.Counting.Constants

/-!
# Polynomial time with an explicit Boolean oracle

These classes use the unchanged oracle Turing machine, with query construction
charged to its runtime. `PSharpPBits` uses the bit interface defined here for
one canonical #P function. The final endpoint is the full binary-answer class
in `FunctionModel`. The completed reduction uses that model directly; no
general equivalence of these oracle classes is claimed.
-/

namespace Toda.Oracle

open Complexity

/-- Languages decided in polynomial time by an actual Boolean-oracle TM. -/
def PWithOracle (oracle : BooleanOracle) : Set Language :=
  {language | ∃ (tapes : ℕ) (machine : OracleTM tapes) (time : ℕ → ℕ),
    machine.DecidesInTime oracle language time ∧ PolyBound time}

/-- Polynomial time using the canonical bit interface of one #P function. -/
def PSharpPBits : Set Language :=
  {language | ∃ F : List Bool → ℕ, F ∈ SharpP ∧ language ∈ PWithOracle (bitOracle F)}

/-- Ordinary polynomial time embeds without making oracle queries. -/
theorem p_subset_pWithOracle (oracle : BooleanOracle) : P ⊆ PWithOracle oracle := by
  intro language hlanguage
  obtain ⟨degree, tapes, machine, time, hdecide, htime⟩ :=
    Set.mem_iUnion.mp hlanguage
  exact ⟨tapes, machine.toOracleTM, time,
    (machine.toOracleTM_decidesInTime_iff oracle language time).mpr hdecide,
    BigO.pow_polynomial_bound htime⟩

/-- Ignoring the constant-zero #P oracle embeds P in the explicit bit class. -/
theorem p_subset_pSharpPBits : P ⊆ PSharpPBits := by
  intro language hlanguage
  exact ⟨fun _ => 0, Counting.sharpP_const 0,
    p_subset_pWithOracle _ hlanguage⟩

/-- A fixed machine decides the oracle's own language, including the cost of
copying the query from the ordinary input. -/
theorem oracle_language_mem_pWithOracle (oracle : BooleanOracle) :
    {input | oracle input = true} ∈ PWithOracle oracle :=
  ⟨0, DirectQuery.machine, fun n => n + 4, DirectQuery.decidesInTime oracle,
    PolyBound.id.add (PolyBound.const 4)⟩

/-- Every #P bit language belongs to the explicit bit-oracle class. -/
theorem bit_language_mem_pSharpPBits {F : List Bool → ℕ} (hF : F ∈ SharpP) :
    {query | bitOracle F query = true} ∈ PSharpPBits :=
  ⟨F, hF, oracle_language_mem_pWithOracle (bitOracle F)⟩

end Toda.Oracle

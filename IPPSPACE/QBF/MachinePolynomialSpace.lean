/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.P.Defs
import IPPSPACE.QBF.MachineGraph

/-!
# Polynomial witnesses for the actual upstream PSPACE class

The upstream asymptotic space bound can be enlarged to an explicit polynomial
valid at every input length. This preserves the actual decider, including the
charged input/output head bounds; it introduces no alternative complexity class.
-/

namespace IPPSPACE

open Complexity

theorem withinDecisionSpace_mono {Q : Type} {tapes : ℕ} (c : Cfg tapes Q)
    {inputLength space larger : ℕ} (h : space ≤ larger)
    (hc : c.WithinDecisionSpace inputLength space) :
    c.WithinDecisionSpace inputLength larger := by
  rcases hc with ⟨⟨hw, hi⟩, ho⟩
  exact ⟨⟨fun i => (hw i).trans h, by omega⟩, by omega⟩

theorem machineDecidesInSpace_mono {tapes : ℕ} {tm : TM tapes}
    {language : Language} {space larger : ℕ → ℕ} (h : ∀ n, space n ≤ larger n)
    (hdec : tm.DecidesInSpace language space) : tm.DecidesInSpace language larger :=
  ⟨fun input c hc => withinDecisionSpace_mono c (h input.length) (hdec.1 input c hc), hdec.2⟩

/-- Every language in the imported `Complexity.PSPACE` has a fixed actual
machine and a polynomial bounding every reachable configuration. -/
theorem pspace_iff_exists_polynomial_space (language : Language) :
    language ∈ PSPACE ↔ ∃ (tapes : ℕ) (tm : TM tapes) (space : Polynomial ℕ),
      tm.DecidesInSpace language (fun n => space.eval n) := by
  constructor
  · intro h
    obtain ⟨degree, hdegree⟩ := Set.mem_iUnion.mp h
    obtain ⟨tapes, tm, space, hdec, hbound⟩ := hdegree
    obtain ⟨polynomial, hp⟩ := hbound.pow_polynomial_bound
    exact ⟨tapes, tm, polynomial, machineDecidesInSpace_mono hp hdec⟩
  · rintro ⟨tapes, tm, polynomial, hdec⟩
    apply Set.mem_iUnion.mpr
    exact ⟨polynomial.natDegree, tapes, tm, (fun n => polynomial.eval n), hdec,
      BigO.of_polynomial_bound polynomial (fun _ => le_rfl)⟩

end IPPSPACE

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerTheorem7Odd

/-!
# Tucker's Theorem 7, assembled

A minimal instance with an asteroidal triple contains one of the five configurations:
the normalized setup (`TuckerTheorem7Setup.lean`) has `R` of length two (`MI 0`), or an even
common prefix (`TuckerTheorem7Even.lean`), or an odd one (`TuckerTheorem7Odd.lean`).  This
discharges the hypothesis `MinimalTriplePattern α` of `TuckerForbidden.lean`, and with
Theorem 6 gives Tucker's sufficiency theorem unconditionally: a Tucker-free family has the
consecutive-ones property.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-- A normalized setup carries a configuration. -/
theorem Setup.not_tuckerFree {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (S : Setup O F x y z) : ¬ IsTuckerFree F := by
  rcases Nat.lt_or_ge S.R.n 2 with h1 | h2
  · exact S.not_tuckerFree_of_R_one (by have := S.R_pos; omega)
  · obtain ⟨h, hm | hm⟩ := Nat.even_or_odd' S.m
    · exact Setup.even_main hm h2
    · exact Setup.odd_main hm h2

/-- **Tucker's Theorem 7** (the minimal-instance form): a minimal instance with an asteroidal
triple contains one of the configurations `MI`, `MII`, `MIII`, `MIV`, `MV`. -/
theorem minimalTriplePattern : MinimalTriplePattern α := by
  intro O F ⟨x, y, z, ht⟩ hmin hT
  obtain ⟨x', y', z', ⟨S⟩⟩ := Setup.exists_of_minimal ⟨ht, hmin⟩
  exact S.not_tuckerFree hT

/-- **Tucker's Theorem 9, sufficiency, unconditional**: a Tucker-free family has the
consecutive-ones property. -/
theorem hasConsecutiveOnes_of_tuckerFree_tucker {O : Finset α} {F : Finset (Finset α)}
    (hT : IsTuckerFree F) : CircularOnes.HasConsecutiveOnes O F :=
  hasConsecutiveOnes_of_tuckerFree' minimalTriplePattern hT

end Tucker

end TSPGap

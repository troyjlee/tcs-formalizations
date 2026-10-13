/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.EventProb

/-!
# Ignored random-tape suffixes in the actual upstream event probability

Restricting a uniform tape to any fixed shorter prefix preserves every event
probability. This uses the upstream rational cardinality definition directly,
including zero-length prefixes and zero padding.
-/

noncomputable section

namespace IPPSPACE

open Complexity
open scoped Classical

/-- Uniform unused suffix bits cancel from the actual upstream event probability. -/
theorem eventProb_bitTape_restrict {n N : ℕ} (h : n ≤ N)
    (event : (Fin n → Bool) → Prop) :
    eventProb (Finset.univ.filter fun tape : Fin N → Bool =>
      event (fun i => tape (Fin.castLE h i))) =
      eventProb (Finset.univ.filter event) := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le h
  have hblock := eventProb_block event (fun _ : Fin padding → Bool => True)
  have hprefix (tape : Fin (n + padding) → Bool) :
      blockFst n padding tape = fun i => tape (Fin.castLE h i) := rfl
  simpa only [hprefix, and_true, Finset.filter_true, eventProb_univ, mul_one] using hblock

/-- A pointwise factorization through a tape prefix preserves exact probability,
without any computability or positivity assumption on the event. -/
theorem eventProb_bitTape_factor {n N : ℕ} (h : n ≤ N)
    (small : (Fin n → Bool) → Prop) (large : (Fin N → Bool) → Prop)
    (hfactor : ∀ tape, large tape ↔ small (fun i => tape (Fin.castLE h i))) :
    eventProb (Finset.univ.filter large) = eventProb (Finset.univ.filter small) := by
  have hevent : Finset.univ.filter large =
      Finset.univ.filter (fun tape => small (fun i => tape (Fin.castLE h i))) := by
    ext tape
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hfactor tape
  rw [hevent]
  exact eventProb_bitTape_restrict h small

/-- Boolean acceptance is the standard event specialization. -/
theorem eventProb_bitTape_restrict_accept {n N : ℕ} (h : n ≤ N)
    (accept : (Fin n → Bool) → Bool) :
    eventProb (Finset.univ.filter fun tape : Fin N → Bool =>
      accept (fun i => tape (Fin.castLE h i)) = true) =
      eventProb (Finset.univ.filter fun tape => accept tape = true) := by
  convert eventProb_bitTape_restrict h (fun tape => accept tape = true) using 1 <;>
    congr 1 <;> ext tape <;> simp

end IPPSPACE

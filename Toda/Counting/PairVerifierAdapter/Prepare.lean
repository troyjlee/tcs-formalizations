import Toda.Counting.EncodedVerifier
import Complexitylib.Models.TuringMachine.Subroutines.PairBuild

/-!
# Frame-preserving construction of an encoded verifier input

The pair builder writes the ordinary encoded input onto a selected work tape
while retaining every unrelated started work tape and the output exactly.
This records the source verifier's blank-work and output frames through the
actual pair-construction computation.
-/

namespace Toda.Counting.PairVerifierAdapter

open Complexity
open CanonicalVerifier EncodedVerifier

variable {n : ℕ}

/-- Build the canonical pair on a fresh work tape, preserving every unrelated
non-marker work tape and the non-marker output tape at no extra time cost. -/
theorem pairBuild_hoareTime_frame (yIdx pIdx : Fin n) (hne : yIdx ≠ pIdx)
    (x y : List Bool) (work : Fin n → Tape) (out : Tape)
    (hyw : work yIdx = witnessTape y) (hpw : work pIdx = witnessTape [])
    (hout : out.read ≠ Γ.start)
    (hothers : ∀ i, i ≠ yIdx → i ≠ pIdx → (work i).read ≠ Γ.start) :
    (TM.pairBuildTM yIdx pIdx).HoareTime (Tapes (witnessTape x) work out)
      (fun _ work' out' =>
        work' pIdx = witnessTape (pair x y) ∧
        (∀ i, i ≠ yIdx → i ≠ pIdx → work' i = work i) ∧ out' = out)
      (TM.pairBuildTime x.length y.length) := by
  intro inp work' out' hp
  rcases hp with ⟨hi, hw, ho⟩
  subst inp
  subst work'
  subst out'
  obtain ⟨c, t, ht, hr, hh, hc⟩ :=
    TM.pairBuildTM_hoareTime_all_started_initTape_move_right yIdx pIdx hne x y
      (witnessTape x) work out ⟨rfl, hyw, hpw⟩
  let initial : Cfg n (TM.pairBuildTM yIdx pIdx).Q :=
    ⟨(TM.pairBuildTM yIdx pIdx).qstart, witnessTape x, work, out⟩
  have htrace : (TM.pairBuildTM yIdx pIdx).toNTM.trace t (fun _ => false) initial = c :=
    (TM.pairBuildTM yIdx pIdx).toNTM_trace_of_reachesIn hr hh le_rfl (fun _ => false)
  refine ⟨c, t, ht, hr, hh, hc, ?_, ?_⟩
  · intro i hiy hip
    have hpres := TM.pairBuildTM_trace_preserves_other_work yIdx pIdx i t
      (fun _ => false) initial hiy hip (hothers i hiy hip)
    rw [htrace] at hpres
    exact hpres
  · have hpres := TM.pairBuildTM_trace_preserves_output yIdx pIdx t
      (fun _ => false) initial hout
    rw [htrace] at hpres
    exact hpres

end Toda.Counting.PairVerifierAdapter

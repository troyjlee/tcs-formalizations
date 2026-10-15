import Toda.Counting.CanonicalVerifier
import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

/-!
# Entry from loaded source and witness tapes

The loader leaves every head at cell one. One entry transition restores the
source input, work, and output heads to their initial marker cells, preserving
the witness head and its first choice. The retargeted prepared verifier then
performs the source's mandatory marker transition using that first choice.
-/

namespace Toda.Counting.CanonicalVerifierEntry

open Complexity
open CanonicalVerifier

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

private abbrev core (N : NTM n) := TM.retargetInput (CanonicalVerifier.machine N)

/-- The entry state is `none`; `some q` runs the retargeted verifier. -/
def machine (N : NTM n) : TM (n + 2) where
  Q := Option (core N).Q
  qstart := none
  qhalt := some (core N).qhalt
  δ q i w o := match q with
    | none =>
      (some (core N).qstart, fun j => TM.readBackWrite (w j), TM.readBackWrite o,
        TM.idleDir i,
        fun j => if j.val = n then TM.idleDir (w j) else TM.moveLeftDir (w j),
        TM.moveLeftDir o)
    | some q =>
      let r := (core N).δ q i w o
      (some r.1, r.2)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none =>
      refine ⟨TM.idleDir_right_of_start, ?_, TM.moveLeftDir_right_of_start⟩
      intro j hj
      by_cases h : j.val = n <;> simp [h, TM.idleDir, TM.moveLeftDir, hj]
    | some q => exact (core N).δ_right_of_start q i w o

private def wrap (N : NTM n) (c : Cfg (n + 2) (core N).Q) :
    Cfg (n + 2) (machine N).Q where
  state := some c.state
  input := c.input
  work := c.work
  output := c.output

private theorem step_wrap (N : NTM n) {c c' : Cfg (n + 2) (core N).Q}
    (hs : (core N).step c = some c') :
    (machine N).step (wrap N c) = some (wrap N c') := by
  have hn := TM.state_ne_qhalt_of_step hs
  simp only [TM.step, hn, ite_false, Option.some.injEq] at hs
  subst c'
  simp [TM.step, machine, wrap, hn]

/-- Loaded tapes at head one, with witness at index `n` and source input at
index `n+1`. The ordinary input tape is ignored. -/
def startedPrepared (N : NTM n) (x bits : List Bool) (realInput : Tape) :
    Cfg (n + 2) (machine N).Q where
  state := (machine N).qstart
  input := realInput
  work := Fin.snoc (Fin.snoc (fun _ : Fin n => witnessTape []) (witnessTape bits))
    (witnessTape x)
  output := witnessTape []

private theorem rewind_witnessTape (bits : List Bool) :
    (witnessTape bits).writeAndMove (TM.readBackWrite (witnessTape bits).read).toΓ
      (TM.moveLeftDir (witnessTape bits).read) = Tape.init (bits.map Γ.ofBool) := by
  have h := ((Tape.StartInvariant.init_ofBool bits).move .right).read_ne_start
    (by simp [Tape.move])
  change (witnessTape bits).read ≠ Γ.start at h
  rw [TM.writeAndMove_readBack _ h]
  simp only [TM.moveLeftDir, h, ite_false]
  rfl

private theorem stay_witnessTape (bits : List Bool) :
    (witnessTape bits).writeAndMove (TM.readBackWrite (witnessTape bits).read).toΓ
      (TM.idleDir (witnessTape bits).read) = witnessTape bits := by
  exact TM.tape_writeAndMove_stable _ (by simp [witnessTape, Tape.move])
    ((Tape.StartInvariant.init_ofBool bits).move .right).2

private theorem entry_step (N : NTM n) (x bits : List Bool) (realInput : Tape) :
    (machine N).step (startedPrepared N x bits realInput) =
      some (wrap N (TM.retargetWrap (CanonicalVerifier.machine N)
        (realInput.move (TM.idleDir realInput.read)) (initialPrepared N x bits))) := by
  have hn : (none : Option (core N).Q) ≠ some (core N).qhalt := by
    intro h
    cases h
  simp only [TM.step, startedPrepared, machine, hn,
    ite_false, Option.some.injEq]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    refine Fin.lastCases ?_ ?_ j
    · simp [wrap, TM.retargetWrap, initialPrepared, embed]
      exact rewind_witnessTape x
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simp [wrap, TM.retargetWrap, initialPrepared, embed]
        change _ = (Fin.snoc (fun _ : Fin n => Tape.init []) (witnessTape bits) :
          Fin (n + 1) → Tape) (Fin.last n)
        rw [Fin.snoc_last]
        exact stay_witnessTape bits
      · intro j
        have hj : j.val ≠ n := by omega
        simp [wrap, TM.retargetWrap, initialPrepared, embed, hj]
        change _ = (Fin.snoc (fun _ : Fin n => Tape.init []) (witnessTape bits) :
          Fin (n + 1) → Tape) j.castSucc
        rw [Fin.snoc_castSucc]
        exact rewind_witnessTape []
  · simpa [wrap, TM.retargetWrap, initialPrepared, embed, NTM.initCfg] using
      rewind_witnessTape []

/-- The loaded entry machine checks the exact canonical list predicate with
one step of overhead. This includes the empty witness and initially halted
source, for which the initially blank source output cannot accept. -/
theorem startedPrepared_correct (N : NTM n) (x bits : List Bool) (realInput : Tape) :
    ∃ c' t, t ≤ 2 * bits.length + 5 ∧
      (machine N).reachesIn t (startedPrepared N x bits realInput) c' ∧
      (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (decide (canonicalListFrom N bits (N.initCfg x))) := by
  obtain ⟨c', t, ht, hr, hh, ho⟩ := CanonicalVerifier.prepared_correct N bits
    (N.initCfg x) (witnessTape bits) Tape.StartInvariant.init_nil
    (witnessTape_hasChoices bits)
  have hi : (initialPrepared N x bits).input.StartInvariant :=
    Tape.StartInvariant.init_ofBool x
  have hw : ∀ j, ((initialPrepared N x bits).work j).StartInvariant := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [initialPrepared, embed, witnessTape] using
        (Tape.StartInvariant.init_ofBool bits).move .right
    · intro j
      simpa [initialPrepared, embed, NTM.initCfg] using Tape.StartInvariant.init_nil
  obtain ⟨r, hret⟩ := TM.retargetInput_reachesIn_of_reachesIn
    (CanonicalVerifier.machine N) hr hi hw Tape.StartInvariant.init_nil
    (realInput.move (TM.idleDir realInput.read))
  refine ⟨wrap N (TM.retargetWrap (CanonicalVerifier.machine N) r c'), t + 1,
    ?_, TM.reachesIn.step (entry_step N x bits realInput)
      (TM.reachesIn_map (wrap N) (fun _ _ => step_wrap N) hret), ?_, ho⟩
  · simp only [Tape.init] at ht
    omega
  · exact congrArg some hh

/-- Fixed-width form, referring directly to the original canonical witness set. -/
theorem startedPrepared_correct_ofFn (N : NTM n) (x : List Bool) (T : ℕ)
    (choices : Fin T → Bool) (realInput : Tape) :
    ∃ c' t, t ≤ 2 * T + 5 ∧
      (machine N).reachesIn t (startedPrepared N x (List.ofFn choices) realInput) c' ∧
      (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (decide (choices ∈ canonicalWitnesses N x T)) := by
  obtain ⟨c', t, ht, hr, hh, ho⟩ := startedPrepared_correct N x (List.ofFn choices) realInput
  refine ⟨c', t, by simpa using ht, hr, hh, ?_⟩
  simpa only [canonicalListFrom_ofFn_iff, canonicalWitnesses,
    mem_canonicalWitnessesFrom] using ho

/-- Hoare form for composition with a loader that leaves all used heads at
one. Ordinary source work tapes are blank; the loaded witness is preserved. -/
theorem started_hoareTime (N : NTM n) (x bits : List Bool) :
    (machine N).HoareTime
      (fun _ work out =>
        (∀ j : Fin n, work j.castSucc.castSucc = witnessTape []) ∧
        work (Fin.last n).castSucc = witnessTape bits ∧
        work (Fin.last (n + 1)) = witnessTape x ∧ out = witnessTape [])
      (fun _ _ out =>
        out.cells 1 = Γ.ofBool (decide (canonicalListFrom N bits (N.initCfg x))))
      (2 * bits.length + 5) := by
  intro inp work out hpre
  rcases hpre with ⟨hw, hb, hx, ho⟩
  have heq : work = (startedPrepared N x bits inp).work := by
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simpa [startedPrepared] using hx
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [startedPrepared] using hb
      · intro j
        simpa [startedPrepared] using hw j
  obtain ⟨c', t, ht, hr, hh, hout⟩ := startedPrepared_correct N x bits inp
  refine ⟨c', t, ht, ?_, hh, hout⟩
  simpa only [heq, ho, startedPrepared] using hr

end Toda.Counting.CanonicalVerifierEntry

import Toda.Counting.ClockedGuessAndVerify
import Toda.Counting.EncodedVerifier
import Toda.Counting.LiftFrame
import Complexitylib.Models.TuringMachine.Subroutines.PairBuild
import Toda.Counting.PairVerifierAdapter.Prepare

/-!
# Ordinary pair-input verifiers on generated work-tape witnesses

The adapter rewinds a generated witness, builds the canonical paired input,
and runs an ordinary deterministic verifier on that virtual input. Two entry
transitions erase the initial rejecting verdict and restore the source's marker
heads. The source work tapes are disjoint from the four setup/witness tapes.
-/

namespace Toda.Counting.PairVerifierAdapter

open Complexity
open CanonicalVerifier ClockedGuessAndVerify PolynomialCounter
open EncodedVerifier

set_option backward.isDefEq.respectTransparency false

variable {k : ℕ}

/-- Source work tapes precede the virtual input and four preparation tapes. -/
def registers (k : ℕ) : ClockedGuessAndVerify.Registers (k + 5) where
  lengthReg := ⟨k + 1, by omega⟩
  counter := ⟨k + 2, by omega⟩
  scratch := ⟨k + 3, by omega⟩
  witness := ⟨k + 4, by omega⟩
  length_counter := by intro h; have := congrArg Fin.val h; simp at this
  length_scratch := by intro h; have := congrArg Fin.val h; simp at this
  counter_scratch := by intro h; have := congrArg Fin.val h; simp at this
  witness_length := by intro h; have := congrArg Fin.val h; simp at this
  witness_counter := by intro h; have := congrArg Fin.val h; simp at this
  witness_scratch := by intro h; have := congrArg Fin.val h; simp at this

def pairIdx (k : ℕ) : Fin (k + 5) := ⟨k, by omega⟩

private abbrev core (M : TM k) := TM.retargetInput M

/-- Two reset transitions followed by the source with retargeted input. -/
def run (M : TM k) : TM (k + 1) where
  Q := Sum Bool (core M).Q
  qstart := .inl false
  qhalt := .inr (core M).qhalt
  δ q i w o := match q with
    | .inl false =>
      (.inl true, fun j => TM.readBackWrite (w j), TM.readBackWrite o,
        TM.idleDir i, fun j => TM.idleDir (w j), TM.moveLeftDir o)
    | .inl true =>
      (.inr (core M).qstart, fun j => TM.readBackWrite (w j), .blank,
        TM.idleDir i, fun j => TM.moveLeftDir (w j), TM.moveLeftDir o)
    | .inr q =>
      let r := (core M).δ q i w o
      (.inr r.1, r.2)
  δ_right_of_start := by
    intro q i w o
    rcases q with b | q
    · cases b
      · exact ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
          TM.moveLeftDir_right_of_start⟩
      · exact ⟨TM.idleDir_right_of_start, fun _ => TM.moveLeftDir_right_of_start,
          TM.moveLeftDir_right_of_start⟩
    · exact (core M).δ_right_of_start q i w o

private def wrap (M : TM k) (c : Cfg (k + 1) (core M).Q) :
    Cfg (k + 1) (run M).Q := ⟨.inr c.state, c.input, c.work, c.output⟩

private theorem step_wrap (M : TM k) {c c' : Cfg (k + 1) (core M).Q}
    (hs : (core M).step c = some c') :
    (run M).step (wrap M c) = some (wrap M c') := by
  have hn := TM.state_ne_qhalt_of_step hs
  simp only [TM.step, hn, ite_false, Option.some.injEq] at hs
  subst c'
  simp [TM.step, run, wrap, hn]

private theorem stay_binary (bits : List Bool) :
    (witnessTape bits).writeAndMove (TM.readBackWrite (witnessTape bits).read).toΓ
      (TM.idleDir (witnessTape bits).read) = witnessTape bits :=
  TM.tape_writeAndMove_stable _ (by simp [witnessTape, Tape.move])
    ((Tape.StartInvariant.init_ofBool bits).move .right).2

private theorem back_binary (bits : List Bool) :
    (witnessTape bits).writeAndMove (TM.readBackWrite (witnessTape bits).read).toΓ
      (TM.moveLeftDir (witnessTape bits).read) = Tape.init (bits.map Γ.ofBool) := by
  have h : (witnessTape bits).read ≠ Γ.start :=
    ((Tape.StartInvariant.init_ofBool bits).move .right).read_ne_start (by simp [Tape.move])
  rw [TM.writeAndMove_readBack _ h]
  simp only [TM.moveLeftDir, h, ite_false]
  rfl

private def runEntry (M : TM k) (z : List Bool) (inp : Tape) : Cfg (k + 1) (run M).Q :=
  ⟨.inl false, inp, Fin.snoc (fun _ : Fin k => witnessTape []) (witnessTape z),
    rejectingTape⟩

private theorem run_entry (M : TM k) (z : List Bool) (inp : Tape) :
    ∃ inp', (run M).reachesIn 2 (runEntry M z inp)
      (wrap M (TM.retargetWrap M inp' (M.initCfg z))) := by
  let inp₁ := inp.move (TM.idleDir inp.read)
  let inp₂ := inp₁.move (TM.idleDir inp₁.read)
  let mid : Cfg (k + 1) (run M).Q :=
    ⟨.inl true, inp₁, Fin.snoc (fun _ : Fin k => witnessTape []) (witnessTape z),
      rejectingTape.move .left⟩
  have hs₁ : (run M).step (runEntry M z inp) = some mid := by
    simp only [TM.step, run, runEntry, Sum.inl_ne_inr, ite_false, Option.some.injEq]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [mid, Fin.snoc_last] using stay_binary z
      · simpa only [mid, Fin.snoc_castSucc] using stay_binary []
    · exact TM.writeAndMove_readBack rejectingTape (by decide) .left
  have hs₂ : (run M).step mid =
      some (wrap M (TM.retargetWrap M inp₂ (M.initCfg z))) := by
    simp only [TM.step, run, mid, Sum.inl_ne_inr, ite_false, Option.some.injEq]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [wrap, TM.retargetWrap]
        exact back_binary z
      · simp [wrap, TM.retargetWrap]
        exact back_binary []
    · apply Tape.ext
      · rfl
      · funext j
        by_cases h0 : j = 0
        · subst j; rfl
        · by_cases h1 : j = 1
          · subst j; rfl
          · simp [wrap, TM.retargetWrap, rejectingTape, Tape.move,
              Tape.writeAndMove, Tape.write, TM.moveLeftDir, Tape.read,
              Tape.init, h0, h1]
  exact ⟨inp₂, .step hs₁ (.step hs₂ .zero)⟩

/-- Running a decider from the pair tape includes output reset and every
source transition, in at most two additional steps. -/
theorem run_hoareTime (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) (z : List Bool) :
    (run M).HoareTime
      (fun _ work out =>
        (∀ j : Fin k, work j.castSucc = witnessTape []) ∧
        work (Fin.last k) = witnessTape z ∧ out = rejectingTape)
      (fun _ _ out =>
        (z ∈ L → out.cells 1 = Γ.one) ∧ (z ∉ L → out.cells 1 = Γ.zero))
      (2 + T z.length) := by
  intro inp work out hp
  rcases hp with ⟨hw, hz, ho⟩
  have heq : work = (runEntry M z inp).work := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [runEntry] using hz
    · simpa [runEntry] using hw j
  obtain ⟨c, t, ht, hr, hh, hy, hn⟩ := hM z
  obtain ⟨inp', hentry⟩ := run_entry M z inp
  obtain ⟨inp'', hret⟩ := TM.retargetInput_reachesIn_of_reachesIn M hr
    (Tape.StartInvariant.init_ofBool z) (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil inp'
  refine ⟨wrap M (TM.retargetWrap M inp'' c), 2 + t, by omega, ?_, ?_, hy, hn⟩
  · rw [heq, ho]
    exact TM.reachesIn_trans _ hentry (TM.reachesIn_map (wrap M) (fun _ _ => step_wrap M) hret)
  · exact congrArg Sum.inr hh

/-- The complete deterministic adapter; all extra preparation tapes are ignored
by the final lifted source simulation. -/
def machine (M : TM k) : TM (k + 5) :=
  TM.seqTM (TM.rewindWorkTM (registers k).witness)
    (TM.seqTM (TM.pairBuildTM (registers k).witness (pairIdx k)) ((run M).liftTM 4))

/-- Runtime as a function of source length and fixed witness width. -/
def verificationTime (a b : ℕ) (T : ℕ → ℕ) (m : ℕ) : ℕ :=
  4 * m + 3 * polynomialClock a b m + 17 + T (2 * m + 2 + polynomialClock a b m)

theorem verificationTime_polyBound (a b : ℕ) {T : ℕ → ℕ} (hT : PolyBound T) :
    PolyBound (verificationTime a b T) := by
  have hp := polynomialClock_polyBound a b
  exact ((((PolyBound.const 4).mul PolyBound.id).add ((PolyBound.const 3).mul hp)).add
    (PolyBound.const 17)).add (polyBound_comp hT
      ((((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 2)).add hp))

private theorem witness_ne_pair (k : ℕ) : (registers k).witness ≠ pairIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [registers, pairIdx] at this

private theorem generated_blank (V : TM (k + 5)) (a b : ℕ) (x : List Bool)
    (choices : Fin (polynomialClock a b x.length) → Bool)
    (j : Fin (k + 5)) (hj : j.val ≤ k) :
    (ClockedGuessAndVerify.verifierCfg V (registers k) a b x choices).work j =
      witnessTape [] := by
  have hne (l : Fin (k + 5)) (hl : k < l.val) : j ≠ l := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [verifierCfg_work_frame _ _ _ _ _ _ j
    (hne _ (by simp [registers])) (hne _ (by simp [registers])),
    workTapes_frame _ _ _ _ _ j (hne _ (by simp [registers]))
      (hne _ (by simp [registers])) (hne _ (by simp [registers]))]
  apply Tape.ext
  · rfl
  · funext i
    by_cases hi : i = 0 <;>
      simp [TM.regTape, TM.regCells, witnessTape, Tape.move, Tape.init, hi]

/-- Every ordinary paired-input verifier runs correctly on every generated
witness, with all tape preparation and reset transitions charged. -/
theorem machine_correct (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) (a b : ℕ) (x : List Bool)
    (choices : Fin (polynomialClock a b x.length) → Bool) :
    ∃ c t, t ≤ verificationTime a b T x.length ∧
      (machine M).reachesIn t
        (ClockedGuessAndVerify.verifierCfg (machine M) (registers k) a b x choices) c ∧
      (machine M).halted c ∧
      (pair x (List.ofFn choices) ∈ L → c.output.cells 1 = Γ.one) ∧
      (pair x (List.ofFn choices) ∉ L → c.output.cells 1 = Γ.zero) := by
  let y := List.ofFn choices
  let c₀ := ClockedGuessAndVerify.verifierCfg (machine M) (registers k) a b x choices
  let work₁ := Function.update c₀.work (registers k).witness (witnessTape y)
  have hp := verifierCfg_prepared (machine M) (registers k) a b x choices
  have hinput : c₀.input = witnessTape x := verifierCfg_input _ _ _ _ _ _
  have houtput : c₀.output = rejectingTape := GuessBits.afterChoices_output _ _ _ _ _
  have hwitness := verifierCfg_witness_cells (machine M) (registers k) a b x choices
  have hhead := verifierCfg_witness_head (machine M) (registers k) a b x choices
  have hwork₁ : ∀ j, (work₁ j).read ≠ Γ.start := by
    intro j
    by_cases hj : j = (registers k).witness
    · subst j
      simp only [work₁, Function.update_self]
      exact ((Tape.StartInvariant.init_ofBool y).move .right).read_ne_start (by simp [Tape.move])
    · dsimp only [work₁]
      rw [Function.update_of_ne hj]
      exact (hp.work_invariant j).read_ne_start (hp.work_positive j)
  have hw₁pair : work₁ (pairIdx k) = witnessTape [] := by
    dsimp only [work₁]
    rw [Function.update_of_ne (Ne.symm (witness_ne_pair k))]
    exact generated_blank _ _ _ _ _ _ le_rfl
  have hw₁source (j : Fin k) :
      work₁ (Fin.castAdd 4 j.castSucc) = witnessTape [] := by
    have hj : Fin.castAdd 4 j.castSucc ≠ (registers k).witness := by
      intro h
      have he := congrArg Fin.val h
      simp [registers] at he
      omega
    dsimp only [work₁]
    rw [Function.update_of_ne hj]
    exact generated_blank _ _ _ _ _ _ (by simp)
  have hrewind := rewindWork_exact (registers k).witness (witnessTape x) rejectingTape c₀.work
    (by rw [← hinput]; exact hp.input_nonstart) (by decide) (by decide)
    (hp.work_invariant _) (by
      intro j _
      exact ⟨(hp.work_invariant j).read_ne_start (hp.work_positive j), hp.work_positive j⟩)
  have hrewind' : (TM.rewindWorkTM (registers k).witness).HoareTime
      (Tapes (witnessTape x) c₀.work rejectingTape)
      (Tapes (witnessTape x) work₁ rejectingTape)
      (polynomialClock a b x.length + 3) := by
    have htape : (⟨1, (Tape.init ((List.ofFn choices).map Γ.ofBool)).cells⟩ : Tape) =
        witnessTape (List.ofFn choices) := rfl
    simpa only [work₁, c₀, y, hwitness, hhead, Nat.add_assoc, htape] using hrewind
  have hpair := pairBuild_hoareTime_frame (registers k).witness (pairIdx k)
    (witness_ne_pair k) x y work₁ rejectingTape (Function.update_self _ _ _)
    hw₁pair (by decide) (fun j _ _ => hwork₁ j)
  have hrun := LiftFrame.liftTM_hoareTime (run M) 4 (run_hoareTime M hM (pair x y))
  have hlast := TM.seqTM_hoareTime _ _ hpair (by
    intro inp work out h
    rcases h with ⟨hpair, hframe, hout⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hjw : Fin.castAdd 4 j.castSucc ≠ (registers k).witness := by
        intro he
        have := congrArg Fin.val he
        simp [registers] at this
        omega
      have hjp : Fin.castAdd 4 j.castSucc ≠ pairIdx k := by
        intro he
        have := congrArg Fin.val he
        simp [pairIdx] at this
        omega
      change TM.transitionTape (work (Fin.castAdd 4 j.castSucc)) = witnessTape []
      rw [hframe _ hjw hjp, hw₁source]
      exact TM.transitionTape_eq_self (by decide)
    · change TM.transitionTape (work (pairIdx k)) = witnessTape (pair x y)
      rw [hpair]
      exact TM.transitionTape_eq_self
        (((Tape.StartInvariant.init_ofBool (pair x y)).move .right).read_ne_start
          (by simp [Tape.move]))
    · rw [hout]
      exact TM.transitionTape_eq_self (by decide)) hrun
  have hfull := TM.seqTM_hoareTime _ _ hrewind' (by
    intro inp work out h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self (by
        exact ((Tape.StartInvariant.init_ofBool x).move .right).read_ne_start
          (by simp [Tape.move])),
      funext fun j => TM.transitionTape_eq_self (hwork₁ j),
      TM.transitionTape_eq_self (by decide)⟩) hlast
  obtain ⟨c, t, ht, hr, hh, hy, hn⟩ := hfull c₀.input c₀.work c₀.output
    ⟨hinput, rfl, houtput⟩
  refine ⟨c, t, ?_, hr, hh, hy, hn⟩
  simp only [TM.pairBuildTime, y, List.length_ofFn, pair_length] at ht
  unfold verificationTime
  omega

end Toda.Counting.PairVerifierAdapter

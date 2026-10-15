import Toda.Counting.CanonicalVerifierEntry
import Toda.Counting.EncodedVerifier.Validator
import Complexitylib.Classes.P.Defs
import Complexitylib.Models.TuringMachine.Subroutines.PairSplit
import Complexitylib.Models.TuringMachine.Subroutines.PairValidate
import Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# A polynomial-time verifier on ordinary encoded inputs

For every source NTM, `canonicalLanguage` consists of encoded pairs of an
input and a canonical accepting witness. The actual deterministic `machine`
validates the pair encoding, rejects malformed strings, clears the validator's
verdict, rewinds and splits the input, and runs the canonical witness checker.
It halts within `7 * input.length + 35` steps. `canonicalLanguage_mem_P` uses
the unchanged machine-based definition of `Complexity.P`.

The intermediate loader specifications account exactly for the work tapes,
output tape, phase transitions, and head positions. They remain reusable
independently of the total verifier and impose no free preprocessing assumption.
-/

namespace Toda.Counting.EncodedVerifier

open Complexity

variable {k : ℕ}

/-- Canonical binary contents with an explicitly specified head position. -/
def binaryTape (bits : List Bool) (head : ℕ) : Tape :=
  ⟨head, (Tape.init (bits.map Γ.ofBool)).cells⟩

@[simp] theorem binaryTape_head (bits : List Bool) (head : ℕ) :
    (binaryTape bits head).head = head := rfl

@[simp] theorem binaryTape_cells (bits : List Bool) (head : ℕ) :
    (binaryTape bits head).cells = (Tape.init (bits.map Γ.ofBool)).cells := rfl

@[simp] theorem binaryTape_one (bits : List Bool) :
    binaryTape bits 1 = (Tape.init (bits.map Γ.ofBool)).move .right := rfl

theorem binaryTape_startInvariant (bits : List Bool) (head : ℕ) :
    (binaryTape bits head).StartInvariant :=
  Tape.StartInvariant.init_ofBool bits

theorem binaryTape_read_ne_start (bits : List Bool) (head : ℕ) (hh : 1 ≤ head) :
    (binaryTape bits head).read ≠ Γ.start :=
  (binaryTape_startInvariant bits head).read_ne_start hh

/-- Two decoded components and otherwise blank, started work tapes. -/
def workLayout (xIdx yIdx : Fin k) (x y : List Bool) (xHead yHead : ℕ) :
    Fin k → Tape := fun i =>
  if i = xIdx then binaryTape x xHead
  else if i = yIdx then binaryTape y yHead
  else binaryTape [] 1

@[simp] theorem workLayout_x (xIdx yIdx : Fin k) (x y : List Bool)
    (xHead yHead : ℕ) :
    workLayout xIdx yIdx x y xHead yHead xIdx = binaryTape x xHead := by
  simp [workLayout]

@[simp] theorem workLayout_y (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (xHead yHead : ℕ) :
    workLayout xIdx yIdx x y xHead yHead yIdx = binaryTape y yHead := by
  simp [workLayout, Ne.symm hne]

theorem workLayout_startInvariant (xIdx yIdx : Fin k) (x y : List Bool)
    (xHead yHead : ℕ) (i : Fin k) :
    (workLayout xIdx yIdx x y xHead yHead i).StartInvariant := by
  simp only [workLayout]
  split <;> first | exact binaryTape_startInvariant _ _ | skip
  split <;> exact binaryTape_startInvariant _ _

theorem workLayout_head_pos (xIdx yIdx : Fin k) (x y : List Bool)
    (xHead yHead : ℕ) (hx : 1 ≤ xHead) (hy : 1 ≤ yHead) (i : Fin k) :
    1 ≤ (workLayout xIdx yIdx x y xHead yHead i).head := by
  simp only [workLayout]
  split <;> first | exact hx | skip
  split <;> first | exact hy | decide

/-- Equality to a complete tape layout, independent of machine state. -/
def Tapes (input : Tape) (work : Fin k → Tape) (output : Tape) : TapePred k :=
  fun inp ws out => inp = input ∧ ws = work ∧ out = output

/-- An exact frame theorem for rewinding a work tape. All other tapes are
preserved, while the selected tape retains its cells and finishes at cell one. -/
theorem rewindWork_exact (idx : Fin k) (inp out : Tape) (work : Fin k → Tape)
    (hinput : inp.read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) (houtHead : 1 ≤ out.head)
    (htarget : (work idx).StartInvariant)
    (hother : ∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head) :
    (TM.rewindWorkTM idx).HoareTime (Tapes inp work out)
      (Tapes inp (Function.update work idx ⟨1, (work idx).cells⟩) out)
      ((work idx).head + 2) := by
  let P : TapePred k := fun inp' work' out' =>
    inp' = inp ∧ out' = out ∧ (work' idx).cells = (work idx).cells ∧
      ∀ i, i ≠ idx → work' i = work i
  have hf := TM.rewindWorkTM_hoareTime_frame idx ((work idx).head) (P := P)
    (by
      intro i w o i' w' o' hp hc _ hw hi ho hh
      rcases hp with ⟨rfl, rfl, hc₀, hw₀⟩
      refine ⟨hi, ?_, hc.trans hc₀, ?_⟩
      · exact Tape.ext hh ho
      · intro j hj
        exact (hw j hj).trans (hw₀ j hj))
  refine hf.consequence ?_ ?_ le_rfl
  · intro i w o h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨htarget.1, htarget.2, le_rfl, hinput, houtput, houtHead,
      hother, rfl, rfl, rfl, fun _ _ => rfl⟩
  · intro i w o h
    rcases h with ⟨hh, hi, ho, hc, hw⟩
    refine ⟨hi, ?_, ho⟩
    funext j
    by_cases hj : j = idx
    · subst j
      simp only [Function.update_self]
      exact Tape.ext hh hc
    · rw [Function.update_of_ne hj]
      exact hw j hj

private theorem transition_tapes (inp out : Tape) (work : Fin k → Tape)
    (hi : inp.read ≠ Γ.start) (ho : out.read ≠ Γ.start)
    (hw : ∀ i, (work i).read ≠ Γ.start) :
    Tapes inp work out (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  exact ⟨TM.transitionInput_eq_self hi,
    funext fun i => TM.transitionTape_eq_self (hw i), TM.transitionTape_eq_self ho⟩

/-- The loader first splits the pair, then rewinds the left and right decoded
components. It does not inspect the source machine or require prepared input. -/
def loader (xIdx yIdx : Fin k) : TM k :=
  TM.seqTM (TM.pairSplitCoreTM xIdx yIdx)
    (TM.seqTM (TM.rewindWorkTM xIdx) (TM.rewindWorkTM yIdx))

private theorem split_exact (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (TM.pairSplitCoreTM xIdx yIdx).HoareTime
      (Tapes (Tape.init ((pair x y).map Γ.ofBool))
        (fun _ => Tape.init []) (Tape.init []))
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y (x.length + 1) (y.length + 1))
        (binaryTape [] 1))
      (TM.pairSplitCoreTime x.length y.length) := by
  intro inp work out h
  rcases h with ⟨rfl, rfl, rfl⟩
  obtain ⟨c, hr, hh, hih, hic, hxh, hx0, hxd, hxt, hyh, hy0, hyd, hyt, hw, ho⟩ :=
    TM.pairSplitCoreTM_reachesIn_initCfg xIdx yIdx hne x y
  refine ⟨c, TM.pairSplitCoreTime x.length y.length, le_rfl, hr, hh, ?_, ?_, ho⟩
  · exact Tape.ext hih hic
  · funext i
    simp only [workLayout]
    split
    · subst i
      exact Tape.ext (by simpa only [binaryTape_head, Nat.add_comm] using hxh)
        (Tape.HasBinaryContent.cells_eq_init ⟨hxd, hxt⟩ hx0)
    · next hix =>
      split
      · subst i
        exact Tape.ext (by simpa only [binaryTape_head, Nat.add_comm] using hyh)
          (Tape.HasBinaryContent.cells_eq_init ⟨hyd, hyt⟩ hy0)
      · next hiy => exact hw i hix hiy

private theorem rewind_layout_x (xIdx yIdx : Fin k) (_hne : xIdx ≠ yIdx)
    (x y : List Bool) (xHead yHead : ℕ) (hx : 1 ≤ xHead) (hy : 1 ≤ yHead) :
    (TM.rewindWorkTM xIdx).HoareTime
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y xHead yHead) (binaryTape [] 1))
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 yHead) (binaryTape [] 1))
      (xHead + 2) := by
  have h := rewindWork_exact xIdx
    (binaryTape (pair x y) ((pair x y).length + 1)) (binaryTape [] 1)
    (workLayout xIdx yIdx x y xHead yHead)
    (binaryTape_read_ne_start _ _ (by omega))
    (binaryTape_read_ne_start _ _ le_rfl) le_rfl
    (workLayout_startInvariant _ _ _ _ _ _ _)
    (by intro i _; exact ⟨(workLayout_startInvariant _ _ _ _ _ _ _).read_ne_start
      (workLayout_head_pos _ _ _ _ _ _ hx hy _),
      workLayout_head_pos _ _ _ _ _ _ hx hy _⟩)
  have heq : Function.update (workLayout xIdx yIdx x y xHead yHead) xIdx
      ⟨1, (workLayout xIdx yIdx x y xHead yHead xIdx).cells⟩ =
      workLayout xIdx yIdx x y 1 yHead := by
    funext i
    by_cases hi : i = xIdx
    · subst i; simp [workLayout, binaryTape]
    · simp [workLayout, hi]
  rw [heq] at h
  simpa only [workLayout_x, binaryTape_head] using h

private theorem rewind_layout_y (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (yHead : ℕ) (hy : 1 ≤ yHead) :
    (TM.rewindWorkTM yIdx).HoareTime
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 yHead) (binaryTape [] 1))
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 1) (binaryTape [] 1))
      (yHead + 2) := by
  have h := rewindWork_exact yIdx
    (binaryTape (pair x y) ((pair x y).length + 1)) (binaryTape [] 1)
    (workLayout xIdx yIdx x y 1 yHead)
    (binaryTape_read_ne_start _ _ (by omega))
    (binaryTape_read_ne_start _ _ le_rfl) le_rfl
    (workLayout_startInvariant _ _ _ _ _ _ _)
    (by intro i _; exact ⟨(workLayout_startInvariant _ _ _ _ _ _ _).read_ne_start
      (workLayout_head_pos _ _ _ _ _ _ le_rfl hy _),
      workLayout_head_pos _ _ _ _ _ _ le_rfl hy _⟩)
  have heq : Function.update (workLayout xIdx yIdx x y 1 yHead) yIdx
      ⟨1, (workLayout xIdx yIdx x y 1 yHead yIdx).cells⟩ =
      workLayout xIdx yIdx x y 1 1 := by
    funext i
    by_cases hi : i = yIdx
    · subst i; simp [workLayout, binaryTape, Ne.symm hne]
    · simp only [Function.update_of_ne hi, workLayout]
      split <;> simp_all
  rw [heq] at h
  simpa only [workLayout_y _ _ hne, binaryTape_head] using h

private theorem loader_of_split (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (pre : TapePred k)
    (hsplit : (TM.pairSplitCoreTM xIdx yIdx).HoareTime pre
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y (x.length + 1) (y.length + 1))
        (binaryTape [] 1))
      (TM.pairSplitCoreTime x.length y.length)) :
    (loader xIdx yIdx).HoareTime pre
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 1) (binaryTape [] 1))
      (3 * x.length + 2 * y.length + 12) := by
  have ht (xh yh : ℕ) (hx : 1 ≤ xh) (hy : 1 ≤ yh) :
      ∀ inp work out,
        Tapes (binaryTape (pair x y) ((pair x y).length + 1))
          (workLayout xIdx yIdx x y xh yh) (binaryTape [] 1) inp work out →
        Tapes (binaryTape (pair x y) ((pair x y).length + 1))
          (workLayout xIdx yIdx x y xh yh) (binaryTape [] 1)
          (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact transition_tapes _ _ _ (binaryTape_read_ne_start _ _ (by omega))
      (binaryTape_read_ne_start _ _ le_rfl)
      (fun i => (workLayout_startInvariant _ _ _ _ _ _ _).read_ne_start
        (workLayout_head_pos _ _ _ _ _ _ hx hy i))
  have hr := TM.seqTM_hoareTime (TM.rewindWorkTM xIdx) (TM.rewindWorkTM yIdx)
    (rewind_layout_x xIdx yIdx hne x y (x.length + 1) (y.length + 1)
      (by omega) (by omega))
    (ht 1 (y.length + 1) le_rfl (by omega))
    (rewind_layout_y xIdx yIdx hne x y (y.length + 1) (by omega))
  have hs := TM.seqTM_hoareTime (TM.pairSplitCoreTM xIdx yIdx)
    (TM.seqTM (TM.rewindWorkTM xIdx) (TM.rewindWorkTM yIdx))
    hsplit
    (ht (x.length + 1) (y.length + 1) (by omega) (by omega)) hr
  convert hs using 1 <;> simp [loader, TM.pairSplitCoreTime]
  omega

/-- Initialized, exact loading of the two components of a canonical pair.
Every ordinary work tape and the output finish blank at cell one. The real
input is preserved and its head finishes immediately past the encoded input. -/
theorem loader_hoareTime (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (loader xIdx yIdx).HoareTime
      (Tapes (Tape.init ((pair x y).map Γ.ofBool))
        (fun _ => Tape.init []) (Tape.init []))
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 1) (binaryTape [] 1))
      (3 * x.length + 2 * y.length + 12) :=
  loader_of_split xIdx yIdx hne x y _ (split_exact xIdx yIdx hne x y)

/-- A single uniform linear budget in the length of the encoded input. -/
theorem loader_hoareTime_linear (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (loader xIdx yIdx).HoareTime
      (Tapes (Tape.init ((pair x y).map Γ.ofBool))
        (fun _ => Tape.init []) (Tape.init []))
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 1) (binaryTape [] 1))
      (2 * (pair x y).length + 8) := by
  apply (loader_hoareTime xIdx yIdx hne x y).mono_bound
  simp only [pair_length]
  omega

/-- The same actual loader can follow another phase once the input is rewound
and all work/output tapes are started and blank. -/
theorem loader_started_hoareTime (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (loader xIdx yIdx).HoareTime
      (Tapes (binaryTape (pair x y) 1) (fun _ => binaryTape [] 1) (binaryTape [] 1))
      (Tapes (binaryTape (pair x y) ((pair x y).length + 1))
        (workLayout xIdx yIdx x y 1 1) (binaryTape [] 1))
      (3 * x.length + 2 * y.length + 12) := by
  apply loader_of_split xIdx yIdx hne x y
  have h := TM.pairSplitCoreTM_hoareTime_prefix_marker_frame xIdx yIdx hne x y
    (fun _ => binaryTape [] 1) (binaryTape [] 1)
    (fun _ _ _ => binaryTape_read_ne_start _ _ le_rfl)
    (binaryTape_read_ne_start _ _ le_rfl)
  refine h.consequence ?_ ?_ le_rfl
  · intro inp work out hh
    rcases hh with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩
  · intro inp work out hh
    rcases hh with ⟨hih, hic, hx0, hx, hy0, hy, hw, ho⟩
    refine ⟨Tape.ext hih hic, ?_, ho⟩
    funext i
    simp only [workLayout]
    split
    · subst i
      exact Tape.ext hx.1 (Tape.HasBinaryContent.cells_eq_init hx.2 hx0)
    · next hix =>
      split
      · subst i
        exact Tape.ext hy.1 (Tape.HasBinaryContent.cells_eq_init hy.2 hy0)
      · next hiy => exact hw i hix hiy

variable {n : ℕ}

/-- Work tape that becomes the verifier's virtual source input. -/
def sourceIndex (n : ℕ) : Fin (n + 2) := Fin.last (n + 1)

/-- Work tape containing the canonical nondeterministic choices. -/
def witnessIndex (n : ℕ) : Fin (n + 2) := (Fin.last n).castSucc

@[simp] theorem sourceIndex_ne_witnessIndex (n : ℕ) :
    sourceIndex n ≠ witnessIndex n := by
  simp [sourceIndex, witnessIndex, Fin.ext_iff]

/-- The canonical-pair language checked by the eventual total verifier. -/
def canonicalLanguage (N : NTM n) : Language :=
  {z | ∃ x bits, z = pair x bits ∧
    CanonicalVerifier.canonicalListFrom N bits (N.initCfg x)}

@[simp] theorem pair_mem_canonicalLanguage_iff (N : NTM n) (x bits : List Bool) :
    pair x bits ∈ canonicalLanguage N ↔
      CanonicalVerifier.canonicalListFrom N bits (N.initCfg x) := by
  constructor
  · rintro ⟨x', bits', heq, h⟩
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact h
  · intro h
    exact ⟨x, bits, rfl, h⟩

/-- Splitting and prepared verification on the canonical pair domain. -/
def canonicalMachine (N : NTM n) : TM (n + 2) :=
  TM.seqTM (loader (sourceIndex n) (witnessIndex n))
    (CanonicalVerifierEntry.machine N)

private theorem loader_to_entry (_N : NTM n) (x bits : List Bool) :
    ∀ inp work out,
      Tapes (binaryTape (pair x bits) ((pair x bits).length + 1))
        (workLayout (sourceIndex n) (witnessIndex n) x bits 1 1)
        (binaryTape [] 1) inp work out →
      (∀ j : Fin n, (TM.transitionTape (work j.castSucc.castSucc)) =
        CanonicalVerifier.witnessTape []) ∧
      TM.transitionTape (work (Fin.last n).castSucc) =
        CanonicalVerifier.witnessTape bits ∧
      TM.transitionTape (work (Fin.last (n + 1))) =
        CanonicalVerifier.witnessTape x ∧
      TM.transitionTape out = CanonicalVerifier.witnessTape [] := by
  intro inp work out h
  rcases h with ⟨rfl, rfl, rfl⟩
  have htrans (i : Fin (n + 2)) :
      TM.transitionTape (workLayout (sourceIndex n) (witnessIndex n) x bits 1 1 i) =
      workLayout (sourceIndex n) (witnessIndex n) x bits 1 1 i :=
    TM.transitionTape_eq_self
      ((workLayout_startInvariant _ _ _ _ _ _ i).read_ne_start
        (workLayout_head_pos _ _ _ _ _ _ le_rfl le_rfl i))
  simp only [htrans]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hjx : j.castSucc.castSucc ≠ sourceIndex n := by
      simp [sourceIndex, Fin.ext_iff]; omega
    have hjw : j.castSucc.castSucc ≠ witnessIndex n := by
      simp [witnessIndex, Fin.ext_iff]; omega
    simp [workLayout, hjx, hjw, CanonicalVerifier.witnessTape]
  · simpa only [witnessIndex, CanonicalVerifier.witnessTape, binaryTape_one] using
      (workLayout_y (sourceIndex n) (witnessIndex n)
        (sourceIndex_ne_witnessIndex n) x bits 1 1)
  · exact workLayout_x _ _ _ _ _ _
  · exact TM.transitionTape_eq_self (binaryTape_read_ne_start [] 1 le_rfl)

/-- The ordinary-input machine decides canonical witnesses on every valid
pair, with all loading and entry costs included. -/
theorem canonicalMachine_hoareTime (N : NTM n) (x bits : List Bool) :
    (canonicalMachine N).HoareTime
      (Tapes (Tape.init ((pair x bits).map Γ.ofBool))
        (fun _ => Tape.init []) (Tape.init []))
      (fun _ _ out => out.cells 1 = Γ.ofBool
        (decide (CanonicalVerifier.canonicalListFrom N bits (N.initCfg x))))
      (3 * x.length + 4 * bits.length + 18) := by
  have h := TM.seqTM_hoareTime _ _
    (loader_hoareTime (sourceIndex n) (witnessIndex n)
      (sourceIndex_ne_witnessIndex n) x bits)
    (loader_to_entry N x bits) (CanonicalVerifierEntry.started_hoareTime N x bits)
  convert h using 1 <;> first | rfl | omega

/-- Started-input form used by the validator's successful branch. -/
theorem canonicalMachine_started_hoareTime (N : NTM n) (x bits : List Bool) :
    (canonicalMachine N).HoareTime
      (Tapes (binaryTape (pair x bits) 1) (fun _ => binaryTape [] 1) (binaryTape [] 1))
      (fun _ _ out => out.cells 1 = Γ.ofBool
        (decide (CanonicalVerifier.canonicalListFrom N bits (N.initCfg x))))
      (3 * x.length + 4 * bits.length + 18) := by
  have h := TM.seqTM_hoareTime _ _
    (loader_started_hoareTime (sourceIndex n) (witnessIndex n)
      (sourceIndex_ne_witnessIndex n) x bits)
    (loader_to_entry N x bits) (CanonicalVerifierEntry.started_hoareTime N x bits)
  convert h using 1 <;> first | rfl | omega

/-- Add the output-marker invariant to any Hoare result whose precondition
supplies it; this uses the actual deterministic reachability proof. -/
theorem hoareTime_outputInvariant (M : TM k) {pre post : TapePred k} {bound : ℕ}
    (h : M.HoareTime pre post bound)
    (hpre : ∀ inp work out, pre inp work out → out.StartInvariant) :
    M.HoareTime pre (fun inp work out => out.StartInvariant ∧ post inp work out) bound := by
  intro inp work out hp
  obtain ⟨c, t, ht, hr, hh, hpost⟩ := h inp work out hp
  have ho := hpre inp work out hp
  exact ⟨c, t, ht, hr, hh,
    ⟨TM.output_cells_zero_eq_start_of_reachesIn hr ho.1,
      TM.output_cells_ne_start_of_reachesIn hr ho.2⟩, hpost⟩

/-- Rewind the preserved encoded input without changing blank work/output. -/
theorem rewindInput_hoareTime (z : List Bool) (bound : ℕ) :
    (TM.rewindInputTM (n := k)).HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ inp.head ≤ bound ∧
        work = (fun _ => binaryTape [] 1) ∧ out = binaryTape [] 1)
      (Tapes (binaryTape z 1) (fun _ => binaryTape [] 1) (binaryTape [] 1))
      (bound + 2) := by
  let P : TapePred k := fun inp work out =>
    inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      work = (fun _ => binaryTape [] 1) ∧ out = binaryTape [] 1
  have h := TM.rewindInputTM_hoareTime_frame (n := k) bound (P := P) (by
    intro inp work out inp' work' out' hp hc _ hw ho
    exact ⟨hc.trans hp.1, hw.trans hp.2.1, ho.trans hp.2.2⟩)
  refine h.consequence ?_ ?_ le_rfl
  · intro inp work out hp
    rcases hp with ⟨hc, hh, rfl, rfl⟩
    refine ⟨?_, ?_, hh, binaryTape_read_ne_start _ _ le_rfl, le_rfl,
      fun _ => ⟨binaryTape_read_ne_start _ _ le_rfl, le_rfl⟩, hc, rfl, rfl⟩
    · rw [hc]; rfl
    · rw [hc]; exact Tape.init_ofBool_cells_ne_start z
  · intro inp work out hp
    exact ⟨Tape.ext hp.1 hp.2.1, hp.2.2⟩

/-- A completed verdict together with the invariant needed by the final
conditional-machine phase transition. -/
def Verdict (N : NTM n) (z : List Bool) : TapePred (n + 2) := fun _ _ out =>
  out.StartInvariant ∧
    (z ∈ canonicalLanguage N → out.cells 1 = Γ.one) ∧
    (z ∉ canonicalLanguage N → out.cells 1 = Γ.zero)

private theorem verdict_transition (N : NTM n) (z : List Bool) :
    ∀ inp work out, Verdict N z inp work out →
      Verdict N z (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
        (TM.transitionTape out) := by
  intro inp work out h
  have heq := TM.transitionTape_cells out h.1.2
  exact ⟨⟨by rw [heq]; exact h.1.1, by rw [heq]; exact h.1.2⟩,
    by rw [heq]; exact h.2⟩

private theorem canonicalMachine_started_verdict (N : NTM n) (x bits : List Bool) :
    (canonicalMachine N).HoareTime
      (Tapes (binaryTape (pair x bits) 1) (fun _ => binaryTape [] 1) (binaryTape [] 1))
      (Verdict N (pair x bits)) (3 * x.length + 4 * bits.length + 18) := by
  have h := hoareTime_outputInvariant _ (canonicalMachine_started_hoareTime N x bits)
    (by intro inp work out hp; rw [hp.2.2]; exact binaryTape_startInvariant [] 1)
  refine h.strengthen_post ?_
  intro inp work out hp
  refine ⟨hp.1, ?_, ?_⟩
  · intro hmem
    have hc := (pair_mem_canonicalLanguage_iff N x bits).mp hmem
    simpa [hc, Γ.ofBool] using hp.2
  · intro hmem
    have hc : ¬CanonicalVerifier.canonicalListFrom N bits (N.initCfg x) :=
      fun h => hmem ((pair_mem_canonicalLanguage_iff N x bits).mpr h)
    simpa [hc, Γ.ofBool] using hp.2

/-- Continuation after successful validation and clearing the verdict. -/
def continuation (N : NTM n) : TM (n + 2) :=
  TM.seqTM TM.rewindInputTM (canonicalMachine N)

/-- Validated inputs have real input cells intact, started blank work and
output, and a bounded real-input head. -/
def Validated (z : List Bool) : TapePred k := fun inp work out =>
  z ∈ validPairEncoding ∧ inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
    inp.head ≤ z.length + 3 ∧ 1 ≤ inp.head ∧ work = (fun _ => binaryTape [] 1) ∧
    out = binaryTape [] 1

/-- The successful continuation has a uniform linear budget. -/
theorem continuation_hoareTime (N : NTM n) (z : List Bool) :
    (continuation N).HoareTime (Validated z) (Verdict N z) (5 * z.length + 24) := by
  intro inp work out hp
  obtain ⟨hv, hc, hh, _, hw, ho⟩ := hp
  obtain ⟨x, bits, rfl⟩ := (mem_validPairEncoding_iff_exists_pair z).mp hv
  have hr := rewindInput_hoareTime (k := n + 2) (pair x bits) ((pair x bits).length + 3)
  have ht : ∀ inp work out,
      Tapes (binaryTape (pair x bits) 1) (fun _ : Fin (n + 2) => binaryTape [] 1)
        (binaryTape [] 1) inp work out →
      Tapes (binaryTape (pair x bits) 1) (fun _ => binaryTape [] 1)
        (binaryTape [] 1) (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact transition_tapes _ _ _ (binaryTape_read_ne_start _ _ le_rfl)
      (binaryTape_read_ne_start _ _ le_rfl) (fun _ => binaryTape_read_ne_start _ _ le_rfl)
  have h := TM.seqTM_hoareTime _ _ hr ht (canonicalMachine_started_verdict N x bits)
  have hb : (pair x bits).length + 3 + 2 + 1 +
      (3 * x.length + 4 * bits.length + 18) ≤ 5 * (pair x bits).length + 24 := by
    simp only [pair_length]; omega
  exact h.mono_bound hb inp work out ⟨hc, hh, hw, ho⟩

/-- Successful validation before its single verdict cell is erased. -/
def BeforeClear (z : List Bool) : TapePred k := fun inp work out =>
  z ∈ validPairEncoding ∧ inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
    inp.head ≤ z.length + 3 ∧ 1 ≤ inp.head ∧
    work = (fun _ => binaryTape [] 1) ∧ out.head = 1 ∧
    out.StartInvariant ∧ ∀ j, 2 ≤ j → out.cells j = Γ.blank

private theorem clear_hoareTime (z : List Bool) :
    (cleanVerdict k).HoareTime (BeforeClear z) (Validated z) 1 := by
  intro inp work out hp
  obtain ⟨hv, hc, hh, hpos, hw, hoh, howf, hotail⟩ := hp
  have hi : inp.read ≠ Γ.start := by
    change inp.cells inp.head ≠ Γ.start
    rw [hc]
    exact Tape.init_ofBool_cells_ne_start z inp.head hpos
  have hwork : ∀ i, (work i).read ≠ Γ.start := by
    rw [hw]
    exact fun _ => binaryTape_read_ne_start [] 1 le_rfl
  obtain ⟨c, t, ht, hr, hhalt, hic, hwc, hoc⟩ :=
    cleanVerdict_hoareTime k inp work hi hwork inp work out
      ⟨rfl, rfl, hoh, howf, hotail⟩
  exact ⟨c, t, ht, hr, hhalt, hv, hic ▸ hc, hic ▸ hh, hic ▸ hpos, hwc.trans hw, hoc⟩

/-- The successful branch clears the validator verdict, rewinds the encoded
input, and executes the proved split-and-verify continuation. -/
def success (N : NTM n) : TM (n + 2) :=
  TM.seqTM (cleanVerdict (n + 2)) (continuation N)

private theorem success_hoareTime (N : NTM n) (z : List Bool) :
    (success N).HoareTime (BeforeClear z) (Verdict N z) (5 * z.length + 26) := by
  have ht : ∀ (inp : Tape) (work : Fin (n + 2) → Tape) (out : Tape), Validated z inp work out →
      Validated z (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
        (TM.transitionTape out) := by
    intro inp work out hp
    obtain ⟨hv, hc, hh, hpos, hw, ho⟩ := hp
    have hi : inp.read ≠ Γ.start := by
      change inp.cells inp.head ≠ Γ.start
      rw [hc]
      exact Tape.init_ofBool_cells_ne_start z inp.head hpos
    rw [TM.transitionInput_eq_self hi]
    subst work; subst out
    have hb := TM.transitionTape_eq_self (binaryTape_read_ne_start [] 1 le_rfl)
    simpa only [hb] using
      (show Validated z inp (fun _ : Fin (n + 2) => binaryTape [] 1) (binaryTape [] 1) from
        ⟨hv, hc, hh, hpos, rfl, rfl⟩)
  have h := TM.seqTM_hoareTime _ _ (clear_hoareTime (k := n + 2) z) ht
    (continuation_hoareTime N z)
  convert h using 1 <;> first | rfl | omega

private def RejectPre (N : NTM n) (z : List Bool) : TapePred (n + 2) :=
  fun _ _ out => z ∉ canonicalLanguage N ∧ out.StartInvariant ∧ out.head ≤ 1

private theorem reject_hoareTime (N : NTM n) (z : List Bool) :
    (TM.writeZeroTM (n := n + 2)).HoareTime (RejectPre N z) (Verdict N z) 4 := by
  have h : (TM.writeZeroTM (n := n + 2)).HoareTime (RejectPre N z)
      (fun _ _ out => z ∉ canonicalLanguage N ∧ out.cells 1 = Γ.zero) 4 := by
    intro inp work out hp
    obtain ⟨c, t, ht, hr, hh, ho⟩ := TM.writeTM_hoareTime (n := n + 2) .zero 1
      inp work out ⟨hp.2.1.1, hp.2.1.2, hp.2.2⟩
    exact ⟨c, t, ht, hr, hh, hp.1, ho⟩
  exact (hoareTime_outputInvariant _ h (fun _ _ _ hp => hp.2.1)).strengthen_post
    (fun _ _ _ hp => ⟨hp.1, fun hm => False.elim (hp.2.1 hm), fun _ => hp.2.2⟩)

/-- Add unused work tapes to the zero-work-tape validator, transporting its
arity across `0 + k = k`. -/
def validatorMachine (k : ℕ) : TM k :=
  cast (congrArg TM (Nat.zero_add k)) (TM.pairValidateTM.liftTM k)

private theorem validatorMachine_hoareTime (k : ℕ) (z : List Bool) :
    (validatorMachine k).HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => TM.AllTapesWF inp work out ∧
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head ≤ z.length + 2 ∧
        (∀ i, work i = (Tape.init []).move .right) ∧
        out.head ≤ z.length + 2 ∧
        (z ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (z ∉ validPairEncoding → out.cells 1 = Γ.zero) ∧
        (∀ j, 2 ≤ j → out.cells j = Γ.blank)) (z.length + 2) := by
  let spec : (j : ℕ) → TM j → Prop := fun _ M => M.HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => TM.AllTapesWF inp work out ∧
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head ≤ z.length + 2 ∧
        (∀ i, work i = (Tape.init []).move .right) ∧
        out.head ≤ z.length + 2 ∧
        (z ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (z ∉ validPairEncoding → out.cells 1 = Γ.zero) ∧
        (∀ j, 2 ≤ j → out.cells j = Γ.blank)) (z.length + 2)
  have transport {j j' : ℕ} (heq : j = j') (M : TM j)
      (h : spec j M) : spec j' (cast (congrArg TM heq) M) := by
    cases heq
    exact h
  exact transport (Nat.zero_add k) _ (validator_hoareTime k z)

/-- A total, ordinary-input deterministic machine for canonical witnesses.
Malformed encodings take a proved rejecting branch. -/
def machine (N : NTM n) : TM (n + 2) :=
  TM.ifTM (validatorMachine (n + 2)) (success N) TM.writeZeroTM

/-- All ordinary inputs, including malformed encodings, halt with the correct
verdict in a single explicit linear time bound. -/
theorem machine_hoareTime (N : NTM n) (z : List Bool) :
    (machine N).HoareTime
      (Tapes (Tape.init (z.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []))
      (Verdict N z) (7 * z.length + 35) := by
  have hthen : ∀ (inp : Tape) (work : Fin (n + 2) → Tape) (out : Tape),
      (TM.AllTapesWF inp work out ∧
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head ≤ z.length + 2 ∧
        (∀ i, work i = (Tape.init []).move .right) ∧
        out.head ≤ z.length + 2 ∧
        (z ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (z ∉ validPairEncoding → out.cells 1 = Γ.zero) ∧
        (∀ j, 2 ≤ j → out.cells j = Γ.blank)) →
      out.cells 1 = Γ.one → BeforeClear z (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) ⟨1, out.cells⟩ := by
    intro inp work out hp hy
    obtain ⟨hwf, hc, hh, hw, _, _, hn, ht⟩ := hp
    have hv : z ∈ validPairEncoding := by
      by_contra hno
      have hzero := hn hno
      rw [hy] at hzero
      cases hzero
    refine ⟨hv, ?_, ?_, TM.transitionInput_head_ge inp hwf.1, ?_, rfl,
      ⟨hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩, ht⟩
    · exact (TM.transitionInput_cells inp).trans hc
    · simp only [TM.transitionInput, Tape.move, TM.idleDir]
      split <;> simp_all <;> omega
    · funext i
      rw [hw i]
      exact TM.transitionTape_eq_self (binaryTape_read_ne_start [] 1 le_rfl)
  have helse : ∀ (inp : Tape) (work : Fin (n + 2) → Tape) (out : Tape),
      (TM.AllTapesWF inp work out ∧
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head ≤ z.length + 2 ∧
        (∀ i, work i = (Tape.init []).move .right) ∧
        out.head ≤ z.length + 2 ∧
        (z ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (z ∉ validPairEncoding → out.cells 1 = Γ.zero) ∧
        (∀ j, 2 ≤ j → out.cells j = Γ.blank)) →
      out.cells 1 ≠ Γ.one → RejectPre N z (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) ⟨1, out.cells⟩ := by
    intro inp work out hp hn
    obtain ⟨hwf, _, _, _, _, hy, _, _⟩ := hp
    refine ⟨?_, ⟨hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩, le_rfl⟩
    rintro ⟨x, bits, rfl, _⟩
    exact hn (hy (pair_mem_validPairEncoding x bits))
  have h := TM.ifTM_hoareTime _ _ _ (validatorMachine_hoareTime (n + 2) z)
    (fun _ _ _ hp => hp.1) (fun _ _ _ hp => hp.2.2.2.2.1)
    hthen helse (success_hoareTime N z) (reject_hoareTime N z)
    (verdict_transition N z) (verdict_transition N z)
  convert h using 1 <;> first | rfl | omega

/-- Machine-based polynomial-time decidability, with the complete encoded
input-loading and malformed-input costs accounted for. -/
theorem machine_decidesInTime (N : NTM n) :
    (machine N).DecidesInTime (canonicalLanguage N) (fun length => 7 * length + 35) := by
  intro z
  obtain ⟨c, t, ht, hr, hh, _, hy, hn⟩ := machine_hoareTime N z
    (Tape.init (z.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl, rfl, rfl⟩
  exact ⟨c, t, ht, hr, hh, hy, hn⟩

/-- Every source NTM has an ordinary encoded-input canonical-witness language
in the unchanged machine-based class `Complexity.P`. -/
theorem canonicalLanguage_mem_P (N : NTM n) : canonicalLanguage N ∈ Complexity.P := by
  apply Set.mem_iUnion.mpr
  refine ⟨1, n + 2, machine N, (fun length => 7 * length + 35),
    machine_decidesInTime N, ?_⟩
  have h : (fun length : ℕ => length) =O (· ^ 1) := by
    simpa only [pow_one] using BigO.refl (fun length : ℕ => length)
  exact (BigO.const_mul_left 7 h).add (BigO.const_le_pow 35 1)

end Toda.Counting.EncodedVerifier

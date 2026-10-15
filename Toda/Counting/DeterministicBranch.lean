import Complexitylib.Classes.SharpP
import Complexitylib.Classes.P.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# A deterministic machine with one productive nondeterministic branch

The ordinary `TM.toNTM` duplicates every deterministic transition. That
embedding preserves acceptance but does not preserve the number of accepting
leaves. Here `false` simulates a deterministic transition and `true` starts a
rejecting cleanup. Cleanup scans the output head back to its left-end marker,
moves to cell one, writes zero, and then enters the shared halt state.
-/

namespace Toda.Counting.DeterministicBranch

set_option backward.isDefEq.respectTransparency false

open Complexity

variable {n : ℕ}

/-- Two additional states: `false` scans left and `true` clears the verdict. -/
abbrev State (M : TM n) := Sum M.Q Bool

private def rejectDelta (M : TM n) (clear : Bool) (o : Γ) :
    State M × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
  if clear then
    (.inl M.qhalt, fun _ => .blank, .zero, .right, fun _ => .right, .right)
  else if o = .start then
    (.inr true, fun _ => .blank, .zero, .right, fun _ => .right, .right)
  else
    (.inr false, fun _ => .blank, .zero, .right, fun _ => .right, .left)

private def branchDelta (M : TM n) (b : Bool) (q : State M)
    (i : Γ) (w : Fin n → Γ) (o : Γ) :
    State M × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
  match q with
  | .inl q =>
      if b then rejectDelta M false o
      else
        let (q', ww, ow, id, wd, od) := M.δ q i w o
        (.inl q', ww, ow, id, wd, od)
  | .inr clear => rejectDelta M clear o

/-- The count-preserving embedding, with unchanged input/work/output tapes. -/
def machine (M : TM n) : NTM n where
  Q := State M
  qstart := .inl M.qstart
  qhalt := .inl M.qhalt
  δ := branchDelta M
  δ_right_of_start := by
    intro b q i w o
    cases q with
    | inl q =>
      cases b with
      | false =>
        simpa [branchDelta] using M.δ_right_of_start q i w o
      | true =>
        by_cases h : o = .start <;> simp [branchDelta, rejectDelta, h]
    | inr clear =>
      cases clear <;> by_cases h : o = .start <;> simp [branchDelta, rejectDelta, h]

/-- Embed a source configuration without changing its tapes. -/
def embed (M : TM n) (c : Cfg n M.Q) : Cfg n (machine M).Q where
  state := .inl c.state
  input := c.input
  work := c.work
  output := c.output

@[simp] theorem embed_initCfg (M : TM n) (x : List Bool) :
    embed M (M.initCfg x) = (machine M).initCfg x := rfl

@[simp] theorem halted_embed (M : TM n) (c : Cfg n M.Q) :
    (machine M).halted (embed M c) ↔ M.halted c := by
  simp [NTM.halted, TM.halted, Cfg.isHalted, embed, machine]

/-- In cleanup, scanning requires the usual tape invariant; clearing occurs at
cell one. The terminal case records an explicit rejecting output. -/
def Rejecting (M : TM n) (c : Cfg n (machine M).Q) : Prop :=
  (c.state = .inr false ∧ c.output.StartInvariant) ∨
  (c.state = .inr true ∧ c.output.head = 1) ∨
  (c.state = .inl M.qhalt ∧ c.output.cells 1 = .zero)

private theorem read_start_iff (t : Tape) (h : t.StartInvariant) :
    t.read = .start ↔ t.head = 0 := by
  constructor
  · intro hr
    by_contra hn
    exact h.read_ne_start (by omega) hr
  · intro hz
    simpa [Tape.read, hz] using h.1

theorem rejecting_not_accepting (M : TM n) (c : Cfg n (machine M).Q)
    (h : Rejecting M c) : ¬ ((machine M).halted c ∧ c.output.cells 1 = .one) := by
  rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨_, ho⟩
  · simp [NTM.halted, Cfg.isHalted, machine, hs]
  · simp [NTM.halted, Cfg.isHalted, machine, hs]
  · simp [ho]

/-- Once cleanup begins, every subsequent branch remains rejecting. -/
theorem rejecting_trace_one (M : TM n) (c : Cfg n (machine M).Q)
    (b : Bool) (h : Rejecting M c) :
    Rejecting M ((machine M).trace 1 (fun _ => b) c) := by
  rcases h with ⟨hs, hi⟩ | ⟨hs, hh⟩ | ⟨hs, ho⟩
  · by_cases hr : c.output.read = .start
    · right; left
      have hz := (read_start_iff c.output hi).mp hr
      simp [NTM.trace, machine, branchDelta, rejectDelta, hs, hr,
        Tape.writeAndMove, Tape.move, Tape.write_head, hz]
    · left
      constructor
      · simp [NTM.trace, machine, branchDelta, rejectDelta, hs, hr]
      · simpa [NTM.trace, machine, branchDelta, rejectDelta, hs, hr] using
          hi.writeAndMove Γw.zero Dir3.left
  · right; right
    simp [NTM.trace, machine, branchDelta, rejectDelta, hs,
      Tape.writeAndMove, Tape.move, Tape.write, hh, Γw.toΓ]
  · have hh : (machine M).halted c := hs
    rw [NTM.trace_halted _ _ _ hh]
    exact Or.inr (Or.inr ⟨hs, ho⟩)

/-- No amount of duplicated cleanup work contributes an accepting leaf. -/
theorem acceptLeafCountFrom_rejecting (M : TM n) (T : ℕ)
    (c : Cfg n (machine M).Q) (h : Rejecting M c) :
    (machine M).acceptLeafCountFrom T c = 0 := by
  induction T generalizing c with
  | zero => simp [NTM.acceptLeafCountFrom, rejecting_not_accepting M c h]
  | succ T ih =>
    by_cases hh : (machine M).halted c
    · have ho : c.output.cells 1 ≠ .one := fun ho =>
        rejecting_not_accepting M c h ⟨hh, ho⟩
      simp [NTM.acceptLeafCountFrom, hh, ho]
    · simp only [NTM.acceptLeafCountFrom, hh, ite_false]
      rw [ih _ (rejecting_trace_one M c false h),
        ih _ (rejecting_trace_one M c true h)]

/-- At every nonhalting source configuration, the true branch starts cleanup. -/
theorem trace_true_rejecting (M : TM n) (c : Cfg n M.Q)
    (hh : ¬ M.halted c) (hi : c.output.StartInvariant) :
    Rejecting M ((machine M).trace 1 (fun _ => true) (embed M c)) := by
  change c.state ≠ M.qhalt at hh
  by_cases hr : c.output.read = .start
  · right; left
    have hz := (read_start_iff c.output hi).mp hr
    simp [NTM.trace, machine, branchDelta, rejectDelta, embed, hh, hr,
      Tape.writeAndMove, Tape.move, Tape.write_head, hz]
  · left
    constructor
    · simp [NTM.trace, machine, branchDelta, rejectDelta, embed, hh, hr]
    · simpa [NTM.trace, machine, branchDelta, rejectDelta, embed, hh, hr] using
        hi.writeAndMove Γw.zero Dir3.left

/-- The false branch reproduces one step of the source deterministic machine. -/
theorem trace_false_one_embed (M : TM n) (c : Cfg n M.Q) :
    (machine M).trace 1 (fun _ => false) (embed M c) =
      embed M (M.toNTM.trace 1 (fun _ => false) c) := by
  by_cases hh : c.state = M.qhalt
  · simp [NTM.trace, machine, embed, TM.toNTM, hh]
  · rcases hd : M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simp [NTM.trace, machine, embed, TM.toNTM, branchDelta, hh, hd]

private theorem trace_cons (N : NTM n) (T : ℕ) (choices : Fin (T + 1) → Bool)
    (c : Cfg n N.Q) :
    N.trace (T + 1) choices c =
      N.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
        (N.trace 1 (fun _ => choices ⟨0, by omega⟩) c) := by
  by_cases hh : c.state = N.qhalt
  · simp [NTM.trace, hh, N.trace_halted T _ hh]
  · simp [NTM.trace, hh]

/-- The unique productive choice sequence faithfully simulates the source. -/
theorem trace_false_embed (M : TM n) (T : ℕ) (c : Cfg n M.Q) :
    (machine M).trace T (fun _ => false) (embed M c) =
      embed M (M.toNTM.trace T (fun _ => false) c) := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    rw [trace_cons, trace_false_one_embed, ih,
      trace_cons M.toNTM T (fun _ => false) c]

/-- Exact accepting-leaf count: zero or one according to the deterministic
computation at the same clock. No all-path halting assumption is needed. -/
theorem acceptLeafCountFrom_embed (M : TM n) (T : ℕ) (c : Cfg n M.Q)
    (hi : c.output.StartInvariant) :
    (machine M).acceptLeafCountFrom T (embed M c) =
      if M.toNTM.halted (M.toNTM.trace T (fun _ => false) c) ∧
        (M.toNTM.trace T (fun _ => false) c).output.cells 1 = .one then 1 else 0 := by
  induction T generalizing c with
  | zero =>
    simp [NTM.acceptLeafCountFrom, NTM.trace, embed, TM.toNTM,
      NTM.halted, Cfg.isHalted, machine]
  | succ T ih =>
    by_cases hh : M.halted c
    · have hh' : M.toNTM.halted c := hh
      rw [M.toNTM.trace_halted (T + 1) _ hh']
      have he : (machine M).halted (embed M c) := (halted_embed M c).mpr hh
      rw [NTM.acceptLeafCountFrom, ite_eq_left he]
      change (if c.output.cells 1 = .one then 1 else 0) =
        if c.state = M.qhalt ∧ c.output.cells 1 = .one then 1 else 0
      simp only [show c.state = M.qhalt from hh, true_and]
    · have hh' : ¬ (machine M).halted (embed M c) := by simpa using hh
      rw [NTM.acceptLeafCountFrom, ite_eq_right hh', trace_false_one_embed,
        acceptLeafCountFrom_rejecting M T _ (trace_true_rejecting M c hh hi), Nat.add_zero]
      have hi' : (M.toNTM.trace 1 (fun _ => false) c).output.StartInvariant := by
        by_cases hs : c.state = M.qhalt
        · simp [NTM.trace, TM.toNTM, hs, hi]
        · rcases hd : M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read with
            ⟨q, ww, ow, id, wd, od⟩
          simpa [NTM.trace, TM.toNTM, hs, hd] using hi.writeAndMove ow od
      rw [ih _ hi', trace_cons M.toNTM T (fun _ => false) c]

/-- From a standard initial configuration, the embedding counts a deterministic
accepting computation once, even when that computation halts early. -/
theorem acceptLeafCount_eq (M : TM n) (x : List Bool) (T : ℕ) :
    (machine M).acceptLeafCount x T =
      if M.toNTM.halted (M.toNTM.trace T (fun _ => false) (M.initCfg x)) ∧
        (M.toNTM.trace T (fun _ => false) (M.initCfg x)).output.cells 1 = .one
      then 1 else 0 := by
  exact acceptLeafCountFrom_embed M T (M.initCfg x) Tape.StartInvariant.init_nil

/-- Cleanup halts in at most the original output-head position plus two steps. -/
theorem halted_trace_scan (M : TM n) (k : ℕ) (c : Cfg n (machine M).Q)
    (hs : c.state = .inr false) (hi : c.output.StartInvariant)
    (hk : c.output.head = k) (choices : Fin (k + 2) → Bool) :
    (machine M).halted ((machine M).trace (k + 2) choices c) := by
  induction k generalizing c with
  | zero =>
    have hr : c.output.read = .start := (read_start_iff c.output hi).mpr hk
    simp [NTM.trace, machine, branchDelta, rejectDelta, hs, hr,
      NTM.halted, Cfg.isHalted]
  | succ k ih =>
    have hr : c.output.read ≠ .start := hi.read_ne_start (by omega)
    let c' := (machine M).trace 1 (fun _ => choices ⟨0, by omega⟩) c
    have hs' : c'.state = .inr false := by
      simp [c', NTM.trace, machine, branchDelta, rejectDelta, hs, hr]
    have hi' : c'.output.StartInvariant := by
      simpa [c', NTM.trace, machine, branchDelta, rejectDelta, hs, hr] using
        hi.writeAndMove Γw.zero Dir3.left
    have hk' : c'.output.head = k := by
      simp [c', NTM.trace, machine, branchDelta, rejectDelta, hs, hr,
        Tape.writeAndMove, Tape.move, Tape.write_head, hk]
    rw [trace_cons _ (k + 2)]
    exact ih c' hs' hi' hk' _

private theorem halted_trace_mono (N : NTM n) (c : Cfg n N.Q)
    {T T' : ℕ} (hle : T ≤ T')
    (h : ∀ choices : Fin T → Bool, N.halted (N.trace T choices c))
    (choices : Fin T' → Bool) : N.halted (N.trace T' choices c) := by
  let choicePrefix : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
  rw [N.trace_mono hle (choices := choicePrefix) (fun _ => rfl) (h choicePrefix)]
  exact h choicePrefix

private theorem source_one_output_invariant (M : TM n) (c : Cfg n M.Q)
    (hi : c.output.StartInvariant) :
    (M.toNTM.trace 1 (fun _ => false) c).output.StartInvariant := by
  by_cases hs : c.state = M.qhalt
  · simpa [NTM.trace, TM.toNTM, hs] using hi
  · rcases hd : M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simpa [NTM.trace, TM.toNTM, hs, hd] using hi.writeAndMove ow od

private theorem source_one_output_head_le (M : TM n) (c : Cfg n M.Q) :
    (M.toNTM.trace 1 (fun _ => false) c).output.head ≤ c.output.head + 1 := by
  by_cases hs : c.state = M.qhalt
  · simp [NTM.trace, TM.toNTM, hs]
  · rcases hd : M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simpa [NTM.trace, TM.toNTM, hs, hd] using c.output.head_writeAndMove_le ow od

/-- A rejecting first choice halts after at most `head + 2` transitions. -/
theorem halted_trace_true_first (M : TM n) (c : Cfg n M.Q)
    (hh : ¬ M.halted c) (hi : c.output.StartInvariant)
    (choices : Fin (c.output.head + 2) → Bool) (hb : choices ⟨0, by omega⟩ = true) :
    (machine M).halted ((machine M).trace (c.output.head + 2) choices (embed M c)) := by
  let r : Cfg n (machine M).Q :=
    { state := .inr false, input := c.input, work := c.work, output := c.output }
  have heq : (machine M).trace 1 (fun _ => true) (embed M c) =
      (machine M).trace 1 (fun _ => true) r := by
    change c.state ≠ M.qhalt at hh
    simp [NTM.trace, machine, branchDelta, embed, r, hh]
  have h := halted_trace_scan M c.output.head r rfl hi rfl choices
  rw [trace_cons _ (c.output.head + 1), hb, heq]
  rw [trace_cons _ (c.output.head + 1), hb] at h
  exact h

/-- From any source configuration, a sufficient deterministic clock yields a
linear all-path clock for the count-preserving embedding. -/
theorem halted_trace_embed (M : TM n) (T : ℕ) (c : Cfg n M.Q)
    (hi : c.output.StartInvariant)
    (hh : M.toNTM.halted (M.toNTM.trace T (fun _ => false) c))
    (choices : Fin (2 * T + c.output.head + 2) → Bool) :
    (machine M).halted
      ((machine M).trace (2 * T + c.output.head + 2) choices (embed M c)) := by
  induction T generalizing c with
  | zero =>
    have hc : (machine M).halted (embed M c) := (halted_embed M c).mpr hh
    rw [NTM.trace_halted _ _ _ hc]
    exact hc
  | succ T ih =>
    by_cases hc : M.halted c
    · have hc' := (halted_embed M c).mpr hc
      rw [NTM.trace_halted _ _ _ hc']
      exact hc'
    · by_cases hb : choices ⟨0, by omega⟩ = true
      · let short : Fin (c.output.head + 2) → Bool :=
          fun i => choices ⟨i.val, by omega⟩
        have hs := halted_trace_true_first M c hc hi short hb
        rw [(machine M).trace_mono (by omega : c.output.head + 2 ≤
            2 * (T + 1) + c.output.head + 2) (choices := short)
            (fun _ => rfl) hs]
        exact hs
      · have hb' : choices ⟨0, by omega⟩ = false := by cases h : choices ⟨0, by omega⟩ <;> simp_all
        let c' := M.toNTM.trace 1 (fun _ => false) c
        have hi' := source_one_output_invariant M c hi
        have hh' : M.toNTM.halted (M.toNTM.trace T (fun _ => false) c') := by
          simpa only [trace_cons M.toNTM T (fun _ => false) c] using hh
        have hhead := source_one_output_head_le M c
        have hrun : ∀ cs : Fin (2 * T + c'.output.head + 2) → Bool,
            (machine M).halted
              ((machine M).trace (2 * T + c'.output.head + 2) cs (embed M c')) :=
          ih c' hi' hh'
        rw [trace_cons _ (2 * (T + 1) + c.output.head + 1), hb', trace_false_one_embed]
        exact halted_trace_mono (machine M) (embed M c') (by dsimp [c']; omega) hrun _

/-- A deterministic clock `T` becomes an all-path clock `2*T+2`. -/
theorem allPathsHaltIn (M : TM n) (T : ℕ → ℕ)
    (hh : ∀ x, M.toNTM.halted
      (M.toNTM.trace (T x.length) (fun _ => false) (M.initCfg x))) :
    (machine M).AllPathsHaltIn (fun m => 2 * T m + 2) := by
  intro x choices
  exact halted_trace_embed M (T x.length) (M.initCfg x)
    Tape.StartInvariant.init_nil (hh x) choices

private theorem source_trace_one_of_step (M : TM n) {c c' : Cfg n M.Q}
    (hs : M.step c = some c') : M.toNTM.trace 1 (fun _ => false) c = c' := by
  have hh := TM.state_ne_qhalt_of_step hs
  rcases hd : M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read with
    ⟨q, ww, ow, id, wd, od⟩
  simp only [TM.step, hh, ite_false, hd, Option.some.injEq] at hs
  simpa [NTM.trace, TM.toNTM, hh, hd] using hs

/-- The source trace is justified by its original deterministic step relation. -/
theorem source_trace_of_reachesIn (M : TM n) {t : ℕ} {c c' : Cfg n M.Q}
    (hr : M.reachesIn t c c') : M.toNTM.trace t (fun _ => false) c = c' := by
  induction hr with
  | zero => rfl
  | step hs _ ih => rw [trace_cons, source_trace_one_of_step M hs, ih]

theorem source_trace_eq_of_halted_reachesIn_le (M : TM n)
    {t T : ℕ} {c c' : Cfg n M.Q} (hle : t ≤ T) (hr : M.reachesIn t c c')
    (hh : M.halted c') : M.toNTM.trace T (fun _ => false) c = c' := by
  have heq := source_trace_of_reachesIn M hr
  have hhalt : M.toNTM.halted (M.toNTM.trace t (fun _ => false) c) := by
    rw [heq]
    exact hh
  rw [M.toNTM.trace_mono hle (choices := fun _ => false) (fun _ => rfl) hhalt, heq]

private theorem source_trace_reachesIn_le (M : TM n) (T : ℕ) (c : Cfg n M.Q) :
    ∃ t, t ≤ T ∧ M.reachesIn t c (M.toNTM.trace T (fun _ => false) c) := by
  induction T generalizing c with
  | zero => exact ⟨0, le_rfl, TM.reachesIn.zero⟩
  | succ T ih =>
    by_cases hh : M.halted c
    · have hh' : M.toNTM.halted c := hh
      rw [M.toNTM.trace_halted (T + 1) _ hh']
      exact ⟨0, by omega, TM.reachesIn.zero⟩
    · cases hs : M.step c with
      | none => exact (hh (TM.step_eq_none_iff_halted.mp hs)).elim
      | some c' =>
        obtain ⟨t, ht, hr⟩ := ih c'
        rw [trace_cons, source_trace_one_of_step M hs]
        exact ⟨t + 1, by omega, TM.reachesIn.step hs hr⟩

/-- The clocked source verdict is exactly the canonical deterministic
`AcceptsInTime` predicate, including early halting. -/
theorem acceptsInTime_iff_source_trace (M : TM n) (x : List Bool) (T : ℕ) :
    M.AcceptsInTime x T ↔
      M.toNTM.halted (M.toNTM.trace T (fun _ => false) (M.initCfg x)) ∧
        (M.toNTM.trace T (fun _ => false) (M.initCfg x)).output.cells 1 = .one := by
  constructor
  · rintro ⟨c, t, ht, hr, hh, ho⟩
    rw [source_trace_eq_of_halted_reachesIn_le M ht hr hh]
    exact ⟨hh, ho⟩
  · intro h
    obtain ⟨t, ht, hr⟩ := source_trace_reachesIn_le M T (M.initCfg x)
    exact ⟨_, t, ht, hr, h.1, h.2⟩

/-- The count is the indicator of canonical deterministic timed acceptance. -/
theorem acceptLeafCount_eq_ite_acceptsInTime (M : TM n) (x : List Bool) (T : ℕ) :
    (machine M).acceptLeafCount x T =
      @ite ℕ (M.AcceptsInTime x T) (Classical.propDecidable _) 1 0 := by
  classical
  rw [acceptLeafCount_eq, acceptsInTime_iff_source_trace]
  by_cases h : M.toNTM.halted (M.toNTM.trace T (fun _ => false) (M.initCfg x)) ∧
      (M.toNTM.trace T (fun _ => false) (M.initCfg x)).output.cells 1 = .one <;> simp [h]

/-- A deterministic language decider induces an all-path polynomial-scale
clock with factor two and an additive two cleanup transitions. -/
theorem allPathsHaltIn_of_decidesInTime (M : TM n) (L : Language) (T : ℕ → ℕ)
    (h : M.DecidesInTime L T) :
    (machine M).AllPathsHaltIn (fun m => 2 * T m + 2) := by
  apply allPathsHaltIn M T
  intro x
  obtain ⟨c, t, ht, hr, hh, _⟩ := h x
  rw [source_trace_eq_of_halted_reachesIn_le M ht hr hh]
  exact hh

/-- Under a source decision-time guarantee, the accepting-leaf count is the
language indicator for every clock at least as large as that guarantee. -/
theorem acceptLeafCount_eq_ite_mem_of_decidesInTime (M : TM n) (L : Language)
    (T : ℕ → ℕ) (h : M.DecidesInTime L T) (x : List Bool) (U : ℕ)
    (hU : T x.length ≤ U) :
    (machine M).acceptLeafCount x U =
      @ite ℕ (x ∈ L) (Classical.propDecidable _) 1 0 := by
  classical
  obtain ⟨c, t, ht, hr, hh, hyes, hno⟩ := h x
  rw [acceptLeafCount_eq, source_trace_eq_of_halted_reachesIn_le M (ht.trans hU) hr hh]
  change (if c.state = M.qhalt ∧ c.output.cells 1 = .one then 1 else 0) =
    if x ∈ L then 1 else 0
  by_cases hx : x ∈ L
  · simp [hx, show c.state = M.qhalt from hh, hyes hx]
  · simp [hx, hno hx]

/-- The natural-valued indicator of a language. -/
noncomputable def indicator (L : Language) (x : List Bool) : ℕ := by
  classical
  exact if x ∈ L then 1 else 0

/-- A polynomial-time deterministic decider gives a genuine accepting-leaf
counting machine for the language indicator. -/
theorem indicator_mem_sharpP_of_decidesInTime (M : TM n) (L : Language)
    (T : ℕ → ℕ) (d : ℕ) (hdec : M.DecidesInTime L T) (hpoly : T =O (· ^ d)) :
    indicator L ∈ SharpP := by
  refine ⟨n, machine M, (fun m => 2 * T m + 2), d,
    allPathsHaltIn_of_decidesInTime M L T hdec, ?_, ?_⟩
  · exact (BigO.const_mul_left 2 hpoly).add (BigO.const_le_pow 2 d)
  · intro x
    simpa [indicator] using
      (acceptLeafCount_eq_ite_mem_of_decidesInTime M L T hdec x
        (2 * T x.length + 2) (by omega)).symm

/-- Every canonical polynomial-time language has its `0/1` indicator in the
canonical accepting-leaf class `SharpP`. No simulation assumption remains. -/
theorem indicator_mem_sharpP (L : Language) (hL : L ∈ Complexity.P) :
    indicator L ∈ Complexity.SharpP := by
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨n, M, T, hdec, hpoly⟩ := hd
  exact indicator_mem_sharpP_of_decidesInTime M L T d hdec hpoly

end Toda.Counting.DeterministicBranch

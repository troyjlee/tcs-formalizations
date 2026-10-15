import Toda.Counting.DeterministicBranch
import Toda.Counting.CanonicalWitness
import Complexitylib.Models.TuringMachine.Internal

/-!
# Preserving only genuine nondeterministic choices

An NTM used for counting may have both guessing steps and deterministic
bookkeeping steps. This wrapper keeps both branches at designated guessing
steps. At other steps only the false branch is productive; the true branch
performs the proved rejecting cleanup. The designation can inspect the finite
control and scanned tape symbols, as an ordinary transition function can.
-/

namespace Toda.Counting.SelectiveBranch

open Complexity

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- Select a single transition of the source for the rejecting-wrapper base. -/
def falseTM (N : NTM n) : TM n where
  Q := N.Q
  qstart := N.qstart
  qhalt := N.qhalt
  δ := N.δ false
  δ_right_of_start := N.δ_right_of_start false

/-- A finite-control test for whether both choices should be productive. -/
abbrev BranchTest (N : NTM n) := N.Q → Γ → (Fin n → Γ) → Γ → Bool

private abbrev base (N : NTM n) := DeterministicBranch.machine (falseTM N)

/-- Keep genuine branches and suppress duplicated deterministic branches. -/
def machine (N : NTM n) (branch : BranchTest N) : NTM n where
  Q := (base N).Q
  qstart := (base N).qstart
  qhalt := (base N).qhalt
  δ := fun b q i w o =>
    match q with
    | .inl q' =>
        if branch q' i w o then
          let (r, ww, ow, id, wd, od) := N.δ b q' i w o
          (.inl r, ww, ow, id, wd, od)
        else (base N).δ b q i w o
    | .inr _ => (base N).δ b q i w o
  δ_right_of_start := by
    intro b q i w o
    cases q with
    | inl q =>
      by_cases hb : branch q i w o = true
      · simpa [hb] using N.δ_right_of_start b q i w o
      · simpa [hb] using (base N).δ_right_of_start b (.inl q) i w o
    | inr q => exact (base N).δ_right_of_start b (.inr q) i w o

/-- Embed the source configuration without altering its tapes. -/
def embed (N : NTM n) (c : Cfg n N.Q) : Cfg n (base N).Q :=
  DeterministicBranch.embed (falseTM N) c

/-- Whether the current source step is designated as genuine branching. -/
def branching (N : NTM n) (branch : BranchTest N) (c : Cfg n N.Q) : Bool :=
  branch c.state c.input.read (fun i => (c.work i).read) c.output.read

@[simp] theorem halted_embed (N : NTM n) (branch : BranchTest N) (c : Cfg n N.Q) :
    (machine N branch).halted (embed N c) ↔ N.halted c := by
  simp [machine, embed, base, falseTM, DeterministicBranch.embed,
    DeterministicBranch.machine, NTM.halted, Cfg.isHalted]

@[simp] theorem embed_initCfg (N : NTM n) (branch : BranchTest N) (x : List Bool) :
    embed N (N.initCfg x) = (machine N branch).initCfg x := rfl

/-- The rejection invariant is inherited from the deterministic wrapper. -/
abbrev Rejecting (N : NTM n) (c : Cfg n (base N).Q) : Prop :=
  DeterministicBranch.Rejecting (falseTM N) c

/-- Cleanup transitions agree with the already proved deterministic wrapper. -/
theorem trace_one_rejecting_eq (N : NTM n) (branch : BranchTest N)
    (c : Cfg n (base N).Q) (b : Bool) (h : Rejecting N c) :
    (machine N branch).trace 1 (fun _ => b) c = (base N).trace 1 (fun _ => b) c := by
  rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ <;>
    simp [NTM.trace, machine, hs, base, DeterministicBranch.machine, falseTM]

/-- Rejecting branches stay rejecting under the selective wrapper. -/
theorem rejecting_trace_one (N : NTM n) (branch : BranchTest N)
    (c : Cfg n (base N).Q) (b : Bool) (h : Rejecting N c) :
    Rejecting N ((machine N branch).trace 1 (fun _ => b) c) := by
  rw [trace_one_rejecting_eq N branch c b h]
  exact DeterministicBranch.rejecting_trace_one (falseTM N) c b h

/-- Once rejection starts, the complete trace agrees with the deterministic
wrapper's cleanup, for every choice tape. -/
theorem trace_rejecting_eq (N : NTM n) (branch : BranchTest N) (T : ℕ)
    (c : Cfg n (base N).Q) (choices : Fin T → Bool) (h : Rejecting N c) :
    (machine N branch).trace T choices c = (base N).trace T choices c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    erw [trace_succ_eq (machine N branch) T c choices,
      trace_succ_eq (base N) T c choices,
      trace_one_rejecting_eq N branch c (choices 0) h]
    exact ih _ _ (DeterministicBranch.rejecting_trace_one (falseTM N) c (choices 0) h)

/-- Suppressed branches contribute no accepting leaves at any clock. -/
theorem acceptLeafCountFrom_rejecting (N : NTM n) (branch : BranchTest N)
    (T : ℕ) (c : Cfg n (base N).Q) (h : Rejecting N c) :
    (machine N branch).acceptLeafCountFrom T c = 0 := by
  induction T generalizing c with
  | zero =>
    have hno : ¬ ((machine N branch).halted c ∧ c.output.cells 1 = .one) :=
      DeterministicBranch.rejecting_not_accepting (falseTM N) c h
    simp [NTM.acceptLeafCountFrom, hno]
  | succ T ih =>
    have hno : ¬ ((machine N branch).halted c ∧ c.output.cells 1 = .one) :=
      DeterministicBranch.rejecting_not_accepting (falseTM N) c h
    by_cases hh : (machine N branch).halted c
    · have ho : c.output.cells 1 ≠ .one := fun ho => hno ⟨hh, ho⟩
      simp [NTM.acceptLeafCountFrom, hh, ho]
    · simp only [NTM.acceptLeafCountFrom, hh, ite_false]
      rw [ih _ (rejecting_trace_one N branch c false h),
        ih _ (rejecting_trace_one N branch c true h)]

/-- A productive transition is exactly the corresponding source transition. -/
theorem trace_one_embed (N : NTM n) (branch : BranchTest N) (c : Cfg n N.Q)
    (b : Bool) (hb : b = false ∨ branching N branch c = true) :
    (machine N branch).trace 1 (fun _ => b) (embed N c) =
      embed N (N.trace 1 (fun _ => b) c) := by
  by_cases hh : N.halted c
  · have he := (halted_embed N branch c).mpr hh
    rw [NTM.trace_halted _ _ _ he, NTM.trace_halted _ _ _ hh]
  · change c.state ≠ N.qhalt at hh
    by_cases hg : branching N branch c = true
    · rcases hd : N.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read with
        ⟨q, ww, ow, id, wd, od⟩
      simp [NTM.trace, machine, embed, base, falseTM, DeterministicBranch.embed,
        DeterministicBranch.machine, branching] at hg ⊢
      simp [hh, hg, hd]
    · have hbf : b = false := hb.resolve_right hg
      subst b
      have heq : (machine N branch).trace 1 (fun _ => false) (embed N c) =
          (base N).trace 1 (fun _ => false) (embed N c) := by
        simp [NTM.trace, machine, embed, base, falseTM, DeterministicBranch.embed,
          DeterministicBranch.machine, branching] at hg ⊢
        simp [hh, hg]
      exact heq.trans (DeterministicBranch.trace_false_one_embed (falseTM N) c)

/-- A suppressed true branch takes exactly the base wrapper's rejection step. -/
theorem trace_true_suppressed_eq (N : NTM n) (branch : BranchTest N) (c : Cfg n N.Q)
    (hh : ¬ N.halted c)
    (hg : branching N branch c = false) :
    (machine N branch).trace 1 (fun _ => true) (embed N c) =
      (base N).trace 1 (fun _ => true) (embed N c) := by
  change c.state ≠ N.qhalt at hh
  simp [NTM.trace, machine, embed, base, falseTM, DeterministicBranch.embed,
    DeterministicBranch.machine, branching] at hg ⊢
  simp [hh, hg]

/-- At a non-guessing step, the unused true choice starts rejecting cleanup. -/
theorem trace_true_rejecting (N : NTM n) (branch : BranchTest N) (c : Cfg n N.Q)
    (hh : ¬ N.halted c) (hi : c.output.StartInvariant)
    (hg : branching N branch c = false) :
    Rejecting N ((machine N branch).trace 1 (fun _ => true) (embed N c)) := by
  rw [trace_true_suppressed_eq N branch c hh hg]
  exact DeterministicBranch.trace_true_rejecting (falseTM N) c hh hi

/-- Source-tree count with one productive successor at bookkeeping steps. -/
def branchCount (N : NTM n) (branch : BranchTest N) : ℕ → Cfg n N.Q → ℕ
  | 0, c => if N.halted c ∧ c.output.cells 1 = .one then 1 else 0
  | T + 1, c =>
      if N.halted c then (if c.output.cells 1 = .one then 1 else 0)
      else branchCount N branch T (N.trace 1 (fun _ => false) c) +
        if branching N branch c then branchCount N branch T (N.trace 1 (fun _ => true) c)
        else 0

private theorem output_invariant_one (N : NTM n) (c : Cfg n N.Q) (b : Bool)
    (hi : c.output.StartInvariant) :
    (N.trace 1 (fun _ => b) c).output.StartInvariant := by
  by_cases hh : N.halted c
  · rw [N.trace_halted _ _ hh]; exact hi
  · change c.state ≠ N.qhalt at hh
    rcases hd : N.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simpa [NTM.trace, hh, hd] using hi.writeAndMove ow od

/-- The source-tree recurrence is realized by an actual upstream NTM. -/
theorem acceptLeafCountFrom_embed (N : NTM n) (branch : BranchTest N)
    (T : ℕ) (c : Cfg n N.Q) (hi : c.output.StartInvariant) :
    (machine N branch).acceptLeafCountFrom T (embed N c) = branchCount N branch T c := by
  induction T generalizing c with
  | zero => simp only [NTM.acceptLeafCountFrom, branchCount, halted_embed]; rfl
  | succ T ih =>
    by_cases hh : N.halted c
    · rw [NTM.acceptLeafCountFrom, ite_eq_left ((halted_embed N branch c).mpr hh),
        branchCount, ite_eq_left hh]
      rfl
    · rw [NTM.acceptLeafCountFrom, ite_eq_right (by simpa using hh), branchCount, ite_eq_right hh]
      rw [trace_one_embed N branch c false (Or.inl rfl), ih _ (output_invariant_one N c false hi)]
      cases hg : branching N branch c with
      | false =>
        rw [ite_eq_right (by decide),
          acceptLeafCountFrom_rejecting N branch T _ (trace_true_rejecting N branch c hh hi hg)]
      | true =>
        rw [ite_eq_left rfl, trace_one_embed N branch c true (Or.inr hg),
          ih _ (output_invariant_one N c true hi)]

/-- From an ordinary initial configuration, the wrapper realizes the source
recurrence at exactly the same clock. -/
theorem acceptLeafCount_eq (N : NTM n) (branch : BranchTest N)
    (T : ℕ) (x : List Bool) :
    (machine N branch).acceptLeafCount x T = branchCount N branch T (N.initCfg x) :=
  acceptLeafCountFrom_embed N branch T (N.initCfg x) Tape.StartInvariant.init_nil

/-- A suppressed first choice finishes cleanup within `head + 2` steps. -/
theorem halted_trace_true_first (N : NTM n) (branch : BranchTest N)
    (c : Cfg n N.Q) (hh : ¬ N.halted c) (hi : c.output.StartInvariant)
    (hg : branching N branch c = false)
    (choices : Fin (c.output.head + 2) → Bool) (hb : choices 0 = true) :
    (machine N branch).halted
      ((machine N branch).trace (c.output.head + 2) choices (embed N c)) := by
  have hbase := DeterministicBranch.halted_trace_true_first (falseTM N) c hh hi choices hb
  erw [trace_succ_eq (machine N branch) (c.output.head + 1), hb,
    trace_true_suppressed_eq N branch c hh hg,
    trace_rejecting_eq N branch (c.output.head + 1) _ _
      (DeterministicBranch.trace_true_rejecting (falseTM N) c hh hi)]
  erw [trace_succ_eq (base N) (c.output.head + 1), hb] at hbase
  exact hbase

private theorem halted_trace_mono (N : NTM n) (c : Cfg n N.Q)
    {T T' : ℕ} (hle : T ≤ T')
    (h : ∀ choices : Fin T → Bool, N.halted (N.trace T choices c))
    (choices : Fin T' → Bool) : N.halted (N.trace T' choices c) := by
  let choicePrefix : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
  rw [N.trace_mono hle (choices := choicePrefix) (fun _ => rfl) (h choicePrefix)]
  exact h choicePrefix

/-- A sufficient source all-path clock gives a linear clock for every
selective-wrapper branch, including the rejecting cleanup branches. -/
theorem halted_trace_embed (N : NTM n) (branch : BranchTest N) (T : ℕ)
    (c : Cfg n N.Q) (hi : c.output.StartInvariant)
    (hh : ∀ sourceChoices : Fin T → Bool, N.halted (N.trace T sourceChoices c))
    (choices : Fin (2 * T + c.output.head + 2) → Bool) :
    (machine N branch).halted
      ((machine N branch).trace (2 * T + c.output.head + 2) choices (embed N c)) := by
  induction T generalizing c with
  | zero =>
    have hc : (machine N branch).halted (embed N c) :=
      (halted_embed N branch c).mpr (hh (fun _ => false))
    rw [NTM.trace_halted _ _ _ hc]
    exact hc
  | succ T ih =>
    by_cases hc : N.halted c
    · have hc' := (halted_embed N branch c).mpr hc
      rw [NTM.trace_halted _ _ _ hc']
      exact hc'
    · by_cases hsupp : choices 0 = true ∧ branching N branch c = false
      · let short : Fin (c.output.head + 2) → Bool :=
          fun i => choices ⟨i.val, by omega⟩
        have hs := halted_trace_true_first N branch c hc hi hsupp.2 short hsupp.1
        rw [(machine N branch).trace_mono (by omega : c.output.head + 2 ≤
            2 * (T + 1) + c.output.head + 2) (choices := short)
            (fun _ => rfl) hs]
        exact hs
      · have hproductive : choices 0 = false ∨ branching N branch c = true := by
          cases hb : choices 0 with
          | false => exact Or.inl rfl
          | true =>
            right
            cases hg : branching N branch c with
            | false => exact (hsupp ⟨hb, hg⟩).elim
            | true => rfl
        let c' := N.trace 1 (fun _ => choices 0) c
        have hi' := output_invariant_one N c (choices 0) hi
        have hh' (cs : Fin T → Bool) : N.halted (N.trace T cs c') := by
          have ht := hh (Fin.cons (choices 0) cs)
          rw [trace_succ_eq] at ht
          simpa only [Fin.cons_zero, Fin.tail_cons] using ht
        have hhead := N.output_head_trace_le 1 (fun _ => choices 0) c
        have hrun : ∀ cs : Fin (2 * T + c'.output.head + 2) → Bool,
            (machine N branch).halted
              ((machine N branch).trace (2 * T + c'.output.head + 2) cs (embed N c')) :=
          ih c' hi' hh'
        erw [trace_succ_eq (machine N branch) (2 * (T + 1) + c.output.head + 1),
          trace_one_embed N branch c (choices 0) hproductive]
        exact halted_trace_mono (machine N branch) (embed N c')
          (by dsimp [c']; omega) hrun _

/-- A source all-path clock `T` becomes the wrapper all-path clock `2*T + 2`. -/
theorem allPathsHaltIn (N : NTM n) (branch : BranchTest N) (T : ℕ → ℕ)
    (hh : N.AllPathsHaltIn T) :
    (machine N branch).AllPathsHaltIn (fun length => 2 * T length + 2) := by
  intro x choices
  exact halted_trace_embed N branch (T x.length) (N.initCfg x)
    Tape.StartInvariant.init_nil (hh x) choices

private theorem branchCount_add_eq (N : NTM n) (branch : BranchTest N)
    (T extra : ℕ) (c : Cfg n N.Q)
    (hh : ∀ choices : Fin T → Bool, N.halted (N.trace T choices c)) :
    branchCount N branch (T + extra) c = branchCount N branch T c := by
  induction T generalizing c with
  | zero =>
    have hc : N.halted c := hh (fun _ => false)
    cases extra with
    | zero => rfl
    | succ extra =>
      rw [Nat.zero_add, branchCount.eq_2, ite_eq_left hc, branchCount.eq_1]
      change (if c.output.cells 1 = .one then 1 else 0) =
        if N.halted c ∧ c.output.cells 1 = .one then 1 else 0
      simp only [show c.state = N.qhalt from hc, NTM.halted, Cfg.isHalted, true_and]
  | succ T ih =>
    have hbranch (b : Bool) (cs : Fin T → Bool) :
        N.halted (N.trace T cs (N.trace 1 (fun _ => b) c)) := by
      have ht := hh (Fin.cons b cs)
      rw [trace_succ_eq] at ht
      simpa only [Fin.cons_zero, Fin.tail_cons] using ht
    rw [Nat.succ_add]
    by_cases hc : N.halted c
    · rw [branchCount, ite_eq_left hc, branchCount, ite_eq_left hc]
    · rw [branchCount, ite_eq_right hc, branchCount, ite_eq_right hc,
        ih _ (hbranch false)]
      cases hg : branching N branch c with
      | false => rfl
      | true => rw [ih _ (hbranch true)]

/-- Once every source branch has halted, extending the clock does not change
the selective source-tree count. -/
theorem branchCount_eq_of_le_of_allChoicesHalt (N : NTM n) (branch : BranchTest N)
    {T T' : ℕ} (hle : T ≤ T') (c : Cfg n N.Q)
    (hh : ∀ choices : Fin T → Bool, N.halted (N.trace T choices c)) :
    branchCount N branch T' c = branchCount N branch T c := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact branchCount_add_eq N branch T extra c hh

/-- A polynomial-time source with a finite-control branch designation yields
a genuine canonical #P function, at the original source clock. -/
theorem branchCount_mem_sharpP (N : NTM n) (branch : BranchTest N)
    (T : ℕ → ℕ) (degree : ℕ) (hh : N.AllPathsHaltIn T)
    (hpoly : T =O (· ^ degree)) :
    (fun x => branchCount N branch (T x.length) (N.initCfg x)) ∈ SharpP := by
  refine ⟨n, machine N branch, (fun length => 2 * T length + 2), degree,
    allPathsHaltIn N branch T hh, ?_, ?_⟩
  · exact (BigO.const_mul_left 2 hpoly).add (BigO.const_le_pow 2 degree)
  · intro x
    rw [acceptLeafCount_eq]
    exact (branchCount_eq_of_le_of_allChoicesHalt N branch (by dsimp; omega)
      (N.initCfg x) (hh x)).symm

end Toda.Counting.SelectiveBranch

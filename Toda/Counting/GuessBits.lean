import Toda.Counting.LeafExpansion
import Complexitylib.Models.TuringMachine.Internal

/-!
# Count-preserving guessing from a prepared unary counter

This NTM consumes one unary counter cell and writes one chosen witness bit
per transition. On exhausting the counter, the false branch enters an
arbitrary continuation NTM and the true branch halts rejecting. The prepared
output tape already carries a zero verdict, so the boundary needs no cleanup.

Preparation of the counter, blank witness tape, and continuation runtime are
explicit obligations. This subroutine does not assert a #P closure theorem.
-/

namespace Toda.Counting.GuessBits

open Complexity
open scoped BigOperators

variable {n : ℕ} {Q : Type}

private def copySymbol : Γ → Γw
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

private def stayUnlessStart (symbol : Γ) : Dir3 :=
  if symbol = .start then .right else .stay

private def delta (N : NTM n) (witness counter : Fin n) (b : Bool) (q : Option N.Q)
    (i : Γ) (w : Fin n → Γ) (o : Γ) :
    Option N.Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
  match q with
  | some q =>
      let (q', ww, ow, id, wd, od) := N.δ b q i w o
      (some q', ww, ow, id, wd, od)
  | none =>
      if w counter = .one then
        (none, (fun j => if j = witness then Γw.ofBool b else copySymbol (w j)),
          copySymbol o, stayUnlessStart i,
          (fun j => if j = witness ∨ j = counter then .right else stayUnlessStart (w j)),
          stayUnlessStart o)
      else
        (some (if b then N.qhalt else N.qstart), (fun j => copySymbol (w j)),
          copySymbol o, stayUnlessStart i, (fun j => stayUnlessStart (w j)), stayUnlessStart o)

/-- A guessing prefix followed by an unchanged arbitrary continuation NTM. -/
def machine (N : NTM n) (witness counter : Fin n) : NTM n where
  Q := Option N.Q
  qstart := none
  qhalt := some N.qhalt
  δ := delta N witness counter
  δ_right_of_start := by
    intro b q i w o
    cases q with
    | some q => simpa [delta] using N.δ_right_of_start b q i w o
    | none =>
      by_cases hc : w counter = .one <;>
        simp only [delta, hc, ite_true, ite_false]
      · refine ⟨?_, ?_, ?_⟩
        · intro hi; simp [stayUnlessStart, hi]
        · intro j hj
          by_cases h : j = witness ∨ j = counter <;> simp [h, stayUnlessStart, hj]
        · intro ho; simp [stayUnlessStart, ho]
      · refine ⟨?_, ?_, ?_⟩
        · intro hi; simp [stayUnlessStart, hi]
        · intro j hj; simp [stayUnlessStart, hj]
        · intro ho; simp [stayUnlessStart, ho]

/-- Enter guessing with the supplied tapes. The source state is ignored. -/
def enter (N : NTM n) (witness counter : Fin n) (c : Cfg n N.Q) :
    Cfg n (machine N witness counter).Q :=
  ⟨none, c.input, c.work, c.output⟩

/-- Embed an ordinary continuation configuration without changing its tapes. -/
def embed (N : NTM n) (witness counter : Fin n) (c : Cfg n N.Q) :
    Cfg n (machine N witness counter).Q :=
  ⟨some c.state, c.input, c.work, c.output⟩

/-- Prepared tape heads stay away from markers; the output is initially rejecting. -/
structure Prepared (c : Cfg n Q) : Prop where
  input_nonstart : c.input.read ≠ .start
  work_invariant : ∀ j, (c.work j).StartInvariant
  work_positive : ∀ j, 0 < (c.work j).head
  output_nonstart : c.output.read ≠ .start
  output_zero : c.output.cells 1 = .zero

/-- There are exactly `remaining` consecutive unary ones from the counter head. -/
def CounterRemaining (counter : Fin n) (c : Cfg n Q) (remaining : ℕ) : Prop :=
  (∀ j < remaining, (c.work counter).cells ((c.work counter).head + j) = .one) ∧
    (c.work counter).cells ((c.work counter).head + remaining) = .blank

/-- Tape-level effect of one genuine bit choice. -/
def writeGuess (witness counter : Fin n) (b : Bool) (c : Cfg n Q) : Cfg n Q :=
  { c with work := fun j =>
      if j = witness then (c.work j).writeAndMove (Γw.ofBool b) .right
      else if j = counter then (c.work j).move .right else c.work j }

/-- The deterministic tape state obtained from a specified finite sequence of choices. -/
def afterChoices (witness counter : Fin n) :
    (T : ℕ) → (Fin T → Bool) → Cfg n Q → Cfg n Q
  | 0, _, c => c
  | T + 1, choices, c =>
      afterChoices witness counter T (Fin.tail choices)
        (writeGuess witness counter (choices 0) c)

private theorem copySymbol_coe (s : Γ) (h : s ≠ .start) :
    (copySymbol s : Γ) = s := by cases s <;> simp_all [copySymbol]

private theorem write_read (t : Tape) : t.write t.read = t := by
  unfold Tape.write Tape.read
  split
  · rfl
  · congr
    exact Function.update_eq_self _ _

private theorem copy_stay (t : Tape) (h : t.read ≠ .start) :
    t.writeAndMove (copySymbol t.read) (stayUnlessStart t.read) = t := by
  rw [copySymbol_coe _ h]
  simp only [stayUnlessStart, h, ite_false, Tape.move]
  exact write_read t

private theorem copy_right (t : Tape) (h : t.read ≠ .start) :
    t.writeAndMove (copySymbol t.read) .right = t.move .right := by
  change (t.write (copySymbol t.read)).move .right = t.move .right
  rw [copySymbol_coe _ h, write_read]

@[simp] theorem halted_embed (N : NTM n) (witness counter : Fin n) (c : Cfg n N.Q) :
    (machine N witness counter).halted (embed N witness counter c) ↔ N.halted c := by
  simp [NTM.halted, Cfg.isHalted, machine, embed]

/-- Continuation steps retain both source branches and exactly their configurations. -/
theorem trace_one_embed (N : NTM n) (witness counter : Fin n)
    (c : Cfg n N.Q) (b : Bool) :
    (machine N witness counter).trace 1 (fun _ => b) (embed N witness counter c) =
      embed N witness counter (N.trace 1 (fun _ => b) c) := by
  by_cases hh : c.state = N.qhalt
  · simp [NTM.trace, machine, embed, hh]
  · rcases hd : N.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simp [NTM.trace, machine, delta, embed, hh, hd]

/-- The continuation embedding preserves its entire accepting-leaf count. -/
theorem acceptLeafCountFrom_embed (N : NTM n) (witness counter : Fin n)
    (T : ℕ) (c : Cfg n N.Q) :
    (machine N witness counter).acceptLeafCountFrom T (embed N witness counter c) =
      N.acceptLeafCountFrom T c := by
  induction T generalizing c with
  | zero => simp [NTM.acceptLeafCountFrom, embed, machine, NTM.halted, Cfg.isHalted]
  | succ T ih =>
      by_cases hh : N.halted c
      · have he := (halted_embed N witness counter c).mpr hh
        rw [NTM.acceptLeafCountFrom, ite_eq_left he,
          NTM.acceptLeafCountFrom, ite_eq_left hh]
        rfl
      · have he : ¬ (machine N witness counter).halted (embed N witness counter c) := by
          simpa using hh
        simp only [NTM.acceptLeafCountFrom, hh, he, ite_false, trace_one_embed, ih]

/-- A nonempty counter yields exactly one write transition per chosen bit. -/
theorem trace_one_enter_of_counter_one (N : NTM n) (witness counter : Fin n)
    (hne : witness ≠ counter) (c : Cfg n N.Q) (hc : Prepared c)
    (hcounter : (c.work counter).read = .one) (b : Bool) :
    (machine N witness counter).trace 1 (fun _ => b) (enter N witness counter c) =
      enter N witness counter (writeGuess witness counter b c) := by
  have hw (j : Fin n) : (c.work j).read ≠ .start :=
    (hc.work_invariant j).read_ne_start (hc.work_positive j)
  simp only [NTM.trace, machine, enter, delta, reduceCtorEq, ite_false, hcounter, ite_true]
  apply Cfg.ext
  · rfl
  · simp [stayUnlessStart, hc.input_nonstart, Tape.move, writeGuess]
  · funext j
    by_cases hjw : j = witness
    · subst j; simp [writeGuess]
    · by_cases hjc : j = counter
      · subst j
        simpa [writeGuess, Ne.symm hne, hjw] using copy_right (c.work counter) (hw counter)
      · simpa [writeGuess, hjw, hjc] using copy_stay (c.work j) (hw j)
  · exact copy_stay c.output hc.output_nonstart

/-- Guessing preserves all the prepared tape conditions. -/
theorem prepared_writeGuess (witness counter : Fin n) (b : Bool) (c : Cfg n Q)
    (hc : Prepared c) : Prepared (writeGuess witness counter b c) := by
  refine ⟨hc.input_nonstart, ?_, ?_, hc.output_nonstart, hc.output_zero⟩
  · intro j
    simp only [writeGuess]
    split
    · exact (hc.work_invariant j).writeAndMove (Γw.ofBool b) .right
    · split
      · exact (hc.work_invariant j).move .right
      · exact hc.work_invariant j
  · intro j
    simp only [writeGuess]
    split
    · simp [Tape.writeAndMove, Tape.move, Tape.write_head]
    · split
      · simp [Tape.move]
      · exact hc.work_positive j

/-- A genuine guess advances the unary counter by exactly one symbol. -/
theorem counterRemaining_writeGuess (witness counter : Fin n) (hne : witness ≠ counter)
    (b : Bool) (c : Cfg n Q) (remaining : ℕ)
    (h : CounterRemaining counter c (remaining + 1)) :
    CounterRemaining counter (writeGuess witness counter b c) remaining := by
  simp only [CounterRemaining, writeGuess, Ne.symm hne, ite_false, ite_true, Tape.move]
  constructor
  · intro j hj
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1 (j + 1) (by omega)
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2

/-- The prepared conditions persist after every specified sequence of guesses. -/
theorem prepared_afterChoices (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) (hc : Prepared c) :
    Prepared (afterChoices witness counter T choices c) := by
  induction T generalizing c with
  | zero => exact hc
  | succ T ih => exact ih (Fin.tail choices) _ (prepared_writeGuess witness counter _ c hc)

/-- Guessing exactly the prescribed number of bits exhausts the unary counter. -/
theorem counterRemaining_afterChoices (witness counter : Fin n) (hne : witness ≠ counter)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg n Q)
    (hc : CounterRemaining counter c T) :
    CounterRemaining counter (afterChoices witness counter T choices c) 0 := by
  induction T generalizing c with
  | zero => exact hc
  | succ T ih =>
      exact ih (Fin.tail choices) _ (counterRemaining_writeGuess witness counter hne _ c T hc)

/-- The first `T` transitions consume exactly the `T` supplied choice bits. -/
theorem trace_enter (N : NTM n) (witness counter : Fin n) (hne : witness ≠ counter)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg n N.Q) (hc : Prepared c)
    (hcounter : CounterRemaining counter c T) :
    (machine N witness counter).trace T choices (enter N witness counter c) =
      enter N witness counter (afterChoices witness counter T choices c) := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      have hread : (c.work counter).read = .one := by
        simpa [Tape.read] using hcounter.1 0 (by omega)
      rw [trace_succ_eq, trace_one_enter_of_counter_one N witness counter hne c hc hread]
      exact ih (Fin.tail choices) _ (prepared_writeGuess witness counter _ c hc)
        (counterRemaining_writeGuess witness counter hne _ c T hcounter)

/-- An exhausted counter uses false to continue and true to halt rejecting. -/
theorem trace_one_enter_of_counter_blank (N : NTM n) (witness counter : Fin n)
    (c : Cfg n N.Q) (hc : Prepared c) (hcounter : (c.work counter).read = .blank)
    (b : Bool) :
    (machine N witness counter).trace 1 (fun _ => b) (enter N witness counter c) =
      embed N witness counter { c with state := if b then N.qhalt else N.qstart } := by
  have hw (j : Fin n) : (c.work j).read ≠ .start :=
    (hc.work_invariant j).read_ne_start (hc.work_positive j)
  simp only [NTM.trace, machine, enter, delta, reduceCtorEq, ite_false, hcounter,
    embed]
  apply Cfg.ext
  · rfl
  · simp [stayUnlessStart, hc.input_nonstart, Tape.move]
  · funext j; exact copy_stay (c.work j) (hw j)
  · exact copy_stay c.output hc.output_nonstart

/-- At the exhaustion boundary only one branch contributes continuation leaves. -/
theorem acceptLeafCountFrom_boundary (N : NTM n) (witness counter : Fin n)
    (U : ℕ) (c : Cfg n N.Q) (hc : Prepared c)
    (hcounter : CounterRemaining counter c 0) :
    (machine N witness counter).acceptLeafCountFrom (U + 1) (enter N witness counter c) =
      N.acceptLeafCountFrom U { c with state := N.qstart } := by
  have hnot : ¬ (machine N witness counter).halted (enter N witness counter c) := by
    simp [NTM.halted, Cfg.isHalted, machine, enter]
  have hread : (c.work counter).read = .blank := by
    simpa [Tape.read] using hcounter.2
  rw [NTM.acceptLeafCountFrom, ite_eq_right hnot,
    trace_one_enter_of_counter_blank N witness counter c hc hread false,
    trace_one_enter_of_counter_blank N witness counter c hc hread true]
  simp only [Bool.false_eq_true, ite_false, ite_true, acceptLeafCountFrom_embed]
  have hz : N.acceptLeafCountFrom U { c with state := N.qhalt } = 0 := by
    cases U <;> simp [NTM.acceptLeafCountFrom, NTM.halted, Cfg.isHalted, hc.output_zero]
  rw [hz, Nat.add_zero]

/-- No branch can halt while the prescribed genuine guesses are being made. -/
theorem noHaltBefore_enter (N : NTM n) (witness counter : Fin n) (hne : witness ≠ counter)
    (T : ℕ) (c : Cfg n N.Q) (hc : Prepared c) (hcounter : CounterRemaining counter c T) :
    NoHaltBefore (machine N witness counter) (T + 1) (enter N witness counter c) := by
  induction T generalizing c with
  | zero =>
      rw [noHaltBefore_succ_iff]
      exact ⟨by simp [NTM.halted, Cfg.isHalted, machine, enter],
        fun _ => noHaltBefore_zero _ _⟩
  | succ T ih =>
      rw [noHaltBefore_succ_iff]
      refine ⟨by simp [NTM.halted, Cfg.isHalted, machine, enter], fun b => ?_⟩
      have hread : (c.work counter).read = .one := by
        simpa [Tape.read] using hcounter.1 0 (by omega)
      rw [trace_one_enter_of_counter_one N witness counter hne c hc hread b]
      exact ih _ (prepared_writeGuess witness counter b c hc)
        (counterRemaining_writeGuess witness counter hne b c T hcounter)

/-- Each prescribed bit string contributes the continuation's leaf count exactly once. -/
theorem acceptLeafCountFrom_eq_sum (N : NTM n) (witness counter : Fin n)
    (hne : witness ≠ counter) (T U : ℕ) (c : Cfg n N.Q) (hc : Prepared c)
    (hcounter : CounterRemaining counter c T) :
    (machine N witness counter).acceptLeafCountFrom (T + 1 + U) (enter N witness counter c) =
      ∑ choices : Fin T → Bool,
        N.acceptLeafCountFrom U
          { afterChoices witness counter T choices c with state := N.qstart } := by
  have hno := (noHaltBefore_enter N witness counter hne T c hc hcounter).mono
    (Nat.le_succ T)
  rw [show T + 1 + U = T + (U + 1) by omega,
    acceptLeafCountFrom_prefix_expansion _ T (U + 1) _ hno]
  apply Finset.sum_congr rfl
  intro choices _
  rw [trace_enter N witness counter hne T choices c hc hcounter]
  exact acceptLeafCountFrom_boundary N witness counter U _
    (prepared_afterChoices witness counter T choices c hc)
    (counterRemaining_afterChoices witness counter hne T choices c hcounter)

/-- The witness head advances by exactly the number of generated bits. -/
theorem afterChoices_witness_head (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) :
    ((afterChoices witness counter T choices c).work witness).head =
      (c.work witness).head + T := by
  induction T generalizing c with
  | zero => simp [afterChoices]
  | succ T ih =>
      rw [afterChoices, ih]
      simp [writeGuess, Tape.writeAndMove, Tape.move, Tape.write_head,
        Nat.add_assoc, Nat.add_comm]

private theorem write_right_cells_of_ne (t : Tape) (symbol : Γw) (j : ℕ)
    (hj : j ≠ t.head) : (t.writeAndMove symbol .right).cells j = t.cells j := by
  simp only [Tape.writeAndMove, Tape.move, Tape.write]
  split <;> simp [Function.update_of_ne hj]

/-- Generating bits never changes an earlier witness cell. -/
theorem afterChoices_witness_before (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) (j : ℕ) (hj : j < (c.work witness).head) :
    ((afterChoices witness counter T choices c).work witness).cells j =
      (c.work witness).cells j := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      rw [afterChoices]
      have hhead : j < ((writeGuess witness counter (choices 0) c).work witness).head := by
        simp only [writeGuess, ite_true, Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      rw [ih (Fin.tail choices) _ hhead]
      simpa only [writeGuess, ite_true] using
        write_right_cells_of_ne (c.work witness) (Γw.ofBool (choices 0)) j (ne_of_lt hj)

/-- Cells beyond the generated witness remain unchanged, including its terminator. -/
theorem afterChoices_witness_after (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) (j : ℕ)
    (hj : (c.work witness).head + T ≤ j) :
    ((afterChoices witness counter T choices c).work witness).cells j =
      (c.work witness).cells j := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      rw [afterChoices]
      have hhead : ((writeGuess witness counter (choices 0) c).work witness).head + T ≤ j := by
        simp only [writeGuess, ite_true, Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      rw [ih (Fin.tail choices) _ hhead]
      simpa only [writeGuess, ite_true] using
        write_right_cells_of_ne (c.work witness) (Γw.ofBool (choices 0)) j (by omega)

private theorem write_right_cells_self (t : Tape) (b : Bool) (hhead : 0 < t.head) :
    (t.writeAndMove (Γw.ofBool b) .right).cells t.head = Γ.ofBool b := by
  cases b <;> simp [Tape.writeAndMove, Tape.move, Tape.write, Nat.ne_of_gt hhead,
    Γw.ofBool, Γ.ofBool]

/-- The generated witness contains the prescribed bits in their original order. -/
theorem afterChoices_witness_bit (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) (hhead : 0 < (c.work witness).head)
    (i : Fin T) :
    ((afterChoices witness counter T choices c).work witness).cells
      ((c.work witness).head + i.val) = Γ.ofBool (choices i) := by
  induction T generalizing c with
  | zero => exact Fin.elim0 i
  | succ T ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [afterChoices]
        have hbefore : (c.work witness).head <
            ((writeGuess witness counter (choices 0) c).work witness).head := by
          simp [writeGuess, Tape.writeAndMove, Tape.move, Tape.write_head]
        simp only [Fin.val_zero, Nat.add_zero]
        rw [afterChoices_witness_before witness counter T (Fin.tail choices)
          (writeGuess witness counter (choices 0) c) (c.work witness).head hbefore]
        simpa only [writeGuess, ite_true] using
          write_right_cells_self (c.work witness) (choices 0) hhead
      · rw [afterChoices]
        have hnext : 0 < ((writeGuess witness counter (choices 0) c).work witness).head := by
          simp [writeGuess, Tape.writeAndMove, Tape.move, Tape.write_head]
        have hbit := ih (Fin.tail choices) (writeGuess witness counter (choices 0) c) hnext i
        have heq : ((writeGuess witness counter (choices 0) c).work witness).head + i.val =
            (c.work witness).head + i.succ.val := by
          simp [writeGuess, Tape.writeAndMove, Tape.move, Tape.write_head,
            Nat.add_assoc, Nat.add_comm]
        rw [heq, show Fin.tail choices i = choices i.succ from rfl] at hbit
        exact hbit

/-- Different finite choice strings produce different witness tapes. -/
theorem afterChoices_injective (witness counter : Fin n) (T : ℕ) (c : Cfg n Q)
    (hhead : 0 < (c.work witness).head) :
    Function.Injective (fun choices : Fin T → Bool =>
      (afterChoices witness counter T choices c).work witness) := by
  intro choices₁ choices₂ heq
  funext i
  have hbit := congrArg (fun tape : Tape => tape.cells ((c.work witness).head + i.val)) heq
  rw [afterChoices_witness_bit witness counter T choices₁ c hhead i,
    afterChoices_witness_bit witness counter T choices₂ c hhead i] at hbit
  cases h₁ : choices₁ i <;> cases h₂ : choices₂ i <;> simp_all [Γ.ofBool]

/-- From witness head one and a blank terminator, the generated tape contains
exactly the chosen binary word in the standard upstream output convention. -/
theorem afterChoices_witness_hasOutput (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) (hhead : (c.work witness).head = 1)
    (hblank : (c.work witness).cells (T + 1) = .blank) :
    ((afterChoices witness counter T choices c).work witness).HasOutput (List.ofFn choices) := by
  constructor
  · intro i hi
    have hi' : i < T := by simpa using hi
    simpa [hhead, Nat.add_comm] using afterChoices_witness_bit witness counter T choices c
      (by omega) ⟨i, hi'⟩
  · simpa [hhead, Nat.add_comm] using
      (afterChoices_witness_after witness counter T choices c (T + 1) (by omega)).trans hblank

/-- Guessing preserves the source input tape. -/
theorem afterChoices_input (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) :
    (afterChoices witness counter T choices c).input = c.input := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih => exact ih (Fin.tail choices) _

/-- Guessing preserves the prepared output tape and its rejecting verdict. -/
theorem afterChoices_output (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) :
    (afterChoices witness counter T choices c).output = c.output := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih => exact ih (Fin.tail choices) _

/-- Other work tapes are untouched by the guessing prefix. -/
theorem afterChoices_other_work (witness counter j : Fin n)
    (hjw : j ≠ witness) (hjc : j ≠ counter) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n Q) :
    (afterChoices witness counter T choices c).work j = c.work j := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      rw [afterChoices, ih]
      simp [writeGuess, hjw, hjc]

/-- The counter contents are preserved; only its head moves. -/
theorem afterChoices_counter_cells (witness counter : Fin n) (hne : witness ≠ counter)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg n Q) :
    ((afterChoices witness counter T choices c).work counter).cells = (c.work counter).cells := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      rw [afterChoices, ih]
      simp [writeGuess, Ne.symm hne, Tape.move]

/-- The counter head advances by the same amount as the witness head. -/
theorem afterChoices_counter_head (witness counter : Fin n) (hne : witness ≠ counter)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg n Q) :
    ((afterChoices witness counter T choices c).work counter).head =
      (c.work counter).head + T := by
  induction T generalizing c with
  | zero => simp [afterChoices]
  | succ T ih =>
      rw [afterChoices, ih]
      simp [writeGuess, Ne.symm hne, Tape.move, Nat.add_assoc, Nat.add_comm]

/-- Every continuation trace is simulated without extra transitions. -/
theorem trace_embed (N : NTM n) (witness counter : Fin n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n N.Q) :
    (machine N witness counter).trace T choices (embed N witness counter c) =
      embed N witness counter (N.trace T choices c) := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      rw [trace_succ_eq, trace_one_embed, ih, trace_succ_eq N T]

/-- Exhausting the counter adds exactly one transition before the continuation. -/
theorem halted_trace_boundary (N : NTM n) (witness counter : Fin n) (U : ℕ)
    (c : Cfg n N.Q) (hc : Prepared c) (hcounter : CounterRemaining counter c 0)
    (hcontinue : ∀ choices : Fin U → Bool,
      N.halted (N.trace U choices { c with state := N.qstart })) :
    ∀ choices : Fin (U + 1) → Bool,
      (machine N witness counter).halted
        ((machine N witness counter).trace (U + 1) choices (enter N witness counter c)) := by
  intro choices
  have hread : (c.work counter).read = .blank := by
    simpa [Tape.read] using hcounter.2
  rw [trace_succ_eq, trace_one_enter_of_counter_blank N witness counter c hc hread]
  cases hb : choices 0 with
  | false =>
      simp only [Bool.false_eq_true, ite_false, trace_embed, halted_embed]
      exact hcontinue (Fin.tail choices)
  | true =>
      simp only [ite_true]
      have hh : (machine N witness counter).halted
          (embed N witness counter { c with state := N.qhalt }) := by
        simp [halted_embed, NTM.halted, Cfg.isHalted]
      rw [NTM.trace_halted _ _ _ hh]
      exact hh

/-- All-path continuation time `U` becomes total time `T+1+U` after guessing. -/
theorem halted_trace_enter (N : NTM n) (witness counter : Fin n)
    (hne : witness ≠ counter) (T U : ℕ) (c : Cfg n N.Q) (hc : Prepared c)
    (hcounter : CounterRemaining counter c T)
    (hcontinue : ∀ bits : Fin T → Bool, ∀ choices : Fin U → Bool,
      N.halted (N.trace U choices
        { afterChoices witness counter T bits c with state := N.qstart })) :
    ∀ choices : Fin (T + 1 + U) → Bool,
      (machine N witness counter).halted
        ((machine N witness counter).trace (T + 1 + U) choices (enter N witness counter c)) := by
  rw [show T + 1 + U = T + (U + 1) by omega]
  intro choices
  rw [NTM.trace_add, trace_enter N witness counter hne T _ c hc hcounter]
  exact halted_trace_boundary N witness counter U _
    (prepared_afterChoices witness counter T _ c hc)
    (counterRemaining_afterChoices witness counter hne T _ c hcounter)
    (hcontinue _) _

end Toda.Counting.GuessBits

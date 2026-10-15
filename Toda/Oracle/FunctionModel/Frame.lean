import Toda.Oracle.FunctionModel.Basic

/-! # Tape invariants and local resource bounds for full-answer machines -/

namespace Toda.Oracle

open Complexity

namespace FunctionCfg

variable {n : ℕ} {Q : Type}

/-- The left marker occurs exactly at cell zero on every tape. -/
structure StartInvariant (cfg : FunctionCfg n Q) : Prop where
  input : cfg.input.StartInvariant
  query : cfg.query.StartInvariant
  answer : cfg.answer.StartInvariant
  work : ∀ i, (cfg.work i).StartInvariant
  output : cfg.output.StartInvariant

@[simp] theorem init_startInvariant (qstart : Q) (input : List Bool) :
    (FunctionCfg.init (n := n) qstart input).StartInvariant :=
  ⟨Tape.StartInvariant.init_ofBool input, Tape.StartInvariant.init_nil,
    Tape.StartInvariant.init_nil, fun _ => Tape.StartInvariant.init_nil,
    Tape.StartInvariant.init_nil⟩

end FunctionCfg

namespace FunctionTM

variable {n : ℕ}

/-- Resetting the answer tape also reinstates its left-marker invariant. -/
theorem step_startInvariant {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg next : FunctionCfg n machine.Q}
    (hstep : machine.step oracle cfg = some next) (h : cfg.StartInvariant) :
    next.StartInvariant := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, hhalt] at hstep
  · cases hquery : machine.queryTransition cfg.state with
    | some state =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      exact ⟨h.input, h.query, Tape.StartInvariant.init_ofBool _, h.work, h.output⟩
    | none =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      exact ⟨h.input.move _, h.query.writeAndMove _ _, h.answer.writeAndMove _ _,
        fun i => (h.work i).writeAndMove _ _, h.output.writeAndMove _ _⟩

theorem reachesIn_startInvariant {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start final) (h : start.StartInvariant) :
    final.StartInvariant := by
  induction hreach with
  | zero => exact h
  | step hone _ ih => exact ih (step_startInvariant hone h)

/-- Each head moves at most one cell right per transition. Oracle answer
replacement resets its head to zero, so it also satisfies this upper bound. -/
theorem head_le_of_step {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg next : FunctionCfg n machine.Q}
    (hstep : machine.step oracle cfg = some next) :
    next.input.head ≤ cfg.input.head + 1 ∧
    next.query.head ≤ cfg.query.head + 1 ∧
    next.answer.head ≤ cfg.answer.head + 1 ∧
    (∀ i, (next.work i).head ≤ (cfg.work i).head + 1) ∧
    next.output.head ≤ cfg.output.head + 1 := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, hhalt] at hstep
  · cases hquery : machine.queryTransition cfg.state with
    | some state =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.zero_le _,
        fun _ => Nat.le_add_right _ _, Nat.le_add_right _ _⟩
    | none =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      exact ⟨Tape.head_move_le _ _, Tape.head_writeAndMove_le _ _ _,
        Tape.head_writeAndMove_le _ _ _, fun _ => Tape.head_writeAndMove_le _ _ _,
        Tape.head_writeAndMove_le _ _ _⟩

theorem head_le_start_add_of_reachesIn {machine : FunctionTM n}
    {oracle : FunctionOracle} {time : ℕ} {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start final) :
    final.input.head ≤ start.input.head + time ∧
    final.query.head ≤ start.query.head + time ∧
    final.answer.head ≤ start.answer.head + time ∧
    (∀ i, (final.work i).head ≤ (start.work i).head + time) ∧
    final.output.head ≤ start.output.head + time := by
  induction hreach with
  | zero => exact ⟨le_refl _, le_refl _, le_refl _, fun _ => le_refl _, le_refl _⟩
  | step hone _ ih =>
    obtain ⟨hi, hq, ha, hw, ho⟩ := head_le_of_step hone
    refine ⟨by omega, by omega, by omega, ?_, by omega⟩
    intro i
    have := hw i
    have := ih.2.2.2.1 i
    omega

theorem input_cells_of_step {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg next : FunctionCfg n machine.Q}
    (hstep : machine.step oracle cfg = some next) : next.input.cells = cfg.input.cells := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, hhalt] at hstep
  · cases hquery : machine.queryTransition cfg.state <;>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep <;>
      subst next <;> simp only [Tape.move_cells]

theorem input_cells_of_reachesIn {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start final) : final.input.cells = start.input.cells := by
  induction hreach with
  | zero => rfl
  | step hone _ ih => exact ih.trans (input_cells_of_step hone)

/-- Output writes remain local even when an oracle answer is supplied. -/
theorem output_cells_ne_of_step {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg next : FunctionCfg n machine.Q}
    (hstep : machine.step oracle cfg = some next) {index : ℕ}
    (hindex : index ≠ cfg.output.head) : next.output.cells index = cfg.output.cells index := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, hhalt] at hstep
  · cases hquery : machine.queryTransition cfg.state with
    | some state =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      rfl
    | none =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
      split
      · rfl
      · exact Function.update_of_ne hindex _ _

theorem reachesIn_output_cells_far {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start final) (index : ℕ)
    (hindex : start.output.head + time < index) :
    final.output.cells index = start.output.cells index := by
  induction hreach with
  | zero => rfl
  | step hone _ ih =>
    have hhead := (head_le_of_step hone).2.2.2.2
    exact (ih (by omega)).trans (output_cells_ne_of_step hone (by omega))

/-- Full oracle answers cannot appear on the ordinary output tape for free:
writing a binary output of length `L` requires at least `L` transitions. -/
theorem output_length_le_of_reachesIn {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {input bits : List Bool} {cfg : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time (machine.initCfg input) cfg)
    (houtput : cfg.output.HasOutput bits) : bits.length ≤ time := by
  by_contra hle
  have hlt : time < bits.length := by omega
  have hfar := reachesIn_output_cells_far hreach (time + 1) (by
    change 0 + time < time + 1
    omega)
  have hcell := houtput.1 time hlt
  rw [hfar] at hcell
  change Γ.blank = Γ.ofBool (bits[time]) at hcell
  generalize hb : bits[time] = bit at hcell
  cases bit <;> cases hcell

end FunctionTM

end Toda.Oracle

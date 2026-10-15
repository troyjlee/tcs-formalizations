import Toda.Oracle.FunctionModel.Defs
import Complexitylib.Models.TuringMachine.Tape.Encoding

/-! # Exact execution and query interfaces for full-answer oracle machines -/

namespace Toda.Oracle

open Complexity

namespace FunctionTM

variable {n : ℕ}

@[simp] theorem answerTape_head (value : ℕ) : (answerTape value).head = 0 := rfl

@[simp] theorem answerTape_hasOutput (value : ℕ) :
    (answerTape value).HasOutput value.bits := by
  constructor
  · intro i hi
    exact Tape.init_ofBool_cells_lt value.bits i hi
  · exact Tape.init_ofBool_cells_ge value.bits _ (le_refl _)

theorem step_eq_none_iff_halted {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg : FunctionCfg n machine.Q} :
    machine.step oracle cfg = none ↔ machine.halted cfg := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, halted, hhalt]
  · cases hquery : machine.queryTransition cfg.state <;>
      simp [step, halted, hhalt, hquery]

theorem reachesIn_functional {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {start first second : FunctionCfg n machine.Q}
    (hfirst : machine.reachesIn oracle time start first)
    (hsecond : machine.reachesIn oracle time start second) : first = second := by
  induction hfirst generalizing second with
  | zero => cases hsecond; rfl
  | step hone _ ih =>
    cases hsecond with
    | step htwo hrest =>
      have hmiddle := Option.some.inj (hone.symm.trans htwo)
      subst hmiddle
      exact ih hrest

theorem reachesIn_trans {machine : FunctionTM n} {oracle : FunctionOracle}
    {first second : ℕ} {start middle final : FunctionCfg n machine.Q}
    (hfirst : machine.reachesIn oracle first start middle)
    (hsecond : machine.reachesIn oracle second middle final) :
    machine.reachesIn oracle (first + second) start final := by
  induction hfirst with
  | zero => simpa using hsecond
  | step hone _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      reachesIn.step hone (ih hsecond)

/-- A full answer is supplied by one query step, without changing any other
head or tape. The continuation cannot depend on the oracle's value. -/
theorem step_query {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg : FunctionCfg n machine.Q} {next : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some next) :
    machine.step oracle cfg = some { cfg with
      state := next
      answer := answerTape (oracle cfg.query.oracleQuery) } := by
  simp [step, hhalt, hquery]

theorem reachesIn_one_query {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg : FunctionCfg n machine.Q} {next : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some next) :
    machine.reachesIn oracle 1 cfg { cfg with
      state := next
      answer := answerTape (oracle cfg.query.oracleQuery) } :=
  reachesIn.step (step_query hhalt hquery) reachesIn.zero

/-- Both ordinary and oracle steps move the query head at most one cell
right. Query evaluation itself leaves that head untouched. -/
theorem query_head_le_of_step {machine : FunctionTM n} {oracle : FunctionOracle}
    {cfg next : FunctionCfg n machine.Q}
    (hstep : machine.step oracle cfg = some next) :
    next.query.head ≤ cfg.query.head + 1 := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, hhalt] at hstep
  · cases hquery : machine.queryTransition cfg.state with
    | some q =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      exact Nat.le_add_right _ _
    | none =>
      simp only [step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst next
      exact Tape.head_writeAndMove_le _ _ _

theorem query_head_le_of_reachesIn {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start final) :
    final.query.head ≤ start.query.head + time := by
  induction hreach with
  | zero => exact Nat.le_refl _
  | step hone _ ih =>
    have hhead := query_head_le_of_step hone
    omega

/-- Starting with a blank query tape, a query cannot contain more bits than
there have been preceding machine steps. -/
theorem query_length_le_of_reachesIn {machine : FunctionTM n} {oracle : FunctionOracle}
    {time : ℕ} {input : List Bool} {cfg : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time (machine.initCfg input) cfg) :
    cfg.query.oracleQuery.length ≤ time := by
  have hhead := query_head_le_of_reachesIn hreach
  change cfg.query.head ≤ 0 + time at hhead
  rw [Tape.length_oracleQuery]
  omega

end FunctionTM

end Toda.Oracle

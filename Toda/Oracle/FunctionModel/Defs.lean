/-
Adapted to full binary answers from Complexitylib's Boolean oracle model.
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Complexitylib.Models.TuringMachine.Oracle
import Complexitylib.Asymptotics.PolyBound
import Complexitylib.Classes.SharpP
import Mathlib.Data.Nat.Bits

/-!
# Deterministic machines with full binary counting-oracle answers

The finite control has a designated continuation for each query state. A query
reads the same head-delimited query string as the upstream Boolean-oracle
model, replaces a dedicated answer tape with the canonical little-endian
binary encoding of the oracle's natural-number answer, and resets that tape's
head to its left marker. No ordinary tape is otherwise changed by a query.

All query preparation, head positioning, and answer processing use ordinary
local steps. In particular, there is no random access to answer bits, no
arbitrary function evaluation in a local transition, and no uncharged query
preprocessing. The unit-charge convention counts the oracle transition as one
step. `reachesChargedIn` also counts the number of supplied answer bits; its
polynomial equivalence for #P oracles is proved separately.
-/

namespace Toda.Oracle

open Complexity

/-- A total natural-valued function oracle, answered in canonical binary. -/
abbrev FunctionOracle := List Bool → ℕ

/-- Ordinary tapes together with dedicated query and answer tapes. -/
structure FunctionCfg (n : ℕ) (Q : Type) where
  state : Q
  input : Tape
  query : Tape
  answer : Tape
  work : Fin n → Tape
  output : Tape

namespace FunctionCfg

variable {n : ℕ} {Q : Type}

abbrev init (qstart : Q) (input : List Bool) : FunctionCfg n Q :=
  { state := qstart
    input := Tape.init (input.map Γ.ofBool)
    query := Tape.init []
    answer := Tape.init []
    work := fun _ => Tape.init []
    output := Tape.init [] }

/-- Forget both dedicated oracle tapes. -/
def erase (cfg : FunctionCfg n Q) : Cfg n Q :=
  { state := cfg.state, input := cfg.input, work := cfg.work, output := cfg.output }

end FunctionCfg

/-- A single ordinary finite-control transition. The input is read-only;
query, answer, work, and output tapes are read-write. -/
structure FunctionLocalTransition (n : ℕ) (Q : Type) where
  nextState : Q
  queryWrite : Γw
  answerWrite : Γw
  workWrites : Fin n → Γw
  outputWrite : Γw
  inputDir : Dir3
  queryDir : Dir3
  answerDir : Dir3
  workDirs : Fin n → Dir3
  outputDir : Dir3

/-- A deterministic multitape function-oracle machine with finite control. -/
structure FunctionTM (n : ℕ) where
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  qstart : Q
  qhalt : Q
  /-- A query state has one fixed successor, independent of the answer. -/
  queryTransition : Q → Option Q
  localTransition :
    Q → Γ → Γ → Γ → (Fin n → Γ) → Γ → FunctionLocalTransition n Q
  localTransition_right_of_start :
    ∀ (q : Q) (inputHead queryHead answerHead : Γ)
      (workHeads : Fin n → Γ) (outputHead : Γ),
      let transition :=
        localTransition q inputHead queryHead answerHead workHeads outputHead
      (inputHead = Γ.start → transition.inputDir = Dir3.right) ∧
      (queryHead = Γ.start → transition.queryDir = Dir3.right) ∧
      (answerHead = Γ.start → transition.answerDir = Dir3.right) ∧
      (∀ index, workHeads index = Γ.start → transition.workDirs index = Dir3.right) ∧
      (outputHead = Γ.start → transition.outputDir = Dir3.right)

attribute [instance] FunctionTM.decEq FunctionTM.finQ

namespace FunctionTM

variable {n : ℕ}

/-- Canonical full answer, with the head reset to cell zero. Zero has the
empty canonical binary encoding. -/
def answerTape (value : ℕ) : Tape := Tape.init (value.bits.map Γ.ofBool)

/-- A query replaces only the answer tape and enters its declared successor. -/
def step (machine : FunctionTM n) (oracle : FunctionOracle)
    (cfg : FunctionCfg n machine.Q) : Option (FunctionCfg n machine.Q) :=
  if cfg.state = machine.qhalt then none else
    match machine.queryTransition cfg.state with
    | some nextState =>
        some { cfg with
          state := nextState
          answer := answerTape (oracle cfg.query.oracleQuery) }
    | none =>
        let transition := machine.localTransition cfg.state cfg.input.read
          cfg.query.read cfg.answer.read (fun i => (cfg.work i).read) cfg.output.read
        some
          { state := transition.nextState
            input := cfg.input.move transition.inputDir
            query := cfg.query.writeAndMove transition.queryWrite transition.queryDir
            answer := cfg.answer.writeAndMove transition.answerWrite transition.answerDir
            work := fun i => (cfg.work i).writeAndMove
              (transition.workWrites i) (transition.workDirs i)
            output := cfg.output.writeAndMove transition.outputWrite transition.outputDir }

abbrev initCfg (machine : FunctionTM n) (input : List Bool) : FunctionCfg n machine.Q :=
  FunctionCfg.init machine.qstart input

abbrev halted (machine : FunctionTM n) (cfg : FunctionCfg n machine.Q) : Prop :=
  cfg.state = machine.qhalt

/-- Exact runtime with one unit for each local or oracle transition. -/
inductive reachesIn (machine : FunctionTM n) (oracle : FunctionOracle) :
    ℕ → FunctionCfg n machine.Q → FunctionCfg n machine.Q → Prop where
  | zero {cfg} : reachesIn machine oracle 0 cfg cfg
  | step {cfg middle result} {time : ℕ} : machine.step oracle cfg = some middle →
      reachesIn machine oracle time middle result →
      reachesIn machine oracle (time + 1) cfg result

/-- Alternative charge: one transition plus all supplied answer bits. -/
def stepCost (machine : FunctionTM n) (oracle : FunctionOracle)
    (cfg : FunctionCfg n machine.Q) : ℕ :=
  match machine.queryTransition cfg.state with
  | some _ => 1 + (oracle cfg.query.oracleQuery).bits.length
  | none => 1

/-- The same executions, with full answer length charged at every query. -/
inductive reachesChargedIn (machine : FunctionTM n) (oracle : FunctionOracle) :
    ℕ → FunctionCfg n machine.Q → FunctionCfg n machine.Q → Prop where
  | zero {cfg} : reachesChargedIn machine oracle 0 cfg cfg
  | step {cfg middle result} {cost : ℕ} : machine.step oracle cfg = some middle →
      reachesChargedIn machine oracle cost middle result →
      reachesChargedIn machine oracle (machine.stepCost oracle cfg + cost) cfg result

/-- Decide a language with an explicit length-dependent unit-charge bound. -/
def DecidesInTime (machine : FunctionTM n) (oracle : FunctionOracle)
    (language : Language) (timeBound : ℕ → ℕ) : Prop :=
  ∀ input, ∃ cfg time, time ≤ timeBound input.length ∧
    machine.reachesIn oracle time (machine.initCfg input) cfg ∧
    machine.halted cfg ∧
    (input ∈ language → cfg.output.cells 1 = Γ.one) ∧
    (input ∉ language → cfg.output.cells 1 = Γ.zero)

/-- The same decision criterion, including the full oracle answer length. -/
def DecidesChargedInTime (machine : FunctionTM n) (oracle : FunctionOracle)
    (language : Language) (timeBound : ℕ → ℕ) : Prop :=
  ∀ input, ∃ cfg cost, cost ≤ timeBound input.length ∧
    machine.reachesChargedIn oracle cost (machine.initCfg input) cfg ∧
    machine.halted cfg ∧
    (input ∈ language → cfg.output.cells 1 = Γ.one) ∧
    (input ∉ language → cfg.output.cells 1 = Γ.zero)

end FunctionTM

/-- Polynomial-time deterministic computation with full binary oracle answers. -/
def PWithFunctionOracle (oracle : FunctionOracle) : Set Language :=
  {language | ∃ (tapes : ℕ) (machine : FunctionTM tapes) (time : ℕ → ℕ),
    machine.DecidesInTime oracle language time ∧ PolyBound time}

/-- The full binary-answer, machine-based counting-oracle class P^#P. -/
def PSharpP : Set Language :=
  {language | ∃ oracle : FunctionOracle,
    oracle ∈ SharpP ∧ language ∈ PWithFunctionOracle oracle}

end Toda.Oracle

import Toda.Oracle.FunctionModel.Basic
import Toda.Counting.PolynomialClock

/-!
# Charging for full binary oracle answers

In a run of `T` steps the query head never exceeds `T`, hence every query has
length at most `T`. If answers to such queries have length at most `A`, the
same run has answer-charged cost at most `T * (1 + A)`. Canonical #P functions
have polynomial binary output length. Consequently the two cost conventions
define the same polynomial-time class, using exactly the same machines.
-/

namespace Toda.Oracle

open Complexity

namespace FunctionTM

variable {n : ℕ}

theorem one_le_stepCost (machine : FunctionTM n) (oracle : FunctionOracle)
    (cfg : FunctionCfg n machine.Q) : 1 ≤ machine.stepCost oracle cfg := by
  cases hquery : machine.queryTransition cfg.state <;> simp [stepCost, hquery]

/-- Forgetting answer-length charges can only decrease the runtime. -/
theorem reachesChargedIn_exists_reachesIn {machine : FunctionTM n}
    {oracle : FunctionOracle} {cost : ℕ} {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesChargedIn oracle cost start final) :
    ∃ time, time ≤ cost ∧ machine.reachesIn oracle time start final := by
  induction hreach with
  | zero => exact ⟨0, le_refl _, reachesIn.zero⟩
  | @step cfg middle final cost hone _ ih =>
    obtain ⟨time, htime, hrest⟩ := ih
    refine ⟨time + 1, ?_, reachesIn.step hone hrest⟩
    have hpositive := one_le_stepCost machine oracle cfg
    omega

/-- A uniform answer-length bound on all possible queries in a run bounds
its answer-charged cost. No bound on the numerical answer value is assumed. -/
theorem reachesIn_exists_reachesChargedIn {machine : FunctionTM n}
    {oracle : FunctionOracle} {time cap answerBound : ℕ}
    {start final : FunctionCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start final)
    (hcap : start.query.head + time ≤ cap)
    (hanswer : ∀ query : List Bool, query.length ≤ cap →
      (oracle query).bits.length ≤ answerBound) :
    ∃ cost, cost ≤ time * (1 + answerBound) ∧
      machine.reachesChargedIn oracle cost start final := by
  induction hreach with
  | zero => exact ⟨0, by simp, reachesChargedIn.zero⟩
  | @step cfg middle final time hone _ ih =>
    have hhead := query_head_le_of_step hone
    have hcap' : middle.query.head + time ≤ cap := by omega
    obtain ⟨cost, hcost, hrest⟩ := ih hcap'
    have hquery : cfg.query.oracleQuery.length ≤ cap := by
      rw [Tape.length_oracleQuery]
      omega
    have hstepcost : machine.stepCost oracle cfg ≤ 1 + answerBound := by
      cases hqueryState : machine.queryTransition cfg.state with
      | none => simp [stepCost, hqueryState]
      | some next =>
        simpa only [stepCost, hqueryState] using Nat.add_le_add_left (hanswer _ hquery) 1
    refine ⟨machine.stepCost oracle cfg + cost, ?_, reachesChargedIn.step hone hrest⟩
    calc
      machine.stepCost oracle cfg + cost ≤
          (1 + answerBound) + time * (1 + answerBound) := Nat.add_le_add hstepcost hcost
      _ = (time + 1) * (1 + answerBound) := by ring

/-- A monotone binary answer-length bound upgrades an ordinary clock to a
clock charging the entire returned answer at every query. -/
theorem DecidesInTime.charged {machine : FunctionTM n} {oracle : FunctionOracle}
    {language : Language} {timeBound answerBound : ℕ → ℕ}
    (hdecides : machine.DecidesInTime oracle language timeBound)
    (hmono : Monotone answerBound)
    (hanswer : ∀ query, (oracle query).bits.length ≤ answerBound query.length) :
    machine.DecidesChargedInTime oracle language
      (fun length => timeBound length * (1 + answerBound (timeBound length))) := by
  intro input
  obtain ⟨cfg, time, htime, hreach, hhalt, hyes, hno⟩ := hdecides input
  have hcap : (machine.initCfg input).query.head + time ≤ timeBound input.length := by
    simpa using htime
  obtain ⟨cost, hcost, hcharged⟩ := reachesIn_exists_reachesChargedIn hreach hcap
    (fun query hquery => (hanswer query).trans (hmono hquery))
  refine ⟨cfg, cost, ?_, hcharged, hhalt, hyes, hno⟩
  exact hcost.trans (Nat.mul_le_mul_right _ htime)

/-- Every charged decision run is also a unit-charge decision run. -/
theorem DecidesChargedInTime.unit {machine : FunctionTM n} {oracle : FunctionOracle}
    {language : Language} {timeBound : ℕ → ℕ}
    (hdecides : machine.DecidesChargedInTime oracle language timeBound) :
    machine.DecidesInTime oracle language timeBound := by
  intro input
  obtain ⟨cfg, cost, hcost, hreach, hhalt, hyes, hno⟩ := hdecides input
  obtain ⟨time, htime, hunit⟩ := reachesChargedIn_exists_reachesIn hreach
  exact ⟨cfg, time, htime.trans hcost, hunit, hhalt, hyes, hno⟩

end FunctionTM

/-- Polynomial time with full answers, charging all supplied answer bits. -/
def PWithFunctionOracleCharged (oracle : FunctionOracle) : Set Language :=
  {language | ∃ (tapes : ℕ) (machine : FunctionTM tapes) (time : ℕ → ℕ),
    machine.DecidesChargedInTime oracle language time ∧ PolyBound time}

/-- The unit-charge and full-answer-charge conventions coincide for #P
oracles. This is a comparison of the same machines, not an assumed oracle
model simulation. -/
theorem pWithFunctionOracle_eq_charged {oracle : FunctionOracle}
    (horacle : oracle ∈ SharpP) :
    PWithFunctionOracle oracle = PWithFunctionOracleCharged oracle := by
  ext language
  constructor
  · rintro ⟨tapes, machine, time, hdecide, hpoly⟩
    obtain ⟨A, B, hbound⟩ := Counting.sharpP_exists_value_size_bound horacle
    let answerBound := fun length => Counting.polynomialClock A B length + 1
    have hmono : Monotone answerBound := fun _ _ h =>
      Nat.add_le_add_right (Counting.polynomialClock_mono A B h) 1
    have hanswer : ∀ query, (oracle query).bits.length ≤ answerBound query.length := by
      intro query
      rw [Nat.size_eq_bits_len]
      exact (hbound query).2
    have hanswerPoly : PolyBound answerBound :=
      (Counting.polynomialClock_polyBound A B).add (PolyBound.const 1)
    exact ⟨tapes, machine, _, hdecide.charged hmono hanswer,
      hpoly.mul ((PolyBound.const 1).add (Counting.polyBound_comp hanswerPoly hpoly))⟩
  · rintro ⟨tapes, machine, time, hdecide, hpoly⟩
    exact ⟨tapes, machine, time, hdecide.unit, hpoly⟩

/-- The final counting-oracle class can equivalently require full binary
answer length to be charged. -/
theorem mem_pSharpP_iff_charged {language : Language} :
    language ∈ PSharpP ↔ ∃ oracle : FunctionOracle,
      oracle ∈ SharpP ∧ language ∈ PWithFunctionOracleCharged oracle := by
  constructor
  · rintro ⟨oracle, horacle, hlanguage⟩
    exact ⟨oracle, horacle, (pWithFunctionOracle_eq_charged horacle) ▸ hlanguage⟩
  · rintro ⟨oracle, horacle, hlanguage⟩
    exact ⟨oracle, horacle, (pWithFunctionOracle_eq_charged horacle).symm ▸ hlanguage⟩

end Toda.Oracle

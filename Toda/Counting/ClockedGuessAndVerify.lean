import Toda.Counting.PolynomialCounter
import Toda.Counting.GuessAndVerify
import Toda.Counting.DeterministicPrefix
import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Polynomially clocked guessing and verification from ordinary input

A deterministic setup computes a polynomial unary counter, after which the
machine guesses every string of that width once and runs a deterministic
work-tape verifier. The resulting witness count belongs to the unchanged
machine-based `SharpP` class.

The verifier runtime premise concerns the concrete generated configurations:
the input is restored to head 1, the witness and counter heads are after their
blocks, and the length and scratch registers retain their prepared values.
No conversion from a verifier on a separately encoded input pair is asserted.
-/

namespace Toda.Counting.ClockedGuessAndVerify

open Complexity Complexity.TM
open PolynomialCounter

variable {n : ℕ}

noncomputable section

/-- Four different work tapes reserve the input length, guessing counter,
Horner scratch space, and a blank witness destination. -/
structure Registers (n : ℕ) where
  lengthReg : Fin n
  counter : Fin n
  scratch : Fin n
  witness : Fin n
  length_counter : lengthReg ≠ counter
  length_scratch : lengthReg ≠ scratch
  counter_scratch : counter ≠ scratch
  witness_length : witness ≠ lengthReg
  witness_counter : witness ≠ counter
  witness_scratch : witness ≠ scratch

/-- The unique output accumulator containing the initial rejecting bit. -/
def rejectingTape : Tape :=
  ⟨2, fun j => if j = 0 then .start else if j = 1 then .zero else .blank⟩

theorem rejectingTape_outAcc : OutAcc [false] rejectingTape := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    rfl
  · intro j hj
    change 2 ≤ j at hj
    simp only [rejectingTape]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem rejectingTape_startInvariant : rejectingTape.StartInvariant :=
  ⟨rejectingTape_outAcc.2.1, rejectingTape_outAcc.parked.2⟩

/-- Canonical tapes immediately before guessing. Its state is the verifier's
initial state, so it can also describe the verification entry configuration. -/
def preparedCfg (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool) : Cfg n V.Q :=
  ⟨V.qstart, inputTape x,
    workTapes r.lengthReg r.counter r.scratch (clockPolynomial a b) x.length,
    rejectingTape⟩

theorem preparedCfg_post (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool) :
    EmitPred (inputTape x)
      (workTapes r.lengthReg r.counter r.scratch (clockPolynomial a b) x.length)
      [false] (preparedCfg V r a b x).input (preparedCfg V r a b x).work
      (preparedCfg V r a b x).output :=
  ⟨rfl, rfl, rejectingTape_outAcc⟩

theorem preparedCfg_prepared (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool) :
    GuessBits.Prepared (preparedCfg V r a b x) :=
  prepared_of_post _ _ _ _ _ _ (preparedCfg_post V r a b x)

theorem preparedCfg_counter (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool) :
    GuessBits.CounterRemaining r.counter (preparedCfg V r a b x)
      (polynomialClock a b x.length) := by
  simpa only [clockPolynomial_eval] using
    counterRemaining_of_post _ _ _ _ _ _ (preparedCfg_post V r a b x)

theorem preparedCfg_witness (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool) :
    (preparedCfg V r a b x).work r.witness = regTape 0 :=
  workTapes_frame _ _ _ _ _ _ r.witness_length r.witness_counter r.witness_scratch

/-- The exact deterministic verifier configuration after generating `choices`.
Both the witness head and counter head are at `polynomialClock a b |x| + 1`. -/
def verifierCfg (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool)
    (choices : Fin (polynomialClock a b x.length) → Bool) : Cfg n V.Q :=
  GuessAndVerify.verifierCfg V r.witness r.counter (polynomialClock a b x.length)
    choices (preparedCfg V r a b x)

/-- The positive-head and marker invariants survive the entire guessing
prefix and the verifier state reset. -/
theorem verifierCfg_prepared (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) :
    GuessBits.Prepared (verifierCfg V r a b x choices) := by
  have h := GuessBits.prepared_afterChoices r.witness r.counter
    (polynomialClock a b x.length) choices (preparedCfg V r a b x)
    (preparedCfg_prepared V r a b x)
  exact ⟨h.input_nonstart, h.work_invariant, h.work_positive,
    h.output_nonstart, h.output_zero⟩

/-- The generated work tape contains precisely the selected binary word. -/
theorem verifierCfg_witness_hasOutput (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) :
    ((verifierCfg V r a b x choices).work r.witness).HasOutput (List.ofFn choices) := by
  apply GuessBits.afterChoices_witness_hasOutput
  · rw [preparedCfg_witness]
    rfl
  · rw [preparedCfg_witness]
    change regCells 0 (polynomialClock a b x.length + 1) = .blank
    exact regCells_blank (by omega)

/-- Full tape contents, including the blank tail and cell-zero marker,
agree with a freshly initialized binary witness tape. -/
theorem verifierCfg_witness_cells (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) :
    ((verifierCfg V r a b x choices).work r.witness).cells =
      (Tape.init ((List.ofFn choices).map Γ.ofBool)).cells := by
  apply Tape.HasBinaryContent.cells_eq_init
  · refine ⟨(verifierCfg_witness_hasOutput V r a b x choices).1, ?_⟩
    intro i hi
    have hi' : polynomialClock a b x.length ≤ i := by simpa using hi
    change ((GuessBits.afterChoices _ _ _ _ _).work r.witness).cells (i + 1) = .blank
    rw [GuessBits.afterChoices_witness_after r.witness r.counter
      (polynomialClock a b x.length) choices (preparedCfg V r a b x) (i + 1)
      (by rw [preparedCfg_witness, regT_head]; omega)]
    rw [preparedCfg_witness]
    change regCells 0 (i + 1) = .blank
    exact regCells_blank (by omega)
  · exact ((verifierCfg_prepared V r a b x choices).work_invariant r.witness).1

theorem verifierCfg_witness_head (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) :
    ((verifierCfg V r a b x choices).work r.witness).head =
      polynomialClock a b x.length + 1 := by
  change ((GuessBits.afterChoices _ _ _ _ _).work r.witness).head = _
  rw [GuessBits.afterChoices_witness_head, preparedCfg_witness, regT_head, Nat.add_comm]

theorem verifierCfg_counter_head (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) :
    ((verifierCfg V r a b x choices).work r.counter).head =
      polynomialClock a b x.length + 1 := by
  change ((GuessBits.afterChoices _ _ _ _ _).work r.counter).head = _
  rw [GuessBits.afterChoices_counter_head _ _ r.witness_counter]
  change (workTapes _ _ _ _ _ r.counter).head + _ = _
  rw [workTapes_counter, regT_head, Nat.add_comm]

/-- Guessing leaves the input exactly restored and every other register in
the deterministic setup's proved frame. -/
theorem verifierCfg_input (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) :
    (verifierCfg V r a b x choices).input = inputTape x :=
  GuessBits.afterChoices_input _ _ _ _ _

theorem verifierCfg_work_frame (V : TM n) (r : Registers n) (a b : ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool)
    (i : Fin n) (hiw : i ≠ r.witness) (hic : i ≠ r.counter) :
    (verifierCfg V r a b x choices).work i =
      workTapes r.lengthReg r.counter r.scratch (clockPolynomial a b) x.length i :=
  GuessBits.afterChoices_other_work _ _ _ hiw hic _ _ _

/-- Acceptance by the actual deterministic verifier at its stated clock. -/
def AcceptsWitness (V : TM n) (r : Registers n) (a b : ℕ) (U : ℕ → ℕ)
    (x : List Bool) (choices : Fin (polynomialClock a b x.length) → Bool) : Prop :=
  GuessAndVerify.AcceptsWitness V r.witness r.counter (polynomialClock a b x.length)
    (U x.length) (preparedCfg V r a b x) choices

instance (V : TM n) (r : Registers n) (a b : ℕ) (U : ℕ → ℕ) (x : List Bool) :
    DecidablePred (AcceptsWitness V r a b U x) := by
  intro choices
  unfold AcceptsWitness
  infer_instance

/-- The number of accepted fixed-width witness strings. -/
def witnessCount (V : TM n) (r : Registers n) (a b : ℕ) (U : ℕ → ℕ)
    (x : List Bool) : ℕ :=
  (Finset.univ.filter (AcceptsWitness V r a b U x)).card

/-- The one substantive verifier premise: a single polynomial clock works on
every input and every generated witness, from the displayed work-tape frame. -/
def VerifierHalts (V : TM n) (r : Registers n) (a b : ℕ) (U : ℕ → ℕ) : Prop :=
  ∀ x, ∀ choices : Fin (polynomialClock a b x.length) → Bool,
    V.toNTM.halted (V.toNTM.trace (U x.length) (fun _ => false)
      (verifierCfg V r a b x choices))

/-- A bounded deterministic run to a halted configuration supplies the trace
clock required by the guessing compiler, without any padding assumption. -/
theorem verifierHalts_of_reachesIn (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ)
    (h : ∀ x, ∀ choices : Fin (polynomialClock a b x.length) → Bool,
      ∃ c t, t ≤ U x.length ∧ V.reachesIn t (verifierCfg V r a b x choices) c ∧
        V.halted c) : VerifierHalts V r a b U := by
  intro x choices
  obtain ⟨c, t, ht, hrun, hhalt⟩ := h x choices
  rw [V.toNTM_trace_of_reachesIn hrun hhalt ht]
  exact hhalt

/-- A reached halted verdict is exactly the acceptance predicate counted by
the compiler, even if the deterministic run finishes before its clock. -/
theorem acceptsWitness_iff_of_reachesIn (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (x : List Bool)
    (choices : Fin (polynomialClock a b x.length) → Bool) {c : Cfg n V.Q} {t : ℕ}
    (ht : t ≤ U x.length) (hrun : V.reachesIn t (verifierCfg V r a b x choices) c)
    (hhalt : V.halted c) :
    AcceptsWitness V r a b U x choices ↔ c.output.cells 1 = .one := by
  change (V.toNTM.halted (V.toNTM.trace (U x.length) (fun _ => false)
    (verifierCfg V r a b x choices)) ∧
    (V.toNTM.trace (U x.length) (fun _ => false)
      (verifierCfg V r a b x choices)).output.cells 1 = .one) ↔ _
  rw [V.toNTM_trace_of_reachesIn hrun hhalt ht]
  exact and_iff_right hhalt

/-- Enough time for guessing and all deterministic-verification cleanup paths. -/
def continuationTime (a b : ℕ) (U : ℕ → ℕ) (m : ℕ) : ℕ :=
  polynomialClock a b m + 1 + (2 * U m + 4)

theorem continuationTime_polyBound (a b : ℕ) {U : ℕ → ℕ} (hU : PolyBound U) :
    PolyBound (continuationTime a b U) :=
  ((polynomialClock_polyBound a b).add (PolyBound.const 1)).add
    (((PolyBound.const 2).mul hU).add (PolyBound.const 4))

/-- The complete actual NTM: polynomial counter setup, count-preserving
guessing, and deterministic verification with rejected duplicate choices. -/
noncomputable def machine (V : TM n) (r : Registers n) (a b : ℕ) : NTM n :=
  DeterministicPrefix.machine
    (PolynomialCounter.machine r.lengthReg r.counter r.scratch (clockPolynomial a b))
    (GuessAndVerify.machine V r.witness r.counter)

/-- Clock for the source sequential machine, before duplicate branches are
suppressed by the final wrapper. -/
def sourceTime (a b : ℕ) (U : ℕ → ℕ) (m : ℕ) : ℕ :=
  PolynomialCounter.timeBound (clockPolynomial a b) m + 1 + continuationTime a b U m

/-- A polynomial all-path clock for the named complete counting machine. -/
def timeBound (a b : ℕ) (U : ℕ → ℕ) (m : ℕ) : ℕ :=
  2 * sourceTime a b U m + 2

theorem timeBound_polyBound (a b : ℕ) {U : ℕ → ℕ} (hU : PolyBound U) :
    PolyBound (timeBound a b U) :=
  ((PolyBound.const 2).mul
    (((PolynomialCounter.timeBound_polyBound (clockPolynomial a b)).add
      (PolyBound.const 1)).add (continuationTime_polyBound a b hU))).add
    (PolyBound.const 2)

/-- All phase-boundary tape transitions are identities on the completed
setup, and its output accumulator is uniquely the canonical rejecting tape. -/
theorem continuation_eq_enter (V : TM n) (r : Registers n) (a b : ℕ) (x : List Bool)
    (d : Cfg n (PolynomialCounter.machine r.lengthReg r.counter r.scratch
      (clockPolynomial a b)).Q)
    (hd : EmitPred (inputTape x)
      (workTapes r.lengthReg r.counter r.scratch (clockPolynomial a b) x.length)
      [false] d.input d.work d.output) :
    DeterministicPrefix.continuation
      (PolynomialCounter.machine r.lengthReg r.counter r.scratch (clockPolynomial a b))
      (GuessAndVerify.machine V r.witness r.counter) d =
      GuessAndVerify.enter V r.witness r.counter (preparedCfg V r a b x) := by
  have hout : d.output = rejectingTape := hd.2.2.eq rejectingTape_outAcc
  apply Cfg.ext
  · rfl
  · change transitionInput d.input = inputTape x
    rw [hd.1]
    exact (parked_init_input x).transitionInput_eq_self
  · change (fun i => transitionTape (d.work i)) =
      workTapes r.lengthReg r.counter r.scratch (clockPolynomial a b) x.length
    rw [hd.2.1]
    funext i
    exact (workTapes_parked _ _ _ _ _ i).transitionTape_eq_self
  · change transitionTape d.output = rejectingTape
    rw [hout]
    exact rejectingTape_outAcc.parked.transitionTape_eq_self

theorem halted_trace_enter (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (hh : VerifierHalts V r a b U) (x : List Bool) :
    ∀ choices : Fin (continuationTime a b U x.length) → Bool,
      (GuessAndVerify.machine V r.witness r.counter).halted
        ((GuessAndVerify.machine V r.witness r.counter).trace
          (continuationTime a b U x.length) choices
          (GuessAndVerify.enter V r.witness r.counter (preparedCfg V r a b x))) := by
  simpa only [continuationTime, preparedCfg, rejectingTape, Nat.add_assoc] using
    GuessAndVerify.halted_trace_enter V r.witness r.counter r.witness_counter
      (polynomialClock a b x.length) (U x.length) (preparedCfg V r a b x)
      (preparedCfg_prepared V r a b x) (preparedCfg_counter V r a b x)
      rejectingTape_startInvariant (hh x)

theorem acceptLeafCountFrom_enter (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (hh : VerifierHalts V r a b U) (x : List Bool) :
    (GuessAndVerify.machine V r.witness r.counter).acceptLeafCountFrom
      (continuationTime a b U x.length)
      (GuessAndVerify.enter V r.witness r.counter (preparedCfg V r a b x)) =
      witnessCount V r a b U x := by
  change _ = (Finset.univ.filter (GuessAndVerify.AcceptsWitness V r.witness r.counter
    (polynomialClock a b x.length) (U x.length) (preparedCfg V r a b x))).card
  simpa only [continuationTime, preparedCfg, rejectingTape, Nat.add_assoc] using
    GuessAndVerify.acceptLeafCountFrom_totalClock_eq_card V r.witness r.counter
      r.witness_counter (polynomialClock a b x.length) (U x.length)
      (preparedCfg V r a b x) (preparedCfg_prepared V r a b x)
      (preparedCfg_counter V r a b x) rejectingTape_startInvariant (hh x)

private theorem source_allPathsHaltIn (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (hh : VerifierHalts V r a b U) :
    (DeterministicPrefix.source
      (PolynomialCounter.machine r.lengthReg r.counter r.scratch (clockPolynomial a b))
      (GuessAndVerify.machine V r.witness r.counter)).AllPathsHaltIn (sourceTime a b U) := by
  intro x choices
  let M := PolynomialCounter.machine r.lengthReg r.counter r.scratch (clockPolynomial a b)
  let N := GuessAndVerify.machine V r.witness r.counter
  obtain ⟨d, t, ht, hrun, hhalt, hpost⟩ := PolynomialCounter.machine_reachesIn
    r.lengthReg r.counter r.scratch r.length_counter r.length_scratch r.counter_scratch
    (clockPolynomial a b) x
  have hcont : ∀ choices : Fin (continuationTime a b U x.length) → Bool,
      N.halted (N.trace _ choices (DeterministicPrefix.continuation M N d)) := by
    rw [continuation_eq_enter V r a b x d hpost]
    exact halted_trace_enter V r a b U hh x
  have hsmall := DeterministicPrefix.source_halted_trace M N hrun hhalt
    (continuationTime a b U x.length) hcont
  have hle : t + 1 + continuationTime a b U x.length ≤ sourceTime a b U x.length := by
    unfold sourceTime
    omega
  let initialChoices : Fin (t + 1 + continuationTime a b U x.length) → Bool :=
    fun i => choices ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
  change (DeterministicPrefix.source M N).halted
    ((DeterministicPrefix.source M N).trace _ choices
      (DeterministicPrefix.first M N (M.initCfg x)))
  rw [(DeterministicPrefix.source M N).trace_mono hle
    (choices := initialChoices) (fun _ => rfl) (hsmall initialChoices)]
  exact hsmall initialChoices

/-- Every branch of the named machine halts by the displayed clock, including
all cleanup paths introduced during deterministic phases. -/
theorem allPathsHaltIn (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (hh : VerifierHalts V r a b U) :
    (machine V r a b).AllPathsHaltIn (timeBound a b U) :=
  SelectiveBranch.allPathsHaltIn _ _ _ (source_allPathsHaltIn V r a b U hh)

/-- Exact counting for the named machine at its all-path runtime clock. -/
theorem acceptLeafCount_eq (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (hh : VerifierHalts V r a b U) (x : List Bool) :
    (machine V r a b).acceptLeafCount x (timeBound a b U x.length) =
      witnessCount V r a b U x := by
  let M := PolynomialCounter.machine r.lengthReg r.counter r.scratch (clockPolynomial a b)
  let N := GuessAndVerify.machine V r.witness r.counter
  obtain ⟨d, t, ht, hrun, hhalt, hpost⟩ := PolynomialCounter.machine_reachesIn
    r.lengthReg r.counter r.scratch r.length_counter r.length_scratch r.counter_scratch
    (clockPolynomial a b) x
  have hcont : ∀ choices : Fin (continuationTime a b U x.length) → Bool,
      N.halted (N.trace _ choices (DeterministicPrefix.continuation M N d)) := by
    rw [continuation_eq_enter V r a b x d hpost]
    exact halted_trace_enter V r a b U hh x
  change (SelectiveBranch.machine (DeterministicPrefix.source M N)
    (DeterministicPrefix.branch M N)).acceptLeafCount _ _ = _
  rw [SelectiveBranch.acceptLeafCount_eq,
    SelectiveBranch.branchCount_eq_of_le_of_allChoicesHalt _ _
      (show sourceTime a b U x.length ≤ timeBound a b U x.length by
        unfold timeBound; omega) _ (source_allPathsHaltIn V r a b U hh x)]
  change SelectiveBranch.branchCount _ _
    (PolynomialCounter.timeBound (clockPolynomial a b) x.length + 1 +
      continuationTime a b U x.length) (DeterministicPrefix.first M N (M.initCfg x)) = _
  rw [DeterministicPrefix.branchCount_first_of_le M N hrun hhalt ht _ hcont,
    continuation_eq_enter V r a b x d hpost]
  exact acceptLeafCountFrom_enter V r a b U hh x

/-- Counting fixed-width witnesses accepted by this uniformly clocked actual
work-tape verifier belongs to canonical #P, from ordinary machine inputs. -/
theorem witnessCount_mem_sharpP (V : TM n) (r : Registers n) (a b : ℕ)
    (U : ℕ → ℕ) (hU : PolyBound U) (hh : VerifierHalts V r a b U) :
    witnessCount V r a b U ∈ SharpP := by
  apply DeterministicPrefix.mem_sharpP
    (PolynomialCounter.machine r.lengthReg r.counter r.scratch (clockPolynomial a b))
    (GuessAndVerify.machine V r.witness r.counter) _
    (PolynomialCounter.timeBound (clockPolynomial a b)) (continuationTime a b U)
    (PolynomialCounter.timeBound_polyBound _) (continuationTime_polyBound a b hU)
  intro x
  obtain ⟨d, t, ht, hrun, hhalt, hpost⟩ := PolynomialCounter.machine_reachesIn
    r.lengthReg r.counter r.scratch r.length_counter r.length_scratch r.counter_scratch
    (clockPolynomial a b) x
  refine ⟨t, d, ht, hrun, hhalt, ?_, ?_⟩
  · rw [continuation_eq_enter V r a b x d hpost]
    exact halted_trace_enter V r a b U hh x
  · rw [continuation_eq_enter V r a b x d hpost]
    exact (acceptLeafCountFrom_enter V r a b U hh x).symm

end

end Toda.Counting.ClockedGuessAndVerify

import Toda.Counting.PolynomialClock
import Toda.Counting.GuessBits
import Complexitylib.Models.TuringMachine.Registers.Horner
import Complexitylib.Models.TuringMachine.Registers.InputLen

/-!
# Preparing polynomial unary counters on an actual deterministic machine

Starting from the ordinary initial configuration, this machine loads the
input length, evaluates a fixed natural polynomial in unary, and writes a
rejecting output bit. The input is restored to cell 1 and every unused work
tape is a blank register. The exact tape frame supports a later guessing
prefix; this file does not yet compose that prefix with a verifier.

The implementation uses the pinned upstream unary register compiler. Its
Horner-prefix side condition is discharged here by a polynomial majorant,
giving a numerical polynomial runtime for every fixed polynomial, including
zero and constant polynomials.
-/

namespace Toda.Counting.PolynomialCounter

open Complexity Complexity.TM

variable {n : ℕ}

/-- The original Boolean input, with its head restored to cell 1. -/
def inputTape (x : List Bool) : Tape :=
  ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩

/-- The exact final work-tape frame. Only these three registers are used. -/
def workTapes (lengthReg counter scratch : Fin n) (p : Polynomial ℕ) (m : ℕ) :
    Fin n → Tape :=
  Function.update
    (Function.update
      (Function.update (fun _ => regTape 0) lengthReg (regTape m))
      scratch (regTape (p.eval m)))
    counter (regTape (p.eval m))

/-- A cap for the input register and every intermediate Horner value. -/
def registerBound (p : Polynomial ℕ) (m : ℕ) : ℕ :=
  m + ((polyCoeffs p).sum + 1) * (m + 1) ^ (p.natDegree + 1)

theorem length_le_registerBound (p : Polynomial ℕ) (m : ℕ) :
    m ≤ registerBound p m := Nat.le_add_right _ _

theorem hornerPrefix_le_registerBound (p : Polynomial ℕ) (m k : ℕ) :
    hornerFold m ((polyCoeffs p).take k) 0 ≤ registerBound p m := by
  have h := hornerFold_take_le m (polyCoeffs p) k
  rw [polyCoeffs_length] at h
  exact h.trans (Nat.le_add_left _ _)

theorem registerBound_polyBound (p : Polynomial ℕ) :
    PolyBound (registerBound p) := by
  exact PolyBound.id.add ((PolyBound.const ((polyCoeffs p).sum + 1)).mul
    ((PolyBound.id.add (PolyBound.const 1)).pow (p.natDegree + 1)))

/-- The upstream Horner evaluation budget with its cap discharged. -/
def evaluationTime (p : Polynomial ℕ) (m : ℕ) : ℕ :=
  opBudget (registerBound p m) + 1 +
    ((p.natDegree + 1) * (layerBudget (registerBound p m) + 1) + 1)

/-- Bump, input-length scan, Horner evaluation, output initialization, and
the three sequential-composition transitions. -/
def timeBound (p : Polynomial ℕ) (m : ℕ) : ℕ :=
  1 + 1 + ((2 * m + 4) + 1 + (evaluationTime p m + 1 + 1))

theorem evaluationTime_polyBound (p : Polynomial ℕ) :
    PolyBound (evaluationTime p) := by
  have hcap := (registerBound_polyBound p).add (PolyBound.const 2)
  have hop : PolyBound (fun m => opBudget (registerBound p m)) :=
    (PolyBound.const 32).mul ((hcap.mul hcap).mul hcap)
  have hlay : PolyBound (fun m => layerBudget (registerBound p m)) :=
    ((PolyBound.const 4).mul hop).add (PolyBound.const 3)
  exact (hop.add (PolyBound.const 1)).add
    (((PolyBound.const (p.natDegree + 1)).mul
      (hlay.add (PolyBound.const 1))).add (PolyBound.const 1))

theorem timeBound_polyBound (p : Polynomial ℕ) : PolyBound (timeBound p) := by
  exact (PolyBound.const (1 + 1)).add
    (((((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 4)).add
      (PolyBound.const 1)).add
        (((evaluationTime_polyBound p).add (PolyBound.const 1)).add
          (PolyBound.const 1)))

/-- An ordinary deterministic machine; the polynomial is fixed in its finite
control. Pairwise distinct register indices are needed for its specification. -/
def machine (lengthReg counter scratch : Fin n) (p : Polynomial ℕ) : TM n :=
  seqTM bumpTM (seqTM (inputLenRegTM lengthReg)
    (seqTM (polyEvalTM lengthReg counter scratch p) (emitBitsTM [false])))

private theorem parked_update (w : Fin n → Tape) (r : Fin n) (v : ℕ)
    (hw : ∀ i, Parked (w i)) :
    ∀ i, Parked ((Function.update w r (regTape v)) i) := by
  intro i
  by_cases h : i = r
  · subst i; simpa using parked_regTape v
  · simpa [Function.update_of_ne h] using hw i

theorem workTapes_parked (lengthReg counter scratch : Fin n)
    (p : Polynomial ℕ) (m : ℕ) (i : Fin n) :
    Parked (workTapes lengthReg counter scratch p m i) :=
  parked_update _ _ _
    (parked_update _ _ _
      (parked_update _ _ _ (fun _ => parked_regTape 0))) i

@[simp] theorem workTapes_counter (lengthReg counter scratch : Fin n)
    (p : Polynomial ℕ) (m : ℕ) :
    workTapes lengthReg counter scratch p m counter = regTape (p.eval m) := by
  simp [workTapes]

theorem workTapes_length (lengthReg counter scratch : Fin n)
    (h₁ : lengthReg ≠ counter) (h₂ : lengthReg ≠ scratch)
    (p : Polynomial ℕ) (m : ℕ) :
    workTapes lengthReg counter scratch p m lengthReg = regTape m := by
  simp [workTapes, h₁, h₂]

theorem workTapes_scratch (lengthReg counter scratch : Fin n)
    (h : scratch ≠ counter) (p : Polynomial ℕ) (m : ℕ) :
    workTapes lengthReg counter scratch p m scratch = regTape (p.eval m) := by
  simp [workTapes, h]

/-- In particular, a separate witness tape stays blank with its head at 1. -/
theorem workTapes_frame (lengthReg counter scratch : Fin n)
    (p : Polynomial ℕ) (m : ℕ) (i : Fin n)
    (h₁ : i ≠ lengthReg) (h₂ : i ≠ counter) (h₃ : i ≠ scratch) :
    workTapes lengthReg counter scratch p m i = regTape 0 := by
  simp [workTapes, h₁, h₂, h₃]

/-- Every final work tape is a canonical register, including unused tapes. -/
theorem workTapes_isReg (lengthReg counter scratch : Fin n)
    (p : Polynomial ℕ) (m : ℕ) (i : Fin n) :
    ∃ v, IsReg v (workTapes lengthReg counter scratch p m i) := by
  by_cases hcounter : i = counter
  · subst i
    exact ⟨p.eval m, by rw [workTapes_counter]; exact reg_regT _⟩
  by_cases hscratch : i = scratch
  · subst i
    exact ⟨p.eval m, by rw [workTapes_scratch _ _ _ hcounter]; exact reg_regT _⟩
  by_cases hlength : i = lengthReg
  · subst i
    exact ⟨m, by rw [workTapes_length _ _ _ hcounter hscratch]; exact reg_regT _⟩
  refine ⟨0, ?_⟩
  rw [workTapes_frame _ _ _ _ _ _ hlength hcounter hscratch]
  exact reg_regT _

/-- The completed setup supplies every preparation invariant required by the
actual count-preserving guessing machine. The statement is state-independent. -/
theorem prepared_of_post {Q : Type} (lengthReg counter scratch : Fin n)
    (p : Polynomial ℕ) (x : List Bool) (c : Cfg n Q)
    (h : EmitPred (inputTape x) (workTapes lengthReg counter scratch p x.length)
      [false] c.input c.work c.output) : GuessBits.Prepared c := by
  obtain ⟨hinp, hwork, hout⟩ := h
  refine ⟨?_, ?_, ?_, hout.parked.read_ne_start, ?_⟩
  · rw [hinp]
    exact (parked_init_input x).read_ne_start
  · intro i
    rw [hwork]
    obtain ⟨v, hv⟩ := workTapes_isReg lengthReg counter scratch p x.length i
    exact ⟨hv.cell0, fun _ hj => hv.cells_ne_start hj⟩
  · intro i
    rw [hwork]
    exact workTapes_parked lengthReg counter scratch p x.length i |>.1
  · exact hout.2.2.1 0 (by decide)

/-- The prepared counter contains exactly `p(|x|)` ones followed by a blank,
including when `p(|x|) = 0`. -/
theorem counterRemaining_of_post {Q : Type} (lengthReg counter scratch : Fin n)
    (p : Polynomial ℕ) (x : List Bool) (c : Cfg n Q)
    (h : EmitPred (inputTape x) (workTapes lengthReg counter scratch p x.length)
      [false] c.input c.work c.output) :
    GuessBits.CounterRemaining counter c (p.eval x.length) := by
  have hc : c.work counter = regTape (p.eval x.length) := by
    rw [h.2.1, workTapes_counter]
  unfold GuessBits.CounterRemaining
  rw [hc]
  simp only [regT_head, regT_cells]
  constructor
  · intro j hj
    exact regCells_one (by omega) (by omega)
  · exact regCells_blank (by omega)

/-- Exact input/work frame and output contents, from the standard initial
tapes, with an explicit polynomial runtime. -/
theorem machine_hoareTime (lengthReg counter scratch : Fin n)
    (h₁ : lengthReg ≠ counter) (h₂ : lengthReg ≠ scratch)
    (h₃ : counter ≠ scratch) (p : Polynomial ℕ) (x : List Bool) :
    (machine lengthReg counter scratch p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (inputTape x) (workTapes lengthReg counter scratch p x.length) [false])
      (timeBound p x.length) := by
  let w₀ : Fin n → Tape := fun _ => regTape 0
  let w₁ := Function.update w₀ lengthReg (regTape x.length)
  have hi : Parked (inputTape x) := parked_init_input x
  have hw₀ : ∀ i, Parked (w₀ i) := fun _ => parked_regTape 0
  have hw₁ : ∀ i, Parked (w₁ i) := parked_update _ _ _ hw₀
  have hbump := (bumpTM_hoareTime (n := n) x).strengthen_post
    (post' := EmitPred (inputTape x) w₀ [])
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      exact ⟨hinp, funext fun i => (hwork i).eq_regT, hout⟩)
  have hlength := inputLenRegTM_hoareTime lengthReg x w₀ []
    (fun i _ => hw₀ i) rfl
  have heval := polyEvalTM_hoareTime lengthReg counter scratch h₁ h₂ h₃
    p (registerBound p x.length) x.length 0 0
    (length_le_registerBound p x.length) (Nat.zero_le _) (Nat.zero_le _)
    (fun k _ => hornerPrefix_le_registerBound p x.length k)
    (inputTape x) w₁ [] hi hw₁
    (by simp [w₁]) (by simp [w₁, w₀, Ne.symm h₁])
    (by simp [w₁, w₀, Ne.symm h₂])
  have hemit := emitBitsTM_hoareTime [false] (inputTape x)
    (workTapes lengthReg counter scratch p x.length) [] hi
    (workTapes_parked lengthReg counter scratch p x.length)
  have hlast := seqTM_hoareTime _ _ heval
    (emitPred_transition hi
      (workTapes_parked lengthReg counter scratch p x.length) []) hemit
  have hrest := seqTM_hoareTime _ _ hlength
    (emitPred_transition hi hw₁ []) hlast
  exact seqTM_hoareTime _ _ hbump (emitPred_transition hi hw₀ []) hrest

/-- The specification applies to the standard initial configuration; no
prepared counter or tape precondition is assumed. -/
theorem machine_reachesIn (lengthReg counter scratch : Fin n)
    (h₁ : lengthReg ≠ counter) (h₂ : lengthReg ≠ scratch)
    (h₃ : counter ≠ scratch) (p : Polynomial ℕ) (x : List Bool) :
    ∃ c t, t ≤ timeBound p x.length ∧
      (machine lengthReg counter scratch p).reachesIn t
        ((machine lengthReg counter scratch p).initCfg x) c ∧
      (machine lengthReg counter scratch p).halted c ∧
      EmitPred (inputTape x) (workTapes lengthReg counter scratch p x.length)
        [false] c.input c.work c.output := by
  exact machine_hoareTime lengthReg counter scratch h₁ h₂ h₃ p x
    _ _ _ ⟨rfl, fun _ => rfl, rfl⟩

/-- The polynomial realizing the explicit clocks used in canonical #P. -/
noncomputable def clockPolynomial (coefficient exponent : ℕ) : Polynomial ℕ :=
  Polynomial.C coefficient * (Polynomial.X + 1) ^ exponent

@[simp] theorem clockPolynomial_eval (coefficient exponent m : ℕ) :
    (clockPolynomial coefficient exponent).eval m =
      polynomialClock coefficient exponent m := by
  simp [clockPolynomial, polynomialClock]

/-- Uniform in the input, this actual deterministic machine prepares the
explicit clock used by `sharpP_iff_exists_polynomialClock`. Its three register
indices and its two numerical clock parameters are fixed in finite control. -/
theorem clock_reachesIn (lengthReg counter scratch : Fin n)
    (h₁ : lengthReg ≠ counter) (h₂ : lengthReg ≠ scratch)
    (h₃ : counter ≠ scratch) (coefficient exponent : ℕ) (x : List Bool) :
    ∃ c t, t ≤ timeBound (clockPolynomial coefficient exponent) x.length ∧
      (machine lengthReg counter scratch (clockPolynomial coefficient exponent)).reachesIn t
        ((machine lengthReg counter scratch
          (clockPolynomial coefficient exponent)).initCfg x) c ∧
      (machine lengthReg counter scratch (clockPolynomial coefficient exponent)).halted c ∧
      EmitPred (inputTape x)
        (workTapes lengthReg counter scratch (clockPolynomial coefficient exponent) x.length)
        [false] c.input c.work c.output ∧
      GuessBits.Prepared c ∧
      GuessBits.CounterRemaining counter c (polynomialClock coefficient exponent x.length) := by
  obtain ⟨c, t, ht, hrun, hhalt, hpost⟩ := machine_reachesIn lengthReg counter scratch
    h₁ h₂ h₃ (clockPolynomial coefficient exponent) x
  refine ⟨c, t, ht, hrun, hhalt, hpost,
    prepared_of_post _ _ _ _ _ _ hpost, ?_⟩
  simpa only [clockPolynomial_eval] using counterRemaining_of_post _ _ _ _ _ _ hpost

end Toda.Counting.PolynomialCounter

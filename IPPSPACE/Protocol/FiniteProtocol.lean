/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.FiniteVerifier
import IPPSPACE.Protocol.Adaptive

/-!
# Adaptive soundness for coefficient-list messages

Every adaptive strategy sending arbitrary coefficient lists is translated to an
ideal polynomial strategy. Oversized lists translate to a rejected polynomial,
so the entire output distributions agree, including early rejection. Honest
polynomials have bounded coefficient encodings and retain perfect completeness.

The checks and transitions are executable; the PMF semantics still uses an ideal
uniform sampler. The remaining field encoding, random-bit implementation, and
machine-level simulation obligations are not discharged by this refinement.
-/

namespace IPPSPACE

universe u

/-- A prover may send any finite list, including an oversized one. It chooses
the list before seeing the fresh challenge, then selects a continuation. -/
def CoefficientStrategy (R : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => List R × (R → CoefficientStrategy R n)

noncomputable section

open MvPolynomial
open scoped Classical ENNReal

variable {R : Type*} [CommRing R]

/-- Translate an arbitrary list strategy, including invalid messages, to the
ideal verifier's strategy space. -/
def CoefficientStrategy.toIdeal (d : ℕ) : {n : ℕ} → CoefficientStrategy R n → ProverStrategy R n
  | 0, _ => PUnit.unit
  | _ + 1, strategy =>
      (checkedPolynomial d strategy.1, fun r => toIdeal d (strategy.2 r))

/-- Encode each polynomial by its first `d + 1` coefficients. This is faithful
only when its degree is at most `d`, as proved below for honest strategies. -/
def encodePolynomialStrategy (d : ℕ) : {n : ℕ} → ProverStrategy R n → CoefficientStrategy R n
  | 0, _ => PUnit.unit
  | _ + 1, strategy =>
      (polynomialCoefficients d strategy.1, fun r => encodePolynomialStrategy d (strategy.2 r))

theorem checkedPolynomial_polynomialCoefficients (d : ℕ) (p : Polynomial R)
    (hp : p.natDegree ≤ d) : checkedPolynomial d (polynomialCoefficients d p) = p := by
  simp only [checkedPolynomial, length_polynomialCoefficients, le_refl, ite_true]
  exact coefficientsPolynomial_polynomialCoefficients d p hp

/-- No information is lost when the honest strategy is encoded as lists. -/
theorem toIdeal_encodePolynomialStrategy_honest [Nontrivial R] (d : ℕ)
    (p : MvPolynomial ℕ R) (ops : List AlgebraicOperator) (c : EvaluationClaim R)
    (hdegree : DegreeBoundedChain ops p d) :
    CoefficientStrategy.toIdeal d (encodePolynomialStrategy d (honestStrategy p ops c)) =
      honestStrategy p ops c := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    have hreply : (univariateSlice c.point op.coordinate (applyOperators ops p)).natDegree ≤ d :=
      (natDegree_univariateSlice_le _ _ _).trans (hdegree.2.degreeOf_output _)
    let reply := univariateSlice c.point op.coordinate (applyOperators ops p)
    change (checkedPolynomial d (polynomialCoefficients d reply),
      fun r => CoefficientStrategy.toIdeal d (encodePolynomialStrategy d
        (honestStrategy p ops (op.advance c reply r)))) =
      (reply, fun r => honestStrategy p ops (op.advance c reply r))
    apply Prod.ext
    · exact checkedPolynomial_polynomialCoefficients d reply hreply
    · funext r
      exact ih _ hdegree.2

variable [DecidableEq R] [Fintype R]

/-- PMF semantics of the finite-state verifier with independent uniform
challenges; the actual checks and transitions are the executable procedures. -/
def runFiniteVerifier (d : ℕ) (terminal : (ℕ → R) → R × ℕ) :
    (ops : List AlgebraicOperator) → FiniteClaim R → CoefficientStrategy R ops.length → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = (terminal c.point).1))
  | op :: ops, c, strategy =>
      if (checkRoundWithCost op d c strategy.1).1 then
        (PMF.uniformOfFintype R).bind (fun r =>
          runFiniteVerifier d terminal ops (c.advanceWithCost op strategy.1 r).1 (strategy.2 r))
      else PMF.pure false

/-- Exact distributional refinement for every adaptive list strategy. -/
theorem runFiniteVerifier_eq_runVerifier [Nontrivial R] (d : ℕ)
    (terminal : (ℕ → R) → R × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim R) (strategy : CoefficientStrategy R ops.length) :
    runFiniteVerifier d terminal ops c strategy =
      runVerifier d (fun x => (terminal x).1) ops c.toClaim
        (CoefficientStrategy.toIdeal d strategy) := by
  induction ops generalizing c with
  | nil =>
    dsimp only [runFiniteVerifier, runVerifier, FiniteClaim.toClaim]
    congr 1
    exact decide_eq_decide.mpr Iff.rfl
  | cons op ops ih =>
    simp only [runFiniteVerifier, CoefficientStrategy.toIdeal, runVerifier]
    by_cases hcheck : (checkRoundWithCost op d c strategy.1).1 = true
    · have hlen := checkRoundWithCost_length op d c strategy.1 hcheck
      have hideal := (checkRoundWithCost_correct op d c strategy.1).mp hcheck
      rw [ite_eq_left hcheck, ite_eq_left hideal]
      congr 1
      funext r
      rw [ih, c.advanceWithCost_toClaim op strategy.1 r hlen]
    · have hideal := (checkRoundWithCost_correct op d c strategy.1).not.mp hcheck
      rw [ite_eq_right hcheck, ite_eq_right hideal]

/-- The prenex protocol with list messages and finite persistent state. -/
def PrenexQBF.runFiniteProtocol (φ : PrenexQBF)
    (strategy : CoefficientStrategy R φ.schedule.length) : PMF Bool :=
  runFiniteVerifier (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    φ.schedule finiteInitialClaim strategy

theorem PrenexQBF.runFiniteProtocol_eq_runProtocol [Nontrivial R] (φ : PrenexQBF)
    (strategy : CoefficientStrategy R φ.schedule.length) :
    φ.runFiniteProtocol strategy =
      φ.runProtocol (CoefficientStrategy.toIdeal (max 2 (nodeCount φ.matrix)) strategy) := by
  exact runFiniteVerifier_eq_runVerifier _ _ _ _ _

/-- Bounded coefficient messages preserve perfect completeness. -/
theorem PrenexQBF.runFiniteProtocol_honest [Nontrivial R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    φ.runFiniteProtocol (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
      (honestStrategy (arithmetize (R := R) φ.matrix) φ.schedule initialClaim)) = PMF.pure true := by
  rw [φ.runFiniteProtocol_eq_runProtocol,
    toIdeal_encodePolynomialStrategy_honest _ _ _ _ φ.degreeBoundedChain_schedule]
  exact φ.runProtocol_honest hclosed htrue

/-- The cubic soundness bound includes arbitrary adaptive list messages,
with no well-formedness assumption on the prover. -/
theorem PrenexQBF.runFiniteProtocol_soundness_le_cube [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : CoefficientStrategy R φ.schedule.length) :
    φ.runFiniteProtocol strategy true ≤
      (((nodeCount φ.toQBF + 1) ^ 3 : ℕ) : ℝ≥0∞) / Fintype.card R := by
  rw [φ.runFiniteProtocol_eq_runProtocol]
  exact φ.runProtocol_soundness_le_cube hclosed hfalse _

theorem PrenexQBF.runFiniteProtocol_soundness_le_third [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (hfield : 3 * (nodeCount φ.toQBF + 1) ^ 3 ≤ Fintype.card R)
    (strategy : CoefficientStrategy R φ.schedule.length) :
    φ.runFiniteProtocol strategy true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [φ.runFiniteProtocol_eq_runProtocol]
  exact φ.runProtocol_soundness_le_third hclosed hfalse hfield _

/-- The same error bound holds for any randomized mixture of list strategies. -/
theorem PrenexQBF.runFiniteProtocol_mixed_soundness_le_third [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (hfield : 3 * (nodeCount φ.toQBF + 1) ^ 3 ≤ Fintype.card R)
    (strategies : PMF (CoefficientStrategy R φ.schedule.length)) :
    (strategies.bind (fun strategy => φ.runFiniteProtocol strategy)) true ≤ (1 : ℝ≥0∞) / 3 :=
  pmf_bind_apply_le _ _ _ _ (fun strategy =>
    φ.runFiniteProtocol_soundness_le_third hclosed hfalse hfield strategy)

end

end IPPSPACE

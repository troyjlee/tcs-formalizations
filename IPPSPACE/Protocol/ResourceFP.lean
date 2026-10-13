/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.P.Unary
import IPPSPACE.Protocol.ReducedProtocol
import IPPSPACE.QBF.MachineReduction

/-!
# Polynomial-time computation of fixed resource budgets

Every fixed natural-coefficient polynomial can be evaluated at a unary-computable
argument in actual upstream `FP`. This certifies the existing protocol resource
calculations and polynomial space/width/output-size budgets.

The polynomial and machine parameters are fixed before the input is supplied.
Computing these budgets does not certify construction of the objects they bound:
QBF parsing, prenex conversion, machine-to-QBF construction, and the complete
interactive verifier still require their own runtime proofs.
-/

namespace IPPSPACE

open Complexity Polynomial

/-- Evaluation of an arbitrary fixed polynomial preserves actual unary
polynomial-time computability. Its coefficients and degree are fixed constants. -/
theorem polynomial_eval_unaryFn (P : Polynomial ℕ) {n : List Bool → ℕ}
    (hn : UnaryFn n) : UnaryFn fun z => P.eval (n z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    exact (hP.add hQ).of_eq (fun _ => (Polynomial.eval_add).symm)
  | monomial k a =>
    exact ((UnaryFn.const a).mul (hn.pow_const k)).of_eq
      (fun _ => (Polynomial.eval_monomial).symm)

theorem polynomial_eval_length_unaryFn (P : Polynomial ℕ) :
    UnaryFn fun z : List Bool => P.eval z.length :=
  polynomial_eval_unaryFn P unaryLength_mem_FP

/-- The same fixed-polynomial budget can be materialized as its binary numeral. -/
theorem polynomial_eval_bits_mem_FP (P : Polynomial ℕ) {n : List Bool → ℕ}
    (hn : UnaryFn n) : (fun z => (P.eval (n z)).bits) ∈ FP :=
  bits_mem_FP (polynomial_eval_unaryFn P hn)

theorem encodedRoundBudget_unaryFn : UnaryFn encodedRoundBudget :=
  (polynomial_eval_length_unaryFn roundResourcePolynomial).of_eq
    (fun input => (encodedRoundBudget_eq input).symm)

theorem coinResourceBudget_unaryFn :
    UnaryFn fun input : List Bool => coinResourcePolynomial.eval input.length :=
  polynomial_eval_length_unaryFn coinResourcePolynomial

theorem messageResourceBudget_unaryFn :
    UnaryFn fun input : List Bool => messageResourcePolynomial.eval input.length :=
  polynomial_eval_length_unaryFn messageResourcePolynomial

theorem parseResourceBudget_unaryFn :
    UnaryFn fun input : List Bool => parseResourcePolynomial.eval input.length :=
  polynomial_eval_length_unaryFn parseResourcePolynomial

theorem prenexLengthBudget_unaryFn {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun input => prenexLengthBudget (n input) :=
  (polynomial_eval_unaryFn prenexLengthPolynomial hn).of_eq
    (fun input => prenexLengthPolynomial_eval (n input))

theorem reducedRoundBudget_unaryFn : UnaryFn reducedRoundBudget :=
  (polynomial_eval_length_unaryFn reducedRoundPolynomial).of_eq
    (fun input => (reducedRoundBudget_eq input).symm)

theorem reducedCoinBudget_unaryFn :
    UnaryFn fun input : List Bool => reducedCoinPolynomial.eval input.length :=
  polynomial_eval_length_unaryFn reducedCoinPolynomial

theorem reducedMessageBudget_unaryFn :
    UnaryFn fun input : List Bool => reducedMessagePolynomial.eval input.length :=
  polynomial_eval_length_unaryFn reducedMessagePolynomial

/-- Exact configuration widths remain unary-computable after polynomial space
substitution. This concerns the numeric width, not configuration construction. -/
theorem configurationWidth_polynomialSpace_unaryFn (states tapes : ℕ)
    (space : Polynomial ℕ) {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun input => configurationWidth states tapes (n input) (space.eval (n input)) :=
  (polynomial_eval_unaryFn (configurationWidthPolynomial states tapes space) hn).of_eq
    (fun input => configurationWidthPolynomial_eval states tapes space (n input))

theorem machineTransitionNodeBound_polynomialSpace_unaryFn (states tapes : ℕ)
    (space : Polynomial ℕ) {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun input => machineTransitionNodeBound states tapes (n input) (space.eval (n input)) :=
  (polynomial_eval_unaryFn (machineTransitionNodePolynomial states tapes space) hn).of_eq
    (fun input => machineTransitionNodePolynomial_eval states tapes space (n input))

/-- Computing the reduction's numeric output budget is polynomial-time. This
does not assert polynomial-time construction of the encoded reduction itself. -/
theorem machineAcceptanceEncodingSize_polynomialSpace_unaryFn (states tapes : ℕ)
    (space : Polynomial ℕ) {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn fun input => machineAcceptanceEncodingSize states tapes (n input) (space.eval (n input)) :=
  (polynomial_eval_unaryFn (machineAcceptanceEncodingPolynomial states tapes space) hn).of_eq
    (fun input => machineAcceptanceEncodingPolynomial_eval states tapes space (n input))

end IPPSPACE

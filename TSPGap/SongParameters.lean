/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib

/-!
# Song's final parameter ledger

Exact rational parameters from Definitions 2–3 and Lemmas 24–26 of
Song, DOI 10.20944/preprints202609.0140.v1. These are separate from the
existing endpoint constants. Naming a candidate saving here does not prove
that a payment construction attains it.
-/

namespace TSPGap.Song

noncomputable section

def h : ℝ := 0.0002642163447
def r : ℝ := h / 4
def d₀ : ℝ := 1.2686955e-14
def p : ℝ := 1.9555663e-9
def K : ℝ := 13.46
def epsilon : ℝ := 4 * K * h
def theta : ℝ := 0.49309279
def xi : ℝ := 0.5013192700
def b₀ : ℝ := 0.00542322454
def sigma : ℝ := 0.00003258748749
def zeta : ℝ := 0.49307672
def t : ℝ := 0.57113594779
def epsilonM : ℝ := 0.000282
def epsilonB : ℝ := 0.00597342282
def epsilonF : ℝ := 0.1
def q₀ : ℝ := 0.56770582
def chi : ℝ := theta * r
def kGood : ℝ := 10.3659382
def H : ℝ := 9.06e-16
def layers : ℕ := 1000000

/-- Candidate general payment saving, not a payment existence theorem. -/
def a : ℝ := zeta * r * p * t
def deltaBot (d : ℝ) : ℝ := 1 / 4 - 5 / 2 * h - 2 * r - d
def J₁ (d : ℝ) : ℝ := (1 + d) * t * (2 + d - deltaBot d) + 2 * d
def J₂ (d : ℝ) : ℝ := (1 + d) * (t * (1 + d) + 0.31) + 2 * d
def J₃ (d : ℝ) : ℝ := (1 + d) * (t * d + 0.85) + 2 * d
/-- Candidate bottom saving; its probabilistic realization remains separate. -/
def aBot : ℝ := p * (1 - J₁ d₀)
def g₀ : ℝ := 1 - (kGood + 1) * h
def pi (u : ℝ) : ℝ := a * g₀ / (2 + u - a * (2 + u - g₀))
def repair (u : ℝ) : ℝ := 10 * (2 + u) / (1 - u)
def kappa (u : ℝ) : ℝ := pi u - repair u * u
/-- Target of the new route, not the repository's proved `kkoEps`. -/
def targetGap : ℝ := 2.05522e-30

end

end TSPGap.Song

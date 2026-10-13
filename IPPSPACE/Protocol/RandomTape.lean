/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MessageProtocol
import IPPSPACE.Protocol.CoinProbability
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Deterministic verification on a fixed random tape

A tape contains exactly one fixed-width bit block for every scheduled round.
The deterministic verifier reads only the current block after a successful
message check. Its outgoing message contains the current residue, never future
tape bits. Uniformly sampling the entire tape gives exactly the adaptive
fair-coin protocol's output distribution, including early rejection.
-/

namespace IPPSPACE

/-- Construct a word from a most-significant-bit-first finite Boolean function. -/
def bitsToWord : {w : ℕ} → (Fin w → Bool) → BitVec w
  | 0, _ => 0
  | _ + 1, bits => BitVec.cons (bits 0) (bitsToWord (Fin.tail bits))

/-- Reveal a word's bits in most-significant-first order. -/
def wordToBits : {w : ℕ} → BitVec w → (Fin w → Bool)
  | 0, _ => Fin.elim0
  | w + 1, word => Fin.cons word.msb (wordToBits (word.setWidth w))

@[simp] theorem wordToBits_bitsToWord {w : ℕ} (bits : Fin w → Bool) :
    wordToBits (bitsToWord bits) = bits := by
  induction w with
  | zero => funext i; exact Fin.elim0 i
  | succ w ih => simp [bitsToWord, wordToBits, ih]

@[simp] theorem bitsToWord_wordToBits {w : ℕ} (word : BitVec w) :
    bitsToWord (wordToBits word) = word := by
  induction w with
  | zero => simp [bitsToWord, BitVec.eq_nil word]
  | succ w ih => simp [bitsToWord, wordToBits, ih]

/-- Bit functions and fixed-width words are the same finite sample space. -/
def bitsWordEquiv (w : ℕ) : (Fin w → Bool) ≃ BitVec w where
  toFun := bitsToWord
  invFun := wordToBits
  left_inv := wordToBits_bitsToWord
  right_inv := bitsToWord_wordToBits

/-- Split a flat tape into consecutive words, preserving every bit. -/
def randomTapeEquiv (n w : ℕ) : (Fin (n * w) → Bool) ≃ (Fin n → BitVec w) where
  toFun bits i := bitsToWord (fun j => bits (finProdFinEquiv (i, j)))
  invFun words k := wordToBits (words (finProdFinEquiv.symm k).1)
    (finProdFinEquiv.symm k).2
  left_inv bits := by
    funext k
    simp only [wordToBits_bitsToWord]
    exact congrArg bits (finProdFinEquiv.apply_symm_apply k)
  right_inv words := by
    funext i
    simp only [Equiv.symm_apply_apply, bitsToWord_wordToBits]

/-- Recursion on the explicit round budget keeps the dependent strategy and tape
indices executable, including after Lean's list-length compiler optimization. -/
def verifyWordTapeCore (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ) :
    (n : ℕ) → List AlgebraicOperator → FiniteClaim (ZMod p) →
      MessageStrategy n → (Fin n → BitVec (residueWidth p)) → Bool
  | 0, [], c, _, _ => decide (c.value = (terminal c.point).1)
  | _ + 1, op :: ops, c, strategy, tape =>
      match parseMessage p (d + 1) strategy.1 with
      | none => false
      | some as =>
        if (checkRoundWithCost op d c as).1 then
          let r := sampleResidue p (tape 0)
          verifyWordTapeCore p d terminal _ ops (c.advanceWithCost op as r).1
            (strategy.2 (encodeMessage [r])) (Fin.tail tape)
        else false
  | _, _, _, _, _ => false

/-- A deterministic execution with one private word reserved per round. -/
def verifyWordTape (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (strategy : MessageStrategy ops.length) (tape : Fin ops.length → BitVec (residueWidth p)) : Bool :=
  verifyWordTapeCore p d terminal ops.length ops c strategy tape

/-- Executable verification from exactly `rounds * wordWidth` raw Boolean coins. -/
def verifyRandomTape (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (strategy : MessageStrategy ops.length)
    (tape : Fin (ops.length * residueWidth p) → Bool) : Bool :=
  verifyWordTape p d terminal ops c strategy (randomTapeEquiv ops.length (residueWidth p) tape)

/-- Reserve additional coins without reading them. -/
def verifyPaddedRandomTape (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (strategy : MessageStrategy ops.length) (padding : ℕ)
    (tape : Fin (ops.length * residueWidth p + padding) → Bool) : Bool :=
  verifyRandomTape p d terminal ops c strategy (fun i => tape (Fin.castAdd padding i))

/-- Padding is ignored pointwise, for every adversarial strategy and every tape. -/
theorem verifyPaddedRandomTape_append (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (strategy : MessageStrategy ops.length) (padding : ℕ)
    (tape : Fin (ops.length * residueWidth p) → Bool) (extra : Fin padding → Bool) :
    verifyPaddedRandomTape p d terminal ops c strategy padding (Fin.append tape extra) =
      verifyRandomTape p d terminal ops c strategy tape := by
  simp only [verifyPaddedRandomTape, Fin.append_left]

noncomputable section

open scoped Classical ENNReal

/-- Uniform distributions are preserved by a bijection of finite sample spaces. -/
theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  have heq (a : α) : b = e a ↔ e.symm b = a := by
    constructor
    · intro h; simp [h]
    · intro h; rw [← h]; simp
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, heq, Fintype.card_congr e]
  simp

/-- Independent uniform draws form a uniform pair. -/
theorem uniform_bind_pair {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun a =>
      (PMF.uniformOfFintype β).map (fun b => (a, b))) = PMF.uniformOfFintype (α × β) := by
  ext pair
  rcases pair with ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    Fintype.card_prod, ENNReal.mul_inv, ite_and]

/-- The first block and the remaining blocks determine a word tape uniquely. -/
def wordTapeConsEquiv (n w : ℕ) :
    BitVec w × (Fin n → BitVec w) ≃ (Fin (n + 1) → BitVec w) where
  toFun pair := Fin.cons pair.1 pair.2
  invFun tape := (tape 0, Fin.tail tape)
  left_inv pair := by simp
  right_inv tape := Fin.cons_self_tail tape

/-- A uniform word tape factors into its independent first word and suffix. -/
theorem uniform_wordTape_succ (n w : ℕ) :
    PMF.uniformOfFintype (Fin (n + 1) → BitVec w) =
      (fairWord w).bind (fun word =>
        (PMF.uniformOfFintype (Fin n → BitVec w)).map (Fin.cons word)) := by
  rw [fairWord_eq_uniform]
  have h := uniform_map_equiv (wordTapeConsEquiv n w)
  rw [← uniform_bind_pair, PMF.map_bind] at h
  simpa only [PMF.map_comp, wordTapeConsEquiv, Equiv.coe_fn_mk, Function.comp_def] using h.symm

/-- Sampling all private words in advance changes no adaptive output probabilities. -/
theorem verifyWordTape_uniform (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (strategy : MessageStrategy ops.length) :
    (PMF.uniformOfFintype (Fin ops.length → BitVec (residueWidth p))).map
      (verifyWordTape p d terminal ops c strategy) =
        runMessageVerifier p d terminal ops c strategy := by
  induction ops generalizing c with
  | nil => exact PMF.map_const _ _
  | cons op ops ih =>
    change (PMF.uniformOfFintype (Fin (ops.length + 1) → BitVec (residueWidth p))).map
      (verifyWordTape p d terminal (op :: ops) c strategy) = _
    rw [uniform_wordTape_succ, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, verifyWordTape, List.length_cons, verifyWordTapeCore, Fin.cons_zero, Fin.tail_cons,
      runMessageVerifier]
    cases hp : parseMessage p (d + 1) strategy.1 with
    | none =>
      simp only [PMF.bind_const]
      exact PMF.map_const _ _
    | some as =>
      by_cases hcheck : (checkRoundWithCost op d c as).1 = true
      · simp only [ite_eq_left hcheck]
        congr 1
        funext word
        exact ih _ _
      · simp only [ite_eq_right hcheck, PMF.bind_const]
        exact PMF.map_const _ _

/-- Uniformly sampling the flat Boolean tape exactly implements the fair-coin protocol. -/
theorem verifyRandomTape_uniform (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ)
    (ops : List AlgebraicOperator) (c : FiniteClaim (ZMod p))
    (strategy : MessageStrategy ops.length) :
    (PMF.uniformOfFintype (Fin (ops.length * residueWidth p) → Bool)).map
      (verifyRandomTape p d terminal ops c strategy) =
        runMessageVerifier p d terminal ops c strategy := by
  rw [← verifyWordTape_uniform p d terminal ops c strategy,
    ← uniform_map_equiv (randomTapeEquiv ops.length (residueWidth p)), PMF.map_comp]
  rfl


/-- Concatenation is a bijection between a tape pair and a longer tape. -/
def bitTapeAppendEquiv (n padding : ℕ) :
    (Fin n → Bool) × (Fin padding → Bool) ≃ (Fin (n + padding) → Bool) where
  toFun pair := Fin.append pair.1 pair.2
  invFun tape := (fun i => tape (Fin.castAdd padding i), fun i => tape (Fin.natAdd n i))
  left_inv pair := by simp
  right_inv tape := Fin.append_castAdd_natAdd

/-- Restriction of a uniform longer tape is uniform on the retained prefix. -/
theorem uniform_bitTape_prefix (n padding : ℕ) :
    (PMF.uniformOfFintype (Fin (n + padding) → Bool)).map
      (fun tape i => tape (Fin.castAdd padding i)) =
        PMF.uniformOfFintype (Fin n → Bool) := by
  rw [← uniform_map_equiv (bitTapeAppendEquiv n padding), ← uniform_bind_pair, PMF.map_comp]
  simp only [Function.comp_def, bitTapeAppendEquiv, Equiv.coe_fn_mk, Fin.append_left]
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  simp only [PMF.map, Function.comp_def, PMF.bind_const]
  exact PMF.bind_pure _

/-- Restrict any larger uniform tape to a bounded prefix, regardless of how
its larger length is presented. -/
theorem uniform_bitTape_restrict (n T : ℕ) (h : n ≤ T) :
    (PMF.uniformOfFintype (Fin T → Bool)).map
      (fun tape i => tape (Fin.castLE h i)) = PMF.uniformOfFintype (Fin n → Bool) := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le h
  exact uniform_bitTape_prefix n padding

/-- Extra independent coins leave the complete output distribution unchanged. -/
theorem verifyPaddedRandomTape_uniform (p d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) (strategy : MessageStrategy ops.length) (padding : ℕ) :
    (PMF.uniformOfFintype (Fin (ops.length * residueWidth p + padding) → Bool)).map
      (verifyPaddedRandomTape p d terminal ops c strategy padding) =
        runMessageVerifier p d terminal ops c strategy := by
  rw [← verifyRandomTape_uniform p d terminal ops c strategy,
    ← uniform_bitTape_prefix (ops.length * residueWidth p) padding, PMF.map_comp]
  rfl

end

/-- The prenex verifier as a deterministic function of a fixed Boolean tape. -/
def PrenexQBF.verifyRandomTape (φ : PrenexQBF) (strategy : MessageStrategy φ.schedule.length)
    (tape : Fin φ.randomBitBudget → Bool) : Bool :=
  IPPSPACE.verifyRandomTape (protocolPrime (nodeCount φ.toQBF)) (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    φ.schedule finiteInitialClaim strategy tape

/-- A prenex execution with an arbitrary number of reserved, unused suffix bits. -/
def PrenexQBF.verifyPaddedRandomTape (φ : PrenexQBF)
    (strategy : MessageStrategy φ.schedule.length) (padding : ℕ)
    (tape : Fin (φ.randomBitBudget + padding) → Bool) : Bool :=
  φ.verifyRandomTape strategy (fun i => tape (Fin.castAdd padding i))

noncomputable section

open MvPolynomial
open scoped Classical ENNReal

theorem PrenexQBF.verifyRandomTape_uniform (φ : PrenexQBF)
    (strategy : MessageStrategy φ.schedule.length) :
    (PMF.uniformOfFintype (Fin φ.randomBitBudget → Bool)).map (φ.verifyRandomTape strategy) =
      φ.runMessageProtocol strategy :=
  IPPSPACE.verifyRandomTape_uniform _ _ _ _ _ _

/-- Every individual tape accepts the canonical honest prover on a closed true input. -/
theorem PrenexQBF.verifyRandomTape_honest (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue)
    (tape : Fin φ.randomBitBudget → Bool) :
    φ.verifyRandomTape (encodeCoefficientStrategy (protocolPrime (nodeCount φ.toQBF))
      (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
        (honestStrategy (arithmetize (R := ProtocolField (nodeCount φ.toQBF)) φ.matrix)
          φ.schedule initialClaim))) tape = true := by
  let strategy := encodeCoefficientStrategy (protocolPrime (nodeCount φ.toQBF))
    (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
      (honestStrategy (arithmetize (R := ProtocolField (nodeCount φ.toQBF)) φ.matrix)
        φ.schedule initialClaim))
  have hs : φ.verifyRandomTape strategy tape ∈
      ((PMF.uniformOfFintype (Fin φ.randomBitBudget → Bool)).map
        (φ.verifyRandomTape strategy)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨tape, PMF.mem_support_uniformOfFintype tape, rfl⟩
  rw [φ.verifyRandomTape_uniform, φ.runMessageProtocol_honest hclosed htrue,
    PMF.support_pure, Set.mem_singleton_iff] at hs
  exact hs

theorem PrenexQBF.verifyRandomTape_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : MessageStrategy φ.schedule.length) :
    ((PMF.uniformOfFintype (Fin φ.randomBitBudget → Bool)).map
      (φ.verifyRandomTape strategy)) true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [φ.verifyRandomTape_uniform]
  exact φ.runMessageProtocol_soundness_le_third hclosed hfalse strategy

/-- Soundness in the rational counting form used by fixed-tape interfaces. -/
theorem PrenexQBF.verifyRandomTape_counting_soundness (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : MessageStrategy φ.schedule.length) :
    ((Finset.univ.filter fun tape => φ.verifyRandomTape strategy tape = true).card : ℚ) /
        2 ^ φ.randomBitBudget ≤ 1 / 3 :=
  (bitTape_acceptance_le_third_iff _ _).mp
    (φ.verifyRandomTape_soundness_le_third hclosed hfalse strategy)


/-- Padding transports the entire output distribution, not just an error bound. -/
theorem PrenexQBF.verifyPaddedRandomTape_uniform (φ : PrenexQBF)
    (strategy : MessageStrategy φ.schedule.length) (padding : ℕ) :
    (PMF.uniformOfFintype (Fin (φ.randomBitBudget + padding) → Bool)).map
      (φ.verifyPaddedRandomTape strategy padding) = φ.runMessageProtocol strategy :=
  IPPSPACE.verifyPaddedRandomTape_uniform _ _ _ _ _ _ _

theorem PrenexQBF.verifyPaddedRandomTape_honest (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) (padding : ℕ)
    (tape : Fin (φ.randomBitBudget + padding) → Bool) :
    φ.verifyPaddedRandomTape (encodeCoefficientStrategy (protocolPrime (nodeCount φ.toQBF))
      (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
        (honestStrategy (arithmetize (R := ProtocolField (nodeCount φ.toQBF)) φ.matrix)
          φ.schedule initialClaim))) padding tape = true :=
  φ.verifyRandomTape_honest hclosed htrue _

theorem PrenexQBF.verifyPaddedRandomTape_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : MessageStrategy φ.schedule.length) (padding : ℕ) :
    ((PMF.uniformOfFintype (Fin (φ.randomBitBudget + padding) → Bool)).map
      (φ.verifyPaddedRandomTape strategy padding)) true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [φ.verifyPaddedRandomTape_uniform]
  exact φ.runMessageProtocol_soundness_le_third hclosed hfalse strategy

/-- The rational soundness bound is unchanged after arbitrary independent padding. -/
theorem PrenexQBF.verifyPaddedRandomTape_counting_soundness (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : MessageStrategy φ.schedule.length) (padding : ℕ) :
    ((Finset.univ.filter fun tape => φ.verifyPaddedRandomTape strategy padding tape = true).card : ℚ) /
        2 ^ (φ.randomBitBudget + padding) ≤ 1 / 3 :=
  (bitTape_acceptance_le_third_iff _ _).mp
    (φ.verifyPaddedRandomTape_soundness_le_third hclosed hfalse strategy padding)

/-- Private randomized selection of a raw strategy preserves fixed-tape soundness. -/
theorem PrenexQBF.verifyRandomTape_mixed_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategies : PMF (MessageStrategy φ.schedule.length)) :
    (strategies.bind (fun strategy =>
      (PMF.uniformOfFintype (Fin φ.randomBitBudget → Bool)).map
        (φ.verifyRandomTape strategy))) true ≤ (1 : ℝ≥0∞) / 3 :=
  pmf_bind_apply_le _ _ _ _ (fun strategy =>
    φ.verifyRandomTape_soundness_le_third hclosed hfalse strategy)

end

end IPPSPACE

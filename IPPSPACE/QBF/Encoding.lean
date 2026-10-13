/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Syntax
import Mathlib.Data.Nat.Size

/-!
# A canonical binary encoding of upstream QBF syntax

Each constructor has a three-bit tag. Natural variable names use their canonical
binary digits, with a continuation marker before each digit and a terminating
zero. Their size is twice the ordinary binary size plus one, including name zero.
All parsers have explicit fuel and return the unused suffix; the outer decoder
requires full consumption. These representation theorems do not assert machine
running time or supply a prenex conversion.
-/

namespace IPPSPACE

open Complexity

/-- Prefix-free framing of a list of binary digits. -/
def frameNameBits : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frameNameBits bs

theorem length_frameNameBits (bs : List Bool) :
    (frameNameBits bs).length = 2 * bs.length + 1 := by
  induction bs <;> simp_all [frameNameBits, Nat.mul_add, Nat.add_assoc]

/-- Read a framed digit list, with a bound on the number of recursive calls. -/
def parseNameBits : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: b :: rest =>
      (parseNameBits fuel rest).map (fun r => (b :: r.1, r.2))
  | _ + 1, _ => none

theorem parseNameBits_frame (bs rest : List Bool) (fuel : ℕ)
    (hfuel : bs.length + 1 ≤ fuel) :
    parseNameBits fuel (frameNameBits bs ++ rest) = some (bs, rest) := by
  induction bs generalizing fuel with
  | nil => cases fuel <;> simp_all [frameNameBits, parseNameBits]
  | cons b bs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel => simp [frameNameBits, parseNameBits, ih fuel (by simpa using hfuel)]

theorem parseNameBits_sound (fuel : ℕ) (bits bs rest : List Bool)
    (h : parseNameBits fuel bits = some (bs, rest)) : frameNameBits bs ++ rest = bits := by
  induction fuel generalizing bits bs with
  | zero => simp [parseNameBits] at h
  | succ fuel ih =>
    cases bits with
    | nil => simp [parseNameBits] at h
    | cons b bits =>
      cases b with
      | false =>
        have heq : ([], bits) = (bs, rest) := by simpa [parseNameBits] using h
        cases heq
        rfl
      | true =>
        cases bits with
        | nil => simp [parseNameBits] at h
        | cons b bits =>
          cases hr : parseNameBits fuel bits with
          | none => simp [parseNameBits, hr] at h
          | some result =>
            rcases result with ⟨digits, suffix⟩
            have heq : (b :: digits, suffix) = (bs, rest) := by
              simpa [parseNameBits, hr] using h
            cases heq
            simpa [frameNameBits] using congrArg (fun xs => true :: b :: xs) (ih _ _ hr)

/-- Decode least-significant-bit-first digits as a natural number. -/
def nameBitsValue (bs : List Bool) : ℕ := bs.foldr Nat.bit 0

@[simp] theorem nameBitsValue_bits (n : ℕ) : nameBitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nameBitsValue]
  | bit b n h ih => simp [Nat.bits_append_bit n b h, nameBitsValue] at ih ⊢; rw [ih]

/-- Self-delimiting canonical binary name, without unary numeric expansion. -/
def encodeNatName (n : ℕ) : List Bool := frameNameBits n.bits

theorem length_encodeNatName (n : ℕ) :
    (encodeNatName n).length = 2 * n.size + 1 := by
  simp [encodeNatName, length_frameNameBits, Nat.size_eq_bits_len]

/-- Reject digit lists with redundant most-significant zeroes. -/
def parseNatName (fuel : ℕ) (bits : List Bool) : Option (ℕ × List Bool) := do
  let result ← parseNameBits fuel bits
  let n := nameBitsValue result.1
  if n.bits = result.1 then some (n, result.2) else none

theorem parseNatName_encode (n fuel : ℕ) (rest : List Bool)
    (hfuel : n.bits.length + 1 ≤ fuel) :
    parseNatName fuel (encodeNatName n ++ rest) = some (n, rest) := by
  simp [parseNatName, encodeNatName, parseNameBits_frame _ _ _ hfuel]

theorem parseNatName_sound (fuel : ℕ) (bits rest : List Bool) (n : ℕ)
    (h : parseNatName fuel bits = some (n, rest)) : encodeNatName n ++ rest = bits := by
  cases hr : parseNameBits fuel bits with
  | none => simp [parseNatName, hr] at h
  | some result =>
    rcases result with ⟨digits, suffix⟩
    by_cases hc : (nameBitsValue digits).bits = digits
    · have heq : (nameBitsValue digits, suffix) = (n, rest) := by
        simpa [parseNatName, hr, hc] using h
      cases heq
      simpa [encodeNatName, hc] using parseNameBits_sound fuel bits digits _ hr
    · simp [parseNatName, hr, hc] at h

/-- Preorder binary syntax with one of eight three-bit constructor tags. -/
def encodeQBF : QBF → List Bool
  | .var n => [false, false, false] ++ encodeNatName n
  | .tru => [false, false, true]
  | .fls => [false, true, false]
  | .neg φ => [false, true, true] ++ encodeQBF φ
  | .conj φ ψ => [true, false, false] ++ encodeQBF φ ++ encodeQBF ψ
  | .disj φ ψ => [true, false, true] ++ encodeQBF φ ++ encodeQBF ψ
  | .ex n φ => [true, true, false] ++ encodeNatName n ++ encodeQBF φ
  | .all n φ => [true, true, true] ++ encodeNatName n ++ encodeQBF φ

/-- Total contribution of binary variable names, including quantifier binders. -/
def qbfNameBitCost : QBF → ℕ
  | .var n => 2 * n.size + 1
  | .tru | .fls => 0
  | .neg φ => qbfNameBitCost φ
  | .conj φ ψ | .disj φ ψ => qbfNameBitCost φ + qbfNameBitCost ψ
  | .ex n φ | .all n φ => 2 * n.size + 1 + qbfNameBitCost φ

theorem length_encodeQBF (φ : QBF) :
    (encodeQBF φ).length = 3 * nodeCount φ + qbfNameBitCost φ := by
  induction φ <;> simp_all [encodeQBF, nodeCount, qbfNameBitCost, length_encodeNatName] <;> omega

theorem nodeCount_le_length_encodeQBF (φ : QBF) : nodeCount φ ≤ (encodeQBF φ).length := by
  rw [length_encodeQBF]
  omega

/-- Fuel-bounded prefix parser for the eight syntax constructors. -/
def parseQBF : ℕ → List Bool → Option (QBF × List Bool)
  | 0, _ => none
  | fuel + 1, false :: false :: false :: bs =>
      (parseNatName fuel bs).map (fun r => (.var r.1, r.2))
  | _ + 1, false :: false :: true :: bs => some (.tru, bs)
  | _ + 1, false :: true :: false :: bs => some (.fls, bs)
  | fuel + 1, false :: true :: true :: bs =>
      (parseQBF fuel bs).map (fun r => (.neg r.1, r.2))
  | fuel + 1, true :: false :: false :: bs => do
      let left ← parseQBF fuel bs
      let right ← parseQBF fuel left.2
      some (.conj left.1 right.1, right.2)
  | fuel + 1, true :: false :: true :: bs => do
      let left ← parseQBF fuel bs
      let right ← parseQBF fuel left.2
      some (.disj left.1 right.1, right.2)
  | fuel + 1, true :: true :: false :: bs => do
      let name ← parseNatName fuel bs
      let body ← parseQBF fuel name.2
      some (.ex name.1 body.1, body.2)
  | fuel + 1, true :: true :: true :: bs => do
      let name ← parseNatName fuel bs
      let body ← parseQBF fuel name.2
      some (.all name.1 body.1, body.2)
  | _ + 1, _ => none

theorem parseQBF_encode (φ : QBF) (fuel : ℕ) (rest : List Bool)
    (hfuel : (encodeQBF φ).length ≤ fuel) :
    parseQBF fuel (encodeQBF φ ++ rest) = some (φ, rest) := by
  induction φ generalizing fuel rest with
  | var n =>
    cases fuel with
    | zero => simp [encodeQBF] at hfuel
    | succ fuel =>
      have hn : n.bits.length + 1 ≤ fuel := by
        simp [encodeQBF, encodeNatName, length_frameNameBits] at hfuel
        omega
      simp [encodeQBF, parseQBF, parseNatName_encode n fuel rest hn]
  | tru => cases fuel <;> simp_all [encodeQBF, parseQBF]
  | fls => cases fuel <;> simp_all [encodeQBF, parseQBF]
  | neg φ ih =>
    cases fuel with
    | zero => simp [encodeQBF] at hfuel
    | succ fuel =>
      have hf : (encodeQBF φ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      simp [encodeQBF, parseQBF, ih fuel rest hf]
  | conj φ ψ ihφ ihψ =>
    cases fuel with
    | zero => simp [encodeQBF] at hfuel
    | succ fuel =>
      have hφ : (encodeQBF φ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      have hψ : (encodeQBF ψ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      simp [encodeQBF, List.append_assoc, parseQBF,
        ihφ fuel (encodeQBF ψ ++ rest) hφ, ihψ fuel rest hψ]
  | disj φ ψ ihφ ihψ =>
    cases fuel with
    | zero => simp [encodeQBF] at hfuel
    | succ fuel =>
      have hφ : (encodeQBF φ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      have hψ : (encodeQBF ψ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      simp [encodeQBF, List.append_assoc, parseQBF,
        ihφ fuel (encodeQBF ψ ++ rest) hφ, ihψ fuel rest hψ]
  | ex n φ ih =>
    cases fuel with
    | zero => simp [encodeQBF] at hfuel
    | succ fuel =>
      have hn : n.bits.length + 1 ≤ fuel := by
        simp [encodeQBF, encodeNatName, length_frameNameBits] at hfuel
        omega
      have hφ : (encodeQBF φ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      simp [encodeQBF, List.append_assoc, parseQBF,
        parseNatName_encode n fuel (encodeQBF φ ++ rest) hn, ih fuel rest hφ]
  | all n φ ih =>
    cases fuel with
    | zero => simp [encodeQBF] at hfuel
    | succ fuel =>
      have hn : n.bits.length + 1 ≤ fuel := by
        simp [encodeQBF, encodeNatName, length_frameNameBits] at hfuel
        omega
      have hφ : (encodeQBF φ).length ≤ fuel := by simp [encodeQBF] at hfuel; omega
      simp [encodeQBF, List.append_assoc, parseQBF,
        parseNatName_encode n fuel (encodeQBF φ ++ rest) hn, ih fuel rest hφ]

/-- Parse with input-length fuel and reject every unused trailing bit. -/
def decodeQBF (bits : List Bool) : Option QBF := do
  let result ← parseQBF bits.length bits
  if result.2 = [] then some result.1 else none

@[simp] theorem decodeQBF_encodeQBF (φ : QBF) : decodeQBF (encodeQBF φ) = some φ := by
  have h := parseQBF_encode φ (encodeQBF φ).length [] (Nat.le_refl _)
  simp only [List.append_nil] at h
  simp [decodeQBF, h]

theorem encodeQBF_injective : Function.Injective encodeQBF := by
  intro φ ψ h
  have := congrArg decodeQBF h
  simpa using this

/-- Every successful prefix parse consumes exactly a canonical formula encoding. -/
theorem parseQBF_sound (fuel : ℕ) (bits rest : List Bool) (φ : QBF)
    (h : parseQBF fuel bits = some (φ, rest)) : encodeQBF φ ++ rest = bits := by
  induction fuel generalizing bits rest φ with
  | zero => simp [parseQBF] at h
  | succ fuel ih =>
    cases bits with
    | nil => simp [parseQBF] at h
    | cons a bits =>
      cases bits with
      | nil => cases a <;> simp [parseQBF] at h
      | cons b bits =>
        cases bits with
        | nil => cases a <;> cases b <;> simp [parseQBF] at h
        | cons c bits =>
          cases a <;> cases b <;> cases c
          · cases hn : parseNatName fuel bits with
            | none => simp [parseQBF, hn] at h
            | some name =>
              rcases name with ⟨n, suffix⟩
              have heq : (QBF.var n, suffix) = (φ, rest) := by
                simpa [parseQBF, hn] using h
              cases heq
              simpa [encodeQBF] using congrArg (fun xs => false :: false :: false :: xs)
                (parseNatName_sound fuel bits _ n hn)
          · have heq : (QBF.tru, bits) = (φ, rest) := Option.some.inj h
            cases heq
            rfl
          · have heq : (QBF.fls, bits) = (φ, rest) := Option.some.inj h
            cases heq
            rfl
          · cases hb : parseQBF fuel bits with
            | none => simp [parseQBF, hb] at h
            | some body =>
              rcases body with ⟨ψ, suffix⟩
              have heq : (QBF.neg ψ, suffix) = (φ, rest) := by
                simpa [parseQBF, hb] using h
              cases heq
              simpa [encodeQBF] using congrArg (fun xs => false :: true :: true :: xs)
                (ih bits _ ψ hb)
          · cases hl : parseQBF fuel bits with
            | none => simp [parseQBF, hl] at h
            | some left =>
              rcases left with ⟨ψ, middle⟩
              cases hr : parseQBF fuel middle with
              | none => simp [parseQBF, hl, hr] at h
              | some right =>
                rcases right with ⟨χ, suffix⟩
                have heq : (QBF.conj ψ χ, suffix) = (φ, rest) := by
                  simpa [parseQBF, hl, hr] using h
                cases heq
                have hleft := ih bits middle ψ hl
                rw [← ih middle _ χ hr] at hleft
                simpa [encodeQBF, List.append_assoc] using
                  congrArg (fun xs => true :: false :: false :: xs) hleft
          · cases hl : parseQBF fuel bits with
            | none => simp [parseQBF, hl] at h
            | some left =>
              rcases left with ⟨ψ, middle⟩
              cases hr : parseQBF fuel middle with
              | none => simp [parseQBF, hl, hr] at h
              | some right =>
                rcases right with ⟨χ, suffix⟩
                have heq : (QBF.disj ψ χ, suffix) = (φ, rest) := by
                  simpa [parseQBF, hl, hr] using h
                cases heq
                have hleft := ih bits middle ψ hl
                rw [← ih middle _ χ hr] at hleft
                simpa [encodeQBF, List.append_assoc] using
                  congrArg (fun xs => true :: false :: true :: xs) hleft
          · cases hn : parseNatName fuel bits with
            | none => simp [parseQBF, hn] at h
            | some name =>
              rcases name with ⟨n, middle⟩
              cases hb : parseQBF fuel middle with
              | none => simp [parseQBF, hn, hb] at h
              | some body =>
                rcases body with ⟨ψ, suffix⟩
                have heq : (QBF.ex n ψ, suffix) = (φ, rest) := by
                  simpa [parseQBF, hn, hb] using h
                cases heq
                have hname := parseNatName_sound fuel bits middle n hn
                rw [← ih middle _ ψ hb] at hname
                simpa [encodeQBF, List.append_assoc] using
                  congrArg (fun xs => true :: true :: false :: xs) hname
          · cases hn : parseNatName fuel bits with
            | none => simp [parseQBF, hn] at h
            | some name =>
              rcases name with ⟨n, middle⟩
              cases hb : parseQBF fuel middle with
              | none => simp [parseQBF, hn, hb] at h
              | some body =>
                rcases body with ⟨ψ, suffix⟩
                have heq : (QBF.all n ψ, suffix) = (φ, rest) := by
                  simpa [parseQBF, hn, hb] using h
                cases heq
                have hname := parseNatName_sound fuel bits middle n hn
                rw [← ih middle _ ψ hb] at hname
                simpa [encodeQBF, List.append_assoc] using
                  congrArg (fun xs => true :: true :: true :: xs) hname

theorem decodeQBF_eq_some_iff (bits : List Bool) (φ : QBF) :
    decodeQBF bits = some φ ↔ encodeQBF φ = bits := by
  constructor
  · intro h
    cases hp : parseQBF bits.length bits with
    | none => simp [decodeQBF, hp] at h
    | some result =>
      rcases result with ⟨ψ, rest⟩
      by_cases hr : rest = []
      · subst rest
        have heq : ψ = φ := by simpa [decodeQBF, hp] using h
        subst ψ
        simpa using parseQBF_sound bits.length bits [] φ hp
      · simp [decodeQBF, hp, hr] at h
  · rintro rfl
    exact decodeQBF_encodeQBF φ

theorem decodeQBF_nodeCount_le (bits : List Bool) (φ : QBF)
    (h : decodeQBF bits = some φ) : nodeCount φ ≤ bits.length := by
  rw [← (decodeQBF_eq_some_iff bits φ).mp h]
  exact nodeCount_le_length_encodeQBF φ

end IPPSPACE

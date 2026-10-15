import Complexitylib.Classes.PH
import Complexitylib.Classes.P.StringAccess
import Mathlib.Data.List.OfFn

/-!
# Bounded-length existential witnesses as exact-width strings

Remove an initial run of true bits and its following delimiter. Every string
of length at most `m` has a representation of length `m+1`. This reduction
preserves existence, and makes no claim of preserving witness counts: the
all-true word also represents the empty witness. The decoder is actual FP.
-/

namespace Toda.Counting

open Complexity

/-- Drop a unary prefix and the first following bit, returning the payload. -/
def decodeBoundedWitness (bits : List Bool) : List Bool :=
  bits.drop (((bits.takeWhile id).length) + 1)

/-- A concrete padded representation of a bounded-length witness. -/
def encodeBoundedWitness (bound : ℕ) (witness : List Bool) : List Bool :=
  List.replicate (bound - witness.length) true ++ false :: witness

theorem decodeBoundedWitness_length (bits : List Bool) :
    (decodeBoundedWitness bits).length ≤ bits.length - 1 := by
  simp only [decodeBoundedWitness, List.length_drop]
  omega

private theorem takeWhile_unary_delimiter (padding : ℕ) (bits : List Bool) :
    ((List.replicate padding true ++ false :: bits).takeWhile id).length = padding := by
  induction padding with
  | zero => simp
  | succ padding _ih => simp [List.replicate_succ]

@[simp] theorem decodeBoundedWitness_encode (bound : ℕ) (witness : List Bool) :
    decodeBoundedWitness (encodeBoundedWitness bound witness) = witness := by
  simp only [decodeBoundedWitness, encodeBoundedWitness, takeWhile_unary_delimiter]
  rw [← List.drop_drop]
  simp

theorem encodeBoundedWitness_length (bound : ℕ) (witness : List Bool)
    (hbound : witness.length ≤ bound) :
    (encodeBoundedWitness bound witness).length = bound + 1 := by
  simp only [encodeBoundedWitness, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- This total decoder runs in polynomial time on all strings. -/
theorem decodeBoundedWitness_mem_FP : decodeBoundedWitness ∈ FP :=
  drop_mem_FP id_mem_FP
    ((UnaryFn.leadingTrueLength id_mem_FP).add (UnaryFn.const 1))

/-- Replace only the witness component of an ordinary paired input. -/
def decodeWitnessPair (input : List Bool) : List Bool :=
  pair (pairFst input) (decodeBoundedWitness (pairSnd input))

theorem decodeWitnessPair_mem_FP : decodeWitnessPair ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP decodeBoundedWitness_mem_FP)

@[simp] theorem decodeWitnessPair_pair (input witness : List Bool) :
    decodeWitnessPair (pair input witness) = pair input (decodeBoundedWitness witness) := by
  simp [decodeWitnessPair]

/-- Natural polynomial evaluation at a unary FP argument is unary FP. -/
theorem polynomial_eval_unary {argument : List Bool → ℕ} (hargument : UnaryFn argument)
    (polynomial : Polynomial ℕ) : UnaryFn fun input => polynomial.eval (argument input) := by
  induction polynomial using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n coefficient =>
      simpa only [Polynomial.eval_monomial] using
        (UnaryFn.const coefficient).mul (hargument.pow_const n)

/-- The canonical bounded existential is exactly an existential over strings
of one extra bit, followed by the actual FP decoder. -/
theorem polyExistsLang_iff_exactWidth (polynomial : Polynomial ℕ) (language : Language)
    (input : List Bool) :
    input ∈ polyExistsLang polynomial language ↔
      ∃ witness : Fin (polynomial.eval input.length + 1) → Bool,
        decodeWitnessPair (pair input (List.ofFn witness)) ∈ language := by
  constructor
  · rintro ⟨witness, hlength, hmem⟩
    let bits := encodeBoundedWitness (polynomial.eval input.length) witness
    have hbits : bits.length = polynomial.eval input.length + 1 :=
      encodeBoundedWitness_length _ _ hlength
    let encoded : Fin (polynomial.eval input.length + 1) → Bool :=
      fun i => bits[i.val]'(by omega)
    have hencoded : List.ofFn encoded = bits := by
      apply List.ext_getElem
      · simp [hbits]
      · intro i hi hj
        simp only [List.getElem_ofFn]
        rfl
    refine ⟨encoded, ?_⟩
    simpa only [hencoded, decodeWitnessPair_pair, bits, decodeBoundedWitness_encode] using hmem
  · rintro ⟨witness, hmem⟩
    refine ⟨decodeBoundedWitness (List.ofFn witness), ?_, ?_⟩
    · simpa using decodeBoundedWitness_length (List.ofFn witness)
    · simpa only [decodeWitnessPair_pair] using hmem

end Toda.Counting

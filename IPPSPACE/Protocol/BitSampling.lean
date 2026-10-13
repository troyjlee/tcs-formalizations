/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.PrimeField
import Mathlib.Probability.Distributions.Uniform

/-!
# Fixed-width binary challenges with controlled bias

Sample a uniform word of width `log2 p + 1` and reduce its value modulo `p`.
The sample space has size strictly greater than `p` and at most `2p`, so every
residue has at most two preimages and probability at most `2 / p`. Sampling
uses exactly one word and never retries or fails. It is not claimed to be
uniform over residues.
-/

namespace IPPSPACE

instance bitWordFintype (w : ℕ) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w)) BitVec.equivFin.toEquiv.symm

@[simp] theorem card_bitWord (w : ℕ) : Fintype.card (BitVec w) = 2 ^ w := by
  simpa using Fintype.card_congr (BitVec.equivFin (m := w)).toEquiv

/-- Turn a word into a field challenge; unlike message decoding, this accepts
every word and uses modular reduction for values at least `p`. -/
def sampleResidue (p : ℕ) (word : BitVec (residueWidth p)) : ZMod p := word.toNat

/-- Each residue has at most two word preimages. -/
theorem sampleResidue_fiber_card_le_two (p : ℕ) [NeZero p] (a : ZMod p) :
    Fintype.card {word : BitVec (residueWidth p) // sampleResidue p word = a} ≤ 2 := by
  let index : {word : BitVec (residueWidth p) // sampleResidue p word = a} → Fin 2 :=
    fun word => ⟨word.val.toNat / p, by
      apply (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne p))).mpr
      exact word.val.toFin.isLt.trans_le (two_pow_residueWidth_le p (NeZero.ne p))⟩
  have hinj : Function.Injective index := by
    intro x y h
    have hdiv : x.val.toNat / p = y.val.toNat / p := congrArg Fin.val h
    have hmod : x.val.toNat % p = y.val.toNat % p := by
      simpa only [sampleResidue, ZMod.val_natCast] using
        congrArg ZMod.val (x.property.trans y.property.symm)
    apply Subtype.ext
    apply BitVec.eq_of_toNat_eq
    have hx := Nat.mod_add_div x.val.toNat p
    have hy := Nat.mod_add_div y.val.toNat p
    rw [hmod, hdiv] at hx
    omega
  simpa using Fintype.card_le_of_injective index hinj

noncomputable section

open scoped Classical ENNReal

/-- Build a word from exactly `w` independent fair Boolean draws. -/
def fairWord : (w : ℕ) → PMF (BitVec w)
  | 0 => PMF.pure 0
  | w + 1 => (PMF.uniformOfFintype Bool).bind (fun b => (fairWord w).map (BitVec.cons b))

/-- Sequential fair-bit sampling is exactly uniform on fixed-width words. -/
theorem fairWord_eq_uniform (w : ℕ) : fairWord w = PMF.uniformOfFintype (BitVec w) := by
  induction w with
  | zero =>
    ext word
    have hword : word = 0 := BitVec.eq_of_toNat_eq (by have := word.isLt; simp at *; omega)
    subst word
    simp [fairWord, PMF.uniformOfFintype_apply]
  | succ w ih =>
    ext word
    have hcons (b : Bool) (rest : BitVec w) :
        word = BitVec.cons b rest ↔ word.msb = b ∧ word.setWidth w = rest := by
      constructor
      · intro h
        simp [h]
      · rintro ⟨hb, hr⟩
        rw [← hb, ← hr]
        exact (BitVec.cons_msb_setWidth word).symm
    have hmap (b : Bool) :
        ((PMF.uniformOfFintype (BitVec w)).map (BitVec.cons b)) word =
          if word.msb = b then ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
      simp only [PMF.map_apply, PMF.uniformOfFintype_apply, card_bitWord, hcons]
      by_cases hb : word.msb = b <;> simp [hb]
    simp only [fairWord, ih, PMF.bind_apply, hmap, PMF.uniformOfFintype_apply,
      Fintype.card_bool, card_bitWord]
    rw [ENNReal.tsum_mul_left]
    simp [pow_succ, ENNReal.mul_inv, mul_comm]

/-- Probability semantics of sampling a uniform binary word and reducing it. -/
def residueSampler (p : ℕ) : PMF (ZMod p) :=
  (PMF.uniformOfFintype (BitVec (residueWidth p))).map (sampleResidue p)

theorem residueSampler_apply (p : ℕ) (a : ZMod p) :
    residueSampler p a =
      (Fintype.card {word : BitVec (residueWidth p) // sampleResidue p word = a} : ℝ≥0∞) /
        (2 ^ residueWidth p : ℕ) := by
  rw [← PMF.toOuterMeasure_apply_singleton, residueSampler,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFintype_apply, card_bitWord]
  congr 2
  exact Fintype.card_congr (Equiv.refl _)

/-- The factor-two bound suffices for soundness with a doubled field threshold. -/
theorem residueSampler_apply_le (p : ℕ) [NeZero p] (a : ZMod p) :
    residueSampler p a ≤ (2 : ℝ≥0∞) / p := by
  rw [residueSampler_apply]
  calc
    _ ≤ (2 : ℝ≥0∞) / (2 ^ residueWidth p : ℕ) := by
      gcongr
      exact_mod_cast sampleResidue_fiber_card_le_two p a
    _ ≤ (2 : ℝ≥0∞) / p := by
      gcongr
      exact_mod_cast (lt_two_pow_residueWidth p).le

end

end IPPSPACE

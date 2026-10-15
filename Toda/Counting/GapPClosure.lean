import Toda.Counting.SharpPAdd
import Toda.Counting.SharpPMul
import Toda.Counting.Constants
import Toda.Counting.AmplificationFormula

/-!
# Algebraic closure of the machine-based counting classes

The witness constructions for #P addition and multiplication imply ring
closure for GapP, defined as a difference of two #P functions. Consequently,
every fixed counting formula preserves GapP. A fixed formula or iteration
count is a parameter of the constructed machine, not part of its input;
input-dependent formulas still require a uniform, costed construction.
-/

namespace Toda.Counting

open Complexity

/-- Natural-valued #P functions embed in GapP. -/
theorem sharpP_cast_mem_gapP {f : List Bool → ℕ} (hf : f ∈ SharpP) :
    (fun x => (f x : ℤ)) ∈ GapP := by
  exact ⟨f, fun _ => 0, hf, sharpP_const 0, fun _ => by simp⟩

/-- The difference of two #P functions is in GapP. -/
theorem sharpP_sub_mem_gapP {f g : List Bool → ℕ}
    (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    (fun x => (f x : ℤ) - (g x : ℤ)) ∈ GapP :=
  ⟨f, g, hf, hg, fun _ => rfl⟩

/-- Addition follows by adding the two positive and the two negative counts. -/
theorem gapP_add {f g : List Bool → ℤ} (hf : f ∈ GapP) (hg : g ∈ GapP) :
    (fun x => f x + g x) ∈ GapP := by
  obtain ⟨a, b, ha, hb, hf⟩ := hf
  obtain ⟨c, d, hc, hd, hg⟩ := hg
  refine ⟨fun x => a x + c x, fun x => b x + d x,
    sharpP_add ha hc, sharpP_add hb hd, fun x => ?_⟩
  dsimp only
  rw [hf x, hg x]
  push_cast
  ring

/-- Subtraction swaps the signs of the second function's counts. -/
theorem gapP_sub {f g : List Bool → ℤ} (hf : f ∈ GapP) (hg : g ∈ GapP) :
    (fun x => f x - g x) ∈ GapP := by
  simpa only [sub_eq_add_neg] using gapP_add hf (GapP.neg_mem hg)

/-- Multiply differences using `(a-b)(c-d) = (ac+bd)-(ad+bc)`. -/
theorem gapP_mul {f g : List Bool → ℤ} (hf : f ∈ GapP) (hg : g ∈ GapP) :
    (fun x => f x * g x) ∈ GapP := by
  obtain ⟨a, b, ha, hb, hf⟩ := hf
  obtain ⟨c, d, hc, hd, hg⟩ := hg
  refine ⟨fun x => a x * c x + b x * d x,
    fun x => a x * d x + b x * c x,
    sharpP_add (sharpP_mul ha hc) (sharpP_mul hb hd),
    sharpP_add (sharpP_mul ha hd) (sharpP_mul hb hc), fun x => ?_⟩
  dsimp only
  rw [hf x, hg x]
  push_cast
  ring

/-- Any fixed natural power preserves #P. -/
theorem sharpP_pow {f : List Bool → ℕ} (hf : f ∈ SharpP) (k : ℕ) :
    (fun x => f x ^ k) ∈ SharpP := by
  induction k with
  | zero => simpa using sharpP_const 1
  | succ k ih => simpa only [pow_succ] using sharpP_mul ih hf

/-- Any fixed natural power preserves GapP. -/
theorem gapP_pow {f : List Bool → ℤ} (hf : f ∈ GapP) (k : ℕ) :
    (fun x => f x ^ k) ∈ GapP := by
  induction k with
  | zero => simpa using gapP_const 1
  | succ k ih => simpa only [pow_succ] using gapP_mul ih hf

/-- Sums over a fixed finite index set preserve #P. -/
theorem sharpP_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → List Bool → ℕ} (hf : ∀ i ∈ s, f i ∈ SharpP) :
    (fun x => ∑ i ∈ s, f i x) ∈ SharpP := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sharpP_const 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      sharpP_add (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Products over a fixed finite index set preserve #P. -/
theorem sharpP_finset_prod {ι : Type*} (s : Finset ι)
    {f : ι → List Bool → ℕ} (hf : ∀ i ∈ s, f i ∈ SharpP) :
    (fun x => ∏ i ∈ s, f i x) ∈ SharpP := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sharpP_const 1
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      sharpP_mul (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Sums over a fixed finite index set preserve GapP. -/
theorem gapP_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → List Bool → ℤ} (hf : ∀ i ∈ s, f i ∈ GapP) :
    (fun x => ∑ i ∈ s, f i x) ∈ GapP := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gapP_const 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      gapP_add (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Products over a fixed finite index set preserve GapP. -/
theorem gapP_finset_prod {ι : Type*} (s : Finset ι)
    {f : ι → List Bool → ℤ} (hf : ∀ i ∈ s, f i ∈ GapP) :
    (fun x => ∏ i ∈ s, f i x) ∈ GapP := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gapP_const 1
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      gapP_mul (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Every fixed arithmetic formula preserves membership in canonical GapP. -/
theorem CountingFormula.eval_mem_gapP (e : CountingFormula)
    {f : List Bool → ℤ} (hf : f ∈ GapP) :
    (fun x => e.eval (f x)) ∈ GapP := by
  induction e with
  | input => exact hf
  | constant value => exact gapP_const value
  | sub a b ha hb => exact gapP_sub ha hb
  | mul a b ha hb => exact gapP_mul ha hb

/-- Any fixed number of amplification rounds preserves GapP. The round count
is independent of the input; this does not establish uniform amplification. -/
theorem gapP_amplifyIterate {f : List Bool → ℤ} (hf : f ∈ GapP) (k : ℕ) :
    (fun x => Arithmetic.amplifyIterate k (f x)) ∈ GapP := by
  simpa only [CountingFormula.eval_iteratedAmplify] using
    (CountingFormula.iteratedAmplify k).eval_mem_gapP hf

end Toda.Counting

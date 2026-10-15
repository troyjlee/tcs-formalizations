import Toda.Counting.GapPClosure
import Toda.Counting.DeterministicBranch
import Complexitylib.Classes.P.Verdict

/-!
# Polynomial-time conditionals in counting classes

A polynomial-time predicate selects between two counting functions. Its two
indicator functions have exactly zero or one accepting leaf, so multiplying
by the indicators and adding does not introduce any extra multiplicity.
Applying this to both constituents of a difference gives the GapP result.
-/

namespace Toda.Counting

open Complexity

/-- Polynomial-time case distinction preserves canonical #P. -/
theorem sharpP_ite {p : List Bool → Prop} [DecidablePred p]
    {f g : List Bool → ℕ} (hp : FPPred p) (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    (fun x => if p x then f x else g x) ∈ SharpP := by
  have hyes := DeterministicBranch.indicator_mem_sharpP {x | p x} hp.mem_P
  have hno := DeterministicBranch.indicator_mem_sharpP {x | ¬ p x} hp.not.mem_P
  have h := sharpP_add (sharpP_mul hyes hf) (sharpP_mul hno hg)
  convert h using 1
  funext x
  by_cases hx : p x <;> simp [DeterministicBranch.indicator, hx]

/-- Polynomial-time case distinction preserves canonical GapP, including
negative values of either branch. -/
theorem gapP_ite {p : List Bool → Prop} [DecidablePred p]
    {f g : List Bool → ℤ} (hp : FPPred p) (hf : f ∈ GapP) (hg : g ∈ GapP) :
    (fun x => if p x then f x else g x) ∈ GapP := by
  obtain ⟨a, b, ha, hb, hfab⟩ := hf
  obtain ⟨c, d, hc, hd, hgcd⟩ := hg
  refine ⟨(fun x => if p x then a x else c x),
    (fun x => if p x then b x else d x),
    sharpP_ite hp ha hc, sharpP_ite hp hb hd, fun x => ?_⟩
  by_cases hx : p x
  · simpa only [ite_eq_left hx] using hfab x
  · simpa only [ite_eq_right hx] using hgcd x

/-- The language-membership form of polynomial-time case distinction in #P. -/
theorem sharpP_ite_mem {L : Language} [DecidablePred (· ∈ L)]
    {f g : List Bool → ℕ} (hL : L ∈ Complexity.P) (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    (fun x => if x ∈ L then f x else g x) ∈ SharpP :=
  sharpP_ite (mem_P_iff_exists_decisionFn.mp hL) hf hg

/-- The language-membership form of polynomial-time case distinction in GapP. -/
theorem gapP_ite_mem {L : Language} [DecidablePred (· ∈ L)]
    {f g : List Bool → ℤ} (hL : L ∈ Complexity.P) (hf : f ∈ GapP) (hg : g ∈ GapP) :
    (fun x => if x ∈ L then f x else g x) ∈ GapP :=
  gapP_ite (mem_P_iff_exists_decisionFn.mp hL) hf hg

end Toda.Counting

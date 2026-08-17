/-
# Prefix-free codes and the converse of Shannon's noiseless coding theorem

Rao's "Coding for sunflowers" (Discrete Analysis 2020) reproves the ALWZ spread lemma with a
better constant, and its one piece of machinery is his Lemma 5:

> Let `E : [t] → {0,1}*` be any prefix-free encoding, and `ℓᵢ` the length of `E(i)`.
> Then `(1/t)·∑ᵢ ℓᵢ ≥ log t`.

This is the converse half of Shannon's noiseless coding theorem, under the uniform
distribution. The proof is two lines given **Kraft's inequality** `∑ᵢ 2^{-ℓᵢ} ≤ 1`:

  `log t − (1/t)∑ ℓᵢ = (1/t)∑ log(t·2^{-ℓᵢ}) ≤ log(∑ 2^{-ℓᵢ}) ≤ log 1 = 0`,

the first inequality by concavity of `log`.

## What is here

Mathlib has `InformationTheory.kraft_mcmillan_inequality` — Kraft's inequality for *uniquely
decodable* codes, which is the harder McMillan direction — but no notion of a prefix-free code
and no Shannon converse. This file supplies both:

* `PrefixFree` and `uniquelyDecodable_of_prefixFree` — prefix-free codes are uniquely
  decodable (the standard peel-off-the-first-codeword induction);
* `kraft_le_one` — Kraft's inequality for a prefix-free set of binary strings;
* `logb_card_le_avg_length` — **Rao's Lemma 5**.

The version actually used downstream is `card_le_of_encoding`: a prefix-free encoding whose
lengths are bounded on average bounds the *number of objects*, which is how the encoding
argument is applied — one exhibits an encoding and reads off a counting inequality.
-/
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Finset

namespace Sunflower

namespace Coding

/-- A set of strings is **prefix-free** if no member is a proper prefix of another. -/
def PrefixFree (S : Set (List Bool)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v

/-- **Prefix-free codes are uniquely decodable.** Peel off the first codeword: it is a prefix
of the common concatenation, so of the other first codeword or vice versa, hence equal to it by
prefix-freeness; then cancel and recurse. -/
theorem uniquelyDecodable_of_prefixFree {S : Set (List Bool)} (hpf : PrefixFree S)
    (hε : [] ∉ S) : InformationTheory.UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ _ h₂ hflat
      rcases L₂ with _ | ⟨w, L₂'⟩
      · rfl
      · exfalso
        have hw : w ∈ S := h₂ w (List.mem_cons_self ..)
        have hwnil : w = [] := by
          have h0 : (w :: L₂').flatten = [] := hflat.symm
          simp only [List.flatten_cons] at h0
          exact (List.append_eq_nil_iff.mp h0).1
        exact hε (hwnil ▸ hw)
  | cons w L₁' ih =>
      intro L₂ h₁ h₂ hflat
      have hw : w ∈ S := h₁ w (List.mem_cons_self ..)
      rcases L₂ with _ | ⟨u, L₂'⟩
      · exfalso
        have hwnil : w = [] := by
          have h0 : (w :: L₁').flatten = [] := hflat
          simp only [List.flatten_cons] at h0
          exact (List.append_eq_nil_iff.mp h0).1
        exact hε (hwnil ▸ hw)
      · have hu : u ∈ S := h₂ u (List.mem_cons_self ..)
        -- both `w` and `u` are prefixes of the common concatenation
        have hwpre : w <+: (w :: L₁').flatten := by
          rw [List.flatten_cons]; exact List.prefix_append _ _
        have hupre : u <+: (w :: L₁').flatten := by
          rw [hflat, List.flatten_cons]; exact List.prefix_append _ _
        have hwu : w = u := by
          rcases le_total w.length u.length with hle | hle
          · exact hpf w hw u hu (List.prefix_of_prefix_length_le hwpre hupre hle)
          · exact (hpf u hu w hw (List.prefix_of_prefix_length_le hupre hwpre hle)).symm
        subst hwu
        -- cancel the common head and recurse
        have htail : L₁'.flatten = L₂'.flatten := by
          have h := hflat
          rw [List.flatten_cons, List.flatten_cons] at h
          exact List.append_cancel_left h
        have := ih L₂' (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
          (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) htail
        rw [this]

/-- **Kraft's inequality** for a prefix-free set of binary strings: `∑ 2^{-|w|} ≤ 1`. -/
theorem kraft_le_one {S : Finset (List Bool)} (hpf : PrefixFree (S : Set (List Bool)))
    (hε : [] ∉ S) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  have h := InformationTheory.kraft_mcmillan_inequality (S := S)
    (uniquelyDecodable_of_prefixFree hpf (by simpa using hε))
  simpa using h

/-- `Real.logb 2` is concave on the positive reals. -/
private lemma concaveOn_logb : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (Real.logb 2) := by
  have hlog : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have h2 : (0 : ℝ) ≤ (Real.log 2)⁻¹ := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hsm := hlog.smul h2
  refine hsm.congr fun x _ => ?_
  show (Real.log 2)⁻¹ * Real.log x = Real.logb 2 x
  rw [Real.logb, div_eq_mul_inv, mul_comm]

/-- **Rao's Lemma 5, in Kraft-weight form.** Only the Kraft inequality is used, not the code
itself: any length function `ℓ` with `∑ 2^{-ℓ i} ≤ 1` has average at least `log₂|T|`.

This is the form to use when the "encoding" is virtual — each field of a record contributing
the reciprocal of its number of choices — which is Kraft mass bookkeeping without bit
strings. `logb_card_le_avg_length` is the special case of an actual prefix-free code. -/
theorem logb_card_le_avg_of_kraft {ι : Type*} {T : Finset ι} (hT : T.Nonempty) (ℓ : ι → ℕ)
    (hkraft : ∑ i ∈ T, (1 / 2 : ℝ) ^ (ℓ i) ≤ 1) :
    Real.logb 2 (T.card : ℝ) ≤ (∑ i ∈ T, (ℓ i : ℝ)) / (T.card : ℝ) := by
  classical
  set t : ℕ := T.card with ht
  have htpos : (0 : ℝ) < (t : ℝ) := by
    rw [ht]; exact_mod_cast Finset.card_pos.mpr hT
  -- Jensen for `logb 2` at the points `t·2^{-ℓᵢ}` with uniform weights
  have hmem : ∀ i ∈ T, (t : ℝ) * (1 / 2 : ℝ) ^ (ℓ i) ∈ Set.Ioi (0 : ℝ) := by
    intro i _
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ (ℓ i) := by positivity
    exact mul_pos htpos this
  have hw0 : ∀ i ∈ T, (0 : ℝ) ≤ 1 / (t : ℝ) := fun _ _ => by positivity
  have hw1 : ∑ _i ∈ T, (1 / (t : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← ht]
    field_simp
  have hjensen := concaveOn_logb.le_map_sum hw0 hw1 hmem
  -- the right-hand side is `logb 2 (∑ 2^{-ℓᵢ}) ≤ 0`
  have hrhs : ∑ i ∈ T, (1 / (t : ℝ)) • ((t : ℝ) * (1 / 2 : ℝ) ^ (ℓ i))
      = ∑ i ∈ T, (1 / 2 : ℝ) ^ (ℓ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    field_simp
  have hknn : (0 : ℝ) < ∑ i ∈ T, (1 / 2 : ℝ) ^ (ℓ i) := by
    refine Finset.sum_pos (fun i _ => by positivity) hT
  have hlogle : Real.logb 2 (∑ i ∈ T, (1 / 2 : ℝ) ^ (ℓ i)) ≤ 0 := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hknn hkraft
    simpa using this
  rw [hrhs] at hjensen
  -- the left-hand side is `logb 2 t − (1/t)∑ ℓᵢ`
  have hlhs : ∑ i ∈ T, (1 / (t : ℝ)) • Real.logb 2 ((t : ℝ) * (1 / 2 : ℝ) ^ (ℓ i))
      = Real.logb 2 (t : ℝ) - (∑ i ∈ T, (ℓ i : ℝ)) / (t : ℝ) := by
    have hterm : ∀ i ∈ T,
        (1 / (t : ℝ)) • Real.logb 2 ((t : ℝ) * (1 / 2 : ℝ) ^ (ℓ i))
          = (1 / (t : ℝ)) * (Real.logb 2 (t : ℝ) - (ℓ i : ℝ)) := by
      intro i _
      have hpow : Real.logb 2 ((1 / 2 : ℝ) ^ (ℓ i)) = -(ℓ i : ℝ) := by
        rw [Real.logb_pow]
        have : Real.logb 2 (1 / 2 : ℝ) = -1 := by
          rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
        rw [this]
        ring
      rw [smul_eq_mul, Real.logb_mul (ne_of_gt htpos) (by positivity), hpow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← ht]
    field_simp
  rw [hlhs] at hjensen
  linarith

/-- **Rao's Lemma 5** (converse of Shannon's noiseless coding theorem, uniform distribution).
A prefix-free encoding of `t` objects has average length at least `log₂ t`. -/
theorem logb_card_le_avg_length {ι : Type*} {T : Finset ι} (hT : T.Nonempty)
    (E : ι → List Bool)
    (hpf : ∀ i ∈ T, ∀ j ∈ T, E i <+: E j → i = j)
    (hne : ∀ i ∈ T, E i ≠ []) :
    Real.logb 2 (T.card : ℝ) ≤ (∑ i ∈ T, ((E i).length : ℝ)) / (T.card : ℝ) := by
  classical
  refine logb_card_le_avg_of_kraft hT (fun i => (E i).length) ?_
  have hinj : ∀ i ∈ T, ∀ j ∈ T, E i = E j → i = j := fun i hi j hj h =>
    hpf i hi j hj (by rw [h])
  have himg : ∑ w ∈ T.image E, (1 / 2 : ℝ) ^ w.length
      = ∑ i ∈ T, (1 / 2 : ℝ) ^ (E i).length :=
    Finset.sum_image fun i hi j hj h => hinj i hi j hj h
  rw [← himg]
  refine kraft_le_one ?_ ?_
  · rintro u hu v hv huv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
    obtain ⟨i, hi, rfl⟩ := hu
    obtain ⟨j, hj, rfl⟩ := hv
    rw [hpf i hi j hj huv]
  · intro hmem
    obtain ⟨i, hi, hEi⟩ := Finset.mem_image.mp hmem
    exact hne i hi hEi

/-- The form the encoding argument uses: if every object in `T` gets a prefix-free encoding of
length at most `ℓ`, then `|T| ≤ 2^ℓ`. -/
theorem card_le_of_encoding {ι : Type*} {T : Finset ι} (hT : T.Nonempty) (E : ι → List Bool)
    {ℓ : ℝ}
    (hpf : ∀ i ∈ T, ∀ j ∈ T, E i <+: E j → i = j)
    (hne : ∀ i ∈ T, E i ≠ [])
    (hlen : ∀ i ∈ T, ((E i).length : ℝ) ≤ ℓ) :
    Real.logb 2 (T.card : ℝ) ≤ ℓ := by
  · refine le_trans (logb_card_le_avg_length hT E hpf hne) ?_
    have htpos : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
    rw [div_le_iff₀ htpos]
    calc ∑ i ∈ T, ((E i).length : ℝ) ≤ ∑ _i ∈ T, ℓ := Finset.sum_le_sum hlen
      _ = ℓ * (T.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Coding

end Sunflower

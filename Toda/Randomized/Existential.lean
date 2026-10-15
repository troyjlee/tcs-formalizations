import Toda.Randomized.UniformWitness
import Toda.Randomized.ExistentialFinite
import Toda.Isolation.ParityExperiment
import Toda.Counting.BoundedWitness

/-!
# Uniform randomized existential elimination

One common inner random seed answers all candidate witnesses. Forty independent
affine isolation experiments turn their existence into a canonical parity
predicate. Every seed is an ordinary flat string, and all input adapters are
polynomial-time string functions.
-/

namespace Toda.Randomized

open Complexity Toda.Parity Toda.Isolation

/-- Existential quantification over strings of exactly the computed width. -/
def existsBitsLanguage (language : Language) (width : List Bool → ℕ) : Language :=
  {x | ∃ witness : Fin (width x) → Bool, pair x (List.ofFn witness) ∈ language}

/-- Move the common inner seed behind the witness in the source query. -/
def innerWitnessQuery (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (pairSnd z)) (pairSnd (pairFst z))

theorem innerWitnessQuery_mem_FP : innerWitnessQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

/-- Split the random tape into one common inner seed and the hash trials. -/
def existentialSeedQuery (innerWidth : List Bool → ℕ) (z : List Bool) : List Bool :=
  pair (pair (pairFst z) ((pairSnd z).take (innerWidth (pairFst z))))
    ((pairSnd z).drop (innerWidth (pairFst z)))

theorem existentialSeedQuery_mem_FP {innerWidth : List Bool → ℕ}
    (hinnerWidth : UnaryFn innerWidth) : existentialSeedQuery innerWidth ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (take_mem_FP pairSnd_mem_FP hinnerWidth.lift))
    (drop_mem_FP pairSnd_mem_FP hinnerWidth.lift)

/-- The suffix of a flat random tape is the second finite-block projection. -/
theorem ofFn_drop_blockSnd (a b : ℕ) (seed : Fin (a + b) → Bool) :
    (List.ofFn seed).drop a = List.ofFn (blockSnd a b seed) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_drop, List.getElem_ofFn]
    rfl

/-- The parity compiler agrees with the finite forty-trial experiment. -/
theorem pair_mem_repeatedIsolationLanguage_iff (language : Language)
    (width : List Bool → ℕ) (x : List Bool)
    (seed : BitString (40 * allWidthSeedWidth (width x))) :
    pair x (List.ofFn seed) ∈ repeatedIsolationLanguage language width ↔
      repeatedOddIsolation (sourceWitnesses language x (width x))
        (blocksEquiv 40 (allWidthSeedWidth (width x)) seed) = true := by
  classical
  rw [pair_mem_repeatedIsolationLanguage]
  simp only [repeatedOddIsolation, oddIsolationTrial, decide_eq_true_eq, Nat.odd_iff]

private theorem pair_mem_repeatedIsolationLanguage_at_width (language : Language)
    (width : List Bool → ℕ) (x : List Bool) {value : ℕ} (hwidth : width x = value)
    (seed : BitString (40 * allWidthSeedWidth value)) :
    pair x (List.ofFn seed) ∈ repeatedIsolationLanguage language width ↔
      repeatedOddIsolation (sourceWitnesses language x value)
        (blocksEquiv 40 (allWidthSeedWidth value) seed) = true := by
  subst value
  exact pair_mem_repeatedIsolationLanguage_iff language width x seed

/-- A single flat tape is bijective with the common seed and forty hash tapes. -/
def existentialSeedEquiv (innerWidth witnessWidth : ℕ) :
    BitString (innerWidth + 40 * allWidthSeedWidth witnessWidth) ≃
      BitString innerWidth × (Fin 40 → BitString (allWidthSeedWidth witnessWidth)) :=
  (blockEquiv innerWidth (40 * allWidthSeedWidth witnessWidth)).trans
    (Equiv.prodCongr (Equiv.refl _) (blocksEquiv 40 (allWidthSeedWidth witnessWidth)))

/-- The compiled randomized existential predicate. -/
noncomputable def existentialPredicate (predicate : Language)
    (witnessWidth innerWidth : List Bool → ℕ) : Language :=
  existentialSeedQuery innerWidth ⁻¹'
    repeatedIsolationLanguage (innerWitnessQuery ⁻¹' predicate)
      (fun z => witnessWidth (pairFst z))

theorem existentialPredicate_mem_parityP {predicate : Language}
    {witnessWidth innerWidth : List Bool → ℕ} (hpredicate : predicate ∈ ParityP)
    (hwitnessWidth : UnaryFn witnessWidth) (hinnerWidth : UnaryFn innerWidth) :
    existentialPredicate predicate witnessWidth innerWidth ∈ ParityP :=
  preimage_mem_parityP
    (repeatedIsolationLanguage_mem_parityP
      (preimage_mem_parityP hpredicate innerWitnessQuery_mem_FP) hwitnessWidth.lift)
    (existentialSeedQuery_mem_FP hinnerWidth)

/-- Exact flat-seed semantics, including the common inner seed. -/
theorem pair_mem_existentialPredicate (predicate : Language)
    (witnessWidth innerWidth : List Bool → ℕ) (x : List Bool)
    (seed : BitString (innerWidth x + 40 * allWidthSeedWidth (witnessWidth x))) :
    pair x (List.ofFn seed) ∈ existentialPredicate predicate witnessWidth innerWidth ↔
      repeatedOddIsolation
        (sourceWitnesses (innerWitnessQuery ⁻¹' predicate)
          (pair x (List.ofFn (existentialSeedEquiv (innerWidth x) (witnessWidth x) seed).1))
          (witnessWidth x))
        (existentialSeedEquiv (innerWidth x) (witnessWidth x) seed).2 = true := by
  change existentialSeedQuery innerWidth (pair x (List.ofFn seed)) ∈
    repeatedIsolationLanguage (innerWitnessQuery ⁻¹' predicate)
      (fun z => witnessWidth (pairFst z)) ↔ _
  simp only [existentialSeedQuery, pairFst_pair, pairSnd_pair,
    ofFn_take_blockFst, ofFn_drop_blockSnd]
  exact pair_mem_repeatedIsolationLanguage_at_width
    (innerWitnessQuery ⁻¹' predicate) (fun z => witnessWidth (pairFst z))
    (pair x (List.ofFn (blockFst (innerWidth x)
      (40 * allWidthSeedWidth (witnessWidth x)) seed)))
    (by simp) (blockSnd (innerWidth x) (40 * allWidthSeedWidth (witnessWidth x)) seed)

private theorem bool_mismatch_iff (value : Bool) (truth : Prop) [Decidable truth] :
    (¬ (value = true ↔ truth)) ↔ value ≠ decide truth := by
  cases value <;> by_cases htruth : truth <;> simp [htruth]

private theorem card_filter_equiv {First Second : Type*} [Fintype First] [Fintype Second]
    (equivalence : First ≃ Second) (first : First → Prop) (second : Second → Prop)
    [DecidablePred first] [DecidablePred second]
    (hiff : ∀ value, first value ↔ second (equivalence value)) :
    (Finset.univ.filter first).card = (Finset.univ.filter second).card := by
  have h := Fintype.card_congr (equivalence.subtypeEquiv hiff)
  simpa only [Fintype.card_subtype] using h

/-- Exact-width existential quantification preserves bounded-error parity
predicates, with a uniform polynomial seed and the same error guarantee. -/
theorem existsBitsLanguage_mem_bpParityP {language : Language}
    {witnessWidth : List Bool → ℕ} (hlanguage : language ∈ BPParityP)
    (hwitnessWidth : UnaryFn witnessWidth) :
    existsBitsLanguage language witnessWidth ∈ BPParityP := by
  classical
  obtain ⟨predicate, innerWidth, hpredicate, hinnerWidth, hbad⟩ :=
    exists_common_good_seed_predicate hlanguage hwitnessWidth
  let totalWidth := fun x => innerWidth x + 40 * allWidthSeedWidth (witnessWidth x)
  refine ⟨existentialPredicate predicate witnessWidth innerWidth, totalWidth,
    existentialPredicate_mem_parityP hpredicate hwitnessWidth hinnerWidth,
    hinnerWidth.add ((UnaryFn.const 40).mul (allWidthSeedWidth_unary hwitnessWidth)), ?_⟩
  intro x
  let truth := sourceWitnesses language x (witnessWidth x)
  let witnesses := fun seed : BitString (innerWidth x) =>
    sourceWitnesses (innerWitnessQuery ⁻¹' predicate)
      (pair x (List.ofFn seed)) (witnessWidth x)
  have hgood : ∀ seed, seed ∉
      allWitnessErrorSeeds language predicate witnessWidth innerWidth x →
      witnesses seed = truth := by
    intro seed hseed
    have hcorrect := (not_mem_allWitnessErrorSeeds_iff
      language predicate witnessWidth innerWidth x seed).mp hseed
    ext witness
    simpa [witnesses, truth, sourceWitnesses, innerWitnessQuery] using hcorrect witness
  have hbound := existential_two_stage_error_bound
    (allWitnessErrorSeeds language predicate witnessWidth innerWidth x)
    truth witnesses (by simpa using hbad x) hgood
  have htruth : x ∈ existsBitsLanguage language witnessWidth ↔ truth.Nonempty := by
    simp [existsBitsLanguage, truth, sourceWitnesses, Finset.filter_nonempty_iff]
  have herror (seed : BitString (totalWidth x)) :
      (¬ (pair x (List.ofFn seed) ∈ existentialPredicate predicate witnessWidth innerWidth ↔
        x ∈ existsBitsLanguage language witnessWidth)) ↔
      repeatedOddIsolation
        (witnesses (existentialSeedEquiv (innerWidth x) (witnessWidth x) seed).1)
        (existentialSeedEquiv (innerWidth x) (witnessWidth x) seed).2 ≠
          decide truth.Nonempty := by
    rw [pair_mem_existentialPredicate, htruth]
    exact bool_mismatch_iff _ _
  have hcard := card_filter_equiv
    (existentialSeedEquiv (innerWidth x) (witnessWidth x))
      (fun seed => ¬ (pair x (List.ofFn seed) ∈
        existentialPredicate predicate witnessWidth innerWidth ↔
          x ∈ existsBitsLanguage language witnessWidth))
      (fun seeds => repeatedOddIsolation (witnesses seeds.1) seeds.2 ≠
        decide truth.Nonempty) herror
  change 16 * (Finset.univ.filter fun seed : BitString (totalWidth x) =>
    ¬ (pair x (List.ofFn seed) ∈ existentialPredicate predicate witnessWidth innerWidth ↔
      x ∈ existsBitsLanguage language witnessWidth)).card ≤ _
  rw [hcard]
  convert hbound using 1
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, totalWidth,
    pow_add]
  rw [← pow_mul, Nat.mul_comm 40]

/-- Canonical polynomially bounded existential quantification preserves the
randomized parity witness operator. -/
theorem polyExistsLang_mem_bpParityP {language : Language}
    (hlanguage : language ∈ BPParityP) (polynomial : Polynomial ℕ) :
    polyExistsLang polynomial language ∈ BPParityP := by
  have hdecoded := preimage_mem_bpParityP hlanguage Toda.Counting.decodeWitnessPair_mem_FP
  have hwidth := (Toda.Counting.polynomial_eval_unary
    (UnaryFn.length id_mem_FP) polynomial).add (UnaryFn.const 1)
  have h := existsBitsLanguage_mem_bpParityP hdecoded hwidth
  dsimp only [id_eq] at h
  have heq : existsBitsLanguage (Toda.Counting.decodeWitnessPair ⁻¹' language)
      (fun x => polynomial.eval x.length + 1) = polyExistsLang polynomial language := by
    ext x
    exact (Toda.Counting.polyExistsLang_iff_exactWidth polynomial language x).symm
  rw [heq] at h
  exact h

end Toda.Randomized

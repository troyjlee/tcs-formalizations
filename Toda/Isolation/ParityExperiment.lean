import Toda.Isolation.AffineEval
import Toda.Parity.Class.Repetition

/-!
# The affine isolation experiment as a canonical parity language

The ordinary input is `pair x seed`. For each possible hash width, the machine
counts the witnesses accepted by the source parity predicate and retained by
the polynomial-time affine zero-cell test. It accepts if one such count is
odd. Uniform parity quantification and polynomially bounded disjunction supply
canonical ParityP membership for the complete experiment.
-/

namespace Toda.Isolation

open Complexity Parity

/-- Source input inside `pair (pair (pair x seed) index) witness`. -/
def experimentSource (z : List Bool) : List Bool := pairFst (pairFst (pairFst z))

/-- Source parity query on the original input and the guessed witness. -/
def experimentQuery (z : List Bool) : List Bool := pair (experimentSource z) (pairSnd z)

theorem experimentSource_mem_FP : experimentSource ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP

theorem experimentQuery_mem_FP : experimentQuery ∈ FP :=
  mem_FP_pair experimentSource_mem_FP pairSnd_mem_FP

/-- The hash zero-cell predicate on an encoded source, flat seed, width index,
and witness. Every malformed input is interpreted through total projections. -/
def experimentHashLanguage (n : List Bool → ℕ) : Language :=
  {z | affineZero (n (experimentSource z)) ((pairSnd (pairFst z)).length + 2)
    (pairSnd (pairFst (pairFst z))) (pairSnd z)
    (affineBlockOffset (n (experimentSource z)) (pairSnd (pairFst z)).length)}

theorem experimentHashLanguage_mem_P {n : List Bool → ℕ} (hn : UnaryFn n) :
    experimentHashLanguage n ∈ Complexity.P := by
  have hdimension := hn.comp experimentSource_mem_FP
  have hindex := UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  exact (affineZero_fppred hdimension (hindex.add (UnaryFn.const 2))
    (affineBlockOffset_unary hdimension hindex)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    pairSnd_mem_FP).mem_P

def hashedWitnessLanguage (L : Language) (n : List Bool → ℕ) : Language :=
  experimentQuery ⁻¹' L ∩ experimentHashLanguage n

theorem hashedWitnessLanguage_mem_parityP {L : Language} {n : List Bool → ℕ}
    (hL : L ∈ ParityP) (hn : UnaryFn n) : hashedWitnessLanguage L n ∈ ParityP :=
  inter_mem_parityP (preimage_mem_parityP hL experimentQuery_mem_FP)
    (P_subset_parityP (experimentHashLanguage_mem_P hn))

/-- Parity of the accepted witnesses in one chosen affine zero-cell. -/
noncomputable def widthParityLanguage (L : Language) (n : List Bool → ℕ) : Language :=
  xorBitsLanguage (hashedWitnessLanguage L n) (fun z => n (pairFst (pairFst z)))

theorem widthParityLanguage_mem_parityP {L : Language} {n : List Bool → ℕ}
    (hL : L ∈ ParityP) (hn : UnaryFn n) : widthParityLanguage L n ∈ ParityP :=
  xorBitsLanguage_mem_parityP (hashedWitnessLanguage_mem_parityP hL hn)
    (hn.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))

/-- Accept if some width between `2` and `n(x)+2` leaves an odd number of
source-accepted witnesses. The flat seed is the second input component. -/
noncomputable def isolationLanguage (L : Language) (n : List Bool → ℕ) : Language :=
  existsIndexLanguage (widthParityLanguage L n) (fun z => n (pairFst z) + 1)

/-- The complete uniformly sized affine isolation experiment is a canonical
parity-counting language. -/
theorem isolationLanguage_mem_parityP {L : Language} {n : List Bool → ℕ}
    (hL : L ∈ ParityP) (hn : UnaryFn n) : isolationLanguage L n ∈ ParityP :=
  existsIndexLanguage_mem_parityP (widthParityLanguage_mem_parityP hL hn)
    (hn.lift.add (UnaryFn.const 1))

/-- The finite set of source-accepted witnesses at a fixed length. -/
noncomputable def sourceWitnesses (L : Language) (x : List Bool) (width : ℕ) :
    Finset (BitString width) := by
  classical
  exact Finset.univ.filter fun witness => pair x (List.ofFn witness) ∈ L

private theorem card_filter_ofFn_width_congr {first second : ℕ}
    (predicate : List Bool → Prop) [DecidablePred predicate] (hwidth : first = second) :
    (Finset.univ.filter fun bits : Fin first → Bool => predicate (List.ofFn bits)).card =
      (Finset.univ.filter fun bits : Fin second → Bool => predicate (List.ofFn bits)).card := by
  subst second
  rfl

/-- Exact semantics of one hashed parity query on a complete flat seed. -/
theorem pair_mem_widthParityLanguage (L : Language) (n : List Bool → ℕ)
    (x : List Bool) (seed : BitString (allWidthSeedWidth (n x))) (index : Fin (n x + 1)) :
    pair (pair x (List.ofFn seed)) (List.replicate index.val true) ∈
        widthParityLanguage L n ↔
      (survivors (allWidthKeep (n x) index) (sourceWitnesses L x (n x))
        (decodeAllWidths (n x) seed index)).card % 2 = 1 := by
  classical
  simp only [widthParityLanguage, xorBitsLanguage, Set.mem_ofPred_eq]
  rw [card_filter_ofFn_width_congr (second := n x)
    (fun bits => pair (pair (pair x (List.ofFn seed)) (List.replicate index.val true)) bits ∈
      hashedWitnessLanguage L n) (by simp)]
  simp only [hashedWitnessLanguage,
    Set.mem_ofPred_eq, pairFst_pair, Set.mem_inter_iff, Set.mem_preimage,
    experimentQuery, experimentSource, pairSnd_pair, experimentHashLanguage,
    List.length_replicate]
  simp only [affineZero_allWidths_iff, survivors, sourceWitnesses, Finset.filter_filter]

/-- Exact semantics of the complete experiment: OR of the hashed parities. -/
theorem pair_mem_isolationLanguage (L : Language) (n : List Bool → ℕ)
    (x : List Bool) (seed : BitString (allWidthSeedWidth (n x))) :
    pair x (List.ofFn seed) ∈ isolationLanguage L n ↔
      ∃ index : Fin (n x + 1),
        (survivors (allWidthKeep (n x) index) (sourceWitnesses L x (n x))
          (decodeAllWidths (n x) seed index)).card % 2 = 1 := by
  simp only [isolationLanguage, existsIndexLanguage, Set.mem_ofPred_eq]
  rw [pairFst_pair]
  apply exists_congr
  intro index
  exact pair_mem_widthParityLanguage L n x seed index

/-- Any seed giving genuine singleton isolation is accepted by the parity
experiment. Other odd-sized cells may also be accepted. -/
theorem flatAllWidthSuccess_subset_seedEvent (L : Language) (n : List Bool → ℕ)
    (x : List Bool) :
    flatAllWidthSuccess (sourceWitnesses L x (n x)) ⊆
      seedEvent (isolationLanguage L n) x (allWidthSeedWidth (n x)) := by
  intro seed hseed
  rw [mem_seedEvent, pair_mem_isolationLanguage]
  obtain ⟨index, hindex⟩ :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hseed).2).2
  exact ⟨index, by rw [hindex]⟩

/-- Nonempty source witness sets are accepted with probability at least one
eighth by the actual parity language on uniform flat affine seeds. -/
theorem isolation_seedEvent_probability_ge_one_eighth (L : Language) (n : List Bool → ℕ)
    (x : List Bool) (hsource : (sourceWitnesses L x (n x)).Nonempty) :
    (1 : ℚ) / 8 ≤ eventProb
      (seedEvent (isolationLanguage L n) x (allWidthSeedWidth (n x))) :=
  (flatAllWidthSuccess_probability_ge_one_eighth _ hsource).trans
    (eventProb_mono (flatAllWidthSuccess_subset_seedEvent L n x))

/-- An empty source witness set rejects for every seed. -/
theorem isolation_rejects_of_empty (L : Language) (n : List Bool → ℕ)
    (x : List Bool) (hsource : sourceWitnesses L x (n x) = ∅)
    (seed : BitString (allWidthSeedWidth (n x))) :
    pair x (List.ofFn seed) ∉ isolationLanguage L n := by
  rw [pair_mem_isolationLanguage]
  simp [hsource, survivors]

/-- Forty independent all-width trials, with the same original source input
passed to every trial. -/
noncomputable def repeatedIsolationLanguage (L : Language) (n : List Bool → ℕ) : Language :=
  repeatExistsLanguage (isolationLanguage L n) (fun x => allWidthSeedWidth (n x))
    (fun _ => 40)

theorem repeatedIsolationLanguage_mem_parityP {L : Language} {n : List Bool → ℕ}
    (hL : L ∈ ParityP) (hn : UnaryFn n) : repeatedIsolationLanguage L n ∈ ParityP :=
  repeatExistsLanguage_mem_parityP (isolationLanguage_mem_parityP hL hn)
    (allWidthSeedWidth_unary hn) (UnaryFn.const 40)

/-- Exact forty-trial semantics, suitable for the finite two-stage error
bound with one common inner random seed inside the source input. -/
theorem pair_mem_repeatedIsolationLanguage (L : Language) (n : List Bool → ℕ)
    (x : List Bool) (seed : BitString (40 * allWidthSeedWidth (n x))) :
    pair x (List.ofFn seed) ∈ repeatedIsolationLanguage L n ↔
      ∃ trial : Fin 40, ∃ index : Fin (n x + 1),
        (survivors (allWidthKeep (n x) index) (sourceWitnesses L x (n x))
          (decodeAllWidths (n x) (blocksEquiv 40 (allWidthSeedWidth (n x)) seed trial)
            index)).card % 2 = 1 := by
  rw [repeatedIsolationLanguage, pair_mem_repeatExistsLanguage]
  simp only [mem_seedEvent, pair_mem_isolationLanguage]

end Toda.Isolation

import Toda.Parity.Class.Majority

/-!
# Independent-block repetition of canonical parity predicates

Every repeated call receives an actual FP-extracted seed block. The resulting
parity language agrees exactly with the finite independent-block majority used
in probability estimates; block counts and widths may depend on the input.
-/

namespace Toda.Parity

open Complexity

/-- The indexed query uses the requested block of the original random tape. -/
def repetitionQuery (q : List Bool → ℕ) (w : List Bool) : List Bool :=
  pair (pairFst (pairFst w))
    (((pairSnd (pairFst w)).drop ((pairSnd w).length * q (pairFst (pairFst w)))).take
      (q (pairFst (pairFst w))))

theorem repetitionQuery_mem_FP {q : List Bool → ℕ} (hq : UnaryFn q) :
    repetitionQuery q ∈ FP := by
  have hx := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hw := hq.comp hx
  exact mem_FP_pair hx (take_mem_FP (drop_mem_FP hs (UnaryFn.index.mul hw)) hw)

/-- Repetition over consecutive equal-width seed blocks. -/
noncomputable def repeatMajorityLanguage (L : Language) (q k : List Bool → ℕ) :
    Language := majorityIndexLanguage ((repetitionQuery q) ⁻¹' L)
      (fun z => k (pairFst z))

theorem repeatMajorityLanguage_mem_parityP {L : Language} {q k : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) (hk : UnaryFn k) :
    repeatMajorityLanguage L q k ∈ ParityP :=
  majorityIndexLanguage_mem_parityP
    (preimage_mem_parityP hL (repetitionQuery_mem_FP hq)) hk.lift

/-- The ordinary string slice is the exact block in the finite product
sample space, even when the block width is zero. -/
theorem ofFn_slice_blocks {k T : ℕ} (seed : Fin (k * T) → Bool) (i : Fin k) :
    ((List.ofFn seed).drop (i.val * T)).take T =
      List.ofFn (blocksEquiv k T seed i) := by
  have hroom : i.val * T + T ≤ k * T := by
    have h := Nat.mul_le_mul_right T (Nat.succ_le_of_lt i.isLt)
    simpa [Nat.add_mul] using h
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    exact Nat.min_eq_left (by omega)
  · intro j hj hj'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
      blocksEquiv_apply]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- The exact single-run success event at the chosen width. -/
noncomputable def seedEvent (L : Language) (x : List Bool) (width : ℕ) :
    Finset (Fin width → Bool) := by
  classical
  exact Finset.univ.filter fun seed => pair x (List.ofFn seed) ∈ L

@[simp] theorem mem_seedEvent (L : Language) (x : List Bool) (width : ℕ)
    (seed : Fin width → Bool) :
    seed ∈ seedEvent L x width ↔ pair x (List.ofFn seed) ∈ L := by
  classical
  simp [seedEvent]

/-- The compiled repetition language has exactly independent-block majority
semantics on every complete random seed. -/
theorem pair_mem_repeatMajorityLanguage (L : Language) (q k : List Bool → ℕ)
    (x : List Bool) (seed : Fin (k x * q x) → Bool) :
    pair x (List.ofFn seed) ∈ repeatMajorityLanguage L q k ↔
      blockMajority (seedEvent L x (q x)) seed = true := by
  classical
  simp only [repeatMajorityLanguage, majorityIndexLanguage, Set.mem_ofPred_eq]
  rw [pairFst_pair]
  change majority (fun i : Fin (k x) =>
    decide (repetitionQuery q (pair (pair x (List.ofFn seed))
      (List.replicate i.val true)) ∈ L)) = true ↔ _
  have hbits : (fun i : Fin (k x) =>
      decide (repetitionQuery q (pair (pair x (List.ofFn seed))
        (List.replicate i.val true)) ∈ L)) =
      (fun i => decide (blocksEquiv (k x) (q x) seed i ∈ seedEvent L x (q x))) := by
    funext i
    simp only [repetitionQuery, pairFst_pair, pairSnd_pair, List.length_replicate,
      ofFn_slice_blocks, mem_seedEvent]
  rw [hbits]
  rfl

/-- Accept when at least one of the independent blocks succeeds. -/
def repeatExistsLanguage (L : Language) (q k : List Bool → ℕ) : Language :=
  existsIndexLanguage ((repetitionQuery q) ⁻¹' L) (fun z => k (pairFst z))

theorem repeatExistsLanguage_mem_parityP {L : Language} {q k : List Bool → ℕ}
    (hL : L ∈ ParityP) (hq : UnaryFn q) (hk : UnaryFn k) :
    repeatExistsLanguage L q k ∈ ParityP :=
  existsIndexLanguage_mem_parityP
    (preimage_mem_parityP hL (repetitionQuery_mem_FP hq)) hk.lift

/-- OR repetition uses exactly the independent seed blocks, with no ignored
positions. The empty collection rejects. -/
theorem pair_mem_repeatExistsLanguage (L : Language) (q k : List Bool → ℕ)
    (x : List Bool) (seed : Fin (k x * q x) → Bool) :
    pair x (List.ofFn seed) ∈ repeatExistsLanguage L q k ↔
      ∃ i : Fin (k x), blocksEquiv (k x) (q x) seed i ∈ seedEvent L x (q x) := by
  simp only [repeatExistsLanguage, existsIndexLanguage, Set.mem_ofPred_eq,
    Set.mem_preimage]
  rw [pairFst_pair]
  apply exists_congr
  intro i
  simp only [repetitionQuery, pairFst_pair, pairSnd_pair, List.length_replicate,
    ofFn_slice_blocks, mem_seedEvent]

end Toda.Parity

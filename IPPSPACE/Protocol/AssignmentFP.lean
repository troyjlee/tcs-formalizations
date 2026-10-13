/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.RoundFP

/-!
# Polynomial-time finite assignment lookup

Updates are a linear-size chain of upstream pairs. Keys stay in binary, and
lookup selects the newest matching entry, with encoded zero as the default.
The raw procedure is total and polynomial-time on every string; its semantic
refinement applies to encoded finite assignments. No array indexed by a name's
numeric value is constructed. The resulting encoded finite-claim operations
certify initialization, lookup, the existing round check, and claim advancement.
Raw lookup does not validate arbitrary assignment chains; its semantic theorems
use canonical internal states. Transcript replay remains a separate obligation.
-/

namespace IPPSPACE

open Complexity

/-- Skip a bounded number of links, with upstream's total fallback on malformed strings. -/
def assignmentChainDrop (count : ℕ) (bits : List Bool) : List Bool := pairSnd^[count] bits

def assignmentChainEntry (count : ℕ) (bits : List Bool) : List Bool :=
  pairFst (assignmentChainDrop count bits)

@[simp] theorem assignmentChainDrop_zero (bits : List Bool) : assignmentChainDrop 0 bits = bits := rfl

@[simp] theorem assignmentChainDrop_succ_pair (count : ℕ) (entry rest : List Bool) :
    assignmentChainDrop (count + 1) (pair entry rest) = assignmentChainDrop count rest := by
  simp [assignmentChainDrop, Function.iterate_succ_apply]

@[simp] theorem assignmentChainEntry_zero_pair (entry rest : List Bool) :
    assignmentChainEntry 0 (pair entry rest) = entry := by
  simp [assignmentChainEntry]

@[simp] theorem assignmentChainEntry_succ_pair (count : ℕ) (entry rest : List Bool) :
    assignmentChainEntry (count + 1) (pair entry rest) = assignmentChainEntry count rest := by
  simp [assignmentChainEntry]

@[simp] theorem assignmentChainDrop_nil (count : ℕ) : assignmentChainDrop count [] = [] := by
  induction count with
  | zero => rfl
  | succ n ih =>
    change pairSnd^[n + 1] [] = []
    rw [Function.iterate_succ_apply', show pairSnd^[n] [] = [] from ih]
    rfl

@[simp] theorem assignmentChainEntry_nil (count : ℕ) : assignmentChainEntry count [] = [] := by
  simp [assignmentChainEntry, pairFst]

theorem assignmentChainDrop_mem_FP {count : List Bool → ℕ} {bits : List Bool → List Bool}
    (hc : UnaryFn count) (hb : bits ∈ FP) :
    (fun z => assignmentChainDrop (count z) (bits z)) ∈ FP := by
  have h := iterate_mem_FP_of_step_le pairSnd_mem_FP hb hc.mem_FP 0 (fun z n _ => by
    rw [Function.iterate_succ_apply']
    simpa using pairSnd_length_le (pairSnd^[n] (bits z)))
  simpa only [List.length_replicate, assignmentChainDrop] using h

theorem assignmentChainEntry_mem_FP {count : List Bool → ℕ} {bits : List Bool → List Bool}
    (hc : UnaryFn count) (hb : bits ∈ FP) :
    (fun z => assignmentChainEntry (count z) (bits z)) ∈ FP :=
  mem_FP_comp (assignmentChainDrop_mem_FP hc hb) pairFst_mem_FP

/-- A nonempty entry's binary key matches the query's numeric value. -/
def AssignmentEntryMatches (query entry : List Bool) : Prop :=
  entry ≠ [] ∧ nameBitsValue query = nameBitsValue (pairFst entry)

instance (query entry : List Bool) : Decidable (AssignmentEntryMatches query entry) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem assignmentEntryMatches_nil (query : List Bool) : ¬ AssignmentEntryMatches query [] := by
  simp [AssignmentEntryMatches]

@[simp] theorem assignmentEntryMatches_pair (query key value : List Bool) :
    AssignmentEntryMatches query (pair key value) ↔ nameBitsValue query = nameBitsValue key := by
  have hne : pair key value ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [pair_length] at this
  simp [AssignmentEntryMatches, hne]

/-- Search links in newest-first order, returning fuel if none matches. -/
def assignmentFindIndex (fuel : ℕ) (query bits : List Bool) : ℕ :=
  (List.range fuel).findIdx (fun i => decide (AssignmentEntryMatches query (assignmentChainEntry i bits)))

def assignmentLookupBitsWithFuel (p fuel : ℕ) (query bits : List Bool) : List Bool :=
  let index := assignmentFindIndex fuel query bits
  if index < fuel then pairSnd (assignmentChainEntry index bits) else roundConstantBits p 0

/-- Input length bounds the number of links in every canonical assignment chain. -/
def assignmentLookupBits (p : ℕ) (query bits : List Bool) : List Bool :=
  assignmentLookupBitsWithFuel p bits.length query bits

theorem assignmentEntryMatches_fppred {query entry : List Bool → List Bool}
    (hq : query ∈ FP) (he : entry ∈ FP) :
    FPPred fun z => AssignmentEntryMatches (query z) (entry z) :=
  ((bitStrings_eq_fppred he (constFn_mem_FP [])).not).and
    (nameBitsValue_eq_fppred hq (mem_FP_comp he pairFst_mem_FP))

theorem assignmentFindIndex_unaryFn {fuel : List Bool → ℕ}
    {query bits : List Bool → List Bool} (hf : UnaryFn fuel) (hq : query ∈ FP) (hb : bits ∈ FP) :
    UnaryFn fun z => assignmentFindIndex (fuel z) (query z) (bits z) := by
  have htest := assignmentEntryMatches_fppred (mem_FP_comp pairFst_mem_FP hq)
    (assignmentChainEntry_mem_FP UnaryFn.index (mem_FP_comp pairFst_mem_FP hb))
  simpa only [assignmentFindIndex, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate] using hf.find htest

theorem assignmentLookupBitsWithFuel_mem_FP {p fuel : List Bool → ℕ}
    {query bits : List Bool → List Bool} (hp : UnaryFn p) (hf : UnaryFn fuel)
    (hq : query ∈ FP) (hb : bits ∈ FP) :
    (fun z => assignmentLookupBitsWithFuel (p z) (fuel z) (query z) (bits z)) ∈ FP := by
  have hi := assignmentFindIndex_unaryFn hf hq hb
  exact (FPPred.lt hi hf).ite_mem_FP
    (mem_FP_comp (assignmentChainEntry_mem_FP hi hb) pairSnd_mem_FP)
    (reduceResidueWord_bits_mem_FP hp (UnaryFn.const 0))

theorem assignmentLookupBits_mem_FP {p : List Bool → ℕ} {query bits : List Bool → List Bool}
    (hp : UnaryFn p) (hq : query ∈ FP) (hb : bits ∈ FP) :
    (fun z => assignmentLookupBits (p z) (query z) (bits z)) ∈ FP :=
  assignmentLookupBitsWithFuel_mem_FP hp (UnaryFn.length hb) hq hb

/-- A linear chain of binary key/residue-word pairs, newest update first. -/
def encodeAssignmentEntries {p : ℕ} : List (ℕ × ZMod p) → List Bool
  | [] => []
  | (name, value) :: rest =>
      pair (pair name.bits (wordBits (encodeResidue value))) (encodeAssignmentEntries rest)

theorem encodeAssignmentEntries_length_ge {p : ℕ} (entries : List (ℕ × ZMod p)) :
    entries.length ≤ (encodeAssignmentEntries entries).length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨name, value⟩
    simp only [encodeAssignmentEntries, pair_length, List.length_cons]
    omega

@[simp] theorem assignmentFindIndex_nil (fuel : ℕ) (query : List Bool) :
    assignmentFindIndex fuel query [] = fuel := by
  simp only [assignmentFindIndex, assignmentChainEntry_nil,
    assignmentEntryMatches_nil, decide_false]
  rw [List.findIdx_eq_length_of_false (fun _ _ => rfl), List.length_range]

theorem assignmentFindIndex_succ_pair (fuel : ℕ) (query entry rest : List Bool) :
    assignmentFindIndex (fuel + 1) query (pair entry rest) =
      if AssignmentEntryMatches query entry then 0 else assignmentFindIndex fuel query rest + 1 := by
  simp only [assignmentFindIndex, List.range_succ_eq_map, List.findIdx_cons,
    List.findIdx_map, assignmentChainEntry_zero_pair, assignmentChainEntry_succ_pair,
    decide_eq_true_eq, Function.comp_def]

/-- Canonical chains return exactly the newest finite assignment, with zero default. -/
theorem assignmentLookupBitsWithFuel_encode {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (query fuel : ℕ) (hfuel : entries.length ≤ fuel) :
    assignmentLookupBitsWithFuel p fuel query.bits (encodeAssignmentEntries entries) =
      wordBits (encodeResidue (assignmentLookupWithCost entries query).1) := by
  induction entries generalizing fuel with
  | nil => simp [assignmentLookupBitsWithFuel, encodeAssignmentEntries, assignmentLookupWithCost]
  | cons entry entries ih =>
    rcases entry with ⟨name, value⟩
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hf : entries.length ≤ fuel := by simpa using Nat.le_of_succ_le_succ hfuel
      by_cases heq : query = name
      · simp [assignmentLookupBitsWithFuel, encodeAssignmentEntries,
          assignmentFindIndex_succ_pair, assignmentLookupWithCost, heq]
      · simpa [assignmentLookupBitsWithFuel, encodeAssignmentEntries,
          assignmentFindIndex_succ_pair, assignmentLookupWithCost, heq] using ih fuel hf

@[simp] theorem assignmentLookupBits_encode {p : ℕ} [NeZero p]
    (entries : List (ℕ × ZMod p)) (query : ℕ) :
    assignmentLookupBits p query.bits (encodeAssignmentEntries entries) =
      wordBits (encodeResidue (assignmentLookupWithCost entries query).1) :=
  assignmentLookupBitsWithFuel_encode entries query _ (encodeAssignmentEntries_length_ge entries)

/-- A persistent claim uses one chain and one current residue word. -/
def encodeFiniteClaim {p : ℕ} (c : FiniteClaim (ZMod p)) : List Bool :=
  pair (encodeAssignmentEntries c.entries) (wordBits (encodeResidue c.value))

@[simp] theorem pairFst_encodeFiniteClaim {p : ℕ} (c : FiniteClaim (ZMod p)) :
    pairFst (encodeFiniteClaim c) = encodeAssignmentEntries c.entries := pairFst_pair _ _

@[simp] theorem pairSnd_encodeFiniteClaim {p : ℕ} (c : FiniteClaim (ZMod p)) :
    pairSnd (encodeFiniteClaim c) = wordBits (encodeResidue c.value) := pairSnd_pair _ _

/-- Prepending one update has additive size, including the binary name's digits. -/
theorem encodeAssignmentEntries_cons_length {p : ℕ} (name : ℕ) (value : ZMod p)
    (entries : List (ℕ × ZMod p)) :
    (encodeAssignmentEntries ((name, value) :: entries)).length =
      (encodeAssignmentEntries entries).length + 4 * name.bits.length + 2 * residueWidth p + 6 := by
  simp only [encodeAssignmentEntries, pair_length, length_wordBits]
  omega

/-- Lookup retains binary names throughout the certified computation. -/
theorem finiteClaim_point_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z))) (query : List Bool → ℕ)
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP)
    (hq : (fun z => (query z).bits) ∈ FP) :
    (fun z => wordBits (encodeResidue ((c z).point (query z)))) ∈ FP := by
  have he : (fun z => encodeAssignmentEntries (c z).entries) ∈ FP := by
    exact mem_FP_of_eq (mem_FP_comp hc pairFst_mem_FP) (fun z => pairFst_encodeFiniteClaim (c z))
  apply mem_FP_of_eq (assignmentLookupBits_mem_FP hp hq he)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  exact assignmentLookupBits_encode (c z).entries (query z)

/-- The initial stored claim is polynomial-time in a unary-computable modulus. -/
theorem finiteInitialClaim_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0) :
    (fun z => encodeFiniteClaim (finiteInitialClaim (R := ZMod (p z)))) ∈ FP := by
  apply mem_FP_of_eq (mem_FP_pair (constFn_mem_FP [])
    (reduceResidueWord_bits_mem_FP hp (UnaryFn.const 1)))
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  simp [encodeFiniteClaim, finiteInitialClaim, encodeAssignmentEntries,
    reduceResidueWord_eq_encodeResidue]

/-- One state update composes binary-name insertion with the certified Horner evaluator. -/
theorem finiteClaim_advance_bits_mem_FP {p : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z))) (op : List Bool → AlgebraicOperator)
    (as : (z : List Bool) → List (ZMod (p z))) (r : (z : List Bool) → ZMod (p z))
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP)
    (hi : (fun z => (op z).coordinate.bits) ∈ FP)
    (has : (fun z => encodeMessage (as z)) ∈ FP)
    (hr : (fun z => wordBits (encodeResidue (r z))) ∈ FP) :
    (fun z => encodeFiniteClaim ((c z).advanceWithCost (op z) (as z) (r z)).1) ∈ FP := by
  have he : (fun z => encodeAssignmentEntries (c z).entries) ∈ FP := by
    exact mem_FP_of_eq (mem_FP_comp hc pairFst_mem_FP) (fun z => pairFst_encodeFiniteClaim (c z))
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hi hr) he)
    (coefficientsEval_bits_mem_FP hp hnz r as hr has)

/-- Checking one encoded finite claim includes newest-first assignment lookup.
The raw message may be malformed; the existing bounded parser determines rejection. -/
theorem finiteClaim_parse_checkRound_mem_FP {p degree : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0) (hd : UnaryFn degree)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z))) (op : List Bool → AlgebraicOperator)
    (message : List Bool → List Bool)
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP)
    (hk : UnaryFn fun z => (op z).roundKind)
    (hi : (fun z => (op z).coordinate.bits) ∈ FP) (hm : message ∈ FP) :
    (fun z => [match parseMessage (p z) (degree z + 1) (message z) with
      | none => false
      | some as => (checkRoundWithCost (op z) (degree z) (c z) as).1]) ∈ FP := by
  have hx := finiteClaim_point_bits_mem_FP hp hnz c (fun z => (op z).coordinate) hc hi
  have hv : (fun z => wordBits (encodeResidue (c z).value)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hc pairSnd_mem_FP) (fun z => pairSnd_encodeFiniteClaim (c z))
  apply mem_FP_of_eq (checkRoundBits_mem_FP hp hk hd hx hv hm)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  rw [checkRoundBits_eq]
  cases parseMessage (p z) (degree z + 1) (message z) <;> rfl

/-- The existing finite verifier's round predicate is polynomial-time on
encoded claims and coefficient lists, including lists above the degree bound. -/
theorem finiteClaim_checkRound_mem_FP {p degree : List Bool → ℕ}
    (hp : UnaryFn p) (hnz : ∀ z, p z ≠ 0) (hd : UnaryFn degree)
    (c : (z : List Bool) → FiniteClaim (ZMod (p z))) (op : List Bool → AlgebraicOperator)
    (as : (z : List Bool) → List (ZMod (p z)))
    (hc : (fun z => encodeFiniteClaim (c z)) ∈ FP)
    (hk : UnaryFn fun z => (op z).roundKind)
    (hi : (fun z => (op z).coordinate.bits) ∈ FP)
    (has : (fun z => encodeMessage (as z)) ∈ FP) :
    (fun z => [(checkRoundWithCost (op z) (degree z) (c z) (as z)).1]) ∈ FP := by
  have hx := finiteClaim_point_bits_mem_FP hp hnz c (fun z => (op z).coordinate) hc hi
  have hv : (fun z => wordBits (encodeResidue (c z).value)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hc pairSnd_mem_FP) (fun z => pairSnd_encodeFiniteClaim (c z))
  apply mem_FP_of_eq (checkRoundBits_mem_FP hp hk hd hx hv has)
  intro z
  let : NeZero (p z) := ⟨hnz z⟩
  rw [checkRoundBits_encodeMessage]

end IPPSPACE

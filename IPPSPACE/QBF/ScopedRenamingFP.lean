/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexConversionFP
import IPPSPACE.Protocol.AssignmentFP

/-!
# Binary environments for scoped binder freshening

A persistent newest-first chain represents the environment passed by the exact
prenex converter. Lookup defaults to the original name, and entering a binder
pushes one update. Returning to the saved tail restores the outer environment.
Both keys and fresh values remain binary, with additive encoded growth.

These are actual `FP` certificates for the environment operations. They do not
certify the traversal, prefix assembly, or complete prenex converter runtime.
-/

namespace IPPSPACE

open Complexity

/-- An environment contains only the active binder updates, innermost first. -/
def scopedNameLookup : List (ℕ × ℕ) → ℕ → ℕ
  | [], query => query
  | (source, target) :: rest, query =>
      if query = source then target else scopedNameLookup rest query

@[simp] theorem scopedNameLookup_nil : scopedNameLookup [] = id := rfl

/-- A push is exactly the function update used in `prenexAux`. -/
theorem scopedNameLookup_cons (source target : ℕ) (rest : List (ℕ × ℕ)) :
    scopedNameLookup ((source, target) :: rest) =
      Function.update (scopedNameLookup rest) source target := by
  funext query
  by_cases h : query = source <;> simp [scopedNameLookup, h]

@[simp] theorem scopedNameLookup_shadow (source inner outer : ℕ)
    (rest : List (ℕ × ℕ)) :
    scopedNameLookup ((source, inner) :: (source, outer) :: rest) =
      scopedNameLookup ((source, inner) :: rest) := by
  funext query
  by_cases h : query = source <;> simp [scopedNameLookup, h]

/-- Pairs are the already imported upstream code; the tail is stored once. -/
def encodeNameEnvironment : List (ℕ × ℕ) → List Bool
  | [] => []
  | (source, target) :: rest =>
      pair (pair source.bits target.bits) (encodeNameEnvironment rest)

@[simp] theorem encodeNameEnvironment_nil : encodeNameEnvironment [] = [] := rfl

@[simp] theorem pairSnd_encodeNameEnvironment_cons (source target : ℕ)
    (rest : List (ℕ × ℕ)) :
    pairSnd (encodeNameEnvironment ((source, target) :: rest)) = encodeNameEnvironment rest := by
  simp [encodeNameEnvironment]

theorem encodeNameEnvironment_length_ge (entries : List (ℕ × ℕ)) :
    entries.length ≤ (encodeNameEnvironment entries).length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨source, target⟩
    simp only [encodeNameEnvironment, pair_length, List.length_cons]
    omega

/-- Raw lookup is total, but its exact environment semantics use canonical
internal chains. A missing key returns the canonical original query. -/
def nameEnvironmentLookupBitsWithFuel (fuel : ℕ) (query bits : List Bool) : List Bool :=
  let index := assignmentFindIndex fuel query bits
  if index < fuel then pairSnd (assignmentChainEntry index bits) else normalizeNameBits query

def nameEnvironmentLookupBits (query bits : List Bool) : List Bool :=
  nameEnvironmentLookupBitsWithFuel bits.length query bits

theorem nameEnvironmentLookupBitsWithFuel_mem_FP {fuel : List Bool → ℕ}
    {query bits : List Bool → List Bool} (hf : UnaryFn fuel) (hq : query ∈ FP) (hb : bits ∈ FP) :
    (fun z => nameEnvironmentLookupBitsWithFuel (fuel z) (query z) (bits z)) ∈ FP := by
  have hi := assignmentFindIndex_unaryFn hf hq hb
  exact (FPPred.lt hi hf).ite_mem_FP
    (mem_FP_comp (assignmentChainEntry_mem_FP hi hb) pairSnd_mem_FP)
    (normalizeNameBits_mem_FP hq)

theorem nameEnvironmentLookupBits_mem_FP {query bits : List Bool → List Bool}
    (hq : query ∈ FP) (hb : bits ∈ FP) :
    (fun z => nameEnvironmentLookupBits (query z) (bits z)) ∈ FP :=
  nameEnvironmentLookupBitsWithFuel_mem_FP (UnaryFn.length hb) hq hb

theorem nameEnvironmentLookupBitsWithFuel_encode (entries : List (ℕ × ℕ))
    (query fuel : ℕ) (hfuel : entries.length ≤ fuel) :
    nameEnvironmentLookupBitsWithFuel fuel query.bits (encodeNameEnvironment entries) =
      (scopedNameLookup entries query).bits := by
  induction entries generalizing fuel with
  | nil => simp [nameEnvironmentLookupBitsWithFuel, scopedNameLookup]
  | cons entry entries ih =>
    rcases entry with ⟨source, target⟩
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hf : entries.length ≤ fuel := Nat.le_of_succ_le_succ hfuel
      by_cases h : query = source
      · simp [nameEnvironmentLookupBitsWithFuel, encodeNameEnvironment,
          assignmentFindIndex_succ_pair, scopedNameLookup, h]
      · simpa [nameEnvironmentLookupBitsWithFuel, encodeNameEnvironment,
          assignmentFindIndex_succ_pair, scopedNameLookup, h] using ih fuel hf

@[simp] theorem nameEnvironmentLookupBits_encode (entries : List (ℕ × ℕ)) (query : ℕ) :
    nameEnvironmentLookupBits query.bits (encodeNameEnvironment entries) =
      (scopedNameLookup entries query).bits :=
  nameEnvironmentLookupBitsWithFuel_encode entries query _ (encodeNameEnvironment_length_ge entries)

/-- One binder push and its exact binary targets have actual runtime certificates. -/
theorem encodeNameEnvironment_cons_mem_FP {entries : List Bool → List (ℕ × ℕ)}
    {source target : List Bool → ℕ}
    (he : (fun z => encodeNameEnvironment (entries z)) ∈ FP)
    (hs : (fun z => (source z).bits) ∈ FP) (ht : (fun z => (target z).bits) ∈ FP) :
    (fun z => encodeNameEnvironment ((source z, target z) :: entries z)) ∈ FP :=
  mem_FP_pair (mem_FP_pair hs ht) he

theorem scopedNameLookup_bits_mem_FP {entries : List Bool → List (ℕ × ℕ)}
    {query : List Bool → ℕ} (he : (fun z => encodeNameEnvironment (entries z)) ∈ FP)
    (hq : (fun z => (query z).bits) ∈ FP) :
    (fun z => (scopedNameLookup (entries z) (query z)).bits) ∈ FP :=
  mem_FP_of_eq (nameEnvironmentLookupBits_mem_FP hq he)
    (fun z => nameEnvironmentLookupBits_encode (entries z) (query z))

/-- The local binary map required by the syntax-renaming certificate. -/
theorem scopedNameLookup_map_mem_FP {entries : List Bool → List (ℕ × ℕ)}
    (he : (fun z => encodeNameEnvironment (entries z)) ∈ FP) :
    (fun w => (scopedNameLookup (entries (pairFst w)) (nameBitsValue (pairSnd w))).bits) ∈ FP :=
  scopedNameLookup_bits_mem_FP (mem_FP_comp pairFst_mem_FP he)
    (nameBitsValue_bits_mem_FP pairSnd_mem_FP)

/-- Apply the current environment uniformly. On a quantifier-free matrix this
is precisely its free-name action; new binders must still push their own scope. -/
theorem encode_renameQBF_environment_mem_FP {entries : List Bool → List (ℕ × ℕ)}
    {formula : List Bool → QBF} (he : (fun z => encodeNameEnvironment (entries z)) ∈ FP)
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) :
    (fun z => encodeQBF (renameQBF (scopedNameLookup (entries z)) (formula z))) ∈ FP :=
  encode_renameQBF_mem_FP hformula (scopedNameLookup_map_mem_FP he)

theorem assignmentChainDrop_encodeNameEnvironment (count : ℕ) (entries : List (ℕ × ℕ)) :
    assignmentChainDrop count (encodeNameEnvironment entries) =
      encodeNameEnvironment (entries.drop count) := by
  induction count generalizing entries with
  | zero => rfl
  | succ count ih =>
    cases entries with
    | nil => simp
    | cons entry entries =>
      rcases entry with ⟨source, target⟩
      simpa only [encodeNameEnvironment, assignmentChainDrop_succ_pair, List.drop_succ_cons]
        using ih entries

/-- Leaving any bounded number of scopes restores the saved outer chain. -/
theorem encodeNameEnvironment_drop_mem_FP {entries : List Bool → List (ℕ × ℕ)}
    {count : List Bool → ℕ} (he : (fun z => encodeNameEnvironment (entries z)) ∈ FP)
    (hc : UnaryFn count) :
    (fun z => encodeNameEnvironment ((entries z).drop (count z))) ∈ FP :=
  mem_FP_of_eq (assignmentChainDrop_mem_FP hc he)
    (fun z => assignmentChainDrop_encodeNameEnvironment (count z) (entries z))

/-- Pushing a frame grows the state additively, never by re-encoding its tail. -/
theorem encodeNameEnvironment_cons_length (source target : ℕ) (entries : List (ℕ × ℕ)) :
    (encodeNameEnvironment ((source, target) :: entries)).length =
      (encodeNameEnvironment entries).length + 4 * source.bits.length + 2 * target.bits.length + 6 := by
  simp only [encodeNameEnvironment, pair_length]
  omega

theorem encodeNameEnvironment_length_le (entries : List (ℕ × ℕ)) (budget : ℕ)
    (h : ∀ entry ∈ entries, entry.1.bits.length ≤ budget ∧ entry.2.bits.length ≤ budget) :
    (encodeNameEnvironment entries).length ≤ entries.length * (6 * budget + 6) := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    obtain ⟨hs, ht⟩ := h entry (by simp)
    have hr := ih (fun other ho => h other (List.mem_cons_of_mem entry ho))
    rcases entry with ⟨source, target⟩
    rw [encodeNameEnvironment_cons_length, List.length_cons, Nat.succ_mul]
    dsimp only at hs ht
    nlinarith

/-- Any active stack using source keys and the converter's actual fresh-name
range has quadratic size in the original binary input, even with huge names. -/
theorem encodeNameEnvironment_prenex_length_le (formula : QBF) (entries : List (ℕ × ℕ))
    (hcount : entries.length ≤ nodeCount formula)
    (hentries : ∀ entry ∈ entries, entry.1 ∈ qbfNames formula ∧
      entry.2 ≤ qbfMaxVar formula + (nodeCount formula + 1)) :
    (encodeNameEnvironment entries).length ≤
      (encodeQBF formula).length * (12 * (encodeQBF formula).length + 18) := by
  have hnode := nodeCount_le_length_encodeQBF formula
  have hmax := qbfMaxVar_size_le_encoding formula
  have hadd := nat_size_add_le (qbfMaxVar formula) (nodeCount formula + 1)
  have hoffset := nat_size_le_self (nodeCount formula + 1)
  have hfresh : (qbfMaxVar formula + (nodeCount formula + 1)).size ≤
      2 * (encodeQBF formula).length + 2 := by omega
  have hbound := encodeNameEnvironment_length_le entries (2 * (encodeQBF formula).length + 2)
    (fun entry he => by
      obtain ⟨hkey, hvalue⟩ := hentries entry he
      have hs := Nat.size_le_size (le_qbfMaxVar_of_mem formula entry.1 hkey)
      have ht := (Nat.size_le_size hvalue).trans hfresh
      simpa only [Nat.size_eq_bits_len] using
        (show entry.1.size ≤ 2 * (encodeQBF formula).length + 2 ∧
          entry.2.size ≤ 2 * (encodeQBF formula).length + 2 from ⟨by omega, ht⟩))
  calc
    _ ≤ entries.length * (6 * (2 * (encodeQBF formula).length + 2) + 6) := hbound
    _ ≤ (encodeQBF formula).length * (6 * (2 * (encodeQBF formula).length + 2) + 6) :=
      Nat.mul_le_mul_right _ (hcount.trans hnode)
    _ = _ := by ring

/-- Proof-free computational fields of the exact prenex converter. -/
structure ScopedPrenexData where
  «prefix» : List Quantifier
  matrix : QBF
  next : ℕ

def ScopedPrenexData.ofResult {formula : QBF} {env : ℕ → ℕ} {start : ℕ}
    (result : PrenexResult formula env start) : ScopedPrenexData :=
  ⟨result.formula.quantifiers, result.formula.matrix, result.next⟩

def ScopedPrenexData.neg (result : ScopedPrenexData) : ScopedPrenexData :=
  ⟨result.prefix.map Quantifier.dual, .neg result.matrix, result.next⟩

def ScopedPrenexData.binary (op : QBFConnective) (left right : ScopedPrenexData) : ScopedPrenexData :=
  ⟨left.prefix ++ right.prefix, op.formula left.matrix right.matrix, right.next⟩

def ScopedPrenexData.quantify (q : Quantifier) (start : ℕ) (child : ScopedPrenexData) :
    ScopedPrenexData :=
  ⟨q.withIndex start :: child.prefix, child.matrix, child.next⟩

/-- This executable recurrence restores the original environment for a binary
sibling, while passing the globally advanced counter from its left sibling. -/
def scopedPrenexAux : QBF → List (ℕ × ℕ) → ℕ → ScopedPrenexData
  | .var i, entries, start => ⟨[], .var (scopedNameLookup entries i), start⟩
  | .tru, _, start => ⟨[], .tru, start⟩
  | .fls, _, start => ⟨[], .fls, start⟩
  | .neg body, entries, start => (scopedPrenexAux body entries start).neg
  | .conj left right, entries, start =>
      let first := scopedPrenexAux left entries start
      first.binary .conj (scopedPrenexAux right entries first.next)
  | .disj left right, entries, start =>
      let first := scopedPrenexAux left entries start
      first.binary .disj (scopedPrenexAux right entries first.next)
  | .ex name body, entries, start =>
      (scopedPrenexAux body ((name, start) :: entries) (start + 1)).quantify (.ex name) start
  | .all name body, entries, start =>
      (scopedPrenexAux body ((name, start) :: entries) (start + 1)).quantify (.all name) start

theorem ScopedPrenexData.ofResult_env_congr (formula : QBF) (env other : ℕ → ℕ)
    (start : ℕ) (he : env = other)
    (h : ∀ i ∈ qbfNames formula, env i < start)
    (ho : ∀ i ∈ qbfNames formula, other i < start) :
    ScopedPrenexData.ofResult (prenexAux formula env start h) =
      ScopedPrenexData.ofResult (prenexAux formula other start ho) := by
  subst other
  rfl

/-- The finite environment recurrence has exactly the existing converter's
prefix, matrix, and counter. This is a functional refinement, not a runtime claim. -/
theorem scopedPrenexAux_eq (formula : QBF) (entries : List (ℕ × ℕ)) (start : ℕ)
    (h : ∀ i ∈ qbfNames formula, scopedNameLookup entries i < start) :
    scopedPrenexAux formula entries start =
      ScopedPrenexData.ofResult (prenexAux formula (scopedNameLookup entries) start h) := by
  induction formula generalizing entries start with
  | var name | tru | fls => rfl
  | neg body ih =>
    simpa only [scopedPrenexAux, ScopedPrenexData.neg, prenexAux,
      ScopedPrenexData.ofResult, PrenexResult.neg] using
      congrArg ScopedPrenexData.neg (ih entries start h)
  | conj left right ihleft ihright =>
    have hl : ∀ i ∈ qbfNames left, scopedNameLookup entries i < start :=
      fun i hi => h i (Finset.mem_union_left _ hi)
    have hr : ∀ i ∈ qbfNames right, scopedNameLookup entries i < start :=
      fun i hi => h i (Finset.mem_union_right _ hi)
    let first := prenexAux left (scopedNameLookup entries) start hl
    have hr' : ∀ i ∈ qbfNames right, scopedNameLookup entries i < first.next :=
      fun i hi => (hr i hi).trans_le first.next_ge
    have heleft := ihleft entries start hl
    have heright := ihright entries first.next hr'
    simp only [scopedPrenexAux, heleft, ScopedPrenexData.ofResult] at ⊢
    rw [show (prenexAux left (scopedNameLookup entries) start hl).next = first.next from rfl,
      heright]
    rfl
  | disj left right ihleft ihright =>
    have hl : ∀ i ∈ qbfNames left, scopedNameLookup entries i < start :=
      fun i hi => h i (Finset.mem_union_left _ hi)
    have hr : ∀ i ∈ qbfNames right, scopedNameLookup entries i < start :=
      fun i hi => h i (Finset.mem_union_right _ hi)
    let first := prenexAux left (scopedNameLookup entries) start hl
    have hr' : ∀ i ∈ qbfNames right, scopedNameLookup entries i < first.next :=
      fun i hi => (hr i hi).trans_le first.next_ge
    have heleft := ihleft entries start hl
    have heright := ihright entries first.next hr'
    simp only [scopedPrenexAux, heleft, ScopedPrenexData.ofResult] at ⊢
    rw [show (prenexAux left (scopedNameLookup entries) start hl).next = first.next from rfl,
      heright]
    rfl
  | ex name body ih =>
    have hb : ∀ i ∈ qbfNames body,
        scopedNameLookup ((name, start) :: entries) i < start + 1 := by
      intro i hi
      have hi' := h i (Finset.mem_insert_of_mem hi)
      by_cases he : i = name
      · simp [scopedNameLookup, he]
      · simpa [scopedNameLookup, he] using hi'.trans (Nat.lt_succ_self start)
    have he := ih ((name, start) :: entries) (start + 1) hb
    rw [scopedPrenexAux, he]
    have hb' : ∀ i ∈ qbfNames body,
        Function.update (scopedNameLookup entries) name start i < start + 1 := by
      rw [← scopedNameLookup_cons]
      exact hb
    rw [ScopedPrenexData.ofResult_env_congr body _ _ _
      (scopedNameLookup_cons name start entries) hb hb']
    rfl
  | all name body ih =>
    have hb : ∀ i ∈ qbfNames body,
        scopedNameLookup ((name, start) :: entries) i < start + 1 := by
      intro i hi
      have hi' := h i (Finset.mem_insert_of_mem hi)
      by_cases he : i = name
      · simp [scopedNameLookup, he]
      · simpa [scopedNameLookup, he] using hi'.trans (Nat.lt_succ_self start)
    have he := ih ((name, start) :: entries) (start + 1) hb
    rw [scopedPrenexAux, he]
    have hb' : ∀ i ∈ qbfNames body,
        Function.update (scopedNameLookup entries) name start i < start + 1 := by
      rw [← scopedNameLookup_cons]
      exact hb
    rw [ScopedPrenexData.ofResult_env_congr body _ _ _
      (scopedNameLookup_cons name start entries) hb hb']
    rfl

/-- Initializing the finite environment with no bindings reproduces the exact
existing prenex output; free names use the identity default. -/
theorem scopedPrenexAux_toPrenex (formula : QBF) :
    (scopedPrenexAux formula [] (qbfMaxVar formula + 1)).prefix = (toPrenex formula).quantifiers ∧
    (scopedPrenexAux formula [] (qbfMaxVar formula + 1)).matrix = (toPrenex formula).matrix := by
  rw [scopedPrenexAux_eq formula [] (qbfMaxVar formula + 1)
    (fun i hi => Nat.lt_succ_of_le (le_qbfMaxVar_of_mem formula i hi))]
  exact ⟨rfl, rfl⟩

end IPPSPACE

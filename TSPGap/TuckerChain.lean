/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerForbidden

/-!
# Indexed chains in a set family

The case analysis of Tucker's Theorem 7 (`TSPGap/TuckerForbidden.lean`) manipulates the
three avoiding paths of a minimal asteroidal triple by their positions: the `i`-th element,
the `i`-th set, the segment between two positions, the path with one vertex replaced.  This
file provides the representation used for that: a *chain* in the family `(O, F)` is a
length `n` together with elements `q 0, …, q n` of `O` and sets `r 1, …, r n` of `F` with
`q (i-1), q i ∈ r i`; the incidence-graph walk `q 0 – r 1 – q 1 – ⋯ – r n – q n`.

* `Chain O F`, with the surgery operations `reverse`, `append`, `take`, `drop`, `cons`,
  `snoc`, `mono`, `restrict`;
* chains realize `Reach` (`Chain.reach`, `Chain.ofReach`), hence `AvoidChain` through
  `avoidSets`;
* `IsShortest`: a chain of minimal length between its endpoints; a shortest chain is
  *induced* (`IsInduced`: injective elements, injective sets, and exactly the consecutive
  incidences), by splicing;
* the cycle configuration `MI`: an induced chain closed up by one more set
  (`hasConfig_MI_of_gap`), and the two *apex* lemmas (`apex_set`, `apex_elem`): a vertex
  with exactly two neighbours in a connected sub-instance either closes a chordless cycle
  of length at least six (an `MI` configuration) or its two neighbours have a common
  neighbour there.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*}

/-! ### Chains -/

/-- A chain in `(O, F)`: elements `q 0, …, q n` of `O` and sets `r 1, …, r n` of `F` with
`q (i-1), q i ∈ r i`.  Values of `q` beyond `n` and of `r` outside `[1, n]` are junk. -/
structure Chain (O : Finset α) (F : Finset (Finset α)) where
  /-- The number of steps. -/
  n : ℕ
  /-- The elements. -/
  q : ℕ → α
  /-- The sets, indexed from `1`. -/
  r : ℕ → Finset α
  q_mem : ∀ i, i ≤ n → q i ∈ O
  r_mem : ∀ i, 1 ≤ i → i ≤ n → r i ∈ F
  left_mem : ∀ i, i < n → q i ∈ r (i + 1)
  right_mem : ∀ i, i < n → q (i + 1) ∈ r (i + 1)

namespace Chain

variable {O O' : Finset α} {F F' : Finset (Finset α)}

/-- The trivial chain at `a`. -/
def single (a : α) (ha : a ∈ O) : Chain O F where
  n := 0
  q := fun _ => a
  r := fun _ => ∅
  q_mem := fun _ _ => ha
  r_mem := fun i h1 h0 => absurd (h1.trans h0) (by omega)
  left_mem := fun _ h => absurd h (Nat.not_lt_zero _)
  right_mem := fun _ h => absurd h (Nat.not_lt_zero _)

/-- A chain of a sub-instance is a chain of the instance. -/
def mono (C : Chain O F) (hO : O ⊆ O') (hF : F ⊆ F') : Chain O' F' where
  n := C.n
  q := C.q
  r := C.r
  q_mem := fun i hi => hO (C.q_mem i hi)
  r_mem := fun i h1 hn => hF (C.r_mem i h1 hn)
  left_mem := C.left_mem
  right_mem := C.right_mem

@[simp] theorem mono_n (C : Chain O F) (hO : O ⊆ O') (hF : F ⊆ F') : (C.mono hO hF).n = C.n := rfl
@[simp] theorem mono_q (C : Chain O F) (hO : O ⊆ O') (hF : F ⊆ F') : (C.mono hO hF).q = C.q := rfl
@[simp] theorem mono_r (C : Chain O F) (hO : O ⊆ O') (hF : F ⊆ F') : (C.mono hO hF).r = C.r := rfl

/-- A chain whose vertices lie in a sub-instance is a chain of that sub-instance. -/
def restrict (C : Chain O F) (hO : ∀ i, i ≤ C.n → C.q i ∈ O')
    (hF : ∀ i, 1 ≤ i → i ≤ C.n → C.r i ∈ F') : Chain O' F' where
  n := C.n
  q := C.q
  r := C.r
  q_mem := hO
  r_mem := hF
  left_mem := C.left_mem
  right_mem := C.right_mem

@[simp] theorem restrict_n (C : Chain O F) (hO : ∀ i, i ≤ C.n → C.q i ∈ O')
    (hF : ∀ i, 1 ≤ i → i ≤ C.n → C.r i ∈ F') : (C.restrict hO hF).n = C.n := rfl
@[simp] theorem restrict_q (C : Chain O F) (hO : ∀ i, i ≤ C.n → C.q i ∈ O')
    (hF : ∀ i, 1 ≤ i → i ≤ C.n → C.r i ∈ F') : (C.restrict hO hF).q = C.q := rfl
@[simp] theorem restrict_r (C : Chain O F) (hO : ∀ i, i ≤ C.n → C.q i ∈ O')
    (hF : ∀ i, 1 ≤ i → i ≤ C.n → C.r i ∈ F') : (C.restrict hO hF).r = C.r := rfl

/-- The reversed chain: `q' i = q (n - i)`, `r' i = r (n + 1 - i)`. -/
def reverse (C : Chain O F) : Chain O F where
  n := C.n
  q := fun i => C.q (C.n - i)
  r := fun i => C.r (C.n + 1 - i)
  q_mem := fun i _ => C.q_mem _ (Nat.sub_le _ _)
  r_mem := fun i h1 hn => C.r_mem _ (by omega) (by omega)
  left_mem := fun i hi => by
    have := C.right_mem (C.n - i - 1) (by omega)
    rw [show C.n - i - 1 + 1 = C.n - i by omega] at this
    rw [show C.n + 1 - (i + 1) = C.n - i by omega]
    exact this
  right_mem := fun i hi => by
    have := C.left_mem (C.n - i - 1) (by omega)
    rw [show C.n - i - 1 + 1 = C.n - i by omega] at this
    rw [show C.n - (i + 1) = C.n - i - 1 by omega, show C.n + 1 - (i + 1) = C.n - i by omega]
    exact this

@[simp] theorem reverse_n (C : Chain O F) : C.reverse.n = C.n := rfl
@[simp] theorem reverse_q (C : Chain O F) (i : ℕ) : C.reverse.q i = C.q (C.n - i) := rfl
@[simp] theorem reverse_r (C : Chain O F) (i : ℕ) : C.reverse.r i = C.r (C.n + 1 - i) := rfl

/-- Concatenation of two chains meeting at an element. -/
def append (C D : Chain O F) (h : C.q C.n = D.q 0) : Chain O F where
  n := C.n + D.n
  q := fun i => if i ≤ C.n then C.q i else D.q (i - C.n)
  r := fun i => if i ≤ C.n then C.r i else D.r (i - C.n)
  q_mem := fun i hi => by
    split_ifs with h'
    · exact C.q_mem i h'
    · exact D.q_mem _ (by omega)
  r_mem := fun i h1 hi => by
    split_ifs with h'
    · exact C.r_mem i h1 h'
    · exact D.r_mem _ (by omega) (by omega)
  left_mem := fun i hi => by
    by_cases h1 : i < C.n
    · simp only [show i ≤ C.n by omega, show i + 1 ≤ C.n by omega, if_true]
      exact C.left_mem i h1
    · by_cases h2 : i = C.n
      · subst h2
        simp only [le_refl, if_true, show ¬ (C.n + 1 ≤ C.n) by omega, if_false,
          Nat.add_sub_cancel_left, h]
        exact D.left_mem 0 (by omega)
      · simp only [show ¬ (i ≤ C.n) by omega, show ¬ (i + 1 ≤ C.n) by omega, if_false]
        rw [show i + 1 - C.n = (i - C.n) + 1 by omega]
        exact D.left_mem _ (by omega)
  right_mem := fun i hi => by
    by_cases h1 : i + 1 ≤ C.n
    · simp only [h1, if_true]
      exact C.right_mem i (by omega)
    · simp only [h1, if_false]
      rw [show i + 1 - C.n = (i - C.n) + 1 by omega]
      exact D.right_mem _ (by omega)

@[simp] theorem append_n (C D : Chain O F) (h : C.q C.n = D.q 0) : (C.append D h).n = C.n + D.n :=
  rfl
theorem append_q (C D : Chain O F) (h : C.q C.n = D.q 0) (i : ℕ) :
    (C.append D h).q i = if i ≤ C.n then C.q i else D.q (i - C.n) := rfl
theorem append_r (C D : Chain O F) (h : C.q C.n = D.q 0) (i : ℕ) :
    (C.append D h).r i = if i ≤ C.n then C.r i else D.r (i - C.n) := rfl

/-- The first `k` steps. -/
def take (C : Chain O F) (k : ℕ) : Chain O F where
  n := min k C.n
  q := C.q
  r := C.r
  q_mem := fun i hi => C.q_mem i (by omega)
  r_mem := fun i h1 hi => C.r_mem i h1 (by omega)
  left_mem := fun i hi => C.left_mem i (by omega)
  right_mem := fun i hi => C.right_mem i (by omega)

@[simp] theorem take_n (C : Chain O F) (k : ℕ) : (C.take k).n = min k C.n := rfl
@[simp] theorem take_q (C : Chain O F) (k : ℕ) : (C.take k).q = C.q := rfl
@[simp] theorem take_r (C : Chain O F) (k : ℕ) : (C.take k).r = C.r := rfl

/-- The chain after the first `k` steps (`k ≤ n`). -/
def drop (C : Chain O F) (k : ℕ) (hk : k ≤ C.n) : Chain O F where
  n := C.n - k
  q := fun i => C.q (k + i)
  r := fun i => C.r (k + i)
  q_mem := fun i hi => C.q_mem (k + i) (by omega)
  r_mem := fun i h1 hi => C.r_mem (k + i) (by omega) (by omega)
  left_mem := fun i hi => by
    rw [show k + (i + 1) = (k + i) + 1 by omega]; exact C.left_mem (k + i) (by omega)
  right_mem := fun i hi => by
    rw [show k + (i + 1) = (k + i) + 1 by omega]; exact C.right_mem (k + i) (by omega)

@[simp] theorem drop_n (C : Chain O F) (k : ℕ) (hk : k ≤ C.n) : (C.drop k hk).n = C.n - k := rfl
@[simp] theorem drop_q (C : Chain O F) (k : ℕ) (hk : k ≤ C.n) (i : ℕ) :
    (C.drop k hk).q i = C.q (k + i) := rfl
@[simp] theorem drop_r (C : Chain O F) (k : ℕ) (hk : k ≤ C.n) (i : ℕ) :
    (C.drop k hk).r i = C.r (k + i) := rfl

/-- Prepend the step `a – S – q 0`. -/
def cons (a : α) (S : Finset α) (C : Chain O F) (ha : a ∈ O) (hS : S ∈ F) (haS : a ∈ S)
    (h0 : C.q 0 ∈ S) : Chain O F where
  n := C.n + 1
  q := fun i => if i = 0 then a else C.q (i - 1)
  r := fun i => if i ≤ 1 then S else C.r (i - 1)
  q_mem := fun i hi => by
    split_ifs with h
    · exact ha
    · exact C.q_mem _ (by omega)
  r_mem := fun i h1 hi => by
    split_ifs with h
    · exact hS
    · exact C.r_mem _ (by omega) (by omega)
  left_mem := fun i hi => by
    by_cases h : i = 0
    · subst h; simp only [if_true, zero_add, le_refl]; exact haS
    · simp only [h, if_false, show ¬ (i + 1 ≤ 1) by omega]
      rw [show i + 1 - 1 = (i - 1) + 1 by omega]
      exact C.left_mem _ (by omega)
  right_mem := fun i hi => by
    by_cases h : i = 0
    · subst h; simp only [zero_add, one_ne_zero, if_false, le_refl, if_true, Nat.sub_self]
      exact h0
    · simp only [show i + 1 ≠ 0 by omega, if_false, show ¬ (i + 1 ≤ 1) by omega]
      rw [show i + 1 - 1 = (i - 1) + 1 by omega]
      exact C.right_mem _ (by omega)

@[simp] theorem cons_n (a : α) (S : Finset α) (C : Chain O F) (ha : a ∈ O) (hS : S ∈ F)
    (haS : a ∈ S) (h0 : C.q 0 ∈ S) : (C.cons a S ha hS haS h0).n = C.n + 1 := rfl
theorem cons_q (a : α) (S : Finset α) (C : Chain O F) (ha : a ∈ O) (hS : S ∈ F)
    (haS : a ∈ S) (h0 : C.q 0 ∈ S) (i : ℕ) :
    (C.cons a S ha hS haS h0).q i = if i = 0 then a else C.q (i - 1) := rfl
theorem cons_r (a : α) (S : Finset α) (C : Chain O F) (ha : a ∈ O) (hS : S ∈ F)
    (haS : a ∈ S) (h0 : C.q 0 ∈ S) (i : ℕ) :
    (C.cons a S ha hS haS h0).r i = if i ≤ 1 then S else C.r (i - 1) := rfl

/-- Append the step `q n – S – b`. -/
def snoc (C : Chain O F) (S : Finset α) (b : α) (hb : b ∈ O) (hS : S ∈ F) (hn : C.q C.n ∈ S)
    (hbS : b ∈ S) : Chain O F where
  n := C.n + 1
  q := fun i => if i ≤ C.n then C.q i else b
  r := fun i => if i ≤ C.n then C.r i else S
  q_mem := fun i hi => by
    split_ifs with h
    · exact C.q_mem i h
    · exact hb
  r_mem := fun i h1 hi => by
    split_ifs with h
    · exact C.r_mem i h1 h
    · exact hS
  left_mem := fun i hi => by
    by_cases h : i < C.n
    · simp only [show i ≤ C.n by omega, show i + 1 ≤ C.n by omega, if_true]
      exact C.left_mem i h
    · have : i = C.n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ (C.n + 1 ≤ C.n) by omega, if_false]
      exact hn
  right_mem := fun i hi => by
    by_cases h : i + 1 ≤ C.n
    · simp only [h, if_true]
      exact C.right_mem i (by omega)
    · simp only [h, if_false]
      exact hbS

@[simp] theorem snoc_n (C : Chain O F) (S : Finset α) (b : α) (hb : b ∈ O) (hS : S ∈ F)
    (hn : C.q C.n ∈ S) (hbS : b ∈ S) : (C.snoc S b hb hS hn hbS).n = C.n + 1 := rfl
theorem snoc_q (C : Chain O F) (S : Finset α) (b : α) (hb : b ∈ O) (hS : S ∈ F)
    (hn : C.q C.n ∈ S) (hbS : b ∈ S) (i : ℕ) :
    (C.snoc S b hb hS hn hbS).q i = if i ≤ C.n then C.q i else b := rfl
theorem snoc_r (C : Chain O F) (S : Finset α) (b : α) (hb : b ∈ O) (hS : S ∈ F)
    (hn : C.q C.n ∈ S) (hbS : b ∈ S) (i : ℕ) :
    (C.snoc S b hb hS hn hbS).r i = if i ≤ C.n then C.r i else S := rfl

/-! ### Chains and reachability -/

/-- Along a chain, `q j` reaches `q k` in `(O', F')` as soon as the segment lies there. -/
theorem reach_segment (C : Chain O F) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ C.n)
    (hO' : ∀ i, j ≤ i → i ≤ k → C.q i ∈ O') (hF' : ∀ i, j < i → i ≤ k → C.r i ∈ F') :
    Reach O' F' (C.q j) (C.q k) := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · subst h; exact Relation.ReflTransGen.refl
    · refine (ih (by omega) (by omega) (fun i h1 h2 => hO' i h1 (by omega))
        (fun i h1 h2 => hF' i h1 (by omega))).tail ?_
      exact ⟨hO' k (by omega) (by omega), hO' (k + 1) (by omega) le_rfl, C.r (k + 1),
        hF' (k + 1) (by omega) le_rfl, C.left_mem k (by omega), C.right_mem k (by omega)⟩

theorem reach (C : Chain O F) : Reach O F (C.q 0) (C.q C.n) :=
  C.reach_segment (Nat.zero_le _) le_rfl (fun i _ hi => C.q_mem i hi)
    (fun i h1 hi => C.r_mem i (by omega) hi)

/-- Reachability is realized by a chain. -/
theorem ofReach {a b : α} (h : Reach O F a b) (ha : a ∈ O) :
    ∃ C : Chain O F, C.q 0 = a ∧ C.q C.n = b := by
  induction h with
  | refl => exact ⟨single a ha, rfl, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨C, h0, hn⟩ := ih
    obtain ⟨_, hc, S, hS, hbS, hcS⟩ := hbc
    exact ⟨C.snoc S _ hc hS (hn ▸ hbS) hcS, by simp [snoc_q, h0], by simp [snoc_q]⟩

theorem avoidChain_iff [DecidableEq α] {a x z : α} (hx : x ∈ O) :
    AvoidChain O F a x z ↔ ∃ C : Chain O (avoidSets F a), C.q 0 = x ∧ C.q C.n = z := by
  have key : ∀ u v, AvoidStep O F a u v ↔ ShareStep O (avoidSets F a) u v := by
    intro u v
    simp only [AvoidStep, ShareStep, mem_avoidSets]
    constructor
    · rintro ⟨hu, hv, S, hS, haS, huS, hvS⟩; exact ⟨hu, hv, S, ⟨hS, haS⟩, huS, hvS⟩
    · rintro ⟨hu, hv, S, ⟨hS, haS⟩, huS, hvS⟩; exact ⟨hu, hv, S, hS, haS, huS, hvS⟩
  have hiff : AvoidChain O F a x z ↔ Reach O (avoidSets F a) x z := by
    constructor
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail ((key _ _).mp hbc)
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail ((key _ _).mpr hbc)
  rw [hiff]
  constructor
  · intro h; exact ofReach h hx
  · rintro ⟨C, h0, hn⟩; rw [← h0, ← hn]; exact C.reach

/-! ### Shortest chains are induced -/

/-- A chain of minimal length between its endpoints. -/
def IsShortest (C : Chain O F) : Prop :=
  ∀ D : Chain O F, D.q 0 = C.q 0 → D.q D.n = C.q C.n → C.n ≤ D.n

/-- An *induced* chain: injective elements, injective sets, and exactly the consecutive
incidences `q i ∈ r i`, `q i ∈ r (i+1)`. -/
structure IsInduced (C : Chain O F) : Prop where
  q_inj : ∀ i j, i ≤ C.n → j ≤ C.n → C.q i = C.q j → i = j
  r_inj : ∀ i j, 1 ≤ i → i ≤ C.n → 1 ≤ j → j ≤ C.n → C.r i = C.r j → i = j
  incid : ∀ i j, i ≤ C.n → 1 ≤ j → j ≤ C.n → (C.q i ∈ C.r j ↔ j = i ∨ j = i + 1)

theorem exists_shortest {a b : α} (h : ∃ C : Chain O F, C.q 0 = a ∧ C.q C.n = b) :
    ∃ C : Chain O F, C.q 0 = a ∧ C.q C.n = b ∧ C.IsShortest := by
  classical
  have hex : ∃ n, ∃ C : Chain O F, C.q 0 = a ∧ C.q C.n = b ∧ C.n = n :=
    let ⟨C, h0, hn⟩ := h; ⟨C.n, C, h0, hn, rfl⟩
  obtain ⟨C, h0, hn, hCn⟩ := Nat.find_spec hex
  refine ⟨C, h0, hn, fun D hD0 hDn => ?_⟩
  rw [hCn]
  exact Nat.find_min' hex ⟨D, hD0.trans h0, hDn.trans hn, rfl⟩

theorem IsShortest.q_inj {C : Chain O F} (hC : C.IsShortest) {i j : ℕ} (hi : i ≤ C.n)
    (hj : j ≤ C.n) (h : C.q i = C.q j) : i = j := by
  by_contra hne
  wlog hij : i < j generalizing i j
  · exact this hj hi h.symm (Ne.symm hne) (by omega)
  -- splice out the segment between the two equal elements
  have hD : (C.take i).q (C.take i).n = (C.drop j hj).q 0 := by
    simp only [take_q, take_n, drop_q, add_zero]
    rw [min_eq_left hi]; exact h
  have := hC ((C.take i).append (C.drop j hj) hD)
    (by simp [append_q]) (by
      simp only [append_q, append_n, take_n, drop_n, drop_q]
      rw [min_eq_left hi]
      split_ifs with h'
      · have : C.n - j = 0 := by omega
        rw [this, add_zero, take_q, h]; congr 1; omega
      · congr 1; omega)
  simp only [append_n, take_n, drop_n] at this
  rw [min_eq_left hi] at this
  omega

theorem IsShortest.r_inj {C : Chain O F} (hC : C.IsShortest) {i j : ℕ} (h1 : 1 ≤ i)
    (hi : i ≤ C.n) (h1' : 1 ≤ j) (hj : j ≤ C.n) (h : C.r i = C.r j) : i = j := by
  by_contra hne
  wlog hij : i < j generalizing i j
  · exact this h1' hj h1 hi h.symm (Ne.symm hne) (by omega)
  -- the chain `q 0 … q (i-1) – r i – q j … q n`
  have hn' : (C.take (i - 1)).n = i - 1 := by simp only [take_n]; omega
  have hmem : (C.take (i - 1)).q (C.take (i - 1)).n ∈ C.r i := by
    rw [hn', take_q]
    have := C.left_mem (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  have hj' : C.q j ∈ C.r i := by
    have := C.right_mem (j - 1) (by omega)
    rwa [show j - 1 + 1 = j by omega, ← h] at this
  set D := ((C.take (i - 1)).snoc (C.r i) (C.q j) (C.q_mem j hj) (C.r_mem i h1 hi) hmem hj')
  have hD : D.q D.n = (C.drop j hj).q 0 := by
    simp only [D, snoc_q, snoc_n, drop_q, add_zero, hn']
    simp only [show ¬ (i - 1 + 1 ≤ i - 1) by omega, if_false]
  have := hC (D.append (C.drop j hj) hD) (by
      simp only [append_q, D, snoc_q, snoc_n, hn', take_q]
      simp only [Nat.zero_le, if_true]) (by
      simp only [append_q, append_n, D, snoc_n, drop_n, drop_q, hn']
      split_ifs with h'
      · have : C.n - j = 0 := by omega
        simp only [snoc_q, hn', this, add_zero]
        rw [if_neg (by omega)]; congr 1; omega
      · congr 1; omega)
  simp only [append_n, D, snoc_n, drop_n, hn'] at this
  omega

theorem IsShortest.incid {C : Chain O F} (hC : C.IsShortest) {i j : ℕ} (hi : i ≤ C.n)
    (h1 : 1 ≤ j) (hj : j ≤ C.n) : C.q i ∈ C.r j ↔ j = i ∨ j = i + 1 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨hne1, hne2⟩ := not_or.mp hne
    rcases Nat.lt_or_gt_of_ne hne1 with hlt | hgt
    · -- `j < i`: the chain `q 0 … q (j-1) – r j – q i … q n`
      have hn' : (C.take (j - 1)).n = j - 1 := by simp only [take_n]; omega
      have hmem : (C.take (j - 1)).q (C.take (j - 1)).n ∈ C.r j := by
        rw [hn', take_q]
        have := C.left_mem (j - 1) (by omega)
        rwa [show j - 1 + 1 = j by omega] at this
      set D := ((C.take (j - 1)).snoc (C.r j) (C.q i) (C.q_mem i hi) (C.r_mem j h1 hj) hmem h)
      have hD : D.q D.n = (C.drop i hi).q 0 := by
        simp only [D, snoc_q, snoc_n, drop_q, add_zero, hn']
        simp only [show ¬ (j - 1 + 1 ≤ j - 1) by omega, if_false]
      have := hC (D.append (C.drop i hi) hD) (by
          simp only [append_q, D, snoc_q, snoc_n, hn', take_q]
          simp only [Nat.zero_le, if_true]) (by
          simp only [append_q, append_n, D, snoc_n, drop_n, drop_q, hn']
          split_ifs with h'
          · have : C.n - i = 0 := by omega
            simp only [snoc_q, hn', this, add_zero]
            rw [if_neg (by omega)]; congr 1; omega
          · congr 1; omega)
      simp only [append_n, D, snoc_n, drop_n, hn'] at this
      omega
    · -- `j ≥ i + 2`: the chain `q 0 … q i – r j – q j … q n`
      have hij : i + 2 ≤ j := by omega
      have hn' : (C.take i).n = i := by simp only [take_n]; omega
      have hmem : (C.take i).q (C.take i).n ∈ C.r j := by rw [hn', take_q]; exact h
      have hjj : C.q j ∈ C.r j := by
        have := C.right_mem (j - 1) (by omega)
        rwa [show j - 1 + 1 = j by omega] at this
      set D := ((C.take i).snoc (C.r j) (C.q j) (C.q_mem j hj) (C.r_mem j h1 hj) hmem hjj)
      have hD : D.q D.n = (C.drop j hj).q 0 := by
        simp only [D, snoc_q, snoc_n, drop_q, add_zero, hn']
        simp only [show ¬ (i + 1 ≤ i) by omega, if_false]
      have := hC (D.append (C.drop j hj) hD) (by
          simp only [append_q, D, snoc_q, snoc_n, hn', take_q]
          simp only [Nat.zero_le, if_true]) (by
          simp only [append_q, append_n, D, snoc_n, drop_n, drop_q, hn']
          split_ifs with h'
          · have : C.n - j = 0 := by omega
            simp only [snoc_q, hn', this, add_zero]
            rw [if_neg (by omega)]; congr 1; omega
          · congr 1; omega)
      simp only [append_n, D, snoc_n, drop_n, hn'] at this
      omega
  · rintro (h | h)
    · rw [h]
      have := C.right_mem (i - 1) (by omega)
      rwa [show i - 1 + 1 = i by omega] at this
    · rw [h]; exact C.left_mem i (by omega)

theorem IsShortest.isInduced {C : Chain O F} (hC : C.IsShortest) : C.IsInduced where
  q_inj := fun _ _ hi hj h => hC.q_inj hi hj h
  r_inj := fun _ _ h1 hi h1' hj h => hC.r_inj h1 hi h1' hj h
  incid := fun _ _ hi h1 hj => hC.incid hi h1 hj

/-- A chain between distinct endpoints has positive length. -/
theorem pos_of_ne {C : Chain O F} (h : C.q 0 ≠ C.q C.n) : 1 ≤ C.n := by
  by_contra h0
  exact h (by rw [show C.n = 0 by omega])

end Chain

/-! ### The cycle configuration `MI` -/

/-- A chordless cycle `q 0 – r 0 – q 1 – r 1 – ⋯ – q (k+2) – r (k+2) – q 0` (row `r i`
containing exactly `q i` and `q (i+1)`, indices mod `k + 3`) is an `MI k` configuration. -/
theorem hasConfig_MI_of_cycle {F : Finset (Finset α)} {k : ℕ} (q : ℕ → α) (r : ℕ → Finset α)
    (hq : ∀ i j, i ≤ k + 2 → j ≤ k + 2 → q i = q j → i = j)
    (hr : ∀ i j, i ≤ k + 2 → j ≤ k + 2 → r i = r j → i = j)
    (hF : ∀ i, i ≤ k + 2 → r i ∈ F)
    (hinc : ∀ i j, i ≤ k + 2 → j ≤ k + 2 → (q j ∈ r i ↔ j = i ∨ j = (i + 1) % (k + 3))) :
    HasConfig F (MI k) := by
  refine ⟨⟨fun i => r i.val, fun i j h => Fin.ext (hr _ _ (by omega) (by omega) h)⟩,
    ⟨fun j => q j.val, fun i j h => Fin.ext (hq _ _ (by omega) (by omega) h)⟩,
    fun i => hF _ (by omega), fun i j => ?_⟩
  simp only [Function.Embedding.coeFn_mk, MI, pairRow, Finset.mem_insert, Finset.mem_singleton]
  rw [hinc i.val j.val (by omega) (by omega), Fin.ext_iff, Fin.ext_iff, Fin.val_add]
  have h1 : ((1 : Fin (k + 3)) : ℕ) = 1 := Fin.val_one (k + 1)
  rw [h1]

/-- An induced chain of length `n ≥ 2` in `(O', F')`, closed up by a set `S ∈ F` containing
exactly its two endpoints, is an `MI (n - 2)` configuration of `F ⊇ F'`. -/
theorem hasConfig_MI_of_gap {O' : Finset α} {F F' : Finset (Finset α)} (hF' : F' ⊆ F)
    (C : Chain O' F') (hC : C.IsInduced) (h2 : 2 ≤ C.n) {S : Finset α} (hS : S ∈ F)
    (h0 : C.q 0 ∈ S) (hn : C.q C.n ∈ S) (hmid : ∀ i, 0 < i → i < C.n → C.q i ∉ S) :
    HasConfig F (MI (C.n - 2)) := by
  obtain ⟨k, hk⟩ : ∃ k, C.n = k + 2 := ⟨C.n - 2, by omega⟩
  rw [show C.n - 2 = k by omega]
  have hS_ne : ∀ i, i < k + 2 → C.r (i + 1) ≠ S := by
    intro i hi h
    have ha := (hC.incid 0 (i + 1) (by omega) (by omega) (by omega)).mp (h ▸ h0)
    have hb := (hC.incid C.n (i + 1) le_rfl (by omega) (by omega)).mp (h ▸ hn)
    omega
  apply hasConfig_MI_of_cycle C.q (fun i => if i < k + 2 then C.r (i + 1) else S)
  · intro i j hi hj h; exact hC.q_inj i j (by omega) (by omega) h
  · intro i j hi hj h
    split_ifs at h with h1 h2 h2
    · have := hC.r_inj (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) h; omega
    · exact absurd h (hS_ne i h1)
    · exact absurd h.symm (hS_ne j h2)
    · omega
  · intro i hi
    split_ifs with h1
    · exact hF' (C.r_mem _ (by omega) (by omega))
    · exact hS
  · intro i j hi hj
    split_ifs with h1
    · rw [hC.incid j (i + 1) (by omega) (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega : i + 1 < k + 3)]
      omega
    · have hi' : i = k + 2 := by omega
      subst hi'
      rw [show (k + 2 + 1) % (k + 3) = 0 from Nat.mod_self (k + 3)]
      constructor
      · intro hjS
        by_contra hne
        exact hmid j (by omega) (by omega) hjS
      · rintro (h | h)
        · rw [h, ← hk]; exact hn
        · rw [h]; exact h0

/-! ### The apex lemmas -/

/-- **Set apex.**  A set `w ∈ F` whose only elements in `O'` are `u ≠ v`, where `u` reaches
`v` in `(O', F')`: either an `MI` configuration of `F ⊇ F'`, or a set of `F'` containing both
`u` and `v`. -/
theorem apex_set {O' : Finset α} {F F' : Finset (Finset α)} (hF' : F' ⊆ F)
    {w : Finset α} (hw : w ∈ F) {u v : α} (huv : u ≠ v) (hu : u ∈ w) (hv : v ∈ w)
    (hnb : ∀ a ∈ O', a ∈ w → a = u ∨ a = v) (huO' : u ∈ O') (hreach : Reach O' F' u v) :
    (∃ k, HasConfig F (MI k)) ∨ ∃ T ∈ F', u ∈ T ∧ v ∈ T := by
  obtain ⟨C, h0, hn, hC⟩ := Chain.exists_shortest (Chain.ofReach hreach huO')
  have h1 : 1 ≤ C.n := Chain.pos_of_ne (by rw [h0, hn]; exact huv)
  rcases Nat.lt_or_ge C.n 2 with hlt | hge
  · right
    have hC1 : C.n = 1 := by omega
    refine ⟨C.r 1, C.r_mem 1 le_rfl (by omega), ?_, ?_⟩
    · rw [← h0]; exact C.left_mem 0 (by omega)
    · rw [← hn, hC1]; exact C.right_mem 0 (by omega)
  · left
    refine ⟨C.n - 2, hasConfig_MI_of_gap hF' C hC.isInduced hge hw (h0 ▸ hu) (hn ▸ hv) ?_⟩
    intro i hi0 hin hiS
    rcases hnb _ (C.q_mem i (by omega)) hiS with h | h
    · rw [← h0] at h; have := hC.q_inj (by omega) (by omega) h; omega
    · rw [← hn] at h; have := hC.q_inj (by omega) (by omega) h; omega

/-- **Element apex.**  An element `w ∈ O` outside `O'` lying in exactly the sets `u ≠ v`
among `F' ∪ {u, v}`, where some element of `u` reaches some element of `v` in `(O', F')`:
either an `MI` configuration of `F ⊇ F'`, or an element of `O'` in both `u` and `v`. -/
theorem apex_elem {O O' : Finset α} {F F' : Finset (Finset α)} (hO' : O' ⊆ O) (hF' : F' ⊆ F)
    {w : α} (hw : w ∈ O) (hwO' : w ∉ O') {u v : Finset α} (huF : u ∈ F) (hvF : v ∈ F)
    (huF' : u ∉ F') (hu : w ∈ u) (hv : w ∈ v) (hnb : ∀ S ∈ F', w ∉ S)
    (hreach : ∃ a b, a ∈ O' ∧ a ∈ u ∧ b ∈ v ∧ Reach O' F' a b) :
    (∃ k, HasConfig F (MI k)) ∨ ∃ t ∈ O', t ∈ u ∧ t ∈ v := by
  classical
  have hex : ∃ n, ∃ C : Chain O' F', C.q 0 ∈ u ∧ C.q C.n ∈ v ∧ C.n = n := by
    obtain ⟨a, b, haO', hau, hbv, hab⟩ := hreach
    obtain ⟨C, h0, hn⟩ := Chain.ofReach hab haO'
    exact ⟨C.n, C, h0 ▸ hau, hn ▸ hbv, rfl⟩
  obtain ⟨C, h0, hn, hCn⟩ := Nat.find_spec hex
  have hmin : ∀ D : Chain O' F', D.q 0 ∈ u → D.q D.n ∈ v → C.n ≤ D.n := fun D hD0 hDn =>
    hCn ▸ Nat.find_min' hex ⟨D, hD0, hDn, rfl⟩
  have hC : C.IsShortest := fun D hD0 hDn => hmin D (hD0 ▸ h0) (hDn ▸ hn)
  have hind := hC.isInduced
  rcases Nat.eq_zero_or_pos C.n with hz | hpos
  · right
    refine ⟨C.q 0, C.q_mem 0 (by omega), h0, ?_⟩
    rw [← hz]; exact hn
  · left
    -- no interior element of the chain lies in `u` or in `v`
    have hnu : ∀ i, 0 < i → i ≤ C.n → C.q i ∉ u := by
      intro i hi0 hin hiu
      have := hmin (C.drop i hin) (by simpa using hiu) (by
        simp only [Chain.drop_q, Chain.drop_n]
        rw [show i + (C.n - i) = C.n by omega]; exact hn)
      simp only [Chain.drop_n] at this
      omega
    have hnv : ∀ i, i < C.n → C.q i ∉ v := by
      intro i hin hiv
      have := hmin (C.take i) (by simpa using h0) (by
        simp only [Chain.take_q, Chain.take_n]
        rw [min_eq_left (by omega)]; exact hiv)
      simp only [Chain.take_n] at this
      omega
    set D := (C.mono hO' hF').cons w u hw huF hu h0 with hD
    have hDn : D.n = C.n + 1 := rfl
    have hDq : ∀ i, D.q i = if i = 0 then w else C.q (i - 1) := fun i => rfl
    have hDr : ∀ i, D.r i = if i ≤ 1 then u else C.r (i - 1) := fun i => rfl
    have hDind : D.IsInduced := by
      refine ⟨?_, ?_, ?_⟩
      · intro i j hi hj h
        rw [hDq, hDq] at h
        split_ifs at h with h1 h2 h2
        · omega
        · exact absurd (h ▸ C.q_mem (j - 1) (by omega)) hwO'
        · exact absurd (h ▸ C.q_mem (i - 1) (by omega)) hwO'
        · have := hind.q_inj (i - 1) (j - 1) (by omega) (by omega) h; omega
      · intro i j h1 hi h1' hj h
        rw [hDr, hDr] at h
        split_ifs at h with h2 h3 h3
        · omega
        · exact absurd (h ▸ C.r_mem (j - 1) (by omega) (by omega)) huF'
        · exact absurd (h ▸ C.r_mem (i - 1) (by omega) (by omega)) huF'
        · have := hind.r_inj (i - 1) (j - 1) (by omega) (by omega) (by omega) (by omega) h
          omega
      · intro i j hi h1 hj
        rw [hDq, hDr]
        by_cases hi0 : i = 0
        · subst hi0
          rw [if_pos rfl]
          by_cases hj1 : j ≤ 1
          · rw [if_pos hj1]; exact iff_of_true hu (Or.inr (by omega))
          · rw [if_neg hj1]
            exact iff_of_false (hnb _ (C.r_mem (j - 1) (by omega) (by omega))) (by omega)
        · rw [if_neg hi0]
          by_cases hj1 : j ≤ 1
          · rw [if_pos hj1]
            constructor
            · intro h
              by_contra hne
              exact hnu (i - 1) (by omega) (by omega) h
            · intro h
              have : i = 1 := by omega
              subst this; exact h0
          · rw [if_neg hj1, hind.incid (i - 1) (j - 1) (by omega) (by omega) (by omega)]
            omega
    refine ⟨D.n - 2, hasConfig_MI_of_gap (Finset.Subset.refl F) D hDind (by omega) hvF ?_ ?_ ?_⟩
    · rw [hDq]; simp only [if_true]; exact hv
    · rw [hDq, hDn]; simp only [add_eq_zero, one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel]; exact hn
    · intro i hi0 hin h
      rw [hDq] at h
      rw [if_neg (by omega)] at h
      exact hnv (i - 1) (by omega) h

end Tucker

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerTheorem7Setup

/-!
# Tucker's Theorem 7: tools for the case analysis

* replacing one set or one element of a chain (`Chain.setR`, `Chain.setQ`);
* a chain running inside an induced chain moves at most one index per step
  (`index_bound_of_inside`);
* a set meeting an induced chain in a non-interval closes an `MI` cycle (`interval_or_MI`);
* the configurations `MII`, `MIII`, `MIV`, `MV` from explicit data.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*}

namespace Chain

variable {O : Finset α} {F : Finset (Finset α)}

/-- Replace the set at index `k` (`1 ≤ k ≤ n`) by `T`. -/
def setR (C : Chain O F) (k : ℕ) (T : Finset α) (hT : T ∈ F) (hl : C.q (k - 1) ∈ T)
    (hr : C.q k ∈ T) : Chain O F where
  n := C.n
  q := C.q
  r := fun i => if i = k then T else C.r i
  q_mem := C.q_mem
  r_mem := fun i h1 hi => by
    split_ifs with h
    · exact hT
    · exact C.r_mem i h1 hi
  left_mem := fun i hi => by
    split_ifs with h
    · rw [show i = k - 1 by omega]; exact hl
    · exact C.left_mem i hi
  right_mem := fun i hi => by
    split_ifs with h
    · rw [show i + 1 = k from h]; exact hr
    · exact C.right_mem i hi

@[simp] theorem setR_n (C : Chain O F) (k : ℕ) (T : Finset α) (hT : T ∈ F) (hl : C.q (k - 1) ∈ T)
    (hr : C.q k ∈ T) : (C.setR k T hT hl hr).n = C.n := rfl
@[simp] theorem setR_q (C : Chain O F) (k : ℕ) (T : Finset α) (hT : T ∈ F) (hl : C.q (k - 1) ∈ T)
    (hr : C.q k ∈ T) : (C.setR k T hT hl hr).q = C.q := rfl
theorem setR_r (C : Chain O F) (k : ℕ) (T : Finset α) (hT : T ∈ F) (hl : C.q (k - 1) ∈ T)
    (hr : C.q k ∈ T) (i : ℕ) : (C.setR k T hT hl hr).r i = if i = k then T else C.r i := rfl

/-- Replace the element at index `k` by `b` (`b` must lie in the sets on both sides). -/
def setQ (C : Chain O F) (k : ℕ) (b : α) (hb : b ∈ O) (hl : b ∈ C.r k) (hr : b ∈ C.r (k + 1)) :
    Chain O F where
  n := C.n
  q := fun i => if i = k then b else C.q i
  r := C.r
  q_mem := fun i hi => by
    split_ifs with h
    · exact hb
    · exact C.q_mem i hi
  r_mem := C.r_mem
  left_mem := fun i hi => by
    split_ifs with h
    · subst h; exact hr
    · exact C.left_mem i hi
  right_mem := fun i hi => by
    split_ifs with h
    · subst h; exact hl
    · exact C.right_mem i hi

@[simp] theorem setQ_n (C : Chain O F) (k : ℕ) (b : α) (hb : b ∈ O) (hl : b ∈ C.r k)
    (hr : b ∈ C.r (k + 1)) : (C.setQ k b hb hl hr).n = C.n := rfl
theorem setQ_q (C : Chain O F) (k : ℕ) (b : α) (hb : b ∈ O) (hl : b ∈ C.r k)
    (hr : b ∈ C.r (k + 1)) (i : ℕ) : (C.setQ k b hb hl hr).q i = if i = k then b else C.q i := rfl
@[simp] theorem setQ_r (C : Chain O F) (k : ℕ) (b : α) (hb : b ∈ O) (hl : b ∈ C.r k)
    (hr : b ∈ C.r (k + 1)) : (C.setQ k b hb hl hr).r = C.r := rfl

end Chain

/-! ### A chain inside an induced chain -/

/-- A chain `C` whose elements from index `l₀` on and sets after `l₀` all lie on the induced
chain `R` moves at most one `R`-index per step: the element `C.q l` at `R`-index `j` satisfies
`j₀ ≤ j + (l - l₀)` and `j ≤ j₀ + (l - l₀)`, where `C.q l₀ = R.q j₀`. -/
theorem index_bound_of_inside {O O' : Finset α} {F F' : Finset (Finset α)} (R : Chain O F)
    (hR : R.IsInduced) (C : Chain O' F') {l₀ j₀ : ℕ} (hl₀ : l₀ ≤ C.n) (hj₀ : j₀ ≤ R.n)
    (h0 : C.q l₀ = R.q j₀)
    (hq : ∀ l, l₀ ≤ l → l ≤ C.n → ∃ j, j ≤ R.n ∧ R.q j = C.q l)
    (hr : ∀ l, l₀ < l → l ≤ C.n → ∃ j, 1 ≤ j ∧ j ≤ R.n ∧ R.r j = C.r l) :
    ∀ l, l₀ ≤ l → l ≤ C.n → ∀ j, j ≤ R.n → R.q j = C.q l →
      j₀ ≤ j + (l - l₀) ∧ j ≤ j₀ + (l - l₀) := by
  intro l hl₀l hl
  induction l with
  | zero =>
    intro j hj hjl
    obtain rfl : l₀ = 0 := by omega
    have := hR.q_inj j j₀ hj hj₀ (hjl.trans h0)
    omega
  | succ l ih =>
    intro j hj hjl
    rcases Nat.eq_or_lt_of_le hl₀l with h | h
    · rw [← h] at hjl
      have := hR.q_inj j j₀ hj hj₀ (hjl.trans h0)
      omega
    · obtain ⟨j', hj', hj'l⟩ := hq l (by omega) (by omega)
      obtain ⟨ih1, ih2⟩ := ih (by omega) (by omega) j' hj' hj'l
      obtain ⟨s, hs1, hs, hsl⟩ := hr (l + 1) (by omega) hl
      -- `C.q l ∈ C.r (l+1)` and `C.q (l+1) ∈ C.r (l+1)`, both read on `R`
      have h1 : R.q j' ∈ R.r s := by rw [hj'l, hsl]; exact C.left_mem l (by omega)
      have h2 : R.q j ∈ R.r s := by rw [hjl, hsl]; exact C.right_mem l (by omega)
      have e1 := (hR.incid j' s hj' hs1 hs).mp h1
      have e2 := (hR.incid j s hj hs1 hs).mp h2
      omega

/-! ### Intervals -/

/-- A set `T ∈ F` meets the elements of an induced chain `R` (with sets in `F`) in an
interval of indices, unless there is an `MI` configuration. -/
theorem interval_or_MI [DecidableEq α] {O : Finset α} {F F' : Finset (Finset α)} (hF' : F' ⊆ F)
    (R : Chain O F') (hR : R.IsInduced) {T : Finset α} (hT : T ∈ F) :
    (∀ i i' i'', i ≤ i' → i' ≤ i'' → i'' ≤ R.n → R.q i ∈ T → R.q i'' ∈ T → R.q i' ∈ T) ∨
      ∃ k, HasConfig F (MI k) := by
  classical
  by_contra hcon
  obtain ⟨hnot, hMI⟩ := not_or.mp hcon
  simp only [not_forall] at hnot
  obtain ⟨i, i', i'', hii', hi'i'', hi'', hi, hi''T, hi'T⟩ := hnot
  -- the nearest elements of `T` on either side of `i'`
  have hexl : ∃ a, a ≤ i' ∧ R.q a ∈ T := ⟨i, hii', hi⟩
  have hexr : ∃ b, i' ≤ b ∧ b ≤ R.n ∧ R.q b ∈ T := ⟨i'', hi'i'', hi'', hi''T⟩
  obtain ⟨a, ha, hai', hamax⟩ : ∃ a, R.q a ∈ T ∧ a ≤ i' ∧ ∀ c, a < c → c ≤ i' → R.q c ∉ T :=
    ⟨Nat.findGreatest (fun a => R.q a ∈ T) i',
      Nat.findGreatest_spec (P := fun a => R.q a ∈ T) hii' hi, Nat.findGreatest_le i',
      fun c hac hci' => Nat.findGreatest_is_greatest hac hci'⟩
  obtain ⟨b, hb, hbmin⟩ : ∃ b, (i' ≤ b ∧ b ≤ R.n ∧ R.q b ∈ T) ∧
      ∀ c, i' ≤ c → c < b → R.q c ∉ T := by
    refine ⟨Nat.find hexr, Nat.find_spec hexr, fun c hi'c hcb hcT => ?_⟩
    have := (Nat.find_spec hexr).2.1
    exact Nat.find_min hexr hcb ⟨hi'c, by omega, hcT⟩
  have ha' : a ≠ i' := fun h => hi'T (h ▸ ha)
  have hb' : b ≠ i' := fun h => hi'T (h ▸ hb.2.2)
  have hab : a < b := by omega
  -- the segment from `a` to `b`
  apply hMI
  refine apex_set (O' := O.filter fun c => ∃ l, a ≤ l ∧ l ≤ b ∧ R.q l = c)
    (F' := F'.filter fun S => ∃ l, a < l ∧ l ≤ b ∧ R.r l = S) (fun S hS => hF' (mem_filter.mp hS).1)
    hT (fun h => by have := hR.q_inj a b (by omega) hb.2.1 h; omega) ha hb.2.2 ?_
    (mem_filter.mpr ⟨R.q_mem a (by omega), a, le_rfl, hab.le, rfl⟩) ?_ |>.resolve_right ?_
  · intro c hc hcT
    obtain ⟨_, l, hal, hlb, rfl⟩ := mem_filter.mp hc
    by_contra hne
    obtain ⟨h1, h2⟩ := not_or.mp hne
    have hla : l ≠ a := fun e => h1 (by rw [e])
    have hlb' : l ≠ b := fun e => h2 (by rw [e])
    rcases Nat.lt_or_ge l i' with h | h
    · exact hamax l (by omega) (by omega) hcT
    · exact hbmin l h (by omega) hcT
  · exact R.reach_segment hab.le hb.2.1
      (fun l h1 h2 => mem_filter.mpr ⟨R.q_mem l (by omega), l, h1, h2, rfl⟩)
      (fun l h1 h2 => mem_filter.mpr ⟨R.r_mem l (by omega) (by omega), l, h1, h2, rfl⟩)
  · rintro ⟨S, hS, haS, hbS⟩
    obtain ⟨_, l, hal, hlb, rfl⟩ := mem_filter.mp hS
    have e1 := (hR.incid a l (by omega) (by omega) (by omega)).mp haS
    have e2 := (hR.incid b l hb.2.1 (by omega) (by omega)).mp hbS
    omega

/-! ### Configurations from explicit data -/

theorem hasConfig_of_fun [DecidableEq α] {F : Finset (Finset α)} {rn cn : ℕ} {M : Pattern rn cn}
    (s : Fin rn → Finset α) (c : Fin cn → α) (hs : Function.Injective s)
    (hc : Function.Injective c) (hF : ∀ i, s i ∈ F) (h : ∀ i j, c j ∈ s i ↔ j ∈ M i) :
    HasConfig F M :=
  ⟨⟨s, hs⟩, ⟨c, hc⟩, hF, h⟩

theorem mem_pairRow_val {c : ℕ} {i j : Fin (c + 2)} :
    j ∈ pairRow i ↔ j.val = i.val ∨ j.val = (i.val + 1) % (c + 2) := by
  simp only [pairRow, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_add]
  have h1 : ((1 : Fin (c + 2)) : ℕ) = 1 := Fin.val_one c
  rw [h1]

/-- `MII (n-2)` from a chordless path `q 0 – r 1 – ⋯ – r n – q n` (`n ≥ 2`), an element `w`
off the path, and sets `u = {w, q 0, …, q (n-1)}`, `v = {w, q 1, …, q n}` (on these
elements). -/
theorem hasConfig_MII_of_data [DecidableEq α] {F : Finset (Finset α)} (q : ℕ → α)
    (r : ℕ → Finset α) {n : ℕ} (hn : 2 ≤ n) (w : α) (u v : Finset α)
    (hq : ∀ i j, i ≤ n → j ≤ n → q i = q j → i = j) (hwq : ∀ i, i ≤ n → q i ≠ w)
    (hr : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → r i = r j → i = j)
    (hrF : ∀ i, 1 ≤ i → i ≤ n → r i ∈ F) (huF : u ∈ F) (hvF : v ∈ F) (huv : u ≠ v)
    (hur : ∀ i, 1 ≤ i → i ≤ n → r i ≠ u) (hvr : ∀ i, 1 ≤ i → i ≤ n → r i ≠ v)
    (hinc : ∀ i j, 1 ≤ i → i ≤ n → j ≤ n → (q j ∈ r i ↔ j + 1 = i ∨ j = i))
    (hwr : ∀ i, 1 ≤ i → i ≤ n → w ∉ r i)
    (hqu : ∀ j, j ≤ n → (q j ∈ u ↔ j < n)) (hwu : w ∈ u)
    (hqv : ∀ j, j ≤ n → (q j ∈ v ↔ 1 ≤ j)) (hwv : w ∈ v) : HasConfig F (MII (n - 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega]
  refine hasConfig_of_fun
    (fun i : Fin (k + 4) => if i.val ≤ k + 1 then r (i.val + 1) else if i.val = k + 2 then u else v)
    (fun j : Fin (k + 4) => if j.val ≤ k + 2 then q j.val else w) ?_ ?_ ?_ ?_
  · intro i i' h
    simp only at h
    split_ifs at h with h1 h2 h3 h3 h4 h5 h6
    · exact Fin.ext (by have := hr _ _ (by omega) (by omega) (by omega) (by omega) h; omega)
    · exact absurd h (hur _ (by omega) (by omega))
    · exact absurd h (hvr _ (by omega) (by omega))
    · exact absurd h.symm (hur _ (by omega) (by omega))
    · exact Fin.ext (by omega)
    · exact absurd h huv
    · exact absurd h.symm (hvr _ (by omega) (by omega))
    · exact absurd h.symm huv
    · exact Fin.ext (by omega)
  · intro j j' h
    simp only at h
    split_ifs at h with h1 h2 h2
    · exact Fin.ext (hq _ _ (by omega) (by omega) h)
    · exact absurd h (hwq _ (by omega))
    · exact absurd h.symm (hwq _ (by omega))
    · exact Fin.ext (by omega)
  · intro i
    split_ifs with h1 h2
    · exact hrF _ (by omega) (by omega)
    · exact huF
    · exact hvF
  · intro i j
    simp only [MII]
    split_ifs with h1 h2 h3 h3
    · -- row `r (i+1)`, column `q j`
      rw [mem_pairRow_val, hinc (i.val + 1) j.val (by omega) (by omega) (by omega)]
      simp only
      rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2 + 2)]
      omega
    · -- row `r (i+1)`, column `w`
      rw [mem_pairRow_val]
      simp only
      rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2 + 2)]
      exact iff_of_false (hwr _ (by omega) (by omega)) (by omega)
    · simp only [mem_filter, mem_univ, true_and]
      rw [hqu j.val (by omega)]
      omega
    · simp only [mem_filter, mem_univ, true_and]
      exact iff_of_true hwu (by omega)
    · simp only [mem_filter, mem_univ, true_and]
      rw [hqv j.val (by omega)]
    · simp only [mem_filter, mem_univ, true_and]
      exact iff_of_true hwv (by omega)

/-- `MIII (n-2)` from a chordless path `q 0 – r 1 – ⋯ – r n – q n` (`n ≥ 2`), an element `x`
off the path, and a set `w = {x, q 1, …, q (n-1)}` (on these elements). -/
theorem hasConfig_MIII_of_data [DecidableEq α] {F : Finset (Finset α)} (q : ℕ → α)
    (r : ℕ → Finset α) {n : ℕ} (hn : 2 ≤ n) (x : α) (w : Finset α)
    (hq : ∀ i j, i ≤ n → j ≤ n → q i = q j → i = j) (hxq : ∀ i, i ≤ n → q i ≠ x)
    (hr : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → r i = r j → i = j)
    (hrF : ∀ i, 1 ≤ i → i ≤ n → r i ∈ F) (hwF : w ∈ F)
    (hwr : ∀ i, 1 ≤ i → i ≤ n → r i ≠ w)
    (hinc : ∀ i j, 1 ≤ i → i ≤ n → j ≤ n → (q j ∈ r i ↔ j + 1 = i ∨ j = i))
    (hxr : ∀ i, 1 ≤ i → i ≤ n → x ∉ r i)
    (hqw : ∀ j, j ≤ n → (q j ∈ w ↔ 1 ≤ j ∧ j < n)) (hxw : x ∈ w) :
    HasConfig F (MIII (n - 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega]
  refine hasConfig_of_fun
    (fun i : Fin (k + 3) => if i.val ≤ k + 1 then r (i.val + 1) else w)
    (fun j : Fin (k + 4) => if j.val ≤ k + 2 then q j.val else x) ?_ ?_ ?_ ?_
  · intro i i' h
    simp only at h
    split_ifs at h with h1 h2 h2
    · exact Fin.ext (by have := hr _ _ (by omega) (by omega) (by omega) (by omega) h; omega)
    · exact absurd h (hwr _ (by omega) (by omega))
    · exact absurd h.symm (hwr _ (by omega) (by omega))
    · exact Fin.ext (by omega)
  · intro j j' h
    simp only at h
    split_ifs at h with h1 h2 h2
    · exact Fin.ext (hq _ _ (by omega) (by omega) h)
    · exact absurd h (hxq _ (by omega))
    · exact absurd h.symm (hxq _ (by omega))
    · exact Fin.ext (by omega)
  · intro i
    split_ifs with h1
    · exact hrF _ (by omega) (by omega)
    · exact hwF
  · intro i j
    simp only [MIII]
    split_ifs with h1 h2 h2
    · rw [mem_pairRow_val, hinc (i.val + 1) j.val (by omega) (by omega) (by omega)]
      simp only
      rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2 + 2)]
      omega
    · rw [mem_pairRow_val]
      simp only
      rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2 + 2)]
      exact iff_of_false (hxr _ (by omega) (by omega)) (by omega)
    · simp only [mem_filter, mem_univ, true_and]
      rw [hqw j.val (by omega)]
      omega
    · simp only [mem_filter, mem_univ, true_and]
      exact iff_of_true hxw (by omega)

end Tucker

end TSPGap

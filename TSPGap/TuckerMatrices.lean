/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CircularOnes

/-!
# Tucker's forbidden configurations

Tucker's structure theorem (A. Tucker, *A structure theorem for the consecutive 1's
property*, J. Combin. Theory Ser. B 12 (1972) 153–162) characterizes the families of
sets whose incidence matrices have the consecutive-ones property for rows by five
families of forbidden submatrices, `M_I(k)`, `M_II(k)`, `M_III(k)` (`k ≥ 1`), `M_IV`
and `M_V`.  A family *contains a configuration* `M` if some distinct rows and distinct
elements realize exactly the incidences of `M` (a submatrix up to permutations of rows
and columns).

The matrices are frozen here **as in Tucker's paper**.  Tucker's parameter is `k ≥ 1`
(`M_I(k)` is `(k+2) × (k+2)`, `M_II(k)` is `(k+3) × (k+3)`, `M_III(k)` is `(k+2) × (k+3)`,
`M_IV` is `4 × 6`, `M_V` is `4 × 5`); the Lean index is shifted so that every `k : ℕ` is a
genuine pattern — `MI k`, `MII k`, `MIII k` are Tucker's `M_I(k+1)`, `M_II(k+1)`,
`M_III(k+1)` — in `0`-based coordinates.  (Audit Q16 caught the earlier unshifted version,
whose `k = 0` instances `{{0,1},{0,1}}` and `{{0,1},{2}}` are not obstructions at all and
made `IsTuckerFree` far too strong.)  Rows are recorded as sets of column indices.

* `MI k`: rows `{i, i+1}` for `i = 0, …, k+2`, indices mod `k+3` — the cycle;
* `MII k`: rows `{i, i+1}` for `i = 0, …, k+1`, then `{0, …, k+1} ∪ {k+3}` and
  `{1, …, k+3}`, on `k+4` columns;
* `MIII k`: rows `{i, i+1}` for `i = 0, …, k+1`, then `{1, …, k+1} ∪ {k+3}`, on `k+4`
  columns;
* `MIV`: `{0,1}, {2,3}, {4,5}, {1,3,5}`;
* `MV`: `{0,1}, {0,1,2,3}, {2,3}, {0,3,4}`.

The primary source was checked against three independent reproductions (Safe 2016,
Figure 5; Blanchette–Vialette–Weller 2012, Figure 1; Stoye–Wittler 2009, Appendix), which
agree; some reproductions index `M_I(k)` etc. by the number of rows.  In BG08's hypergraph
language (Figure 8) these are `C_n` (`n ≥ 3`), `M_n`/`N_n` (`n ≥ 1`) and `O_2`, `O_1`.

This file only fixes the patterns and the configuration predicate, with its
monotonicity and relabeling lemmas.  The sufficiency theorem — a Tucker-free family has
the consecutive-ones property — is `TSPGap/TuckerSufficiency.lean`; the reduction of a
configuration to a cycle or a comb of a symmetric family is `TSPGap/TuckerReduction.lean`.
-/

namespace TSPGap
open Finset

namespace Tucker

/-- A `0/1` pattern with `r` rows and `c` columns: each row as the set of its columns. -/
abbrev Pattern (r c : ℕ) := Fin r → Finset (Fin c)

/-- The row `{i, i + 1}` (indices in `Fin c`). -/
def pairRow {c : ℕ} [NeZero c] (i : Fin c) : Finset (Fin c) := {i, i + 1}

/-- `MI k` = Tucker's `M_I(k+1)`: the cycle on `k + 3` rows and `k + 3` columns. -/
def MI (k : ℕ) : Pattern (k + 3) (k + 3) := fun i => pairRow i

/-- `MII k` = Tucker's `M_II(k+1)`: `(k + 4) × (k + 4)`. -/
def MII (k : ℕ) : Pattern (k + 4) (k + 4) := fun i =>
  if i.val ≤ k + 1 then pairRow ⟨i.val, by omega⟩
  else if i.val = k + 2 then univ.filter fun j => j.val ≤ k + 1 ∨ j.val = k + 3
  else univ.filter fun j => 1 ≤ j.val

/-- `MIII k` = Tucker's `M_III(k+1)`: `(k + 3) × (k + 4)`. -/
def MIII (k : ℕ) : Pattern (k + 3) (k + 4) := fun i =>
  if i.val ≤ k + 1 then pairRow ⟨i.val, by omega⟩
  else univ.filter fun j => (1 ≤ j.val ∧ j.val ≤ k + 1) ∨ j.val = k + 3

/-- `M_IV`: `4 × 6`. -/
def MIV : Pattern 4 6 := ![{0, 1}, {2, 3}, {4, 5}, {1, 3, 5}]

/-- `M_V`: `4 × 5`. -/
def MV : Pattern 4 5 := ![{0, 1}, {0, 1, 2, 3}, {2, 3}, {0, 3, 4}]

variable {α : Type*} [DecidableEq α]

/-- `F` contains the pattern `M` as a configuration: distinct rows of `F` and distinct
elements realizing exactly the incidences of `M`. -/
def HasConfig (F : Finset (Finset α)) {r c : ℕ} (M : Pattern r c) : Prop :=
  ∃ (ρ : Fin r ↪ Finset α) (γ : Fin c ↪ α), (∀ i, ρ i ∈ F) ∧ ∀ i j, γ j ∈ ρ i ↔ j ∈ M i

/-- `F` contains none of Tucker's configurations. -/
def IsTuckerFree (F : Finset (Finset α)) : Prop :=
  (∀ k, ¬ HasConfig F (MI k)) ∧ (∀ k, ¬ HasConfig F (MII k)) ∧
    (∀ k, ¬ HasConfig F (MIII k)) ∧ ¬ HasConfig F MIV ∧ ¬ HasConfig F MV

omit [DecidableEq α] in
theorem HasConfig.mono {F F' : Finset (Finset α)} (h : F ⊆ F') {r c : ℕ} {M : Pattern r c}
    (hM : HasConfig F M) : HasConfig F' M := by
  obtain ⟨ρ, γ, hρ, hspec⟩ := hM
  exact ⟨ρ, γ, fun i => h (hρ i), hspec⟩

omit [DecidableEq α] in
theorem IsTuckerFree.mono {F F' : Finset (Finset α)} (h : F' ⊆ F) (hF : IsTuckerFree F) :
    IsTuckerFree F' :=
  ⟨fun k hk => hF.1 k (hk.mono h), fun k hk => hF.2.1 k (hk.mono h),
    fun k hk => hF.2.2.1 k (hk.mono h), fun hk => hF.2.2.2.1 (hk.mono h),
    fun hk => hF.2.2.2.2 (hk.mono h)⟩

omit [DecidableEq α] in
/-- Configurations transport along relabelings of the ground set. -/
theorem HasConfig.map {β : Type*} [DecidableEq β] {F : Finset (Finset α)} (f : α ↪ β)
    {r c : ℕ} {M : Pattern r c} (hM : HasConfig F M) :
    HasConfig (F.image fun R => R.map f) M := by
  obtain ⟨ρ, γ, hρ, hspec⟩ := hM
  refine ⟨⟨fun i => (ρ i).map f, fun i i' h => ρ.injective (Finset.map_injective f h)⟩,
    γ.trans f, fun i => Finset.mem_image_of_mem _ (hρ i), fun i j => ?_⟩
  simp only [Function.Embedding.coeFn_mk, Function.Embedding.trans_apply, Finset.mem_map' f]
  exact hspec i j

/-- A configuration of the restriction `F|O` (rows `R ∩ O`) is a configuration of `F`,
provided the pattern has no all-zero column (so every column lies in `O`). -/
theorem HasConfig.of_restrict {F : Finset (Finset α)} {O : Finset α} {r c : ℕ}
    {M : Pattern r c} (hcol : ∀ j, ∃ i, j ∈ M i)
    (hM : HasConfig (F.image fun R => R ∩ O) M) : HasConfig F M := by
  classical
  obtain ⟨ρ, γ, hρ, hspec⟩ := hM
  choose S hS hSρ using fun i => Finset.mem_image.mp (hρ i)
  have hO : ∀ j, γ j ∈ O := fun j => by
    obtain ⟨i, hi⟩ := hcol j
    have := (hspec i j).mpr hi
    rw [← hSρ i] at this
    exact (Finset.mem_inter.mp this).2
  refine ⟨⟨S, fun i i' h => ρ.injective (by rw [← hSρ i, ← hSρ i', h])⟩, γ, hS, fun i j => ?_⟩
  simp only [Function.Embedding.coeFn_mk]
  rw [← hspec i j, ← hSρ i, Finset.mem_inter]
  exact ⟨fun h => ⟨h, hO j⟩, fun h => h.1⟩

/-! ### No pattern has an all-zero column -/

theorem mem_pairRow {c : ℕ} [NeZero c] {i x : Fin c} : x ∈ pairRow i ↔ x = i ∨ x = i + 1 := by
  simp [pairRow]

theorem MI_col (k : ℕ) (j : Fin (k + 3)) : ∃ i, j ∈ MI k i :=
  ⟨j, by simp [MI, mem_pairRow]⟩

theorem MII_col (k : ℕ) (j : Fin (k + 4)) : ∃ i, j ∈ MII k i := by
  by_cases hj : j.val ≤ k + 1
  · exact ⟨⟨j.val, by omega⟩, by simp [MII, hj, mem_pairRow]⟩
  · by_cases hj' : j.val = k + 2
    · refine ⟨⟨k + 1, by omega⟩, ?_⟩
      simp only [MII, le_refl, if_true, mem_pairRow]
      right
      ext
      simp [Fin.val_add, hj', Nat.mod_eq_of_lt]
    · refine ⟨⟨k + 2, by omega⟩, ?_⟩
      have h2 : j.val = k + 3 := by have := j.isLt; omega
      simp [MII, h2]

theorem MIII_col (k : ℕ) (j : Fin (k + 4)) : ∃ i, j ∈ MIII k i := by
  by_cases hj : j.val ≤ k + 1
  · exact ⟨⟨j.val, by omega⟩, by simp [MIII, hj, mem_pairRow]⟩
  · by_cases hj' : j.val = k + 2
    · refine ⟨⟨k + 1, by omega⟩, ?_⟩
      simp only [MIII, le_refl, if_true, mem_pairRow]
      right
      ext
      simp [Fin.val_add, hj', Nat.mod_eq_of_lt]
    · refine ⟨⟨k + 2, by omega⟩, ?_⟩
      have h2 : j.val = k + 3 := by have := j.isLt; omega
      simp [MIII, h2]

theorem MIV_col (j : Fin 6) : ∃ i, j ∈ MIV i := by
  fin_cases j <;> decide

theorem MV_col (j : Fin 5) : ∃ i, j ∈ MV i := by
  fin_cases j <;> decide

/-- Tucker-freeness passes to restrictions `R ↦ R ∩ O`. -/
theorem IsTuckerFree.restrict {F : Finset (Finset α)} (h : IsTuckerFree F) (O : Finset α) :
    IsTuckerFree (F.image fun R => R ∩ O) :=
  ⟨fun k hk => h.1 k (hk.of_restrict (MI_col k)), fun k hk => h.2.1 k (hk.of_restrict (MII_col k)),
    fun k hk => h.2.2.1 k (hk.of_restrict (MIII_col k)),
    fun hk => h.2.2.2.1 (hk.of_restrict MIV_col), fun hk => h.2.2.2.2 (hk.of_restrict MV_col)⟩

end Tucker

end TSPGap

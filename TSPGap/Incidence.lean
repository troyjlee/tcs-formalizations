/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic
import TSPGap.CauchyBinet

/-!
# The reduced oriented incidence matrix

The third link.  **For `T.card = k`**, `gramMinor (reducedIncidence k) T` is `1`
exactly when `T` is a spanning tree, and `0` otherwise.  The cardinality
hypothesis is not decoration: it is what makes the selected columns square, and
without it the Gram minor is not a `{0,1}`-valued invariant at all.

## Total unimodularity, not leaf induction

The Gram minor is evaluated through total unimodularity rather than by deleting
leaves and transporting matrices.  The TU induction is the only substantial part:
for a square submatrix, either some column has at most one nonzero entry — Laplace
expand and recurse — or every column has two, which are `+1` and `-1`, so the rows
sum to zero and the determinant vanishes.

`gramMinor_of_tu` is the generic bridge, and it is where the sign disappears for
good: for a totally unimodular `A` with `|S|` equal to the number of rows, the
square reindexing has determinant in `{0, ±1}`, and the Gram minor is its
*square*.  So `gramMinor A S = if FullRowRank (colsOn A S) then 1 else 0` — a
statement with no orientation in it.

## The graph side is then linear algebra

`vecMul u (reducedIncidence k) e = Fin.snoc u 0 e.inf - Fin.snoc u 0 e.sup`:
deleting the last vertex is *extension by zero*.  So a vector in the left kernel
is exactly a potential that is constant along every edge and vanishes at the last
vertex — whence

`FullRowRank (colsOn (reducedIncidence k) T) ↔ (fromEdgeSet ↑T).Connected`,

with no cardinality hypothesis at all.

## Loop-freeness comes free from the determinant

`IsSpanningTree` also demands no loops, and at `T.card = k` that is *implied* by
connectivity — a connected graph on `k+1` vertices needs `k` genuine edges.
Rather than prove that counting fact, note that a loop contributes a **zero
column**; with as many columns as rows the determinant then vanishes, so full row
rank fails, so the graph is disconnected.  The linear algebra already knows.

## Main results

* `isTotallyUnimodular_incidence`, `isTotallyUnimodular_reducedIncidence`.
* `vecMul_reducedIncidence` — extension by zero.
* `fullRowRank_reducedIncidence` — needed by `Determinant.lean` in its own right,
  not only through the Gram characterization.
* `gramMinor_of_tu` — the generic bridge.
* `fullRowRank_colsOn_reducedIncidence_iff` — the graph bridge.
* `gramMinor_reducedIncidence` — the target.
-/

namespace TSPGap

open Matrix

/-! ### Sign values -/

/-- The three values a totally unimodular determinant can take. -/
def IsSgn (x : ℝ) : Prop := x = 0 ∨ x = 1 ∨ x = -1

theorem isSgn_iff {x : ℝ} : x ∈ Set.range (SignType.cast : SignType → ℝ) ↔ IsSgn x := by
  constructor
  · rintro ⟨s, rfl⟩
    cases s <;> simp [IsSgn]
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩]

theorem IsSgn.mul {x y : ℝ} (hx : IsSgn x) (hy : IsSgn y) : IsSgn (x * y) := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp [IsSgn]

theorem isSgn_neg_one_pow (j : ℕ) : IsSgn ((-1 : ℝ) ^ j) := by
  rcases Nat.even_or_odd j with h | h
  · exact Or.inr (Or.inl h.neg_one_pow)
  · exact Or.inr (Or.inr h.neg_one_pow)

/-! ### The generic bridge: Gram minors of a totally unimodular matrix -/

section Generic

variable {r m : Type*} [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

/-- `colsOn A S` reindexed to a square matrix, available when `S` has exactly as
many elements as `A` has rows.  Which bijection is used is immaterial: everything
below sees only `det ^ 2`. -/
noncomputable def squareOn (A : Matrix r m ℝ) (S : Finset m)
    (hS : S.card = Fintype.card r) : Matrix r r ℝ :=
  (colsOn A S).submatrix id
    (Fintype.equivOfCardEq (by rw [Fintype.card_coe, hS]) : r ≃ {x // x ∈ S})

omit [Fintype m] [DecidableEq m] in
theorem gramMinor_eq_sq (A : Matrix r m ℝ) (S : Finset m) (hS : S.card = Fintype.card r) :
    gramMinor A S = (squareOn A S hS).det ^ 2 := by
  set ε : r ≃ {x // x ∈ S} := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hS]) with hε
  have hprod : colsOn A S * (colsOn A S)ᵀ
      = squareOn A S hS * (squareOn A S hS)ᵀ := by
    rw [squareOn, ← hε, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv (colsOn A S) (colsOn A S)ᵀ id ε id,
      Matrix.submatrix_id_id]
  rw [gramMinor, hprod, Matrix.det_mul, Matrix.det_transpose, sq]

omit [Fintype m] [DecidableEq m] in
/-- Full row rank of the selected columns is nonvanishing of the square
reindexing. -/
theorem fullRowRank_iff_det (A : Matrix r m ℝ) (S : Finset m) (hS : S.card = Fintype.card r) :
    FullRowRank (colsOn A S) ↔ (squareOn A S hS).det ≠ 0 := by
  set ε : r ≃ {x // x ∈ S} := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hS]) with hε
  have hvec : ∀ u : r → ℝ,
      Matrix.vecMul u (squareOn A S hS) = 0 ↔ Matrix.vecMul u (colsOn A S) = 0 := by
    intro u
    constructor
    · intro h
      funext j
      have := congrFun h (ε.symm j)
      simpa [squareOn, ← hε, Matrix.vecMul, dotProduct, Matrix.submatrix_apply] using this
    · intro h
      funext j
      have := congrFun h (ε j)
      simpa [squareOn, ← hε, Matrix.vecMul, dotProduct, Matrix.submatrix_apply] using this
  constructor
  · intro hF hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    exact hv0 (hF v ((hvec v).mp hv))
  · intro hdet u hu
    by_contra hu0
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hu0, (hvec u).mpr hu⟩)

open Classical in
omit [Fintype m] [DecidableEq m] in
/-- **The generic bridge.**  For a totally unimodular matrix, the Gram minor on
a column set of the right size is `1` or `0` according to full row rank.

The square of a `{0, ±1}` determinant is `{0, 1}`, so no sign survives. -/
theorem gramMinor_of_tu {A : Matrix r m ℝ} (hA : A.IsTotallyUnimodular)
    {S : Finset m} (hS : S.card = Fintype.card r) :
    gramMinor A S = if FullRowRank (colsOn A S) then 1 else 0 := by
  have hsgn : IsSgn (squareOn A S hS).det := by
    rw [← isSgn_iff]
    exact (Matrix.isTotallyUnimodular_iff_fintype A).mp hA r id _
  rw [gramMinor_eq_sq A S hS]
  by_cases hd : (squareOn A S hS).det = 0
  · rw [if_neg (by rw [fullRowRank_iff_det A S hS]; exact fun h => h hd), hd]
    norm_num
  · rw [if_pos ((fullRowRank_iff_det A S hS).mpr hd)]
    rcases hsgn with h | h | h
    · exact absurd h hd
    · rw [h]; norm_num
    · rw [h]; norm_num

omit [Fintype m] [DecidableEq m] in
/-- A zero column rules out full row rank, once there are as many columns as
rows.  This is how loop-freeness will be obtained, without any edge count. -/
theorem not_fullRowRank_of_zero_col {A : Matrix r m ℝ} {S : Finset m}
    (hS : S.card = Fintype.card r) {e₀ : m} (he₀ : e₀ ∈ S)
    (hzero : ∀ i, A i e₀ = 0) : ¬ FullRowRank (colsOn A S) := by
  rw [fullRowRank_iff_det A S hS]
  push Not
  set ε : r ≃ {x // x ∈ S} := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hS]) with hε
  refine Matrix.det_eq_zero_of_column_eq_zero (ε.symm ⟨e₀, he₀⟩) fun i => ?_
  simp only [squareOn, ← hε, Matrix.submatrix_apply, Equiv.apply_symm_apply, colsOn]
  exact hzero i

end Generic

/-! ### The oriented incidence matrices -/

/-- The **oriented incidence matrix**: `+1` at the smaller endpoint of an edge,
`-1` at the larger.  A loop gets the zero column, since its two endpoints
coincide and the entries cancel. -/
noncomputable def incidence (k : ℕ) : Matrix (Fin (k+1)) (Sym2 (Fin (k+1))) ℝ :=
  fun v e => (if e.inf = v then 1 else 0) - (if e.sup = v then 1 else 0)

theorem incidence_apply (k : ℕ) (v : Fin (k+1)) (e : Sym2 (Fin (k+1))) :
    incidence k v e = (if e.inf = v then 1 else 0) - (if e.sup = v then 1 else 0) := rfl

theorem isSgn_incidence (k : ℕ) (v : Fin (k+1)) (e : Sym2 (Fin (k+1))) :
    IsSgn (incidence k v e) := by
  rw [incidence_apply]
  split_ifs <;> simp [IsSgn]

theorem incidence_eq_zero_of_ne {k : ℕ} {v : Fin (k+1)} {e : Sym2 (Fin (k+1))}
    (h1 : e.inf ≠ v) (h2 : e.sup ≠ v) : incidence k v e = 0 := by
  rw [incidence_apply, if_neg h1, if_neg h2, sub_zero]

theorem incidence_eq_zero_of_inf_eq_sup {k : ℕ} {v : Fin (k+1)} {e : Sym2 (Fin (k+1))}
    (h : e.inf = e.sup) : incidence k v e = 0 := by
  rw [incidence_apply, h, sub_self]

theorem incidence_inf {k : ℕ} {e : Sym2 (Fin (k+1))} (h : e.inf ≠ e.sup) :
    incidence k e.inf e = 1 := by
  rw [incidence_apply, if_pos rfl, if_neg (fun hc => h hc.symm), sub_zero]

theorem incidence_sup {k : ℕ} {e : Sym2 (Fin (k+1))} (h : e.inf ≠ e.sup) :
    incidence k e.sup e = -1 := by
  rw [incidence_apply, if_neg h, if_pos rfl, zero_sub]

/-- A nonzero entry pins the vertex to an endpoint and rules out a loop. -/
theorem endpoint_of_incidence_ne_zero {k : ℕ} {v : Fin (k+1)} {e : Sym2 (Fin (k+1))}
    (h : incidence k v e ≠ 0) : e.inf ≠ e.sup ∧ (e.inf = v ∨ e.sup = v) := by
  refine ⟨fun hd => h (incidence_eq_zero_of_inf_eq_sup hd), ?_⟩
  by_contra hc
  push Not at hc
  exact h (incidence_eq_zero_of_ne hc.1 hc.2)

/-- The **reduced** incidence matrix: the last vertex's row deleted. -/
noncomputable def reducedIncidence (k : ℕ) : Matrix (Fin k) (Sym2 (Fin (k+1))) ℝ :=
  (incidence k).submatrix Fin.castSucc id

/-! ### Deleting the last vertex is extension by zero -/

theorem sum_ite_castSucc {k : ℕ} (u : Fin k → ℝ) (v : Fin (k+1)) :
    ∑ i : Fin k, (if v = i.castSucc then u i else 0)
      = (Fin.snoc u 0 : Fin (k+1) → ℝ) v := by
  induction v using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact if_neg fun h => (Fin.castSucc_lt_last i).ne h.symm
  | cast j =>
    rw [Fin.snoc_castSucc]
    rw [Finset.sum_eq_single j]
    · exact if_pos rfl
    · intro b _ hb
      exact if_neg fun h => hb (Fin.castSucc_injective _ h).symm
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- **The left action of the reduced incidence matrix is a potential
difference**, with the deleted vertex given the value zero. -/
theorem vecMul_reducedIncidence {k : ℕ} (u : Fin k → ℝ) (e : Sym2 (Fin (k+1))) :
    Matrix.vecMul u (reducedIncidence k) e
      = (Fin.snoc u 0 : Fin (k+1) → ℝ) e.inf - (Fin.snoc u 0 : Fin (k+1) → ℝ) e.sup := by
  rw [Matrix.vecMul, dotProduct]
  have hterm : ∀ i : Fin k, u i * reducedIncidence k i e
      = (if e.inf = i.castSucc then u i else 0) - (if e.sup = i.castSucc then u i else 0) := by
    intro i
    rw [reducedIncidence, Matrix.submatrix_apply, id_eq, incidence_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
    sum_ite_castSucc, sum_ite_castSucc]

/-- **The reduced incidence matrix has full row rank.**  Test against the edge
joining a vertex to the deleted one. -/
theorem fullRowRank_reducedIncidence (k : ℕ) : FullRowRank (reducedIncidence k) := by
  intro u hu
  funext i
  have h := congrFun hu s(i.castSucc, Fin.last k)
  rw [vecMul_reducedIncidence, Sym2.inf_mk, Sym2.sup_mk,
    inf_eq_left.mpr (Fin.castSucc_lt_last i).le,
    sup_eq_right.mpr (Fin.castSucc_lt_last i).le, Fin.snoc_castSucc, Fin.snoc_last] at h
  simpa using h

/-! ### Total unimodularity -/

/-- **The oriented incidence matrix is totally unimodular.**

Induction on the size of the square submatrix.  A repeated row makes the
determinant vanish, so assume the rows are distinct.  If some column has at most
one nonzero entry, Laplace expansion along it reduces to a smaller submatrix of
the same matrix.  Otherwise every column has two nonzero entries — necessarily
`+1` at one endpoint and `-1` at the other — so every column sums to zero, the
all-ones vector is in the left kernel, and the determinant vanishes. -/
theorem isTotallyUnimodular_incidence (k : ℕ) : (incidence k).IsTotallyUnimodular := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g _ _
    exact isSgn_iff.mpr (Or.inr (Or.inl (by simp)))
  | succ n ih =>
    intro f g hf hg
    refine isSgn_iff.mpr ?_
    · by_cases hcol : ∃ j, ∃ i₀, ∀ i, i ≠ i₀ → (incidence k).submatrix f g i j = 0
      · -- Laplace expansion along a column with a single nonzero entry
        obtain ⟨j, i₀, hj⟩ := hcol
        rw [Matrix.det_succ_column _ j, Finset.sum_eq_single i₀]
        · refine ((isSgn_neg_one_pow _).mul (isSgn_incidence _ _ _)).mul ?_
          exact isSgn_iff.mp (ih (f ∘ i₀.succAbove) (g ∘ j.succAbove)
            (hf.comp (Fin.succAbove_right_injective))
            (hg.comp (Fin.succAbove_right_injective)))
        · intro b _ hb
          rw [hj b hb, mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i₀) h
      · -- every column has both endpoints, so the columns sum to zero
        left
        push Not at hcol
        have hzero : Matrix.vecMul (fun _ => (1 : ℝ)) ((incidence k).submatrix f g) = 0 := by
          funext j
          obtain ⟨i₁, hi₁ne, hi₁⟩ := hcol j 0
          obtain ⟨i₂, hi₂ne, hi₂⟩ := hcol j i₁
          obtain ⟨hd₁, hv₁⟩ := endpoint_of_incidence_ne_zero hi₁
          obtain ⟨-, hv₂⟩ := endpoint_of_incidence_ne_zero hi₂
          -- both endpoints of the edge `g j` are hit by `f`
          have hboth : (∃ i, f i = (g j).inf) ∧ ∃ i, f i = (g j).sup := by
            have hne : f i₂ ≠ f i₁ := fun h => hi₂ne (hf h)
            rcases hv₁ with h1 | h1 <;> rcases hv₂ with h2 | h2
            · exact absurd (h2.symm.trans h1) hne
            · exact ⟨⟨i₁, h1.symm⟩, ⟨i₂, h2.symm⟩⟩
            · exact ⟨⟨i₂, h2.symm⟩, ⟨i₁, h1.symm⟩⟩
            · exact absurd (h2.symm.trans h1) hne
          -- each indicator sums to one
          have hone : ∀ v : Fin (k+1), (∃ i, f i = v) →
              ∑ i : Fin (n+1), (if v = f i then (1 : ℝ) else 0) = 1 := by
            rintro v ⟨i₀, rfl⟩
            rw [Finset.sum_eq_single i₀]
            · exact if_pos rfl
            · intro b _ hb
              exact if_neg fun h => hb (hf h.symm)
            · intro h
              exact absurd (Finset.mem_univ i₀) h
          show ∑ i : Fin (n+1), (1 : ℝ) * (incidence k).submatrix f g i j = 0
          have hterm : ∀ i : Fin (n+1), (1 : ℝ) * (incidence k).submatrix f g i j
              = (if (g j).inf = f i then (1 : ℝ) else 0)
                - (if (g j).sup = f i then (1 : ℝ) else 0) := by
            intro i
            rw [one_mul, Matrix.submatrix_apply, incidence_apply]
          rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
            hone _ hboth.1, hone _ hboth.2, sub_self]
        have hone_ne : (fun _ => (1 : ℝ)) ≠ (0 : Fin (n+1) → ℝ) := by
          intro h
          have := congrFun h 0
          norm_num at this
        exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hone_ne, hzero⟩

theorem isTotallyUnimodular_reducedIncidence (k : ℕ) :
    (reducedIncidence k).IsTotallyUnimodular :=
  (isTotallyUnimodular_incidence k).submatrix _ _

/-! ### The graph bridge -/

theorem sym2_inf_sup {k : ℕ} (e : Sym2 (Fin (k+1))) : s(e.inf, e.sup) = e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.inf_mk, Sym2.sup_mk]
    rcases le_total a b with h | h
    · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
    · rw [inf_eq_right.mpr h, sup_eq_left.mpr h, Sym2.eq_swap]

theorem inf_eq_sup_of_isDiag {k : ℕ} {e : Sym2 (Fin (k+1))} (h : e.IsDiag) :
    e.inf = e.sup := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at h
    subst h
    rw [Sym2.inf_mk, Sym2.sup_mk, inf_idem, sup_idem]

/-- **Full row rank of the selected columns is connectivity.**

A vector in the left kernel is a potential constant along every edge and zero at
the deleted vertex; it vanishes identically exactly when the graph is connected.
No cardinality hypothesis is involved. -/
theorem fullRowRank_colsOn_reducedIncidence_iff (k : ℕ) (T : Finset (Sym2 (Fin (k+1)))) :
    FullRowRank (colsOn (reducedIncidence k) T)
      ↔ (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Connected := by
  classical
  have hvec : ∀ u : Fin k → ℝ, Matrix.vecMul u (colsOn (reducedIncidence k) T) = 0
      ↔ ∀ e ∈ T, (Fin.snoc u 0 : Fin (k+1) → ℝ) e.inf
          = (Fin.snoc u 0 : Fin (k+1) → ℝ) e.sup := by
    intro u
    constructor
    · intro h e he
      have h' : Matrix.vecMul u (reducedIncidence k) e = 0 := congrFun h ⟨e, he⟩
      rw [vecMul_reducedIncidence, sub_eq_zero] at h'
      exact h'
    · intro h
      funext j
      have h' := h j.1 j.2
      show Matrix.vecMul u (reducedIncidence k) j.1 = 0
      rw [vecMul_reducedIncidence, h', sub_self]
  have hedge : ∀ (u : Fin k → ℝ),
      (∀ e ∈ T, (Fin.snoc u 0 : Fin (k+1) → ℝ) e.inf = (Fin.snoc u 0 : Fin (k+1) → ℝ) e.sup) →
      ∀ {a b : Fin (k+1)}, s(a, b) ∈ T →
        (Fin.snoc u 0 : Fin (k+1) → ℝ) a = (Fin.snoc u 0 : Fin (k+1) → ℝ) b := by
    intro u hu a b hab
    have h := hu _ hab
    rw [Sym2.inf_mk, Sym2.sup_mk] at h
    rcases le_total a b with hle | hle
    · rwa [inf_eq_left.mpr hle, sup_eq_right.mpr hle] at h
    · rw [inf_eq_right.mpr hle, sup_eq_left.mpr hle] at h
      exact h.symm
  constructor
  · -- full row rank forces connectivity
    intro hF
    by_contra hnc
    have hex : ∃ w : Fin (k+1),
        ¬ (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Reachable w (Fin.last k) := by
      by_contra hall
      push Not at hall
      exact hnc ⟨fun a b => (hall a).trans (hall b).symm⟩
    obtain ⟨w, hw⟩ := hex
    let φ : Fin (k+1) → ℝ := fun v =>
      if (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Reachable v (Fin.last k)
        then 0 else 1
    have hφ : ∀ v : Fin (k+1), φ v =
        if (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Reachable v (Fin.last k)
          then 0 else 1 := fun _ => rfl
    have hφlast : φ (Fin.last k) = 0 := by
      rw [hφ]
      exact if_pos (SimpleGraph.Reachable.refl _)
    have hsnoc : (Fin.snoc (fun i => φ i.castSucc) 0 : Fin (k+1) → ℝ) = φ := by
      funext v
      induction v using Fin.lastCases with
      | last => rw [Fin.snoc_last, hφlast]
      | cast j => rw [Fin.snoc_castSucc]
    have hker : Matrix.vecMul (fun i => φ i.castSucc) (colsOn (reducedIncidence k) T) = 0 := by
      rw [hvec, hsnoc]
      intro e he
      by_cases hd : e.inf = e.sup
      · rw [hd]
      · have hadj : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Adj e.inf e.sup := by
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨by rw [sym2_inf_sup]; exact_mod_cast he, hd⟩
        simp only [hφ]
        by_cases hr : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Reachable
            e.inf (Fin.last k)
        · rw [if_pos hr, if_pos (hadj.symm.reachable.trans hr)]
        · rw [if_neg hr, if_neg fun hc => hr (hadj.reachable.trans hc)]
    have hzero := hF _ hker
    have hwne : w ≠ Fin.last k := fun h => hw (h ▸ SimpleGraph.Reachable.refl _)
    obtain ⟨j, rfl⟩ : ∃ j : Fin k, j.castSucc = w := by
      induction w using Fin.lastCases with
      | last => exact absurd rfl hwne
      | cast j => exact ⟨j, rfl⟩
    have hcontra : φ (Fin.castSucc j) = 0 := congrFun hzero j
    rw [hφ, if_neg hw] at hcontra
    norm_num at hcontra
  · -- connectivity forces full row rank
    intro hconn u hu
    rw [hvec] at hu
    have hconst : ∀ v w : Fin (k+1),
        (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (k+1))))).Reachable v w →
          (Fin.snoc u 0 : Fin (k+1) → ℝ) v = (Fin.snoc u 0 : Fin (k+1) → ℝ) w := by
      rintro v w ⟨p⟩
      induction p with
      | nil => rfl
      | cons hadj _ ih =>
        refine Eq.trans ?_ ih
        rw [SimpleGraph.fromEdgeSet_adj] at hadj
        exact hedge u hu (by exact_mod_cast hadj.1)
    funext i
    have h := hconst i.castSucc (Fin.last k) (hconn.preconnected _ _)
    rw [Fin.snoc_castSucc, Fin.snoc_last] at h
    exact h

/-! ### The target -/

open Classical in
/-- **The Gram minor of the reduced incidence matrix detects spanning trees.**

Loop-freeness is not proved by counting edges: a loop is a zero column, which
kills the determinant, hence full row rank, hence connectivity.  That step is
where `T.card = k` is spent — it is what makes the column set square. -/
theorem gramMinor_reducedIncidence (k : ℕ) {T : Finset (Sym2 (Fin (k+1)))} (hT : T.card = k) :
    gramMinor (reducedIncidence k) T = if IsSpanningTree (k+1) T then 1 else 0 := by
  classical
  have hcard : T.card = Fintype.card (Fin k) := by rw [hT, Fintype.card_fin]
  rw [gramMinor_of_tu (isTotallyUnimodular_reducedIncidence k) hcard]
  by_cases hst : IsSpanningTree (k+1) T
  · rw [if_pos hst, if_pos ((fullRowRank_colsOn_reducedIncidence_iff k T).mpr hst.2.2)]
  · rw [if_neg hst, if_neg ?_]
    intro hF
    refine hst ⟨fun e he hdiag => ?_, by simpa using hT,
      (fullRowRank_colsOn_reducedIncidence_iff k T).mp hF⟩
    refine not_fullRowRank_of_zero_col hcard he (fun i => ?_) hF
    rw [reducedIncidence, Matrix.submatrix_apply, id_eq]
    exact incidence_eq_zero_of_inf_eq_sup (inf_eq_sup_of_isDiag hdiag)

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerChain

/-!
# Tucker's Theorem 7: the normalized minimal triple

The setting of the case analysis of Tucker's Theorem 7 (`TuckerTheorem7Cases.lean`): a
minimal instance `(O, F)` with an asteroidal triple `x, y, z`, and the three avoiding paths
as chains (`TSPGap/TuckerChain.lean`)

* `P` from `x` to `y` in `(O, avoidSets F z)`, `Q` from `x` to `z` in `(O, avoidSets F y)`,
  `R` from `y` to `z` in `(O, avoidSets F x)`, each *shortest*;
* `R` at least as long as `P` and `Q` (Tucker's naming of the triple);
* `P`, `Q` with a common initial segment of maximal length `m` (in vertex positions:
  the vertex at position `2i` is `q i`, at position `2i - 1` is `r i`) among all shortest
  pairs — the repair of the printed proof's "circuit through `x`" (`TUCKER_DESIGN.md`).

The file provides the certificates of minimality in chain form (a vertex missed by three
avoiding chains, `no_chains_avoiding_elem`/`no_chains_avoiding_set`; every vertex lies on
one of the three paths, `mem_chains_of_minimal`), the structure `Setup` packaging the
normalized data with its `y ↔ z` symmetry `Setup.swap`, and the first facts: the paths are
induced, the avoided point is not on its path, the common prefix ends strictly before both
paths do, and the next vertices differ.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-! ### Avoiding chains -/

namespace Chain

variable {O : Finset α} {F : Finset (Finset α)} {a : α}

theorem r_memF (C : Chain O (avoidSets F a)) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ C.n) : C.r i ∈ F :=
  (mem_avoidSets.mp (C.r_mem i h1 hi)).1

theorem r_avoid (C : Chain O (avoidSets F a)) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ C.n) : a ∉ C.r i :=
  (mem_avoidSets.mp (C.r_mem i h1 hi)).2

/-- The avoided element is not on a nontrivial avoiding chain. -/
theorem ne_avoid (C : Chain O (avoidSets F a)) (hn : 1 ≤ C.n) {i : ℕ} (hi : i ≤ C.n) :
    C.q i ≠ a := by
  intro h
  rcases Nat.lt_or_ge i C.n with hlt | hge
  · have := C.left_mem i hlt
    rw [h] at this
    exact C.r_avoid (by omega) (by omega : i + 1 ≤ C.n) this
  · have : i = C.n := by omega
    subst this
    have := C.right_mem (C.n - 1) (by omega)
    rw [show C.n - 1 + 1 = C.n by omega, h] at this
    exact C.r_avoid (by omega) le_rfl this

/-- An avoiding chain none of whose sets contains `b` avoids `b`. -/
def reavoid (C : Chain O (avoidSets F a)) (b : α) (hb : ∀ i, 1 ≤ i → i ≤ C.n → b ∉ C.r i) :
    Chain O (avoidSets F b) :=
  C.restrict (fun i hi => C.q_mem i hi)
    (fun i h1 hi => mem_avoidSets.mpr ⟨C.r_memF h1 hi, hb i h1 hi⟩)

@[simp] theorem reavoid_n (C : Chain O (avoidSets F a)) (b : α)
    (hb : ∀ i, 1 ≤ i → i ≤ C.n → b ∉ C.r i) : (C.reavoid b hb).n = C.n := rfl
@[simp] theorem reavoid_q (C : Chain O (avoidSets F a)) (b : α)
    (hb : ∀ i, 1 ≤ i → i ≤ C.n → b ∉ C.r i) : (C.reavoid b hb).q = C.q := rfl
@[simp] theorem reavoid_r (C : Chain O (avoidSets F a)) (b : α)
    (hb : ∀ i, 1 ≤ i → i ≤ C.n → b ∉ C.r i) : (C.reavoid b hb).r = C.r := rfl

omit [DecidableEq α] in
theorem reverse_isShortest {C : Chain O F} (hC : C.IsShortest) : C.reverse.IsShortest := by
  intro D hD0 hDn
  simp only [reverse_q, Nat.sub_zero] at hD0 hDn
  have := hC D.reverse (by simp [reverse_q, hDn]) (by simp [reverse_q, hD0])
  simpa using this

end Chain

/-! ### Symmetries of a triple -/

omit [DecidableEq α] in
theorem IsAsteroidalTriple.symm_yz {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (h : IsAsteroidalTriple O F x y z) : IsAsteroidalTriple O F x z y :=
  ⟨h.x_mem, h.z_mem, h.y_mem, h.ne_xz, h.ne_yz.symm, h.ne_xy, h.path_xz, h.path_xy,
    h.path_yz.symm⟩

omit [DecidableEq α] in
/-- The cyclic rotation `(x, y, z) ↦ (y, z, x)`. -/
theorem IsAsteroidalTriple.rot {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (h : IsAsteroidalTriple O F x y z) : IsAsteroidalTriple O F y z x :=
  ⟨h.y_mem, h.z_mem, h.x_mem, h.ne_yz, h.ne_xz.symm, h.ne_xy.symm, h.path_yz, h.path_xy.symm,
    h.path_xz.symm⟩

omit [DecidableEq α] in
theorem IsMinimalTriple.symm_yz {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (h : IsMinimalTriple O F x y z) : IsMinimalTriple O F x z y :=
  ⟨h.triple.symm_yz, h.min⟩

omit [DecidableEq α] in
theorem IsMinimalTriple.rot {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (h : IsMinimalTriple O F x y z) : IsMinimalTriple O F y z x :=
  ⟨h.triple.rot, h.min⟩

/-! ### Certificates of minimality, in chain form -/

/-- Three avoiding chains whose vertices lie in `(O', F')` give the triple in `(O', F')`. -/
theorem triple_of_chains {O O' : Finset α} {F F' : Finset (Finset α)} {x y z : α}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (P : Chain O (avoidSets F z)) (hP0 : P.q 0 = x) (hPn : P.q P.n = y)
    (Q : Chain O (avoidSets F y)) (hQ0 : Q.q 0 = x) (hQn : Q.q Q.n = z)
    (R : Chain O (avoidSets F x)) (hR0 : R.q 0 = y) (hRn : R.q R.n = z)
    (hOP : ∀ i, i ≤ P.n → P.q i ∈ O') (hFP : ∀ i, 1 ≤ i → i ≤ P.n → P.r i ∈ F')
    (hOQ : ∀ i, i ≤ Q.n → Q.q i ∈ O') (hFQ : ∀ i, 1 ≤ i → i ≤ Q.n → Q.r i ∈ F')
    (hOR : ∀ i, i ≤ R.n → R.q i ∈ O') (hFR : ∀ i, 1 ≤ i → i ≤ R.n → R.r i ∈ F') :
    IsAsteroidalTriple O' F' x y z := by
  have hx : x ∈ O' := hP0 ▸ hOP 0 (Nat.zero_le _)
  have hy : y ∈ O' := hPn ▸ hOP P.n le_rfl
  have hz : z ∈ O' := hQn ▸ hOQ Q.n le_rfl
  refine ⟨hx, hy, hz, hxy, hyz, hxz, ?_, ?_, ?_⟩
  · rw [avoidingPath_iff_chain hz, Chain.avoidChain_iff hx]
    exact ⟨P.restrict hOP (fun i h1 hi => mem_avoidSets.mpr ⟨hFP i h1 hi, P.r_avoid h1 hi⟩),
      hP0, hPn⟩
  · rw [avoidingPath_iff_chain hy, Chain.avoidChain_iff hx]
    exact ⟨Q.restrict hOQ (fun i h1 hi => mem_avoidSets.mpr ⟨hFQ i h1 hi, Q.r_avoid h1 hi⟩),
      hQ0, hQn⟩
  · rw [avoidingPath_iff_chain hx, Chain.avoidChain_iff hy]
    exact ⟨R.restrict hOR (fun i h1 hi => mem_avoidSets.mpr ⟨hFR i h1 hi, R.r_avoid h1 hi⟩),
      hR0, hRn⟩

/-- **Deleted-element certificate**: in a minimal instance, three avoiding chains none of
which uses the element `r` cannot exist. -/
theorem no_chains_avoiding_elem {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (hmin : IsMinimalTriple O F x y z) {r : α} (hr : r ∈ O)
    (P : Chain O (avoidSets F z)) (hP0 : P.q 0 = x) (hPn : P.q P.n = y)
    (hP : ∀ i, i ≤ P.n → P.q i ≠ r)
    (Q : Chain O (avoidSets F y)) (hQ0 : Q.q 0 = x) (hQn : Q.q Q.n = z)
    (hQ : ∀ i, i ≤ Q.n → Q.q i ≠ r)
    (R : Chain O (avoidSets F x)) (hR0 : R.q 0 = y) (hRn : R.q R.n = z)
    (hR : ∀ i, i ≤ R.n → R.q i ≠ r) : False := by
  have hlt : (O.erase r).card < O.card := Finset.card_erase_lt_of_mem hr
  refine hmin.min (O.erase r) (Finset.erase_subset _ _) F le_rfl (by omega) x y z
    (triple_of_chains hmin.triple.ne_xy hmin.triple.ne_yz hmin.triple.ne_xz P hP0 hPn Q hQ0 hQn
      R hR0 hRn ?_ ?_ ?_ ?_ ?_ ?_)
  · exact fun i hi => Finset.mem_erase.mpr ⟨hP i hi, P.q_mem i hi⟩
  · exact fun i h1 hi => P.r_memF h1 hi
  · exact fun i hi => Finset.mem_erase.mpr ⟨hQ i hi, Q.q_mem i hi⟩
  · exact fun i h1 hi => Q.r_memF h1 hi
  · exact fun i hi => Finset.mem_erase.mpr ⟨hR i hi, R.q_mem i hi⟩
  · exact fun i h1 hi => R.r_memF h1 hi

/-- **Deleted-set certificate**: in a minimal instance, three avoiding chains none of which
uses the set `r` cannot exist. -/
theorem no_chains_avoiding_set {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (hmin : IsMinimalTriple O F x y z) {r : Finset α} (hr : r ∈ F)
    (P : Chain O (avoidSets F z)) (hP0 : P.q 0 = x) (hPn : P.q P.n = y)
    (hP : ∀ i, 1 ≤ i → i ≤ P.n → P.r i ≠ r)
    (Q : Chain O (avoidSets F y)) (hQ0 : Q.q 0 = x) (hQn : Q.q Q.n = z)
    (hQ : ∀ i, 1 ≤ i → i ≤ Q.n → Q.r i ≠ r)
    (R : Chain O (avoidSets F x)) (hR0 : R.q 0 = y) (hRn : R.q R.n = z)
    (hR : ∀ i, 1 ≤ i → i ≤ R.n → R.r i ≠ r) : False := by
  have hlt : (F.erase r).card < F.card := Finset.card_erase_lt_of_mem hr
  refine hmin.min O le_rfl (F.erase r) (Finset.erase_subset _ _) (by omega) x y z
    (triple_of_chains hmin.triple.ne_xy hmin.triple.ne_yz hmin.triple.ne_xz P hP0 hPn Q hQ0 hQn
      R hR0 hRn ?_ ?_ ?_ ?_ ?_ ?_)
  · exact fun i hi => P.q_mem i hi
  · exact fun i h1 hi => Finset.mem_erase.mpr ⟨hP i h1 hi, P.r_memF h1 hi⟩
  · exact fun i hi => Q.q_mem i hi
  · exact fun i h1 hi => Finset.mem_erase.mpr ⟨hQ i h1 hi, Q.r_memF h1 hi⟩
  · exact fun i hi => R.q_mem i hi
  · exact fun i h1 hi => Finset.mem_erase.mpr ⟨hR i h1 hi, R.r_memF h1 hi⟩

/-- **Every vertex of a minimal instance lies on the three avoiding chains.** -/
theorem mem_chains_of_minimal {O : Finset α} {F : Finset (Finset α)} {x y z : α}
    (hmin : IsMinimalTriple O F x y z)
    (P : Chain O (avoidSets F z)) (hP0 : P.q 0 = x) (hPn : P.q P.n = y)
    (Q : Chain O (avoidSets F y)) (hQ0 : Q.q 0 = x) (hQn : Q.q Q.n = z)
    (R : Chain O (avoidSets F x)) (hR0 : R.q 0 = y) (hRn : R.q R.n = z) :
    (∀ a ∈ O, (∃ i, i ≤ P.n ∧ P.q i = a) ∨ (∃ i, i ≤ Q.n ∧ Q.q i = a) ∨
        ∃ i, i ≤ R.n ∧ R.q i = a) ∧
      ∀ S ∈ F, (∃ i, 1 ≤ i ∧ i ≤ P.n ∧ P.r i = S) ∨ (∃ i, 1 ≤ i ∧ i ≤ Q.n ∧ Q.r i = S) ∨
        ∃ i, 1 ≤ i ∧ i ≤ R.n ∧ R.r i = S := by
  constructor
  · intro a ha
    by_contra hcon
    have h1 : ¬ ∃ i, i ≤ P.n ∧ P.q i = a := fun h => hcon (Or.inl h)
    have h2 : ¬ ∃ i, i ≤ Q.n ∧ Q.q i = a := fun h => hcon (Or.inr (Or.inl h))
    have h3 : ¬ ∃ i, i ≤ R.n ∧ R.q i = a := fun h => hcon (Or.inr (Or.inr h))
    exact no_chains_avoiding_elem hmin ha P hP0 hPn (fun i hi e => h1 ⟨i, hi, e⟩)
      Q hQ0 hQn (fun i hi e => h2 ⟨i, hi, e⟩) R hR0 hRn (fun i hi e => h3 ⟨i, hi, e⟩)
  · intro S hS
    by_contra hcon
    have h1 : ¬ ∃ i, 1 ≤ i ∧ i ≤ P.n ∧ P.r i = S := fun h => hcon (Or.inl h)
    have h2 : ¬ ∃ i, 1 ≤ i ∧ i ≤ Q.n ∧ Q.r i = S := fun h => hcon (Or.inr (Or.inl h))
    have h3 : ¬ ∃ i, 1 ≤ i ∧ i ≤ R.n ∧ R.r i = S := fun h => hcon (Or.inr (Or.inr h))
    exact no_chains_avoiding_set hmin hS P hP0 hPn (fun i h1' hi e => h1 ⟨i, h1', hi, e⟩)
      Q hQ0 hQn (fun i h1' hi e => h2 ⟨i, h1', hi, e⟩) R hR0 hRn
      (fun i h1' hi e => h3 ⟨i, h1', hi, e⟩)

/-! ### The common prefix -/

/-- The chains `P` and `Q` agree on the first `m` vertex positions (position `2i` is
`q i`, position `2i - 1` is `r i`), and both have at least `m` positions. -/
def IsPrefix {O : Finset α} {F₁ F₂ : Finset (Finset α)} (P : Chain O F₁) (Q : Chain O F₂)
    (m : ℕ) : Prop :=
  m ≤ 2 * P.n ∧ m ≤ 2 * Q.n ∧ (∀ i, 2 * i ≤ m → P.q i = Q.q i) ∧
    ∀ i, 1 ≤ i → 2 * i ≤ m + 1 → P.r i = Q.r i

omit [DecidableEq α] in
theorem IsPrefix.symm {O : Finset α} {F₁ F₂ : Finset (Finset α)} {P : Chain O F₁}
    {Q : Chain O F₂} {m : ℕ} (h : IsPrefix P Q m) : IsPrefix Q P m :=
  ⟨h.2.1, h.1, fun i hi => (h.2.2.1 i hi).symm, fun i h1 hi => (h.2.2.2 i h1 hi).symm⟩

omit [DecidableEq α] in
theorem IsPrefix.mono {O : Finset α} {F₁ F₂ : Finset (Finset α)} {P : Chain O F₁}
    {Q : Chain O F₂} {m m' : ℕ} (h : IsPrefix P Q m) (hm : m' ≤ m) : IsPrefix P Q m' :=
  ⟨hm.trans h.1, hm.trans h.2.1, fun i hi => h.2.2.1 i (by omega),
    fun i h1 hi => h.2.2.2 i h1 (by omega)⟩

omit [DecidableEq α] in
theorem isPrefix_zero {O : Finset α} {F₁ F₂ : Finset (Finset α)} {P : Chain O F₁}
    {Q : Chain O F₂} (h : P.q 0 = Q.q 0) : IsPrefix P Q 0 :=
  ⟨Nat.zero_le _, Nat.zero_le _, fun i hi => by
    obtain rfl : i = 0 := by omega
    exact h, fun i h1 hi => by omega⟩

/-! ### The normalized triple -/

/-- The normalized data of Tucker's Theorem 7: a minimal instance with an asteroidal
triple `x, y, z`, shortest avoiding chains `P : x ⇝ y`, `Q : x ⇝ z`, `R : y ⇝ z`, with `R`
longest and `P, Q` of maximal common prefix `m` among shortest pairs. -/
structure Setup (O : Finset α) (F : Finset (Finset α)) (x y z : α) where
  hmin : IsMinimalTriple O F x y z
  P : Chain O (avoidSets F z)
  Q : Chain O (avoidSets F y)
  R : Chain O (avoidSets F x)
  P0 : P.q 0 = x
  Pn : P.q P.n = y
  Q0 : Q.q 0 = x
  Qn : Q.q Q.n = z
  R0 : R.q 0 = y
  Rn : R.q R.n = z
  P_short : P.IsShortest
  Q_short : Q.IsShortest
  R_short : R.IsShortest
  PR : P.n ≤ R.n
  QR : Q.n ≤ R.n
  m : ℕ
  prefix_ : IsPrefix P Q m
  prefix_max : ∀ (P' : Chain O (avoidSets F z)) (Q' : Chain O (avoidSets F y)),
    P'.q 0 = x → P'.q P'.n = y → P'.IsShortest → Q'.q 0 = x → Q'.q Q'.n = z → Q'.IsShortest →
    ∀ m', IsPrefix P' Q' m' → m' ≤ m

namespace Setup

variable {O : Finset α} {F : Finset (Finset α)} {x y z : α}

/-- The `y ↔ z` symmetry. -/
def swap (S : Setup O F x y z) : Setup O F x z y where
  hmin := S.hmin.symm_yz
  P := S.Q
  Q := S.P
  R := S.R.reverse
  P0 := S.Q0
  Pn := S.Qn
  Q0 := S.P0
  Qn := S.Pn
  R0 := by simp [Chain.reverse_q, S.Rn]
  Rn := by simp [Chain.reverse_q, S.R0]
  P_short := S.Q_short
  Q_short := S.P_short
  R_short := Chain.reverse_isShortest S.R_short
  PR := S.QR
  QR := S.PR
  m := S.m
  prefix_ := S.prefix_.symm
  prefix_max := fun P' Q' hP0 hPn hP hQ0 hQn hQ m' h =>
    S.prefix_max Q' P' hQ0 hQn hQ hP0 hPn hP m' h.symm

/-! ### Existence of a normalized setup -/

/-- The setup from three shortest avoiding chains with the last one longest. -/
theorem exists_of_shortest (hmin : IsMinimalTriple O F x y z)
    (P₀ : Chain O (avoidSets F z)) (hP0 : P₀.q 0 = x) (hPn : P₀.q P₀.n = y) (hP : P₀.IsShortest)
    (Q₀ : Chain O (avoidSets F y)) (hQ0 : Q₀.q 0 = x) (hQn : Q₀.q Q₀.n = z) (hQ : Q₀.IsShortest)
    (R₀ : Chain O (avoidSets F x)) (hR0 : R₀.q 0 = y) (hRn : R₀.q R₀.n = z) (hR : R₀.IsShortest)
    (hPR : P₀.n ≤ R₀.n) (hQR : Q₀.n ≤ R₀.n) : Nonempty (Setup O F x y z) := by
  classical
  let p : ℕ → Prop := fun m => ∃ (P' : Chain O (avoidSets F z)) (Q' : Chain O (avoidSets F y)),
    P'.q 0 = x ∧ P'.q P'.n = y ∧ P'.IsShortest ∧ Q'.q 0 = x ∧ Q'.q Q'.n = z ∧ Q'.IsShortest ∧
      IsPrefix P' Q' m
  have hp0 : p 0 := ⟨P₀, Q₀, hP0, hPn, hP, hQ0, hQn, hQ, isPrefix_zero (hP0.trans hQ0.symm)⟩
  have hbound : ∀ m, p m → m ≤ 2 * P₀.n := by
    rintro m ⟨P', Q', hP0', hPn', hP', hQ0', hQn', hQ', hpre⟩
    have : P₀.n ≤ P'.n := hP P' (hP0'.trans hP0.symm) (hPn'.trans hPn.symm)
    have : P'.n ≤ P₀.n := hP' P₀ (hP0.trans hP0'.symm) (hPn.trans hPn'.symm)
    have := hpre.1
    omega
  obtain ⟨P, Q, hP0', hPn', hP', hQ0', hQn', hQ', hpre⟩ :
      p (Nat.findGreatest p (2 * P₀.n)) :=
    Nat.findGreatest_spec (P := p) (Nat.zero_le _) hp0
  refine ⟨⟨hmin, P, Q, R₀, hP0', hPn', hQ0', hQn', hR0, hRn, hP', hQ', hR, ?_, ?_,
    Nat.findGreatest p (2 * P₀.n), hpre, ?_⟩⟩
  · exact (hP' P₀ (hP0.trans hP0'.symm) (hPn.trans hPn'.symm)).trans hPR
  · exact (hQ' Q₀ (hQ0.trans hQ0'.symm) (hQn.trans hQn'.symm)).trans hQR
  · intro P' Q' hP0' hPn' hP' hQ0' hQn' hQ' m' hpre'
    have hm' : p m' := ⟨P', Q', hP0', hPn', hP', hQ0', hQn', hQ', hpre'⟩
    exact Nat.le_findGreatest (hbound m' hm') hm'

/-- Every minimal triple has a normalized setup, after renaming the triple. -/
theorem exists_of_minimal (hmin : IsMinimalTriple O F x y z) :
    ∃ x' y' z', Nonempty (Setup O F x' y' z') := by
  have ht := hmin.triple
  obtain ⟨P₀, hP0, hPn, hP⟩ := Chain.exists_shortest
    ((Chain.avoidChain_iff ht.x_mem).mp ((avoidingPath_iff_chain ht.z_mem).mp ht.path_xy))
  obtain ⟨Q₀, hQ0, hQn, hQ⟩ := Chain.exists_shortest
    ((Chain.avoidChain_iff ht.x_mem).mp ((avoidingPath_iff_chain ht.y_mem).mp ht.path_xz))
  obtain ⟨R₀, hR0, hRn, hR⟩ := Chain.exists_shortest
    ((Chain.avoidChain_iff ht.y_mem).mp ((avoidingPath_iff_chain ht.x_mem).mp ht.path_yz))
  by_cases h1 : P₀.n ≤ R₀.n ∧ Q₀.n ≤ R₀.n
  · exact ⟨x, y, z, exists_of_shortest hmin P₀ hP0 hPn hP Q₀ hQ0 hQn hQ R₀ hR0 hRn hR h1.1 h1.2⟩
  by_cases h2 : P₀.n ≤ Q₀.n ∧ R₀.n ≤ Q₀.n
  · -- `Q₀ : x ⇝ z` is longest: the triple `(y, x, z)`
    refine ⟨y, x, z, exists_of_shortest hmin.rot.symm_yz P₀.reverse (by simp [hPn])
      (by simp [hP0]) (Chain.reverse_isShortest hP) R₀ hR0 hRn hR Q₀ hQ0 hQn hQ ?_ ?_⟩
    · simpa using h2.1
    · exact h2.2
  · -- `P₀ : x ⇝ y` is longest: the triple `(z, x, y)`
    have h3 : Q₀.n ≤ P₀.n ∧ R₀.n ≤ P₀.n := by omega
    refine ⟨z, x, y, exists_of_shortest hmin.rot.rot Q₀.reverse (by simp [hQn])
      (by simp [hQ0]) (Chain.reverse_isShortest hQ) R₀.reverse (by simp [hRn]) (by simp [hR0])
      (Chain.reverse_isShortest hR) P₀ hP0 hPn hP ?_ ?_⟩
    · simpa using h3.1
    · simpa using h3.2

/-! ### First facts -/

theorem ne_xy (S : Setup O F x y z) : x ≠ y := S.hmin.triple.ne_xy
theorem ne_yz (S : Setup O F x y z) : y ≠ z := S.hmin.triple.ne_yz
theorem ne_xz (S : Setup O F x y z) : x ≠ z := S.hmin.triple.ne_xz
theorem x_mem (S : Setup O F x y z) : x ∈ O := S.hmin.triple.x_mem
theorem y_mem (S : Setup O F x y z) : y ∈ O := S.hmin.triple.y_mem
theorem z_mem (S : Setup O F x y z) : z ∈ O := S.hmin.triple.z_mem

theorem P_pos (S : Setup O F x y z) : 1 ≤ S.P.n :=
  Chain.pos_of_ne (by rw [S.P0, S.Pn]; exact S.ne_xy)
theorem Q_pos (S : Setup O F x y z) : 1 ≤ S.Q.n :=
  Chain.pos_of_ne (by rw [S.Q0, S.Qn]; exact S.ne_xz)
theorem R_pos (S : Setup O F x y z) : 1 ≤ S.R.n :=
  Chain.pos_of_ne (by rw [S.R0, S.Rn]; exact S.ne_yz)

theorem P_ind (S : Setup O F x y z) : S.P.IsInduced := S.P_short.isInduced
theorem Q_ind (S : Setup O F x y z) : S.Q.IsInduced := S.Q_short.isInduced
theorem R_ind (S : Setup O F x y z) : S.R.IsInduced := S.R_short.isInduced

/-- `z` is not on `P`. -/
theorem P_ne_z (S : Setup O F x y z) {i : ℕ} (hi : i ≤ S.P.n) : S.P.q i ≠ z :=
  S.P.ne_avoid S.P_pos hi
/-- `y` is not on `Q`. -/
theorem Q_ne_y (S : Setup O F x y z) {i : ℕ} (hi : i ≤ S.Q.n) : S.Q.q i ≠ y :=
  S.Q.ne_avoid S.Q_pos hi
/-- `x` is not on `R`. -/
theorem R_ne_x (S : Setup O F x y z) {i : ℕ} (hi : i ≤ S.R.n) : S.R.q i ≠ x :=
  S.R.ne_avoid S.R_pos hi

theorem prefix_q (S : Setup O F x y z) {i : ℕ} (hi : 2 * i ≤ S.m) : S.P.q i = S.Q.q i :=
  S.prefix_.2.2.1 i hi
theorem prefix_r (S : Setup O F x y z) {i : ℕ} (h1 : 1 ≤ i) (hi : 2 * i ≤ S.m + 1) :
    S.P.r i = S.Q.r i :=
  S.prefix_.2.2.2 i h1 hi

/-- The common prefix ends strictly before `P` does. -/
theorem m_lt_P (S : Setup O F x y z) : S.m < 2 * S.P.n := by
  have h := S.prefix_.1
  by_contra hlt
  have hm : S.m = 2 * S.P.n := by omega
  have := S.prefix_q (i := S.P.n) (by omega)
  rw [S.Pn] at this
  exact S.Q_ne_y (by have := S.prefix_.2.1; omega) this.symm

/-- The common prefix ends strictly before `Q` does. -/
theorem m_lt_Q (S : Setup O F x y z) : S.m < 2 * S.Q.n := by
  have h := S.prefix_.2.1
  by_contra hlt
  have hm : S.m = 2 * S.Q.n := by omega
  have := S.prefix_q (i := S.Q.n) (by omega)
  rw [S.Qn] at this
  exact S.P_ne_z (by have := S.prefix_.1; omega) this

/-- After an even prefix `m = 2h` the next sets differ. -/
theorem div_even (S : Setup O F x y z) {h : ℕ} (hm : S.m = 2 * h) : S.P.r (h + 1) ≠ S.Q.r (h + 1) := by
  intro heq
  have h1 := S.m_lt_P
  have h2 := S.m_lt_Q
  have := S.prefix_max S.P S.Q S.P0 S.Pn S.P_short S.Q0 S.Qn S.Q_short (S.m + 1)
    ⟨by omega, by omega, fun i hi => S.prefix_q (by omega), fun i hi1 hi => ?_⟩
  · omega
  · rcases Nat.lt_or_ge (2 * i) (S.m + 2) with hlt | hge
    · exact S.prefix_r hi1 (by omega)
    · have : i = h + 1 := by omega
      subst this; exact heq

/-- After an odd prefix `m = 2h + 1` the next elements differ. -/
theorem div_odd (S : Setup O F x y z) {h : ℕ} (hm : S.m = 2 * h + 1) : S.P.q (h + 1) ≠ S.Q.q (h + 1) := by
  intro heq
  have h1 := S.m_lt_P
  have h2 := S.m_lt_Q
  have := S.prefix_max S.P S.Q S.P0 S.Pn S.P_short S.Q0 S.Qn S.Q_short (S.m + 1)
    ⟨by omega, by omega, fun i hi => ?_, fun i hi1 hi => S.prefix_r hi1 (by omega)⟩
  · omega
  · rcases Nat.lt_or_ge (2 * i) (S.m + 1) with hlt | hge
    · exact S.prefix_q (by omega)
    · have : i = h + 1 := by omega
      subst this; exact heq

end Setup

end Tucker

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OneSideLaminar

/-!
# The polygon of a one-side component, read from the root as intervals

KKO21 §4.2 work with atoms `a₀, …, a_{m−1}` around the cycle, `a₀` the root, and identify
every cut with the interval `[ℓ(A), r(A))` of atoms it contains.  This module sets that
up for a `PolygonRep` with a root index `r` and no inside atoms (`PolygonRep.Rooted`):

* `pos r i = (i − r).val` is the offset of an index from the root, `idx v` the index of the
  atom holding a vertex `v`, and `ivl a b` the union of the atoms at offsets `a … b`;
* a member `S` occupies the offsets `lo S … hi S` with `1 ≤ lo S`, `hi S < m`
  (`mem_iff_pos`, `eq_ivl`): the arc of `S` avoids the root, so read from the root it does
  not wrap;
* the set relations between members are interval arithmetic: `subset_iff`,
  `disjoint_iff`, `crossing_iff`, and the two sides of a crossing
  (`crossesOnLeft_iff`, `crossesOnRight_iff`);
* endpoint incidence (`exists_endpoint`): every boundary between two consecutive atoms is
  an endpoint of some member, because the two atoms are distinct.

Everything downstream (the hierarchies, the adjacent-pair estimate, Theorem A.3) is
stated in these coordinates, where the case analyses are `omega`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {𝒞 : Finset (Finset (Fin n))}

/-! ### `Fin` arithmetic, in `if` form -/

theorem Fin.val_add_ite {m : ℕ} (a b : Fin m) :
    (a + b).val = if a.val + b.val < m then a.val + b.val else a.val + b.val - m := by
  have ha := a.isLt
  have hb := b.isLt
  rw [Fin.val_add]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Fin.val_sub_ite {m : ℕ} (a b : Fin m) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + m - b.val := by
  have ha := a.isLt
  have hb := b.isLt
  rw [Fin.val_sub]
  split_ifs with h
  · rw [show m - b.val + a.val = (a.val - b.val) + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **A rooted polygon with no inside atoms**: a root index and Lemma A.1's covering. -/
structure Rooted where
  /-- The index of the root atom. -/
  r : Fin P.m
  hr : P.out r = P.rootAtom
  /-- Every vertex lies in an outside atom (Lemma A.1). -/
  cover : ∀ v : Fin n, ∃ i, v ∈ P.out i

variable (R : P.Rooted)

/-! ### Offsets from the root -/

/-- The offset of an index from the root. -/
def pos (i : Fin P.m) : ℕ := (i - R.r).val

theorem pos_lt (i : Fin P.m) : P.pos R i < P.m := (i - R.r).isLt

theorem pos_root : P.pos R R.r = 0 := by simp [pos]

theorem pos_eq_iff {i j : Fin P.m} : P.pos R i = P.pos R j ↔ i = j :=
  ⟨fun h => sub_left_inj.mp (Fin.ext h), fun h => h ▸ rfl⟩

theorem pos_eq_zero_iff {i : Fin P.m} : P.pos R i = 0 ↔ i = R.r := by
  rw [← P.pos_root R, pos_eq_iff]

/-- The index at a given offset. -/
def idxAt (t : ℕ) (ht : t < P.m) : Fin P.m := R.r + ⟨t, ht⟩

theorem pos_idxAt {t : ℕ} (ht : t < P.m) : P.pos R (P.idxAt R t ht) = t := by
  simp [pos, idxAt]

/-- The index of the atom holding a vertex. -/
noncomputable def idx (v : Fin n) : Fin P.m := Classical.choose (R.cover v)

theorem mem_out_idx (v : Fin n) : v ∈ P.out (P.idx R v) := Classical.choose_spec (R.cover v)

theorem idx_eq_of_mem {v : Fin n} {i : Fin P.m} (hv : v ∈ P.out i) : P.idx R v = i := by
  by_contra h
  exact disjoint_left.mp (atoms_disjoint (P.out_atom _) (P.out_atom i)
    fun e => h (P.out_injective e)) (P.mem_out_idx R v) hv

theorem mem_out_iff {v : Fin n} {i : Fin P.m} : v ∈ P.out i ↔ P.idx R v = i :=
  ⟨P.idx_eq_of_mem R, fun h => h ▸ P.mem_out_idx R v⟩

/-- The union of the atoms at offsets `a … b`. -/
noncomputable def ivl (a b : ℕ) : Finset (Fin n) :=
  univ.filter fun v => a ≤ P.pos R (P.idx R v) ∧ P.pos R (P.idx R v) ≤ b

theorem mem_ivl {a b : ℕ} {v : Fin n} :
    v ∈ P.ivl R a b ↔ a ≤ P.pos R (P.idx R v) ∧ P.pos R (P.idx R v) ≤ b := by
  simp [ivl]

/-- An atom is the singleton interval at its offset. -/
theorem out_idxAt_eq_ivl {t : ℕ} (ht : t < P.m) : P.out (P.idxAt R t ht) = P.ivl R t t := by
  ext v
  rw [mem_ivl, P.mem_out_iff R]
  constructor
  · intro h
    rw [h, P.pos_idxAt R ht]
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    have : P.pos R (P.idx R v) = t := le_antisymm h2 h1
    rw [← P.pos_idxAt R ht] at this
    exact (P.pos_eq_iff R).mp this

theorem out_eq_ivl (i : Fin P.m) : P.out i = P.ivl R (P.pos R i) (P.pos R i) := by
  have h : i = P.idxAt R (P.pos R i) (P.pos_lt R i) := by
    rw [← P.pos_eq_iff R, P.pos_idxAt R]
  conv_lhs => rw [h]
  exact P.out_idxAt_eq_ivl R _

theorem ivl_nonempty {a b : ℕ} (hab : a ≤ b) (hb : b < P.m) : (P.ivl R a b).Nonempty := by
  obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R a (by omega))
  refine ⟨v, (P.mem_ivl R).mpr ?_⟩
  rw [(P.mem_out_iff R).mp hv, P.pos_idxAt R]
  exact ⟨le_rfl, hab⟩

/-- The root lies in no interval of positive offsets. -/
theorem root_notMem_ivl {a b : ℕ} (ha : 1 ≤ a) {v : Fin n} (hv : v ∈ P.rootAtom) :
    v ∉ P.ivl R a b := by
  intro h
  rw [mem_ivl] at h
  have : P.idx R v = R.r := P.idx_eq_of_mem R (R.hr ▸ hv)
  rw [this, P.pos_root R] at h
  omega

/-! ### Members as intervals -/

/-- The offset of the first atom of a member. -/
def lo (S : Finset (Fin n)) : ℕ := P.pos R (P.start S)

/-- The offset of the last atom of a member. -/
def hi (S : Finset (Fin n)) : ℕ := P.lo R S + P.len S - 1

variable {S : Finset (Fin n)}

/-- The root's index is outside the arc of any member. -/
theorem root_notMem_arc' (hS : S ∈ 𝒞) : R.r ∉ arcSet (P.start S) (P.len S) := by
  intro hc
  have hsub : P.out R.r ⊆ S := (P.outside_eq_arc S hS R.r).mpr hc
  obtain ⟨v, hv⟩ := P.out_nonempty R.r
  have hdisj := P.rootAtom_disjoint S hS
  rw [← R.hr] at hdisj
  exact (disjoint_left.mp hdisj hv) (hsub hv)

theorem root_val_sub_start (hS : S ∈ 𝒞) : P.len S ≤ (R.r - P.start S).val := by
  have h := P.root_notMem_arc' R hS
  rwa [mem_arcSet_compl] at h

theorem one_le_lo (hS : S ∈ 𝒞) : 1 ≤ P.lo R S := by
  have h2 := P.two_le_len S hS
  have hr := P.root_val_sub_start R hS
  by_contra h
  have h0 : (P.start S - R.r).val = 0 := by unfold lo pos at h; omega
  have : P.start S = R.r := sub_eq_zero.mp (Fin.ext h0)
  rw [this, sub_self] at hr
  simp at hr
  omega

theorem lo_add_len_le (hS : S ∈ 𝒞) : P.lo R S + P.len S ≤ P.m := by
  have hr := P.root_val_sub_start R hS
  have hne : P.start S ≠ R.r := by
    intro e
    rw [e, sub_self] at hr
    have := P.two_le_len S hS
    simp at hr
    omega
  have := val_sub_add_val_sub (m := P.m) hne
  unfold lo pos
  omega

theorem hi_lt (hS : S ∈ 𝒞) : P.hi R S < P.m := by
  have := P.lo_add_len_le R hS
  have := P.two_le_len S hS
  unfold hi
  omega

theorem lo_lt_hi (hS : S ∈ 𝒞) : P.lo R S < P.hi R S := by
  have := P.two_le_len S hS
  unfold hi
  omega

/-- Arc membership, read from the root: the arc of a member does not wrap. -/
theorem mem_arc_iff_pos (hS : S ∈ 𝒞) (i : Fin P.m) :
    i ∈ arcSet (P.start S) (P.len S) ↔ P.lo R S ≤ P.pos R i ∧ P.pos R i ≤ P.hi R S := by
  have hm := P.hm
  have hlen := P.two_le_len S hS
  have hlo := P.one_le_lo R hS
  have hsum := P.lo_add_len_le R hS
  have hrel := val_sub_rel i R.r (P.start S)
  have hrel' := val_sub_rel i (P.start S) R.r
  have hne : P.start S ≠ R.r := by
    intro e
    have := P.one_le_lo R hS
    unfold lo pos at this
    rw [e, sub_self] at this
    simp at this
  have hcirc := val_sub_add_val_sub (m := P.m) hne
  have hi1 := (i - P.start S).isLt
  have hi2 := (i - R.r).isLt
  rw [mem_arcSet]
  unfold hi lo pos at *
  constructor
  · intro h
    rw [Nat.mod_eq_of_lt (by omega)] at hrel
    omega
  · rintro ⟨h1, h2⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hrel'
    omega

/-- Membership in a member, by the offset of the vertex's atom. -/
theorem mem_iff_pos (hS : S ∈ 𝒞) (v : Fin n) :
    v ∈ S ↔ P.lo R S ≤ P.pos R (P.idx R v) ∧ P.pos R (P.idx R v) ≤ P.hi R S := by
  rw [← P.mem_arc_iff_pos R hS, ← P.outside_eq_arc S hS]
  constructor
  · intro hv
    rcases atom_subset_or_disjoint (P.out_atom (P.idx R v)) hS with h | h
    · exact h
    · exact absurd hv (disjoint_left.mp h (P.mem_out_idx R v))
  · intro h
    exact h (P.mem_out_idx R v)

/-- A member is the interval of its offsets. -/
theorem eq_ivl (hS : S ∈ 𝒞) : S = P.ivl R (P.lo R S) (P.hi R S) := by
  ext v
  rw [mem_ivl, P.mem_iff_pos R hS]

/-- The atom at an offset of a member lies in it. -/
theorem idxAt_subset (hS : S ∈ 𝒞) {t : ℕ} (ht : t < P.m) (h1 : P.lo R S ≤ t)
    (h2 : t ≤ P.hi R S) : P.out (P.idxAt R t ht) ⊆ S := by
  intro v hv
  rw [P.mem_iff_pos R hS, (P.mem_out_iff R).mp hv, P.pos_idxAt R]
  exact ⟨h1, h2⟩

/-- An atom at an offset outside a member is disjoint from it. -/
theorem disjoint_idxAt (hS : S ∈ 𝒞) {t : ℕ} (ht : t < P.m)
    (h : t < P.lo R S ∨ P.hi R S < t) : Disjoint (P.out (P.idxAt R t ht)) S := by
  rw [disjoint_left]
  intro v hv hvS
  rw [P.mem_iff_pos R hS, (P.mem_out_iff R).mp hv, P.pos_idxAt R] at hvS
  omega

/-! ### Set relations as interval arithmetic -/

variable {A B : Finset (Fin n)}

theorem subset_iff (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) :
    A ⊆ B ↔ P.lo R B ≤ P.lo R A ∧ P.hi R A ≤ P.hi R B := by
  have hlo := P.one_le_lo R hA
  have hhi := P.hi_lt R hA
  have hlh := P.lo_lt_hi R hA
  constructor
  · intro h
    obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R (P.lo R A) (by omega))
    obtain ⟨w, hw⟩ := P.out_nonempty (P.idxAt R (P.hi R A) hhi)
    have hvB := (P.mem_iff_pos R hB v).mp (h (P.idxAt_subset R hA _ le_rfl hlh.le hv))
    have hwB := (P.mem_iff_pos R hB w).mp (h (P.idxAt_subset R hA _ hlh.le le_rfl hw))
    rw [(P.mem_out_iff R).mp hv, P.pos_idxAt R] at hvB
    rw [(P.mem_out_iff R).mp hw, P.pos_idxAt R] at hwB
    omega
  · rintro ⟨h1, h2⟩ v hv
    rw [P.mem_iff_pos R hA] at hv
    rw [P.mem_iff_pos R hB]
    omega

theorem disjoint_iff (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) :
    Disjoint A B ↔ P.hi R A < P.lo R B ∨ P.hi R B < P.lo R A := by
  have hhiA := P.hi_lt R hA
  have hhiB := P.hi_lt R hB
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hmax : max (P.lo R A) (P.lo R B) ≤ P.hi R A ∧ max (P.lo R A) (P.lo R B) ≤ P.hi R B :=
      ⟨max_le (P.lo_lt_hi R hA).le hcon.1, max_le hcon.2 (P.lo_lt_hi R hB).le⟩
    obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R (max (P.lo R A) (P.lo R B))
      (lt_of_le_of_lt hmax.1 hhiA))
    have hvA := P.idxAt_subset R hA _ (le_max_left _ _) hmax.1 hv
    have hvB := P.idxAt_subset R hB _ (le_max_right _ _) hmax.2 hv
    exact disjoint_left.mp h hvA hvB
  · intro h
    rw [disjoint_left]
    intro v hvA hvB
    rw [P.mem_iff_pos R hA] at hvA
    rw [P.mem_iff_pos R hB] at hvB
    omega

theorem crossing_iff (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) :
    Crossing A B ↔
      (P.lo R A < P.lo R B ∧ P.lo R B ≤ P.hi R A ∧ P.hi R A < P.hi R B) ∨
        (P.lo R B < P.lo R A ∧ P.lo R A ≤ P.hi R B ∧ P.hi R B < P.hi R A) := by
  have hhiA := P.hi_lt R hA
  have hhiB := P.hi_lt R hB
  have hloA := P.one_le_lo R hA
  have hloB := P.one_le_lo R hB
  constructor
  · intro hc
    have h1 : ¬ A ⊆ B := fun h => by
      obtain ⟨v, hv⟩ := hc.2.1
      exact (mem_sdiff.mp hv).2 (h (mem_sdiff.mp hv).1)
    have h2 : ¬ B ⊆ A := fun h => by
      obtain ⟨v, hv⟩ := hc.2.2.1
      exact (mem_sdiff.mp hv).2 (h (mem_sdiff.mp hv).1)
    have h3 : ¬ Disjoint A B := fun h => by
      obtain ⟨v, hv⟩ := hc.1
      exact disjoint_left.mp h (mem_inter.mp hv).1 (mem_inter.mp hv).2
    rw [P.subset_iff R hA hB] at h1
    rw [P.subset_iff R hB hA] at h2
    rw [P.disjoint_iff R hA hB] at h3
    omega
  · intro h
    have hne : ¬ A ⊆ B ∧ ¬ B ⊆ A ∧ ¬ Disjoint A B := by
      rw [P.subset_iff R hA hB, P.subset_iff R hB hA, P.disjoint_iff R hA hB]
      omega
    obtain ⟨x, hx⟩ := not_disjoint_iff.mp hne.2.2
    obtain ⟨y, hy1, hy2⟩ := not_subset.mp hne.1
    obtain ⟨z, hz1, hz2⟩ := not_subset.mp hne.2.1
    obtain ⟨w, hw⟩ := P.rootAtom_nonempty
    exact BG.crossing_of_witnesses hx.1 hx.2 hy1 hy2 hz1 hz2
      (disjoint_left.mp (P.rootAtom_disjoint A hA) hw)
      (disjoint_left.mp (P.rootAtom_disjoint B hB) hw)

/-- `W` crosses `S` on the left: it starts before `S`, reaches into it, and ends inside. -/
theorem crossesOnLeft_iff {W : Finset (Fin n)} (hW : W ∈ 𝒞) (hS : S ∈ 𝒞) :
    P.CrossesOnLeft W S ↔ P.lo R W < P.lo R S ∧ P.lo R S ≤ P.hi R W ∧ P.hi R W < P.hi R S := by
  have eS : P.pos R (P.start S) = P.lo R S := rfl
  rw [CrossesOnLeft, P.crossing_iff R hW hS, P.mem_arc_iff_pos R hW, eS]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- `W` crosses `S` on the right: it starts inside `S` and ends beyond it. -/
theorem crossesOnRight_iff {W : Finset (Fin n)} (hW : W ∈ 𝒞) (hS : S ∈ 𝒞) :
    P.CrossesOnRight W S ↔ P.lo R S < P.lo R W ∧ P.lo R W ≤ P.hi R S ∧ P.hi R S < P.hi R W := by
  have eW : P.pos R (P.start W) = P.lo R W := rfl
  rw [CrossesOnRight, P.crossing_iff R hW hS, P.mem_arc_iff_pos R hS, eW]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Two members with the same offsets are equal. -/
theorem eq_of_lo_hi (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (h1 : P.lo R A = P.lo R B)
    (h2 : P.hi R A = P.hi R B) : A = B :=
  subset_antisymm ((P.subset_iff R hA hB).mpr ⟨h1.ge, h2.le⟩)
    ((P.subset_iff R hB hA).mpr ⟨h1.le, h2.ge⟩)

/-! ### Endpoint incidence -/

/-- Two vertices in atoms at different offsets are separated by a member. -/
theorem exists_separating {v w : Fin n} (h : P.pos R (P.idx R v) ≠ P.pos R (P.idx R w)) :
    ∃ S ∈ 𝒞, ¬ (v ∈ S ↔ w ∈ S) := by
  by_contra hcon
  push Not at hcon
  have hw : w ∈ atomOf 𝒞 v := mem_atomOf.mpr fun S hS => by
    have := hcon S hS
    tauto
  have hv : v ∈ atomOf 𝒞 v := mem_atomOf_self 𝒞 v
  have hA : atomOf 𝒞 v ∈ atoms 𝒞 := mem_atoms.mpr ⟨v, rfl⟩
  -- the atom of `v` is `P.out (idx v)`: an atom meeting it
  have e1 : atomOf 𝒞 v = P.out (P.idx R v) := by
    by_contra hne
    exact disjoint_left.mp (atoms_disjoint hA (P.out_atom _) hne) hv (P.mem_out_idx R v)
  have hw' : w ∈ P.out (P.idx R v) := e1 ▸ hw
  exact h (by rw [(P.mem_out_iff R).mp hw'])

/-- **Endpoint incidence**: for `1 ≤ p ≤ m − 1`, the boundary between the atoms at offsets
`p − 1` and `p` is an endpoint of some member — the member separating the two atoms starts
at `p` or ends at `p − 1`. -/
theorem exists_endpoint {p : ℕ} (hp1 : 1 ≤ p) (hp2 : p ≤ P.m - 1) :
    ∃ S ∈ 𝒞, P.lo R S = p ∨ P.hi R S = p - 1 := by
  have hm := P.hm
  obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R (p - 1) (by omega))
  obtain ⟨w, hw⟩ := P.out_nonempty (P.idxAt R p (by omega))
  have hpv : P.pos R (P.idx R v) = p - 1 := by rw [(P.mem_out_iff R).mp hv, P.pos_idxAt R]
  have hpw : P.pos R (P.idx R w) = p := by rw [(P.mem_out_iff R).mp hw, P.pos_idxAt R]
  obtain ⟨S, hS, hsep⟩ := P.exists_separating R (v := v) (w := w) (by omega)
  refine ⟨S, hS, ?_⟩
  rw [P.mem_iff_pos R hS v, P.mem_iff_pos R hS w, hpv, hpw] at hsep
  omega

/-- The boundary before the first atom: some member starts at offset `1`. -/
theorem exists_lo_one : ∃ S ∈ 𝒞, P.lo R S = 1 := by
  have hm := P.hm
  obtain ⟨S, hS, h⟩ := P.exists_endpoint R (p := 1) le_rfl (by omega)
  refine ⟨S, hS, ?_⟩
  have := P.one_le_lo R hS
  have := P.lo_lt_hi R hS
  omega

/-- The boundary after the last atom: some member ends at offset `m − 1`. -/
theorem exists_hi_last : ∃ S ∈ 𝒞, P.hi R S = P.m - 1 := by
  have hm := P.hm
  obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R (P.m - 1) (by omega))
  obtain ⟨w, hw⟩ := P.rootAtom_nonempty
  have hpv : P.pos R (P.idx R v) = P.m - 1 := by rw [(P.mem_out_iff R).mp hv, P.pos_idxAt R]
  have hpw : P.pos R (P.idx R w) = 0 := by
    rw [P.idx_eq_of_mem R (R.hr ▸ hw), P.pos_root R]
  obtain ⟨S, hS, hsep⟩ := P.exists_separating R (v := v) (w := w) (by omega)
  refine ⟨S, hS, ?_⟩
  have hwS : w ∉ S := disjoint_left.mp (P.rootAtom_disjoint S hS) hw
  have hlo := P.one_le_lo R hS
  have hhi := P.hi_lt R hS
  rw [P.mem_iff_pos R hS v, hpv] at hsep
  have hvS : P.lo R S ≤ P.m - 1 ∧ P.m - 1 ≤ P.hi R S := by tauto
  omega

end PolygonRep

end TSPGap

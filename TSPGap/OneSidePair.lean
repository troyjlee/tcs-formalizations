/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OneSideHierarchy

/-!
# KKO21 Lemma 4.18: the interior adjacent-pair estimate

For a rooted polygon of a component of `N_{η,≤1}` with atoms `a₀, …, a_{m−1}` (`a₀` the
root) and `1 ≤ i ≤ m − 2`:

* `exists_left_interval`: some interval `[j, i+1]` of atoms with `j ≤ i` is a `3η`-near
  minimum cut; `exists_right_interval` is the mirror image, by reflection;
* `pair_nearMin`: `aᵢ ∪ aᵢ₊₁` is a `6η`-near minimum cut (the intersection of the two);
* `adjacent_mass`: `x(E(aᵢ, aᵢ₊₁)) ≥ 1 − 3η` (the disjoint-union identity and the LP bound
  on the two atoms).

The constants are KKO22's (members `η`-near); KKO21's `6η`/`12η` are the same statements
for `2η`-near members.  The proof of the left claim follows KKO21: a member ending at
`i + 1` finishes at once; otherwise a member `A` starts at `i + 2`, and either `A` is open
on the left — its strict parent `L`, the common right-crosser `R` of `A, L`, and if
`L` starts at `i + 1` also `L`'s strict parent `L'` and the right-crosser `R'` of `L, L'`
(the two crossers are nested) — or `A` is crossed on the left, and the left-crosser `L`
starting earliest is open on the left with strict parent `L'`, whose common right-crosser
with `L` starts exactly at `i + 2` because `A` is open on the right.  In every case the
interval is `L ∖ U` or `L' ∖ U` for a `2η`-near union `U` starting at `i + 2`
(`interval_of_sdiff`).

`exists_mem_of_pos`: every non-root atom lies in some member (used downstream to place the
root edge in the root atom).
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

namespace PolygonRep

variable (P : PolygonRep 𝒞) (R : P.Rooted)

/-! ### Interval calculus -/

section IvlCalc

variable {a b c d : ℕ}

theorem ivl_inter_of (hac : a ≤ c) (hbd : b ≤ d) :
    P.ivl R a b ∩ P.ivl R c d = P.ivl R c b := by
  ext v
  simp only [mem_inter, mem_ivl]
  omega

theorem ivl_union_of (hac : a ≤ c) (hcb : c ≤ b + 1) (hbd : b ≤ d) :
    P.ivl R a b ∪ P.ivl R c d = P.ivl R a d := by
  ext v
  simp only [mem_union, mem_ivl]
  omega

theorem ivl_sdiff_left (hac : a < c) (hcb : c ≤ b) (hbd : b ≤ d) :
    P.ivl R a b \ P.ivl R c d = P.ivl R a (c - 1) := by
  ext v
  simp only [mem_sdiff, mem_ivl]
  omega

theorem ivl_sdiff_right (hca : c ≤ a) (had : a ≤ d) :
    P.ivl R a b \ P.ivl R c d = P.ivl R (d + 1) b := by
  ext v
  simp only [mem_sdiff, mem_ivl]
  omega

theorem ivl_ne_univ (ha : 1 ≤ a) : P.ivl R a b ≠ univ := by
  intro h
  obtain ⟨v, hv⟩ := P.rootAtom_nonempty
  exact P.root_notMem_ivl R ha hv (h ▸ mem_univ v)

theorem disjoint_ivl_of_lt (h : b < c) : Disjoint (P.ivl R a b) (P.ivl R c d) := by
  rw [disjoint_left]
  intro v h1 h2
  rw [mem_ivl] at h1 h2
  omega

/-- Crossing intervals of atoms cross as sets. -/
theorem crossing_ivl (ha : 1 ≤ a) (hac : a < c) (hcb : c ≤ b) (hbd : b < d) (hd : d < P.m) :
    Crossing (P.ivl R a b) (P.ivl R c d) := by
  obtain ⟨u, hu⟩ := P.out_nonempty (P.idxAt R c (by omega))
  obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R a (by omega))
  obtain ⟨w, hw⟩ := P.out_nonempty (P.idxAt R d hd)
  obtain ⟨z, hz⟩ := P.rootAtom_nonempty
  have hpu : P.pos R (P.idx R u) = c := by rw [(P.mem_out_iff R).mp hu, P.pos_idxAt R]
  have hpv : P.pos R (P.idx R v) = a := by rw [(P.mem_out_iff R).mp hv, P.pos_idxAt R]
  have hpw : P.pos R (P.idx R w) = d := by rw [(P.mem_out_iff R).mp hw, P.pos_idxAt R]
  refine BG.crossing_of_witnesses (x := u) (y := v) (z := w) (w := z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
    | (rw [mem_ivl]; omega)
    | exact P.root_notMem_ivl R ha hz
    | exact P.root_notMem_ivl R (by omega) hz

end IvlCalc

/-- Every non-root atom lies in some member: otherwise the members left of it and those
right of it would be two nonempty classes with no crossing between them. -/
theorem exists_mem_of_pos (hcomp : IsOneSideComponent e₀ x η 𝒞) {t : ℕ} (ht1 : 1 ≤ t)
    (ht2 : t ≤ P.m - 1) : ∃ S ∈ 𝒞, P.lo R S ≤ t ∧ t ≤ P.hi R S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨L₁, hL₁, hlo⟩ := P.exists_lo_one R
  obtain ⟨B₁, hB₁, hhi⟩ := P.exists_hi_last R
  have hm := P.hm
  obtain ⟨D, hD, E, hE, hGD, hGE, hDE⟩ :=
    exists_boundary_crossing (𝒞 := 𝒞) (Good := fun D => P.hi R D < t)
      (show P.hi R L₁ < t by
        have := hcon L₁ hL₁
        omega) B₁ (hcomp.conn L₁ hL₁ B₁ hB₁) (by simp only [not_lt]; omega)
  simp only [not_lt] at hGE
  have hcr := (P.crossing_iff R hD hE).mp hDE
  have := hcon E hE
  omega

/-! ### The interval of a difference -/

/-- A member `L` reaching to offset `≥ i + 2` from `≤ i + 1`, and a `ε'`-near interval `U`
starting at `i + 2` and ending after `L`: `L ∖ U = [lo L, i + 1]` is `(η + ε')`-near. -/
theorem interval_of_sdiff (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {i u : ℕ} {ε' : ℝ} {L : Finset (Fin n)} (hL : L ∈ 𝒞) (hlo : P.lo R L ≤ i + 1)
    (hhi : i + 2 ≤ P.hi R L) (hu : P.hi R L < u) (hum : u < P.m)
    (hU : IsNearMinCut x ε' (P.ivl R (i + 2) u)) :
    IsNearMinCut x (η + ε') (P.ivl R (P.lo R L) (i + 1)) := by
  have hlo1 := P.one_le_lo R hL
  have hc : Crossing L (P.ivl R (i + 2) u) := by
    rw [P.eq_ivl R hL]
    exact P.crossing_ivl R hlo1 (by omega) hhi hu hum
  have h := nearMinCut_sdiff hx (hcomp.nearMin L hL) hU hc
  have e : L \ P.ivl R (i + 2) u = P.ivl R (P.lo R L) (i + 1) := by
    ext v
    simp only [mem_sdiff, mem_ivl, P.mem_iff_pos R hL]
    omega
  rwa [e] at h

/-! ### The left claim -/

/-- **KKO21 Lemma 4.18, the left claim**: for `1 ≤ i ≤ m − 2` some interval `[j, i + 1]`
with `j ≤ i` is a `3η`-near minimum cut. -/
theorem exists_left_interval (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ P.m - 1) :
    ∃ j, 1 ≤ j ∧ j ≤ i ∧ IsNearMinCut x (3 * η) (P.ivl R j (i + 1)) := by
  classical
  have hm := P.hm
  have hnm := hcomp.nearMin
  -- a member ending at `i + 1` finishes at once
  by_cases hend : ∃ S ∈ 𝒞, P.hi R S = i + 1
  · obtain ⟨S, hS, hhi⟩ := hend
    refine ⟨P.lo R S, P.one_le_lo R hS, by have := P.lo_lt_hi R hS; omega, ?_⟩
    have e : P.ivl R (P.lo R S) (i + 1) = S := by
      rw [← hhi]
      exact (P.eq_ivl R hS).symm
    rw [e]
    exact (hnm S hS).mono (by linarith)
  push Not at hend
  -- a member starting at `i + 2`
  obtain ⟨A, hA, hloA⟩ : ∃ A ∈ 𝒞, P.lo R A = i + 2 := by
    rcases Nat.lt_or_ge (i + 2) P.m with hlt | hge
    · obtain ⟨S, hS, h⟩ := P.exists_endpoint R (p := i + 2) (by omega) (by omega)
      rcases h with h | h
      · exact ⟨S, hS, h⟩
      · exact absurd (by omega : P.hi R S = i + 1) (hend S hS)
    · obtain ⟨S, hS, h⟩ := P.exists_hi_last R
      exact absurd (by omega : P.hi R S = i + 1) (hend S hS)
  have hAlh := P.lo_lt_hi R hA
  have hAhi := P.hi_lt R hA
  -- the general step, for a member `L'` starting at `≤ i + 1`, reaching `≥ i + 2`, and an
  -- interval `U` from `i + 2` ending after `L'`
  have step : ∀ L' ∈ 𝒞, P.lo R L' ≤ i → i + 2 ≤ P.hi R L' → ∀ u, P.hi R L' < u → u < P.m →
      ∀ ε', ε' ≤ 2 * η → IsNearMinCut x ε' (P.ivl R (i + 2) u) →
      ∃ j, 1 ≤ j ∧ j ≤ i ∧ IsNearMinCut x (3 * η) (P.ivl R j (i + 1)) := by
    intro L' hL' hlo hhi u hu hum ε' hε' hU
    exact ⟨P.lo R L', P.one_le_lo R hL', hlo,
      (P.interval_of_sdiff R hx hcomp hL' (by omega) hhi hu hum hU).mono (by linarith)⟩
  by_cases hAo : P.OpenLeft A
  · -- Case 1: `A` is open on the left
    obtain ⟨L, hL⟩ := P.exists_strictParentL R hcomp
      (P.exists_strictAncL R hx hcomp hη0 hη hAo (by omega))
    have hLo := hL.1.2.1
    have hAL := hL.1.2.2.1
    have hloL := hL.1.2.2.2
    have hLm := hLo.1
    have hAL' := (P.subset_iff R hA hLm).mp hAL
    obtain ⟨Rc, hRc, hRA, hRL⟩ := P.exists_crossesOnRight_of_strictParentL R hx hcomp hη0 hη hL
    have hRA' := (P.crossesOnRight_iff R hRc hA).mp hRA
    have hRL' := (P.crossesOnRight_iff R hRc hLm).mp hRL
    have hRhi := P.hi_lt R hRc
    -- `A ∪ R` is `2η`-near, an interval from `i + 2`
    have hAR : IsNearMinCut x (2 * η) (P.ivl R (i + 2) (P.hi R Rc)) := by
      have h := nearMinCut_union hx (hnm A hA) (hnm Rc hRc) hRA.1.symm
      have e : A ∪ Rc = P.ivl R (i + 2) (P.hi R Rc) := by
        ext v
        simp only [mem_union, mem_ivl, P.mem_iff_pos R hA, P.mem_iff_pos R hRc]
        omega
      rw [e] at h
      exact h.mono (by linarith)
    by_cases hloL' : P.lo R L ≤ i
    · exact step L hLm hloL' (by omega) _ hRL'.2.2 hRhi _ le_rfl hAR
    · -- `L` starts at `i + 1`: its strict parent `L'`, the right-crosser `R'` of `L, L'`,
      -- and the nesting of `R, R'`
      have hloL1 : P.lo R L = i + 1 := by omega
      obtain ⟨L', hL'⟩ := P.exists_strictParentL R hcomp
        (P.exists_strictAncL R hx hcomp hη0 hη hLo (by omega))
      have hL'o := hL'.1.2.1
      have hLL' := hL'.1.2.2.1
      have hloL' := hL'.1.2.2.2
      have hL'm := hL'o.1
      have hLL'' := (P.subset_iff R hLm hL'm).mp hLL'
      obtain ⟨Rc', hRc', hR'L, hR'L'⟩ :=
        P.exists_crossesOnRight_of_strictParentL R hx hcomp hη0 hη hL'
      have hR'L₁ := (P.crossesOnRight_iff R hRc' hLm).mp hR'L
      have hR'L'₁ := (P.crossesOnRight_iff R hRc' hL'm).mp hR'L'
      have hR'hi := P.hi_lt R hRc'
      -- both crossers are open on the right (they are crossed on the left by `L`)
      have hRo : P.OpenRight Rc := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hRc with h | h
        · exact absurd (P.crossesOnLeft_iff_crossesOnRight_swap.mpr hRL) (h.2 L hLm)
        · exact h
      have hR'o : P.OpenRight Rc' := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hRc' with h | h
        · exact absurd (P.crossesOnLeft_iff_crossesOnRight_swap.mpr hR'L) (h.2 L hLm)
        · exact h
      have hnd : ¬ Disjoint Rc Rc' := by
        rw [P.disjoint_iff R hRc hRc']
        omega
      rcases P.nested_of_openRight hcomp hRo hR'o hnd with hsub | hsub
      · -- `R ⊆ R'`: use `A ∪ R'`
        have hsub' := (P.subset_iff R hRc hRc').mp hsub
        have hAR' : IsNearMinCut x (2 * η) (P.ivl R (i + 2) (P.hi R Rc')) := by
          by_cases hlo2 : P.lo R Rc' = i + 2
          · have e : P.ivl R (i + 2) (P.hi R Rc') = Rc' := by
              rw [← hlo2]
              exact (P.eq_ivl R hRc').symm
            rw [e]
            exact (hnm Rc' hRc').mono (by linarith)
          · have hc : Crossing A Rc' := by
              rw [P.crossing_iff R hA hRc']
              omega
            have h := nearMinCut_union hx (hnm A hA) (hnm Rc' hRc') hc
            have e : A ∪ Rc' = P.ivl R (i + 2) (P.hi R Rc') := by
              ext v
              simp only [mem_union, mem_ivl, P.mem_iff_pos R hA, P.mem_iff_pos R hRc']
              omega
            rw [e] at h
            exact h.mono (by linarith)
        exact step L' hL'm (by omega) (by omega) _ hR'L'₁.2.2 hR'hi _ le_rfl hAR'
      · -- `R' ⊆ R`: use `A ∪ R`, which `L'` crosses since `hi L' < hi R' ≤ hi R`
        have hsub' := (P.subset_iff R hRc' hRc).mp hsub
        exact step L' hL'm (by omega) (by omega) _ (by omega) hRhi _ le_rfl hAR
  · -- Case 2: `A` is crossed on the left; take the left-crosser starting earliest
    obtain ⟨L, hL, hmin⟩ := Finset.exists_min_image (𝒞.filter fun L => P.CrossesOnLeft L A)
      (P.lo R) (by
        obtain ⟨W, hW, hc⟩ := P.exists_crossesOnLeft_of_not_openLeft hA hAo
        exact ⟨W, mem_filter.mpr ⟨hW, hc⟩⟩)
    rw [mem_filter] at hL
    obtain ⟨hLm, hLc⟩ := hL
    have hLc' := (P.crossesOnLeft_iff R hLm hA).mp hLc
    have hAr : P.OpenRight A := by
      rcases P.openLeft_or_openRight hx hcomp hη0 hη hA with h | h
      · exact absurd h hAo
      · exact h
    by_cases hloL : P.lo R L ≤ i
    · -- `L ∖ A`
      have hAiv : IsNearMinCut x η (P.ivl R (i + 2) (P.hi R A)) := by
        have e : P.ivl R (i + 2) (P.hi R A) = A := by
          rw [← hloA]
          exact (P.eq_ivl R hA).symm
        rw [e]
        exact hnm A hA
      exact step L hLm hloL (by omega) _ hLc'.2.2 hAhi _ (by linarith) hAiv
    · have hloL1 : P.lo R L = i + 1 := by omega
      -- `L` is open on the left: a left-crosser of `L` would cross `A` earlier or end at `i+1`
      have hLo : P.OpenLeft L := by
        refine ⟨hLm, fun L₂ hL₂ hc => ?_⟩
        have hc' := (P.crossesOnLeft_iff R hL₂ hLm).mp hc
        by_cases h2 : i + 2 ≤ P.hi R L₂
        · have hcA : P.CrossesOnLeft L₂ A := (P.crossesOnLeft_iff R hL₂ hA).mpr (by omega)
          have := hmin L₂ (mem_filter.mpr ⟨hL₂, hcA⟩)
          omega
        · exact hend L₂ hL₂ (by omega)
      obtain ⟨L', hL'⟩ := P.exists_strictParentL R hcomp
        (P.exists_strictAncL R hx hcomp hη0 hη hLo (by omega))
      have hL'o := hL'.1.2.1
      have hLL' := hL'.1.2.2.1
      have hloL' := hL'.1.2.2.2
      have hL'm := hL'o.1
      have hLL'' := (P.subset_iff R hLm hL'm).mp hLL'
      -- `L'` reaches beyond `A`, else it crosses `A` on the left earlier than `L`
      have hL'A : P.hi R A ≤ P.hi R L' := by
        by_contra hlt
        push Not at hlt
        have hcA : P.CrossesOnLeft L' A := (P.crossesOnLeft_iff R hL'm hA).mpr (by omega)
        have := hmin L' (mem_filter.mpr ⟨hL'm, hcA⟩)
        omega
      obtain ⟨Rc, hRc, hRL, hRL'⟩ :=
        P.exists_crossesOnRight_of_strictParentL R hx hcomp hη0 hη hL'
      have hRL₁ := (P.crossesOnRight_iff R hRc hLm).mp hRL
      have hRL'₁ := (P.crossesOnRight_iff R hRc hL'm).mp hRL'
      have hRhi := P.hi_lt R hRc
      -- `R` starts exactly at `i + 2`, since `A` is open on the right
      have hloR : P.lo R Rc = i + 2 := by
        by_contra hne
        have hcA : P.CrossesOnRight Rc A := (P.crossesOnRight_iff R hRc hA).mpr (by omega)
        exact hAr.2 Rc hRc hcA
      have hRiv : IsNearMinCut x η (P.ivl R (i + 2) (P.hi R Rc)) := by
        have e : P.ivl R (i + 2) (P.hi R Rc) = Rc := by
          rw [← hloR]
          exact (P.eq_ivl R hRc).symm
        rw [e]
        exact hnm Rc hRc
      exact step L' hL'm (by omega) (by omega) _ hRL'₁.2.2 hRhi _ (by linarith) hRiv

/-! ### The right claim, by reflection -/

/-- **KKO21 Lemma 4.18, the right claim**: some interval `[i, j']` with `j' ≥ i + 1` is a
`3η`-near minimum cut. -/
theorem exists_right_interval (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ P.m - 1) :
    ∃ j', i + 1 ≤ j' ∧ j' ≤ P.m - 1 ∧ IsNearMinCut x (3 * η) (P.ivl R i j') := by
  have hm := P.hm
  obtain ⟨j, hj1, hj2, hj⟩ := P.reflect.exists_left_interval R.reflect hx hcomp hη0 hη
    (i := P.m - 1 - i) (by omega) (by change P.m - 1 - i + 1 ≤ P.m - 1; omega)
  refine ⟨P.m - j, by omega, by omega, ?_⟩
  have e := P.reflect_ivl R (a := i) (b := P.m - j) hi1 (by omega)
  rw [show P.m - (P.m - j) = j by omega] at e
  rw [show P.m - 1 - i + 1 = P.m - i by omega] at hj
  rw [← e]
  exact hj

/-! ### The pair -/

/-- **KKO21 Lemma 4.18**: `aᵢ ∪ aᵢ₊₁` is a `6η`-near minimum cut for `1 ≤ i ≤ m − 2`. -/
theorem pair_nearMin (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ P.m - 1) :
    IsNearMinCut x (6 * η) (P.ivl R i (i + 1)) := by
  have hm := P.hm
  obtain ⟨j, hj1, hj2, hj⟩ := P.exists_left_interval R hx hcomp hη0 hη hi1 hi2
  obtain ⟨j', hj'1, hj'2, hj'⟩ := P.exists_right_interval R hx hcomp hη0 hη hi1 hi2
  rcases eq_or_lt_of_le hj2 with hji | hjlt
  · rw [hji] at hj
    exact hj.mono (by linarith)
  rcases eq_or_lt_of_le hj'1 with hji' | hj'lt
  · rw [← hji'] at hj'
    exact hj'.mono (by linarith)
  have hc : Crossing (P.ivl R j (i + 1)) (P.ivl R i j') :=
    P.crossing_ivl R hj1 hjlt (by omega) hj'lt (by omega)
  have h := nearMinCut_inter hx hj hj' hc
  rw [P.ivl_inter_of R hjlt.le hj'lt.le] at h
  exact h.mono (by linarith)

/-- **KKO21 Lemma 4.18**, the mass: `x(E(aᵢ, aᵢ₊₁)) ≥ 1 − 3η` for `1 ≤ i ≤ m − 2`. -/
theorem adjacent_mass (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ P.m - 1) :
    1 - 3 * η ≤ pairSum x (P.ivl R i i) (P.ivl R (i + 1) (i + 1)) := by
  have hm := P.hm
  have hQ := P.pair_nearMin R hx hcomp hη0 hη hi1 hi2
  have hd : Disjoint (P.ivl R i i) (P.ivl R (i + 1) (i + 1)) :=
    P.disjoint_ivl_of_lt R (by omega)
  have hU : P.ivl R i i ∪ P.ivl R (i + 1) (i + 1) = P.ivl R i (i + 1) :=
    P.ivl_union_of R (by omega) (by omega) (by omega)
  have hid := cutSum_add_cutSum_of_disjoint x hd
  rw [hU] at hid
  have h1 := two_le_cutSum hx (P.ivl_nonempty R (a := i) (b := i) le_rfl (by omega))
    (P.ivl_ne_univ R (a := i) (b := i) hi1)
  have h2 := two_le_cutSum hx (P.ivl_nonempty R (a := i + 1) (b := i + 1) le_rfl (by omega))
    (P.ivl_ne_univ R (a := i + 1) (b := i + 1) (by omega))
  have h3 := hQ.cut_le
  linarith

end PolygonRep

end TSPGap

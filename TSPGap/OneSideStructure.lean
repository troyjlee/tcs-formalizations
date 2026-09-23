/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OneSidePair

/-!
# KKO22 Theorem A.3 = KKO21 Theorem 4.9: the structure of a one-side polygon

For a rooted polygon of a component of `N_{η,≤1}` with atoms `a₀, …, a_{m−1}`:

* `atom_nearMin` (KKO21 Lemma 4.19): every non-root atom is a `7η`-near minimum cut — the
  pair `aₜ ∪ aₜ₊₁` at `6η` intersected with, or minus, a member separating the two atoms;
* `exists_maxOpenRight`, `outer_nearMin`, `root_cut_le` (Lemma 4.16): the cut open on the
  right of maximal size reaches the last atom and contains every cut open on the right; it
  crosses the member starting at the first atom, so `a₁ ∪ ⋯ ∪ a_{m−1} = a₀ᶜ` is
  `2η`-near;
* `root_neighbor_left` / `root_neighbor_right` (Lemma 4.17): `x(E(a₀, a₁)) ≥ 1 − η`, by
  KKO21 Lemma 2.6 on the two extreme cuts, through the `2η`-near union with the member
  starting at `a₂` when the maximal right cut starts later; the right neighbour by
  reflection;
* `root_middle_le`: `x(E(a₀, a₂ ∪ ⋯ ∪ a_{m−2})) ≤ 4η`, from `cut(a₀) ≤ 2 + 2η`;
* `rootEdge_mem_root`: both endpoints of the root edge lie in the root atom (every non-root
  atom lies in a member, and members avoid the root edge);
* the index-level forms `adjacent_mass_idx` (`≥ 1 − 3η` for every cyclically adjacent pair,
  the root's two neighbours included), `atom_cut_le_idx` (`≤ 2 + 7η` for every atom), and
  their transfer to `e₀.restrict x₀` (`pairSum_restrict_eq`, `cutSum_restrict_out`).

`NearCycle.lean` assembles these into `oneSide_structure` at the consumer constant `7η`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  {𝒞 : Finset (Finset (Fin n))}

namespace PolygonRep

variable (P : PolygonRep 𝒞) (R : P.Rooted)

/-! ### Lemma 4.19: atom degrees -/

/-- **KKO21 Lemma 4.19**: every non-root atom is a `7η`-near minimum cut. -/
theorem atom_nearMin (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ P.m - 1) :
    IsNearMinCut x (7 * η) (P.ivl R t t) := by
  have hm := P.hm
  have hnm := hcomp.nearMin
  rcases Nat.lt_or_ge t (P.m - 1) with hlt | hge
  · have hQ := P.pair_nearMin R hx hcomp hη0 hη ht1 (by omega)
    obtain ⟨C, hC, h⟩ := P.exists_endpoint R (p := t + 1) (by omega) (by omega)
    have hClh := P.lo_lt_hi R hC
    have hChi := P.hi_lt R hC
    have hClo := P.one_le_lo R hC
    rcases h with h | h
    · -- `C` starts at `t + 1`: `aₜ = Q ∖ C`
      have hc : Crossing (P.ivl R t (t + 1)) C := by
        rw [P.eq_ivl R hC, h]
        exact P.crossing_ivl R ht1 (by omega) le_rfl (by omega) hChi
      have hh := nearMinCut_sdiff hx hQ (hnm C hC) hc
      have e : P.ivl R t (t + 1) \ C = P.ivl R t t := by
        ext v
        simp only [mem_sdiff, mem_ivl, P.mem_iff_pos R hC]
        omega
      rw [e] at hh
      exact hh.mono (by linarith)
    · -- `C` ends at `t`: `aₜ = C ∩ Q`
      have hc : Crossing C (P.ivl R t (t + 1)) := by
        rw [P.eq_ivl R hC, h]
        exact P.crossing_ivl R hClo (by omega) le_rfl (by omega) (by omega)
      have hh := nearMinCut_inter hx (hnm C hC) hQ hc
      have e : C ∩ P.ivl R t (t + 1) = P.ivl R t t := by
        ext v
        simp only [mem_inter, mem_ivl, P.mem_iff_pos R hC]
        omega
      rw [e] at hh
      exact hh.mono (by linarith)
  · have ht : t = P.m - 1 := by omega
    have hQ := P.pair_nearMin R hx hcomp hη0 hη (i := P.m - 2) (by omega) (by omega)
    rw [show P.m - 2 + 1 = P.m - 1 by omega] at hQ
    obtain ⟨C, hC, h⟩ := P.exists_endpoint R (p := P.m - 1) (by omega) le_rfl
    have hClh := P.lo_lt_hi R hC
    have hChi := P.hi_lt R hC
    have hClo := P.one_le_lo R hC
    rcases h with h | h
    · exfalso
      omega
    · have hc : Crossing (P.ivl R (P.m - 2) (P.m - 1)) C := by
        rw [P.eq_ivl R hC, h]
        exact (P.crossing_ivl R hClo (by omega) (by omega) (by omega) (by omega)).symm
      have hh := nearMinCut_sdiff hx hQ (hnm C hC) hc
      have e : P.ivl R (P.m - 2) (P.m - 1) \ C = P.ivl R t t := by
        ext v
        simp only [mem_sdiff, mem_ivl, P.mem_iff_pos R hC]
        omega
      rw [e] at hh
      exact hh.mono (by linarith)

/-! ### Lemma 4.16: the outer cut -/

/-- The cut open on the right of maximal size: it reaches the last atom, starts at offset
`≥ 2`, and contains every cut open on the right (KKO21's unique ancestor-free cut of the
right hierarchy, Corollary 4.15). -/
theorem exists_maxOpenRight (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) :
    ∃ M ∈ 𝒞, P.OpenRight M ∧ P.hi R M = P.m - 1 ∧ 2 ≤ P.lo R M ∧
      ∀ D, P.OpenRight D → D ⊆ M := by
  classical
  have hm := P.hm
  obtain ⟨B₁, hB₁, hhi₁⟩ := P.exists_hi_last R
  have hB₁o : P.OpenRight B₁ := ⟨hB₁, fun W hW hc => by
    rw [P.crossesOnRight_iff R hW hB₁] at hc
    have := P.hi_lt R hW
    omega⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image (𝒞.filter fun D => P.OpenRight D)
    Finset.card ⟨B₁, mem_filter.mpr ⟨hB₁, hB₁o⟩⟩
  rw [mem_filter] at hM
  obtain ⟨hMm, hMo⟩ := hM
  have hall : ∀ D, P.OpenRight D → D ⊆ M := by
    intro D hD
    by_cases hd : Disjoint D M
    · obtain ⟨E, hEo, hDE, hME⟩ := P.common_ancestorR R hx hcomp hη0 hη hD hMo hd
      have hle := hmax E (mem_filter.mpr ⟨hEo.1, hEo⟩)
      have hEM : M = E := eq_of_subset_of_card_le hME hle
      rw [← hEM] at hDE
      exact hDE
    · rcases P.nested_of_openRight hcomp hD hMo hd with h | h
      · exact h
      · have hle := hmax D (mem_filter.mpr ⟨hD.1, hD⟩)
        rw [eq_of_subset_of_card_le h hle]
  have hhiM : P.hi R M = P.m - 1 := by
    have := (P.subset_iff R hB₁ hMm).mp (hall B₁ hB₁o)
    have := P.hi_lt R hMm
    omega
  refine ⟨M, hMm, hMo, hhiM, ?_, hall⟩
  have h1 := P.one_le_lo R hMm
  have hlen := P.len_le M hMm
  have h2 := P.two_le_len M hMm
  have : P.hi R M = P.lo R M + P.len M - 1 := rfl
  omega

/-- **KKO21 Lemma 4.16**: the union of the non-root atoms is a `2η`-near minimum cut. -/
theorem outer_nearMin (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) : IsNearMinCut x (2 * η) (P.ivl R 1 (P.m - 1)) := by
  have hm := P.hm
  obtain ⟨M, hMm, hMo, hhiM, hloM, hall⟩ := P.exists_maxOpenRight R hx hcomp hη0 hη
  obtain ⟨L₁, hL₁, hlo₁⟩ := P.exists_lo_one R
  have hL₁o : P.OpenLeft L₁ := ⟨hL₁, fun W hW hc => by
    rw [P.crossesOnLeft_iff R hW hL₁] at hc
    have := P.one_le_lo R hW
    omega⟩
  obtain ⟨C, hC, hcC⟩ := P.exists_crossesOnRight_of_openLeft hcomp hL₁o
  have hcC' := (P.crossesOnRight_iff R hC hL₁).mp hcC
  have hCo : P.OpenRight C := by
    rcases P.openLeft_or_openRight hx hcomp hη0 hη hC with h | h
    · exact absurd (P.crossesOnLeft_iff_crossesOnRight_swap.mpr hcC) (h.2 L₁ hL₁)
    · exact h
  have hCM := (P.subset_iff R hC hMm).mp (hall C hCo)
  have hChi := P.hi_lt R hC
  have hc : Crossing L₁ M := by
    rw [P.crossing_iff R hL₁ hMm]
    omega
  have h := nearMinCut_union hx (hcomp.nearMin L₁ hL₁) (hcomp.nearMin M hMm) hc
  have e : L₁ ∪ M = P.ivl R 1 (P.m - 1) := by
    ext v
    simp only [mem_union, mem_ivl, P.mem_iff_pos R hL₁, P.mem_iff_pos R hMm]
    have := P.pos_lt R (P.idx R v)
    omega
  rw [e] at h
  exact h.mono (by linarith)

/-- The complement of the root atom is the union of the other atoms. -/
theorem compl_root_eq : (P.out R.r)ᶜ = P.ivl R 1 (P.m - 1) := by
  ext v
  rw [mem_compl, mem_ivl, P.mem_out_iff R, ← P.pos_eq_zero_iff R]
  have := P.pos_lt R (P.idx R v)
  omega

theorem root_cut_le (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) : cutSum x (P.out R.r) ≤ 2 + 2 * η := by
  rw [← cutSum_compl, P.compl_root_eq R]
  exact (P.outer_nearMin R hx hcomp hη0 hη).cut_le

/-! ### Lemma 4.17: the root's neighbours -/

/-- **KKO21 Lemma 4.17**, left: `x(E(a₁, a₀)) ≥ 1 − η`. -/
theorem root_neighbor_left (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) : 1 - η ≤ pairSum x (P.ivl R 1 1) (P.out R.r) := by
  have hm := P.hm
  obtain ⟨M, hMm, hMo, hhiM, hloM, hall⟩ := P.exists_maxOpenRight R hx hcomp hη0 hη
  obtain ⟨L₁, hL₁, hlo₁⟩ := P.exists_lo_one R
  have hL₁lh := P.lo_lt_hi R hL₁
  have hL₁len := P.len_le L₁ hL₁
  have hL₁hi : P.hi R L₁ = P.lo R L₁ + P.len L₁ - 1 := rfl
  have hcompl : (L₁ ∪ P.ivl R 2 (P.m - 1))ᶜ = P.out R.r := by
    ext v
    rw [mem_compl, mem_union, mem_ivl, P.mem_iff_pos R hL₁, P.mem_out_iff R,
      ← P.pos_eq_zero_iff R]
    have := P.pos_lt R (P.idx R v)
    omega
  have hsd : L₁ \ P.ivl R 2 (P.m - 1) = P.ivl R 1 1 := by
    ext v
    rw [mem_sdiff, mem_ivl, mem_ivl, P.mem_iff_pos R hL₁]
    have := P.pos_lt R (P.idx R v)
    omega
  by_cases h2 : P.lo R M = 2
  · have hc : Crossing L₁ M := by
      rw [P.crossing_iff R hL₁ hMm]
      omega
    have hb := one_sub_half_le_pairSum_sdiff_compl hx (hcomp.nearMin L₁ hL₁)
      (hcomp.nearMin M hMm) hc
    have eM : M = P.ivl R 2 (P.m - 1) := by
      rw [P.eq_ivl R hMm, h2, hhiM]
    rw [eM, hsd, hcompl] at hb
    linarith
  · have hloM2 : 2 < P.lo R M := by omega
    obtain ⟨C, hC, h⟩ := P.exists_endpoint R (p := 2) (by omega) (by omega)
    have hClh := P.lo_lt_hi R hC
    have hClo := P.one_le_lo R hC
    rcases h with hloC | hhiC
    · have hCo : P.OpenLeft C := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hC with h' | h'
        · exact h'
        · exfalso
          have := (P.subset_iff R hC hMm).mp (hall C h')
          omega
      obtain ⟨B', hB', hcB'⟩ := P.exists_crossesOnRight_of_openLeft hcomp hCo
      have hcB'' := (P.crossesOnRight_iff R hB' hC).mp hcB'
      have hB'o : P.OpenRight B' := by
        rcases P.openLeft_or_openRight hx hcomp hη0 hη hB' with h' | h'
        · exact absurd (P.crossesOnLeft_iff_crossesOnRight_swap.mpr hcB') (h'.2 C hC)
        · exact h'
      have hB'M := (P.subset_iff R hB' hMm).mp (hall B' hB'o)
      have hcMC : Crossing M C := by
        rw [P.crossing_iff R hMm hC]
        omega
      have hU := nearMinCut_union hx (hcomp.nearMin M hMm) (hcomp.nearMin C hC) hcMC
      have eU : M ∪ C = P.ivl R 2 (P.m - 1) := by
        ext v
        simp only [mem_union, mem_ivl, P.mem_iff_pos R hMm, P.mem_iff_pos R hC]
        omega
      rw [eU] at hU
      have hc : Crossing L₁ (P.ivl R 2 (P.m - 1)) := by
        rw [P.eq_ivl R hL₁, hlo₁]
        exact P.crossing_ivl R le_rfl (by omega) (by omega) (by omega) (by omega)
      have hb := one_sub_half_le_pairSum_sdiff_compl hx (hcomp.nearMin L₁ hL₁) hU hc
      rw [hsd, hcompl] at hb
      linarith
    · exfalso
      omega

/-- **KKO21 Lemma 4.17**, right: `x(E(a_{m−1}, a₀)) ≥ 1 − η`, by reflection. -/
theorem root_neighbor_right (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) :
    1 - η ≤ pairSum x (P.ivl R (P.m - 1) (P.m - 1)) (P.out R.r) := by
  have hm := P.hm
  have h := P.reflect.root_neighbor_left R.reflect hx hcomp hη0 hη
  have e := P.reflect_ivl R (a := P.m - 1) (b := P.m - 1) (by omega) (by omega)
  rw [show P.m - (P.m - 1) = 1 by omega] at e
  rw [e] at h
  simpa using h

/-! ### The root and the middle -/

/-- `x(E(a₀, a₂ ∪ ⋯ ∪ a_{m−2})) ≤ 4η`. -/
theorem root_middle_le (hx : x ∈ subtourLP n) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) :
    pairSum x (P.out R.r) (P.ivl R 2 (P.m - 2)) ≤ 4 * η := by
  have hm := P.hm
  have hcut := P.root_cut_le R hx hcomp hη0 hη
  rw [cutSum_eq_pairSum, P.compl_root_eq R] at hcut
  have e : P.ivl R 1 (P.m - 1) =
      P.ivl R 1 1 ∪ (P.ivl R 2 (P.m - 2) ∪ P.ivl R (P.m - 1) (P.m - 1)) := by
    ext v
    simp only [mem_union, mem_ivl]
    omega
  have d1 : Disjoint (P.ivl R 1 1) (P.ivl R 2 (P.m - 2) ∪ P.ivl R (P.m - 1) (P.m - 1)) := by
    rw [disjoint_left]
    intro v h1 h2
    rw [mem_ivl] at h1
    rw [mem_union, mem_ivl, mem_ivl] at h2
    omega
  have d2 : Disjoint (P.ivl R 2 (P.m - 2)) (P.ivl R (P.m - 1) (P.m - 1)) :=
    P.disjoint_ivl_of_lt R (by omega)
  rw [e, pairSum_union_right x _ d1, pairSum_union_right x _ d2] at hcut
  have h1 := P.root_neighbor_left R hx hcomp hη0 hη
  have h2 := P.root_neighbor_right R hx hcomp hη0 hη
  rw [pairSum_comm] at h1 h2
  linarith

/-- Both endpoints of the root edge lie in the root atom: every non-root atom lies in a
member, and the members avoid the root edge. -/
theorem rootEdge_mem_root (hcomp : IsOneSideComponent e₀ x η 𝒞) :
    e₀.u₀ ∈ P.out R.r ∧ e₀.v₀ ∈ P.out R.r := by
  have key : ∀ w, (∀ S ∈ 𝒞, w ∉ S) → w ∈ P.out R.r := by
    intro w hw
    rw [P.mem_out_iff R, ← P.pos_eq_zero_iff R]
    by_contra hne
    have hp := P.pos_lt R (P.idx R w)
    obtain ⟨S, hS, h1, h2⟩ := P.exists_mem_of_pos R hcomp (t := P.pos R (P.idx R w))
      (by omega) (by omega)
    exact hw S hS ((P.mem_iff_pos R hS w).mpr ⟨h1, h2⟩)
  exact ⟨key _ fun S hS => (hcomp.avoids S hS).1, key _ fun S hS => (hcomp.avoids S hS).2⟩

/-! ### Index-level forms -/

theorem pos_add_one (i : Fin P.m) :
    P.pos R (i + 1) = if P.pos R i + 1 < P.m then P.pos R i + 1 else 0 := by
  have hm := P.hm
  have h1 : (1 : Fin P.m).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  unfold pos
  rw [show i + 1 - R.r = (i - R.r) + 1 by abel, Fin.val_add_ite, h1]
  have := (i - R.r).isLt
  split_ifs <;> omega

theorem out_add_one_eq (i : Fin P.m) (h : P.pos R i + 1 < P.m) :
    P.out (i + 1) = P.ivl R (P.pos R i + 1) (P.pos R i + 1) := by
  rw [P.out_eq_ivl R (i + 1), P.pos_add_one R, if_pos h]

theorem out_add_one_eq_root (i : Fin P.m) (h : P.pos R i + 1 = P.m) :
    P.out (i + 1) = P.out R.r := by
  congr 1
  rw [← P.pos_eq_iff R, P.pos_add_one R, if_neg (by omega), P.pos_root R]

/-- Every cyclically adjacent pair of atoms carries mass `≥ 1 − 3η`. -/
theorem adjacent_mass_idx (R : P.Rooted) (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) (i : Fin P.m) :
    1 - 3 * η ≤ pairSum x (P.out i) (P.out (i + 1)) := by
  have hm := P.hm
  have hp := P.pos_lt R i
  rcases Nat.lt_or_ge (P.pos R i + 1) P.m with hlt | hge
  · rw [P.out_add_one_eq R i hlt]
    rcases Nat.eq_zero_or_pos (P.pos R i) with h0 | hpos
    · have hi : i = R.r := (P.pos_eq_zero_iff R).mp h0
      rw [h0, hi]
      have := P.root_neighbor_left R hx hcomp hη0 hη
      rw [pairSum_comm] at this
      linarith
    · rw [P.out_eq_ivl R i]
      exact P.adjacent_mass R hx hcomp hη0 hη hpos (by omega)
  · rw [P.out_add_one_eq_root R i (by omega), P.out_eq_ivl R i,
      show P.pos R i = P.m - 1 by omega]
    have := P.root_neighbor_right R hx hcomp hη0 hη
    linarith

/-- Every atom, the root included, is a `7η`-near minimum cut. -/
theorem atom_cut_le_idx (R : P.Rooted) (hx : x ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (hη0 : 0 < η) (hη : η ≤ 2 / 5) (i : Fin P.m) : cutSum x (P.out i) ≤ 2 + 7 * η := by
  rcases Nat.eq_zero_or_pos (P.pos R i) with h0 | hpos
  · have hi : i = R.r := (P.pos_eq_zero_iff R).mp h0
    rw [hi]
    have := P.root_cut_le R hx hcomp hη0 hη
    linarith
  · rw [P.out_eq_ivl R i]
    exact (P.atom_nearMin R hx hcomp hη0 hη hpos (by have := P.pos_lt R i; omega)).cut_le

/-! ### Transfer to the restricted LP point -/

/-- The root edge joins no two distinct atoms. -/
theorem edge_notMem_betweenEdges (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {i j : Fin P.m}
    (hij : i ≠ j) : e₀.edge ∉ betweenEdges (P.out i) (P.out j) := by
  intro h
  obtain ⟨hu, hv⟩ := P.rootEdge_mem_root R hcomp
  rw [betweenEdges, mem_filter] at h
  obtain ⟨-, u, hu', v, hv', he⟩ := h
  rw [RootEdge.edge] at he
  have hui : P.idx R u = i := P.idx_eq_of_mem R hu'
  have hvj : P.idx R v = j := P.idx_eq_of_mem R hv'
  have hur : P.idx R e₀.u₀ = R.r := P.idx_eq_of_mem R hu
  have hvr : P.idx R e₀.v₀ = R.r := P.idx_eq_of_mem R hv
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply hij
    rw [← hui, ← hvj, ← h1, ← h2, hur, hvr]
  · apply hij
    rw [← hui, ← hvj, ← h1, ← h2, hvr, hur]

/-- The root edge joins the root atom to no set disjoint from it. -/
theorem edge_notMem_betweenEdges_root (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {B : Finset (Fin n)} (hB : Disjoint (P.out R.r) B) :
    e₀.edge ∉ betweenEdges (P.out R.r) B := by
  intro h
  obtain ⟨hu, hv⟩ := P.rootEdge_mem_root R hcomp
  rw [betweenEdges, mem_filter] at h
  obtain ⟨-, u, -, v, hv', he⟩ := h
  rw [RootEdge.edge] at he
  rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact disjoint_left.mp hB (h2 ▸ hv) hv'
  · exact disjoint_left.mp hB (h1 ▸ hu) hv'

/-- The mass between two distinct atoms is unchanged by deleting the root edge. -/
theorem pairSum_restrict_eq (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {i j : Fin P.m}
    (hij : i ≠ j) (x₀ : Sym2 (Fin n) → ℝ) :
    pairSum (e₀.restrict x₀) (P.out i) (P.out j) = pairSum x₀ (P.out i) (P.out j) := by
  have hd : Disjoint (P.out i) (P.out j) :=
    atoms_disjoint (P.out_atom i) (P.out_atom j) fun e => hij (P.out_injective e)
  rw [← sum_betweenEdges _ hd, ← sum_betweenEdges _ hd]
  exact RootEdge.sum_restrict_of_notMem (P.edge_notMem_betweenEdges R hcomp hij)

/-- The mass between the root atom and a set disjoint from it is unchanged by deleting the
root edge. -/
theorem pairSum_restrict_root_eq (hcomp : IsOneSideComponent e₀ x η 𝒞)
    {B : Finset (Fin n)} (hB : Disjoint (P.out R.r) B) (x₀ : Sym2 (Fin n) → ℝ) :
    pairSum (e₀.restrict x₀) (P.out R.r) B = pairSum x₀ (P.out R.r) B := by
  rw [← sum_betweenEdges _ hB, ← sum_betweenEdges _ hB]
  exact RootEdge.sum_restrict_of_notMem (P.edge_notMem_betweenEdges_root R hcomp hB)

/-- The cut of an atom is unchanged by deleting the root edge. -/
theorem cutSum_restrict_out (R : P.Rooted) (hcomp : IsOneSideComponent e₀ x η 𝒞)
    (i : Fin P.m)
    (x₀ : Sym2 (Fin n) → ℝ) :
    cutSum (e₀.restrict x₀) (P.out i) = cutSum x₀ (P.out i) := by
  obtain ⟨hu, hv⟩ := P.rootEdge_mem_root R hcomp
  by_cases hir : i = R.r
  · subst hir
    rw [← cutSum_compl (e₀.restrict x₀), ← cutSum_compl x₀]
    exact cutSum_restrict ⟨fun h => (mem_compl.mp h) hu, fun h => (mem_compl.mp h) hv⟩
  · refine cutSum_restrict ⟨fun h => hir ?_, fun h => hir ?_⟩
    · exact (P.idx_eq_of_mem R h).symm.trans (P.idx_eq_of_mem R hu)
    · exact (P.idx_eq_of_mem R h).symm.trans (P.idx_eq_of_mem R hv)

end PolygonRep

end TSPGap

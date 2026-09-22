/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleMatching
import TSPGap.SongGoodness

/-!
# Song's Hall inequality and matching allocation

Hall's condition holds with the four-h goodness policy, upward coefficient
`kGood`, demand discount `epsilonB` and fixed inflation `2*d₀`, for every
hierarchy error between zero and `d₀`. The three-child case uses goodness of
all bundles. The four-child case separates zero/one bad bundle from two bad
bundles, using parity to exclude three bad-incident atoms.

The actual max-entropy law supplies the matching inputs. No Hall certificate
or probabilistic matching certificate is assumed by the public producer.
-/

namespace TSPGap.Song
open Finset

/-- The bad-incident coefficient in the proper-family Hall inequality is negative. -/
theorem hall_bad_coefficient {eta : ℝ} (heta : 0 ≤ eta) :
    (kGood + 1) * h + d₀ + 2 * d₀ * h - epsilonB / 2 - kGood * h * epsilonB - eta < 0 := by
  classical
  have hnum : (kGood + 1) * h + d₀ + 2 * d₀ * h - epsilonB / 2 - kGood * h * epsilonB < 0 := by
    norm_num [kGood, h, d₀, epsilonB]
  linarith only [hnum, heta]

/-- Hall's scalar inequality for a nonempty proper atom family. -/
theorem hall_proper_arith {eta q j : ℝ} (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hq : 1 ≤ q) (hj : 0 ≤ j) :
    j *
        ((1 / 2 + kGood * h) * (1 - epsilonB)) + (q - j) * (1 + eta) ≤
      (1 + 2 * d₀) * (q - eta / 2 - j * (1 / 2 + h)) := by
  classical
  let b := (kGood + 1) * h + d₀ + 2 * d₀ * h - epsilonB / 2 - kGood * h * epsilonB - eta
  have hb : b ≤ 0 := (hall_bad_coefficient heta).le
  have ha : 0 ≤ 2 * d₀ - eta := by
    have hd : 0 ≤ d₀ := by norm_num [d₀]
    linarith only [hd, hcap]
  have hqmul := mul_le_mul_of_nonneg_right hq ha
  have hjmul := mul_nonpos_of_nonneg_of_nonpos hj hb
  have hbase : 0 ≤ (2 * d₀ - eta) - (1 + 2 * d₀) * eta / 2 := by
    norm_num [d₀] at hcap ⊢
    linarith only [hcap]
  have hexp : (1 + 2 * d₀) * (q - eta / 2 - j * (1 / 2 + h)) -
      (j *
        ((1 / 2 + kGood * h) * (1 - epsilonB)) + (q - j) * (1 + eta)) =
      q * (2 * d₀ - eta) - (1 + 2 * d₀) * eta / 2 - j * b := by
    dsimp [b]
    ring
  linarith only [hexp, hbase, hqmul, hjmul]

/-- The three-child Hall bound, including hierarchy error `d₀`. -/
theorem hall_three_arith {eta : ℝ} (hcap : eta ≤ d₀) :
    2 + eta ≤ (1 + 2 * d₀) * (2 - eta / 2) := by
  classical
  norm_num [d₀] at hcap ⊢
  linarith only [hcap]

/-- Four children and at most one bad bundle. -/
theorem hall_four_sparse_arith {eta : ℝ} (hcap : eta ≤ d₀) :
    2 + eta + 4 / 10 ≤ (1 + 2 * d₀) * (3 - eta / 2 - (1 / 2 + h)) := by
  classical
  norm_num [d₀, h] at hcap ⊢
  linarith only [hcap]

/-- Four children and two bad bundles; every demand has the fractional discount. -/
theorem hall_four_bad_arith {eta : ℝ} (hcap : eta ≤ d₀) :
    (1 - epsilonB) * (2 + eta) ≤ (1 + 2 * d₀) * (2 - eta / 2 - 2 * h) := by
  classical
  norm_num [d₀, h, epsilonB] at hcap ⊢
  linarith only [hcap]

/-- Five or more children, allowing the worst bad-incident count. -/
theorem hall_many_arith {eta k : ℝ} (hcap : eta ≤ d₀) (hk : 5 ≤ k) :
    2 + eta + k / 10 ≤ (1 + 2 * d₀) * (k - 1 - eta / 2 - k * (1 / 2 + h) / 2) := by
  classical
  norm_num [d₀, h] at hcap ⊢
  linarith only [hcap, hk]

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
variable (H : Hierarchy x e₀ eta)

/-- Demand bounds with Song's upward coefficient and fractional discount. -/
theorem demand_le {μ : TreeDist n x} {S : Finset (Fin n)}
    (D : goodness.MatchingInputs H μ S kGood) (hx : IsRestrictedLP e₀ x) (hS : S ∈ H.cuts)
    (heta : 0 ≤ eta) {u : Finset (Fin n)} (hu : u ∈ H.children S) (k : ℕ) :
    demand x S epsilonB k u ≤ 1 + eta ∧
      (goodness.IsBadIncident H μ S u →
        demand x S epsilonB k u ≤ (1 / 2 + kGood * h) * (1 - epsilonB)) := by
  classical
  have hu_c := H.mem_children.mp hu
  have hup0 := upSum_nonneg hx.nonneg S u
  have hup1 : upSum x S u ≤ 1 + eta :=
    upSum_le_one_add hx (H.avoids S hS) hu_c.2.2.1 (H.child_nonempty hu_c)
      (H.nearMin S hS).cut_le (H.child_nearMin hu_c).cut_le
  have hB0 : 0 ≤ epsilonB := by norm_num [epsilonB]
  have hB1 : epsilonB ≤ 1 := by norm_num [epsilonB]
  have hBp := mul_nonneg hup0 hB0
  constructor
  · unfold demand fFactor zFactor
    split_ifs with h1 h2 h2 <;> nlinarith [h2]
  · intro hbi
    have hbad : upSum x S u ≤ 1 / 2 + kGood * h := D.upSum_le_of_badIncident hu hbi
    have hsmall : 1 / 5 ≤ (1 / 2 + kGood * h) * (1 - epsilonB) := by
      norm_num [h, kGood, epsilonB]
    have hupper : 1 / 2 + kGood * h ≤ 9 / 10 := by norm_num [h, kGood]
    have hprod := mul_le_mul_of_nonneg_right hbad (sub_nonneg.mpr hB1)
    unfold demand fFactor zFactor
    split_ifs with h1 h2 h2
    · nlinarith only [h2.2, hsmall, hBp]
    · nlinarith only [hprod]
    · nlinarith only [h2.2, hsmall]
    · have hlt : upSum x S u < 1 / 10 := by
        by_contra hc
        exact h1 ⟨le_of_not_gt hc, hbad.trans hupper⟩
      nlinarith only [hlt, hsmall]

open Classical in
/-- The demand of a family: bad-incident atoms at `(1/2 + kGood*h)(1 − ε_B)`, the
rest at `1 + ε_η`. -/
theorem sum_demand_le {μ : TreeDist n x} {S : Finset (Fin n)}
    (D : goodness.MatchingInputs H μ S kGood) (hx : IsRestrictedLP e₀ x) (hS : S ∈ H.cuts)
    (heta : 0 ≤ eta)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) (k : ℕ) :
    ∑ u ∈ Q, demand x S epsilonB k u
      ≤ ((Q.filter (goodness.IsBadIncident H μ S)).card : ℝ) *
        ((1 / 2 + kGood * h) * (1 - epsilonB))
        + ((Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u)).card : ℝ) * (1 + eta) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (goodness.IsBadIncident H μ S)]
  have h1 : ∑ u ∈ Q.filter (goodness.IsBadIncident H μ S), demand x S epsilonB k u
      ≤ ((Q.filter (goodness.IsBadIncident H μ S)).card : ℝ) *
        ((1 / 2 + kGood * h) * (1 - epsilonB)) := by
    have := Finset.sum_le_card_nsmul (Q.filter (goodness.IsBadIncident H μ S))
      (fun u => demand x S epsilonB k u) ((1 / 2 + kGood * h) * (1 - epsilonB)) fun u hu =>
        (demand_le H D hx hS heta (hQ (Finset.mem_filter.mp hu).1) k).2
          (Finset.mem_filter.mp hu).2
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ u ∈ Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u), demand x S epsilonB k u
      ≤ ((Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u)).card : ℝ) * (1 + eta) := by
    have := Finset.sum_le_card_nsmul (Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u))
      (fun u => demand x S epsilonB k u) (1 + eta) fun u hu =>
        (demand_le H D hx hS heta (hQ (Finset.mem_filter.mp hu).1) k).1
    rwa [nsmul_eq_mul] at this
  linarith

set_option maxHeartbeats 2000000 in
-- The cardinality cases combine finite-sum identities, parity and exact rational bounds.
/-- Hall's inequality from the two policy-specific probabilistic inputs. -/
theorem hall_inequality_of_inputs (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (D : goodness.MatchingInputs H μ S kGood)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) :
    ∑ u ∈ Q, demand x S epsilonB (H.children S).card u ≤
      goodness.touchCap μ (2 * d₀) (H.children S) Q := by
  classical
  have hh0 : 0 ≤ h := by norm_num [h]
  have hB0 : 0 ≤ epsilonB := by norm_num [epsilonB]
  have hBless : epsilonB < 1 := by norm_num [epsilonB]
  have hdiscount : 0 ≤ 1 - epsilonB := by norm_num [epsilonB]
  have hα0 : 0 ≤ 2 * d₀ := by norm_num [d₀]
  have hscale : 0 ≤ 1 + 2 * d₀ := by norm_num [d₀]
  have htriangle : (4 * kGood + 2) * goodness.halfWidth + eta < 1 := by
    have hnum : (4 * kGood + 2) * h + d₀ < 1 := by norm_num [h, kGood, d₀]
    change (4 * kGood + 2) * h + eta < 1
    linarith only [hnum, hcap]
  have hjQ : (Q.filter (goodness.IsBadIncident H μ S)).card ≤ Q.card := Finset.card_filter_le _ _
  have hcards : (Q.filter (goodness.IsBadIncident H μ S)).card
      + (Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u)).card = Q.card :=
    Finset.card_filter_add_card_filter_not _
  have hdem := sum_demand_le H D hx hS heta hQ (H.children S).card
  have hcapeq := goodness.touchCap_eq H (μ := μ) (S := S) (α := 2 * d₀) Q
  rw [H.sum_touch_pairSum hQ] at hcapeq
  have hbad := goodness.badCap_touch_le H D hx hQ
  rw [show goodness.halfWidth = h from rfl] at hbad
  have hjR : ((Q.filter (goodness.IsBadIncident H μ S)).card : ℝ) ≤ Q.card := by exact_mod_cast hjQ
  have hcR : ((Q.filter (goodness.IsBadIncident H μ S)).card : ℝ)
      + ((Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u)).card : ℝ) = Q.card := by
    exact_mod_cast hcards
  have hjnn : (0 : ℝ) ≤ (Q.filter (goodness.IsBadIncident H μ S)).card := Nat.cast_nonneg _
  rcases eq_or_ne Q (H.children S) with hQch | hQch
  · /- ### `Q = A(S)`: Claim 6.5 -/
    subst hQch
    have hne : (H.children S).Nonempty :=
      Finset.card_pos.mp ((show (0 : ℕ) < 3 by norm_num).trans_le h3)
    have hsumup := H.sum_upSum_children x hS hne
    have hcS := (H.nearMin S hS).cut_le
    have hcS2 := H.two_le_cutSum hx hS
    have htop := H.topSum_ge hx hS hne
    have hbadall := goodness.badCap_all_le H D
    rw [show goodness.halfWidth = h from rfl] at hbadall
    -- the all-touching bad mass is the bad mass
    have hbadeq : ∑ u ∈ (H.children S), ∑ u' ∈ (H.children S).erase u,
        (if (u ∈ (H.children S) ∨ u' ∈ (H.children S)) ∧ ¬ goodness.IsGood μ u u'
          then pairSum x u u' / 2 else 0)
        = ∑ u ∈ (H.children S), ∑ u' ∈ (H.children S).erase u,
        (if ¬ goodness.IsGood μ u u' then pairSum x u u' / 2 else 0) := by
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' _ => ?_
      simp [hu]
    rw [hbadeq] at hcapeq
    -- the demand: at most `x(δ(S)) + [k ≥ 4] k/10`
    have hdemZ : ∑ u ∈ (H.children S), demand x S epsilonB (H.children S).card u
        ≤ cutSum x S + (if 4 ≤ (H.children S).card then ((H.children S).card : ℝ) / 10 else 0) := by
      have hterm : ∀ u ∈ (H.children S), demand x S epsilonB (H.children S).card u
          ≤ upSum x S u + (if 4 ≤ (H.children S).card then (1 : ℝ) / 10 else 0) := by
        intro u hu
        have hup0 := upSum_nonneg hx.nonneg S u
        have hF := fFactor_le_one (x := x) (S := S) hB0 u
        have hFnn : 0 ≤ fFactor x S epsilonB u := (fFactor_pos (by linarith) u).le
        have hZ1 := one_le_zFactor (x := x) S (H.children S).card u
        have hZ : upSum x S u * zFactor x S (H.children S).card u
            ≤ upSum x S u + (if 4 ≤ (H.children S).card then (1 : ℝ) / 10 else 0) := by
          unfold zFactor
          split_ifs with hz hk hk
          · linarith [hz.2]
          · exact absurd hz.1 hk
          · linarith
          · linarith
        unfold demand
        nlinarith [mul_le_mul_of_nonneg_right hF
          (mul_nonneg hup0
            (hZ1.trans' (by norm_num) : (0 : ℝ) ≤ zFactor x S (H.children S).card u))]
      calc ∑ u ∈ (H.children S), demand x S epsilonB (H.children S).card u
          ≤ ∑ u ∈ (H.children S),
              (upSum x S u + (if 4 ≤ (H.children S).card then (1 : ℝ) / 10 else 0)) :=
            Finset.sum_le_sum hterm
        _ = cutSum x S +
            (if 4 ≤ (H.children S).card then ((H.children S).card : ℝ) / 10 else 0) := by
            rw [Finset.sum_add_distrib, hsumup, Finset.sum_const, nsmul_eq_mul]
            split_ifs
            all_goals simp
            all_goals ring
    -- the touching mass is `x(E→(S))`
    have htouch : Hierarchy.touchSum x S (H.children S) = H.topSum x S := rfl
    rw [htouch] at hcapeq
    have hjk : (((H.children S).filter (goodness.IsBadIncident H μ S)).card : ℝ) ≤
        (H.children S).card := hjR
    have hk3 : (3 : ℝ) ≤ (H.children S).card := by exact_mod_cast h3
    rw [hcapeq]
    set j : ℝ := (((H.children S).filter (goodness.IsBadIncident H μ S)).card : ℝ) with hj
    set B := ∑ u ∈ (H.children S), ∑ u' ∈ (H.children S).erase u,
      (if ¬ goodness.IsGood μ u u' then pairSum x u u' / 2 else 0) with hB
    have hBnn : 0 ≤ B := by
      rw [hB]
      refine Finset.sum_nonneg fun u hu => Finset.sum_nonneg fun u' hu' => ?_
      have hp : 0 ≤ pairSum x u u' / 2 :=
        div_nonneg (pairSum_nonneg_lp hx.nonneg (H.children_disjoint (H.mem_children.mp hu)
          (H.mem_children.mp (Finset.mem_erase.mp hu').2)
          (Ne.symm (Finset.mem_erase.mp hu').1))) (by norm_num)
      split_ifs <;> first | exact le_rfl | exact hp
    -- cases on `k = |A(S)|`
    rcases Nat.lt_or_ge (H.children S).card 4 with hk4 | hk4
    · -- `k = 3`: no bad bundle
      have hk3' : (H.children S).card = 3 := by omega
      have hj0 : ((H.children S).filter (goodness.IsBadIncident H μ S)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u hu ⟨u', hu', huu', hbad⟩
        exact hbad (D.isGood_of_card_three hx hS hk3' htriangle hu hu' huu')
      have hj0R : j = 0 := by rw [hj, hj0]; simp
      rw [hj0R] at hbadall
      simp only [zero_mul, zero_div] at hbadall
      rw [if_neg (not_le.mpr hk4)] at hdemZ
      simp only [add_zero] at hdemZ
      have hkR : ((H.children S).card : ℝ) = 3 := by exact_mod_cast hk3'
      rw [hkR] at htop
      have hB0 : B = 0 := le_antisymm hbadall hBnn
      rw [hB0, sub_zero]
      have hmass : 2 - eta / 2 ≤ H.topSum x S := by linarith only [htop]
      exact hdemZ.trans (hcS.trans ((hall_three_arith hcap).trans
        (mul_le_mul_of_nonneg_left hmass hscale)))
    · rw [if_pos hk4] at hdemZ
      have hk4R : (4 : ℝ) ≤ (H.children S).card := by exact_mod_cast hk4
      rcases Nat.lt_or_ge (H.children S).card 5 with hk5 | hk5
      · -- `k = 4`
        have hk4' : (H.children S).card = 4 := by omega
        have hkR : ((H.children S).card : ℝ) = 4 := by exact_mod_cast hk4'
        rw [hkR] at htop hdemZ
        have heven := D.badIncident_card_even
        have hj4 : ((H.children S).filter (goodness.IsBadIncident H μ S)).card ≤ 4 := by
          rw [← hk4']
          exact hjQ
        rcases Nat.lt_or_ge ((H.children S).filter (goodness.IsBadIncident H μ S)).card 3 with
          hjlt | hjge
        · -- at most one bad bundle
          have hjR2 : j ≤ 2 := by
            rw [hj]
            exact_mod_cast (by omega :
              ((H.children S).filter (goodness.IsBadIncident H μ S)).card ≤ 2)
          have hBle : B ≤ 1 / 2 + h := by nlinarith
          have hmass : 3 - eta / 2 - (1 / 2 + h) ≤ H.topSum x S - B := by
            linarith only [htop, hBle]
          have hdemcap : cutSum x S + 4 / 10 ≤ 2 + eta + 4 / 10 := by
            linarith only [hcS]
          exact hdemZ.trans (hdemcap.trans
            ((hall_four_sparse_arith hcap).trans (mul_le_mul_of_nonneg_left hmass hscale)))
        · -- `j = 4`: every atom is bad-incident, hence fractional
          have hj4' : ((H.children S).filter (goodness.IsBadIncident H μ S)).card = 4 := by
            rcases heven with ⟨m, hm⟩; omega
          have hall : ∀ u ∈ (H.children S), goodness.IsBadIncident H μ S u := by
            intro u hu
            have : (H.children S).filter (goodness.IsBadIncident H μ S) = (H.children S) :=
              Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hj4', hk4'])
            rw [← this] at hu
            exact (Finset.mem_filter.mp hu).2
          have hup : ∀ u ∈ (H.children S), upSum x S u ≤ 1 / 2 + kGood * h :=
            fun u hu => D.upSum_le_of_badIncident hu (hall u hu)
          have hfour : 1 / 10 + 3 * (1 / 2 + kGood * h) < 2 := by
            norm_num [h, kGood]
          have hupper : 1 / 2 + kGood * h ≤ 9 / 10 := by norm_num [h, kGood]
          have hlow : ∀ u ∈ (H.children S), 1 / 10 < upSum x S u := by
            intro u hu
            by_contra hc
            push Not at hc
            have hrest : ∑ u' ∈ (H.children S).erase u, upSum x S u' ≤ 3 * (1 / 2 + kGood * h) := by
              have := Finset.sum_le_card_nsmul ((H.children S).erase u) (fun u' => upSum x S u')
                (1 / 2 + kGood * h) fun u' hu' => hup u' (Finset.mem_erase.mp hu').2
              rw [nsmul_eq_mul, Finset.card_erase_of_mem hu, hk4'] at this
              norm_num at this
              linarith
            have hsplit := Finset.sum_erase_add (H.children S) (fun u' => upSum x S u') hu
            linarith
          have hdem' : ∑ u ∈ (H.children S), demand x S epsilonB (H.children S).card u =
              (1 - epsilonB) * cutSum x S := by
            rw [← hsumup, Finset.mul_sum]
            refine Finset.sum_congr rfl fun u hu => ?_
            unfold demand fFactor zFactor
            rw [if_pos ⟨(hlow u hu).le, by linarith [hup u hu]⟩,
              if_neg (fun h => absurd h.2 (not_le.mpr (hlow u hu)))]
            ring
          rw [hdem']
          have hjR4 : j = 4 := by rw [hj, hj4']; norm_num
          rw [hjR4] at hbadall
          have hmass : 2 - eta / 2 - 2 * h ≤ H.topSum x S - B := by
            linarith only [htop, hbadall]
          exact (mul_le_mul_of_nonneg_left hcS hdiscount).trans
            ((hall_four_bad_arith hcap).trans (mul_le_mul_of_nonneg_left hmass hscale))
      · -- `k ≥ 5`
        have hk5R : (5 : ℝ) ≤ (H.children S).card := by exact_mod_cast hk5
        have hBle : B ≤ ((H.children S).card : ℝ) * (1 / 2 + h) / 2 :=
          le_trans hbadall (by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_right hjk (by norm_num [h]))
        have hmass : ((H.children S).card : ℝ) - 1 - eta / 2 -
            ((H.children S).card : ℝ) * (1 / 2 + h) / 2 ≤ H.topSum x S - B := by
          linarith only [htop, hBle]
        have hdemcap : cutSum x S + ((H.children S).card : ℝ) / 10 ≤
            2 + eta + ((H.children S).card : ℝ) / 10 := by
          linarith only [hcS]
        exact hdemZ.trans (hdemcap.trans
          ((hall_many_arith hcap hk5R).trans (mul_le_mul_of_nonneg_left hmass hscale)))
  · /- ### `Q ⊊ A(S)`: KKO (30) -/
    rcases Q.eq_empty_or_nonempty with hQe | hQne
    · subst hQe
      simp only [Finset.sum_empty]
      unfold BundleGoodnessPolicy.touchCap
      refine Finset.sum_nonneg fun u hu => Finset.sum_nonneg fun u' hu' => ?_
      split_ifs with h
      · exact goodness.rowCap_nonneg hx.nonneg μ hα0 (H.children_disjoint (H.mem_children.mp hu)
          (H.mem_children.mp (Finset.mem_erase.mp hu').2) (Ne.symm (Finset.mem_erase.mp hu').1))
      · exact le_rfl
    have htouch := H.touchSum_ge_card hx hS hQ hQch
    have hq1 : (1 : ℝ) ≤ Q.card := by exact_mod_cast Finset.card_pos.mpr hQne
    rw [hcapeq]
    set j : ℝ := ((Q.filter (goodness.IsBadIncident H μ S)).card : ℝ) with hj
    set q : ℝ := (Q.card : ℝ) with hq
    have key := hall_proper_arith heta hcap hq1 hjnn
    have hQj : ((Q.filter (fun u => ¬ goodness.IsBadIncident H μ S u)).card : ℝ) = q - j := by
      rw [hq, hj]; linarith
    rw [hQj] at hdem
    have h1 := mul_le_mul_of_nonneg_left hbad (by norm_num [d₀] : (0 : ℝ) ≤ 1 + (2 * d₀))
    have h2 := mul_le_mul_of_nonneg_left htouch (by norm_num [d₀] : (0 : ℝ) ≤ 1 + (2 * d₀))
    linarith

/-- The actual hierarchy and tree law satisfy Hall's condition at fixed inflation `2*d₀`. -/
theorem hall_inequality (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ H.children S) :
    ∑ u ∈ Q, demand x S epsilonB (H.children S).card u ≤
      goodness.touchCap μ (2 * d₀) (H.children S) Q :=
  hall_inequality_of_inputs H hx hS (matchingInputs hx μ hμ H heta hcap) h3 heta hcap hQ


/-- A saturating flow on Song-good ordered bundles, constructed from the actual law. -/
theorem exists_saturating_flow (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∃ z : OrientedBundle (H.children S) → {u // u ∈ H.children S} → ℝ,
      IsFlow (goodness.arcCapacity x μ (H.children S) (2 * d₀))
        (goodness.rowCapacity x μ (H.children S) (2 * d₀))
        (colCapacity x S (H.children S) epsilonB (H.children S).card) z ∧
      ∀ u, ∑ p, z p u = colCapacity x S (H.children S) epsilonB (H.children S).card u := by
  classical
  apply goodness.exists_saturating_flow x μ S (H.children S) (2 * d₀) epsilonB
    (H.children S).card hx.nonneg (by norm_num [d₀]) (by norm_num [epsilonB])
  · exact fun u hu v hv huv =>
      H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hv) huv
  · exact fun Q hQ => hall_inequality H hx μ hμ hS h3 heta hcap hQ

/-- Song's matching data at fixed inflation `2*d₀` and discount `epsilonB`. -/
theorem exists_matchingData (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    Nonempty (goodness.MatchingData H μ S epsilonB (2 * d₀)) :=
  goodness.exists_matchingData_of_hall hx μ H S (epsilonB := epsilonB) (alpha := 2 * d₀)
    (by norm_num [epsilonB]) (by norm_num [d₀])
    (fun Q hQ => hall_inequality H hx μ hμ hS h3 heta hcap hQ)

/-- **Song's Lemma 16:** allocation support, bundle capacity and atom conservation. -/
theorem lemma_6_2 (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∃ m : Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ u v, 0 ≤ m u v) ∧
      (∀ u v, m u v ≠ 0 →
        u ∈ H.children S ∧ v ∈ H.children S ∧ u ≠ v ∧ goodness.IsGood μ u v) ∧
      (∀ u ∈ H.children S, ∀ v ∈ H.children S, u ≠ v →
        m u v * fFactor x S epsilonB u + m v u * fFactor x S epsilonB v ≤
          (1 + 2 * d₀) * pairSum x u v) ∧
      (∀ u ∈ H.children S,
        ∑ v ∈ (H.children S).erase u, m u v = upSum x S u * zFactor x S (H.children S).card u) := by
  obtain ⟨M⟩ := exists_matchingData H hx μ hμ hS h3 heta hcap
  exact ⟨M.m, M.nonneg, M.support, M.bound, M.sum⟩

/-- The allocation producer at the actual hierarchy error `7*t`. -/
theorem exists_matchingData_seven_mul (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {t : ℝ} (ht : 0 ≤ t) (htH : t ≤ Song.H)
    (Ht : Hierarchy x e₀ (7 * t)) {S : Finset (Fin n)} (hS : S ∈ Ht.cuts)
    (h3 : 3 ≤ (Ht.children S).card) :
    Nonempty (goodness.MatchingData Ht μ S epsilonB (2 * d₀)) := by
  apply exists_matchingData Ht hx μ hμ hS h3 (by positivity)
  have hnum : 7 * Song.H ≤ d₀ := by norm_num [Song.H, d₀]
  linarith only [htH, hnum]

end TSPGap.Song

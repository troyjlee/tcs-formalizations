/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RankSequence

/-!
# Stability of conditioned extreme faces

Conditioning a fixed-rank stable weight on a **minimum-cost face** preserves
stability, by external-field scaling into the existing fixed-rank limit
theorem — no new Hurwitz-type theorem, and no boundary specialization.

For an integer coordinate cost `c` with `m` a lower bound for the cost on the
support, tilt the weight by the external field `t ↦ t^{c(S) − m}` and
normalize:

`w_t(S) = w(S) · t^{c(S) − m} / Z_t,   t > 0.`

Each `w_t` is a positive coordinate scaling (`X i ↦ t^{c i} · X i`) followed
by a nonzero scalar, so it is stable; it stays nonnegative, fixed-rank and
normalized.  As `t → 0⁺` it converges to `w` conditioned on `c(S) = m`,
normalized, and `isRealStable_of_approx` — the same adapter that closed the
max-entropy limit — supplies stability of the conditioned law.  The
convergence is by explicit estimate, not filters: for `0 < t ≤ 1` every
coordinate of the difference is at most `t·B` with
`B = T/W + T²/W²` (`T` the total mass, `W` the face mass).

This one theorem covers an edge forced out or in, finite cylinders, maximal
internal-edge counts (hence "induces a tree"), and intersections of such
conditions — each is a choice of cost vector.  Forced-in coordinates stay in
the ambient set, preserving the rank.

* `setCost`, `faceWeight`, `faceDist` — the cost, the conditioned weight,
  and its normalization.
* `isRealStable_genPoly_faceDist` — the main theorem.
* `isRealStableOrZero_genPoly_faceWeight` — the zero-mass form: no
  positivity hypothesis, `IsRealStableOrZero` conclusion.
* `isRealStableOrZero_genPoly_deleteWeight` — the first corollary: an edge
  forced out is the face of the indicator cost at minimum `0`.
* `exists_bernoulli_rank_law_faceDist` — the Bernoulli rank law for the
  conditioned law, by instantiating `RankSequence`.
-/

namespace TSPGap

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The additive cost of a set under integer coordinate costs. -/
def setCost (c : ι → ℕ) (S : Finset ι) : ℕ := ∑ i ∈ S, c i

/-- `w` conditioned on the cost-`m` face, unnormalized. -/
def faceWeight (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) : Finset ι → ℝ :=
  fun S => if setCost c S = m then w S else 0

/-- The normalized conditioned law. -/
noncomputable def faceDist (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) :
    Finset ι → ℝ :=
  fun S => faceWeight w c m S / totalMass (faceWeight w c m)

omit [Fintype ι] [DecidableEq ι] in
theorem weightNonneg_faceWeight {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (c : ι → ℕ) (m : ℕ) : WeightNonneg (faceWeight w c m) := by
  intro S
  rw [faceWeight]
  split_ifs
  · exact hnn S
  · exact le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem faceWeight_eq_zero_of_weight {w : Finset ι → ℝ} {c : ι → ℕ} {m : ℕ}
    {S : Finset ι} (h : w S = 0) : faceWeight w c m S = 0 := by
  rw [faceWeight]
  split_ifs
  · exact h
  · rfl

omit [DecidableEq ι] in
/-- The normalized face is a fixed-rank normalized weight. -/
theorem fixedRankNormalized_faceDist {w : Finset ι → ℝ} {r : ℕ} {c : ι → ℕ}
    {m : ℕ} (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    (hmass : 0 < totalMass (faceWeight w c m)) :
    FixedRankNormalized r (faceDist w c m) := by
  refine ⟨fun S => div_nonneg (weightNonneg_faceWeight hnn c m S) hmass.le,
    fun S hS => ?_, ?_⟩
  · have h0 : w S = 0 := by
      by_contra hc
      exact hS (hr S hc)
    rw [faceDist, faceWeight_eq_zero_of_weight h0, zero_div]
  · rw [show ∑ S : Finset ι, faceDist w c m S
        = totalMass (faceWeight w c m) / totalMass (faceWeight w c m) by
      rw [totalMass, Finset.sum_div]
      rfl]
    exact div_self hmass.ne'

/-- **Stability of the conditioned extreme face.**  The external field
`t^{c(S) − m}` realizes the conditioned law as a limit of positive coordinate
scalings of `w`, and the fixed-rank limit adapter carries stability across. -/
theorem isRealStable_genPoly_faceDist {w : Finset ι → ℝ} {r : ℕ} {c : ι → ℕ}
    {m : ℕ} (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (hmin : ∀ S, w S ≠ 0 → m ≤ setCost c S)
    (hmass : 0 < totalMass (faceWeight w c m)) :
    IsRealStable (genPoly (faceDist w c m)) := by
  classical
  set W : ℝ := totalMass (faceWeight w c m) with hW
  set T : ℝ := totalMass w with hT
  have hface_le_w : ∀ S, faceWeight w c m S ≤ w S := by
    intro S
    rw [faceWeight]
    split_ifs
    · exact le_rfl
    · exact hnn S
  have hWT : W ≤ T := Finset.sum_le_sum fun S _ => hface_le_w S
  have hTpos : 0 < T := lt_of_lt_of_le hmass hWT
  have hwT : ∀ S, w S ≤ T := fun S =>
    Finset.single_le_sum (fun S' _ => hnn S') (Finset.mem_univ S)
  set B : ℝ := T / W + T ^ 2 / W ^ 2 with hB
  have hBpos : 0 < B := by positivity
  refine isRealStable_of_approx (fixedRankNormalized_faceDist hr hnn hmass)
    fun δ hδ => ?_
  set t : ℝ := min 1 (δ / B) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hδ hBpos)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htB : t * B ≤ δ := by
    calc t * B ≤ δ / B * B :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hBpos.le
      _ = δ := div_mul_cancel₀ δ hBpos.ne'
  set Zt : ℝ := ∑ S : Finset ι, w S * t ^ (setCost c S - m) with hZt
  -- the partition function is trapped between the face and total masses
  have hface_le : ∀ S : Finset ι,
      faceWeight w c m S ≤ w S * t ^ (setCost c S - m) := by
    intro S
    rw [faceWeight]
    split_ifs with h
    · rw [h, Nat.sub_self, pow_zero, mul_one]
    · exact mul_nonneg (hnn S) (pow_nonneg ht0.le _)
  have hWZ : W ≤ Zt := Finset.sum_le_sum fun S _ => hface_le S
  have hZpos : 0 < Zt := lt_of_lt_of_le hmass hWZ
  have hZW : Zt - W ≤ t * T := by
    have hsplit : Zt - W = ∑ S : Finset ι,
        (w S * t ^ (setCost c S - m) - faceWeight w c m S) := by
      rw [hZt, hW, totalMass, ← Finset.sum_sub_distrib]
    rw [hsplit, hT, totalMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [faceWeight]
    split_ifs with h
    · rw [h, Nat.sub_self, pow_zero, mul_one, sub_self]
      exact mul_nonneg ht0.le (hnn S)
    · rcases eq_or_ne (w S) 0 with h0 | h0
      · simp [h0]
      · have h1 : 1 ≤ setCost c S - m := by
          have := hmin S h0
          omega
        have hpow : t ^ (setCost c S - m) ≤ t := by
          calc t ^ (setCost c S - m) ≤ t ^ 1 :=
                pow_le_pow_of_le_one ht0.le ht1 h1
            _ = t := pow_one t
        calc w S * t ^ (setCost c S - m) - 0
            = w S * t ^ (setCost c S - m) := by ring
          _ ≤ w S * t := mul_le_mul_of_nonneg_left hpow (hnn S)
          _ = t * w S := mul_comm _ _
  refine ⟨fun S => w S * t ^ (setCost c S - m) / Zt, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- nonneg
    exact fun S =>
      div_nonneg (mul_nonneg (hnn S) (pow_nonneg ht0.le _)) hZpos.le
  · -- supported at rank r
    intro S hS
    have h0 : w S = 0 := by
      by_contra hc
      exact hS (hr S hc)
    rw [h0, zero_mul, zero_div]
  · -- total mass one
    rw [← Finset.sum_div, ← hZt]
    exact div_self hZpos.ne'
  · -- stability: positive coordinate scaling and a nonzero scalar
    have h1 : IsRealStable (genPoly fun S => w S * ∏ i ∈ S, t ^ c i) := by
      have h := hst.scale (c := fun i => t ^ c i) fun i => pow_pos ht0 _
      rwa [bind₁_scale_genPoly] at h
    have h2 := h1.const_mul (c := (t ^ m * Zt)⁻¹)
      (inv_ne_zero (by positivity))
    rw [const_mul_genPoly] at h2
    have hveq : (fun S => (t ^ m * Zt)⁻¹ * (w S * ∏ i ∈ S, t ^ c i))
        = fun S => w S * t ^ (setCost c S - m) / Zt := by
      funext S
      rw [Finset.prod_pow_eq_pow_sum,
        show (∑ i ∈ S, c i) = setCost c S from rfl]
      rcases eq_or_ne (w S) 0 with h0 | h0
      · simp [h0]
      · have hle := hmin S h0
        have hpow : t ^ setCost c S = t ^ m * t ^ (setCost c S - m) := by
          rw [← pow_add, Nat.add_sub_cancel' hle]
        rw [hpow]
        field_simp
    rwa [hveq] at h2
  · -- δ-closeness, coordinatewise
    intro S
    have hdivle : ∀ a b cc d : ℝ, 0 ≤ a → a ≤ cc → 0 < d → d ≤ b →
        a / b ≤ cc / d := by
      intro a b cc d ha hac hd hdb
      have hb : 0 < b := lt_of_lt_of_le hd hdb
      rw [div_le_div_iff₀ hb hd]
      calc a * d ≤ cc * d := mul_le_mul_of_nonneg_right hac hd.le
        _ ≤ cc * b := mul_le_mul_of_nonneg_left hdb (le_trans ha hac)
    have hcase : |w S * t ^ (setCost c S - m) / Zt - faceDist w c m S|
        ≤ t * B := by
      rcases eq_or_ne (w S) 0 with h0 | h0
      · rw [h0, faceDist, faceWeight_eq_zero_of_weight h0]
        simpa using mul_nonneg ht0.le hBpos.le
      · rw [faceDist, faceWeight]
        split_ifs with h
        · -- on the face: both are `w S` over nearby denominators
          rw [h, Nat.sub_self, pow_zero, mul_one]
          have hmono : w S / Zt ≤ w S / W :=
            hdivle _ _ _ _ (hnn S) le_rfl hmass hWZ
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hmono)]
          have heq : w S / W - w S / Zt = w S * (Zt - W) / (W * Zt) := by
            field_simp
          rw [heq]
          calc w S * (Zt - W) / (W * Zt) ≤ T * (t * T) / (W * W) :=
                hdivle _ _ _ _
                  (mul_nonneg (hnn S) (sub_nonneg.mpr hWZ))
                  (mul_le_mul (hwT S) hZW (sub_nonneg.mpr hWZ) hTpos.le)
                  (mul_pos hmass hmass)
                  (mul_le_mul_of_nonneg_left hWZ hmass.le)
            _ = t * (T ^ 2 / W ^ 2) := by
                field_simp
            _ ≤ t * B := by
                have hTB : T ^ 2 / W ^ 2 ≤ B := by
                  rw [hB]
                  have : 0 ≤ T / W := by positivity
                  linarith
                exact mul_le_mul_of_nonneg_left hTB ht0.le
        · -- off the face: the tilt kills the term
          have h1 : 1 ≤ setCost c S - m := by
            have := hmin S h0
            omega
          have hpow : t ^ (setCost c S - m) ≤ t := by
            calc t ^ (setCost c S - m) ≤ t ^ 1 :=
                  pow_le_pow_of_le_one ht0.le ht1 h1
              _ = t := pow_one t
          rw [zero_div, sub_zero,
            abs_of_nonneg (div_nonneg
              (mul_nonneg (hnn S) (pow_nonneg ht0.le _)) hZpos.le)]
          calc w S * t ^ (setCost c S - m) / Zt ≤ T * t / W :=
                hdivle _ _ _ _
                  (mul_nonneg (hnn S) (pow_nonneg ht0.le _))
                  (mul_le_mul (hwT S) hpow (pow_nonneg ht0.le _) hTpos.le)
                  hmass hWZ
            _ = t * (T / W) := by ring
            _ ≤ t * B := by
                have hTB : T / W ≤ B := by
                  rw [hB]
                  have : 0 ≤ T ^ 2 / W ^ 2 := by positivity
                  linarith
                exact mul_le_mul_of_nonneg_left hTB ht0.le
    exact hcase.trans htB

/-- **The zero-mass form**: with no positivity hypothesis, the unnormalized
face is stable or identically zero. -/
theorem isRealStableOrZero_genPoly_faceWeight {w : Finset ι → ℝ} {r : ℕ}
    {c : ι → ℕ} {m : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    (hmin : ∀ S, w S ≠ 0 → m ≤ setCost c S) :
    IsRealStableOrZero (genPoly (faceWeight w c m)) := by
  classical
  rcases eq_or_lt_of_le (Finset.sum_nonneg
      fun S _ => weightNonneg_faceWeight hnn c m S) with hzero | hmass
  · -- zero mass: every face weight vanishes
    left
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      fun S _ => weightNonneg_faceWeight hnn c m S).mp hzero.symm
    have hfw : faceWeight w c m = fun _ => (0 : ℝ) :=
      funext fun S => hall S (Finset.mem_univ S)
    rw [hfw, genPoly]
    simp
  · -- positive mass: rescale the normalized face
    right
    have hmass : 0 < totalMass (faceWeight w c m) := hmass
    have hstface := isRealStable_genPoly_faceDist hst hr hnn hmin hmass
    have h2 := hstface.const_mul (c := totalMass (faceWeight w c m)) hmass.ne'
    rw [const_mul_genPoly] at h2
    have heq : (fun S => totalMass (faceWeight w c m) * faceDist w c m S)
        = faceWeight w c m := by
      funext S
      rw [faceDist, mul_div_cancel₀ _ hmass.ne']
    rwa [heq] at h2

/-! ### First corollary: an edge forced out -/

omit [Fintype ι] in
/-- The indicator cost of a single coordinate realizes `deleteWeight` as the
minimum-cost face at `m = 0`. -/
theorem faceWeight_indicator_eq_deleteWeight (w : Finset ι → ℝ) (e : ι) :
    faceWeight w (fun i => if i = e then 1 else 0) 0 = deleteWeight w e := by
  classical
  funext S
  rw [faceWeight, deleteWeight, setCost, Finset.sum_ite_eq' S e fun _ => 1]
  by_cases h : e ∈ S
  · rw [if_pos h, if_pos h, if_neg one_ne_zero]
  · rw [if_neg h, if_neg h, if_pos rfl]

/-- **Deletion preserves stability** (or kills the weight): forcing an edge
out is conditioning on the zero-cost face of its indicator. -/
theorem isRealStableOrZero_genPoly_deleteWeight {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (e : ι) :
    IsRealStableOrZero (genPoly (deleteWeight w e)) := by
  rw [← faceWeight_indicator_eq_deleteWeight]
  exact isRealStableOrZero_genPoly_faceWeight hst hr hnn
    fun S _ => Nat.zero_le _

/-! ### The Bernoulli rank law for the conditioned law -/

/-- **The conditioned Bernoulli rank law**: the rank sequence of the
normalized face along any `F` is a Bernoulli-sum law — `RankSequence`
instantiated at the conditioned law, which the face-stability theorem has
just qualified. -/
theorem exists_bernoulli_rank_law_faceDist {w : Finset ι → ℝ} {r : ℕ}
    {c : ι → ℕ} {m : ℕ} (hst : IsRealStable (genPoly w))
    (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    (hmin : ∀ S, w S ≠ 0 → m ≤ setCost c S)
    (hmass : 0 < totalMass (faceWeight w c m)) (F : Finset ι) :
    ∃ (m' : ℕ) (q : Fin m' → ℝ), (∀ j, 0 < q j ∧ q j ≤ 1) ∧
      ∀ k : ℕ, weightMass (faceDist w c m) (fun S => (S ∩ F).card = k)
        = Bernoulli.probCount q k := by
  have hFRN := fixedRankNormalized_faceDist hr hnn hmass
  refine exists_bernoulli_rank_law (r := r)
    (isRealStable_genPoly_faceDist hst hr hnn hmin hmass)
    (fun S h0 => ?_) hFRN.nonneg ?_ F
  · by_contra hc
    exact h0 (hFRN.supported S hc)
  · rw [totalMass]
    exact hFRN.total

/-! ### The cylinder face

The cost `2` on forced-out coordinates, `0` on forced-in ones, `1` elsewhere
has the cylinder as its minimum-cost face: on the rank-`r` support the cost
is `r + |S ∩ O| − |S ∩ I| ≥ r − |I|`, with equality exactly at the cylinder.
Forced-in coordinates stay in the ambient set, so the rank is preserved. -/

/-- The cost whose minimum face is the cylinder. -/
def cylCost (I O : Finset ι) : ι → ℕ :=
  fun i => if i ∈ O then 2 else if i ∈ I then 0 else 1

open Classical in
/-- `w` conditioned on a cylinder, unnormalized. -/
noncomputable def cylinderFaceWeight (w : Finset ι → ℝ) (I O : Finset ι) :
    Finset ι → ℝ :=
  fun S => if cylinderEvent I O S then w S else 0

omit [Fintype ι] in
theorem setCost_cylCost {I O : Finset ι} (S : Finset ι) :
    setCost (cylCost I O) S = 2 * (S ∩ O).card + (S \ (I ∪ O)).card := by
  classical
  rw [setCost, ← Finset.sum_filter_add_sum_filter_not S (· ∈ O)]
  have h1 : ∑ i ∈ S.filter (· ∈ O), cylCost I O i = 2 * (S ∩ O).card := by
    rw [Finset.sum_congr rfl fun i hi => show cylCost I O i = 2 from
        if_pos (Finset.mem_filter.mp hi).2,
      Finset.sum_const, Finset.filter_mem_eq_inter, smul_eq_mul, mul_comm]
  have h2 : ∑ i ∈ S.filter (fun i => ¬ i ∈ O), cylCost I O i
      = (S \ (I ∪ O)).card := by
    calc ∑ i ∈ S.filter (fun i => ¬ i ∈ O), cylCost I O i
        = ∑ i ∈ S.filter (fun i => ¬ i ∈ O), (if i ∈ I then 0 else 1) :=
          Finset.sum_congr rfl fun i hi => by
            rw [cylCost, if_neg (Finset.mem_filter.mp hi).2]
      _ = (S \ (I ∪ O)).card := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
            mul_zero, zero_add, smul_eq_mul, mul_one]
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union]
          tauto
  rw [h1, h2]

omit [Fintype ι] in
theorem card_inter_partition {I O : Finset ι} (hIO : Disjoint I O)
    (S : Finset ι) :
    (S ∩ I).card + (S ∩ O).card + (S \ (I ∪ O)).card = S.card := by
  classical
  have h1 : (S ∩ (I ∪ O)).card + (S \ (I ∪ O)).card = S.card :=
    Finset.card_inter_add_card_sdiff S (I ∪ O)
  have h2 : S ∩ (I ∪ O) = (S ∩ I) ∪ (S ∩ O) :=
    Finset.inter_union_distrib_left S I O
  have h3 : Disjoint (S ∩ I) (S ∩ O) :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hIO
  rw [h2, Finset.card_union_of_disjoint h3] at h1
  omega

omit [Fintype ι] in
/-- The cylinder, in the card form `omega` consumes. -/
theorem cylinderEvent_iff_cards {I O S : Finset ι} :
    cylinderEvent I O S ↔ (S ∩ I).card = I.card ∧ (S ∩ O).card = 0 := by
  rw [cylinderEvent]
  constructor
  · rintro ⟨hI, hO⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.inter_eq_right.mpr hI]
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro j hj
      obtain ⟨hjS, hjO⟩ := Finset.mem_inter.mp hj
      exact hO j hjO hjS
  · rintro ⟨hi, ho⟩
    refine ⟨fun j hj => ?_, fun j hjO hjS => ?_⟩
    · have heq : S ∩ I = I :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right hi.ge
      exact (Finset.mem_inter.mp (by rw [heq]; exact hj)).1
    · rw [Finset.card_eq_zero] at ho
      exact absurd (ho ▸ Finset.mem_inter.mpr ⟨hjS, hjO⟩)
        (Finset.notMem_empty j)

omit [Fintype ι] in
/-- **The cylinder is a minimum-cost face** of `cylCost`, at `m = r − |I|`. -/
theorem faceWeight_cylCost_eq {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) {I O : Finset ι} (hIO : Disjoint I O)
    (hIr : I.card ≤ r) :
    faceWeight w (cylCost I O) (r - I.card) = cylinderFaceWeight w I O := by
  classical
  funext S
  rw [faceWeight, cylinderFaceWeight]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · rw [h0]
    split_ifs <;> rfl
  · have hcard := hr S h0
    have hcost := setCost_cylCost (I := I) (O := O) S
    have hpart := card_inter_partition hIO S
    have hle : (S ∩ I).card ≤ I.card :=
      Finset.card_le_card Finset.inter_subset_right
    by_cases hcyl : cylinderEvent I O S
    · obtain ⟨hi, ho⟩ := cylinderEvent_iff_cards.mp hcyl
      rw [if_pos (by rw [hcost]; omega), if_pos hcyl]
    · rw [if_neg fun heq => hcyl (cylinderEvent_iff_cards.mpr
        (by rw [hcost] at heq; omega)), if_neg hcyl]

omit [Fintype ι] in
/-- Every supported set costs at least `r − |I|`. -/
theorem cylCost_min {w : Finset ι → ℝ} {r : ℕ} (hr : FixedRankWeight r w)
    {I O : Finset ι} (hIO : Disjoint I O) :
    ∀ S, w S ≠ 0 → r - I.card ≤ setCost (cylCost I O) S := by
  intro S h0
  have hcard := hr S h0
  rw [setCost_cylCost]
  have hpart := card_inter_partition hIO S
  have hle : (S ∩ I).card ≤ I.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- **Cylinder conditioning preserves stability**, in the zero-mass form. -/
theorem isRealStableOrZero_genPoly_cylinderFaceWeight {w : Finset ι → ℝ}
    {r : ℕ} (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {I O : Finset ι} (hIO : Disjoint I O)
    (hIr : I.card ≤ r) :
    IsRealStableOrZero (genPoly (cylinderFaceWeight w I O)) := by
  rw [← faceWeight_cylCost_eq hr hIO hIr]
  exact isRealStableOrZero_genPoly_faceWeight hst hr hnn (cylCost_min hr hIO)

/-- **The normalized cylinder-conditioned law is stable.** -/
theorem isRealStable_genPoly_cylinderFaceDist {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {I O : Finset ι} (hIO : Disjoint I O)
    (hIr : I.card ≤ r)
    (hmass : 0 < totalMass (cylinderFaceWeight w I O)) :
    IsRealStable (genPoly fun S =>
      cylinderFaceWeight w I O S / totalMass (cylinderFaceWeight w I O)) := by
  rw [← faceWeight_cylCost_eq hr hIO hIr] at hmass ⊢
  exact isRealStable_genPoly_faceDist hst hr hnn (cylCost_min hr hIO) hmass

/-- **The Bernoulli rank law for the cylinder-conditioned law.** -/
theorem exists_bernoulli_rank_law_cylinder {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {I O : Finset ι} (hIO : Disjoint I O)
    (hIr : I.card ≤ r)
    (hmass : 0 < totalMass (cylinderFaceWeight w I O)) (F : Finset ι) :
    ∃ (m' : ℕ) (q : Fin m' → ℝ), (∀ j, 0 < q j ∧ q j ≤ 1) ∧
      ∀ k : ℕ, weightMass (fun S =>
          cylinderFaceWeight w I O S / totalMass (cylinderFaceWeight w I O))
        (fun S => (S ∩ F).card = k) = Bernoulli.probCount q k := by
  rw [← faceWeight_cylCost_eq hr hIO hIr] at hmass ⊢
  exact exists_bernoulli_rank_law_faceDist hst hr hnn (cylCost_min hr hIO)
    hmass F

/-! ### Contraction, by cancelling `X e`

An erased `contractWeight` is recovered from the singleton cylinder:
`genPoly` of the forced-in face is `X e` times `genPoly` of the contraction,
and `X e` never vanishes in the open upper half-plane. -/

theorem genPoly_zero : genPoly (fun _ : Finset ι => (0 : ℝ)) = 0 := by
  rw [genPoly]
  simp

/-- The multi-affine decomposition of a generating polynomial at one
coordinate: the `e`-free part is the deletion, the `e`-divisible part is
`X e` times the contraction. -/
theorem genPoly_delete_add_X_mul_contract (w : Finset ι → ℝ) (e : ι) :
    genPoly w
      = genPoly (deleteWeight w e) + X e * genPoly (contractWeight w e) := by
  classical
  have hcontract : genPoly (contractWeight w e)
      = ∑ V ∈ Finset.univ.filter (fun V : Finset ι => e ∉ V),
          C (w (insert e V)) * ∏ i ∈ V, X i := by
    rw [genPoly, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun V : Finset ι => e ∉ V)]
    have h1 : ∀ V ∈ Finset.univ.filter (fun V : Finset ι => e ∉ V),
        C (contractWeight w e V) * ∏ i ∈ V, X i
          = C (w (insert e V)) * ∏ i ∈ V, X i := fun V hV => by
      rw [contractWeight, if_neg (Finset.mem_filter.mp hV).2]
    have h2 : ∑ V ∈ Finset.univ.filter (fun V : Finset ι => ¬ e ∉ V),
        C (contractWeight w e V) * ∏ i ∈ V, X i = 0 :=
      Finset.sum_eq_zero fun V hV => by
        rw [contractWeight, if_pos (not_not.mp (Finset.mem_filter.mp hV).2)]
        simp
    rw [Finset.sum_congr rfl h1, h2, add_zero]
  have hdelete : genPoly (deleteWeight w e)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => ¬ e ∈ S),
          C (w S) * ∏ i ∈ S, X i := by
    rw [genPoly, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset ι => ¬ e ∈ S)]
    have h1 : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => ¬ e ∈ S),
        C (deleteWeight w e S) * ∏ i ∈ S, X i = C (w S) * ∏ i ∈ S, X i :=
      fun S hS => by
        rw [deleteWeight, if_neg (Finset.mem_filter.mp hS).2]
    have h2 : ∑ S ∈ Finset.univ.filter (fun S : Finset ι => ¬ ¬ e ∈ S),
        C (deleteWeight w e S) * ∏ i ∈ S, X i = 0 :=
      Finset.sum_eq_zero fun S hS => by
        rw [deleteWeight, if_pos (not_not.mp (Finset.mem_filter.mp hS).2)]
        simp
    rw [Finset.sum_congr rfl h1, h2, add_zero]
  have hin : ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S),
      C (w S) * ∏ i ∈ S, X i = X e * genPoly (contractWeight w e) := by
    rw [hcontract, Finset.mul_sum]
    refine Finset.sum_nbij' (fun S => S.erase e) (fun V => insert e V)
      ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact Finset.notMem_erase e S
    · intro V hV
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV ⊢
      exact Finset.mem_insert_self e V
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.insert_erase hS
    · intro V hV
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
      exact Finset.erase_insert hV
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.insert_erase hS, ← Finset.mul_prod_erase S _ hS]
      ring
  rw [genPoly, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun S : Finset ι => e ∈ S), hin, ← hdelete, add_comm]

open Classical in
/-- The forced-in face carries `X e` explicitly. -/
theorem genPoly_cylinderFace_singleton (w : Finset ι → ℝ) (e : ι) :
    genPoly (cylinderFaceWeight w {e} ∅)
      = X e * genPoly (contractWeight w e) := by
  have hdel : deleteWeight (cylinderFaceWeight w {e} ∅) e
      = fun _ => (0 : ℝ) := by
    funext V
    rw [deleteWeight]
    split_ifs with h
    · rfl
    · rw [cylinderFaceWeight,
        if_neg fun hcyl => h (hcyl.1 (Finset.mem_singleton_self e))]
  have hcon : contractWeight (cylinderFaceWeight w {e} ∅) e
      = contractWeight w e := by
    funext V
    rw [contractWeight, contractWeight]
    split_ifs with h
    · rfl
    · rw [cylinderFaceWeight, if_pos
        ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e V),
          fun j hj => absurd hj (Finset.notMem_empty j)⟩]
  have h := genPoly_delete_add_X_mul_contract (cylinderFaceWeight w {e} ∅) e
  rw [hdel, hcon, genPoly_zero, zero_add] at h
  exact h

/-- **Contraction preserves stability** (or kills the weight): derived from
the forced-in face by cancelling `X e`, which never vanishes in the open
upper half-plane. -/
theorem isRealStableOrZero_genPoly_contractWeight {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (e : ι) :
    IsRealStableOrZero (genPoly (contractWeight w e)) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · -- rank zero: nothing contains `e`
    left
    have hzero : contractWeight w e = fun _ => (0 : ℝ) := by
      funext V
      rw [contractWeight]
      split_ifs with h
      · rfl
      · by_contra hc
        have hcard := hr _ hc
        rw [hr0] at hcard
        exact absurd (Finset.card_eq_zero.mp hcard)
          (Finset.insert_ne_empty e V)
    rw [hzero, genPoly_zero]
  · have hcyl := isRealStableOrZero_genPoly_cylinderFaceWeight hst hr hnn
      (I := {e}) (O := ∅) (Finset.disjoint_empty_right _)
      (by simp only [Finset.card_singleton]; exact hr0)
    have hXe := genPoly_cylinderFace_singleton w e
    rcases hcyl with h0 | hstF
    · left
      rw [hXe] at h0
      rcases mul_eq_zero.mp h0 with hX | h
      · exact absurd hX (MvPolynomial.X_ne_zero e)
      · exact h
    · right
      intro z hz hzero
      refine hstF z hz ?_
      rw [hXe, map_mul, MvPolynomial.map_X, eval_mul, eval_X, hzero,
        mul_zero]

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountCapacityExtraction

/-!
# Three certified count extractions

The stable-or-zero projected weights make all three extractions legitimate.
The final block can have target one, or target two with a sure baseline one;
both cost exactly three factors of `exp(-1)`. Empty or impossible layers
are included without normalization or division by their masses.

These theorems consume a uniform capacity lower bound. Supplying it from the
mean profile still requires the grouped-polynomial and baseline-shift bridge.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem blockScale_pos (F : Finset ι) {x : ι → ℝ} {t : ℝ}
    (hx : ∀ i, 0 < x i) (ht : 0 < t) : ∀ i, 0 < blockScale F x t i := by
  intro i
  by_cases hi : i ∈ F <;> simp [blockScale, Finset.piecewise, hi, hx, ht]

/-- Repeated projected count mass is the joint event in the original space.
Disjointness is spent here, not silently assumed in a coefficient rewrite. -/
theorem totalMass_projectCount_three (w : Finset ι → ℝ) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (a b c : ℕ) :
    totalMass (projectCount (projectCount (projectCount w A a) B b) C c) =
      weightMass w (fun S => (S ∩ A).card = a ∧ (S ∩ B).card = b ∧ (S ∩ C).card = c) := by
  rw [totalMass_projectCount, weightMass_projectCount, weightMass_projectCount]
  apply weightMass_congr
  intro S
  rw [inter_projectCount_witness hAB, inter_projectCount_witness hBC,
    inter_projectCount_witness hAC]

/-- **Three-count extraction, including the baseline-one variant.**
The last target is one or two; in the latter case its support baseline is
preserved through the first two projections, then canceled before extraction. -/
theorem three_counts_ge_of_capacity {w : Finset ι → ℝ} {r k : ℕ} {L : ℝ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hk : k = 1 ∨ k = 2)
    (hbase : ∀ S, w S ≠ 0 → k - 1 ≤ (S ∩ C).card)
    (hcap : ∀ a b t : ℝ, 0 < a → 0 < b → 0 < t →
      L * a * b * t ^ k ≤ MvPolynomial.eval
        (blockScale A (blockScale B (blockScale C (fun _ => 1) t) b) a) (genPoly w)) :
    Real.exp (-3) * L ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ C).card = k) := by
  let wA := projectCount w A 1
  let wB := projectCount wA B 1
  have hsA : IsRealStableOrZero (genPoly wA) := isRealStableOrZero_projectCount hst hr hnn A 1
  have hrA : FixedRankWeight (r - 1) wA := fixedRankWeight_projectCount hr A 1
  have hnA : WeightNonneg wA := weightNonneg_projectCount hnn A 1
  have hsB : IsRealStableOrZero (genPoly wB) := isRealStableOrZero_projectCount hsA hrA hnA B 1
  have hrB : FixedRankWeight (r - 1 - 1) wB := fixedRankWeight_projectCount hrA B 1
  have hnB : WeightNonneg wB := weightNonneg_projectCount hnA B 1
  have hA : ∀ b t : ℝ, 0 < b → 0 < t →
      Real.exp (-1) * (L * b * t ^ k) ≤ MvPolynomial.eval
        (blockScale B (blockScale C (fun _ => 1) t) b) (genPoly wA) := by
    intro b t hb ht
    apply projectCount_eval_lower_bound hst hr hnn A
      (blockScale B (blockScale C (fun _ => 1) t) b)
      (fun i _ => blockScale_pos B (blockScale_pos C (fun _ => one_pos) ht) hb i)
    intro a ha
    convert hcap a b t ha hb ht using 1
    ring
  have hB : ∀ t : ℝ, 0 < t →
      Real.exp (-1) * (Real.exp (-1) * L * t ^ k) ≤
        MvPolynomial.eval (blockScale C (fun _ => 1) t) (genPoly wB) := by
    intro t ht
    apply projectCount_eval_lower_bound hsA hrA hnA B
      (blockScale C (fun _ => 1) t)
      (fun i _ => blockScale_pos C (fun _ => one_pos) ht i)
    intro b hb
    convert hA b t hb ht using 1
    ring
  have hfinal : Real.exp (-1) * (Real.exp (-1) * (Real.exp (-1) * L)) ≤
      MvPolynomial.eval (fun _ => 1) (genPoly (projectCount wB C k)) := by
    rcases hk with rfl | rfl
    · apply projectCount_eval_lower_bound hsB hrB hnB C (fun _ => 1) (fun _ _ => one_pos)
      intro t ht
      convert hB t ht using 1
      ring
    · have hbA := projectCount_preserves_lower_count (k := 1) hAC hbase
      have hbB := projectCount_preserves_lower_count (k := 1) hBC hbA
      apply projectCount_eval_lower_bound_two hsB hrB hnB C (fun _ => 1)
        (fun _ _ => one_pos) hbB
      intro t ht
      convert hB t ht using 1
      ring
  have hexp : Real.exp (-1) * (Real.exp (-1) * (Real.exp (-1) * L)) =
      Real.exp (-3) * L := by
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [hexp, eval_one_genPoly] at hfinal
  change Real.exp (-3) * L ≤ totalMass (projectCount (projectCount (projectCount w A 1) B 1) C k)
    at hfinal
  rwa [totalMass_projectCount_three w A B C hAB hAC hBC] at hfinal

/-- The unshifted all-ones specialization. -/
theorem three_counts_one_ge_of_capacity {w : Finset ι → ℝ} {r : ℕ} {L : ℝ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcap : ∀ a b t : ℝ, 0 < a → 0 < b → 0 < t →
      L * a * b * t ≤ MvPolynomial.eval
        (blockScale A (blockScale B (blockScale C (fun _ => 1) t) b) a) (genPoly w)) :
    Real.exp (-3) * L ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ C).card = 1) := by
  exact three_counts_ge_of_capacity hst hr hnn A B C hAB hAC hBC (Or.inl rfl)
    (fun _ _ => Nat.zero_le _) (by simpa using hcap)

/-- Lemma 5.21's baseline-one count requires only three, not four,
extraction factors. No representative of the sure block is chosen. -/
theorem three_counts_shifted_ge_of_capacity {w : Finset ι → ℝ} {r : ℕ} {L : ℝ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hb : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ C).card)
    (hcap : ∀ a b t : ℝ, 0 < a → 0 < b → 0 < t →
      L * a * b * t ^ 2 ≤ MvPolynomial.eval
        (blockScale A (blockScale B (blockScale C (fun _ => 1) t) b) a) (genPoly w)) :
    Real.exp (-3) * L ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ C).card = 2) :=
  three_counts_ge_of_capacity hst hr hnn A B C hAB hAC hBC (Or.inr rfl) hb hcap

end TSPGap

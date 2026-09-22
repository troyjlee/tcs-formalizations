/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RayleighCondition

/-!
# Feder–Mihail: the generic weight layer

The homogeneous specialization of Borcea–Brändén–Liggett Theorem 4.8 — closure
under conditioning, plus pairwise negative correlation and homogeneity, gives
conditional negative association.  Fixed-rank tree distributions need none of the
nonhomogeneous homogenization machinery.

Everything here is stated for **generic weights**, not for `TreeDist`: the
`IsMaxEntropyLimit` statements will be corollaries at the very end, never the
induction carrier.

## The active set

Conditioning does not shrink the ambient type — `contractWeight w k` still lives
on `Finset ι` — so neither `Fintype.card ι` nor the events' dependency witnesses
can carry the induction.  (The latter is not merely inconvenient but unsound: the
positive-influence coordinate that homogeneity supplies may lie outside both
witnesses.)  Instead the weight carries an explicit **active set**
`WeightSupportedOn w K`, starting at `K = univ`; conditioning on `k` sends it to
`K.erase k`, so `K.card` descends while event dependence stays a separate matter.

## Scale invariance

Masses are unnormalized and every correlation statement is cross-multiplied:

`NegCorrelated w A B : W(A ∩ B) · M ≤ W(A) · W(B)`,

homogeneous of degree two in `w`, so it is insensitive to the normalization that
conditioning destroys.  ⚠️ For a **nonnegative** weight a zero-mass conditioning
event is harmless — every sub-mass vanishes with it, so both sides are `0`; for a
general signed weight the statement stays meaningful but that degeneracy claim
does not hold.

## The homogeneity input

`sum_influence_eq_zero`: for a rank-`r` weight supported on `K`,

`∑_{e ∈ K} (M · W(A ∩ e) − W(A) · W(e)) = 0`.

Both halves are the same double count — every set in the support meets `K` in
exactly `r` elements — so the influences of the active coordinates on any event
sum to zero.  This is the only place homogeneity is used, and it is what forces
a coordinate of nonnegative influence to exist.

## The coordinate–event theorem

`coordinate_event_negCorrelation`: a coordinate is negatively correlated with any
increasing event that ignores it.  Strong induction on the active set, with the
auxiliary coordinate selected *inside the measure already conditioned on `e`* and
required to co-occur with it.
-/

namespace TSPGap

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Weight predicates -/

/-- Nonnegativity, with no normalization. -/
def WeightNonneg (w : Finset ι → ℝ) : Prop := ∀ S, 0 ≤ w S

/-- Homogeneity: the weight vanishes off the sets of size `r`. -/
def FixedRankWeight (r : ℕ) (w : Finset ι → ℝ) : Prop := ∀ S, w S ≠ 0 → S.card = r

/-- The **active set**: every set carrying weight lies inside `K`.  This is what
the induction descends on. -/
def WeightSupportedOn (w : Finset ι → ℝ) (K : Finset ι) : Prop := ∀ S, w S ≠ 0 → S ⊆ K

/-! ### Masses -/

section Masses

omit [DecidableEq ι]

open Classical in
/-- The mass of an event, indicator-style: no filter, hence no decidability
bookkeeping, and manifestly linear in `w`. -/
noncomputable def weightMass (w : Finset ι → ℝ) (A : Finset ι → Prop) : ℝ :=
  ∑ S : Finset ι, if A S then w S else 0

noncomputable def totalMass (w : Finset ι → ℝ) : ℝ := ∑ S : Finset ι, w S

theorem weightMass_congr {w : Finset ι → ℝ} {A B : Finset ι → Prop} (h : ∀ S, A S ↔ B S) :
    weightMass w A = weightMass w B := by
  classical
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · rw [if_pos hA, if_pos ((h S).mp hA)]
  · rw [if_neg hA, if_neg (fun hB => hA ((h S).mpr hB))]

@[simp] theorem weightMass_true (w : Finset ι → ℝ) :
    weightMass w (fun _ => True) = totalMass w := by
  classical
  simp [weightMass, totalMass]

theorem weightMass_nonneg {w : Finset ι → ℝ} (hw : WeightNonneg w) (A : Finset ι → Prop) :
    0 ≤ weightMass w A := by
  classical
  refine Finset.sum_nonneg fun S _ => ?_
  by_cases hA : A S
  · rw [if_pos hA]; exact hw S
  · rw [if_neg hA]

theorem totalMass_nonneg {w : Finset ι → ℝ} (hw : WeightNonneg w) : 0 ≤ totalMass w := by
  simpa using weightMass_nonneg hw (fun _ => True)

/-- A single set is a lower bound for the mass of any event it satisfies. -/
theorem le_weightMass {w : Finset ι → ℝ} (hnn : WeightNonneg w) {A : Finset ι → Prop}
    {S : Finset ι} (hS : A S) : w S ≤ weightMass w A := by
  classical
  refine le_trans (le_of_eq (if_pos hS).symm) (Finset.single_le_sum (f := fun T =>
    if A T then w T else 0) (fun T _ => ?_) (Finset.mem_univ S))
  by_cases hT : A T
  · rw [if_pos hT]; exact hnn T
  · rw [if_neg hT]

/-- A sub-event has no more mass. -/
theorem weightMass_mono {w : Finset ι → ℝ} (hw : WeightNonneg w) {A B : Finset ι → Prop}
    (h : ∀ S, A S → B S) : weightMass w A ≤ weightMass w B := by
  classical
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases hA : A S
  · rw [if_pos hA, if_pos (h S hA)]
  · rw [if_neg hA]
    by_cases hB : B S
    · rw [if_pos hB]; exact hw S
    · rw [if_neg hB]

theorem weightMass_le_totalMass {w : Finset ι → ℝ} (hw : WeightNonneg w)
    (A : Finset ι → Prop) : weightMass w A ≤ totalMass w := by
  simpa using weightMass_mono hw (B := fun _ => True) fun _ _ => trivial

/-! ### Scale-invariant correlation -/

/-- `W(A ∩ B) · M ≤ W(A) · W(B)`: cross-multiplied, hence unnormalized and
homogeneous of degree two in `w`. -/
def NegCorrelated (w : Finset ι → ℝ) (A B : Finset ι → Prop) : Prop :=
  weightMass w (fun S => A S ∧ B S) * totalMass w ≤ weightMass w A * weightMass w B

/-- The reverse inequality. -/
def PosCorrelated (w : Finset ι → ℝ) (A B : Finset ι → Prop) : Prop :=
  weightMass w A * weightMass w B ≤ weightMass w (fun S => A S ∧ B S) * totalMass w

theorem NegCorrelated.symm {w : Finset ι → ℝ} {A B : Finset ι → Prop}
    (h : NegCorrelated w A B) : NegCorrelated w B A := by
  rw [NegCorrelated, weightMass_congr (fun S => and_comm), mul_comm (weightMass w B)]
  exact h

/-- Scale invariance, made explicit. -/
theorem NegCorrelated.smul {w : Finset ι → ℝ} {A B : Finset ι → Prop}
    (h : NegCorrelated w A B) {c : ℝ} (hc : 0 ≤ c) :
    NegCorrelated (fun S => c * w S) A B := by
  classical
  have hm : ∀ P : Finset ι → Prop, weightMass (fun S => c * w S) P = c * weightMass w P := by
    intro P
    rw [weightMass, weightMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hP : P S <;> simp [hP]
  have ht : totalMass (fun S => c * w S) = c * totalMass w := by
    rw [totalMass, totalMass, Finset.mul_sum]
  rw [NegCorrelated, hm, hm, hm, ht]
  calc (c * weightMass w (fun S => A S ∧ B S)) * (c * totalMass w)
      = (c * c) * (weightMass w (fun S => A S ∧ B S) * totalMass w) := by ring
    _ ≤ (c * c) * (weightMass w A * weightMass w B) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hc hc)
    _ = (c * weightMass w A) * (c * weightMass w B) := by ring

end Masses

/-! ### Event dependence -/

section Events

omit [Fintype ι]

/-- `A` is determined by the coordinates in `K`. -/
def EventDependsOn (A : Finset ι → Prop) (K : Finset ι) : Prop :=
  ∀ S T : Finset ι, S ∩ K = T ∩ K → (A S ↔ A T)

theorem EventDependsOn.mono {A : Finset ι → Prop} {K L : Finset ι}
    (h : EventDependsOn A K) (hKL : K ⊆ L) : EventDependsOn A L := by
  intro S T hST
  refine h S T ?_
  ext a
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨haS, haK⟩
    have : a ∈ S ∩ L := Finset.mem_inter.mpr ⟨haS, hKL haK⟩
    rw [hST] at this
    exact ⟨(Finset.mem_inter.mp this).1, haK⟩
  · rintro ⟨haT, haK⟩
    have : a ∈ T ∩ L := Finset.mem_inter.mpr ⟨haT, hKL haK⟩
    rw [← hST] at this
    exact ⟨(Finset.mem_inter.mp this).1, haK⟩

/-! ### Coordinate-blind sections

`outSection A k` and `inSection A k` are the two conditionings of `A`, written so
that they are defined on *all* of `Finset ι` and blind to the coordinate `k`.
That keeps the ambient type fixed, which is what the active-set induction
needs. -/

/-- `A` after deleting `k`. -/
def outSection (A : Finset ι → Prop) (k : ι) : Finset ι → Prop := fun S => A (S.erase k)

/-- `A` after contracting `k`. -/
def inSection (A : Finset ι → Prop) (k : ι) : Finset ι → Prop := fun S => A (insert k S)

theorem outSection_of_notMem {A : Finset ι → Prop} {k : ι} {S : Finset ι} (h : k ∉ S) :
    outSection A k S ↔ A S := by rw [outSection, Finset.erase_eq_of_notMem h]

theorem inSection_insert {A : Finset ι → Prop} {k : ι} (S : Finset ι) :
    inSection A k S ↔ A (insert k S) := Iff.rfl

/-- Deleting `k` cuts `k` out of the dependency set. -/
theorem EventDependsOn.outSection {A : Finset ι → Prop} {K : Finset ι}
    (h : EventDependsOn A K) (k : ι) : EventDependsOn (TSPGap.outSection A k) (K.erase k) := by
  intro S T hST
  refine h _ _ ?_
  have key : ∀ U : Finset ι, (U.erase k) ∩ K = U ∩ (K.erase k) := by
    intro U
    ext a
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  rw [key, key, hST]

/-- Contracting `k` cuts `k` out of the dependency set. -/
theorem EventDependsOn.inSection {A : Finset ι → Prop} {K : Finset ι}
    (h : EventDependsOn A K) (k : ι) : EventDependsOn (TSPGap.inSection A k) (K.erase k) := by
  intro S T hST
  refine h _ _ ?_
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert]
  by_cases hak : a = k
  · subst hak
    simp
  · have := congrArg (fun U : Finset ι => a ∈ U) hST
    simp only [Finset.mem_inter, Finset.mem_erase, eq_iff_iff] at this
    constructor
    · rintro ⟨hS | hS, haK⟩
      · exact absurd hS hak
      · exact ⟨Or.inr (this.mp ⟨hS, hak, haK⟩).1, haK⟩
    · rintro ⟨hT | hT, haK⟩
      · exact absurd hT hak
      · exact ⟨Or.inr (this.mpr ⟨hT, hak, haK⟩).1, haK⟩

theorem Monotone.outSection {A : Finset ι → Prop} (h : Monotone A) (k : ι) :
    Monotone (TSPGap.outSection A k) :=
  fun _ _ hST => h (Finset.erase_subset_erase k hST)

theorem Monotone.inSection {A : Finset ι → Prop} (h : Monotone A) (k : ι) :
    Monotone (TSPGap.inSection A k) :=
  fun _ _ hST => h (Finset.insert_subset_insert k hST)

/-- **Monotonicity nests the two sections.**  This is the only place `Monotone`
enters the section calculus. -/
theorem outSection_le_inSection {A : Finset ι → Prop} (h : Monotone A) (k : ι) (S : Finset ι) :
    TSPGap.outSection A k S → TSPGap.inSection A k S :=
  fun hs => h (fun _ ha => Finset.mem_insert_of_mem (Finset.mem_of_mem_erase ha)) hs

end Events

/-! ### Conditioning preserves the predicates -/

section Preserve

omit [Fintype ι]

theorem WeightNonneg.delete {w : Finset ι → ℝ} (hw : WeightNonneg w) (k : ι) :
    WeightNonneg (deleteWeight w k) := by
  intro V
  by_cases h : k ∈ V
  · simp [deleteWeight, h]
  · simpa [deleteWeight, h] using hw V

theorem WeightNonneg.contract {w : Finset ι → ℝ} (hw : WeightNonneg w) (k : ι) :
    WeightNonneg (contractWeight w k) := by
  intro V
  by_cases h : k ∈ V
  · simp [contractWeight, h]
  · simpa [contractWeight, h] using hw (insert k V)

theorem FixedRankWeight.delete {r : ℕ} {w : Finset ι → ℝ} (hr : FixedRankWeight r w) (k : ι) :
    FixedRankWeight r (deleteWeight w k) := by
  intro V hV
  by_cases h : k ∈ V
  · rw [deleteWeight, if_pos h] at hV
    exact absurd rfl hV
  · rw [deleteWeight, if_neg h] at hV
    exact hr V hV

theorem FixedRankWeight.contract {r : ℕ} {w : Finset ι → ℝ} (hr : FixedRankWeight r w) (k : ι) :
    FixedRankWeight (r - 1) (contractWeight w k) := by
  intro V hV
  by_cases h : k ∈ V
  · rw [contractWeight, if_pos h] at hV
    exact absurd rfl hV
  · rw [contractWeight, if_neg h] at hV
    have := hr _ hV
    rw [Finset.card_insert_of_notMem h] at this
    omega

theorem WeightSupportedOn.delete {w : Finset ι → ℝ} {K : Finset ι}
    (hs : WeightSupportedOn w K) (k : ι) : WeightSupportedOn (deleteWeight w k) (K.erase k) := by
  intro V hV
  by_cases h : k ∈ V
  · rw [deleteWeight, if_pos h] at hV
    exact absurd rfl hV
  · rw [deleteWeight, if_neg h] at hV
    intro a ha
    exact Finset.mem_erase.mpr ⟨fun hak => h (hak ▸ ha), hs V hV ha⟩

theorem WeightSupportedOn.contract {w : Finset ι → ℝ} {K : Finset ι}
    (hs : WeightSupportedOn w K) (k : ι) :
    WeightSupportedOn (contractWeight w k) (K.erase k) := by
  intro V hV
  by_cases h : k ∈ V
  · rw [contractWeight, if_pos h] at hV
    exact absurd rfl hV
  · rw [contractWeight, if_neg h] at hV
    intro a ha
    exact Finset.mem_erase.mpr
      ⟨fun hak => h (hak ▸ ha), hs _ hV (Finset.mem_insert_of_mem ha)⟩

end Preserve

/-! ### Mass bridges -/

theorem weightMass_deleteWeight (w : Finset ι → ℝ) (k : ι) (A : Finset ι → Prop) :
    weightMass (deleteWeight w k) (TSPGap.outSection A k)
      = weightMass w (fun S => k ∉ S ∧ A S) := by
  classical
  refine Finset.sum_congr rfl fun V _ => ?_
  simp only [TSPGap.outSection, deleteWeight]
  by_cases h : k ∈ V
  · simp [h]
  · rw [Finset.erase_eq_of_notMem h]
    by_cases hA : A V <;> simp [h, hA]

theorem weightMass_contractWeight (w : Finset ι → ℝ) (k : ι) (A : Finset ι → Prop) :
    weightMass (contractWeight w k) (TSPGap.inSection A k)
      = weightMass w (fun S => k ∈ S ∧ A S) := by
  classical
  have hL : weightMass (contractWeight w k) (TSPGap.inSection A k)
      = ∑ V ∈ Finset.univ.filter (fun V : Finset ι => k ∉ V ∧ A (insert k V)),
          w (insert k V) := by
    rw [weightMass, Finset.sum_filter]
    refine Finset.sum_congr rfl fun V _ => ?_
    simp only [TSPGap.inSection, contractWeight]
    by_cases h : k ∈ V
    · simp [h]
    · by_cases hA : A (insert k V) <;> simp [h, hA]
  have hR : weightMass w (fun S => k ∈ S ∧ A S)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => k ∈ S ∧ A S), w S := by
    rw [Finset.sum_filter, weightMass]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases h : k ∈ S ∧ A S
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun V => insert k V) (fun S => S.erase k) ?_ ?_ ?_ ?_ ?_
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV ⊢
    exact ⟨Finset.mem_insert_self k V, hV.2⟩
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact ⟨Finset.notMem_erase k S, by rw [Finset.insert_erase hS.1]; exact hS.2⟩
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
    exact Finset.erase_insert hV.1
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.insert_erase hS.1
  · intro V _
    rfl

theorem totalMass_deleteWeight (w : Finset ι → ℝ) (k : ι) :
    totalMass (deleteWeight w k) = weightMass w (fun S => k ∉ S) := by
  have h := weightMass_deleteWeight w k (fun _ => True)
  rw [weightMass_congr (A := TSPGap.outSection (fun _ => True) k) (B := fun _ => True)
    (fun _ => Iff.rfl), weightMass_true] at h
  rw [h]
  exact weightMass_congr fun S => by simp

theorem totalMass_contractWeight (w : Finset ι → ℝ) (k : ι) :
    totalMass (contractWeight w k) = weightMass w (fun S => k ∈ S) := by
  have h := weightMass_contractWeight w k (fun _ => True)
  rw [weightMass_congr (A := TSPGap.inSection (fun _ => True) k) (B := fun _ => True)
    (fun _ => Iff.rfl), weightMass_true] at h
  rw [h]
  exact weightMass_congr fun S => by simp

/-! ### The homogeneity identity -/

/-- Double counting: every set carrying weight meets the active set in exactly
`r` coordinates. -/
theorem sum_mem_weightMass {w : Finset ι → ℝ} {r : ℕ} {K : Finset ι}
    (hr : FixedRankWeight r w) (hsup : WeightSupportedOn w K) (A : Finset ι → Prop) :
    ∑ e ∈ K, weightMass w (fun S => A S ∧ e ∈ S) = (r : ℝ) * weightMass w A := by
  classical
  have key : ∀ S : Finset ι, ∑ e ∈ K, (if A S ∧ e ∈ S then w S else 0)
      = (r : ℝ) * (if A S then w S else 0) := by
    intro S
    by_cases hw : w S = 0
    · simp [hw]
    · by_cases hA : A S
      · have hSK : S ⊆ K := hsup S hw
        have hcard : S.card = r := hr S hw
        have hterm : ∀ e ∈ K, (if A S ∧ e ∈ S then w S else 0) = if e ∈ S then w S else 0 := by
          intro e _
          by_cases he : e ∈ S <;> simp [hA, he]
        rw [if_pos hA, Finset.sum_congr rfl hterm, Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr hSK, Finset.sum_const, hcard, nsmul_eq_mul]
      · simp [hA]
  calc ∑ e ∈ K, weightMass w (fun S => A S ∧ e ∈ S)
      = ∑ e ∈ K, ∑ S : Finset ι, (if A S ∧ e ∈ S then w S else 0) :=
        Finset.sum_congr rfl fun e _ => by
          rw [weightMass]
          refine Finset.sum_congr rfl fun S _ => ?_
          by_cases h : A S ∧ e ∈ S
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h]
    _ = ∑ S : Finset ι, ∑ e ∈ K, (if A S ∧ e ∈ S then w S else 0) := Finset.sum_comm
    _ = ∑ S : Finset ι, (r : ℝ) * (if A S then w S else 0) :=
        Finset.sum_congr rfl fun S _ => key S
    _ = (r : ℝ) * weightMass w A := by rw [weightMass, Finset.mul_sum]

/-- **The influences of the active coordinates on any event sum to zero.**

This is the whole of the homogeneity input, and it is what forces a coordinate of
nonnegative influence to exist. -/
theorem sum_influence_eq_zero {w : Finset ι → ℝ} {r : ℕ} {K : Finset ι}
    (hr : FixedRankWeight r w) (hsup : WeightSupportedOn w K) (A : Finset ι → Prop) :
    ∑ e ∈ K, (totalMass w * weightMass w (fun S => A S ∧ e ∈ S)
      - weightMass w A * weightMass w (fun S => e ∈ S)) = 0 := by
  classical
  have h2 : ∀ e : ι, weightMass w (fun S => e ∈ S)
      = weightMass w (fun S => (fun _ => True) S ∧ e ∈ S) :=
    fun e => weightMass_congr fun S => by simp
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_mem_weightMass hr hsup A,
    Finset.sum_congr rfl (fun e _ => h2 e), sum_mem_weightMass hr hsup (fun _ => True),
    weightMass_true]
  ring

/-! ### The algebraic core of the conditioning step

Conditioning on an auxiliary coordinate `f` splits every mass into an `in` and an
`out` part.  Feeding the two branch inequalities — which the induction hypothesis
supplies — through the split leaves exactly a product of two influences.  This
lemma is that computation, in bare real arithmetic and division-free. -/

/-- With `Min ain ≤ bin cin` and `Mout aout ≤ bout cout` in the two branches, the
unsplit influence is controlled by the product of the influence of `f` on the
coordinate and the influence of `f` on the event:

`Δ · Min · Mout ≤ Cov(f, e) · Cov(f, A)`.

Since pairwise negative correlation makes the first factor `≤ 0`, it suffices to
find an auxiliary coordinate whose influence on the event is `≥ 0`. -/
theorem influence_cross_bound {Min Mout ain aout bin bout cin cout : ℝ}
    (hMin : 0 ≤ Min) (hMout : 0 ≤ Mout)
    (hin : Min * ain ≤ bin * cin) (hout : Mout * aout ≤ bout * cout) :
    ((Min + Mout) * (ain + aout) - (bin + bout) * (cin + cout)) * (Min * Mout)
      ≤ (Mout * bin - Min * bout) * (Mout * cin - Min * cout) := by
  have h1 : Min * Mout * (Min * ain) ≤ Min * Mout * (bin * cin) :=
    mul_le_mul_of_nonneg_left hin (mul_nonneg hMin hMout)
  have h2 : Min * Mout * (Mout * aout) ≤ Min * Mout * (bout * cout) :=
    mul_le_mul_of_nonneg_left hout (mul_nonneg hMin hMout)
  have h3 : Mout ^ 2 * (Min * ain) ≤ Mout ^ 2 * (bin * cin) :=
    mul_le_mul_of_nonneg_left hin (sq_nonneg Mout)
  have h4 : Min ^ 2 * (Mout * aout) ≤ Min ^ 2 * (bout * cout) :=
    mul_le_mul_of_nonneg_left hout (sq_nonneg Min)
  nlinarith [h1, h2, h3, h4]

/-! ### The four-cell inequality

Conditioning on `e` and an auxiliary `f` splits the mass into four cells

`u = W(e f)`, `v = W(e f̄)`, `s = W(ē f)`, `t = W(ē f̄)`

with `A`-submasses `a, b, c, d`.  The four hypotheses are, in order: pairwise
negative correlation of `e` and `f`; nonnegative influence of `f` on `A` **in the
measure already conditioned on `e`**; and the two recursive branches, `f`
contracted and `f` deleted.  Together they give the coordinate–event
inequality. -/

/-- **The four-cell inequality**, division-free.

⚠️ `0 < u` is not a convenience: with `u = 0` the implication is false, and
`u = 0, v = s = t = 1, a = c = 0, b = d = 1` satisfies all four hypotheses while
violating the conclusion.  `u = W(e ∧ f)` is exactly co-occurrence of `e` and
`f`, which is why the auxiliary coordinate must be chosen among those that
genuinely co-occur with `e`. -/
theorem fourCell_negCorrelated {u v s t a b c d : ℝ}
    (hu : 0 < u) (hv : 0 ≤ v) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : 0 ≤ d) (hdt : d ≤ t)
    (H1 : u * t ≤ v * s) (H2 : b * u ≤ a * v)
    (H3 : a * s ≤ u * c) (H4 : b * t ≤ v * d) :
    (a + b) * (s + t) ≤ (u + v) * (c + d) := by
  -- `f` and `A` are positively correlated given `e`, in unnormalized form
  have step1 : 0 ≤ v * c - b * s := by
    have key : u * (v * c - b * s) = v * (u * c - a * s) + s * (a * v - b * u) := by ring
    nlinarith [mul_nonneg hv (sub_nonneg.mpr H3), mul_nonneg hs (sub_nonneg.mpr H2)]
  have step2 : 0 ≤ (u * d - a * t) + (v * c - b * s) := by
    rcases le_or_gt (a * t) (u * d) with h | h
    · linarith
    · rcases eq_or_lt_of_le ht with ht0 | ht0
      · -- the deleted-`f`, absent-`e` cell is empty, so its `A`-submass is too
        have hd0 : d = 0 := le_antisymm (ht0 ▸ hdt) hd
        have hat : a * t = 0 := by rw [← ht0, mul_zero]
        have hud : u * d = 0 := by rw [hd0, mul_zero]
        rw [hat, hud]
        linarith
      · have key : (u * t) * ((u * d - a * t) + (v * c - b * s))
            = (v * s - u * t) * (a * t - u * d) + (t * v) * (u * c - a * s)
              + (u * s) * (v * d - b * t) := by ring
        have hpos : 0 < u * t := mul_pos hu ht0
        nlinarith [mul_nonneg (sub_nonneg.mpr H1) (le_of_lt (sub_pos.mpr h)),
          mul_nonneg (mul_nonneg ht hv) (sub_nonneg.mpr H3),
          mul_nonneg (mul_nonneg (le_of_lt hu) hs) (sub_nonneg.mpr H4)]
  have hid : (u + v) * (c + d) - (a + b) * (s + t)
      = (u * c - a * s) + (v * d - b * t) + ((u * d - a * t) + (v * c - b * s)) := by ring
  linarith [step2, sub_nonneg.mpr H3, sub_nonneg.mpr H4]

/-! ### Conditional selection

The auxiliary coordinate must be chosen **in the measure already conditioned on
`e`**, not in the original one.  Selecting in the original measure is what fails:
once `Cov(e, A) > 0`, the influence identity gives no *second* coordinate of
nonnegative influence. -/

/-- From `sum_influence_eq_zero`, some active coordinate has nonnegative
influence on the event. -/
theorem exists_nonneg_influence {w : Finset ι → ℝ} {r : ℕ} {K : Finset ι}
    (hr : FixedRankWeight r w) (hsup : WeightSupportedOn w K) (A : Finset ι → Prop)
    (hK : K.Nonempty) :
    ∃ f ∈ K, 0 ≤ totalMass w * weightMass w (fun S => A S ∧ f ∈ S)
      - weightMass w A * weightMass w (fun S => f ∈ S) := by
  by_contra hcon
  push Not at hcon
  have h := sum_influence_eq_zero hr hsup A
  have hneg : ∑ e ∈ K, (totalMass w * weightMass w (fun S => A S ∧ e ∈ S)
      - weightMass w A * weightMass w (fun S => e ∈ S)) < ∑ _e ∈ K, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hK fun e he => hcon e he
  rw [Finset.sum_const, smul_zero] at hneg
  linarith

/-- **The selection used by the induction**: apply the influence identity to the
measure conditioned on `e`, and to `A`'s section there.  The coordinate it
returns has nonnegative influence on `A` *given `e`*, which is hypothesis `H2` of
`fourCell_negCorrelated`. -/
theorem exists_nonneg_influence_contract {w : Finset ι → ℝ} {r : ℕ} {K : Finset ι} (e : ι)
    (hr : FixedRankWeight r w) (hsup : WeightSupportedOn w K) (A : Finset ι → Prop)
    (hK : (K.erase e).Nonempty) :
    ∃ f ∈ K.erase e,
      0 ≤ totalMass (contractWeight w e)
            * weightMass (contractWeight w e)
                (fun S => TSPGap.inSection A e S ∧ f ∈ S)
        - weightMass (contractWeight w e) (TSPGap.inSection A e)
            * weightMass (contractWeight w e) (fun S => f ∈ S) :=
  exists_nonneg_influence (hr.contract e) (hsup.contract e) (TSPGap.inSection A e) hK

omit [DecidableEq ι] in
/-- A coordinate of zero marginal has zero joint mass with every event, hence
zero influence. -/
theorem weightMass_eq_zero_of_marginal {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {f : ι} (hf : weightMass w (fun S => f ∈ S) = 0) (A : Finset ι → Prop) :
    weightMass w (fun S => A S ∧ f ∈ S) = 0 :=
  le_antisymm (hf ▸ weightMass_mono hnn fun _ hS => hS.2) (weightMass_nonneg hnn _)

/-- **The selection the induction actually needs.**

⚠️ `exists_nonneg_influence` can return an unused coordinate — zero marginal, and
hence zero influence, which satisfies the conclusion vacuously while failing the
`0 < u` hypothesis of `fourCell_negCorrelated`.  Restricting the influence sum to
the positive-marginal coordinates fixes this: the discarded terms are *exactly*
zero, by nonnegativity, so the restricted sum still vanishes. -/
theorem exists_posMarginal_nonneg_influence {w : Finset ι → ℝ} {r : ℕ} {K : Finset ι}
    (hnn : WeightNonneg w) (hr : FixedRankWeight r w) (hsup : WeightSupportedOn w K)
    (A : Finset ι → Prop) (hK : ∃ f ∈ K, 0 < weightMass w (fun S => f ∈ S)) :
    ∃ f ∈ K, 0 < weightMass w (fun S => f ∈ S) ∧
      0 ≤ totalMass w * weightMass w (fun S => A S ∧ f ∈ S)
        - weightMass w A * weightMass w (fun S => f ∈ S) := by
  classical
  set inf : ι → ℝ := fun f => totalMass w * weightMass w (fun S => A S ∧ f ∈ S)
    - weightMass w A * weightMass w (fun S => f ∈ S) with hinfdef
  have hzero : ∀ f ∈ K.filter (fun f => ¬ (0 < weightMass w (fun S => f ∈ S))), inf f = 0 := by
    intro f hf
    simp only [Finset.mem_filter, not_lt] at hf
    have h0 : weightMass w (fun S => f ∈ S) = 0 :=
      le_antisymm hf.2 (weightMass_nonneg hnn _)
    rw [hinfdef]
    simp only [weightMass_eq_zero_of_marginal hnn h0 A, h0, mul_zero, sub_zero]
  have hsum : ∑ f ∈ K.filter (fun f => 0 < weightMass w (fun S => f ∈ S)), inf f = 0 := by
    have h := sum_influence_eq_zero hr hsup A
    rw [← Finset.sum_filter_add_sum_filter_not K
      (fun f => 0 < weightMass w (fun S => f ∈ S)), Finset.sum_eq_zero hzero, add_zero] at h
    exact h
  obtain ⟨f₀, hf₀K, hf₀pos⟩ := hK
  have hPne : (K.filter (fun f => 0 < weightMass w (fun S => f ∈ S))).Nonempty :=
    ⟨f₀, Finset.mem_filter.mpr ⟨hf₀K, hf₀pos⟩⟩
  by_contra hcon
  push Not at hcon
  have hneg : ∑ f ∈ K.filter (fun f => 0 < weightMass w (fun S => f ∈ S)), inf f
      < ∑ _f ∈ K.filter (fun f => 0 < weightMass w (fun S => f ∈ S)), (0 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hPne fun f hf => ?_
    simp only [Finset.mem_filter] at hf
    exact hcon f hf.1 hf.2
  rw [Finset.sum_const, smul_zero] at hneg
  linarith

/-- The form the induction uses: select inside the measure conditioned on `e`,
among the coordinates that genuinely co-occur with `e`. -/
theorem exists_posMarginal_nonneg_influence_contract {w : Finset ι → ℝ} {r : ℕ}
    {K : Finset ι} (e : ι) (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (A : Finset ι → Prop)
    (hK : ∃ f ∈ K.erase e, 0 < weightMass (contractWeight w e) (fun S => f ∈ S)) :
    ∃ f ∈ K.erase e, 0 < weightMass (contractWeight w e) (fun S => f ∈ S) ∧
      0 ≤ totalMass (contractWeight w e)
            * weightMass (contractWeight w e)
                (fun S => TSPGap.inSection A e S ∧ f ∈ S)
        - weightMass (contractWeight w e) (TSPGap.inSection A e)
            * weightMass (contractWeight w e) (fun S => f ∈ S) :=
  exists_posMarginal_nonneg_influence (hnn.contract e) (hr.contract e) (hsup.contract e)
    (TSPGap.inSection A e) hK

/-- Splitting an event's mass at a coordinate. -/
theorem weightMass_split_mem (w : Finset ι → ℝ) (A : Finset ι → Prop) (k : ι) :
    weightMass w A = weightMass w (fun S => A S ∧ k ∈ S)
      + weightMass w (fun S => A S ∧ k ∉ S) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · by_cases hk : k ∈ S <;> simp [hA, hk]
  · simp [hA]

/-! ### The degenerate branch -/

/-- **No co-occurring coordinate makes the inequality immediate.**

If no active coordinate has positive marginal under the measure conditioned on
`e`, then every positive-weight set containing `e` is `{e}`.  Since `A` ignores
`e`, monotonicity then decides `A` on all of them at once — and this subsumes the
total-mass-zero case. -/
theorem negCorrelated_of_no_coOccurrence {w : Finset ι → ℝ} {K : Finset ι} {e : ι}
    (hnn : WeightNonneg w) (hsup : WeightSupportedOn w K) {A : Finset ι → Prop}
    (hmono : Monotone A) (hdep : EventDependsOn A (K.erase e))
    (hno : ∀ f ∈ K.erase e, weightMass (contractWeight w e) (fun S => f ∈ S) = 0) :
    NegCorrelated w (fun S => e ∈ S) A := by
  classical
  -- the conditioned measure is carried by the empty set alone
  have hsupp0 : ∀ V : Finset ι, contractWeight w e V ≠ 0 → V = ∅ := by
    intro V hV
    by_contra hne
    obtain ⟨f, hf⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hfK : f ∈ K.erase e := (hsup.contract e) V hV hf
    have hle : contractWeight w e V ≤ weightMass (contractWeight w e) (fun S => f ∈ S) :=
      le_weightMass (hnn.contract e) hf
    rw [hno f hfK] at hle
    exact hV (le_antisymm hle ((hnn.contract e) V))
  have hmass : ∀ A' : Finset ι → Prop, weightMass (contractWeight w e) A'
      = if A' ∅ then contractWeight w e ∅ else 0 := by
    intro A'
    refine Finset.sum_eq_single (∅ : Finset ι) (fun V _ hV => ?_) (fun h => absurd
      (Finset.mem_univ (∅ : Finset ι)) h)
    by_cases hA : A' V
    · rw [if_pos hA]
      by_contra hc
      exact hV (hsupp0 V hc)
    · rw [if_neg hA]
  -- the two masses involving `e`
  have hE : weightMass w (fun S => e ∈ S) = contractWeight w e ∅ := by
    rw [← totalMass_contractWeight, ← weightMass_true, hmass]
    simp
  have hAE : weightMass w (fun S => e ∈ S ∧ A S)
      = if A {e} then contractWeight w e ∅ else 0 := by
    rw [← weightMass_contractWeight w e A, hmass]
    rfl
  by_cases hAe : A {e}
  · -- `A` ignores `e`, so `A ∅` holds, and monotonicity spreads it everywhere
    have hA0 : A ∅ := by
      have hint : ({e} : Finset ι) ∩ (K.erase e) = ∅ ∩ (K.erase e) := by
        rw [Finset.empty_inter]
        ext a
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_erase,
          Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        simp
      exact (hdep {e} ∅ hint).mp hAe
    have hall : ∀ S : Finset ι, A S := fun S => hmono (Finset.empty_subset S) hA0
    have hAfull : weightMass w A = totalMass w := by
      rw [weightMass_congr (B := fun _ => True) fun S => iff_of_true (hall S) trivial,
        weightMass_true]
    have hboth : weightMass w (fun S => e ∈ S ∧ A S) = weightMass w (fun S => e ∈ S) :=
      weightMass_congr fun S => ⟨fun h => h.1, fun h => ⟨h, hall S⟩⟩
    rw [NegCorrelated, hboth, hAfull]
  · rw [NegCorrelated, hAE, if_neg hAe, zero_mul]
    exact mul_nonneg (weightMass_nonneg hnn _) (weightMass_nonneg hnn _)

/-! ### Cell decompositions -/

section Cells

variable (w : Finset ι → ℝ) (A : Finset ι → Prop) (e f : ι)

theorem totalMass_split_four :
    totalMass w = weightMass w (fun S => e ∈ S ∧ f ∈ S) + weightMass w (fun S => e ∈ S ∧ f ∉ S)
      + weightMass w (fun S => e ∉ S ∧ f ∈ S) + weightMass w (fun S => e ∉ S ∧ f ∉ S) := by
  classical
  rw [totalMass, weightMass, weightMass, weightMass, weightMass,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [he, hf]

theorem weightMass_split_four :
    weightMass w A = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
      + weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S))
      + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∈ S))
      + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∉ S)) := by
  classical
  rw [weightMass, weightMass, weightMass, weightMass, weightMass,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [hA, he, hf]
  · simp [hA]

theorem weightMass_mem_split_left :
    weightMass w (fun S => e ∈ S) = weightMass w (fun S => e ∈ S ∧ f ∈ S)
      + weightMass w (fun S => e ∈ S ∧ f ∉ S) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [he, hf]

theorem weightMass_mem_split_right :
    weightMass w (fun S => f ∈ S) = weightMass w (fun S => e ∈ S ∧ f ∈ S)
      + weightMass w (fun S => e ∉ S ∧ f ∈ S) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [he, hf]

theorem weightMass_notMem_split :
    weightMass w (fun S => f ∉ S) = weightMass w (fun S => e ∈ S ∧ f ∉ S)
      + weightMass w (fun S => e ∉ S ∧ f ∉ S) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [he, hf]

theorem weightMass_memAnd_split :
    weightMass w (fun S => e ∈ S ∧ A S) = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
      + weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S)) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [hA, he, hf]
  · simp [hA]

theorem weightMass_memAnd_split_right :
    weightMass w (fun S => f ∈ S ∧ A S) = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
      + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∈ S)) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [hA, he, hf]
  · simp [hA]

theorem weightMass_notMemAnd_split :
    weightMass w (fun S => f ∉ S ∧ A S) = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S))
      + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∉ S)) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · by_cases he : e ∈ S <;> by_cases hf : f ∈ S <;> simp [hA, he, hf]
  · simp [hA]

end Cells

/-! ### The Rayleigh bridge and the conditioned-mass bridges -/

omit [DecidableEq ι] in
theorem weightMass_eq_filter_sum (w : Finset ι → ℝ) (P : Finset ι → Prop) [DecidablePred P] :
    weightMass w P = ∑ S ∈ Finset.univ.filter P, w S := by
  rw [Finset.sum_filter, weightMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : P S
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- Pairwise negative correlation of two coordinates, in the generic predicate
form this file uses. -/
theorem rayleighNegCorrelated_mem {w : Finset ι → ℝ} (hR : RayleighNonneg (genPoly w))
    {e f : ι} (hef : e ≠ f) : NegCorrelated w (fun S => e ∈ S) (fun S => f ∈ S) := by
  classical
  have h := negCorrelation_of_rayleighNonneg hR hef
  rw [NegCorrelated, weightMass_eq_filter_sum, weightMass_eq_filter_sum,
    weightMass_eq_filter_sum, totalMass, mul_comm]
  exact h

/-- A conditioned mass, when the event cannot see the conditioned coordinate. -/
theorem weightMass_contract_blind {w : Finset ι → ℝ} {f : ι} (B : Finset ι → Prop)
    (hB : ∀ S : Finset ι, B (insert f S) ↔ B S) :
    weightMass (contractWeight w f) B = weightMass w (fun S => f ∈ S ∧ B S) := by
  rw [weightMass_congr (B := TSPGap.inSection B f) fun S => (hB S).symm]
  exact weightMass_contractWeight w f B

theorem weightMass_delete_blind {w : Finset ι → ℝ} {f : ι} (B : Finset ι → Prop)
    (hB : ∀ S : Finset ι, B (S.erase f) ↔ B S) :
    weightMass (deleteWeight w f) B = weightMass w (fun S => f ∉ S ∧ B S) := by
  rw [weightMass_congr (B := TSPGap.outSection B f) fun S => (hB S).symm]
  exact weightMass_deleteWeight w f B

omit [Fintype ι] in
theorem inSection_of_mem {A : Finset ι → Prop} {f : ι} {S : Finset ι} (h : f ∈ S) :
    TSPGap.inSection A f S ↔ A S := by
  rw [TSPGap.inSection, Finset.insert_eq_self.mpr h]

/-! ### The glue -/

/-- The target, expressed in the four cells. -/
theorem negCorrelated_mem_of_cells {w : Finset ι → ℝ} {e f : ι} {A : Finset ι → Prop}
    (h : (weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
          + weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S)))
        * (weightMass w (fun S => e ∉ S ∧ f ∈ S) + weightMass w (fun S => e ∉ S ∧ f ∉ S))
      ≤ (weightMass w (fun S => e ∈ S ∧ f ∈ S) + weightMass w (fun S => e ∈ S ∧ f ∉ S))
        * (weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∈ S))
          + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∉ S)))) :
    NegCorrelated w (fun S => e ∈ S) A := by
  rw [NegCorrelated, weightMass_memAnd_split w A e f, totalMass_split_four w e f,
    weightMass_mem_split_left w e f, weightMass_split_four w A e f]
  nlinarith [h]

/-! ### The coordinate–event theorem -/

/-- **Feder–Mihail's coordinate–event inequality.**

A coordinate is negatively correlated with any increasing event that ignores it.
Strong induction on the active set: either no coordinate co-occurs with `e`, and
the degenerate branch applies, or the conditional selector supplies an auxiliary
`f` with positive marginal and nonnegative influence, and the four-cell
inequality combines the two recursive branches with pairwise negative
correlation.

The dependency invariant survives because `(K \ {e}) \ {f} = (K \ {f}) \ {e}`. -/
theorem coordinate_event_negCorrelation :
    ∀ (K : Finset ι) (w : Finset ι → ℝ) (r : ℕ) (e : ι) (A : Finset ι → Prop),
      WeightNonneg w → FixedRankWeight r w → WeightSupportedOn w K →
      RayleighNonneg (genPoly w) → e ∈ K → Monotone A → EventDependsOn A (K.erase e) →
      NegCorrelated w (fun S => e ∈ S) A := by
  intro K
  induction K using Finset.strongInductionOn with
  | _ K ih =>
  intro w r e A hnn hr hsup hR he hmono hdep
  classical
  have hcomm : ∀ (t : Finset ι) (x y : ι), (t.erase x).erase y = (t.erase y).erase x := by
    intro t x y
    ext z
    simp only [Finset.mem_erase]
    tauto
  by_cases hex : ∃ f ∈ K.erase e, 0 < weightMass (contractWeight w e) (fun S => f ∈ S)
  · obtain ⟨f, hfKe, hfpos, hinf⟩ :=
      exists_posMarginal_nonneg_influence_contract e hnn hr hsup A hex
    have hfe : f ≠ e := (Finset.mem_erase.mp hfKe).1
    have hfK : f ∈ K := (Finset.mem_erase.mp hfKe).2
    have hef : e ≠ f := Ne.symm hfe
    have hlt : K.erase f ⊂ K := Finset.erase_ssubset hfK
    have heKf : e ∈ K.erase f := Finset.mem_erase.mpr ⟨hef, he⟩
    have hIn := ih (K.erase f) hlt (contractWeight w f) (r - 1) e (TSPGap.inSection A f)
      (hnn.contract f) (hr.contract f) (hsup.contract f)
      (rayleighNonneg_contractWeight hR f) heKf (TSPGap.Monotone.inSection hmono f)
      (by rw [hcomm]; exact hdep.inSection f)
    have hOut := ih (K.erase f) hlt (deleteWeight w f) r e (TSPGap.outSection A f)
      (hnn.delete f) (hr.delete f) (hsup.delete f)
      (rayleighNonneg_deleteWeight hR f) heKf (TSPGap.Monotone.outSection hmono f)
      (by rw [hcomm]; exact hdep.outSection f)
    have hPair := rayleighNegCorrelated_mem hR hef
    -- rewrite every conditioned mass into the four cells
    -- the selector, in cells
    have hH2 : weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S))
          * weightMass w (fun S => e ∈ S ∧ f ∈ S)
        ≤ weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
          * weightMass w (fun S => e ∈ S ∧ f ∉ S) := by
      rw [totalMass_contractWeight,
        weightMass_congr (A := fun S => TSPGap.inSection A e S ∧ f ∈ S)
          (B := TSPGap.inSection (fun T => A T ∧ f ∈ T) e)
          (fun S => by simp [TSPGap.inSection, Finset.mem_insert, hfe]),
        weightMass_contractWeight w e (fun T => A T ∧ f ∈ T),
        weightMass_contractWeight w e A,
        weightMass_congr (A := fun S => f ∈ S) (B := TSPGap.inSection (fun T => f ∈ T) e)
          (fun S => by simp [TSPGap.inSection, Finset.mem_insert, hfe]),
        weightMass_contractWeight w e (fun T => f ∈ T)] at hinf
      rw [weightMass_mem_split_left w e f] at hinf
      rw [weightMass_congr (A := fun S => e ∈ S ∧ (A S ∧ f ∈ S))
        (B := fun S => A S ∧ (e ∈ S ∧ f ∈ S)) (fun S => by tauto),
        weightMass_memAnd_split w A e f,
        weightMass_congr (A := fun S => e ∈ S ∧ f ∈ S) (B := fun S => e ∈ S ∧ f ∈ S)
          (fun S => Iff.rfl)] at hinf
      nlinarith [hinf]
    -- positive marginal, in cells
    have hu : 0 < weightMass w (fun S => e ∈ S ∧ f ∈ S) := by
      rwa [weightMass_contract_blind (w := w) (f := e) (fun S => f ∈ S)
        (fun S => by simp [Finset.mem_insert, hfe])] at hfpos
    -- pairwise negative correlation, in cells
    have hH1 : weightMass w (fun S => e ∈ S ∧ f ∈ S) * weightMass w (fun S => e ∉ S ∧ f ∉ S)
        ≤ weightMass w (fun S => e ∈ S ∧ f ∉ S) * weightMass w (fun S => e ∉ S ∧ f ∈ S) := by
      unfold NegCorrelated at hPair
      rw [totalMass_split_four w e f, weightMass_mem_split_left w e f,
        weightMass_mem_split_right w e f] at hPair
      nlinarith [hPair]
    -- the contracted branch, in cells
    have e1 : totalMass (contractWeight w f) = weightMass w (fun S => e ∈ S ∧ f ∈ S)
        + weightMass w (fun S => e ∉ S ∧ f ∈ S) := by
      rw [totalMass_contractWeight, weightMass_mem_split_right w e f]
    have e2 : weightMass (contractWeight w f) (fun S => e ∈ S)
        = weightMass w (fun S => e ∈ S ∧ f ∈ S) := by
      rw [weightMass_contract_blind (w := w) (f := f) (fun S => e ∈ S)
        (fun S => by simp [Finset.mem_insert, hef])]
      exact weightMass_congr fun S => by tauto
    have e3 : weightMass (contractWeight w f) (TSPGap.inSection A f)
        = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
          + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∈ S)) := by
      rw [weightMass_contractWeight w f A, weightMass_memAnd_split_right w A e f]
    have e4 : weightMass (contractWeight w f) (fun S => e ∈ S ∧ TSPGap.inSection A f S)
        = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S)) := by
      have hcg : ∀ S : Finset ι,
          (e ∈ S ∧ TSPGap.inSection A f S) ↔ TSPGap.inSection (fun T => e ∈ T ∧ A T) f S := by
        intro S
        simp only [TSPGap.inSection, Finset.mem_insert, hef, false_or]
      rw [weightMass_congr hcg, weightMass_contractWeight w f (fun T => e ∈ T ∧ A T)]
      exact weightMass_congr fun S => by tauto
    have hH3 : weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∈ S))
          * weightMass w (fun S => e ∉ S ∧ f ∈ S)
        ≤ weightMass w (fun S => e ∈ S ∧ f ∈ S)
          * weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∈ S)) := by
      unfold NegCorrelated at hIn
      rw [e1, e2, e3, e4] at hIn
      nlinarith [hIn]
    -- the deleted branch, in cells
    have g1 : totalMass (deleteWeight w f) = weightMass w (fun S => e ∈ S ∧ f ∉ S)
        + weightMass w (fun S => e ∉ S ∧ f ∉ S) := by
      rw [totalMass_deleteWeight, weightMass_notMem_split w e f]
    have g2 : weightMass (deleteWeight w f) (fun S => e ∈ S)
        = weightMass w (fun S => e ∈ S ∧ f ∉ S) := by
      rw [weightMass_delete_blind (w := w) (f := f) (fun S => e ∈ S)
        (fun S => by simp [Finset.mem_erase, hef])]
      exact weightMass_congr fun S => by tauto
    have g3 : weightMass (deleteWeight w f) (TSPGap.outSection A f)
        = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S))
          + weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∉ S)) := by
      rw [weightMass_deleteWeight w f A, weightMass_notMemAnd_split w A e f]
    have g4 : weightMass (deleteWeight w f) (fun S => e ∈ S ∧ TSPGap.outSection A f S)
        = weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S)) := by
      have hcg : ∀ S : Finset ι,
          (e ∈ S ∧ TSPGap.outSection A f S) ↔ TSPGap.outSection (fun T => e ∈ T ∧ A T) f S := by
        intro S
        simp only [TSPGap.outSection, Finset.mem_erase, hef, ne_eq, not_false_eq_true, true_and]
      rw [weightMass_congr hcg, weightMass_deleteWeight w f (fun T => e ∈ T ∧ A T)]
      exact weightMass_congr fun S => by tauto
    have hH4 : weightMass w (fun S => A S ∧ (e ∈ S ∧ f ∉ S))
          * weightMass w (fun S => e ∉ S ∧ f ∉ S)
        ≤ weightMass w (fun S => e ∈ S ∧ f ∉ S)
          * weightMass w (fun S => A S ∧ (e ∉ S ∧ f ∉ S)) := by
      unfold NegCorrelated at hOut
      rw [g1, g2, g3, g4] at hOut
      nlinarith [hOut]
    exact negCorrelated_mem_of_cells
      (fourCell_negCorrelated hu (weightMass_nonneg hnn _) (weightMass_nonneg hnn _)
        (weightMass_nonneg hnn _) (weightMass_nonneg hnn _)
        (weightMass_mono hnn fun S hS => hS.2) hH1 hH2 hH3 hH4)
  · push Not at hex
    refine negCorrelated_of_no_coOccurrence hnn hsup hmono hdep fun g hg => ?_
    exact le_antisymm (hex g hg) (weightMass_nonneg (hnn.contract e) _)

/-- `coordinate_event_negCorrelation` with the usual implicit arguments. -/
theorem negCorrelated_mem_of_monotone {w : Finset ι → ℝ} {r : ℕ} {K : Finset ι} {e : ι}
    {A : Finset ι → Prop} (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (hR : RayleighNonneg (genPoly w)) (he : e ∈ K)
    (hmono : Monotone A) (hdep : EventDependsOn A (K.erase e)) :
    NegCorrelated w (fun S => e ∈ S) A :=
  coordinate_event_negCorrelation K w r e A hnn hr hsup hR he hmono hdep

/-! ### Two events: the second induction

Feder–Mihail's second step (Lyons, Theorem 6.5).  Two increasing events with
*disjoint* dependency witnesses are negatively correlated.

The selection changes: the auxiliary coordinate is chosen **inside `A`'s
dependency witness**.  Coordinates outside it have nonpositive influence on `A`
by `coordinate_event_negCorrelation`, and the influences sum to zero, so some
coordinate inside has nonnegative influence.  Disjointness then puts that
coordinate outside `B`'s witness, so the same theorem gives it nonpositive
influence on `B` — opposite signs, which is exactly what the two-cell inequality
consumes.

⚠️ Unlike the coordinate–event step, **no positive marginal is needed**: if a
branch has zero mass the submass bounds collapse the conclusion to the other
branch's recursive hypothesis. -/

/-- **Selection inside the dependency witness.**  Coordinates outside `KA` have
nonpositive influence on `A`; since all influences sum to zero, some coordinate
of `KA` has nonnegative influence. -/
theorem exists_posCorrelated_mem_of_dependsOn {w : Finset ι → ℝ} {r : ℕ} {K KA : Finset ι}
    (hnn : WeightNonneg w) (hr : FixedRankWeight r w) (hsup : WeightSupportedOn w K)
    (hR : RayleighNonneg (genPoly w)) {A : Finset ι → Prop} (hmono : Monotone A)
    (hdep : EventDependsOn A KA) (hKA : KA ⊆ K) (hne : KA.Nonempty) :
    ∃ f ∈ KA, 0 ≤ totalMass w * weightMass w (fun S => A S ∧ f ∈ S)
      - weightMass w A * weightMass w (fun S => f ∈ S) := by
  classical
  set inf : ι → ℝ := fun g => totalMass w * weightMass w (fun S => A S ∧ g ∈ S)
    - weightMass w A * weightMass w (fun S => g ∈ S) with hinfdef
  have houts : ∀ g ∈ K \ KA, inf g ≤ 0 := by
    intro g hg
    rw [Finset.mem_sdiff] at hg
    have hdg : EventDependsOn A (K.erase g) :=
      hdep.mono fun a ha => Finset.mem_erase.mpr ⟨fun h => hg.2 (h ▸ ha), hKA ha⟩
    have hnc := coordinate_event_negCorrelation K w r g A hnn hr hsup hR hg.1 hmono hdg
    unfold NegCorrelated at hnc
    rw [weightMass_congr (A := fun S => g ∈ S ∧ A S) (B := fun S => A S ∧ g ∈ S)
      fun S => by tauto] at hnc
    rw [hinfdef]
    simp only
    nlinarith [hnc]
  have hsplit : ∑ g ∈ K \ KA, inf g + ∑ g ∈ KA, inf g = ∑ g ∈ K, inf g :=
    Finset.sum_sdiff hKA
  have htot : ∑ g ∈ K, inf g = 0 := sum_influence_eq_zero hr hsup A
  have hle : ∑ g ∈ K \ KA, inf g ≤ 0 := Finset.sum_nonpos houts
  have hge : 0 ≤ ∑ g ∈ KA, inf g := by linarith [hsplit, htot, hle]
  by_contra hcon
  push Not at hcon
  have hneg : ∑ g ∈ KA, inf g < ∑ _g ∈ KA, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne fun g hg => hcon g hg
  rw [Finset.sum_const, smul_zero] at hneg
  linarith

/-- **The two-cell inequality**, division-free and zero-safe.

`x, y` are the `A ∧ B` masses of the two branches, `u, v` the branch masses,
`a, b` the `A` masses and `c, d` the `B` masses.  The hypotheses are the two
recursive branches, then `f` positively influencing `A` and negatively
influencing `B`.

⚠️ No *strict* positivity is required — unlike the coordinate–event step — but
nonnegativity and the submass bounds are, and they are not decoration: without
them the implication is false.  They are also what makes the corners free: if
`u = 0` they force `a = c = x = 0` and the conclusion *is* the second recursive
hypothesis, symmetrically for `v = 0`. -/
theorem twoCell_negCorrelated {x y u v a b c d : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hau : a ≤ u) (hbv : b ≤ v) (hcu : c ≤ u) (hdv : d ≤ v)
    (hxa : x ≤ a) (hyb : y ≤ b)
    (H1 : x * u ≤ a * c) (H2 : y * v ≤ b * d)
    (H3 : b * u ≤ a * v) (H4 : c * v ≤ u * d) :
    (x + y) * (u + v) ≤ (a + b) * (c + d) := by
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · have ha : a = 0 := le_antisymm (hu0 ▸ hau) (le_trans hx hxa)
    have hx0 : x = 0 := le_antisymm (ha ▸ hxa) hx
    have hc0 : c = 0 := le_antisymm (hu0 ▸ hcu) hc
    rw [← hu0, ha, hx0, hc0]
    simpa using H2
  rcases eq_or_lt_of_le hv with hv0 | hv0
  · have hb : b = 0 := le_antisymm (hv0 ▸ hbv) (le_trans hy hyb)
    have hy0 : y = 0 := le_antisymm (hb ▸ hyb) hy
    have hd0 : d = 0 := le_antisymm (hv0 ▸ hdv) hd
    rw [← hv0, hb, hy0, hd0]
    simpa using H1
  · have key : u * v * ((a + b) * (c + d) - (x + y) * (u + v))
        = (u * d - c * v) * (a * v - b * u)
          + (u + v) * (v * (a * c - x * u) + u * (b * d - y * v)) := by ring
    have hpos : 0 < u * v := mul_pos hu0 hv0
    nlinarith [mul_nonneg (sub_nonneg.mpr H4) (sub_nonneg.mpr H3),
      mul_nonneg (add_nonneg hu hv)
        (add_nonneg (mul_nonneg hv (sub_nonneg.mpr H1)) (mul_nonneg hu (sub_nonneg.mpr H2)))]

/-! ### Splitting at one coordinate -/

section OneSplit

variable (w : Finset ι → ℝ) (A : Finset ι → Prop) (k : ι)

theorem totalMass_split_mem :
    totalMass w = weightMass w (fun S => k ∈ S) + weightMass w (fun S => k ∉ S) := by
  classical
  rw [totalMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hk : k ∈ S <;> simp [hk]

theorem weightMass_split_memAnd :
    weightMass w A = weightMass w (fun S => k ∈ S ∧ A S)
      + weightMass w (fun S => k ∉ S ∧ A S) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S
  · by_cases hk : k ∈ S <;> simp [hA, hk]
  · simp [hA]

end OneSplit

/-- The two-event target, expressed in the two branches. -/
theorem negCorrelated_of_sections {w : Finset ι → ℝ} {f : ι} {A B : Finset ι → Prop}
    (h : (weightMass w (fun S => f ∈ S ∧ (A S ∧ B S))
          + weightMass w (fun S => f ∉ S ∧ (A S ∧ B S)))
        * (weightMass w (fun S => f ∈ S) + weightMass w (fun S => f ∉ S))
      ≤ (weightMass w (fun S => f ∈ S ∧ A S) + weightMass w (fun S => f ∉ S ∧ A S))
        * (weightMass w (fun S => f ∈ S ∧ B S) + weightMass w (fun S => f ∉ S ∧ B S))) :
    NegCorrelated w A B := by
  rw [NegCorrelated, weightMass_split_memAnd w (fun S => A S ∧ B S) f,
    totalMass_split_mem w f, weightMass_split_memAnd w A f, weightMass_split_memAnd w B f]
  exact h

/-- An event with an empty dependency witness is constant, and constants are
negatively correlated with everything. -/
theorem negCorrelated_of_constDep {w : Finset ι → ℝ} {A B : Finset ι → Prop}
    (hdep : EventDependsOn A ∅) : NegCorrelated w A B := by
  classical
  have hconst : ∀ S T : Finset ι, A S ↔ A T := fun S T => hdep S T (by simp)
  by_cases hA : A (∅ : Finset ι)
  · have hall : ∀ S : Finset ι, A S := fun S => (hconst ∅ S).mp hA
    rw [NegCorrelated,
      weightMass_congr (A := fun S => A S ∧ B S) (B := B) (fun S => ⟨fun h => h.2,
        fun h => ⟨hall S, h⟩⟩),
      weightMass_congr (A := A) (B := fun _ => True) (fun S => iff_of_true (hall S) trivial),
      weightMass_true]
    exact le_of_eq (mul_comm _ _)
  · have hnone : ∀ S : Finset ι, ¬ A S := fun S h => hA ((hconst S ∅).mp h)
    have hz : weightMass w (fun _ : Finset ι => False) = 0 := by simp [weightMass]
    rw [NegCorrelated,
      weightMass_congr (A := fun S => A S ∧ B S) (B := fun _ => False)
        (fun S => ⟨fun h => hnone S h.1, False.elim⟩),
      weightMass_congr (A := A) (B := fun _ => False)
        (fun S => ⟨fun h => hnone S h, False.elim⟩), hz, zero_mul, zero_mul]

/-- **Negative association for two increasing events with disjoint dependency
witnesses.** -/
theorem increasing_events_negCorrelation :
    ∀ (K : Finset ι) (w : Finset ι → ℝ) (r : ℕ) (A B : Finset ι → Prop) (KA KB : Finset ι),
      WeightNonneg w → FixedRankWeight r w → WeightSupportedOn w K →
      RayleighNonneg (genPoly w) → Monotone A → Monotone B →
      EventDependsOn A KA → EventDependsOn B KB → KA ⊆ K → KB ⊆ K → Disjoint KA KB →
      NegCorrelated w A B := by
  intro K
  induction K using Finset.strongInductionOn with
  | _ K ih =>
  intro w r A B KA KB hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
  classical
  rcases Finset.eq_empty_or_nonempty KA with hKA | hKA
  · exact negCorrelated_of_constDep (hKA ▸ hdA)
  obtain ⟨f, hfKA, hinf⟩ :=
    exists_posCorrelated_mem_of_dependsOn hnn hr hsup hR hmA hdA hAK hKA
  have hfK : f ∈ K := hAK hfKA
  have hfKB : f ∉ KB := Finset.disjoint_left.mp hdisj hfKA
  have hBneg : NegCorrelated w (fun S => f ∈ S) B :=
    coordinate_event_negCorrelation K w r f B hnn hr hsup hR hfK hmB
      (hdB.mono fun a ha => Finset.mem_erase.mpr ⟨fun h => hfKB (h ▸ ha), hBK ha⟩)
  have hlt : K.erase f ⊂ K := Finset.erase_ssubset hfK
  have hdisj' : Disjoint (KA.erase f) (KB.erase f) :=
    Disjoint.mono (Finset.erase_subset f KA) (Finset.erase_subset f KB) hdisj
  have hIn := ih (K.erase f) hlt (contractWeight w f) (r - 1)
    (TSPGap.inSection A f) (TSPGap.inSection B f) (KA.erase f) (KB.erase f)
    (hnn.contract f) (hr.contract f) (hsup.contract f) (rayleighNonneg_contractWeight hR f)
    (TSPGap.Monotone.inSection hmA f) (TSPGap.Monotone.inSection hmB f)
    (hdA.inSection f) (hdB.inSection f)
    (Finset.erase_subset_erase f hAK) (Finset.erase_subset_erase f hBK) hdisj'
  have hOut := ih (K.erase f) hlt (deleteWeight w f) r
    (TSPGap.outSection A f) (TSPGap.outSection B f) (KA.erase f) (KB.erase f)
    (hnn.delete f) (hr.delete f) (hsup.delete f) (rayleighNonneg_deleteWeight hR f)
    (TSPGap.Monotone.outSection hmA f) (TSPGap.Monotone.outSection hmB f)
    (hdA.outSection f) (hdB.outSection f)
    (Finset.erase_subset_erase f hAK) (Finset.erase_subset_erase f hBK) hdisj'
  -- the contracted branch, in cells
  have i1 : weightMass (contractWeight w f) (fun S => TSPGap.inSection A f S
      ∧ TSPGap.inSection B f S) = weightMass w (fun S => f ∈ S ∧ (A S ∧ B S)) := by
    rw [weightMass_congr (A := fun S => TSPGap.inSection A f S ∧ TSPGap.inSection B f S)
      (B := TSPGap.inSection (fun T => A T ∧ B T) f) (fun S => Iff.rfl)]
    exact weightMass_contractWeight w f (fun T => A T ∧ B T)
  have hH1 : weightMass w (fun S => f ∈ S ∧ (A S ∧ B S)) * weightMass w (fun S => f ∈ S)
      ≤ weightMass w (fun S => f ∈ S ∧ A S) * weightMass w (fun S => f ∈ S ∧ B S) := by
    unfold NegCorrelated at hIn
    rw [i1, totalMass_contractWeight, weightMass_contractWeight w f A,
      weightMass_contractWeight w f B] at hIn
    exact hIn
  -- the deleted branch, in cells
  have o1 : weightMass (deleteWeight w f) (fun S => TSPGap.outSection A f S
      ∧ TSPGap.outSection B f S) = weightMass w (fun S => f ∉ S ∧ (A S ∧ B S)) := by
    rw [weightMass_congr (A := fun S => TSPGap.outSection A f S ∧ TSPGap.outSection B f S)
      (B := TSPGap.outSection (fun T => A T ∧ B T) f) (fun S => Iff.rfl)]
    exact weightMass_deleteWeight w f (fun T => A T ∧ B T)
  have hH2 : weightMass w (fun S => f ∉ S ∧ (A S ∧ B S)) * weightMass w (fun S => f ∉ S)
      ≤ weightMass w (fun S => f ∉ S ∧ A S) * weightMass w (fun S => f ∉ S ∧ B S) := by
    unfold NegCorrelated at hOut
    rw [o1, totalMass_deleteWeight, weightMass_deleteWeight w f A,
      weightMass_deleteWeight w f B] at hOut
    exact hOut
  -- `f` influences `A` upward
  have hH3 : weightMass w (fun S => f ∉ S ∧ A S) * weightMass w (fun S => f ∈ S)
      ≤ weightMass w (fun S => f ∈ S ∧ A S) * weightMass w (fun S => f ∉ S) := by
    rw [weightMass_congr (A := fun S => A S ∧ f ∈ S) (B := fun S => f ∈ S ∧ A S)
      (fun S => by tauto), totalMass_split_mem w f, weightMass_split_memAnd w A f] at hinf
    nlinarith [hinf]
  -- and `B` downward
  have hH4 : weightMass w (fun S => f ∈ S ∧ B S) * weightMass w (fun S => f ∉ S)
      ≤ weightMass w (fun S => f ∈ S) * weightMass w (fun S => f ∉ S ∧ B S) := by
    unfold NegCorrelated at hBneg
    rw [totalMass_split_mem w f, weightMass_split_memAnd w B f] at hBneg
    nlinarith [hBneg]
  exact negCorrelated_of_sections
    (twoCell_negCorrelated (weightMass_nonneg hnn _) (weightMass_nonneg hnn _)
      (weightMass_nonneg hnn _) (weightMass_nonneg hnn _) (weightMass_nonneg hnn _)
      (weightMass_nonneg hnn _)
      (weightMass_mono hnn fun S hS => hS.1) (weightMass_mono hnn fun S hS => hS.1)
      (weightMass_mono hnn fun S hS => hS.1) (weightMass_mono hnn fun S hS => hS.1)
      (weightMass_mono hnn fun S hS => ⟨hS.1, hS.2.1⟩)
      (weightMass_mono hnn fun S hS => ⟨hS.1, hS.2.1⟩) hH1 hH2 hH3 hH4)

/-- `increasing_events_negCorrelation` with the usual implicit arguments. -/
theorem negCorrelated_of_disjoint_monotone {w : Finset ι → ℝ} {r : ℕ} {K KA KB : Finset ι}
    {A B : Finset ι → Prop} (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (hR : RayleighNonneg (genPoly w))
    (hmA : Monotone A) (hmB : Monotone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hAK : KA ⊆ K) (hBK : KB ⊆ K) (hdisj : Disjoint KA KB) :
    NegCorrelated w A B :=
  increasing_events_negCorrelation K w r A B KA KB hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj

/-! ### Complement algebra

Negating an event exchanges increasing and decreasing and leaves the dependency
witness alone, so the three remaining sign patterns are inclusion–exclusion away
from the increasing/increasing theorem. -/

omit [DecidableEq ι] in
theorem weightMass_not (w : Finset ι → ℝ) (A : Finset ι → Prop) :
    weightMass w (fun S => ¬ A S) = totalMass w - weightMass w A := by
  classical
  rw [totalMass, weightMass, weightMass, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S <;> simp [hA]

omit [DecidableEq ι] in
theorem weightMass_or (w : Finset ι → ℝ) (A B : Finset ι → Prop) :
    weightMass w (fun S => A S ∨ B S) + weightMass w (fun S => A S ∧ B S)
      = weightMass w A + weightMass w B := by
  classical
  rw [weightMass, weightMass, weightMass, weightMass, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S <;> by_cases hB : B S <;> simp [hA, hB]

omit [DecidableEq ι] in
theorem weightMass_and_not (w : Finset ι → ℝ) (A B : Finset ι → Prop) :
    weightMass w (fun S => A S ∧ ¬ B S)
      = weightMass w A - weightMass w (fun S => A S ∧ B S) := by
  classical
  rw [weightMass, weightMass, weightMass, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hA : A S <;> by_cases hB : B S <;> simp [hA, hB]

omit [Fintype ι] [DecidableEq ι] in
theorem Antitone.not_monotone {A : Finset ι → Prop} (h : Antitone A) :
    Monotone (fun S => ¬ A S) := fun _ _ hST hS hT => hS (h hST hT)

omit [Fintype ι] in
theorem EventDependsOn.not {A : Finset ι → Prop} {K : Finset ι} (h : EventDependsOn A K) :
    EventDependsOn (fun S => ¬ A S) K := fun S T hST => not_congr (h S T hST)

omit [DecidableEq ι] in
theorem PosCorrelated.symm {w : Finset ι → ℝ} {A B : Finset ι → Prop}
    (h : PosCorrelated w A B) : PosCorrelated w B A := by
  rw [PosCorrelated, weightMass_congr (A := fun S => B S ∧ A S) (B := fun S => A S ∧ B S)
    (fun S => by tauto), mul_comm (weightMass w B)]
  exact h

/-- **Two decreasing events with disjoint witnesses are negatively
correlated**, by inclusion–exclusion on the complements. -/
theorem decreasing_events_negCorrelation {w : Finset ι → ℝ} {r : ℕ} {K KA KB : Finset ι}
    {A B : Finset ι → Prop} (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (hR : RayleighNonneg (genPoly w))
    (hmA : Antitone A) (hmB : Antitone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hAK : KA ⊆ K) (hBK : KB ⊆ K) (hdisj : Disjoint KA KB) :
    NegCorrelated w A B := by
  have h := negCorrelated_of_disjoint_monotone hnn hr hsup hR (TSPGap.Antitone.not_monotone hmA)
    (TSPGap.Antitone.not_monotone hmB) hdA.not hdB.not hAK hBK hdisj
  have hnotand : weightMass w (fun S => ¬ A S ∧ ¬ B S)
      = totalMass w - weightMass w A - weightMass w B
        + weightMass w (fun S => A S ∧ B S) := by
    rw [weightMass_congr (A := fun S => ¬ A S ∧ ¬ B S) (B := fun S => ¬ (A S ∨ B S))
      (fun S => by tauto), weightMass_not]
    have h2 := weightMass_or w A B
    linarith
  unfold NegCorrelated at h ⊢
  rw [hnotand, weightMass_not, weightMass_not] at h
  nlinarith [h]

/-- **An increasing and a decreasing event with disjoint witnesses are
positively correlated.** -/
theorem mixed_events_posCorrelation {w : Finset ι → ℝ} {r : ℕ} {K KA KB : Finset ι}
    {A B : Finset ι → Prop} (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (hR : RayleighNonneg (genPoly w))
    (hmA : Monotone A) (hmB : Antitone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hAK : KA ⊆ K) (hBK : KB ⊆ K) (hdisj : Disjoint KA KB) :
    PosCorrelated w A B := by
  have h := negCorrelated_of_disjoint_monotone hnn hr hsup hR hmA (TSPGap.Antitone.not_monotone hmB)
    hdA hdB.not hAK hBK hdisj
  unfold NegCorrelated at h
  rw [weightMass_and_not w A B, weightMass_not] at h
  unfold PosCorrelated
  nlinarith [h]

/-- The other mixed pattern. -/
theorem mixed_events_posCorrelation' {w : Finset ι → ℝ} {r : ℕ} {K KA KB : Finset ι}
    {A B : Finset ι → Prop} (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (hR : RayleighNonneg (genPoly w))
    (hmA : Antitone A) (hmB : Monotone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hAK : KA ⊆ K) (hBK : KB ⊆ K) (hdisj : Disjoint KA KB) :
    PosCorrelated w A B :=
  (mixed_events_posCorrelation hnn hr hsup hR hmB hmA hdB hdA hBK hAK hdisj.symm).symm

/-! ### The finite-cylinder layer

Conditioning on a **cylinder** — a finite set `I` of coordinates forced in and a
finite set `O` forced out — is repeated contraction and deletion.  Every
hypothesis of the increasing/increasing theorem is closed under both
conditionings, so a finite induction over the cylinder's coordinates gives the
cross-multiplied conditional statement

`W(C ∩ A ∩ B) · W(C) ≤ W(C ∩ A) · W(C ∩ B)`

with no normalized conditional measure and no positivity assumption on `W(C)`.

⚠️ The cylinder needs **no disjointness from the witnesses** `KA`, `KB`:
conditioning only erases coordinates from them, and erasing preserves their
disjointness from each other.  Nor is `Disjoint I O` needed: an overlapping
cylinder is unsatisfiable, and the deletion bridge is blind to whether the
deleted coordinate also lies in `I`. -/

omit [Fintype ι] [DecidableEq ι] in
/-- The cylinder event: everything in `I` present, everything in `O` absent. -/
def cylinderEvent (I O : Finset ι) : Finset ι → Prop :=
  fun S => I ⊆ S ∧ ∀ j ∈ O, j ∉ S

omit [DecidableEq ι] in
/-- Masses agree for events that agree on the weight's support. -/
theorem weightMass_congr_of_support {w : Finset ι → ℝ} {A B : Finset ι → Prop}
    (h : ∀ S, w S ≠ 0 → (A S ↔ B S)) : weightMass w A = weightMass w B := by
  classical
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hw : w S = 0
  · by_cases hA : A S <;> by_cases hB : B S <;> simp [hA, hB, hw]
  · by_cases hA : A S
    · rw [if_pos hA, if_pos ((h S hw).mp hA)]
    · rw [if_neg hA, if_neg fun hB => hA ((h S hw).mpr hB)]

/-- **Forcing one more coordinate in is contraction.**  Unconditional on the
weight: with `k ∉ I` and `k ∉ O` the two events already agree pointwise. -/
theorem weightMass_cylinder_contract (w : Finset ι → ℝ) {k : ι} {I O : Finset ι}
    (hkI : k ∉ I) (hkO : k ∉ O) (X : Finset ι → Prop) :
    weightMass (contractWeight w k)
        (fun S => cylinderEvent I O S ∧ TSPGap.inSection X k S)
      = weightMass w (fun S => cylinderEvent (insert k I) O S ∧ X S) := by
  have h1 : weightMass (contractWeight w k)
        (fun S => cylinderEvent I O S ∧ TSPGap.inSection X k S)
      = weightMass (contractWeight w k)
          (TSPGap.inSection (fun S => cylinderEvent (insert k I) O S ∧ X S) k) := by
    refine weightMass_congr fun S => ?_
    simp only [TSPGap.inSection, cylinderEvent]
    constructor
    · rintro ⟨⟨hI, hO⟩, hX⟩
      refine ⟨⟨Finset.insert_subset_insert k hI, ?_⟩, hX⟩
      intro j hj hjmem
      rcases Finset.mem_insert.mp hjmem with rfl | hjS
      · exact hkO hj
      · exact hO j hj hjS
    · rintro ⟨⟨hI, hO⟩, hX⟩
      refine ⟨⟨fun a ha => ?_, fun j hj hjS => hO j hj (Finset.mem_insert_of_mem hjS)⟩, hX⟩
      rcases Finset.mem_insert.mp (hI (Finset.mem_insert_of_mem ha)) with rfl | h
      · exact absurd ha hkI
      · exact h
  rw [h1, weightMass_contractWeight]
  refine weightMass_congr fun S => ?_
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨h.1.1 (Finset.mem_insert_self k I), h⟩

/-- The cylinder's own mass, under contraction. -/
theorem weightMass_cylinder_contract' (w : Finset ι → ℝ) {k : ι} {I O : Finset ι}
    (hkI : k ∉ I) (hkO : k ∉ O) :
    weightMass (contractWeight w k) (cylinderEvent I O)
      = weightMass w (cylinderEvent (insert k I) O) := by
  have h1 : weightMass (contractWeight w k) (cylinderEvent I O)
      = weightMass (contractWeight w k)
          (fun S => cylinderEvent I O S ∧ TSPGap.inSection (fun _ => True) k S) :=
    weightMass_congr fun S => by simp [TSPGap.inSection]
  rw [h1, weightMass_cylinder_contract w hkI hkO]
  exact weightMass_congr fun S => by simp

/-- **Forcing one more coordinate out is deletion.**  ⚠️ Hypothesis-free — in
particular blind to `k ∈ I` — but only on the deleted weight's support, where
`k` is absent; this is where `weightMass_congr_of_support` earns its keep. -/
theorem weightMass_cylinder_delete (w : Finset ι → ℝ) (k : ι) (I O : Finset ι)
    (X : Finset ι → Prop) :
    weightMass (deleteWeight w k)
        (fun S => cylinderEvent I O S ∧ TSPGap.outSection X k S)
      = weightMass w (fun S => cylinderEvent I (insert k O) S ∧ X S) := by
  have h1 : weightMass (deleteWeight w k)
        (fun S => cylinderEvent I O S ∧ TSPGap.outSection X k S)
      = weightMass (deleteWeight w k)
          (TSPGap.outSection (fun S => cylinderEvent I (insert k O) S ∧ X S) k) := by
    refine weightMass_congr_of_support fun S hS => ?_
    have hk : k ∉ S := fun hmem => hS (deleteWeight_vanishes w k S hmem)
    simp only [TSPGap.outSection, cylinderEvent, Finset.erase_eq_of_notMem hk]
    constructor
    · rintro ⟨⟨hI, hO⟩, hX⟩
      refine ⟨⟨hI, ?_⟩, hX⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjO
      · exact hk
      · exact hO j hjO
    · rintro ⟨⟨hI, hO⟩, hX⟩
      exact ⟨⟨hI, fun j hj => hO j (Finset.mem_insert_of_mem hj)⟩, hX⟩
  rw [h1, weightMass_deleteWeight]
  refine weightMass_congr fun S => ?_
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨h.1.2 k (Finset.mem_insert_self k O), h⟩

/-- The cylinder's own mass, under deletion. -/
theorem weightMass_cylinder_delete' (w : Finset ι → ℝ) (k : ι) (I O : Finset ι) :
    weightMass (deleteWeight w k) (cylinderEvent I O)
      = weightMass w (cylinderEvent I (insert k O)) := by
  have h1 : weightMass (deleteWeight w k) (cylinderEvent I O)
      = weightMass (deleteWeight w k)
          (fun S => cylinderEvent I O S ∧ TSPGap.outSection (fun _ => True) k S) :=
    weightMass_congr fun S => by simp [TSPGap.outSection]
  rw [h1, weightMass_cylinder_delete w k I O]
  exact weightMass_congr fun S => by simp

/-- The in-only cylinder: peel `I` by contraction down to the unconditional
theorem. -/
theorem cylinder_in_negCorrelation (I : Finset ι) :
    ∀ (w : Finset ι → ℝ) (r : ℕ) (K KA KB : Finset ι) (A B : Finset ι → Prop),
      WeightNonneg w → FixedRankWeight r w → WeightSupportedOn w K →
      RayleighNonneg (genPoly w) → Monotone A → Monotone B →
      EventDependsOn A KA → EventDependsOn B KB → KA ⊆ K → KB ⊆ K → Disjoint KA KB →
      weightMass w (fun S => cylinderEvent I ∅ S ∧ (A S ∧ B S))
          * weightMass w (cylinderEvent I ∅)
        ≤ weightMass w (fun S => cylinderEvent I ∅ S ∧ A S)
            * weightMass w (fun S => cylinderEvent I ∅ S ∧ B S) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro w r K KA KB A B hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
    have h := negCorrelated_of_disjoint_monotone hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
    unfold NegCorrelated at h
    rw [weightMass_congr (A := fun S => cylinderEvent ∅ ∅ S ∧ (A S ∧ B S))
        (B := fun S => A S ∧ B S) (fun S => by simp [cylinderEvent]),
      weightMass_congr (A := cylinderEvent ∅ ∅) (B := fun _ => True)
        (fun S => by simp [cylinderEvent]),
      weightMass_true,
      weightMass_congr (A := fun S => cylinderEvent ∅ ∅ S ∧ A S) (B := A)
        (fun S => by simp [cylinderEvent]),
      weightMass_congr (A := fun S => cylinderEvent ∅ ∅ S ∧ B S) (B := B)
        (fun S => by simp [cylinderEvent])]
    exact h
  | @insert k I hkI ih =>
    intro w r K KA KB A B hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
    have h := ih (contractWeight w k) (r - 1) (K.erase k) (KA.erase k) (KB.erase k)
      (TSPGap.inSection A k) (TSPGap.inSection B k)
      (hnn.contract k) (hr.contract k) (hsup.contract k)
      (rayleighNonneg_contractWeight hR k)
      (TSPGap.Monotone.inSection hmA k) (TSPGap.Monotone.inSection hmB k)
      (hdA.inSection k) (hdB.inSection k)
      (Finset.erase_subset_erase k hAK) (Finset.erase_subset_erase k hBK)
      (Disjoint.mono (Finset.erase_subset k KA) (Finset.erase_subset k KB) hdisj)
    rw [weightMass_congr
        (A := fun S => cylinderEvent I ∅ S
          ∧ (TSPGap.inSection A k S ∧ TSPGap.inSection B k S))
        (B := fun S => cylinderEvent I ∅ S ∧ TSPGap.inSection (fun T => A T ∧ B T) k S)
        (fun S => Iff.rfl),
      weightMass_cylinder_contract w hkI (Finset.notMem_empty k) (fun T => A T ∧ B T),
      weightMass_cylinder_contract' w hkI (Finset.notMem_empty k),
      weightMass_cylinder_contract w hkI (Finset.notMem_empty k) A,
      weightMass_cylinder_contract w hkI (Finset.notMem_empty k) B] at h
    exact h

/-- The general cylinder: peel `O` by deletion down to the in-only case. -/
theorem cylinder_negCorrelation_aux (O : Finset ι) :
    ∀ (I : Finset ι) (w : Finset ι → ℝ) (r : ℕ) (K KA KB : Finset ι) (A B : Finset ι → Prop),
      WeightNonneg w → FixedRankWeight r w → WeightSupportedOn w K →
      RayleighNonneg (genPoly w) → Monotone A → Monotone B →
      EventDependsOn A KA → EventDependsOn B KB → KA ⊆ K → KB ⊆ K → Disjoint KA KB →
      weightMass w (fun S => cylinderEvent I O S ∧ (A S ∧ B S))
          * weightMass w (cylinderEvent I O)
        ≤ weightMass w (fun S => cylinderEvent I O S ∧ A S)
            * weightMass w (fun S => cylinderEvent I O S ∧ B S) := by
  classical
  induction O using Finset.induction_on with
  | empty =>
    intro I w r K KA KB A B hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
    exact cylinder_in_negCorrelation I w r K KA KB A B
      hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
  | @insert k O _hkO ih =>
    intro I w r K KA KB A B hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj
    have h := ih I (deleteWeight w k) r (K.erase k) (KA.erase k) (KB.erase k)
      (TSPGap.outSection A k) (TSPGap.outSection B k)
      (hnn.delete k) (hr.delete k) (hsup.delete k)
      (rayleighNonneg_deleteWeight hR k)
      (TSPGap.Monotone.outSection hmA k) (TSPGap.Monotone.outSection hmB k)
      (hdA.outSection k) (hdB.outSection k)
      (Finset.erase_subset_erase k hAK) (Finset.erase_subset_erase k hBK)
      (Disjoint.mono (Finset.erase_subset k KA) (Finset.erase_subset k KB) hdisj)
    rw [weightMass_congr
        (A := fun S => cylinderEvent I O S
          ∧ (TSPGap.outSection A k S ∧ TSPGap.outSection B k S))
        (B := fun S => cylinderEvent I O S ∧ TSPGap.outSection (fun T => A T ∧ B T) k S)
        (fun S => Iff.rfl),
      weightMass_cylinder_delete w k I O (fun T => A T ∧ B T),
      weightMass_cylinder_delete' w k I O,
      weightMass_cylinder_delete w k I O A,
      weightMass_cylinder_delete w k I O B] at h
    exact h

/-- **Conditional negative correlation on a cylinder**, cross-multiplied:
`W(C ∩ A ∩ B) · W(C) ≤ W(C ∩ A) · W(C ∩ B)` for increasing `A`, `B` with
disjoint dependency witnesses and any cylinder `C`. -/
theorem cylinder_negCorrelated {w : Finset ι → ℝ} {r : ℕ} {K KA KB : Finset ι}
    {A B : Finset ι → Prop} (hnn : WeightNonneg w) (hr : FixedRankWeight r w)
    (hsup : WeightSupportedOn w K) (hR : RayleighNonneg (genPoly w))
    (hmA : Monotone A) (hmB : Monotone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hAK : KA ⊆ K) (hBK : KB ⊆ K) (hdisj : Disjoint KA KB)
    (I O : Finset ι) :
    weightMass w (fun S => cylinderEvent I O S ∧ (A S ∧ B S))
        * weightMass w (cylinderEvent I O)
      ≤ weightMass w (fun S => cylinderEvent I O S ∧ A S)
          * weightMass w (fun S => cylinderEvent I O S ∧ B S) :=
  cylinder_negCorrelation_aux O I w r K KA KB A B
    hnn hr hsup hR hmA hmB hdA hdB hAK hBK hdisj

/-! ### The tree bridge and the event exports -/

theorem TreeDist.weightNonneg {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) :
    WeightNonneg μ.prob := μ.prob_nonneg

theorem TreeDist.fixedRankWeight {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) :
    FixedRankWeight (n - 1) μ.prob := fun S hS => (μ.support_spanningTree S hS).2.1

theorem TreeDist.weightSupportedOn {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) :
    WeightSupportedOn μ.prob Finset.univ := fun S _ => Finset.subset_univ S

open Classical in
/-- The one bridge from the generic masses to `TreeDist` probabilities. -/
theorem weightMass_treeDist {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)
    (A : Finset (Sym2 (Fin n)) → Prop) : weightMass μ.prob A = μ.probEvent A := by
  rw [weightMass_eq_filter_sum, probEvent_filter]

theorem totalMass_treeDist {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) :
    totalMass μ.prob = 1 := μ.total

section Exports

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
  {A B : Finset (Sym2 (Fin n)) → Prop} {KA KB : Finset (Sym2 (Fin n))}

/-- **Negative association at the max-entropy limit: two increasing events.** -/
theorem IsMaxEntropyLimit.negAssoc_increasing (h : IsMaxEntropyLimit μ)
    (hmA : Monotone A) (hmB : Monotone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hdisj : Disjoint KA KB) :
    μ.probEvent (fun T => A T ∧ B T) ≤ μ.probEvent A * μ.probEvent B := by
  have hnc := negCorrelated_of_disjoint_monotone μ.weightNonneg μ.fixedRankWeight
    μ.weightSupportedOn (rayleighNonneg_genPoly h.treeRealStable) hmA hmB hdA hdB
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj
  unfold NegCorrelated at hnc
  rwa [weightMass_treeDist, weightMass_treeDist, weightMass_treeDist,
    totalMass_treeDist, mul_one] at hnc

/-- Two decreasing events. -/
theorem IsMaxEntropyLimit.negAssoc_decreasing (h : IsMaxEntropyLimit μ)
    (hmA : Antitone A) (hmB : Antitone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hdisj : Disjoint KA KB) :
    μ.probEvent (fun T => A T ∧ B T) ≤ μ.probEvent A * μ.probEvent B := by
  have hnc := decreasing_events_negCorrelation μ.weightNonneg μ.fixedRankWeight
    μ.weightSupportedOn (rayleighNonneg_genPoly h.treeRealStable) hmA hmB hdA hdB
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj
  unfold NegCorrelated at hnc
  rwa [weightMass_treeDist, weightMass_treeDist, weightMass_treeDist,
    totalMass_treeDist, mul_one] at hnc

/-- Increasing against decreasing: positively correlated. -/
theorem IsMaxEntropyLimit.posAssoc_increasing_decreasing (h : IsMaxEntropyLimit μ)
    (hmA : Monotone A) (hmB : Antitone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hdisj : Disjoint KA KB) :
    μ.probEvent A * μ.probEvent B ≤ μ.probEvent (fun T => A T ∧ B T) := by
  have hpc := mixed_events_posCorrelation μ.weightNonneg μ.fixedRankWeight
    μ.weightSupportedOn (rayleighNonneg_genPoly h.treeRealStable) hmA hmB hdA hdB
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj
  unfold PosCorrelated at hpc
  rwa [weightMass_treeDist, weightMass_treeDist, weightMass_treeDist,
    totalMass_treeDist, mul_one] at hpc

/-- Decreasing against increasing. -/
theorem IsMaxEntropyLimit.posAssoc_decreasing_increasing (h : IsMaxEntropyLimit μ)
    (hmA : Antitone A) (hmB : Monotone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hdisj : Disjoint KA KB) :
    μ.probEvent A * μ.probEvent B ≤ μ.probEvent (fun T => A T ∧ B T) := by
  have hpc := mixed_events_posCorrelation' μ.weightNonneg μ.fixedRankWeight
    μ.weightSupportedOn (rayleighNonneg_genPoly h.treeRealStable) hmA hmB hdA hdB
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj
  unfold PosCorrelated at hpc
  rwa [weightMass_treeDist, weightMass_treeDist, weightMass_treeDist,
    totalMass_treeDist, mul_one] at hpc

/-- **Conditional negative association at the max-entropy limit**: conditioned
on any cylinder — edges `I` forced into the tree, edges `O` forced out — two
increasing events with disjoint witnesses stay negatively correlated, in
cross-multiplied form, with no positivity needed for the cylinder's
probability and no disjointness between the cylinder and the witnesses. -/
theorem IsMaxEntropyLimit.negAssoc_cylinder (h : IsMaxEntropyLimit μ)
    (hmA : Monotone A) (hmB : Monotone B) (hdA : EventDependsOn A KA)
    (hdB : EventDependsOn B KB) (hdisj : Disjoint KA KB)
    (I O : Finset (Sym2 (Fin n))) :
    μ.probEvent (fun T => cylinderEvent I O T ∧ (A T ∧ B T))
        * μ.probEvent (cylinderEvent I O)
      ≤ μ.probEvent (fun T => cylinderEvent I O T ∧ A T)
          * μ.probEvent (fun T => cylinderEvent I O T ∧ B T) := by
  have hc := cylinder_negCorrelated μ.weightNonneg μ.fixedRankWeight μ.weightSupportedOn
    (rayleighNonneg_genPoly h.treeRealStable) hmA hmB hdA hdB
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj I O
  rwa [weightMass_treeDist, weightMass_treeDist, weightMass_treeDist,
    weightMass_treeDist] at hc

end Exports

/-! ### What remains

⭐ The Feder–Mihail layer is **complete**: both inductions
(`coordinate_event_negCorrelation`, `increasing_events_negCorrelation`), the
complement algebra, the finite-cylinder conditional statement
(`cylinder_negCorrelated`), and the `IsMaxEntropyLimit` exports.  Tree
conditioning stays separate, under `Fact28.lean`.  Next consumers: the
truncation step and the KKO §5 anti-concentration argument, which will feed the
exports above.

⚠️ An earlier draft of this note pointed at a stochastic-domination argument.
That was wrong: no coupling theorem is needed, and `influence_cross_bound` above,
though valid, is the wrong shape for this route — the working decomposition is
the four-cell one. -/

end TSPGap

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeAtomFace

/-!
# Bundle partitions, connectivity baselines, and the present face

The structural layer Lemma 5.17 runs on, below all of its numerics.

## Support completeness

⚠️ `E ⊆ betweenEdges u v` is enough for Lemma 2.27, but **not** for the cut
decompositions: `δ(u) − E` is only the right object if `E` captures *every*
edge of a supported tree that runs between `u` and `v`.  `SupportComplete`
says exactly that, in the form the proofs consume — `S ∩ betweenEdges u v ⊆ E`
on the support.  Zero-marginal ambient edges may stay outside `E`; the
hierarchy discharges the condition through `isEdgeParent_of_between_children`.

## Connectivity baselines

KKO's "`U_T ≥ 1` and `(V+f)_T ≥ 1` with probability 1 under `ν−e`, because
otherwise the tree would be disconnected".  Formally: a spanning tree crosses
every proper nonempty vertex set at least once, and conditioning a bundle
*out* cannot remove any of those crossings, because the conditioned trees meet
the bundle nowhere.  So `δ(a) ∖ E` still carries at least one edge —
`one_le_card_inter_sdiff_of_avoid`, and its mass form
`totalMass_le_expCard_avoid`, which is the shifted baseline the three-cell
corollary needs.

## The present face

Conditioning a bundle *in* is the maximum face at `m = 1` on a one-hot
support, so `MaxFace.lean` applies unchanged: `presentWeight w E`, its mass,
its stability.  And the two conditionings commute on the nose — both are
coordinate restrictions — which is what lets `ν+f−e` be read either way.

## Main results

* `SupportComplete`, `bundle_disjoint`, `card_inter_cut_split`.
* `exists_crossing_edge`, `one_le_card_cut_inter_atom`,
  `one_le_card_inter_sdiff_of_avoid`, `totalMass_le_expCard_avoid`.
* `presentWeight`, `totalMass_presentWeight`,
  `isRealStable_genPoly_presentDist`, `present_avoid_comm`.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Support-complete bundles -/

/-- The bundle captures every supported crossing between its endpoint atoms.
The `⊆ betweenEdges` half is Lemma 2.27's hypothesis; the support half is what
the cut decompositions need. -/
def SupportComplete (w : Finset (Sym2 (Fin n)) → ℝ) (E : Finset (Sym2 (Fin n)))
    (u v : Finset (Fin n)) : Prop :=
  E ⊆ betweenEdges u v ∧ ∀ S, w S ≠ 0 → S ∩ betweenEdges u v ⊆ E

theorem betweenEdges_subset_cutEdges_left {A B : Finset (Fin n)} (h : Disjoint A B) :
    betweenEdges A B ⊆ cutEdges A := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
  exact mem_cutEdges_iff''.mpr ⟨a, ha, b,
    Finset.mem_compl.mpr (fun hc => Finset.disjoint_left.mp h hc hb), rfl⟩

/-- Two bundles sharing only the middle atom are disjoint. -/
theorem bundle_disjoint {u v z : Finset (Fin n)} (huv : Disjoint u v)
    (huz : Disjoint u z) : Disjoint (betweenEdges u v) (betweenEdges v z) := by
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
  obtain ⟨c, hc, d, hd, hcd⟩ := mem_betweenEdges_iff.mp he'
  rcases Sym2.eq_iff.mp hcd with ⟨h1, -⟩ | ⟨h2, -⟩
  · exact Finset.disjoint_left.mp huv ha (by rw [h1]; exact hc)
  · exact Finset.disjoint_left.mp huz ha (by rw [h2]; exact hd)

open Classical in
/-- The middle atom's cut splits into the two bundles and the rest. -/
theorem card_inter_cut_split {T E F D : Finset (Sym2 (Fin n))}
    (hEF : Disjoint E F) (hED : Disjoint E D) (hFD : Disjoint F D) :
    (T ∩ (E ∪ F ∪ D)).card = (T ∩ E).card + (T ∩ F).card + (T ∩ D).card := by
  classical
  have hd1 : Disjoint (T ∩ E) (T ∩ F) :=
    hEF.mono Finset.inter_subset_right Finset.inter_subset_right
  have hd2 : Disjoint (T ∩ E ∪ T ∩ F) (T ∩ D) := by
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact hED.mono Finset.inter_subset_right Finset.inter_subset_right
    · exact hFD.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]

/-! ### Connectivity baselines -/

/-- A walk from inside `a` to outside `a` crosses `δ(a)`. -/
theorem exists_crossing_edge {T : Finset (Sym2 (Fin n))} {a : Finset (Fin n)}
    {x y : Fin n}
    (p : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).Walk x y) :
    x ∈ a → y ∉ a → ∃ e ∈ p.edges, e ∈ cutEdges a := by
  induction p with
  | nil => intro hx hy; exact absurd hx hy
  | @cons b c d hadj q ih =>
      intro hx hy
      by_cases hc : c ∈ a
      · obtain ⟨e, hep, hecut⟩ := ih hc hy
        exact ⟨e, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hep, hecut⟩
      · refine ⟨s(b, c), by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self, ?_⟩
        exact mem_cutEdges_iff''.mpr ⟨b, hx, c, Finset.mem_compl.mpr hc, rfl⟩

/-- **A spanning tree crosses every proper nonempty vertex set.** -/
theorem one_le_card_cut_inter_atom {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {a : Finset (Fin n)} (hne : a.Nonempty)
    (hproper : a ≠ Finset.univ) : 1 ≤ (T ∩ cutEdges a).card := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ a := by
    by_contra hc
    exact hproper (Finset.eq_univ_iff_forall.mpr
      fun x => not_not.mp (not_exists.mp hc x))
  obtain ⟨p⟩ := hT.2.2.preconnected x y
  obtain ⟨e, hep, hecut⟩ := exists_crossing_edge (a := a) p hx hy
  have heT : e ∈ T := by
    have := p.edges_subset_edgeSet hep
    rw [SimpleGraph.edgeSet_fromEdgeSet] at this
    simpa using this.1
  exact Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨heT, hecut⟩⟩

/-- **The baseline survives conditioning a bundle out.**  On a tree missing
`E` entirely, the crossings of `δ(a)` are all still in `δ(a) ∖ E`. -/
theorem one_le_card_inter_sdiff_of_avoid {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {a : Finset (Fin n)} (hne : a.Nonempty)
    (hproper : a ≠ Finset.univ) {E : Finset (Sym2 (Fin n))}
    (hE : (T ∩ E).card = 0) : 1 ≤ (T ∩ (cutEdges a \ E)).card := by
  classical
  have hTE : ∀ x ∈ T, x ∉ E := by
    intro x hx hxE
    have : x ∈ T ∩ E := Finset.mem_inter.mpr ⟨hx, hxE⟩
    rw [Finset.card_eq_zero] at hE
    simp [hE] at this
  have hsub : T ∩ cutEdges a ⊆ T ∩ (cutEdges a \ E) := by
    intro x hx
    obtain ⟨hxT, hxc⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hxT, Finset.mem_sdiff.mpr ⟨hxc, hTE x hxT⟩⟩
  exact le_trans (one_le_card_cut_inter_atom hT hne hproper) (Finset.card_le_card hsub)

open Classical in
/-- The mass form of the baseline: `E_ν[(δ(a) ∖ E)_T] ≥ 1`, cross-multiplied. -/
theorem totalMass_le_expCard_avoid {w : Finset (Sym2 (Fin n)) → ℝ}
    (hnn : WeightNonneg w) (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {a : Finset (Fin n)} (hne : a.Nonempty) (hproper : a ≠ Finset.univ)
    (E : Finset (Sym2 (Fin n))) :
    totalMass (avoidWeight w E) ≤ expCard (avoidWeight w E) (cutEdges a \ E) := by
  classical
  rw [totalMass, expCard]
  refine Finset.sum_le_sum fun S _ => ?_
  rcases eq_or_ne (avoidWeight w E S) 0 with h0 | h0
  · rw [h0, zero_mul]
  · have hcard : (S ∩ E).card = 0 := by
      by_contra hc
      exact h0 (by rw [avoidWeight_apply, if_neg hc])
    have hwS : w S ≠ 0 := by
      intro hc
      exact h0 (by rw [avoidWeight_apply, if_pos hcard, hc])
    have hbase := one_le_card_inter_sdiff_of_avoid (htree S hwS) hne hproper hcard
    have hnn' : 0 ≤ avoidWeight w E S := weightNonneg_avoidWeight hnn E S
    have : (1 : ℝ) ≤ ((S ∩ (cutEdges a \ E)).card : ℝ) := by exact_mod_cast hbase
    nlinarith [hnn', this]

/-! ### The present face -/

section Present

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `w` conditioned on the bundle `E` being **present**: the maximum face at
`m = 1` of a one-hot support. -/
noncomputable def presentWeight (w : Finset ι → ℝ) (E : Finset ι) : Finset ι → ℝ :=
  faceWeight w (indicatorCost E) 1

omit [Fintype ι] in
theorem presentWeight_apply (w : Finset ι → ℝ) (E : Finset ι) (S : Finset ι) :
    presentWeight w E S = if (S ∩ E).card = 1 then w S else 0 :=
  faceWeight_indicatorCost_apply w E 1 S

theorem totalMass_presentWeight (w : Finset ι → ℝ) (E : Finset ι) :
    totalMass (presentWeight w E) = weightMass w (fun S => (S ∩ E).card = 1) :=
  totalMass_face w E 1

/-- On a one-hot support the present face carries exactly the bundle's
expected count. -/
theorem totalMass_presentWeight_eq_expCard {w : Finset ι → ℝ} {E : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) :
    totalMass (presentWeight w E) = expCard w E := by
  rw [totalMass_presentWeight, expCard_eq_weightMass_one hone]

omit [Fintype ι] in
theorem weightNonneg_presentWeight {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (E : Finset ι) : WeightNonneg (presentWeight w E) :=
  weightNonneg_faceWeight hnn (indicatorCost E) 1

/-- Stability of the normalized present face — the maximum-face route, since
one-hot support makes `m = 1` a maximum. -/
theorem isRealStable_genPoly_presentDist {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {E : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1)
    (hmass : 0 < totalMass (presentWeight w E)) :
    IsRealStable (genPoly (faceDist w (indicatorCost E) 1)) :=
  isRealStable_genPoly_maxFaceDist hst hr hnn hone hmass

/-! ### The present-side conditional comparisons

The mirror of `marginal_avoid_ge` / `expCard_avoid_ge` / `expCard_avoid_le`
(`Conditioning.lean`): on a one-hot support, conditioning the bundle to be
**present** can only *lower* a marginal off the bundle — `e ∈ T` and the
increasing `1 ≤ |T ∩ F|` are negatively correlated, and on the support
`1 ≤ |T ∩ F|` *is* the face event — while fixed rank bounds the loss:
conditioning fixes the bundle's own count at `1`, so by conservation the
outside can lose at most the mass the bundle gains, which normalizes to
`E[X] + E[F] − 1 ≤ E[X | F present] ≤ E[X]` for `X` disjoint from `F`.
Cross-multiplied; no positivity assumptions. -/

/-- **Conditioning on presence lowers the marginals off `F`**, on a one-hot
support.  Negative correlation between `e ∈ T` and `1 ≤ |T ∩ F|`. -/
theorem marginal_present_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1) {e : ι} (he : e ∉ F) :
    weightMass (presentWeight w F) (fun S => e ∈ S) * totalMass w
      ≤ weightMass w (fun S => e ∈ S) * totalMass (presentWeight w F) := by
  classical
  have hmem : Monotone (fun S : Finset ι => e ∈ S) := fun _ _ hST hmem => hST hmem
  have hdmem : EventDependsOn (fun S : Finset ι => e ∈ S) {e} := by
    intro S T hST
    constructor
    · intro h
      have hin : e ∈ S ∩ {e} :=
        Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self e⟩
      rw [hST] at hin
      exact (Finset.mem_inter.mp hin).1
    · intro h
      have hin : e ∈ T ∩ {e} :=
        Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self e⟩
      rw [← hST] at hin
      exact (Finset.mem_inter.mp hin).1
  have hNC := negCorrelated_of_disjoint_monotone hnn hr
    (K := Finset.univ) (fun S _ => Finset.subset_univ S)
    (rayleighNonneg_genPoly hst) hmem (monotone_le_card F 1) hdmem
    (eventDependsOn_le_card F 1) (Finset.subset_univ _) (Finset.subset_univ _)
    (Finset.disjoint_singleton_left.mpr he)
  unfold NegCorrelated at hNC
  have hbridge : weightMass (presentWeight w F) (fun S => e ∈ S)
      = weightMass w (fun S => e ∈ S ∧ 1 ≤ (S ∩ F).card) := by
    rw [presentWeight, weightMass_face]
    refine weightMass_congr_of_support fun S hS => ?_
    have := hone S hS
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
  have htotp : totalMass (presentWeight w F)
      = weightMass w (fun S => 1 ≤ (S ∩ F).card) := by
    rw [totalMass_presentWeight]
    refine weightMass_congr_of_support fun S hS => ?_
    have := hone S hS
    omega
  rw [hbridge, htotp]
  exact hNC

/-- **`E[X | F present] ≤ E[X]`** for `X` disjoint from `F`, cross-multiplied. -/
theorem expCard_present_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1) {X : Finset ι}
    (hXF : Disjoint X F) :
    expCard (presentWeight w F) X * totalMass w
      ≤ expCard w X * totalMass (presentWeight w F) := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.sum_mul,
    Finset.sum_mul]
  exact Finset.sum_le_sum fun e he =>
    marginal_present_le hst hr hnn hone (Finset.disjoint_left.mp hXF he)

/-- On the present face the bundle's expected count is exactly the mass. -/
theorem expCard_presentWeight_self (w : Finset ι → ℝ) (F : Finset ι) :
    expCard (presentWeight w F) F = totalMass (presentWeight w F) := by
  classical
  rw [expCard, totalMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [presentWeight_apply]
  by_cases h : (S ∩ F).card = 1
  · rw [if_pos h, h, Nat.cast_one, mul_one]
  · rw [if_neg h, zero_mul]

/-- **`E[X] + E[F] − 1 ≤ E[X | F present]`** (normalized reading) for `X`
disjoint from `F`, cross-multiplied: conservation at fixed rank, spending
`expCard_present_le` on the rest of the ground set. -/
theorem expCard_present_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1) {X : Finset ι}
    (hXF : Disjoint X F) :
    (expCard w X + expCard w F - totalMass w) * totalMass (presentWeight w F)
      ≤ expCard (presentWeight w F) X * totalMass w := by
  classical
  have hrank : FixedRankWeight r (presentWeight w F) :=
    fixedRankWeight_faceWeight hr _ 1
  have hpart : ∀ v : Finset ι → ℝ,
      expCard v X + expCard v F + expCard v (Finset.univ \ (X ∪ F))
        = expCard v Finset.univ := by
    intro v
    rw [expCard_sdiff_of_subset v (Finset.subset_univ (X ∪ F)),
      expCard_union_of_disjoint v hXF]
    ring
  have hRF : Disjoint (Finset.univ \ (X ∪ F)) F :=
    Finset.disjoint_left.mpr fun a ha haF =>
      (Finset.mem_sdiff.mp ha).2 (Finset.mem_union_right _ haF)
  have hR := expCard_present_le hst hr hnn hone hRF
  have h0 := hpart (presentWeight w F)
  have h1 := hpart w
  rw [expCard_univ hrank, expCard_presentWeight_self] at h0
  rw [expCard_univ hr] at h1
  have e0 : expCard (presentWeight w F) X * totalMass w
      = ((r : ℝ) * totalMass (presentWeight w F)
          - totalMass (presentWeight w F)
          - expCard (presentWeight w F) (Finset.univ \ (X ∪ F)))
        * totalMass w := by
    rw [← h0]; ring
  have e1 : (expCard w X + expCard w F - totalMass w)
        * totalMass (presentWeight w F)
      = ((r : ℝ) * totalMass w - expCard w (Finset.univ \ (X ∪ F))
          - totalMass w) * totalMass (presentWeight w F) := by
    rw [← h1]; ring
  rw [e0, e1]
  nlinarith [hR]

/-- A set the support never meets has expected count zero. -/
theorem expCard_eq_zero_of_support {w : Finset ι → ℝ} {D : Finset ι}
    (h : ∀ S, w S ≠ 0 → (S ∩ D).card = 0) : expCard w D = 0 := by
  classical
  rw [expCard]
  refine Finset.sum_eq_zero fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · rw [h0, zero_mul]
  · rw [h S h0, Nat.cast_zero, mul_zero]

/-! ### Present and avoid commute -/

omit [Fintype ι] in
open Classical in
theorem present_avoid_comm (w : Finset ι → ℝ) (E F : Finset ι) :
    avoidWeight (presentWeight w F) E = presentWeight (avoidWeight w E) F := by
  classical
  funext S
  rw [avoidWeight_apply, presentWeight_apply, presentWeight_apply, avoidWeight_apply]
  by_cases h1 : (S ∩ E).card = 0 <;> by_cases h2 : (S ∩ F).card = 1 <;>
    simp [h1, h2]

omit [Fintype ι] [DecidableEq ι] in
open Classical in
theorem avoid_avoid_comm (w : Finset ι → ℝ) (E F : Finset ι) :
    avoidWeight (avoidWeight w F) E = avoidWeight (avoidWeight w E) F := by
  classical
  funext S
  rw [avoidWeight_apply, avoidWeight_apply, avoidWeight_apply, avoidWeight_apply]
  by_cases h1 : (S ∩ E).card = 0 <;> by_cases h2 : (S ∩ F).card = 0 <;>
    simp [h1, h2]

end Present

/-! ### Consuming support completeness

`ThreeCell` wants genuine `Finset.Disjoint`, not "disjoint on the support".
Support completeness is what converts the one into the other: on a supported
tree the bundle `E` and the ambient `betweenEdges u v` cut out the same edges,
so every count may be taken against the *ambient* sets — and those really are
disjoint, because `δ(u) ∩ δ(v) = betweenEdges u v` for disjoint atoms. -/

theorem inter_bundle_eq_of_supportComplete {w : Finset (Sym2 (Fin n)) → ℝ}
    {E : Finset (Sym2 (Fin n))} {u v : Finset (Fin n)}
    (hSC : SupportComplete w E u v) {S : Finset (Sym2 (Fin n))} (hS : w S ≠ 0) :
    S ∩ E = S ∩ betweenEdges u v := by
  classical
  refine Finset.Subset.antisymm ?_ (fun x hx => Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).1, hSC.2 S hS hx⟩)
  intro x hx
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
    hSC.1 (Finset.mem_inter.mp hx).2⟩

/-- **Two disjoint atoms' cuts meet exactly in the bundle between them.** -/
theorem cutEdges_inter_cutEdges {u v : Finset (Fin n)} (huv : Disjoint u v) :
    cutEdges u ∩ cutEdges v = betweenEdges u v := by
  classical
  ext e
  refine ⟨fun he => ?_, fun he => ?_⟩
  · obtain ⟨hu, hv⟩ := Finset.mem_inter.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hu
    obtain ⟨c, hc, d, -, hcd⟩ := mem_cutEdges_iff''.mp hv
    rcases Sym2.eq_iff.mp hcd with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (show a ∈ v by rw [h1]; exact hc) (Finset.disjoint_left.mp huv ha)
    · exact mem_betweenEdges_iff.mpr ⟨a, ha, b, by rw [h2]; exact hc, rfl⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact mem_cutEdges_iff''.mpr ⟨a, ha, b,
        Finset.mem_compl.mpr fun hc => Finset.disjoint_left.mp huv hc hb, rfl⟩
    · exact mem_cutEdges_iff''.mpr ⟨b, hb, a,
        Finset.mem_compl.mpr fun hc => Finset.disjoint_left.mp huv ha hc, Sym2.eq_swap⟩

/-- The two punctured cuts are **literally** disjoint. -/
theorem disjoint_punctured_cuts {u v : Finset (Fin n)} (huv : Disjoint u v) :
    Disjoint (cutEdges u \ betweenEdges u v) (cutEdges v \ betweenEdges u v) := by
  classical
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  obtain ⟨heu, hE⟩ := Finset.mem_sdiff.mp he
  obtain ⟨hev, -⟩ := Finset.mem_sdiff.mp he'
  exact hE (by rw [← cutEdges_inter_cutEdges huv]; exact Finset.mem_inter.mpr ⟨heu, hev⟩)

/-- The punctured cut may be taken against the ambient bundle. -/
theorem inter_punctured_eq_of_supportComplete {w : Finset (Sym2 (Fin n)) → ℝ}
    {E : Finset (Sym2 (Fin n))} {u v a : Finset (Fin n)}
    (hSC : SupportComplete w E u v) {S : Finset (Sym2 (Fin n))} (hS : w S ≠ 0) :
    S ∩ (cutEdges a \ E) = S ∩ (cutEdges a \ betweenEdges u v) := by
  classical
  have hb := inter_bundle_eq_of_supportComplete hSC hS
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hx, hc, hE⟩
    refine ⟨hx, hc, fun hcon => hE ?_⟩
    have : x ∈ S ∩ betweenEdges u v := Finset.mem_inter.mpr ⟨hx, hcon⟩
    exact (Finset.mem_inter.mp (hb ▸ this)).2
  · rintro ⟨hx, hc, hB⟩
    refine ⟨hx, hc, fun hcon => hB ?_⟩
    have : x ∈ S ∩ E := Finset.mem_inter.mpr ⟨hx, hcon⟩
    exact (Finset.mem_inter.mp (hb ▸ this)).2

/-! ### Normalizing the present/avoid restriction once

`present_avoid_comm` is an equality of *raw* weights.  The kernel works with
normalized laws, so the same equality is needed one level up.  It follows from
scale-invariance: both normalized conditionings divide by their own mass, so
rescaling the input by any nonzero constant leaves them unchanged. -/

section Normalize

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem avoidWeight_smul (c : ℝ) (w : Finset ι → ℝ) (E : Finset ι) :
    avoidWeight (fun S => c * w S) E = fun S => c * avoidWeight w E S := by
  classical
  funext S
  rw [avoidWeight_apply, avoidWeight_apply]
  by_cases h : (S ∩ E).card = 0 <;> simp [h]

omit [DecidableEq ι] in
theorem avoidDist_smul {c : ℝ} (hc : c ≠ 0) (w : Finset ι → ℝ) (E : Finset ι) :
    avoidDist (fun S => c * w S) E = avoidDist w E := by
  classical
  funext S
  rw [avoidDist, avoidDist, avoidWeight_smul, totalMass_smul]
  rcases eq_or_ne (totalMass (avoidWeight w E)) 0 with h0 | h0
  · rw [h0, mul_zero, div_zero, div_zero]
  · rw [mul_div_mul_left _ _ hc]

omit [DecidableEq ι] in
/-- `faceDist` is the face weight rescaled, so any normalized conditioning
applied to it agrees with the one applied to the raw face. -/
theorem avoidDist_faceDist {w : Finset ι → ℝ} {cst : ι → ℕ} {m : ℕ}
    (hmass : totalMass (faceWeight w cst m) ≠ 0) (E : Finset ι) :
    avoidDist (faceDist w cst m) E = avoidDist (faceWeight w cst m) E := by
  have heq : faceDist w cst m
      = fun S => (totalMass (faceWeight w cst m))⁻¹ * faceWeight w cst m S := by
    funext S
    rw [faceDist, div_eq_inv_mul]
  rw [heq, avoidDist_smul (inv_ne_zero hmass)]

/-- **The normalized present/avoid restriction, once.** -/
theorem avoidDist_presentWeight_comm (w : Finset ι → ℝ) (F E : Finset ι) :
    avoidDist (presentWeight w F) E = faceDist (avoidWeight w E) (indicatorCost F) 1 := by
  classical
  funext S
  rw [avoidDist, faceDist, present_avoid_comm, presentWeight]

omit [Fintype ι] [DecidableEq ι] in
theorem faceWeight_smul (c : ℝ) (w : Finset ι → ℝ) (cst : ι → ℕ) (m : ℕ) :
    faceWeight (fun S => c * w S) cst m = fun S => c * faceWeight w cst m S := by
  funext S
  rw [faceWeight, faceWeight]
  split_ifs
  · rfl
  · rw [mul_zero]

omit [DecidableEq ι] in
theorem faceDist_smul {c : ℝ} (hc : c ≠ 0) (w : Finset ι → ℝ) (cst : ι → ℕ)
    (m : ℕ) : faceDist (fun S => c * w S) cst m = faceDist w cst m := by
  classical
  funext S
  rw [faceDist, faceDist, faceWeight_smul, totalMass_smul]
  rcases eq_or_ne (totalMass (faceWeight w cst m)) 0 with h0 | h0
  · rw [h0, mul_zero, div_zero, div_zero]
  · rw [mul_div_mul_left _ _ hc]

/-- **Avoiding `E` and presenting `F` commute at the normalized level**: the
`E`-avoided present law is the present face of the `E`-avoided law. -/
theorem avoidDist_presentDist_comm {w : Finset ι → ℝ} {F E : Finset ι}
    (hface : totalMass (faceWeight w (indicatorCost F) 1) ≠ 0)
    (havoid : totalMass (avoidWeight w E) ≠ 0) :
    avoidDist (faceDist w (indicatorCost F) 1) E
      = faceDist (avoidDist w E) (indicatorCost F) 1 := by
  have hsplit : avoidDist w E
      = fun S => (totalMass (avoidWeight w E))⁻¹ * avoidWeight w E S := by
    funext S
    rw [avoidDist, div_eq_inv_mul]
  rw [avoidDist_faceDist hface E, hsplit, faceDist_smul (inv_ne_zero havoid),
    ← presentWeight, avoidDist_presentWeight_comm]

end Normalize

end TSPGap

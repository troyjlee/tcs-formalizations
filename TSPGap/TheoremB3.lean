/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OJoin
import TSPGap.NearCycle
import TSPGap.PolygonOneSideExistence

/-!
# KKO22 Theorem B.3: the payment at a cut

Theorem B.3 is the hierarchy's payment, and `Theorem61.lean` derives
`exists_slack_pair` (Theorem 6.1) from it.  Its own proof is a case analysis
over five kinds of near-minimum cut; this file carries all of it except the
construction of the hierarchy itself.

Three of KKO's five types — 2, 4 and 5 — end in the *same* inequality.  A
slack vector bounded below by `−βxₑ` loses at most `(2+η)β` across a
near-minimum cut, so a cut is settled as soon as `s*` pays `(2+η)β` on it
(`payment_of_pay`); and KKO choose `α = (2+η)β/(1 − ε)` in each of the two
theorems producing `s*` precisely so that their payment `α(1 − ε)` comes to
that figure.  Instantiated at that scaling, Theorem 5.2 (`exists_slackStar_
bothSides`) and Appendix A (`exists_slackStar_oneSide`) therefore deliver the
*same* bound, and the difference between the types is only which cuts each of
them covers.  Type 3 is the trivial `payment_of_nonneg`.

## What this file now carries

* **Definition B.1**, the `Hierarchy`, whose near-cycle cuts are witnessed by a
  `NearCycle` rooted at the cut's complement (`Hierarchy.Presents`).
* **The parent calculus.**  Definition B.1 defines both parents canonically as
  smallest containers, so the hierarchy stores neither: `IsChildOf H.cuts S S'`
  is `p(S) = S'`, and `Hierarchy.IsEdgeParent` is `p(e)`, with existence,
  uniqueness, and the two ways the development ever identifies one — between
  two children (`isEdgeParent_of_between_children`) and at the side edges of a
  nested cut (`Presents.isEdgeParent_of_mem_sideEdges`).
* **Theorem B.2** stated exactly (`IsMainPayment`), all five properties phrased
  through that calculus; it is proved downstream, in `MainPaymentExistence.lean`
  (`exists_mainPayment`), from §5–§7.
* **Type 4 complete at one cut** (`payment_of_leftmost`, `payment_of_rightmost`):
  the split `δ(S) = A ⊍ D ⊍ F`, the mass `x(F) ≥ 1 − ε/2`, the edge parents of
  `F`, and B.2's near-cycle inequality, assembled.
* **The construction** (`OneSideFamily`, `IsHierarchyOf`): Facts B.4 and B.5 in
  the clauses Theorem B.3 consumes, and the **component-to-near-cycle
  correspondence** (`Hierarchy.presents_of_atoms`) that identifies Appendix A's
  near-cycle for a component with Definition B.1's near-cycle cut of the
  hierarchy.  `OneSideFamily.exists_slackStar_of_index` delivers both at once,
  over one and the same near-cycle.
* **Appendix A globally** (`OneSideFamily.exists_slackStar_global`): the
  per-component vectors summed at no extra per-edge cost, their disjointness
  read off the parent calculus.
* **Type 5** (`exists_slackStar_triangle`): Lemma A.13 at KKO's scaling, over
  the same interface — a triangle is a near-cycle with `k = 0`.
* **The classification** (`OneSideFamily.IsHierarchyOf.classify`) and the
  payment it feeds (`payment_of_interval`, `payment_of_nearCycleCut`,
  `payment_of_hierarchy`).  Types 4 and 5 turn out to be one lemma: both are
  cuts that are intervals of a near-cycle presenting a hierarchy cut, and the
  three branches do not care where the near-cycle came from.

* **Theorem B.3 itself** (`exists_payment_of_hierarchy`), from a hierarchy and
  the Main Payment Theorem.

What remains is plumbing, not mathematics: building the hierarchy from the two
structural boxes, enlarging the constant of `OJoin.exists_payment_hierarchy`
from `125ηβ` to `600ηβ` with `EndToEnd.kkoEta` shrunk to match, and moving
Theorem 6.1's derivation below this file, which imports `OJoin`.  That is
`Theorem61.lean`, where the hierarchy is built and Theorem B.2 invoked.

⚠️ The constant: `s*` is the sum of two vectors, so its cost is the sum of
theirs.  KKO get `(18 + 44)η`'s worth; Appendix A here proves `4(8ε_η + ε_η)`
rather than `44η` (see the entry in `notes.md`), so Theorem B.3 costs `600ηβxₑ`
in place of KKO's `125ηβxₑ`.  `EndToEnd.lean` absorbs the difference: `η` drops
to `ε_P/3600`, and `β` is taken at KKO's own `η/(4 + 2η)` — though at the
repaired `ε_P` the rational `η/5` would serve too.  ⚠️ The gap constant itself is
`10⁻⁴¹`, not `10⁻³⁶` — but that is `ε_P`'s doing, not Theorem B.3's: see
`epsP`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {η β : ℝ}

/-- **The payment inequality of KKO's Types 2, 4 and 5.**  A slack vector
never below `−βxₑ` loses at most `(2+η)β` across a near-minimum cut, so any
nonnegative vector paying that much on the cut settles it. -/
theorem payment_of_pay {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {S : Finset (Fin n)} {s s' : Sym2 (Fin n) → ℝ}
    (hβ0 : 0 ≤ β) (hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e)
    (hs : ∀ e, -(β * e₀.restrict x₀ e) ≤ s e)
    (hcut : ∑ e ∈ cutEdges S, e₀.restrict x₀ e ≤ 2 + η)
    (hpay : (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' e) :
    0 ≤ ∑ e ∈ cutEdges S, (s e + s' e) := by
  have hlow : ∑ e ∈ cutEdges S, -(β * e₀.restrict x₀ e) ≤ ∑ e ∈ cutEdges S, s e :=
    Finset.sum_le_sum fun e _ => hs e
  have hneg : ∑ e ∈ cutEdges S, -(β * e₀.restrict x₀ e)
      = -(β * ∑ e ∈ cutEdges S, e₀.restrict x₀ e) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  have hβcut : β * ∑ e ∈ cutEdges S, e₀.restrict x₀ e ≤ β * (2 + η) :=
    mul_le_mul_of_nonneg_left hcut hβ0
  rw [Finset.sum_add_distrib]
  rw [hneg] at hlow
  nlinarith

/-- **KKO's Type 3.**  A cut on which the hierarchy's own vector is already
nonnegative needs no help from `s*`. -/
theorem payment_of_nonneg {S : Finset (Fin n)} {s s' : Sym2 (Fin n) → ℝ}
    (hs : 0 ≤ ∑ e ∈ cutEdges S, s e) (hs' : ∀ e, 0 ≤ s' e) :
    0 ≤ ∑ e ∈ cutEdges S, (s e + s' e) := by
  have : 0 ≤ ∑ e ∈ cutEdges S, s' e := Finset.sum_nonneg fun e _ => hs' e
  rw [Finset.sum_add_distrib]
  linarith

/-- The scaling that makes a payment of `α(1 − ε)` come to exactly `(2+η)β`:
KKO's `α = (2+η)β/(1 − ε_η)`. -/
theorem alpha_mul_one_sub {ε : ℝ} (hε : ε ≠ 1) :
    ((2 + η) * β / (1 - ε)) * (1 - ε) = (2 + η) * β :=
  div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hε))

/-- **Theorem 5.2 at KKO's scaling.**  On a cut crossed on both sides the
vector of Theorem 5.2 pays exactly what Type 2 needs. -/
theorem exists_slackStar_bothSides {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (hη0 : 0 < η) (hη : η < 1 / 10) (hβ0 : 0 ≤ β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → CrossedBothSides e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ 18 * ((2 + η) * β / (1 - η)) * η * e₀.restrict x₀ e) := by
  have hαnn : 0 ≤ (2 + η) * β / (1 - η) := by
    refine div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  obtain ⟨s', hs'nn, hs'pay, hs'exp⟩ :=
    exists_slack_vector_of_subtourLP (α := (2 + η) * β / (1 - η)) (η := η) e₀ hx₀ μ
      hαnn hη0 hη
  refine ⟨s', hs'nn, fun S T hS hboth hodd => ?_, hs'exp⟩
  have h := hs'pay S T hS hboth hodd
  rwa [alpha_mul_one_sub (by linarith : η ≠ 1)] at h

/-- **Appendix A at KKO's scaling.**  On the relevant cuts of a component of
`N_{η,≤1}` the happy-polygon vector pays exactly what Types 4 and 5 need — the
same `(2+η)β` as Theorem 5.2 pays on Type 2. -/
theorem exists_slackStar_oneSide {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : PolygonRep 𝒞) (hcomp : IsOneSideComponent e₀ x₀ η 𝒞)
    (hroot : P.rootAtom = atomOf 𝒞 e₀.u₀)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom ∧ cutSum x₀ A ≤ 2 + η)
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      N.root = P.rootAtom ∧
      (∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
        ↔ A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S ∈ 𝒞 ∪ 𝒜, ∃ i j : Fin (N.k + 3), N.interval i j = S ∧
        0 < i ∧ i ≤ j ∧ ¬ (i = 1 ∧ j = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (i = 1 → N.LeftHappy T) → (j = N.lastIdx → N.RightHappy T) →
          (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + η))
            * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s' T e = 0) := by
  have hαnn : 0 ≤ (2 + η) * β / (1 - 7 * η) :=
    div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  obtain ⟨N, s', hNroot, hNatom, hs'nn, hs'pay, hs'exp, hs'supp⟩ :=
    exists_happySlack_of_oneSideComponent (α := (2 + η) * β / (1 - 7 * η))
      hx₀ μ P hcomp hroot 𝒜 h𝒜 hαnn hη0 hη
  refine ⟨N, s', hNroot, hNatom, hs'nn, fun S hS => ?_, hs'exp, hs'supp⟩
  obtain ⟨i, j, hij, hp1, hp2, hp3, hpay⟩ := hs'pay S hS
  refine ⟨i, j, hij, hp1, hp2, hp3, fun T hodd hL hR => ?_⟩
  have h := hpay T hodd hL hR
  rwa [alpha_mul_one_sub (by linarith : (7 : ℝ) * η ≠ 1)] at h

theorem fin_one_ne_zero {k : ℕ} : (1 : Fin (k + 3)) ≠ 0 := by
  intro hc
  have hv := congrArg Fin.val hc
  have h1 : ((1 : Fin (k + 3)) : ℕ) = 1 := rfl
  rw [h1] at hv
  simp at hv

/-! ### Definition A.4 is a partition, and Definition B.1

The `A, B, C` of a near-cycle partition the edges at its root atom — which is
what makes them Definition B.1's partition of the edges leaving a near-cycle
*cut*, the two being complementary sides of the same cut. -/

variable {x : Sym2 (Fin n) → ℝ} {ε : ℝ}

namespace NearCycle

variable (P : NearCycle x ε)

theorem lastIdx_ne_zero : P.lastIdx ≠ 0 := by
  rw [lastIdx]
  intro hc
  have hv := congrArg Fin.val hc
  simp only [Fin.val_last, Fin.val_zero] at hv
  omega

theorem partA_subset_cutEdges_root : P.partA ⊆ cutEdges P.root := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  refine mem_cutEdges_iff'.mpr ⟨u, hu, v, Finset.mem_compl.mpr ?_, rfl⟩
  intro hc
  exact (Finset.disjoint_left.mp (P.atom_disjoint _ _ (by simp)) hv) hc

theorem partB_subset_cutEdges_root : P.partB ⊆ cutEdges P.root := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  have hlast : P.atom (P.lastIdx + 1) = P.root := by
    rw [root]; congr 1; simp [lastIdx]
  rw [hlast] at hv
  refine mem_cutEdges_iff'.mpr ⟨v, hv, u, Finset.mem_compl.mpr ?_, Sym2.eq_swap⟩
  intro hc
  exact (Finset.disjoint_left.mp (P.atom_disjoint _ _ (P.lastIdx_ne_zero)) hu) hc

theorem partA_disjoint_partB : Disjoint P.partA P.partB :=
  P.group_disjoint (Ne.symm P.lastIdx_ne_zero)

/-- **Definition A.4 is a partition.**  The edges leaving the root split into
`A`, `B` and `C`, and `A` and `B` are disjoint. -/
theorem partA_union_partB_union_partC :
    P.partA ∪ P.partB ∪ P.partC = cutEdges P.root := by
  rw [partC]
  rw [Finset.union_sdiff_of_subset]
  exact Finset.union_subset P.partA_subset_cutEdges_root P.partB_subset_cutEdges_root

/-! #### The edges a cut keeps inside the near-cycle

KKO's Type 4 needs two bounds on a cut `S` nested inside the outer cut `S'` of
a near-cycle: the edges `F = δ(S) ∖ δ(S')` staying inside carry nearly a unit,
and what leaves towards the root is correspondingly small (their Lemma 2.10).

There are two ways to get them.  The *coarse* one, below, reads them off the
group at the cut's far end, and so pays the near-cycle's own `ε` — which is
looser than the paper's figure, since Theorem A.3 bundles the adjacent-atom
mass together with everything else.  The *exact* one, further down, does not
look at the near-cycle at all: the two edge sets are `E(S, S' ∖ S)` and
`E(S, S'ᶜ)`, so KKO21 Lemma 2.7 on nested near-minimum cuts applies directly
and gives the paper's constants.  Type 4 uses the exact bounds. -/

/-- A **coarse** lower bound on `F`, through the group at the cut's far end:
`1 − ε` where the near-cycle's `ε` bundles several facts.  The exact bound is
`one_sub_half_le_sum_sideEdges`. -/
theorem one_sub_le_sum_sideEdges_left {j : Fin (P.k + 3)} (hx : ∀ e, 0 ≤ x e)
    (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j ≤ P.lastIdx) (h2 : j ≠ P.lastIdx) :
    1 - ε ≤ ∑ e ∈ P.sideEdges (P.interval 1 j), x e := by
  have hone : (0 : Fin (P.k + 3)) < 1 := by simp [Fin.lt_def]
  have hj0 : j ≠ 0 := ne_of_gt (lt_of_lt_of_le hone h1j)
  have hgS : P.group j ⊆ cutEdges (P.interval 1 j) :=
    P.group_subset_cutEdges_of_boundary h1j hone hj (Or.inr rfl)
  have hgU : Disjoint (P.group j) (P.upEdges (P.interval 1 j)) :=
    P.group_disjoint_upEdges hj0 (P.add_one_ne_zero' h2) _
  have hgside : P.group j ⊆ P.sideEdges (P.interval 1 j) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hgS he, fun hc => (Finset.disjoint_left.mp hgU he) hc⟩
  refine le_trans (P.one_sub_le_group_mass j) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hgside (fun e _ _ => hx e)

/-- A **coarse** version of Lemma 2.10, through the same group: what leaves
towards the root is everything but the far group.  The exact bound is
`sum_upEdges_le_one_add`. -/
theorem sum_upEdges_le_left {j : Fin (P.k + 3)} (hx : ∀ e, 0 ≤ x e)
    (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j ≤ P.lastIdx) (h2 : j ≠ P.lastIdx)
    {d : ℝ} (hnm : cutSum x (P.interval 1 j) ≤ 2 + d) :
    ∑ e ∈ P.upEdges (P.interval 1 j), x e ≤ 1 + d + ε := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp [Finset.mem_Icc]
  have hside := P.one_sub_le_sum_sideEdges_left hx h1j hj h2
  have hsplit := Finset.sum_sdiff (f := x)
    (P.upEdges_subset_cutEdges (P.interval_disjoint_atom h0))
  have hc : ∑ e ∈ cutEdges (P.interval 1 j), x e = cutSum x (P.interval 1 j) := rfl
  rw [hc] at hsplit
  have hs : P.sideEdges (P.interval 1 j)
      = cutEdges (P.interval 1 j) \ P.upEdges (P.interval 1 j) := rfl
  rw [hs] at hside
  linarith

/-- The **outer cut** of a near-cycle: the union of its non-root atoms, the
complement of the root atom.  This is the cut that Definition B.1 calls a
near-cycle cut. -/
def outerCut : Finset (Fin n) := P.rootᶜ

theorem interval_subset_outerCut {i j : Fin (P.k + 3)}
    (h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i j) :
    P.interval i j ⊆ P.outerCut := by
  intro v hv
  rw [outerCut, Finset.mem_compl, root]
  intro hc
  exact (P.notMem_interval h0 hc) hv

/-- An interval missing some non-root atom leaves room in the outer cut.  This
is the properness that KKO21 Lemma 2.7 needs of the nested pair `S ⊂ S'`, and
it is why a leftmost cut of a near-cycle is never the whole outer cut. -/
theorem nonempty_outerCut_sdiff_interval {i j t : Fin (P.k + 3)} (ht0 : t ≠ 0)
    (ht : t ∉ Finset.Icc i j) : (P.outerCut \ P.interval i j).Nonempty := by
  obtain ⟨v, hv⟩ := P.atom_nonempty t
  refine ⟨v, Finset.mem_sdiff.mpr ⟨?_, P.notMem_interval ht hv⟩⟩
  rw [outerCut, Finset.mem_compl, root]
  exact fun hc => (Finset.disjoint_left.mp (P.atom_disjoint t 0 ht0) hv) hc

/-- **A proper interval leaves room in the outer cut.**  It misses `a₁` if it
does not start there, and `a_{m-1}` if it does not end there — and Theorem
A.12's relevant cuts never do both, which is what `hproper` says. -/
theorem nonempty_outerCut_sdiff_of_proper {a b : Fin (P.k + 3)} (h1 : 0 < a)
    (hb : b ≤ P.lastIdx) (hproper : ¬ (a = 1 ∧ b = P.lastIdx)) :
    (P.outerCut \ P.interval a b).Nonempty := by
  rcases eq_or_ne a 1 with rfl | hane
  · refine P.nonempty_outerCut_sdiff_interval P.lastIdx_ne_zero ?_
    rw [Finset.mem_Icc]
    rintro ⟨-, h2⟩
    exact hproper ⟨rfl, le_antisymm hb h2⟩
  · have h1a : (1 : Fin (P.k + 3)) < a :=
      lt_of_le_of_ne (one_le_of_pos h1) (Ne.symm hane)
    refine P.nonempty_outerCut_sdiff_interval fin_one_ne_zero ?_
    rw [Finset.mem_Icc]
    rintro ⟨h2, -⟩
    exact absurd h2 (not_le.mpr h1a)

/-- **The side edges of a nested cut are the edges to the rest of the outer
cut.**  An edge leaving `S` either goes to the root atom — those are the
`upEdges` — or stays inside the outer cut. -/
theorem sideEdges_eq_betweenEdges {S : Finset (Fin n)} (hS : S ⊆ P.outerCut) :
    P.sideEdges S = betweenEdges S (P.outerCut \ S) := by
  ext e
  rw [sideEdges, Finset.mem_sdiff, mem_betweenEdges_iff']
  constructor
  · rintro ⟨hcut, hup⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_cutEdges_iff'.mp hcut
    refine ⟨u, hu, v, Finset.mem_sdiff.mpr ⟨?_, Finset.mem_compl.mp hv⟩, rfl⟩
    rw [outerCut, Finset.mem_compl]
    intro hvroot
    exact hup (mem_betweenEdges_iff'.mpr ⟨u, hu, v, hvroot, rfl⟩)
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨hvouter, hvS⟩ := Finset.mem_sdiff.mp hv
    refine ⟨mem_cutEdges_iff'.mpr ⟨u, hu, v, Finset.mem_compl.mpr hvS, rfl⟩, ?_⟩
    intro hmem
    obtain ⟨a, ha, b, hb, heq⟩ := mem_betweenEdges_iff'.mp hmem
    rw [outerCut, Finset.mem_compl] at hvouter
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hvouter hb
    · exact (Finset.mem_compl.mp (hS hu)) hb

/-- The endpoints of `e₀` lie in the root atom: the atoms cover the vertices,
and every other atom avoids them. -/
theorem mem_root_of_avoids {e₀ : RootEdge n}
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t)) :
    e₀.u₀ ∈ P.root ∧ e₀.v₀ ∈ P.root := by
  constructor
  · obtain ⟨t, ht⟩ := P.atom_cover e₀.u₀
    rcases eq_or_ne t 0 with rfl | hne
    · exact ht
    · exact absurd ht (havoid t hne).1
  · obtain ⟨t, ht⟩ := P.atom_cover e₀.v₀
    rcases eq_or_ne t 0 with rfl | hne
    · exact ht
    · exact absurd ht (havoid t hne).2

theorem avoidsRootEdge_of_subset_outerCut {e₀ : RootEdge n}
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {S : Finset (Fin n)} (hS : S ⊆ P.outerCut) : AvoidsRootEdge e₀ S := by
  obtain ⟨hu, hv⟩ := P.mem_root_of_avoids havoid
  constructor
  · intro hc
    exact (Finset.mem_compl.mp (hS hc)) hu
  · intro hc
    exact (Finset.mem_compl.mp (hS hc)) hv

/-- The outer cut is an `ε`-near minimum cut: it is the complement of the root
atom, whose degree Theorem A.3 bounds. -/
theorem isNearMinCut_outerCut {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    (hne : P.outerCut.Nonempty) : IsNearMinCut x₀ ε P.outerCut := by
  obtain ⟨hu, hv⟩ := P.mem_root_of_avoids havoid
  have havoidOuter : AvoidsRootEdge e₀ P.outerCut :=
    P.avoidsRootEdge_of_subset_outerCut havoid (Finset.Subset.refl _)
  refine ⟨hne, fun h => havoidOuter.1 (by rw [h]; exact Finset.mem_univ _), ?_⟩
  rw [← cutSum_restrict havoidOuter, outerCut, cutSum_compl]
  exact P.atom_cut_le 0

/-! #### Definition B.1's split of an extremal cut

Type 4 at an unhappy near-cycle needs the leftmost cut's edges written as
`δ(S) = A ⊍ D ⊍ F` with `D ⊆ C`, which is what the Main Payment Theorem's
inequality `s(A) + s(F) + s⁻(C) ≥ 0` is designed to consume.  The three parts
are read off the near-cycle directly: `A` is its own `A` (a leftmost cut
contains it), `F = sideEdges S` is what stays inside the outer cut, and `D` is
whatever else goes up to the root — which can only be `C`, since `B` does not
reach a cut that misses the last atom. -/

/-- What a leftmost cut sends to the root beyond `A` lies in `C`: `A`, `B` and
`C` exhaust `δ(a₀)`, and `B` cannot meet a cut missing `a_{m-1}`. -/
theorem upEdges_sdiff_partA_subset_partC {j : Fin (P.k + 3)}
    (hj : j < P.lastIdx) :
    P.upEdges (P.interval 1 j) \ P.partA ⊆ P.partC := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp [Finset.mem_Icc]
  have hl : P.lastIdx ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _
    exact hj
  intro e he
  obtain ⟨heU, heA⟩ := Finset.mem_sdiff.mp he
  refine Finset.mem_sdiff.mpr ⟨P.upEdges_subset_cutEdges_root
    (P.interval_disjoint_atom h0) heU, ?_⟩
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact heA h
  · exact (Finset.disjoint_left.mp (P.upEdges_disjoint_partB h0 hl) heU) h

/-- The mirror at a rightmost cut. -/
theorem upEdges_sdiff_partB_subset_partC {i : Fin (P.k + 3)}
    (h1i : (1 : Fin (P.k + 3)) < i) :
    P.upEdges (P.interval i P.lastIdx) \ P.partB ⊆ P.partC := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr (lt_trans (by simp) h1i))
  have h1 : (1 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr h1i)
  intro e he
  obtain ⟨heU, heB⟩ := Finset.mem_sdiff.mp he
  refine Finset.mem_sdiff.mpr ⟨P.upEdges_subset_cutEdges_root
    (P.interval_disjoint_atom h0) heU, ?_⟩
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact (Finset.disjoint_left.mp (P.upEdges_disjoint_partA h0 h1) heU) h
  · exact heB h

/-- **The leftmost split**, `δ(S) = A ⊍ D ⊍ F` with `D ⊆ C`, in exactly the
shape `payment_of_negPart` consumes. -/
theorem exists_split_left {j : Fin (P.k + 3)}
    (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j < P.lastIdx) :
    ∃ D : Finset (Sym2 (Fin n)),
      cutEdges (P.interval 1 j) = P.partA ∪ D ∪ P.sideEdges (P.interval 1 j) ∧
      Disjoint P.partA D ∧
      Disjoint (P.partA ∪ D) (P.sideEdges (P.interval 1 j)) ∧
      D ⊆ P.partC := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp [Finset.mem_Icc]
  have hA : P.partA ⊆ P.upEdges (P.interval 1 j) :=
    P.partA_subset_upEdges (by simp [Finset.mem_Icc, h1j])
  refine ⟨P.upEdges (P.interval 1 j) \ P.partA, ?_, Finset.disjoint_sdiff, ?_,
    P.upEdges_sdiff_partA_subset_partC hj⟩
  · rw [Finset.union_sdiff_of_subset hA, sideEdges]
    exact (Finset.union_sdiff_of_subset
      (P.upEdges_subset_cutEdges (P.interval_disjoint_atom h0))).symm
  · rw [Finset.union_sdiff_of_subset hA, sideEdges]
    exact Finset.disjoint_sdiff

/-- **The rightmost split**, with `B` in place of `A`. -/
theorem exists_split_right {i : Fin (P.k + 3)}
    (h1i : (1 : Fin (P.k + 3)) < i) (hi : i ≤ P.lastIdx) :
    ∃ D : Finset (Sym2 (Fin n)),
      cutEdges (P.interval i P.lastIdx)
          = P.partB ∪ D ∪ P.sideEdges (P.interval i P.lastIdx) ∧
      Disjoint P.partB D ∧
      Disjoint (P.partB ∪ D) (P.sideEdges (P.interval i P.lastIdx)) ∧
      D ⊆ P.partC := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr (lt_trans (by simp) h1i))
  have hB : P.partB ⊆ P.upEdges (P.interval i P.lastIdx) :=
    P.partB_subset_upEdges (by simp [Finset.mem_Icc, hi])
  refine ⟨P.upEdges (P.interval i P.lastIdx) \ P.partB, ?_, Finset.disjoint_sdiff, ?_,
    P.upEdges_sdiff_partB_subset_partC h1i⟩
  · rw [Finset.union_sdiff_of_subset hB, sideEdges]
    exact (Finset.union_sdiff_of_subset
      (P.upEdges_subset_cutEdges (P.interval_disjoint_atom h0))).symm
  · rw [Finset.union_sdiff_of_subset hB, sideEdges]
    exact Finset.disjoint_sdiff

/-! #### The exact bounds, from Lemma 2.7 on nested cuts

Two layers meet here, and they should not be confused.  The *core* of each
bound is KKO21 Lemma 2.7 on a nested pair of near-minimum cuts `S ⊆ S'` —
`le_pairSum_of_subset` and `pairSum_le_of_subset` — and it knows nothing of
near-cycles: only that the two cuts are near-minimum and nested.  What the
wrappers below add is *convenience*: they take `S'` to be the outer cut of a
near-cycle and obtain its near-minimality from `P.atom_cut_le 0`, the root
atom's degree bound, via `isNearMinCut_outerCut`.  So the constants are the
paper's for reasons independent of Theorem A.3; the near-cycle enters only to
supply the outer cut's own `ε`. -/

variable {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}

/-- **KKO22's `x(F) ≥ 1 − ε_{S'}/2`.**  The edges a nested cut keeps inside
the outer cut are `E(S, S' ∖ S)`, so KKO21 Lemma 2.7's lower bound applies
directly — no property of the near-cycle beyond `S ⊆ S'` is used, and the
constant is the paper's. -/
theorem one_sub_half_le_sum_sideEdges (hx₀ : x₀ ∈ subtourLP n)
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {S : Finset (Fin n)} {d : ℝ} (hSsub : S ⊆ P.outerCut)
    (hS : IsNearMinCut x₀ d S) (hne : (P.outerCut \ S).Nonempty) :
    1 - ε / 2 ≤ ∑ e ∈ P.sideEdges S, e₀.restrict x₀ e := by
  have hSavoid : AvoidsRootEdge e₀ S := P.avoidsRootEdge_of_subset_outerCut havoid hSsub
  have houter : IsNearMinCut x₀ ε P.outerCut :=
    P.isNearMinCut_outerCut havoid (hS.nonempty.mono hSsub)
  have hd : Disjoint S (P.outerCut \ S) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 => (Finset.mem_sdiff.mp hv2).2 hv1
  have hbridge : ∑ e ∈ P.sideEdges S, e₀.restrict x₀ e
      = ∑ e ∈ P.sideEdges S, x₀ e := by
    refine RootEdge.sum_restrict_of_notMem fun hc => ?_
    exact (RootEdge.edge_notMem_cutEdges hSavoid) (Finset.mem_sdiff.mp hc).1
  rw [hbridge, P.sideEdges_eq_betweenEdges hSsub, sum_betweenEdges x₀ hd]
  exact le_pairSum_of_subset hx₀ hS houter hSsub hne

/-- **KKO22 Lemma 2.10.**  What a nested cut sends to the root atom is
`E(S, S'ᶜ)`, so KKO21 Lemma 2.7's upper bound applies — again with the
paper's constant, and again using nothing about the near-cycle. -/
theorem sum_upEdges_le_one_add (hx₀ : x₀ ∈ subtourLP n)
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {S : Finset (Fin n)} {d : ℝ} (hSsub : S ⊆ P.outerCut)
    (hS : IsNearMinCut x₀ d S) (hne : (P.outerCut \ S).Nonempty) :
    ∑ e ∈ P.upEdges S, e₀.restrict x₀ e ≤ 1 + (d + ε) / 2 := by
  have hSavoid : AvoidsRootEdge e₀ S := P.avoidsRootEdge_of_subset_outerCut havoid hSsub
  have houter : IsNearMinCut x₀ ε P.outerCut :=
    P.isNearMinCut_outerCut havoid (hS.nonempty.mono hSsub)
  have hd : Disjoint S P.outerCutᶜ :=
    Finset.disjoint_left.mpr fun v hv1 hv2 => (Finset.mem_compl.mp hv2) (hSsub hv1)
  have hup : P.upEdges S = betweenEdges S P.outerCutᶜ := by
    rw [upEdges, outerCut, compl_compl]
  have hdisjSroot : Disjoint S P.root :=
    Finset.disjoint_left.mpr fun v hv1 hv2 => (Finset.mem_compl.mp (hSsub hv1)) hv2
  have hbridge : ∑ e ∈ P.upEdges S, e₀.restrict x₀ e
      = ∑ e ∈ P.upEdges S, x₀ e := by
    refine RootEdge.sum_restrict_of_notMem fun hc => ?_
    exact (RootEdge.edge_notMem_cutEdges hSavoid)
      (P.upEdges_subset_cutEdges hdisjSroot hc)
  rw [hbridge, hup, sum_betweenEdges x₀ hd]
  exact pairSum_le_of_subset hx₀ hS houter hSsub hne

end NearCycle

/-! ### Definition B.1: the hierarchy -/

/-- `a` is a **child** of `S` in the family `𝒮`: a maximal proper subcut.

This is Definition B.1's `p(a) = S` read from below: `S` is the smallest cut
of the family properly containing `a` exactly when `a` is one of its maximal
proper subcuts, so the hierarchy stores no parent function. -/
def IsChildOf (𝒮 : Finset (Finset (Fin n))) (a S : Finset (Fin n)) : Prop :=
  a ∈ 𝒮 ∧ S ∈ 𝒮 ∧ a ⊂ S ∧ ∀ b ∈ 𝒮, a ⊂ b → ¬ b ⊂ S

/-- An edge lies **inside** a vertex set when both of its endpoints do. -/
def EdgeInside (e : Sym2 (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ e, v ∈ S

theorem edgeInside_iff {u v : Fin n} {S : Finset (Fin n)} :
    EdgeInside s(u, v) S ↔ u ∈ S ∧ v ∈ S := by
  refine ⟨fun h => ⟨h u (Sym2.mem_mk_left u v), h v (Sym2.mem_mk_right u v)⟩, ?_⟩
  rintro ⟨hu, hv⟩ w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact hu
  · exact hv

theorem EdgeInside.mono {e : Sym2 (Fin n)} {S T : Finset (Fin n)}
    (h : EdgeInside e S) (hST : S ⊆ T) : EdgeInside e T := fun v hv => hST (h v hv)

/-- Two sets both containing an edge share a vertex, so they are not disjoint.
This is what makes the containers of an edge in a laminar family a *chain*,
and hence what makes the smallest one smallest for `⊆`. -/
theorem EdgeInside.not_disjoint {e : Sym2 (Fin n)} {S R : Finset (Fin n)}
    (hS : EdgeInside e S) (hR : EdgeInside e R) : ¬ Disjoint S R := by
  revert hS hR
  induction e using Sym2.ind with
  | _ u v =>
    intro hS hR hd
    exact Finset.disjoint_left.mp hd (hS u (Sym2.mem_mk_left u v))
      (hR u (Sym2.mem_mk_left u v))

/-- An edge between two subsets of `S` lies inside `S`. -/
theorem edgeInside_of_mem_betweenEdges {A B S : Finset (Fin n)} (hA : A ⊆ S)
    (hB : B ⊆ S) {e : Sym2 (Fin n)} (he : e ∈ betweenEdges A B) :
    EdgeInside e S := by
  obtain ⟨u, hu, v, hv, rfl⟩ := NearCycle.mem_betweenEdges_iff'.mp he
  exact edgeInside_iff.mpr ⟨hA hu, hB hv⟩

/-- The root of every hierarchy over `e₀`: `V ∖ {u₀, v₀}`, the vertex set of
the contracted graph `G/e₀`. -/
def RootEdge.rootCut (e₀ : RootEdge n) : Finset (Fin n) :=
  ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ

/-- **KKO22 Definition B.1: a hierarchy.**  A laminar family of `ε`-near
minimum cuts, rooted at `V ∖ {u₀, v₀}`, in which every cut is the union of its
children and is classified as a *near-cycle* cut or a *degree* cut.

A near-cycle cut is exactly the outer cut of a `NearCycle` whose non-root
atoms are its children: the near-cycle's root atom is the complement, so its
`A`, `B`, `C` are Definition B.1's partition of the cut's edges and its
happiness is Definition B.1's. -/
structure Hierarchy (x : Sym2 (Fin n) → ℝ) (e₀ : RootEdge n) (ε : ℝ) where
  /-- The cuts of the hierarchy. -/
  cuts : Finset (Finset (Fin n))
  nearMin : ∀ S ∈ cuts, IsNearMinCut x ε S
  avoids : ∀ S ∈ cuts, AvoidsRootEdge e₀ S
  laminar : ∀ A ∈ cuts, ∀ B ∈ cuts, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  /-- The root of the hierarchy is `V ∖ {u₀, v₀}`. -/
  root_mem : ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ ∈ cuts
  le_root : ∀ S ∈ cuts, S ⊆ ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ
  /-- Every cut is the union of its children — except the minimal ones, which
  have none. -/
  union_children : ∀ S ∈ cuts, ∀ v ∈ S,
    (∃ a, IsChildOf cuts a S ∧ v ∈ a) ∨ ∀ a, ¬ IsChildOf cuts a S
  /-- Which cuts are near-cycle cuts; the rest are degree cuts. -/
  IsNearCycleCut : Finset (Fin n) → Prop
  /-- A near-cycle cut is the outer cut of a near-cycle whose non-root atoms
  are its children. -/
  nearCycle_spec : ∀ S ∈ cuts, IsNearCycleCut S →
    ∃ N : NearCycle x ε, N.root = Sᶜ ∧
      ∀ a, IsChildOf cuts a S ↔ ∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = a

namespace Hierarchy

variable {e₀ : RootEdge n} (H : Hierarchy x e₀ ε)

theorem child_subset {a S : Finset (Fin n)} (h : IsChildOf H.cuts a S) : a ⊆ S :=
  h.2.2.1.1

/-- Two distinct children are disjoint: neither can sit inside the other
without contradicting maximality. -/
theorem children_disjoint {a b S : Finset (Fin n)} (ha : IsChildOf H.cuts a S)
    (hb : IsChildOf H.cuts b S) (hab : a ≠ b) : Disjoint a b := by
  rcases H.laminar a ha.1 b hb.1 with h | h | h
  · exact absurd (ha.2.2.2 b hb.1 (ssubset_of_subset_of_ne h hab) hb.2.2.1) not_false
  · exact absurd (hb.2.2.2 a ha.1 (ssubset_of_subset_of_ne h (Ne.symm hab)) ha.2.2.1)
      not_false
  · exact h

/-- **KKO22's degree rule** — the clause `Hierarchy` does not record.

KKO22 separate a hierarchy's cuts into three kinds: a cut with **at least three**
children that is not an outer polygon cut is a *degree cut*, one with exactly two
children is a *triangle cut*, and the rest are outer polygon cuts
([KKO22, 2105.10043v3, §3]: "If `S ∈ H` has at least three children and it is not
an outer polygon cut, call it a degree cut.  If it has exactly two children, call
it a triangle cut").

`Hierarchy` stores only the near-cycle/degree split, so the "at least three"
clause has to travel separately.  ⚠️ It is a genuine *hypothesis*, not a
consequence: nothing in `Hierarchy` rules out a non-near-cycle cut with exactly
two children, and on such a cut §7's top-edge argument and the Main Payment
Theorem both fail.  Every result that needs a degree cut to have three atoms must
therefore ask for this.

Stated as "three pairwise-distinct children exist" rather than
`3 ≤ (H.children S).card` only because `children` is defined downstream;
`Hierarchy.DegreeRule.three` converts to the cardinality form. -/
def DegreeRule : Prop :=
  ∀ S ∈ H.cuts, ¬ H.IsNearCycleCut S → (∃ a, IsChildOf H.cuts a S) →
    ∃ a b c, IsChildOf H.cuts a S ∧ IsChildOf H.cuts b S ∧ IsChildOf H.cuts c S ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- The near-cycle of a near-cycle cut has the cut's edges for its `δ(a₀)`. -/
theorem cutEdges_eq_of_nearCycle {S : Finset (Fin n)} {N : NearCycle x ε}
    (h : N.root = Sᶜ) : cutEdges S = cutEdges N.root := by
  rw [h, cutEdges_compl]

/-! #### The parent calculus

Definition B.1 defines both parents canonically as smallest containers, so the
hierarchy stores neither.  For cuts, `IsChildOf H.cuts S S'` already says
`p(S) = S'`.  For edges, KKO "abuse notation" and write `p(e)` for the smallest
cut of `H` containing both endpoints of `e`; that is `IsEdgeParent` below, and
laminarity makes "smallest" for `⊆` and "smallest" for cardinality — which is
the sense KKO's footnote picks — the same thing. -/

theorem rootCut_mem : e₀.rootCut ∈ H.cuts := H.root_mem

theorem subset_rootCut {S : Finset (Fin n)} (hS : S ∈ H.cuts) : S ⊆ e₀.rootCut :=
  H.le_root S hS

/-- **`p(S)` exists** for every cut but the root: the smallest cut properly
containing it.  The argument is the one for `p(e)` — a container of least
cardinality is a container of least inclusion — with the root cut in place of
the edge's ambient container. -/
theorem exists_isChildOf {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hne : S ≠ e₀.rootCut) : ∃ S', IsChildOf H.cuts S S' := by
  classical
  have hroot : S ⊂ e₀.rootCut := ssubset_of_subset_of_ne (H.subset_rootCut hS) hne
  obtain ⟨S', hS'mem, hmin⟩ := Finset.exists_min_image
    (H.cuts.filter fun R => S ⊂ R) Finset.card
    ⟨e₀.rootCut, Finset.mem_filter.mpr ⟨H.rootCut_mem, hroot⟩⟩
  obtain ⟨hS'cut, hS'ss⟩ := Finset.mem_filter.mp hS'mem
  refine ⟨S', hS, hS'cut, hS'ss, fun b hb hSb hbS' => ?_⟩
  exact absurd (Finset.card_lt_card hbS')
    (not_lt.mpr (hmin b (Finset.mem_filter.mpr ⟨hb, hSb⟩)))

/-- `p(S)` is well defined: two parents contain each other, and neither can be
a proper subcut of the other without contradicting the maximality of `S` as a
child. -/
theorem IsChildOf.unique {S S₁ S₂ : Finset (Fin n)}
    (h₁ : IsChildOf H.cuts S S₁) (h₂ : IsChildOf H.cuts S S₂) : S₁ = S₂ := by
  rcases H.laminar S₁ h₁.2.1 S₂ h₂.2.1 with h | h | h
  · rcases eq_or_ne S₁ S₂ with heq | hne
    · exact heq
    · exact absurd (ssubset_of_subset_of_ne h hne) (h₂.2.2.2 S₁ h₁.2.1 h₁.2.2.1)
  · rcases eq_or_ne S₂ S₁ with heq | hne
    · exact heq.symm
    · exact absurd (ssubset_of_subset_of_ne h hne) (h₁.2.2.2 S₂ h₂.2.1 h₂.2.2.1)
  · obtain ⟨v, hv⟩ := (H.nearMin S h₁.1).nonempty
    exact absurd (Finset.disjoint_left.mp h (h₁.2.2.1.1 hv) (h₂.2.2.1.1 hv)) not_false

open Classical in
/-- **A strict descendant lies inside a child.**  Among the cuts sitting
between `S'` and `S` pick one of *largest* cardinality: anything properly
containing it and still properly inside `S` would be larger still, so the
choice is a maximal proper subcut of `S` — a child — and it contains `S'`.

This is the laminar content of KKO21 Observation 4.32.  Note it needs no
appeal to `union_children`: the maximal-cardinality argument never has to know
that the children cover `S`. -/
theorem exists_child_superset {S' S : Finset (Fin n)} (hS' : S' ∈ H.cuts)
    (hS : S ∈ H.cuts) (hlt : S' ⊂ S) :
    ∃ a, IsChildOf H.cuts a S ∧ S' ⊆ a := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image
    (H.cuts.filter fun b => S' ⊆ b ∧ b ⊂ S) Finset.card
    ⟨S', Finset.mem_filter.mpr ⟨hS', Finset.Subset.refl S', hlt⟩⟩
  obtain ⟨hacut, haS', haS⟩ := Finset.mem_filter.mp ha
  refine ⟨a, ⟨hacut, hS, haS, fun b hb hab hbS => ?_⟩, haS'⟩
  have hbmem : b ∈ H.cuts.filter fun b => S' ⊆ b ∧ b ⊂ S :=
    Finset.mem_filter.mpr ⟨hb, haS'.trans hab.subset, hbS⟩
  exact absurd (Finset.card_lt_card hab) (not_lt.mpr (hmax b hbmem))

/-- **KKO22 Definition B.1's `p(e)`.**  The smallest cut of the hierarchy
containing both endpoints of `e`. -/
def IsEdgeParent (e : Sym2 (Fin n)) (S : Finset (Fin n)) : Prop :=
  S ∈ H.cuts ∧ EdgeInside e S ∧ ∀ R ∈ H.cuts, EdgeInside e R → S ⊆ R

/-- `p(e)` is well defined: two smallest containers contain each other. -/
theorem IsEdgeParent.unique {e : Sym2 (Fin n)} {S S' : Finset (Fin n)}
    (h : H.IsEdgeParent e S) (h' : H.IsEdgeParent e S') : S = S' :=
  Finset.Subset.antisymm (h.2.2 S' h'.1 h'.2.1) (h'.2.2 S h.1 h.2.1)

/-- **`p(e)` exists** for every edge internal to the hierarchy's root.  A
container of least cardinality is a container of least inclusion: laminarity
offers three alternatives against any other container, and an edge inside both
rules out disjointness, while cardinality rules out proper containment. -/
theorem exists_isEdgeParent {e : Sym2 (Fin n)} (he : EdgeInside e e₀.rootCut) :
    ∃ S, H.IsEdgeParent e S := by
  classical
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
    (H.cuts.filter fun S => EdgeInside e S) Finset.card
    ⟨e₀.rootCut, Finset.mem_filter.mpr ⟨H.rootCut_mem, he⟩⟩
  obtain ⟨hScut, hSin⟩ := Finset.mem_filter.mp hS
  refine ⟨S, hScut, hSin, fun R hR hRin => ?_⟩
  have hRD : R ∈ H.cuts.filter fun S => EdgeInside e S :=
    Finset.mem_filter.mpr ⟨hR, hRin⟩
  rcases H.laminar S hScut R hR with h | h | h
  · exact h
  · have hRS : R = S := Finset.eq_of_subset_of_card_le h (hmin R hRD)
    rw [← hRS]
  · exact absurd h (hSin.not_disjoint hRin)

/-- **`p(e) = S` for an edge between two children of `S`.**  Any cut of the
hierarchy holding both endpoints holds both children — laminarity leaves it no
other option, since it meets each and cannot sit inside either — and then
maximality of the children forbids it from sitting properly inside `S`.

This is the only way the development ever identifies an edge parent, and it is
what Theorem B.2's hypothesis `p(e) = S` for `e ∈ F` is discharged by. -/
theorem isEdgeParent_of_between_children {a b S : Finset (Fin n)}
    (ha : IsChildOf H.cuts a S) (hb : IsChildOf H.cuts b S) (hab : a ≠ b)
    {e : Sym2 (Fin n)} (he : e ∈ betweenEdges a b) : H.IsEdgeParent e S := by
  have hdab : Disjoint a b := H.children_disjoint ha hb hab
  obtain ⟨u, hu, v, hv, rfl⟩ := NearCycle.mem_betweenEdges_iff'.mp he
  refine ⟨ha.2.1, edgeInside_iff.mpr ⟨H.child_subset ha hu, H.child_subset hb hv⟩,
    fun R hR hRin => ?_⟩
  obtain ⟨huR, hvR⟩ := edgeInside_iff.mp hRin
  -- both children sit inside `R`
  have key : ∀ {c d : Finset (Fin n)}, IsChildOf H.cuts c S → Disjoint c d →
      ∀ {p q : Fin n}, p ∈ c → q ∈ d → p ∈ R → q ∈ R → c ⊆ R := by
    intro c d hc hcd p q hp hq hpR hqR
    rcases H.laminar c hc.1 R hR with h | h | h
    · exact h
    · exact absurd (Finset.disjoint_left.mp hcd (h hqR) hq) not_false
    · exact absurd (Finset.disjoint_left.mp h hp hpR) not_false
  have haR : a ⊆ R := key ha hdab hu hv huR hvR
  have hbR : b ⊆ R := key hb hdab.symm hv hu hvR huR
  have hbne : b.Nonempty := (H.nearMin b hb.1).nonempty
  have hass : a ⊂ R := by
    refine ssubset_of_subset_of_ne haR fun hc => ?_
    obtain ⟨w, hw⟩ := hbne
    exact Finset.disjoint_left.mp hdab (hc ▸ hbR hw) hw
  rcases H.laminar S ha.2.1 R hR with h | h | h
  · exact h
  · have hRS : R = S := by
      by_contra hne
      exact ha.2.2.2 R hR hass (ssubset_of_subset_of_ne h hne)
    rw [← hRS]
  · exact absurd (Finset.disjoint_left.mp h (H.child_subset ha hu) huR) not_false

/-! #### The near-cycle of a near-cycle cut

`nearCycle_spec` produces its witness existentially; `Presents` names the two
properties so that Theorem B.2's near-cycle clause can quantify over the
witness rather than re-derive it. -/

/-- `N` **presents** the near-cycle cut `S`: its root atom is the complement of
`S`, and its non-root atoms are exactly the children of `S`. -/
def Presents (N : NearCycle x ε) (S : Finset (Fin n)) : Prop :=
  N.root = Sᶜ ∧ ∀ a, IsChildOf H.cuts a S ↔ ∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = a

theorem exists_presents {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) : ∃ N : NearCycle x ε, H.Presents N S :=
  H.nearCycle_spec S hS hcyc

/-- **A triangle cut** (Definition B.1): a hierarchy cut with exactly two
children.  KKO give it its own `A, B, C` partition — `A = E(X, X ∖ Y)`,
`B = E(Y, Y ∖ X)`, `C = ∅` — and Theorem B.3's Type 5 pays for it by Lemma
A.13 rather than by Theorem A.12, which is why it is named apart from the
near-cycle cuts. -/
def IsTriangleCut (S : Finset (Fin n)) : Prop :=
  ∃ X Y : Finset (Fin n), IsChildOf H.cuts X S ∧ IsChildOf H.cuts Y S ∧ X ≠ Y ∧
    ∀ Z, IsChildOf H.cuts Z S → Z = X ∨ Z = Y

/-- **The component-to-near-cycle correspondence.**  A near-cycle whose root
atom is `a₀` and whose non-root atoms are the atoms of `𝒞` other than `a₀`
presents the cut `a₀ᶜ` — the outer polygon cut — as soon as the hierarchy's
children there are those same atoms.

Both halves arrive from elsewhere and meet only here: the first is what
`exists_happySlack_of_oneSideComponent` now returns alongside its vector, and
the second is what the hierarchy construction of Theorem B.3 produces (Fact
B.4).  Composing them is a rewrite, which is the point — the two developments
speak of the same near-cycle without either having to build the other's. -/
theorem presents_of_atom_iff {S : Finset (Fin n)} {N : NearCycle x ε}
    {C : Finset (Fin n) → Prop} (hroot : N.root = Sᶜ)
    (hatom : ∀ A : Finset (Fin n),
      (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A) ↔ C A)
    (hchild : ∀ a : Finset (Fin n), IsChildOf H.cuts a S ↔ C a) :
    H.Presents N S :=
  ⟨hroot, fun a => (hchild a).trans (hatom a).symm⟩

/-- The instance at a component, where the description `C` is "an atom other
than the root". -/
theorem presents_of_atoms {𝒞 : Finset (Finset (Fin n))} {a₀ : Finset (Fin n)}
    {N : NearCycle x ε} (hroot : N.root = a₀)
    (hatom : ∀ A : Finset (Fin n),
      (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A) ↔ A ∈ atoms 𝒞 ∧ A ≠ a₀)
    (hchild : ∀ a : Finset (Fin n),
      IsChildOf H.cuts a a₀ᶜ ↔ (a ∈ atoms 𝒞 ∧ a ≠ a₀)) :
    H.Presents N a₀ᶜ :=
  H.presents_of_atom_iff (by rw [hroot, compl_compl]) hatom hchild

variable {H}

/-- The near-cycle's outer cut is the cut it presents. -/
theorem Presents.outerCut_eq {N : NearCycle x ε} {S : Finset (Fin n)}
    (h : H.Presents N S) : N.outerCut = S := by
  rw [NearCycle.outerCut, h.1, compl_compl]

theorem Presents.atom_isChildOf {N : NearCycle x ε} {S : Finset (Fin n)}
    (h : H.Presents N S) {t : Fin (N.k + 3)} (ht : t ≠ 0) :
    IsChildOf H.cuts (N.atom t) S := (h.2 (N.atom t)).mpr ⟨t, ht, rfl⟩

/-- Every non-root atom of the presenting near-cycle avoids `e₀`: it is a cut
of the hierarchy, and those are rooted. -/
theorem Presents.avoids_atom {N : NearCycle x ε} {S : Finset (Fin n)}
    (h : H.Presents N S) {t : Fin (N.k + 3)} (ht : t ≠ 0) :
    AvoidsRootEdge e₀ (N.atom t) := H.avoids _ (h.atom_isChildOf ht).1

/-- **An interior group edge is parented by the near-cycle cut.**  The group
`E(aᵢ, aᵢ₊₁)` with neither index the root joins two distinct non-root atoms,
which are two distinct children of the cut the near-cycle presents.

This is what makes the slack vectors of different components disjointly
supported: Lemma A.8 charges only interior groups, so a charged edge determines
`p(e)`, and `p(e)` determines the component. -/
theorem Presents.isEdgeParent_of_mem_group {N : NearCycle x ε}
    {S' : Finset (Fin n)} (h : H.Presents N S') {g : Fin (N.k + 3)}
    (hg0 : g ≠ 0) (hg1 : g + 1 ≠ 0) {e : Sym2 (Fin n)} (he : e ∈ N.group g) :
    H.IsEdgeParent e S' := by
  have hne : N.atom g ≠ N.atom (g + 1) := by
    intro hc
    obtain ⟨w, hw⟩ := N.atom_nonempty g
    exact Finset.disjoint_left.mp (N.atom_disjoint g (g + 1) (N.ne_add_one g)) hw (hc ▸ hw)
  exact H.isEdgeParent_of_between_children (h.atom_isChildOf hg0)
    (h.atom_isChildOf hg1) hne he

/-- **The Type 4 adapter.**  Every edge a nested cut keeps inside the outer cut
has the near-cycle cut for its parent: such an edge runs between two distinct
non-root atoms, and those are two distinct children.

This is what turns Theorem B.2's condition `p(e) = S'` for all `e ∈ F` — which
looks like a fact about the hierarchy — into a fact about the near-cycle, and
it is the reason `F = δ(S) ∖ δ(S')` is the right set to feed the Main Payment
Theorem. -/
theorem Presents.isEdgeParent_of_mem_sideEdges {N : NearCycle x ε}
    {S' : Finset (Fin n)} (h : H.Presents N S') {i j : Fin (N.k + 3)}
    (h0 : (0 : Fin (N.k + 3)) ∉ Finset.Icc i j) {e : Sym2 (Fin n)}
    (he : e ∈ N.sideEdges (N.interval i j)) : H.IsEdgeParent e S' := by
  rw [N.sideEdges_eq_betweenEdges (N.interval_subset_outerCut h0)] at he
  obtain ⟨u, hu, v, hv, rfl⟩ := NearCycle.mem_betweenEdges_iff'.mp he
  obtain ⟨houter, hvS⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨t, ht, hut⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨t', hvt'⟩ := N.atom_cover v
  have ht0 : t ≠ 0 := fun hc => h0 (hc ▸ ht)
  have ht'0 : t' ≠ 0 := by
    rintro rfl
    exact (Finset.mem_compl.mp houter) hvt'
  have ht' : t' ∉ Finset.Icc i j := fun hc => hvS (N.atom_subset_interval hc hvt')
  have htt' : t ≠ t' := fun hc => ht' (hc ▸ ht)
  have hne : N.atom t ≠ N.atom t' := by
    intro hc
    obtain ⟨w, hw⟩ := N.atom_nonempty t
    exact Finset.disjoint_left.mp (N.atom_disjoint t t' htt') hw (hc ▸ hw)
  exact H.isEdgeParent_of_between_children (h.atom_isChildOf ht0)
    (h.atom_isChildOf ht'0) hne
    (NearCycle.mem_betweenEdges_iff'.mpr ⟨u, hut, v, hvt', rfl⟩)

end Hierarchy

/-- Expectation commutes with a sum over an arbitrary finite index — the
`Finset (Sym2 (Fin n))`-indexed form is `TreeDist.expect_sum`. -/
theorem TreeDist.expect_sum' (μ : TreeDist n x) {ι : Type*} (s : Finset ι)
    (f : ι → Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => ∑ i ∈ s, f i T) = ∑ i ∈ s, μ.expect (fun T => f i T) := by
  simp only [TreeDist.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### The construction: Facts B.4 and B.5

KKO build the hierarchy by running a procedure on `N_{η,≤1}`: an uncrossed cut
goes in whole; a component of two or more cuts contributes its non-root atoms
and the union of them, the *outer polygon cut*, which is then named a
near-cycle cut.  Fact B.4 says the result is a valid hierarchy and Fact B.5
that its non-singleton components match the components of `N_{η,≤1}` one for
one.

`OneSideFamily` is what the procedure ranges over, and `IsHierarchyOf` is what
it produces, stated in the clauses Theorem B.3 actually consumes. -/

/-- **The family of components of `N_{η,≤1}`**: one polygon per component
holding two or more cuts, in the style of `PolygonFamily`.  Singleton
components carry no polygon — `PolygonRep` demands four outside atoms — and
need none: they go into the hierarchy as themselves. -/
structure OneSideFamily (x : Sym2 (Fin n) → ℝ) (η : ℝ) (e₀ : RootEdge n) where
  /-- The number of non-singleton components. -/
  N : ℕ
  /-- The components of `N_{η,≤1}`, one per polygon. -/
  comp : Fin N → Finset (Finset (Fin n))
  isComp : ∀ i, IsOneSideComponent e₀ x η (comp i)
  comp_injective : Function.Injective comp
  /-- The polygon representation of each component. -/
  rep : ∀ i, PolygonRep (comp i)
  /-- KKO's root convention (§4.2), as in `PolygonFamily`. -/
  root_eq : ∀ i, (rep i).rootAtom = atomOf (comp i) e₀.u₀
  /-- The enumerated components exhaust the cuts of `N_{η,≤1}` **that cross
  something**; the rest are the singletons the procedure adds directly. -/
  exists_index : ∀ S, IsOneSideNearMinCut e₀ x η S →
    (∃ T, IsOneSideNearMinCut e₀ x η T ∧ Crossing S T) → ∃ i, S ∈ comp i

namespace OneSideFamily

variable {e₀ : RootEdge n} (F : OneSideFamily x η e₀)

/-- The root atom of component `i`. -/
def rootAtom (i : Fin F.N) : Finset (Fin n) := (F.rep i).rootAtom

/-- **The outer polygon cut** of component `i`: the union of its non-root
atoms.  With no inside atoms the atoms cover `V`, so that union *is* the
complement of the root atom — which is how Definition B.1 sees it, the
near-cycle presenting the cut being rooted at its complement. -/
def outerCut (i : Fin F.N) : Finset (Fin n) := (F.rootAtom i)ᶜ

theorem outerCut_compl (i : Fin F.N) : (F.outerCut i)ᶜ = F.rootAtom i :=
  compl_compl _

/-- Both endpoints of `e₀` lie in the root atom: `u₀` because the root atom is
its atom, `v₀` because no cut of the component separates them. -/
theorem mem_rootAtom (i : Fin F.N) :
    e₀.u₀ ∈ F.rootAtom i ∧ e₀.v₀ ∈ F.rootAtom i := by
  constructor
  · rw [rootAtom, F.root_eq i]; exact mem_atomOf_self _ _
  · rw [rootAtom, F.root_eq i, mem_atomOf]
    intro S hS
    have hav := (F.isComp i).avoids S hS
    exact ⟨fun hc => absurd hc hav.1, fun hc => absurd hc hav.2⟩

/-- The outer cut is rooted: the endpoints of `e₀` are in the root atom, which
is its complement. -/
theorem avoidsRootEdge_outerCut (i : Fin F.N) :
    AvoidsRootEdge e₀ (F.outerCut i) := by
  obtain ⟨hu, hv⟩ := F.mem_rootAtom i
  exact ⟨fun hc => (Finset.mem_compl.mp hc) hu, fun hc => (Finset.mem_compl.mp hc) hv⟩

open Classical in
/-- **Definition A.7's relevant atoms** of a component: its non-root atoms of
small enough degree.  Together with the component's own cuts these are the cuts
Appendix A pays for, and by Fact B.4 they are exactly the children of the
component's outer cut that are `η`-near minimum. -/
noncomputable def relevantAtoms (i : Fin F.N) : Finset (Finset (Fin n)) :=
  (atoms (F.comp i)).filter fun A => A ≠ F.rootAtom i ∧ cutSum x A ≤ 2 + η

open Classical in
theorem mem_relevantAtoms {i : Fin F.N} {A : Finset (Fin n)} :
    A ∈ F.relevantAtoms i ↔
      A ∈ atoms (F.comp i) ∧ A ≠ F.rootAtom i ∧ cutSum x A ≤ 2 + η := by
  rw [relevantAtoms, Finset.mem_filter]

/-- Every cut of the component sits inside its outer cut, the root atom being
disjoint from all of them. -/
theorem subset_outerCut (i : Fin F.N) {S : Finset (Fin n)} (hS : S ∈ F.comp i) :
    S ⊆ F.outerCut i := by
  intro v hv
  refine Finset.mem_compl.mpr fun hc => ?_
  rw [rootAtom, F.root_eq i, mem_atomOf] at hc
  exact ((F.isComp i).avoids S hS).1 ((hc S hS).mpr hv)

/-- **KKO22 Facts B.4 and B.5**, as the interface Theorem B.3 consumes: `H` is
the hierarchy the construction produces from the family `F`. -/
structure IsHierarchyOf {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {η : ℝ}
    (F : OneSideFamily x₀ η e₀)
    (H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)) : Prop where
  /-- B.4: an uncrossed cut of `N_{η,≤1}` goes into the hierarchy whole. -/
  uncrossed_mem : ∀ S, IsOneSideNearMinCut e₀ x₀ η S →
    (¬ ∃ T, IsOneSideNearMinCut e₀ x₀ η T ∧ Crossing S T) → S ∈ H.cuts
  /-- B.4: each component contributes its non-root atoms … -/
  atom_mem : ∀ (i : Fin F.N) (a : Finset (Fin n)),
    a ∈ atoms (F.comp i) → a ≠ F.rootAtom i → a ∈ H.cuts
  /-- … and its outer polygon cut … -/
  outer_mem : ∀ i, F.outerCut i ∈ H.cuts
  /-- … which is named a near-cycle cut … -/
  outer_nearCycle : ∀ i, H.IsNearCycleCut (F.outerCut i)
  /-- … and whose children are exactly those atoms.  This is the clause the
  component-to-near-cycle correspondence consumes. -/
  children_outer : ∀ (i : Fin F.N) (a : Finset (Fin n)),
    IsChildOf H.cuts a (F.outerCut i) ↔ (a ∈ atoms (F.comp i) ∧ a ≠ F.rootAtom i)
  /-- **Fact B.5**, one direction: distinct components give distinct
  near-cycle cuts. -/
  outer_injective : Function.Injective F.outerCut
  /-- **Fact B.5**, the other: every near-cycle cut of the hierarchy that is
  not a triangle comes from a component. -/
  exists_index_of_nearCycle : ∀ S ∈ H.cuts, H.IsNearCycleCut S →
    ¬ H.IsTriangleCut S → ∃ i, F.outerCut i = S
  /-- The clause KKO record just before Theorem B.2, and the one the five-type
  classification runs on: every cut of `N_{η,≤1}` is either in the hierarchy
  or a cut of one of the components. -/
  coverage : ∀ S, IsOneSideNearMinCut e₀ x₀ η S → S ∈ H.cuts ∨ ∃ i, S ∈ F.comp i

/-- **The correspondence, at the hierarchy.**  Appendix A's near-cycle for a
component and Definition B.1's near-cycle cut are the same object: the one
presents the other.

This is what Type 4 needs.  Appendix A supplies `hroot` and `hatom` alongside
its slack vector, Fact B.4 supplies `children_outer`, and
`Hierarchy.presents_of_atoms` does the rest — so `payment_of_leftmost` and
`payment_of_rightmost` apply at a cut of the component without either side
having to build the other's object. -/
theorem IsHierarchyOf.presents {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    (hH : F.IsHierarchyOf H) (i : Fin F.N)
    {N : NearCycle (e₀.restrict x₀) (7 * η)} (hroot : N.root = F.rootAtom i)
    (hatom : ∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
      ↔ A ∈ atoms (F.comp i) ∧ A ≠ F.rootAtom i) :
    H.Presents N (F.outerCut i) :=
  H.presents_of_atoms hroot hatom (hH.children_outer i)

/-- **Theorem B.3's classification.**  Every rooted `η`-near minimum cut other
than the hierarchy's root falls into one of KKO's types.

Type 1 is absent: rooted cuts avoid `e₀` by construction.  What the hierarchy
construction buys is the disjunction itself — `coverage` puts a cut of
`N_{η,≤1}` either in the hierarchy or in a component, and the cut parent then
splits the hierarchy case three ways, by whether `p(S)` is a degree cut
(Type 3), a triangle (Type 5), or a near-cycle cut of a component (Type 4 at an
atom).  Fact B.5 is what supplies the last step: a non-triangle near-cycle cut
*is* some component's outer cut. -/
theorem IsHierarchyOf.classify {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    (hH : F.IsHierarchyOf H) {S : Finset (Fin n)}
    (hS : IsRootedNearMinCut e₀ x₀ η S) (hne : S ≠ e₀.rootCut) :
    CrossedBothSides e₀ x₀ η S ∨
    (∃ S', IsChildOf H.cuts S S' ∧ ¬ H.IsNearCycleCut S') ∨
    (∃ i, S ∈ F.comp i) ∨
    (∃ i, IsChildOf H.cuts S (F.outerCut i)) ∨
    (∃ S', IsChildOf H.cuts S S' ∧ H.IsNearCycleCut S' ∧ H.IsTriangleCut S') := by
  by_cases hboth : CrossedBothSides e₀ x₀ η S
  · exact Or.inl hboth
  rcases hH.coverage S ⟨hS, hboth⟩ with hmem | hcomp
  · obtain ⟨S', hchild⟩ := H.exists_isChildOf hmem hne
    by_cases hcyc : H.IsNearCycleCut S'
    · by_cases htri : H.IsTriangleCut S'
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨S', hchild, hcyc, htri⟩)))
      · obtain ⟨i, hi⟩ := hH.exists_index_of_nearCycle S' hchild.2.1 hcyc htri
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, by rw [hi]; exact hchild⟩)))
    · exact Or.inr (Or.inl ⟨S', hchild, hcyc⟩)
  · exact Or.inr (Or.inr (Or.inl hcomp))

/-- **The seam, closed.**  At a component of the family, Appendix A's slack
vector and the hierarchy's near-cycle cut are delivered together, over one and
the same near-cycle.

Everything Theorem B.3's Type 4 needs at that component is then available at
once: `payment_of_pay` for the cuts Appendix A settles outright, and
`payment_of_leftmost`/`payment_of_rightmost` — which need `H.Presents N S'` —
for the extremal ones at an unhappy near-cycle. -/
theorem exists_slackStar_of_index {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    (hH : F.IsHierarchyOf H) (i : Fin F.N) (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms (F.comp i) ∧ A ≠ F.rootAtom i ∧ cutSum x₀ A ≤ 2 + η)
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      H.Presents N (F.outerCut i) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S ∈ F.comp i ∪ 𝒜, ∃ a b : Fin (N.k + 3), N.interval a b = S ∧
        0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
          (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + η))
            * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s' T e = 0) := by
  obtain ⟨N, s', hNroot, hNatom, hnn, hpay, hexp, hsupp⟩ :=
    exists_slackStar_oneSide (𝒞 := F.comp i) hx₀ μ (F.rep i) (F.isComp i)
      (F.root_eq i) 𝒜 h𝒜 hη0 hη hβ0
  exact ⟨N, s', hH.presents i hNroot hNatom, hnn, hpay, hexp, hsupp⟩

/-- **Appendix A, globally.**  The per-component vectors of Theorem A.12 sum to
a single vector at no extra per-edge cost — `125ηβxₑ` once, not once per
component.

The vectors are disjointly supported, and the parent calculus is what says so.
Lemma A.8 charges only the *interior* groups `E(a₁,a₂), …, E(a_{m−2},a_{m−1})`
(`boundary_of_mem_chargeSet'`), so a charged edge joins two non-root atoms of
its component — two distinct children of that component's near-cycle cut — and
therefore `p(e)` is that cut.  Uniqueness of `p(e)`, with Fact B.5's
injectivity of the outer cuts, pins the component: at most one summand at any
edge is ever nonzero.

The payment survives the sum for the trivial reason that the other summands are
nonnegative. -/
theorem exists_slackStar_global {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    (hH : F.IsHierarchyOf H) (𝒜 : Fin F.N → Finset (Finset (Fin n)))
    (h𝒜 : ∀ i, ∀ A ∈ 𝒜 i,
      A ∈ atoms (F.comp i) ∧ A ≠ F.rootAtom i ∧ cutSum x₀ A ≤ 2 + η)
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ i : Fin F.N, ∃ N : NearCycle (e₀.restrict x₀) (7 * η),
        H.Presents N (F.outerCut i) ∧
        ∀ S ∈ F.comp i ∪ 𝒜 i, ∃ a b : Fin (N.k + 3), N.interval a b = S ∧
          0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
          ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
            (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
            (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + η))
            * e₀.restrict x₀ e) := by
  classical
  choose N sv hpres hnn hpay hexp hsupp using fun i : Fin F.N =>
    exists_slackStar_of_index hx₀ μ hH i (𝒜 i) (h𝒜 i) hη0 hη hβ0
  refine ⟨fun T e => ∑ i : Fin F.N, sv i T e, fun T e => ?_, fun i => ?_, fun e => ?_⟩
  · exact Finset.sum_nonneg fun i _ => hnn i T e
  · refine ⟨N i, hpres i, fun S hS => ?_⟩
    obtain ⟨a, b, hab, hp1, hp2, hp3, hp⟩ := hpay i S hS
    refine ⟨a, b, hab, hp1, hp2, hp3, fun T hodd hL hR => ?_⟩
    refine le_trans (hp T hodd hL hR) (Finset.sum_le_sum fun e _ => ?_)
    exact Finset.single_le_sum (f := fun j => sv j T e)
      (fun j _ => hnn j T e) (Finset.mem_univ i)
  · -- at most one component charges any given edge
    have hkey : ∀ (i : Fin F.N) (T : Finset (Sym2 (Fin n))), sv i T e ≠ 0 →
        H.IsEdgeParent e (F.outerCut i) := by
      intro i T hne
      by_cases hall : ∀ g : Fin ((N i).k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ (N i).group g
      · exact absurd (hsupp i T e hall) hne
      · push Not at hall
        obtain ⟨g, hg0, hg1, hgm⟩ := hall
        exact (hpres i).isEdgeParent_of_mem_group hg0 hg1 hgm
    have huniq : ∀ (i j : Fin F.N) (T T' : Finset (Sym2 (Fin n))),
        sv i T e ≠ 0 → sv j T' e ≠ 0 → i = j := fun i j T T' hi hj =>
      hH.outer_injective
        (Hierarchy.IsEdgeParent.unique H (hkey i T hi) (hkey j T' hj))
    have hCnn : (0:ℝ) ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + η)) :=
      mul_nonneg (div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)) (by linarith)
    rw [μ.expect_sum' Finset.univ fun i T => sv i T e]
    by_cases hex : ∃ (i : Fin F.N) (T : Finset (Sym2 (Fin n))), sv i T e ≠ 0
    · obtain ⟨i₀, T₀, hi₀⟩ := hex
      have hzero : ∀ i ∈ (Finset.univ : Finset (Fin F.N)), i ≠ i₀ →
          μ.expect (fun T => sv i T e) = 0 := by
        intro i _ hne
        have hz : ∀ T, sv i T e = 0 := fun T => by
          by_contra hc
          exact hne (huniq i i₀ T T₀ hc hi₀)
        simp only [hz]
        exact μ.expect_const 0
      rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀) hzero]
      exact hexp i₀ e
    · push Not at hex
      have hall : ∑ i : Fin F.N, μ.expect (fun T => sv i T e) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [hex i]
        exact μ.expect_const 0
      rw [hall]
      exact mul_nonneg hCnn (RootEdge.restrict_nonneg hx₀.1 e)

end OneSideFamily

/-! ### Type 5: the triangle

A triangle cut has exactly two children and is not a component of `N_{η,≤1}`,
so Appendix A's component wrapper cannot reach it.  What reaches it is
`exists_happySlack_triangle` — Theorem A.12 at `k = 0` — and the packaging
below is word for word the packaging at a component, because the objects are
the same: a near-cycle, identified by its root atom and its non-root atoms, and
a vector paying `(2+η)β` on the extremal cuts under happiness. -/

/-- **KKO22 Lemma A.13 at KKO's scaling.**  At a triangle cut of the hierarchy
the slack vector and the near-cycle cut arrive together, exactly as at a
component (`OneSideFamily.exists_slackStar_of_index`).

`payment_of_leftmost` and `payment_of_rightmost` then apply verbatim: a
triangle *is* a near-cycle, and its two children are the intervals `[1,1]` and
`[2,2]`. -/
theorem exists_slackStar_triangle {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)} {dd : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    {S' X Y : Finset (Fin n)} (hXY : X ∪ Y = S')
    (hchild : ∀ a : Finset (Fin n), IsChildOf H.cuts a S' ↔ (a = X ∨ a = Y))
    (hd : Disjoint X Y)
    (hX : IsNearMinCut x₀ (7 * η) X) (hY : IsNearMinCut x₀ (7 * η) Y)
    (hS : IsNearMinCut x₀ (7 * η) S') (havoid : AvoidsRootEdge e₀ S')
    (hdd0 : 0 ≤ dd) (hXd : cutSum x₀ X ≤ 2 + dd) (hYd : cutSum x₀ Y ≤ 2 + dd)
    (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      H.Presents N S' ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S : Finset (Fin n), (S = X ∨ S = Y) → ∃ a b : Fin (N.k + 3),
        N.interval a b = S ∧ 0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
          (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + dd))
            * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s' T e = 0) := by
  have hαnn : 0 ≤ (2 + η) * β / (1 - 7 * η) :=
    div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  subst hXY
  obtain ⟨N, s', hroot, hatom, hnn, hpay, hexp, hsupp⟩ :=
    exists_happySlack_triangle (α := (2 + η) * β / (1 - 7 * η)) (d := dd)
      hx₀ μ hd hX hY hS havoid hαnn (by linarith) (by linarith) hdd0 hXd hYd
  refine ⟨N, s',
    H.presents_of_atom_iff (C := fun A => A = X ∨ A = Y) hroot hatom hchild,
    hnn, fun S hS0 => ?_, hexp, hsupp⟩
  obtain ⟨a, b, hab, h1, h2, h3, hp⟩ := hpay S hS0
  refine ⟨a, b, hab, h1, h2, h3, fun T hodd hL hR => ?_⟩
  have h := hp T hodd hL hR
  rwa [alpha_mul_one_sub (by linarith : (7 : ℝ) * η ≠ 1)] at h

/-! #### The family exists

Mirrors `exists_polygonFamily`: the components of `N_{η,≤1}` holding more than
one cut, enumerated, each carrying a polygon.  The polygon is
`polygonRep_exists_oneSide` (`PolygonOneSideExistence.lean`, proved from the BG08
core on 2026-09-08; until then an assumption stated here): a component of the
induced family need not be a rooted crossing component of `N_η`, but BG08
Theorem 4 asks only for a connected cross graph, so no coarsening is needed. -/

open Classical in
/-- The components of `N_{η,≤1}` holding more than one cut. -/
noncomputable def bigOneSideComps (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ)
    (η : ℝ) : Finset (Finset (Finset (Fin n))) :=
  ((univ.filter fun S => IsOneSideNearMinCut e₀ x η S).image
    (oneSideComp e₀ x η)).filter fun 𝒟 => 2 ≤ 𝒟.card

open Classical in
theorem mem_bigOneSideComps {e₀ : RootEdge n} {𝒟 : Finset (Finset (Fin n))} :
    𝒟 ∈ bigOneSideComps e₀ x η ↔
      (∃ S, IsOneSideNearMinCut e₀ x η S ∧ oneSideComp e₀ x η S = 𝒟) ∧ 2 ≤ 𝒟.card := by
  rw [bigOneSideComps, mem_filter, mem_image]
  refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨?_, h.2⟩⟩
  · obtain ⟨S, hS, hSD⟩ := h.1
    exact ⟨S, (mem_filter.mp hS).2, hSD⟩
  · obtain ⟨S, hS, hSD⟩ := h.1
    exact ⟨S, mem_filter.mpr ⟨mem_univ _, hS⟩, hSD⟩

theorem isOneSideComponent_of_mem_bigOneSideComps {e₀ : RootEdge n}
    {𝒟 : Finset (Finset (Fin n))} (h : 𝒟 ∈ bigOneSideComps e₀ x η) :
    IsOneSideComponent e₀ x η 𝒟 := by
  obtain ⟨⟨S, hS, rfl⟩, _⟩ := mem_bigOneSideComps.mp h
  exact isOneSideComponent_oneSideComp hS

/-- A cut of `N_{η,≤1}` that crosses another lies in an enumerated component:
the two are distinct members of its reachability class. -/
theorem oneSideComp_mem_bigOneSideComps {e₀ : RootEdge n} {S T : Finset (Fin n)}
    (hS : IsOneSideNearMinCut e₀ x η S) (hT : IsOneSideNearMinCut e₀ x η T)
    (hcr : Crossing S T) : oneSideComp e₀ x η S ∈ bigOneSideComps e₀ x η := by
  have hSmem : S ∈ oneSideComp e₀ x η S := mem_oneSideComp.mpr .refl
  have hTmem : T ∈ oneSideComp e₀ x η S :=
    mem_oneSideComp.mpr (Relation.ReflTransGen.single ⟨hS, hT, hcr⟩)
  have hne : S ≠ T := by
    rintro rfl
    obtain ⟨_, h2, _, _⟩ := hcr
    rw [Finset.sdiff_self] at h2
    exact Finset.not_nonempty_empty h2
  exact mem_bigOneSideComps.mpr ⟨⟨S, hS, rfl⟩, Finset.one_lt_card.mpr ⟨S, hSmem, T, hTmem, hne⟩⟩

/-- **The family of components of `N_{η,≤1}` exists**, so that
`polygonRep_exists_oneSide` is actually invoked rather than merely stated. -/
theorem exists_oneSideFamily (hx : x ∈ subtourLP n) (hη0 : 0 ≤ η)
    (hη : η < 2 / 5) (e₀ : RootEdge n) : Nonempty (OneSideFamily x η e₀) := by
  classical
  have hisC : ∀ i : Fin (bigOneSideComps e₀ x η).card,
      IsOneSideComponent e₀ x η
        ((bigOneSideComps e₀ x η).equivFin.symm i : Finset (Finset (Fin n))) :=
    fun i => isOneSideComponent_of_mem_bigOneSideComps
      ((bigOneSideComps e₀ x η).equivFin.symm i).2
  have hcard : ∀ i : Fin (bigOneSideComps e₀ x η).card,
      2 ≤ ((bigOneSideComps e₀ x η).equivFin.symm i : Finset (Finset (Fin n))).card :=
    fun i => (mem_bigOneSideComps.mp
      ((bigOneSideComps e₀ x η).equivFin.symm i).2).2
  choose P hP using fun i => polygonRep_exists_oneSide hx hη0 hη (hisC i) (hcard i)
  refine ⟨{ N := (bigOneSideComps e₀ x η).card
            comp := fun i => ((bigOneSideComps e₀ x η).equivFin.symm i :
              Finset (Finset (Fin n)))
            isComp := hisC
            comp_injective := ?_
            rep := P
            root_eq := hP
            exists_index := ?_ }⟩
  · intro i j hij
    exact (bigOneSideComps e₀ x η).equivFin.symm.injective (Subtype.ext hij)
  · rintro S hS ⟨T, hT, hcr⟩
    refine ⟨(bigOneSideComps e₀ x η).equivFin
      ⟨oneSideComp e₀ x η S, oneSideComp_mem_bigOneSideComps hS hT hcr⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact mem_oneSideComp.mpr .refl

/-! KKO22 Facts B.4 and B.5 — the construction of the hierarchy from the family,
`exists_hierarchy_of_oneSideFamily` — are proved in `HierarchyExistence.lean`, downstream of
the one-side polygon results.  Until 2026-09-09 they were an assumption here. -/

/-! ### The negative part, and Type 4 at an unhappy near-cycle -/

/-- The **negative part** of a slack vector on a set of edges: KKO's `s⁻(C)`. -/
noncomputable def negPart (s : Sym2 (Fin n) → ℝ) (C : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ C, min (s e) 0

theorem negPart_le_sum {s : Sym2 (Fin n) → ℝ} {C D : Finset (Sym2 (Fin n))}
    (hDC : D ⊆ C) : negPart s C ≤ ∑ e ∈ D, s e := by
  have h1 : negPart s C ≤ ∑ e ∈ D, min (s e) 0 := by
    rw [negPart]
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun e => -min (s e) 0) hDC
      (fun e _ _ => neg_nonneg.mpr (min_le_right _ _))
    simp only [Finset.sum_neg_distrib] at h
    linarith
  exact h1.trans (Finset.sum_le_sum fun e _ => min_le_left _ _)

/-- **KKO's Type 4 at an unhappy near-cycle.**  A leftmost cut splits into the
`A` edges of the near-cycle, the edges `D` it takes from `C`, and the edges
`F` that stay inside; the Main Payment Theorem bounds `s(A) + s(F) + s⁻(C)`
from below, and `s⁻(C) ≤ s(D)` because the terms it adds outside `D` are
nonpositive.

This is why KKO write `s⁻(C)` rather than `s(C)`: which edges of `C` the cut
takes is unpredictable, so in the worst case it takes exactly the ones with
negative slack — and that worst case is what the negative part measures. -/
theorem payment_of_negPart {S : Finset (Fin n)}
    {A F C D : Finset (Sym2 (Fin n))} {s s' : Sym2 (Fin n) → ℝ}
    (hsplit : cutEdges S = A ∪ D ∪ F)
    (hAD : Disjoint A D) (hADF : Disjoint (A ∪ D) F) (hDC : D ⊆ C)
    (hineq : 0 ≤ (∑ e ∈ A, s e) + (∑ e ∈ F, s e) + negPart s C)
    (hs' : ∀ e, 0 ≤ s' e) :
    0 ≤ ∑ e ∈ cutEdges S, (s e + s' e) := by
  have hD : negPart s C ≤ ∑ e ∈ D, s e := negPart_le_sum hDC
  have hsum : ∑ e ∈ cutEdges S, s e
      = (∑ e ∈ A, s e) + (∑ e ∈ D, s e) + ∑ e ∈ F, s e := by
    rw [hsplit, Finset.sum_union hADF, Finset.sum_union hAD]
  have hs'nn : 0 ≤ ∑ e ∈ cutEdges S, s' e := Finset.sum_nonneg fun e _ => hs' e
  rw [Finset.sum_add_distrib, hsum]
  linarith

/-! ### KKO22 Theorem B.2: the Main Payment Theorem

The hierarchy's own slack vector.  Everything it says is said through the
parent calculus above: (i) and (iv) quantify over cuts by their *cut* parent,
which is `IsChildOf`, and (i) and (iii) quantify over edges by their *edge*
parent, which is `IsEdgeParent`.  Neither is stored by the hierarchy — both are
the canonical smallest container of Definition B.1 — so nothing here needs a
field that a construction of the hierarchy would have to supply. -/

/-- **The conclusion of KKO22 Theorem B.2** (= KKO21 Theorem 4.33), bundled:
the good edges `E_g` and the hierarchy's random slack vector `s`, with the
paper's five properties. -/
structure IsMainPayment {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (H : Hierarchy (e₀.restrict x₀) e₀ ε) (μ : TreeDist n (e₀.restrict x₀))
    (β : ℝ) (Eg : Finset (Sym2 (Fin n)))
    (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) : Prop where
  /-- (i) `E_g ⊆ E ∖ δ({u₀, v₀})`: a good edge is a genuine edge of `E` lying
  inside the hierarchy's root. -/
  good_edge : ∀ e ∈ Eg, e ∈ edgeFinset n ∧ EdgeInside e e₀.rootCut
  /-- (i) Every **bottom** edge is good — an edge whose parent `p(e)` is a
  near-cycle cut. -/
  bottom_good : ∀ (e : Sym2 (Fin n)) (S : Finset (Fin n)), e ∈ edgeFinset n →
    H.IsEdgeParent e S → H.IsNearCycleCut S → e ∈ Eg
  /-- (i) A non-root cut whose parent `p(S)` is not a near-cycle cut carries
  three quarters of its mass on good edges. -/
  good_mass : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' →
    ¬ H.IsNearCycleCut S' → 3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e
  /-- (ii) `s` never falls below `−βxₑ`. -/
  lower : ∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e
  /-- (ii) `s` is supported on the good edges. -/
  support : ∀ T, ∀ e ∉ Eg, s T e = 0
  /-- (iii) **The near-cycle inequality.**  At a near-cycle cut that is not
  left happy, any set `F` of edges parented by that cut and carrying `1 − ε/2`
  of mass satisfies `s(A) + s(F) + s⁻(C) ≥ 0`. -/
  left_unhappy : ∀ (S : Finset (Fin n)) (N : NearCycle (e₀.restrict x₀) ε),
    S ∈ H.cuts → H.IsNearCycleCut S → H.Presents N S →
    ∀ T : Finset (Sym2 (Fin n)), ¬ N.LeftHappy T →
      ∀ F : Finset (Sym2 (Fin n)), (∀ e ∈ F, e ∈ edgeFinset n ∧ e ≠ e₀.edge) →
        (∀ e ∈ F, H.IsEdgeParent e S) →
        1 - ε / 2 ≤ ∑ e ∈ F, e₀.restrict x₀ e →
        0 ≤ (∑ e ∈ N.partA, s T e) + (∑ e ∈ F, s T e) + negPart (s T) N.partC
  /-- (iii) The mirror, at a near-cycle cut that is not right happy. -/
  right_unhappy : ∀ (S : Finset (Fin n)) (N : NearCycle (e₀.restrict x₀) ε),
    S ∈ H.cuts → H.IsNearCycleCut S → H.Presents N S →
    ∀ T : Finset (Sym2 (Fin n)), ¬ N.RightHappy T →
      ∀ F : Finset (Sym2 (Fin n)), (∀ e ∈ F, e ∈ edgeFinset n ∧ e ≠ e₀.edge) →
        (∀ e ∈ F, H.IsEdgeParent e S) →
        1 - ε / 2 ≤ ∑ e ∈ F, e₀.restrict x₀ e →
        0 ≤ (∑ e ∈ N.partB, s T e) + (∑ e ∈ F, s T e) + negPart (s T) N.partC
  /-- (iv) A non-root cut whose parent is not a near-cycle cut is satisfied by
  `s` alone whenever the tree crosses it an odd number of times.  This is
  Theorem B.3's Type 3. -/
  degree : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' → ¬ H.IsNearCycleCut S' →
    ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, s T e
  /-- (v) `s` gains `ε_P βxₑ` in expectation on every good edge. -/
  expect : ∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsP * β * e₀.restrict x₀ e)


/-! ### Type 4 at an unhappy near-cycle, complete at one cut

Everything Theorem B.3's Type 4 needs at a *single* near-cycle cut is now in
place, and the two theorems below assemble it: the split of the nested cut's
edges (`exists_split_left`), the mass on the edges that stay inside
(`one_sub_half_le_sum_sideEdges`, KKO22 Lemma 2.10), the identification of
their edge parent (`Presents.isEdgeParent_of_mem_sideEdges`), and the Main
Payment Theorem's own inequality.  What is left for the global proof is only
which cuts these apply to. -/

variable {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}

/-- The edges a nested cut keeps inside the outer cut are genuine edges of `E`:
they cross the cut, so they are off-diagonal, and the cut is rooted. -/
theorem NearCycle.sideEdges_subset_edges (N : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t))
    {S : Finset (Fin n)} (hSsub : S ⊆ N.outerCut) :
    ∀ e ∈ N.sideEdges S, e ∈ edgeFinset n ∧ e ≠ e₀.edge := by
  intro e he
  have hcut : e ∈ cutEdges S := (Finset.mem_sdiff.mp he).1
  refine ⟨cutEdges_subset_edgeFinset' S hcut, fun hc => ?_⟩
  exact RootEdge.edge_notMem_cutEdges
    (N.avoidsRootEdge_of_subset_outerCut havoid hSsub) (hc ▸ hcut)

/-- **Type 4 at a leftmost cut of an unhappy near-cycle.**  The near-cycle's
`A` always crosses a leftmost cut, what else goes to the root can only come
from `C`, and what stays inside is `F`; the Main Payment Theorem's inequality
`s(A) + s(F) + s⁻(C) ≥ 0` then settles the cut, with no help from `s*`. -/
theorem payment_of_leftmost {ε : ℝ} {H : Hierarchy (e₀.restrict x₀) e₀ ε}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hx₀ : x₀ ∈ subtourLP n)
    {S' : Finset (Fin n)} (hS' : S' ∈ H.cuts) (hcyc : H.IsNearCycleCut S')
    {N : NearCycle (e₀.restrict x₀) ε} (hpres : H.Presents N S')
    {j : Fin (N.k + 3)} (h1j : (1 : Fin (N.k + 3)) ≤ j) (hj : j < N.lastIdx)
    {d : ℝ} (hS : IsNearMinCut x₀ d (N.interval 1 j))
    {T : Finset (Sym2 (Fin n))} (hun : ¬ N.LeftHappy T)
    {s' : Sym2 (Fin n) → ℝ} (hs' : ∀ e, 0 ≤ s' e) :
    0 ≤ ∑ e ∈ cutEdges (N.interval 1 j), (s T e + s' e) := by
  have h0 : (0 : Fin (N.k + 3)) ∉ Finset.Icc (1 : Fin (N.k + 3)) j := by
    simp [Finset.mem_Icc]
  have hl : N.lastIdx ∉ Finset.Icc (1 : Fin (N.k + 3)) j := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _
    exact hj
  have havoid : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t) :=
    fun _ ht => hpres.avoids_atom ht
  have hsub := N.interval_subset_outerCut h0
  have hmass := N.one_sub_half_le_sum_sideEdges hx₀ havoid hsub hS
    (N.nonempty_outerCut_sdiff_interval N.lastIdx_ne_zero hl)
  have hineq := hMP.left_unhappy S' N hS' hcyc hpres T hun _
    (N.sideEdges_subset_edges havoid hsub)
    (fun _ he => hpres.isEdgeParent_of_mem_sideEdges h0 he) hmass
  obtain ⟨D, hsplit, hAD, hADF, hDC⟩ := N.exists_split_left h1j hj
  exact payment_of_negPart hsplit hAD hADF hDC hineq hs'

/-- **Type 4 at a rightmost cut**, the mirror image. -/
theorem payment_of_rightmost {ε : ℝ} {H : Hierarchy (e₀.restrict x₀) e₀ ε}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hx₀ : x₀ ∈ subtourLP n)
    {S' : Finset (Fin n)} (hS' : S' ∈ H.cuts) (hcyc : H.IsNearCycleCut S')
    {N : NearCycle (e₀.restrict x₀) ε} (hpres : H.Presents N S')
    {i : Fin (N.k + 3)} (h1i : (1 : Fin (N.k + 3)) < i) (hi : i ≤ N.lastIdx)
    {d : ℝ} (hS : IsNearMinCut x₀ d (N.interval i N.lastIdx))
    {T : Finset (Sym2 (Fin n))} (hun : ¬ N.RightHappy T)
    {s' : Sym2 (Fin n) → ℝ} (hs' : ∀ e, 0 ≤ s' e) :
    0 ≤ ∑ e ∈ cutEdges (N.interval i N.lastIdx), (s T e + s' e) := by
  have h0 : (0 : Fin (N.k + 3)) ∉ Finset.Icc i N.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr (lt_trans (by simp) h1i))
  have h1 : (1 : Fin (N.k + 3)) ∉ Finset.Icc i N.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr h1i)
  have hone : (1 : Fin (N.k + 3)) ≠ 0 := by
    intro hc
    have hv := congrArg Fin.val hc
    have h1' : ((1 : Fin (N.k + 3)) : ℕ) = 1 := rfl
    rw [h1'] at hv
    simp at hv
  have havoid : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t) :=
    fun _ ht => hpres.avoids_atom ht
  have hsub := N.interval_subset_outerCut h0
  have hmass := N.one_sub_half_le_sum_sideEdges hx₀ havoid hsub hS
    (N.nonempty_outerCut_sdiff_interval hone h1)
  have hineq := hMP.right_unhappy S' N hS' hcyc hpres T hun _
    (N.sideEdges_subset_edges havoid hsub)
    (fun _ he => hpres.isEdgeParent_of_mem_sideEdges h0 he) hmass
  obtain ⟨D, hsplit, hAD, hADF, hDC⟩ := N.exists_split_right h1i hi
  exact payment_of_negPart hsplit hAD hADF hDC hineq hs'

/-- **Types 4 and 5, in one lemma.**  At a cut that is an interval of a
near-cycle presenting a hierarchy cut, the payment holds however the near-cycle
falls for the tree: Appendix A — or, for a triangle, Lemma A.13 — pays outright
unless the cut is extremal and the near-cycle is unhappy on that side, and
there the Main Payment Theorem's own inequality settles it, with no help from
`s*` at all.

The three branches are KKO's own, and they are the reason Types 4 and 5 read
alike in the paper: once a triangle is a near-cycle like any other, the only
difference between the two types is which theorem supplies `hpayA`. -/
theorem payment_of_interval {ε : ℝ} {H : Hierarchy (e₀.restrict x₀) e₀ ε}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hx₀ : x₀ ∈ subtourLP n)
    {S' : Finset (Fin n)} (hS' : S' ∈ H.cuts) (hcyc : H.IsNearCycleCut S')
    {N : NearCycle (e₀.restrict x₀) ε} (hpres : H.Presents N S')
    {a b : Fin (N.k + 3)} (ha : (1 : Fin (N.k + 3)) ≤ a) (hab : a ≤ b)
    (hbl : b ≤ N.lastIdx) (hproper : ¬ (a = 1 ∧ b = N.lastIdx))
    {d : ℝ} (hSnm : IsNearMinCut x₀ d (N.interval a b))
    {T : Finset (Sym2 (Fin n))} {s' : Sym2 (Fin n) → ℝ} (hs' : ∀ e, 0 ≤ s' e)
    (hpayA : (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
      (2 + η) * β ≤ ∑ e ∈ cutEdges (N.interval a b), s' e)
    (hcut : ∑ e ∈ cutEdges (N.interval a b), e₀.restrict x₀ e ≤ 2 + η)
    (hβ0 : 0 ≤ β) (hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e) :
    0 ≤ ∑ e ∈ cutEdges (N.interval a b), (s T e + s' e) := by
  by_cases hL : a = 1 ∧ ¬ N.LeftHappy T
  · obtain ⟨rfl, hun⟩ := hL
    have hb : b < N.lastIdx := lt_of_le_of_ne hbl fun hc => hproper ⟨rfl, hc⟩
    exact payment_of_leftmost hMP hx₀ hS' hcyc hpres hab hb hSnm hun hs'
  · by_cases hR : b = N.lastIdx ∧ ¬ N.RightHappy T
    · obtain ⟨rfl, hun⟩ := hR
      have ha1 : (1 : Fin (N.k + 3)) < a :=
        lt_of_le_of_ne ha fun hc => hproper ⟨hc.symm, rfl⟩
      exact payment_of_rightmost hMP hx₀ hS' hcyc hpres ha1 hab hSnm hun hs'
    · push Not at hL hR
      exact payment_of_pay hβ0 hxnn (hMP.lower T) hcut (hpayA hL hR)

/-- **Types 4 and 5, at the output of the paying theorem.**  `payment_of_
interval` with the interval supplied by whichever theorem pays — Appendix A at
a component, Lemma A.13 at a triangle — so both types reduce to one
application, which is why they read alike in KKO's proof. -/
theorem payment_of_nearCycleCut {ε : ℝ} {H : Hierarchy (e₀.restrict x₀) e₀ ε}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hx₀ : x₀ ∈ subtourLP n)
    {S' : Finset (Fin n)} (hS' : S' ∈ H.cuts) (hcyc : H.IsNearCycleCut S')
    {N : NearCycle (e₀.restrict x₀) ε} (hpres : H.Presents N S')
    {S : Finset (Fin n)} {a b : Fin (N.k + 3)} (hab : N.interval a b = S)
    (h0 : 0 < a) (hle : a ≤ b) (hproper : ¬ (a = 1 ∧ b = N.lastIdx))
    (hS : IsRootedNearMinCut e₀ x₀ η S)
    {T : Finset (Sym2 (Fin n))} {s' : Sym2 (Fin n) → ℝ} (hs' : ∀ e, 0 ≤ s' e)
    (hodd : Odd (cutEdges S ∩ T).card)
    (hpayA : (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
      (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' e)
    (hβ0 : 0 ≤ β) (hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e) :
    0 ≤ ∑ e ∈ cutEdges S, (s T e + s' e) := by
  have hcut : ∑ e ∈ cutEdges S, e₀.restrict x₀ e ≤ 2 + η := by
    have h2 : cutSum (e₀.restrict x₀) S = cutSum x₀ S := cutSum_restrict hS.avoids
    have h := hS.nearMin.cut_le
    rw [cutSum] at h2
    linarith
  subst hab
  exact payment_of_interval hMP hx₀ hS' hcyc hpres (one_le_of_pos h0) hle
    (Fin.le_last _) hproper hS.nearMin hs' hpayA hcut hβ0 hxnn

/-- **Theorem B.3's clause (iv) at a cut nested in a near-cycle cut.**
Everything such a cut keeps inside the outer cut is a *bottom* edge — its
parent is the near-cycle cut — hence good by Theorem B.2(i); and that part
alone carries `1 − ε/2` of the cut's mass.

KKO reach the same conclusion the other way round, bounding what goes up to
the root by Lemma 2.10 and subtracting from `x(δ(S)) ≥ 2`.  Both routes are
KKO21 Lemma 2.7; this one uses its lower bound directly and so needs neither
the subtour constraint at `S` nor the upper bound. -/
theorem good_mass_of_nested {ε : ℝ} {H : Hierarchy (e₀.restrict x₀) e₀ ε}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hx₀ : x₀ ∈ subtourLP n) (hε : ε ≤ 1 / 2)
    {S' : Finset (Fin n)} (hcyc : H.IsNearCycleCut S')
    {N : NearCycle (e₀.restrict x₀) ε} (hpres : H.Presents N S')
    {i j : Fin (N.k + 3)} (h0 : (0 : Fin (N.k + 3)) ∉ Finset.Icc i j)
    (hne : (N.outerCut \ N.interval i j).Nonempty)
    {d : ℝ} (hS : IsNearMinCut x₀ d (N.interval i j)) :
    3 / 4 ≤ ∑ e ∈ cutEdges (N.interval i j) ∩ Eg, e₀.restrict x₀ e := by
  have havoid : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t) :=
    fun _ ht => hpres.avoids_atom ht
  have hsub := N.interval_subset_outerCut h0
  have hmass := N.one_sub_half_le_sum_sideEdges hx₀ havoid hsub hS hne
  have hgood : N.sideEdges (N.interval i j) ⊆ cutEdges (N.interval i j) ∩ Eg := by
    intro e he
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp he).1,
      hMP.bottom_good e S' (N.sideEdges_subset_edges havoid hsub e he).1
        (hpres.isEdgeParent_of_mem_sideEdges h0 he) hcyc⟩
  have hle : ∑ e ∈ N.sideEdges (N.interval i j), e₀.restrict x₀ e
      ≤ ∑ e ∈ cutEdges (N.interval i j) ∩ Eg, e₀.restrict x₀ e :=
    Finset.sum_le_sum_of_subset_of_nonneg hgood
      (fun e _ _ => RootEdge.restrict_nonneg hx₀.1 e)
  linarith

/-! ### Types 4 and 5 over the whole hierarchy

`payment_of_hierarchy` wants one vector paying at every near-cycle cut, and
`payment_of_nearCycleCut` pays at one.  The step between is a globalization of
the shape the components already got, over a single index set: the near-cycle
cuts of the hierarchy.  Indexing by the cuts themselves, rather than by
components and triangles separately, makes the injectivity that the
disjointness argument needs a triviality. -/

/-- The cuts a near-cycle cut of the hierarchy is **responsible** for: its own
children, and — when it is a component's outer cut — the cuts of that
component.  This is exactly what Theorem B.3's Types 4 and 5 hand to it. -/
def Responsible {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (F : OneSideFamily x₀ η e₀) (H : Hierarchy (e₀.restrict x₀) e₀ (7 * η))
    (S' S : Finset (Fin n)) : Prop :=
  IsChildOf H.cuts S S' ∨ ∃ i, F.outerCut i = S' ∧ S ∈ F.comp i

/-- **Appendix A over the whole hierarchy.**  Every near-cycle cut carries a
near-cycle and a paying vector — Appendix A's at a component, Lemma A.13's at a
triangle — and the sum over all of them costs no more per edge than one, for
the reason `exists_slackStar_global` already gave: a charged edge lies in an
interior group, so `p(e)` is the cut its near-cycle presents, and the cuts index
the sum.

This is Types 4 and 5 of Theorem B.3, in the form `payment_of_hierarchy`
consumes.  Which of the two a cut falls under is decided by whether it is a
component's outer cut — and if it is not, Fact B.5 leaves only a triangle. -/
theorem exists_slackStar_hierarchy {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hH : F.IsHierarchyOf H)
    (hx₀ : x₀ ∈ subtourLP n) (hη0 : 0 < η) (hη : η ≤ 1 / 100) (hβ0 : 0 ≤ β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S' S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        S' ∈ H.cuts → H.IsNearCycleCut S' → Responsible F H S' S →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ S' S : Finset (Fin n), S' ∈ H.cuts → H.IsNearCycleCut S' →
        Responsible F H S' S → IsRootedNearMinCut e₀ x₀ η S →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + 7 * η))
            * e₀.restrict x₀ e) := by
  classical
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  have hCnn : (0:ℝ) ≤ (2 + η) * β / (1 - 7 * η) :=
    div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  -- every hierarchy cut is near minimum over the LP point itself
  have hconv : ∀ A ∈ H.cuts, IsNearMinCut x₀ (7 * η) A := fun A hA =>
    ⟨(H.nearMin A hA).nonempty, (H.nearMin A hA).ne_univ, by
      rw [← cutSum_restrict (H.avoids A hA)]; exact (H.nearMin A hA).cut_le⟩
  set 𝒩 : Finset (Finset (Fin n)) := H.cuts.filter H.IsNearCycleCut with h𝒩
  have hkey : ∀ p : {S' // S' ∈ 𝒩}, ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (sv : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      H.Presents N p.1 ∧ (∀ T e, 0 ≤ sv T e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        sv T e = 0) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), Responsible F H p.1 S →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + sv T e)) ∧
      (∀ S : Finset (Fin n), Responsible F H p.1 S →
        IsRootedNearMinCut e₀ x₀ η S →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => sv T e)
        ≤ ((2 + η) * β / (1 - 7 * η)) * (4 * (8 * (7 * η) + 7 * η))
            * e₀.restrict x₀ e) := by
    rintro ⟨S', hS'𝒩⟩
    obtain ⟨hS', hcyc⟩ := Finset.mem_filter.mp hS'𝒩
    by_cases hout : ∃ i, F.outerCut i = S'
    · -- a component's outer cut: Appendix A
      obtain ⟨i, hi⟩ := hout
      obtain ⟨N, sv, hpres, hnn, hpay, hexp, hsupp⟩ :=
        OneSideFamily.exists_slackStar_of_index hx₀ μ hH i (F.relevantAtoms i)
          (fun A hA => F.mem_relevantAtoms.mp hA) hη0 hη hβ0
      have hpres' : H.Presents N S' := hi ▸ hpres
      have hmemS : ∀ S, Responsible F H S' S → IsRootedNearMinCut e₀ x₀ η S →
          S ∈ F.comp i ∪ F.relevantAtoms i := by
        intro S hresp hSnm
        rcases hresp with hchild | ⟨j, hj, hcomp⟩
        · refine Finset.mem_union_right _ (F.mem_relevantAtoms.mpr ?_)
          obtain ⟨h1, h2⟩ := (hH.children_outer i S).mp (by rw [hi]; exact hchild)
          exact ⟨h1, h2, hSnm.nearMin.cut_le⟩
        · have hji : j = i := hH.outer_injective (by rw [hj, hi])
          exact Finset.mem_union_left _ (hji ▸ hcomp)
      refine ⟨N, sv, hpres', hnn, hsupp, fun S T hresp hSnm hodd => ?_,
        fun S hresp hSnm => ?_, fun e => ?_⟩
      · obtain ⟨a, b, hab, h1, h2, h3, hp⟩ := hpay S (hmemS S hresp hSnm)
        exact payment_of_nearCycleCut hMP hx₀ hS' hcyc hpres' hab h1 h2 h3
          hSnm (hnn T) hodd (hp T hodd) hβ0 hxnn
      · obtain ⟨a, b, hab, h1, h2, h3, -⟩ := hpay S (hmemS S hresp hSnm)
        subst hab
        refine good_mass_of_nested hMP hx₀ (by linarith) hcyc hpres' ?_ ?_ hSnm.nearMin
        · rw [Finset.mem_Icc]
          rintro ⟨hle, -⟩
          exact absurd hle (not_le.mpr h1)
        · exact N.nonempty_outerCut_sdiff_of_proper h1 (Fin.le_last _) h3
      · refine le_trans (hexp e) ?_
        have hmono : 4 * (8 * (7 * η) + η) ≤ 4 * (8 * (7 * η) + 7 * η) := by linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmono hCnn) (hxnn e)
    · -- otherwise Fact B.5 leaves only a triangle: Lemma A.13
      have htri : H.IsTriangleCut S' := by
        by_contra hc
        exact hout (hH.exists_index_of_nearCycle S' hS' hcyc hc)
      obtain ⟨X, Y, hX, hY, hXY, hall⟩ := htri
      have hunion : X ∪ Y = S' := by
        refine Finset.Subset.antisymm
          (Finset.union_subset (H.child_subset hX) (H.child_subset hY)) fun v hv => ?_
        rcases H.union_children S' hS' v hv with ⟨a, ha, hva⟩ | hnone
        · rcases hall a ha with rfl | rfl
          · exact Finset.mem_union_left _ hva
          · exact Finset.mem_union_right _ hva
        · exact absurd hX (hnone X)
      have hchild : ∀ a : Finset (Fin n), IsChildOf H.cuts a S' ↔ (a = X ∨ a = Y) :=
        fun a => ⟨fun h => hall a h, fun h => by rcases h with rfl | rfl; exacts [hX, hY]⟩
      obtain ⟨N, sv, hpres, hnn, hpay, hexp, hsupp⟩ :=
        exists_slackStar_triangle (dd := 7 * η) hx₀ μ hunion hchild
          (H.children_disjoint hX hY hXY) (hconv X hX.1) (hconv Y hY.1) (hconv S' hS')
          (H.avoids S' hS') (by linarith) (hconv X hX.1).cut_le (hconv Y hY.1).cut_le
          hη0 hη hβ0
      have hmemS : ∀ S, Responsible F H S' S → (S = X ∨ S = Y) := by
        intro S hresp
        rcases hresp with hc | ⟨i, hi, -⟩
        · exact hall S hc
        · exact absurd ⟨i, hi⟩ hout
      refine ⟨N, sv, hpres, hnn, hsupp, fun S T hresp hSnm hodd => ?_,
        fun S hresp hSnm => ?_, hexp⟩
      · obtain ⟨a, b, hab, h1, h2, h3, hp⟩ := hpay S (hmemS S hresp)
        exact payment_of_nearCycleCut hMP hx₀ hS' hcyc hpres hab h1 h2 h3 hSnm
          (hnn T) hodd (hp T hodd) hβ0 hxnn
      · obtain ⟨a, b, hab, h1, h2, h3, -⟩ := hpay S (hmemS S hresp)
        subst hab
        refine good_mass_of_nested hMP hx₀ (by linarith) hcyc hpres ?_ ?_ hSnm.nearMin
        · rw [Finset.mem_Icc]
          rintro ⟨hle, -⟩
          exact absurd hle (not_le.mpr h1)
        · exact N.nonempty_outerCut_sdiff_of_proper h1 (Fin.le_last _) h3
  choose N sv hpres hnn hsupp hpay hgood hexp using hkey
  refine ⟨fun T e => ∑ p : {S' // S' ∈ 𝒩}, sv p T e, fun T e => ?_, ?_, ?_, fun e => ?_⟩
  · exact Finset.sum_nonneg fun p _ => hnn p T e
  · intro S' S T hS' hcyc hresp hSnm hodd
    set p : {S'' // S'' ∈ 𝒩} := ⟨S', Finset.mem_filter.mpr ⟨hS', hcyc⟩⟩ with hp
    refine le_trans (hpay p S T hresp hSnm hodd) (Finset.sum_le_sum fun e _ => ?_)
    have := Finset.single_le_sum (f := fun q : {S'' // S'' ∈ 𝒩} => sv q T e)
      (fun q _ => hnn q T e) (Finset.mem_univ p)
    linarith
  · intro S' S hS' hcyc hresp hSnm
    exact hgood ⟨S', Finset.mem_filter.mpr ⟨hS', hcyc⟩⟩ S hresp hSnm
  · -- at most one near-cycle cut charges any given edge
    have hkeyE : ∀ (p : {S' // S' ∈ 𝒩}) (T : Finset (Sym2 (Fin n))),
        sv p T e ≠ 0 → H.IsEdgeParent e p.1 := by
      intro p T hne
      by_cases hall : ∀ g : Fin ((N p).k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ (N p).group g
      · exact absurd (hsupp p T e hall) hne
      · push Not at hall
        obtain ⟨g, hg0, hg1, hgm⟩ := hall
        exact (hpres p).isEdgeParent_of_mem_group hg0 hg1 hgm
    have huniq : ∀ (p q : {S' // S' ∈ 𝒩}) (T T' : Finset (Sym2 (Fin n))),
        sv p T e ≠ 0 → sv q T' e ≠ 0 → p = q := fun p q T T' hp hq =>
      Subtype.ext (Hierarchy.IsEdgeParent.unique H (hkeyE p T hp) (hkeyE q T' hq))
    rw [μ.expect_sum' Finset.univ fun p T => sv p T e]
    by_cases hex : ∃ (p : {S' // S' ∈ 𝒩}) (T : Finset (Sym2 (Fin n))), sv p T e ≠ 0
    · obtain ⟨p₀, T₀, hp₀⟩ := hex
      have hzero : ∀ p ∈ (Finset.univ : Finset {S' // S' ∈ 𝒩}), p ≠ p₀ →
          μ.expect (fun T => sv p T e) = 0 := by
        intro p _ hne
        have hz : ∀ T, sv p T e = 0 := fun T => by
          by_contra hc
          exact hne (huniq p p₀ T T₀ hc hp₀)
        simp only [hz]
        exact μ.expect_const 0
      rw [Finset.sum_eq_single_of_mem p₀ (Finset.mem_univ p₀) hzero]
      exact hexp p₀ e
    · push Not at hex
      have hall : ∑ p : {S' // S' ∈ 𝒩}, μ.expect (fun T => sv p T e) = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        simp only [hex p]
        exact μ.expect_const 0
      rw [hall]
      exact mul_nonneg (mul_nonneg hCnn (by linarith)) (hxnn e)

/-- **Theorem B.3(ii), assembled from the classification.**  With a payment for
each type, every odd rooted near-minimum cut other than the hierarchy's root is
settled.

Type 2 is `payment_of_pay` at Theorem 5.2's vector; Type 3 is
`payment_of_nonneg` at the Main Payment Theorem's clause (iv); Types 4 and 5
are `payment_of_interval`, at a component and at a triangle — the hypotheses
`hpay4` and `hpay5`, which differ only in which theorem supplies the
near-cycle.

The root cut is excluded here and settled elsewhere: the tree crosses
`V ∖ {u₀, v₀}` exactly twice (`card_cut_inter_rootPair`), so the parity
hypothesis is vacuous there — which is how `exists_slack_pair` already uses
it. -/
theorem payment_of_hierarchy {F : OneSideFamily x₀ η e₀}
    {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hH : F.IsHierarchyOf H)
    (hβ0 : 0 ≤ β) (hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e) (hs' : ∀ T e, 0 ≤ s' T e)
    (hpay2 : ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → CrossedBothSides e₀ x₀ η S →
      Odd (cutEdges S ∩ T).card → (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e)
    (hpay4 : ∀ (i : Fin F.N) (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      (S ∈ F.comp i ∨ IsChildOf H.cuts S (F.outerCut i)) →
      IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e))
    (hpay5 : ∀ (S S' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsChildOf H.cuts S S' → H.IsNearCycleCut S' → H.IsTriangleCut S' →
      IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) :
    ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → S ≠ e₀.rootCut →
      Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e) := by
  intro S T hS hne hodd
  rcases hH.classify hS hne with hboth | ⟨S', hchild, hdeg⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ |
    ⟨S', hchild, hcyc, htri⟩
  · have hcut : ∑ e ∈ cutEdges S, e₀.restrict x₀ e ≤ 2 + η := by
      have h2 : cutSum (e₀.restrict x₀) S = cutSum x₀ S := cutSum_restrict hS.avoids
      have h := hS.nearMin.cut_le
      rw [cutSum] at h2
      linarith
    exact payment_of_pay hβ0 hxnn (hMP.lower T) hcut (hpay2 S T hS hboth hodd)
  · exact payment_of_nonneg (hMP.degree S S' hchild hdeg T hodd) (hs' T)
  · exact hpay4 i S T (Or.inl hi) hS hodd
  · exact hpay4 i S T (Or.inr hi) hS hodd
  · exact hpay5 S S' T hchild hcyc htri hS hodd

/-- **KKO22 Theorem B.3**, from the hierarchy and the Main Payment Theorem.

`s*` is the sum of two vectors, exactly as in KKO: Theorem 5.2's for the cuts
crossed on both sides, and Appendix A's — over the whole hierarchy, components
and triangles alike — for the rest.  The five types are `payment_of_hierarchy`,
the root cut is settled by parity (the tree crosses `V ∖ {u₀, v₀}` exactly
twice, `card_cut_inter_rootPair`), and clause (iv) selects between
`IsMainPayment.good_mass` and `good_mass_of_nested` by the classification.

⚠️ **The constant is `600ηβ`, not KKO's `125ηβ`.**  Appendix A here costs
`4α(8ε_η + ε_η) = 252αη` where KKO have `44αη`, because their `44` is inherited
from KKO21's sharper Lemmas 4.18–4.19 and does not follow from Theorem A.3 as
stated (see `notes.md`).  With `α = (2+η)β/(1 − ε)` the two vectors come to
about `541ηβ`, and `600` is a round bound.  `Theorem61.lean` carries the change
through: `EndToEnd.kkoEta` is `ε_P/3600` rather than KKO's `ε_P/750`, and `β`
has to be taken at KKO's own `η/(4 + 2η)`.  The gap constant survives. -/
theorem exists_payment_of_hierarchy {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {F : OneSideFamily x₀ η e₀} {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)}
    {μ : TreeDist n (e₀.restrict x₀)} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hMP : IsMainPayment H μ β Eg s) (hH : F.IsHierarchyOf H)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 600 * η * β * e₀.restrict x₀ e) ∧
      (∀ S : Finset (Fin n), IsRootedNearMinCut e₀ x₀ η S →
        ¬ CrossedBothSides e₀ x₀ η S → S ≠ e₀.rootCut →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) := by
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  obtain ⟨s2, hs2nn, hs2pay, hs2exp⟩ :=
    exists_slackStar_bothSides e₀ hx₀ μ hη0 (by linarith) (le_of_lt hβ0)
  obtain ⟨sA, hAnn, hApay, hAgood, hAexp⟩ :=
    exists_slackStar_hierarchy hMP hH hx₀ hη0 (by linarith) (le_of_lt hβ0)
  have hnn' : ∀ (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)), 0 ≤ s2 T e + sA T e :=
    fun T e => add_nonneg (hs2nn T e) (hAnn T e)
  refine ⟨fun T e => s2 T e + sA T e, hnn', ?_, ?_, ?_⟩
  · -- the five types, plus the root cut by parity
    intro S T hTprob hS hodd
    by_cases hroot : S = e₀.rootCut
    · exfalso
      rw [hroot, RootEdge.rootCut, cutEdges_compl,
        card_cut_inter_rootPair hx₀ hx₀e μ hn hTprob] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    · refine payment_of_hierarchy hMP hH (le_of_lt hβ0) hxnn hnn' ?_ ?_ ?_ S T hS hroot hodd
      · intro S₀ T₀ hS₀ hboth hodd₀
        refine le_trans (hs2pay S₀ T₀ hS₀ hboth hodd₀) (Finset.sum_le_sum fun e _ => ?_)
        have := hAnn T₀ e
        linarith
      · intro i S₀ T₀ hmem hS₀ hodd₀
        have hresp : Responsible F H (F.outerCut i) S₀ := by
          rcases hmem with h | h
          · exact Or.inr ⟨i, rfl, h⟩
          · exact Or.inl h
        refine le_trans (hApay (F.outerCut i) S₀ T₀ (hH.outer_mem i)
          (hH.outer_nearCycle i) hresp hS₀ hodd₀) (Finset.sum_le_sum fun e _ => ?_)
        have := hs2nn T₀ e
        linarith
      · intro S₀ S' T₀ hchild hcyc _ hS₀ hodd₀
        refine le_trans (hApay S' S₀ T₀ hchild.2.1 hcyc (Or.inl hchild) hS₀ hodd₀)
          (Finset.sum_le_sum fun e _ => ?_)
        have := hs2nn T₀ e
        linarith
  · -- the cost: Theorem 5.2's `18αη` and Appendix A's `252αη`
    intro e
    have hb1 : (2 + η) * β / (1 - η) ≤ 2.01 * β := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hb2 : (2 + η) * β / (1 - 7 * η) ≤ 2.01 * β := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hx := hxnn e
    have hηx : 0 ≤ η * e₀.restrict x₀ e := mul_nonneg (le_of_lt hη0) hx
    have k1 : 0 ≤ (2.01 * β - (2 + η) * β / (1 - η)) * (η * e₀.restrict x₀ e) :=
      mul_nonneg (sub_nonneg.mpr hb1) hηx
    have k2 : 0 ≤ (2.01 * β - (2 + η) * β / (1 - 7 * η)) * (η * e₀.restrict x₀ e) :=
      mul_nonneg (sub_nonneg.mpr hb2) hηx
    have k3 : 0 ≤ η * β * e₀.restrict x₀ e :=
      mul_nonneg (mul_nonneg (le_of_lt hη0) (le_of_lt hβ0)) hx
    have h1 := hs2exp e
    have h2 := hAexp e
    have hsum : μ.expect (fun T => s2 T e + sA T e)
        = μ.expect (fun T => s2 T e) + μ.expect (fun T => sA T e) :=
      μ.expect_add _ _
    rw [hsum]
    nlinarith [k1, k2, k3, h1, h2]
  · -- clause (iv)
    intro S hS hboth hroot
    rcases hH.classify hS hroot with hb | ⟨S', hchild, hdeg⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ |
      ⟨S', hchild, hcyc, -⟩
    · exact absurd hb hboth
    · exact hMP.good_mass S S' hchild hdeg
    · exact hAgood (F.outerCut i) S (hH.outer_mem i) (hH.outer_nearCycle i)
        (Or.inr ⟨i, rfl, hi⟩) hS
    · exact hAgood (F.outerCut i) S (hH.outer_mem i) (hH.outer_nearCycle i)
        (Or.inl hi) hS
    · exact hAgood S' S hchild.2.1 hcyc (Or.inl hchild) hS

/-- **Theorem B.3's case analysis.**  Once every odd rooted near-minimum cut
is classified into KKO's types, the payment follows from the three steps
proved above.

The disjunction is the classification: a cut is settled either because `s*`
pays `(2+η)β` on it (Types 2, 4 and 5 in their happy cases, from Theorem 5.2
and Appendix A at KKO's scaling `α = (2+η)β/(1 − ε)`), or because the
hierarchy's own vector is already nonnegative there (Type 3, from the Main
Payment Theorem), or because the cut splits as `A ⊎ D ⊎ F` against a
near-cycle whose inequality the Main Payment Theorem supplies (Types 4 and 5
when the near-cycle is unhappy).  Type 1 does not appear: rooted cuts avoid
`e₀`. -/
theorem payment_of_classification {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (hβ0 : 0 ≤ β) (hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e)
    (hs : ∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e)
    (hs' : ∀ T e, 0 ≤ s' T e)
    (hclass : ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
      ((2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∨
      (0 ≤ ∑ e ∈ cutEdges S, s T e) ∨
      (∃ A F C D : Finset (Sym2 (Fin n)), cutEdges S = A ∪ D ∪ F ∧
        Disjoint A D ∧ Disjoint (A ∪ D) F ∧ D ⊆ C ∧
        0 ≤ (∑ e ∈ A, s T e) + (∑ e ∈ F, s T e) + negPart (s T) C)) :
    ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e) := by
  intro S T hS hodd
  rcases hclass S T hS hodd with hpay | hnn | ⟨A, F, C, D, hsplit, hAD, hADF, hDC, hineq⟩
  · have hcut : ∑ e ∈ cutEdges S, e₀.restrict x₀ e ≤ 2 + η := by
      have h2 : cutSum (e₀.restrict x₀) S = cutSum x₀ S := cutSum_restrict hS.avoids
      have h := hS.nearMin.cut_le
      rw [cutSum] at h2
      linarith
    exact payment_of_pay hβ0 hxnn (hs T) hcut hpay
  · exact payment_of_nonneg hnn (hs' T)
  · exact payment_of_negPart hsplit hAD hADF hDC hineq (hs' T)

end TSPGap

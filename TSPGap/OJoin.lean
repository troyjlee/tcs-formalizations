/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Theorem52
import TSPGap.Tour
import TSPGap.Leaves
import TSPGap.Euler
import TSPGap.EdmondsJoin

/-!
# KKO22 §6.2: the O-join vector

Theorem 5.2 produces a slack vector; §6.2 turns it into a *tour*.  The step
this file formalizes is the polyhedral one: the vector

  `yₑ = xₑ/2 + sₑ + s*ₑ`  (and `y` big on the distinguished edge `e₀`)

is feasible for the O-join polyhedron of the tree's odd-degree vertices, and
its cost is below `c(x)/2` by a constant factor.  Feasibility splits exactly
as in KKO:

* a cut carrying `e₀` is paid for by `e₀` alone (KKO put `y_{e₀} = ∞`; since
  `c(e₀) = 0` the finite value `1` does the same work and keeps `c(y)` a real
  number);
* an `η`-near minimum cut is paid for by the slack pair, which is where
  Theorem 5.2 and its one-side-crossed companion enter;
* any other cut is paid for by `x` alone, because `x(δ(S)) ≥ 2 + η` and
  `β(4 + 2η) ≤ η`.

**The parity bridge.**  The O-join polyhedron quantifies over cuts with
`|S ∩ O|` odd, while §5 speaks of cuts the tree meets an odd number of times.
These agree by the handshake lemma modulo two, proved here
(`odd_cutEdges_inter_of_odd_inter_oddVerts`) — summing degrees over `S` counts
internal edges twice and cut edges once.

**No assumption left here.**  The max-entropy distribution (KKO22 §2.1) was declared
here as a `sorry`-tracked assumption until 2026-09-10; it is now proved in
`MaxEntropyExistence.lean` (`exists_maxEntropy_treeDist`), which imports this file for
`IsLambdaUniform` and `IsMaxEntropyLimit`.  Everything here is proved — including the
O-join half of Edmonds–Johnson, which was briefly declared here as well before being
derived from `edmondsJohnson_ojoin` (a box in `BlackBoxes.lean` until 2026-09-10, now
proved in `EdmondsJoin.lean`), and Euler's theorem in the form the
output layer consumes (`exists_spanning_closed_walk`), which was a declared assumption
here until 2026-09-06 and is now derived from `Euler.lean`.

KKO22 Theorem 6.1 used to be a fourth, declared here beside its derivation.
It is now proved, in `Theorem61.lean` — which has to sit below `TheoremB3.lean`
and therefore below this file, since Theorem B.3 is what it consumes.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η β : ℝ}

/-! ### Linearity of expectation

Three one-line facts, kept here so that `TreeDist.lean` need not be rebuilt. -/

namespace TreeDist

theorem expect_const (μ : TreeDist n x) (a : ℝ) :
    μ.expect (fun _ => a) = a := by
  rw [expect, ← Finset.sum_mul, μ.total, one_mul]

theorem expect_add (μ : TreeDist n x) (f g : Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => f T + g T) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add]
  rw [Finset.sum_add_distrib]

theorem expect_mul_left (μ : TreeDist n x) (a : ℝ)
    (f : Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => a * f T) = a * μ.expect f := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem expect_sum (μ : TreeDist n x) (F : Finset (Sym2 (Fin n)))
    (f : Sym2 (Fin n) → Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => ∑ e ∈ F, f e T) = ∑ e ∈ F, μ.expect (fun T => f e T) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

end TreeDist

/-! ### Degrees, odd vertices and joins -/

open Classical in
/-- The degree of a vertex in an edge set. -/
noncomputable def degreeIn (F : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (F.filter fun e => v ∈ e).card

open Classical in
/-- The odd-degree vertices of an edge set — KKO's `O`. -/
noncomputable def oddVerts (F : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => Odd (degreeIn F v)

/-- `J` is an **`O`-join**: its odd-degree vertices are exactly `O`. -/
def IsJoin (O : Finset (Fin n)) (J : Finset (Sym2 (Fin n))) : Prop :=
  oddVerts J = O

/-! ### The handshake, modulo two -/

/-- A cut is unchanged by complementation. -/
theorem cutEdges_compl (S : Finset (Fin n)) : cutEdges Sᶜ = cutEdges S := by
  ext e
  simp only [PolygonRep.mem_cutEdges_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Finset.mem_compl] at hu
    have hv' : v ∈ S := by
      by_contra h
      exact hv (Finset.mem_compl.mpr h)
    exact ⟨v, hv', u, hu, Sym2.eq_swap⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨v, Finset.mem_compl.mpr hv, u, ?_, Sym2.eq_swap⟩
    simp [hu]

open Classical in
/-- **An edge meets `S` in two, one or no endpoints** — and the middle case
is exactly membership in the cut. -/
theorem card_filter_mem_mod_two {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (he : ¬ e.IsDiag) :
    (S.filter fun v => v ∈ e).card % 2 = if e ∈ cutEdges S then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (by rw [h]; simp)
    have hfil : (S.filter fun v => v ∈ s(a, b))
        = S.filter (fun v => v = a ∨ v = b) := by
      refine Finset.filter_congr fun v _ => ?_
      simp [Sym2.mem_iff]
    rw [hfil]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · have hset : S.filter (fun v => v = a ∨ v = b) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => h.2, by rintro (rfl | rfl) <;> simp [ha, hb]⟩
      rw [hset, Finset.card_pair hab, if_neg]
      intro hmem
      obtain ⟨u, hu, w, hw, huw⟩ := PolygonRep.mem_cutEdges_iff.mp hmem
      rcases Sym2.eq_iff.mp huw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hw (h2 ▸ hb)
      · exact hw (h1 ▸ ha)
    · have hset : S.filter (fun v => v = a ∨ v = b) = {a} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hv, rfl | rfl⟩
          · rfl
          · exact absurd hv hb
        · rintro rfl
          exact ⟨ha, Or.inl rfl⟩
      rw [hset, Finset.card_singleton,
        if_pos (PolygonRep.mem_cutEdges_iff.mpr ⟨a, ha, b, hb, rfl⟩)]
    · have hset : S.filter (fun v => v = a ∨ v = b) = {b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hv, rfl | rfl⟩
          · exact absurd hv ha
          · rfl
        · rintro rfl
          exact ⟨hb, Or.inr rfl⟩
      rw [hset, Finset.card_singleton,
        if_pos (PolygonRep.mem_cutEdges_iff.mpr ⟨b, hb, a, ha, Sym2.eq_swap⟩)]
    · have hset : S.filter (fun v => v = a ∨ v = b) = ∅ := by
        ext v
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro hv (rfl | rfl)
        · exact ha hv
        · exact hb hv
      rw [hset, Finset.card_empty, if_neg]
      intro hmem
      obtain ⟨u, hu, w, hw, huw⟩ := PolygonRep.mem_cutEdges_iff.mp hmem
      rcases Sym2.eq_iff.mp huw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ha (h1 ▸ hu)
      · exact hb (h2 ▸ hu)

open Classical in
/-- A sum of naturals has the parity of the number of odd summands. -/
theorem sum_mod_two (S : Finset (Fin n)) (f : Fin n → ℕ) :
    (∑ v ∈ S, f v) % 2 = (S.filter fun v => f v % 2 = 1).card % 2 := by
  classical
  refine Finset.induction_on S (by simp) ?_
  intro a S' ha ih
  rw [Finset.sum_insert ha, Finset.filter_insert]
  by_cases h : f a % 2 = 1
  · rw [if_pos h, Finset.card_insert_of_notMem
      (fun hc => ha (Finset.mem_filter.mp hc).1)]
    omega
  · rw [if_neg h]
    omega

open Classical in
/-- **The handshake, modulo two.**  Summing degrees over `S` counts the edges
inside `S` twice and the edges of the cut once. -/
theorem sum_degreeIn_mod_two (S : Finset (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∑ v ∈ S, degreeIn F v) % 2 = (cutEdges S ∩ F).card % 2 := by
  classical
  revert hF
  refine Finset.induction_on F (by simp [degreeIn]) ?_
  intro e F' he ih hF
  have ih' := ih fun a ha => hF a (Finset.mem_insert_of_mem ha)
  have hediag : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F')
  have hdeg : ∀ v, degreeIn (insert e F') v
      = degreeIn F' v + (if v ∈ e then 1 else 0) := by
    intro v
    simp only [degreeIn, Finset.filter_insert]
    by_cases hv : v ∈ e
    · rw [if_pos hv, Finset.card_insert_of_notMem
        (fun hc => he (Finset.mem_filter.mp hc).1), if_pos hv]
    · rw [if_neg hv, if_neg hv]
      simp
  have hsum1 : ∑ v ∈ S, (if v ∈ e then 1 else 0)
      = (S.filter fun v => v ∈ e).card := by
    rw [← Finset.sum_filter]
    simp
  have hsum : ∑ v ∈ S, degreeIn (insert e F') v
      = (∑ v ∈ S, degreeIn F' v) + (S.filter fun v => v ∈ e).card := by
    rw [Finset.sum_congr rfl fun v _ => hdeg v, Finset.sum_add_distrib, hsum1]
  have hcut : (cutEdges S ∩ insert e F').card
      = (cutEdges S ∩ F').card + (if e ∈ cutEdges S then 1 else 0) := by
    by_cases hce : e ∈ cutEdges S
    · have hins : cutEdges S ∩ insert e F' = insert e (cutEdges S ∩ F') := by
        ext f
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hf, rfl | hf'⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hf, hf'⟩
        · rintro (rfl | ⟨hf, hf'⟩)
          · exact ⟨hce, Or.inl rfl⟩
          · exact ⟨hf, Or.inr hf'⟩
      rw [hins, Finset.card_insert_of_notMem
        (fun hc => he (Finset.mem_inter.mp hc).2), if_pos hce]
    · have hins : cutEdges S ∩ insert e F' = cutEdges S ∩ F' := by
        ext f
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hf, rfl | hf'⟩
          · exact absurd hf hce
          · exact ⟨hf, hf'⟩
        · rintro ⟨hf, hf'⟩
          exact ⟨hf, Or.inr hf'⟩
      rw [hins, if_neg hce]
      omega
  have hkey := card_filter_mem_mod_two (S := S) hediag
  rw [hsum, hcut]
  by_cases hce : e ∈ cutEdges S
  · rw [if_pos hce] at hkey ⊢
    omega
  · rw [if_neg hce] at hkey ⊢
    omega

open Classical in
/-- **The parity bridge.**  If `S` meets the odd-degree vertices of `F` an
odd number of times, then `F` meets the cut `δ(S)` an odd number of times.
This is what identifies the O-join polyhedron's cuts with §5's. -/
theorem odd_cutEdges_inter_of_odd_inter_oddVerts {S : Finset (Fin n)}
    {F : Finset (Sym2 (Fin n))} (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (h : Odd (S ∩ oddVerts F).card) : Odd (cutEdges S ∩ F).card := by
  classical
  have hfil : S ∩ oddVerts F = S.filter fun v => degreeIn F v % 2 = 1 := by
    ext v
    simp only [Finset.mem_inter, oddVerts, Finset.mem_filter, Finset.mem_univ,
      true_and, Nat.odd_iff]
  rw [hfil, Nat.odd_iff] at h
  have h1 := sum_mod_two S (degreeIn F)
  have h2 := sum_degreeIn_mod_two S F hF
  rw [Nat.odd_iff]
  omega

open Classical in
/-- The odd-degree vertices are even in number — the handshake at `S = univ`,
where there is no cut. -/
theorem even_card_oddVerts (F : Finset (Sym2 (Fin n)))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) : Even (oddVerts F).card := by
  classical
  have hcut : cutEdges (Finset.univ : Finset (Fin n)) ∩ F = ∅ := by
    ext e
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hmem
    obtain ⟨u, -, w, hw, -⟩ := PolygonRep.mem_cutEdges_iff.mp hmem
    exact absurd (Finset.mem_univ w) hw
  have h1 := sum_mod_two (Finset.univ : Finset (Fin n)) (degreeIn F)
  have h2 := sum_degreeIn_mod_two (Finset.univ : Finset (Fin n)) F hF
  have hfil : (Finset.univ.filter fun v => degreeIn F v % 2 = 1) = oddVerts F := by
    ext v
    simp only [oddVerts, Finset.mem_filter, Finset.mem_univ, true_and, Nat.odd_iff]
  rw [hfil] at h1
  rw [hcut, Finset.card_empty] at h2
  rw [Nat.even_iff]
  omega

/-! ### The O-join polyhedron -/

/-- **The O-join polyhedron** (KKO22 (3)): nonnegative weights giving mass at
least one to every cut meeting `O` oddly. -/
def OJoinFeasible (O : Finset (Fin n)) (y : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧
    ∀ S : Finset (Fin n), Odd (S ∩ O).card → 1 ≤ ∑ e ∈ cutEdges S, y e

open Classical in
/-- **KKO's `y`** (§6.2): half the LP point, corrected by the slack vectors,
and paying for the distinguished edge outright.  KKO write `y_{e₀} = ∞`;
since `c(e₀) = 0`, the value `1` buys exactly the same cuts at the same
(zero) price, and keeps `c(y)` finite. -/
noncomputable def ojoinVec (e₀ : RootEdge n) (x₀ : Sym2 (Fin n) → ℝ)
    (s s' : Sym2 (Fin n) → ℝ) : Sym2 (Fin n) → ℝ :=
  fun e => if e = e₀.edge then 1 else e₀.restrict x₀ e / 2 + s e + s' e

/-- **Feasibility of `y`** — KKO22 §6.2's case analysis.  The three cases are
the distinguished edge, the near-minimum cuts (where the slack pair works),
and everything else (where `x(δ(S)) ≥ 2 + η` alone suffices, because
`β(4 + 2η) ≤ η`). -/
theorem ojoinFeasible_of_slack {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) {T : Finset (Sym2 (Fin n))}
    (hT : ∀ e ∈ T, ¬ e.IsDiag) {s s' : Sym2 (Fin n) → ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1) (hβ0 : 0 ≤ β) (hβη : β * (4 + 2 * η) ≤ η)
    (hs : ∀ e, -(β * e₀.restrict x₀ e) ≤ s e) (hs' : ∀ e, 0 ≤ s' e)
    (hsat : ∀ S : Finset (Fin n), IsRootedNearMinCut e₀ x₀ η S →
      Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, (s e + s' e)) :
    OJoinFeasible (oddVerts T) (ojoinVec e₀ x₀ s s') := by
  classical
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  have hβhalf : β ≤ 1 / 2 := by nlinarith
  -- nonnegativity
  have hynn : ∀ e, 0 ≤ ojoinVec e₀ x₀ s s' e := by
    intro e
    rw [ojoinVec]
    split
    · norm_num
    · have h1 := hs e
      have h2 := hs' e
      have h3 := hxnn e
      nlinarith
  refine ⟨hynn, ?_⟩
  -- the cut condition, first for cuts avoiding the distinguished edge
  have key : ∀ S : Finset (Fin n), AvoidsRootEdge e₀ S →
      Odd (S ∩ oddVerts T).card → 1 ≤ ∑ e ∈ cutEdges S, ojoinVec e₀ x₀ s s' e := by
    intro S havoid hodd
    have hne : S.Nonempty := by
      rcases Finset.eq_empty_or_nonempty S with rfl | h
      · rw [Finset.empty_inter, Finset.card_empty] at hodd
        exact absurd hodd (by decide)
      · exact h
    have hnu : S ≠ Finset.univ := by
      rintro rfl
      exact havoid.1 (Finset.mem_univ _)
    have he₀ : e₀.edge ∉ cutEdges S := RootEdge.edge_notMem_cutEdges havoid
    have hy : ∀ e ∈ cutEdges S,
        ojoinVec e₀ x₀ s s' e = e₀.restrict x₀ e / 2 + (s e + s' e) := by
      intro e he
      have hne' : e ≠ e₀.edge := fun h => he₀ (h ▸ he)
      rw [ojoinVec, if_neg hne']
      ring
    have hsplit : ∑ e ∈ cutEdges S, ojoinVec e₀ x₀ s s' e
        = cutSum x₀ S / 2 + ∑ e ∈ cutEdges S, (s e + s' e) := by
      rw [Finset.sum_congr rfl hy, Finset.sum_add_distrib, ← Finset.sum_div,
        ← cutSum, cutSum_restrict havoid]
    have hlp : 2 ≤ cutSum x₀ S := hx₀.2.2 S hne hnu
    by_cases hnear : IsNearMinCut x₀ η S
    · -- a near minimum cut: the slack pair pays for it
      have := hsat S ⟨hnear, havoid⟩
        (odd_cutEdges_inter_of_odd_inter_oddVerts hT hodd)
      rw [hsplit]
      linarith
    · -- not near minimum: the LP point alone pays for it
      have hbig : 2 + η ≤ cutSum x₀ S := by
        by_contra hcon
        exact hnear ⟨hne, hnu, le_of_lt (by linarith)⟩
      have hlow : -(β * cutSum x₀ S) ≤ ∑ e ∈ cutEdges S, (s e + s' e) := by
        have hstep : ∀ e ∈ cutEdges S,
            -(β * e₀.restrict x₀ e) ≤ s e + s' e := by
          intro e _
          have h1 := hs e
          have h2 := hs' e
          linarith
        have h1 : ∑ e ∈ cutEdges S, -(β * e₀.restrict x₀ e)
            = -(β * cutSum (e₀.restrict x₀) S) := by
          rw [cutSum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        rw [cutSum_restrict havoid] at h1
        rw [← h1]
        exact Finset.sum_le_sum hstep
      rw [hsplit]
      nlinarith
  -- the general cut, reduced to the avoiding case
  intro S hodd
  by_cases hmem : e₀.edge ∈ cutEdges S
  · have hone : (1 : ℝ) = ojoinVec e₀ x₀ s s' e₀.edge := by rw [ojoinVec, if_pos rfl]
    rw [hone]
    exact Finset.single_le_sum (f := ojoinVec e₀ x₀ s s') (fun e _ => hynn e) hmem
  · -- the endpoints of `e₀` are on the same side; orient `S` away from them
    have hsame : (e₀.u₀ ∈ S ∧ e₀.v₀ ∈ S) ∨ (e₀.u₀ ∉ S ∧ e₀.v₀ ∉ S) := by
      by_cases hu : e₀.u₀ ∈ S <;> by_cases hv : e₀.v₀ ∈ S
      · exact Or.inl ⟨hu, hv⟩
      · exact absurd (PolygonRep.mem_cutEdges_iff.mpr ⟨e₀.u₀, hu, e₀.v₀, hv, rfl⟩) hmem
      · exact absurd (PolygonRep.mem_cutEdges_iff.mpr
          ⟨e₀.v₀, hv, e₀.u₀, hu, Sym2.eq_swap⟩) hmem
      · exact Or.inr ⟨hu, hv⟩
    rcases hsame with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · -- both endpoints inside: pass to the complement
      have havoid : AvoidsRootEdge e₀ Sᶜ :=
        ⟨by simp [hu], by simp [hv]⟩
      have hpar : (S ∩ oddVerts T).card + (Sᶜ ∩ oddVerts T).card
          = (oddVerts T).card := by
        have h := Finset.card_filter_add_card_filter_not
          (s := oddVerts T) (p := fun v => v ∈ S)
        have e1 : (oddVerts T).filter (fun v => v ∈ S) = S ∩ oddVerts T := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_inter]
          exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
        have e2 : (oddVerts T).filter (fun v => ¬ v ∈ S) = Sᶜ ∩ oddVerts T := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_compl]
          exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
        rw [e1, e2] at h
        exact h
      have heven := even_card_oddVerts T hT
      have hodd' : Odd (Sᶜ ∩ oddVerts T).card := by
        rw [Nat.odd_iff] at hodd ⊢
        rw [Nat.even_iff] at heven
        omega
      have := key Sᶜ havoid hodd'
      rwa [cutEdges_compl] at this
    · exact key S ⟨hu, hv⟩ hodd

/-! ### Two facts about tree distributions

Both belong in `TreeDist.lean`; they are developed here to keep the build
cheap, and can move in a cleanup pass. -/

namespace TreeDist

open Classical in
/-- **KKO22 Fact 2.3**, the cost form of the marginal identity: the expected
cost of the tree is the `x`-cost of the edge set. -/
theorem expect_sum_eq (μ : TreeDist n x) (c : Sym2 (Fin n) → ℝ) :
    μ.expect (fun T => ∑ e ∈ T, c e) = ∑ e ∈ edgeFinset n, c e * x e := by
  classical
  have key : ∀ T : Finset (Sym2 (Fin n)),
      μ.prob T * (∑ e ∈ T, c e)
        = ∑ e ∈ edgeFinset n, (if e ∈ T then μ.prob T * c e else 0) := by
    intro T
    by_cases hp : μ.prob T = 0
    · simp [hp]
    · have hT := μ.support_spanningTree T hp
      have hsub : T ⊆ edgeFinset n := fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ e, hT.1 e he⟩
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr hsub, Finset.mul_sum]
  rw [expect, Finset.sum_congr rfl fun T _ => key T, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← μ.marginals e he, Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun T _ => by
    by_cases h : e ∈ T <;> simp [h, mul_comm]

/-- **The probabilistic method**: some tree of the support is at most
average. -/
theorem exists_le_expect (μ : TreeDist n x) (f : Finset (Sym2 (Fin n)) → ℝ) :
    ∃ T : Finset (Sym2 (Fin n)), μ.prob T ≠ 0 ∧ f T ≤ μ.expect f := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨T₀, hT₀⟩ : ∃ T : Finset (Sym2 (Fin n)), μ.prob T ≠ 0 := by
    by_contra h
    push_neg at h
    have := μ.total
    rw [Finset.sum_congr rfl fun T _ => h T, Finset.sum_const_zero] at this
    exact zero_ne_one this
  have hlt : ∑ T : Finset (Sym2 (Fin n)), μ.prob T * μ.expect f
      < ∑ T : Finset (Sym2 (Fin n)), μ.prob T * f T := by
    refine Finset.sum_lt_sum (fun T _ => ?_) ⟨T₀, Finset.mem_univ T₀, ?_⟩
    · rcases eq_or_ne (μ.prob T) 0 with h | h
      · rw [h, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hcon T h)) (μ.prob_nonneg T)
    · exact mul_lt_mul_of_pos_left (hcon T₀ hT₀)
        (lt_of_le_of_ne (μ.prob_nonneg T₀) (Ne.symm hT₀))
  rw [← Finset.sum_mul, μ.total, one_mul] at hlt
  exact lt_irrefl _ (lt_of_le_of_lt (le_of_eq (by rw [expect])) hlt)

end TreeDist

/-! ### The max-entropy interface

The precise Lean interface the assembly consumes for the max-entropy distribution
(KKO22 §2.1, [SV19]): `IsLambdaUniform` and `IsMaxEntropyLimit`.  The existence theorem
was declared here until 2026-09-10 and is now proved in `MaxEntropyExistence.lean`; Euler's
theorem, declared here until 2026-09-06, is derived from `Euler.lean`.

`epsP`, `IsLambdaUniform` and `IsMaxEntropyLimit` are here rather than in
`Theorem61.lean` because the Main Payment Theorem's statement needs them and
`TheoremB3.lean` imports this file. -/

/-! #### A spanning tree through a given edge

Needed only to refute the λ-uniform interface below: over the restricted
marginals the distinguished edge has marginal zero, so no tree containing it
can have positive probability — while a λ-uniform measure with positive weights
gives *every* spanning tree positive probability.  The star at `u₀` is such a
tree. -/

open Classical in
/-- The **star** at `u`: every edge from `u` to another vertex. -/
noncomputable def starTree (u : Fin n) : Finset (Sym2 (Fin n)) :=
  (Finset.univ.erase u).image fun v => s(u, v)

theorem mem_starTree {u v : Fin n} (h : v ≠ u) : s(u, v) ∈ starTree u := by
  classical
  exact Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨h, Finset.mem_univ v⟩, rfl⟩

/-- The star is a spanning tree: `n − 1` non-loop edges, and every vertex is a
step from its centre. -/
theorem starTree_isSpanningTree (hn : 2 ≤ n) (u : Fin n) :
    IsSpanningTree n (starTree u) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    rw [Sym2.mk_isDiag_iff]
    exact fun hc => (Finset.mem_erase.mp hv).1 hc.symm
  · have hinj : Set.InjOn (fun v => s(u, v))
        ((Finset.univ.erase u : Finset (Fin n)) : Set (Fin n)) := by
      intro a ha b _ hab
      rcases Sym2.eq_iff.mp hab with ⟨-, h⟩ | ⟨-, h2⟩
      · exact h
      · exact absurd h2 (Finset.mem_erase.mp (Finset.mem_coe.mp ha)).1
    rw [starTree, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
  · have hadj : ∀ v : Fin n, v ≠ u →
        (SimpleGraph.fromEdgeSet ((starTree u : Finset (Sym2 (Fin n))) :
          Set (Sym2 (Fin n)))).Adj u v := by
      intro v hv
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr (mem_starTree hv), fun hc => hv hc.symm⟩
    have hreach : ∀ v : Fin n,
        (SimpleGraph.fromEdgeSet ((starTree u : Finset (Sym2 (Fin n))) :
          Set (Sym2 (Fin n)))).Reachable u v := by
      intro v
      rcases eq_or_ne v u with rfl | hv
      · exact SimpleGraph.Reachable.refl _
      · exact (hadj v hv).reachable
    haveI : Nonempty (Fin n) := ⟨u⟩
    exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

/-- A **λ-uniform** spanning-tree distribution (KKO22 §2.1): the probability
of a tree is proportional to the product of `λ` over its edges.  The
max-entropy distribution *in the interior* of the spanning-tree polytope is of
this form, and KKO21's strongly-Rayleigh machinery is stated for it. -/
def IsLambdaUniform {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) : Prop :=
  ∃ lam : Sym2 (Fin n) → ℝ, (∀ e, 0 < lam e) ∧ ∃ Z : ℝ, 0 < Z ∧
    ∀ T : Finset (Sym2 (Fin n)), IsSpanningTree n T →
      μ.prob T = (∏ e ∈ T, lam e) / Z

/-- KKO22's `ε_P` (their Eq. (35)), the constant the hierarchy's slack vector
gains on every edge: `ε_P = (ε₁/6)(τ/β)p`.

⚠️⚠️ **`2.5·10⁻¹⁸`, not KKO's `3.12·10⁻¹⁶`.**  Their value is computed at
`p = 0.005ε₂²`, while this development carries the *repaired* `p = 0.00004ε₂²`
— Theorem 5.28's constant, see `Lemma522` — which is smaller by a factor of
`125`.  At `ε₂ = 0.0002`, `τ = 0.571β` and `ε₁ = ε₂/12`, `§7`'s top saving is

`p·τ·(ε₁/6) = 1.6·10⁻¹² · 0.571 · (1/360000) = 2.537777…·10⁻¹⁸`

per unit of `β·xₑ`, so `3.12·10⁻¹⁶` is **unattainable** here and `2.5·10⁻¹⁸` is
what Lemma 7.2 can deliver, with 1.5% to spare.  `kkoEps` drops with it. -/
noncomputable def epsP : ℝ := 2.5e-18

theorem epsP_pos : 0 < epsP := by unfold epsP; norm_num

/-- ⚠️ **No distribution with the restricted marginals is λ-uniform.**

`e₀.restrict x₀` gives the distinguished edge marginal zero, so every tree in
the support avoids it (`rootEdge_notMem_of_prob`).  A λ-uniform measure with
strictly positive weights, on the other hand, gives *every* spanning tree
positive probability — and the star at `u₀` is a spanning tree containing `e₀`.

So the assumption `∃ μ, IsLambdaUniform μ` that this file used to declare was
**false as stated**, in the same way `polygonRep_exists` was over unrooted
components (`Rooted.lean`).  Allowing zero weights does not repair it either:
`e₀.restrict x₀` lies on a face of the spanning-tree polytope, and KKO21 record
that an exact λ-uniform representation need not exist there.  What they use is
a *limit* of λ-uniform distributions, which is `IsMaxEntropyLimit` below. -/
theorem not_isLambdaUniform (hn : 2 ≤ n) {x₀ : Sym2 (Fin n) → ℝ}
    {e₀ : RootEdge n} (μ : TreeDist n (e₀.restrict x₀)) : ¬ IsLambdaUniform μ := by
  rintro ⟨lam, hlam, Z, hZ, hrep⟩
  have hmem : e₀.edge ∈ starTree e₀.u₀ := mem_starTree (Ne.symm e₀.ne)
  have hpos : 0 < μ.prob (starTree e₀.u₀) := by
    rw [hrep _ (starTree_isSpanningTree hn e₀.u₀)]
    exact div_pos (Finset.prod_pos fun e _ => hlam e) hZ
  exact rootEdge_notMem_of_prob μ (ne_of_gt hpos) hmem

/-- **The max-entropy distribution, as a limit** (KKO22 §2.1, [SV19]).

On the boundary of the spanning-tree polytope an exact λ-uniform representation
need not exist, and over `e₀.restrict x₀` it provably does not
(`not_isLambdaUniform`).  What KKO21 actually consume is that `μ` is a limit of
λ-uniform distributions: on a finite sample space weak convergence *is*
pointwise convergence of the probabilities, and both the strongly-Rayleigh
property and the conditioning identities of KKO21 Fact 2.8 are closed
conditions, so they pass to the limit.

The approximants are allowed their own marginals `y`; that is the point, since
the marginals of a λ-uniform distribution can never sit on the face. -/
def IsMaxEntropyLimit {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (y : Sym2 (Fin n) → ℝ) (ν : TreeDist n y),
    IsLambdaUniform ν ∧ ∀ T : Finset (Sym2 (Fin n)), |ν.prob T - μ.prob T| ≤ δ

/-- **Why the limit notion suffices.**  Any property of the probability vector
closed under pointwise limits — strong Rayleigh and Fact 2.8's conditioning
identities are both of that kind — transfers from the λ-uniform approximants to
`μ` itself.  Milestone 5's obligation is exactly to supply `hclosed` for the
two properties KKO21 use. -/
theorem IsMaxEntropyLimit.of_closed {x : Sym2 (Fin n) → ℝ} {μ : TreeDist n x}
    (h : IsMaxEntropyLimit μ) {P : (Finset (Sym2 (Fin n)) → ℝ) → Prop}
    (hclosed : ∀ f : Finset (Sym2 (Fin n)) → ℝ,
      (∀ δ : ℝ, 0 < δ → ∃ g, P g ∧ ∀ T, |g T - f T| ≤ δ) → P f)
    (hP : ∀ {y : Sym2 (Fin n) → ℝ} (ν : TreeDist n y), IsLambdaUniform ν → P ν.prob) :
    P μ.prob :=
  hclosed μ.prob fun δ hδ => by
    obtain ⟨y, ν, hν, hclose⟩ := h δ hδ
    exact ⟨ν.prob, hP ν hν, hclose⟩

/-! The max-entropy distribution — KKO22 §2.1 with Fact 2.2: the restricted LP point lies in
the spanning-tree polytope, and a distribution with those marginals exists as a limit of
λ-uniform distributions — is `exists_maxEntropy_treeDist`, proved in
`MaxEntropyExistence.lean` from Edmonds' theorem (`EdmondsTree.lean`) and the
exponential-family limit (`ExpFamilyLimit.lean`).  Until 2026-09-10 it was an assumption
here. -/



/-- **Edmonds–Johnson (KKO22 Proposition 2.4), in the form §6.2 consumes.**  A
feasible point of the O-join polyhedron dominates the cost of an actual join.

This was declared as a fourth assumption here, duplicating
`edmondsJohnson_ojoin` (then a box in `BlackBoxes.lean`, proved in `EdmondsJoin.lean`
since 2026-09-10).  It is not an assumption: the two statements
differ only in how "join" is spelled — `oddVerts J = O` against
`∀ v, v ∈ O ↔ Odd (degIn J v)` — and on an edge set with no loops `degIn` and
`degreeIn` are the same filter. -/
theorem exists_join_le_of_feasible {c : Sym2 (Fin n) → ℝ} (hc : ∀ e, 0 ≤ c e)
    {O : Finset (Fin n)} (hO : Even O.card) {y : Sym2 (Fin n) → ℝ}
    (hy : OJoinFeasible O y) :
    ∃ J : Finset (Sym2 (Fin n)), (∀ e ∈ J, ¬ e.IsDiag) ∧ IsJoin O J ∧
      ∑ e ∈ J, c e ≤ ∑ e ∈ edgeFinset n, c e * y e := by
  classical
  obtain ⟨J, hJdiag, hJodd, hJcost⟩ :=
    edmondsJohnson_ojoin hc O hO hy.1 (fun S hS => hy.2 S hS)
  refine ⟨J, hJdiag, ?_, hJcost⟩
  have hdeg : ∀ v : Fin n, degIn J v = degreeIn J v := by
    intro v
    rw [degIn, degreeIn]
    exact congrArg Finset.card
      (Finset.filter_congr fun e he => by simp [hJdiag e he])
  ext v
  rw [oddVerts, Finset.mem_filter]
  exact ⟨fun h => (hJodd v).mpr (by rw [hdeg]; exact h.2),
    fun h => ⟨Finset.mem_univ v, by rw [← hdeg]; exact (hJodd v).mp h⟩⟩

/-- **Euler's theorem**, in the form the O-join argument consumes: a connected
multigraph with even degrees has a closed walk through every vertex whose cost
is the total cost of its edges — here the spanning tree together with a join.
Proved in `Euler.lean` (`exists_spanning_closed_walk_core`) for edge multisets;
`degreeIn T v + degreeIn J v` is the multiset degree of `T ⊎ J`. -/
theorem exists_spanning_closed_walk {c : Sym2 (Fin n) → ℝ}
    {T J : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    (hJ : ∀ e ∈ J, ¬ e.IsDiag)
    (heven : ∀ v : Fin n, Even (degreeIn T v + degreeIn J v)) :
    ∃ (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v),
      (∀ u : Fin n, u ∈ W.support) ∧
      tourCost c W ≤ (∑ e ∈ T, c e) + ∑ e ∈ J, c e := by
  classical
  have hconv : ∀ v : Fin n, mdeg (T.val + J.val) v = degreeIn T v + degreeIn J v := by
    intro v
    rw [mdeg_add]
    unfold mdeg degreeIn
    rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val]
  exact exists_spanning_closed_walk_core hT hJ (fun v => by rw [hconv]; exact heven v)

end TSPGap

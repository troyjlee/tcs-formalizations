/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BadEvents

/-!
# From Lemma 5.4 to the per-polygon count of four

KKO22 Lemma 5.4 is a *pairwise exclusion*, not a count:

> Let `p, q` be two polygon points such that `e = {a, b}` and
> `a ∈ L(p) ∩ L(q)`.  Then `e ∉ E(B→(p)) ∩ E(B→(q))`.

The count `4` that Theorem 5.2's `hdeg` needs is `2 + 2`, and this file is
the step from one to the other.

The mechanism is worth stating plainly, because it is the whole reason the
constant is four.  An edge charged by the right event at `p` has **one**
endpoint inside `L(p)^∩R` and the other outside it (that is what
`betweenEdges` means), and `L(p)^∩R ⊆ L(p)`.  So a charging point comes with
a distinguished endpoint of `e`.  Lemma 5.4 says two distinct points cannot
distinguish the *same* endpoint.  An edge has two endpoints, so at most two
points charge it on the right — and symmetrically two on the left.

`card_le_two_of_witness` isolates exactly that argument with the exclusion
as a hypothesis, and `card_rightCharging_le_two_of_polygon` closes the loop:
it discharges the exclusion from the assembled Lemma 5.4
(`PolygonRep.lemma54_right`), leaving only the per-point geometric data.
-/

namespace TSPGap

variable {n : ℕ}

/-- **Two endpoints, so at most two charging points.**

Each `p ∈ s` has a witness set `X p` containing an endpoint of the edge, and
distinct points have disjoint witness sets.  The map sending `p` to its
endpoint is then injective into a two-element set. -/
theorem card_le_two_of_witness {α : Type*} {s : Finset α}
    {X : α → Finset (Fin n)} {u v : Fin n}
    (hw : ∀ p ∈ s, u ∈ X p ∨ v ∈ X p)
    (hdisj : ∀ p ∈ s, ∀ q ∈ s, ∀ w, (w = u ∨ w = v) →
      w ∈ X p → w ∈ X q → p = q) :
    s.card ≤ 2 := by
  classical
  have hmem : ∀ p ∈ s, (if u ∈ X p then u else v) ∈ X p := by
    intro p hp
    by_cases h : u ∈ X p
    · rwa [if_pos h]
    · rw [if_neg h]
      exact (hw p hp).resolve_left h
  have key : s.card ≤ ({u, v} : Finset (Fin n)).card := by
    refine Finset.card_le_card_of_injOn (fun p => if u ∈ X p then u else v)
      (fun p _ => ?_) (fun p hp q hq hpq => ?_)
    · by_cases h : u ∈ X p
      · simp [h]
      · simp [h]
    · have hbeta : (if u ∈ X p then u else v) = (if u ∈ X q then u else v) := hpq
      refine hdisj p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) _ ?_
        (hmem p (Finset.mem_coe.mp hp))
        (by rw [hbeta]; exact hmem q (Finset.mem_coe.mp hq))
      by_cases h : u ∈ X p
      · exact Or.inl (if_pos h)
      · exact Or.inr (if_neg h)
  exact key.trans ((Finset.card_insert_le _ _).trans (by simp))

/-- An edge of `betweenEdges A B` has an endpoint in `A`. -/
theorem mem_left_of_mem_betweenEdges {A B : Finset (Fin n)} {u v : Fin n}
    (h : s(u, v) ∈ betweenEdges A B) : u ∈ A ∨ v ∈ A := by
  obtain ⟨a, ha, b, _, hab⟩ := (Finset.mem_filter.mp h).2
  rcases Sym2.eq_iff.mp hab.symm with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl (h1 ▸ ha)
  · exact Or.inr (h1 ▸ ha)

/-- With disjoint sides, the endpoint opposite one in `A` lies in `B`. -/
theorem mem_right_of_mem_betweenEdges {A B : Finset (Fin n)} {u v : Fin n}
    (hd : Disjoint A B) (h : s(u, v) ∈ betweenEdges A B) (hu : u ∈ A) :
    v ∈ B := by
  obtain ⟨a, ha, b, hb, hab⟩ := (Finset.mem_filter.mp h).2
  rcases Sym2.eq_iff.mp hab.symm with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact h2 ▸ hb
  · exact absurd (h2 ▸ hb) (Finset.disjoint_left.mp hd hu)

/-- **At most two polygon points charge an edge on the right.**

`X p` is `L(p)^∩R ∖ L*(p)`, the inner side of `E(B→(p))`; `hexcl` is KKO22
Lemma 5.4, in the form its proof delivers — two points sharing a vertex of
that set are equal.

The shared vertex is required to be an **endpoint of the charged edge**
(`w = u ∨ w = v`).  Lemma 5.4 is only about that case, and the witness this
argument produces always is one, so nothing is lost; demanding equality from
an arbitrary shared vertex would be asking for more than KKO prove. -/
theorem card_rightCharging_le_two {α : Type*} {s : Finset α}
    {L LR Lstar : α → Finset (Fin n)} {u v : Fin n}
    (hcharge : ∀ p ∈ s, s(u, v) ∈ badEdgesRight (L p) (LR p) (Lstar p))
    (hexcl : ∀ p ∈ s, ∀ q ∈ s, ∀ w, (w = u ∨ w = v) →
      w ∈ (L p ∩ LR p) \ Lstar p → w ∈ (L q ∩ LR q) \ Lstar q → p = q) :
    s.card ≤ 2 :=
  card_le_two_of_witness
    (fun p hp => mem_left_of_mem_betweenEdges (hcharge p hp)) hexcl

/-- **At most two polygon points charge an edge on the left** — the mirror. -/
theorem card_leftCharging_le_two {α : Type*} {s : Finset α}
    {R RL Rstar : α → Finset (Fin n)} {u v : Fin n}
    (hcharge : ∀ p ∈ s, s(u, v) ∈ badEdgesLeft (R p) (RL p) (Rstar p))
    (hexcl : ∀ p ∈ s, ∀ q ∈ s, ∀ w, (w = u ∨ w = v) →
      w ∈ (R p ∩ RL p) \ Rstar p → w ∈ (R q ∩ RL q) \ Rstar q → p = q) :
    s.card ≤ 2 :=
  card_le_two_of_witness
    (fun p hp => mem_left_of_mem_betweenEdges (hcharge p hp)) hexcl

/-- **The per-polygon count of four**, in the shape Theorem 5.2's `hlocal`
asks for: a set of bad events inside one polygon splits by direction, and
each side contributes at most two. -/
theorem card_le_four_of_split {β : Type*} {t : Finset β}
    {dir : β → Bool}
    (hR : (t.filter fun b => dir b = true).card ≤ 2)
    (hL : (t.filter fun b => dir b = false).card ≤ 2) :
    t.card ≤ 4 := by
  classical
  have hsplit : t = (t.filter fun b => dir b = true) ∪
      (t.filter fun b => dir b = false) := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, ← and_or_left]
    constructor
    · intro hb
      refine ⟨hb, ?_⟩
      cases dir b <;> simp
    · exact fun h => h.1
  calc t.card = ((t.filter fun b => dir b = true) ∪
        (t.filter fun b => dir b = false)).card := by rw [← hsplit]
    _ ≤ (t.filter fun b => dir b = true).card
          + (t.filter fun b => dir b = false).card := Finset.card_union_le _ _
    _ ≤ 4 := by omega

/-! ### Lemma 5.4 feeds the exclusion

The abstract `hexcl` of `card_rightCharging_le_two` is exactly what
`PolygonRep.lemma54_right` delivers, once the charged edge's *other*
endpoint is extracted: the two sides of `badEdgesRight` are disjoint, so a
shared endpoint in the inner side forces the opposite endpoint into the
outer one, for both points at once. -/

namespace PolygonRep

variable {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
variable {𝒞 : Finset (Finset (Fin n))}

/-- **KKO22 Lemma 5.4**, in the contrapositive shape the counting uses: two
polygon points whose right bad events charge the same edge through a shared
inner endpoint are equal.  This is where the paper's omitted hypothesis
`p ≠ q` surfaces — the exclusion only ever bites for distinct points. -/
theorem eq_of_badEdgesRight_shared (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {p q : Fin P.m} {Lp Lq LpR LqR LpStar LqStar : Finset (Fin n)}
    (hLp : Lp ∈ 𝒞) (hLq : Lq ∈ 𝒞)
    (hrp : P.rightPoint Lp = p) (hrq : P.rightPoint Lq = q)
    (hLpR : P.IsSR Lp LpR) (hLqR : P.IsSR Lq LqR)
    (hLpStar : P.IsChosenLStar (Lp ∩ LpR) (P.start LpR) LpStar)
    (hLqStar : P.IsChosenLStar (Lq ∩ LqR) (P.start LqR) LqStar)
    {u v w : Fin n}
    (hcp : s(u, v) ∈ badEdgesRight Lp LpR LpStar)
    (hcq : s(u, v) ∈ badEdgesRight Lq LqR LqStar)
    (hw : w = u ∨ w = v)
    (hwp : w ∈ (Lp ∩ LpR) \ LpStar) (hwq : w ∈ (Lq ∩ LqR) \ LqStar) :
    p = q := by
  by_contra hne
  have hrne : P.rightPoint Lp ≠ P.rightPoint Lq := by
    rw [hrp, hrq]
    exact hne
  have hdp : Disjoint ((Lp ∩ LpR) \ LpStar) (LpR \ (Lp ∩ LpR)) :=
    Finset.disjoint_left.mpr fun t ht ht' =>
      (Finset.mem_sdiff.mp ht').2 (Finset.mem_sdiff.mp ht).1
  have hdq : Disjoint ((Lq ∩ LqR) \ LqStar) (LqR \ (Lq ∩ LqR)) :=
    Finset.disjoint_left.mpr fun t ht ht' =>
      (Finset.mem_sdiff.mp ht').2 (Finset.mem_sdiff.mp ht).1
  rcases hw with hwu | hwv
  · have hwpu : u ∈ (Lp ∩ LpR) \ LpStar := hwu ▸ hwp
    have hwqu : u ∈ (Lq ∩ LqR) \ LqStar := hwu ▸ hwq
    exact P.lemma54_right hx hη0 hη hC hLp hLq hLpR hLqR hLpStar hLqStar
      hrne hwpu hwqu (mem_right_of_mem_betweenEdges hdp hcp hwpu)
      (mem_right_of_mem_betweenEdges hdq hcq hwqu)
  · have hwpv : v ∈ (Lp ∩ LpR) \ LpStar := hwv ▸ hwp
    have hwqv : v ∈ (Lq ∩ LqR) \ LqStar := hwv ▸ hwq
    have hcp' : s(v, u) ∈ badEdgesRight Lp LpR LpStar := by
      rwa [Sym2.eq_swap]
    have hcq' : s(v, u) ∈ badEdgesRight Lq LqR LqStar := by
      rwa [Sym2.eq_swap]
    exact P.lemma54_right hx hη0 hη hC hLp hLq hLpR hLqR hLpStar hLqStar
      hrne hwpv hwqv (mem_right_of_mem_betweenEdges hdp hcp' hwpv)
      (mem_right_of_mem_betweenEdges hdq hcq' hwqv)

/-- **At most two polygon points charge an edge on the right**, with the
abstract exclusion discharged by Lemma 5.4: only the per-point geometric
data remains. -/
theorem card_rightCharging_le_two_of_polygon (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {s : Finset (Fin P.m)} {L LR Lstar : Fin P.m → Finset (Fin n)}
    {u v : Fin n}
    (hmem : ∀ p ∈ s, L p ∈ 𝒞)
    (hright : ∀ p ∈ s, P.rightPoint (L p) = p)
    (hSR : ∀ p ∈ s, P.IsSR (L p) (LR p))
    (hstar : ∀ p ∈ s, P.IsChosenLStar (L p ∩ LR p) (P.start (LR p)) (Lstar p))
    (hcharge : ∀ p ∈ s, s(u, v) ∈ badEdgesRight (L p) (LR p) (Lstar p)) :
    s.card ≤ 2 :=
  card_rightCharging_le_two hcharge fun p hp q hq _w hw hwp hwq =>
    P.eq_of_badEdgesRight_shared hx hη0 hη hC (hmem p hp) (hmem q hq)
      (hright p hp) (hright q hq) (hSR p hp) (hSR q hq) (hstar p hp)
      (hstar q hq) (hcharge p hp) (hcharge q hq) hw hwp hwq

/-- **KKO22 Lemma 5.4, left version**, in the contrapositive shape the
counting uses — the mirror of `eq_of_badEdgesRight_shared`.  Here the
polygon points are the cuts' *left* points, which are literally the arc
starts, so the omitted `p ≠ q` hypothesis enters as distinct starts. -/
theorem eq_of_badEdgesLeft_shared (P : PolygonRep 𝒞) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {p q : Fin P.m} {Rp Rq RpL RqL RpStar RqStar : Finset (Fin n)}
    (hRp : Rp ∈ 𝒞) (hRq : Rq ∈ 𝒞)
    (hlp : P.leftPoint Rp = p) (hlq : P.leftPoint Rq = q)
    (hRpL : P.IsSL Rp RpL) (hRqL : P.IsSL Rq RqL)
    (hRpStar : P.IsChosenRStar (Rp ∩ RpL) (P.start Rp)
      (P.len RpL - (P.start Rp - P.start RpL).val) RpStar)
    (hRqStar : P.IsChosenRStar (Rq ∩ RqL) (P.start Rq)
      (P.len RqL - (P.start Rq - P.start RqL).val) RqStar)
    {u v w : Fin n}
    (hcp : s(u, v) ∈ badEdgesLeft Rp RpL RpStar)
    (hcq : s(u, v) ∈ badEdgesLeft Rq RqL RqStar)
    (hw : w = u ∨ w = v)
    (hwp : w ∈ (Rp ∩ RpL) \ RpStar) (hwq : w ∈ (Rq ∩ RqL) \ RqStar) :
    p = q := by
  by_contra hne
  have hrne : P.start Rp ≠ P.start Rq := by
    intro h
    refine hne ?_
    rw [← hlp, ← hlq]
    exact h
  have hdp : Disjoint ((Rp ∩ RpL) \ RpStar) (RpL \ (Rp ∩ RpL)) :=
    Finset.disjoint_left.mpr fun t ht ht' =>
      (Finset.mem_sdiff.mp ht').2 (Finset.mem_sdiff.mp ht).1
  have hdq : Disjoint ((Rq ∩ RqL) \ RqStar) (RqL \ (Rq ∩ RqL)) :=
    Finset.disjoint_left.mpr fun t ht ht' =>
      (Finset.mem_sdiff.mp ht').2 (Finset.mem_sdiff.mp ht).1
  rcases hw with hwu | hwv
  · have hwpu : u ∈ (Rp ∩ RpL) \ RpStar := hwu ▸ hwp
    have hwqu : u ∈ (Rq ∩ RqL) \ RqStar := hwu ▸ hwq
    exact P.lemma54_left hx hη0 hη hC hRp hRq hRpL hRqL hRpStar hRqStar
      hrne hwpu hwqu (mem_right_of_mem_betweenEdges hdp hcp hwpu)
      (mem_right_of_mem_betweenEdges hdq hcq hwqu)
  · have hwpv : v ∈ (Rp ∩ RpL) \ RpStar := hwv ▸ hwp
    have hwqv : v ∈ (Rq ∩ RqL) \ RqStar := hwv ▸ hwq
    have hcp' : s(v, u) ∈ badEdgesLeft Rp RpL RpStar := by
      rwa [Sym2.eq_swap]
    have hcq' : s(v, u) ∈ badEdgesLeft Rq RqL RqStar := by
      rwa [Sym2.eq_swap]
    exact P.lemma54_left hx hη0 hη hC hRp hRq hRpL hRqL hRpStar hRqStar
      hrne hwpv hwqv (mem_right_of_mem_betweenEdges hdp hcp' hwpv)
      (mem_right_of_mem_betweenEdges hdq hcq' hwqv)

/-- **At most two polygon points charge an edge on the left**, with the
abstract exclusion discharged by the left Lemma 5.4 — the mirror of
`card_rightCharging_le_two_of_polygon`. -/
theorem card_leftCharging_le_two_of_polygon (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {s : Finset (Fin P.m)} {R RL Rstar : Fin P.m → Finset (Fin n)}
    {u v : Fin n}
    (hmem : ∀ p ∈ s, R p ∈ 𝒞)
    (hleft : ∀ p ∈ s, P.leftPoint (R p) = p)
    (hSL : ∀ p ∈ s, P.IsSL (R p) (RL p))
    (hstar : ∀ p ∈ s, P.IsChosenRStar (R p ∩ RL p) (P.start (R p))
      (P.len (RL p) - (P.start (R p) - P.start (RL p)).val) (Rstar p))
    (hcharge : ∀ p ∈ s, s(u, v) ∈ badEdgesLeft (R p) (RL p) (Rstar p)) :
    s.card ≤ 2 :=
  card_leftCharging_le_two hcharge fun p hp q hq _w hw hwp hwq =>
    P.eq_of_badEdgesLeft_shared hx hη0 hη hC (hmem p hp) (hmem q hq)
      (hleft p hp) (hleft q hq) (hSL p hp) (hSL q hq) (hstar p hp)
      (hstar q hq) (hcharge p hp) (hcharge q hq) hw hwp hwq

/-- **The per-polygon count of four, at the event level** — the shape of
Theorem 5.2's `hlocal` for a single polygon.

`t` is a set of bad events charging the edge `{u, v}`, each carrying a
direction and its witness cuts, with at most one event per anchor point
and direction (`hRinj`, `hLinj`) — the invariant the bad-event index type
will provide by construction.  Lemma 5.4 bounds each direction by two
through the anchor points, and the directions split the set: `2 + 2`. -/
theorem card_badEvents_le_four_of_polygon (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {β : Type*} {t : Finset β} {u v : Fin n} {dir : β → Bool}
    {L LR Lstar R RL Rstar : β → Finset (Fin n)}
    (hRmem : ∀ b ∈ t, dir b = true → L b ∈ 𝒞)
    (hRSR : ∀ b ∈ t, dir b = true → P.IsSR (L b) (LR b))
    (hRstar : ∀ b ∈ t, dir b = true →
      P.IsChosenLStar (L b ∩ LR b) (P.start (LR b)) (Lstar b))
    (hRcharge : ∀ b ∈ t, dir b = true →
      s(u, v) ∈ badEdgesRight (L b) (LR b) (Lstar b))
    (hRinj : ∀ b ∈ t, ∀ b' ∈ t, dir b = true → dir b' = true →
      P.rightPoint (L b) = P.rightPoint (L b') → b = b')
    (hLmem : ∀ b ∈ t, dir b = false → R b ∈ 𝒞)
    (hLSL : ∀ b ∈ t, dir b = false → P.IsSL (R b) (RL b))
    (hLstar : ∀ b ∈ t, dir b = false →
      P.IsChosenRStar (R b ∩ RL b) (P.start (R b))
        (P.len (RL b) - (P.start (R b) - P.start (RL b)).val) (Rstar b))
    (hLcharge : ∀ b ∈ t, dir b = false →
      s(u, v) ∈ badEdgesLeft (R b) (RL b) (Rstar b))
    (hLinj : ∀ b ∈ t, ∀ b' ∈ t, dir b = false → dir b' = false →
      P.leftPoint (R b) = P.leftPoint (R b') → b = b') :
    t.card ≤ 4 := by
  classical
  refine card_le_four_of_split (dir := dir) ?_ ?_
  · refine card_rightCharging_le_two (L := L) (LR := LR) (Lstar := Lstar)
      (u := u) (v := v) ?_ ?_
    · intro b hb
      obtain ⟨hbt, hbd⟩ := Finset.mem_filter.mp hb
      exact hRcharge b hbt hbd
    · intro b hb b' hb' w hw hwb hwb'
      obtain ⟨hbt, hbd⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbt', hbd'⟩ := Finset.mem_filter.mp hb'
      exact hRinj b hbt b' hbt' hbd hbd'
        (P.eq_of_badEdgesRight_shared hx hη0 hη hC (hRmem b hbt hbd)
          (hRmem b' hbt' hbd') rfl rfl (hRSR b hbt hbd) (hRSR b' hbt' hbd')
          (hRstar b hbt hbd) (hRstar b' hbt' hbd') (hRcharge b hbt hbd)
          (hRcharge b' hbt' hbd') hw hwb hwb')
  · refine card_leftCharging_le_two (R := R) (RL := RL) (Rstar := Rstar)
      (u := u) (v := v) ?_ ?_
    · intro b hb
      obtain ⟨hbt, hbd⟩ := Finset.mem_filter.mp hb
      exact hLcharge b hbt hbd
    · intro b hb b' hb' w hw hwb hwb'
      obtain ⟨hbt, hbd⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbt', hbd'⟩ := Finset.mem_filter.mp hb'
      exact hLinj b hbt b' hbt' hbd hbd'
        (P.eq_of_badEdgesLeft_shared hx hη0 hη hC (hLmem b hbt hbd)
          (hLmem b' hbt' hbd') rfl rfl (hLSL b hbt hbd) (hLSL b' hbt' hbd')
          (hLstar b hbt hbd) (hLstar b' hbt' hbd') (hLcharge b hbt hbd)
          (hLcharge b' hbt' hbd') hw hwb hwb')

end PolygonRep

end TSPGap

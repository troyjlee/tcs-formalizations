import TSPGap.InsideAtoms
import TSPGap.TreeDist

/-!
# The bad events, concretely

Up to now KKO22's bad events `B→(p)`, `B←(p)` and their edge sets `E(B→(p))`,
`E(B←(p))` existed only in docstrings: §5's lemmas were stated about the
underlying objects (`arrowRight`, `arrowCirc`, and Lemma 5.6 in the generic
shape `X, Y, Z`), while `MainTheorem` took the bad events as an abstract
interface.  Nothing connected the two.

This file closes that gap for a single polygon.  It *defines* the events and
their edge sets, and then re-derives the two §5 inputs of Theorem 5.2 as
statements about those definitions:

* `probEvent_occursRight_le` / `probEvent_occursLeft_le` — Lemma 5.5, i.e.
  Theorem 5.2's `hprob`, for the concrete events;
* `one_sub_le_sum_badEdgesRight` / `..._badEdgesLeft` — Lemma 5.6, the heavy
  edge-set bound feeding Theorem 5.2's `hsat`.

Following KKO, `B→(p)` is read off the proof of Lemma 5.3: it is the failure
of what that proof assumes, namely that the tree meets `E→(L(p))` exactly once
and misses `E∘(L(p))` entirely.  The edge set is the one Lemma 5.6 measures,
`E(B→(p)) = E(L^∩R ∖ L*, L_R ∖ L^∩R)`.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
variable {𝒞 : Finset (Finset (Fin n))}

/-- A cut edge is a genuine (non-loop) edge. -/
theorem cutEdges_subset_edgeFinset (S : Finset (Fin n)) :
    cutEdges S ⊆ edgeFinset n := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (Finset.mem_filter.mp he).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hdiag
  rw [Sym2.mk_isDiag_iff] at hdiag
  subst hdiag
  exact (Finset.mem_compl.mp hv) hu

theorem arrowCirc_subset_cutEdges (S L R : Finset (Fin n)) :
    PolygonRep.arrowCirc S L R ⊆ cutEdges S := by
  rw [PolygonRep.arrowCirc]
  exact Finset.sdiff_subset.trans Finset.sdiff_subset

/-! ### The events -/

/-- **KKO22's bad event `B→(p)`**, with `L = L(p)`, `LL = L_L`, `LR = L_R`:
the tree fails to meet `E→(L)` exactly once, or meets `E∘(L)` at all.

This is exactly the negation of what the proof of Lemma 5.3 assumes when it
supposes `B→(p_r)` has *not* occurred. -/
def OccursRight (L LL LR : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  (PolygonRep.arrowRight L LR ∩ T).card ≠ 1 ∨
    (PolygonRep.arrowCirc L LL LR ∩ T).Nonempty

/-- **KKO22's bad event `B←(p)`**, with `R = R(p)`, `RL = R_L`, `RR = R_R`:
the mirror of `OccursRight`, with `E←` in place of `E→`. -/
def OccursLeft (R RL RR : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  (PolygonRep.arrowLeft R RL ∩ T).card ≠ 1 ∨
    (PolygonRep.arrowCirc R RL RR ∩ T).Nonempty

/-- **`E(B→(p))`**, the edge set charged when `B→(p)` occurs:
`E(L^∩R ∖ L*, L_R ∖ L^∩R)`, in the notation of Lemma 5.6. -/
def badEdgesRight (L LR Lstar : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  betweenEdges ((L ∩ LR) \ Lstar) (LR \ (L ∩ LR))

/-- **`E(B←(p))`**, the mirror edge set. -/
def badEdgesLeft (R RL Rstar : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  betweenEdges ((R ∩ RL) \ Rstar) (RL \ (R ∩ RL))

/-! ### Lemma 5.5 for the concrete events — Theorem 5.2's `hprob` -/

/-- **KKO22 Lemma 5.5** for `B→(p)` as defined above: the bad event has
probability at most `4.5η`.

The tree distribution has marginals `e₀.restrict x` — the restricted
vector, as in Theorem 5.2's statement — while the geometry stays over the
LP point `x`.  The `E∘` half is fully internal: `sum_arrowCirc_le'` gives
`x(E∘(L)) ≤ 2η`, the restricted mass is no larger
(`RootEdge.sum_restrict_le`), and Markov converts it.  The `E→` half is
Corollary 2.12, which enters as the hypothesis `hcor`, exactly as in KKO's
proof. -/
theorem probEvent_occursRight_le (μ : TreeDist n (e₀.restrict x))
    (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 5) (P : PolygonRep 𝒞) {L LL LR : Finset (Fin n)}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hL : L ∈ 𝒞) (hLL : LL ∈ 𝒞) (hLR : LR ∈ 𝒞)
    (hcL : P.CrossesOnLeft LL L) (hcR : P.CrossesOnRight LR L)
    (hcor : 1 - 2.5 * η
      ≤ μ.probEvent (fun T => (PolygonRep.arrowRight L LR ∩ T).card = 1)) :
    μ.probEvent (fun T => OccursRight L LL LR T) ≤ 4.5 * η :=
  μ.prob_badEvent_le_of_mass hcor
    ((arrowCirc_subset_cutEdges L LL LR).trans (cutEdges_subset_edgeFinset L))
    (le_trans (RootEdge.sum_restrict_le hx.1 _)
      (P.sum_arrowCirc_le' hx hη0 hη hC hL hLL hLR hcL hcR))

/-- **KKO22 Lemma 5.5** for `B←(p)`, the mirror. -/
theorem probEvent_occursLeft_le (μ : TreeDist n (e₀.restrict x))
    (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 5) (P : PolygonRep 𝒞) {R RL RR : Finset (Fin n)}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞) (hR : R ∈ 𝒞) (hRL : RL ∈ 𝒞) (hRR : RR ∈ 𝒞)
    (hcL : P.CrossesOnLeft RL R) (hcR : P.CrossesOnRight RR R)
    (hcor : 1 - 2.5 * η
      ≤ μ.probEvent (fun T => (PolygonRep.arrowLeft R RL ∩ T).card = 1)) :
    μ.probEvent (fun T => OccursLeft R RL RR T) ≤ 4.5 * η :=
  μ.prob_badEvent_le_of_mass hcor
    ((arrowCirc_subset_cutEdges R RL RR).trans (cutEdges_subset_edgeFinset R))
    (le_trans (RootEdge.sum_restrict_le hx.1 _)
      (P.sum_arrowCirc_le' hx hη0 hη hC hR hRL hRR hcL hcR))

/-! ### Lemma 5.6 for the concrete edge sets — the input to `hsat` -/

/-- **KKO22 Lemma 5.6** for `E(B→(p))` as defined above: the charged edge set
carries `x`-mass at least `1 − η`.  This is the generic lemma instantiated at
`X = L^∩R`, `Z = L*`, `Y = L_R`. -/
theorem one_sub_le_sum_badEdgesRight (hx : x ∈ subtourLP n)
    {L LR Lstar : Finset (Fin n)} (hZX : Lstar ⊆ L ∩ LR)
    (h1 : ((L ∩ LR) \ Lstar).Nonempty) (h1' : (L ∩ LR) \ Lstar ≠ Finset.univ)
    (h2 : (LR \ (L ∩ LR)).Nonempty) (h2' : LR \ (L ∩ LR) ≠ Finset.univ)
    (hnmc : IsNearMinCut x (2 * η) (LR \ Lstar)) :
    1 - η ≤ ∑ e ∈ badEdgesRight L LR Lstar, x e :=
  PolygonRep.one_sub_le_sum_badEdges hx hZX Finset.inter_subset_right h1 h1' h2 h2'
    hnmc

/-- **KKO22 Lemma 5.6** for `E(B←(p))`, the mirror. -/
theorem one_sub_le_sum_badEdgesLeft (hx : x ∈ subtourLP n)
    {R RL Rstar : Finset (Fin n)} (hZX : Rstar ⊆ R ∩ RL)
    (h1 : ((R ∩ RL) \ Rstar).Nonempty) (h1' : (R ∩ RL) \ Rstar ≠ Finset.univ)
    (h2 : (RL \ (R ∩ RL)).Nonempty) (h2' : RL \ (R ∩ RL) ≠ Finset.univ)
    (hnmc : IsNearMinCut x (2 * η) (RL \ Rstar)) :
    1 - η ≤ ∑ e ∈ badEdgesLeft R RL Rstar, x e :=
  PolygonRep.one_sub_le_sum_badEdges hx hZX Finset.inter_subset_right h1 h1' h2 h2'
    hnmc

/-! ### Lemma 5.3 for the concrete events — the "which event occurs" half of `hsat` -/

/-- **KKO22 Lemma 5.3** stated with the concrete events: if the tree does not
meet `δ(S)` exactly twice, then `B←(p_l)` or `B→(p_r)` occurs.

This is `bad_event_at_polygon_points` with its two `card ≠ 0` disjuncts read as
`Nonempty`, which is how the events are defined here. -/
theorem occurs_of_cut_card_ne_two {S L R SL SR LL LR RL RR : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))}
    (hinterLR : L ∩ R = S)
    (hEleft : PolygonRep.arrowLeft S SL = PolygonRep.arrowLeft R RL)
    (hEright : PolygonRep.arrowRight S SR = PolygonRep.arrowRight L LR)
    (hdS : Disjoint (SL \ S) (SR \ S))
    (hdL : Disjoint (LL \ L) (LR \ L)) (hdR : Disjoint (RL \ R) (RR \ R))
    (h427L : Disjoint (LL \ L) (R \ L)) (h427R : Disjoint (L \ R) (RR \ R))
    (hcor58 : Disjoint (PolygonRep.arrowLeft L LL) (PolygonRep.arrowRight R RR))
    (hT : (cutEdges S ∩ T).card ≠ 2) :
    OccursLeft R RL RR T ∨ OccursRight L LL LR T := by
  have h := PolygonRep.bad_event_at_polygon_points hinterLR hEleft hEright hdS
    hdL hdR h427L h427R hcor58 hT
  exact h.imp (fun hl => hl.imp id fun hc => Finset.card_pos.mp (Nat.pos_of_ne_zero hc))
    (fun hr => hr.imp id fun hc => Finset.card_pos.mp (Nat.pos_of_ne_zero hc))

/-! ### `E(B) ⊆ E←`, `E→` — the missing inclusion -/

theorem betweenEdges_mono {A A' B B' : Finset (Fin n)} (hA : A' ⊆ A)
    (hB : B' ⊆ B) : betweenEdges A' B' ⊆ betweenEdges A B := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hA hu, v, hB hv, rfl⟩

/-- **`E(B→(p)) ⊆ E→(p)`.**  The step Theorem 5.2's proof uses (with Lemma
5.1's `E→(p) = E→(S)`) to conclude `E(B) ⊆ δ(S)`.

Both sides shrink: `L^∩R ∖ L* ⊆ L ∩ L_R` outright, and `L_R ∖ L^∩R = L_R ∖ L`
because a vertex of `L_R` lies outside `L ∩ L_R` exactly when it lies outside
`L`.  So the charged edge set sits inside `E(L ∩ L_R, L_R ∖ L) = E→(L)`. -/
theorem badEdgesRight_subset_arrowRight (L LR Lstar : Finset (Fin n)) :
    badEdgesRight L LR Lstar ⊆ PolygonRep.arrowRight L LR := by
  rw [badEdgesRight, PolygonRep.arrowRight]
  refine betweenEdges_mono Finset.sdiff_subset ?_
  intro w hw
  rw [Finset.mem_sdiff] at hw ⊢
  exact ⟨hw.1, fun hL => hw.2 (Finset.mem_inter.mpr ⟨hL, hw.1⟩)⟩

/-- **`E(B←(p)) ⊆ E←(p)`**, the mirror. -/
theorem badEdgesLeft_subset_arrowLeft (R RL Rstar : Finset (Fin n)) :
    badEdgesLeft R RL Rstar ⊆ PolygonRep.arrowLeft R RL := by
  rw [badEdgesLeft, PolygonRep.arrowLeft]
  refine betweenEdges_mono Finset.sdiff_subset ?_
  intro w hw
  rw [Finset.mem_sdiff] at hw ⊢
  exact ⟨hw.1, fun hR => hw.2 (Finset.mem_inter.mpr ⟨hR, hw.1⟩)⟩

/-! ### `hsat`, assembled

Theorem 5.2's first hypothesis, now derived rather than assumed: from a cut
the tree meets other than twice, produce an occurring bad event whose charged
edges lie in `δ(S)` and carry `x`-mass at least `1 − η`.
-/

/-- **Theorem 5.2's `hsat`, for the concrete bad events.**

The three ingredients are Lemma 5.3 (`occurs_of_cut_card_ne_two`, which event
occurs), the inclusions above composed with Lemma 5.1's arrow equalities
(`E(B) ⊆ δ(S)`), and Lemma 5.6 (the `x`-mass).  The geometric hypotheses are
exactly Lemma 5.3's; the `h*L`/`h*R` groups are Lemma 5.6's, one per side. -/
theorem exists_occurring_badEvent (hx : x ∈ subtourLP n)
    {S L R SL SR LL LR RL RR Lstar Rstar : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))}
    (hinterLR : L ∩ R = S)
    (hEleft : PolygonRep.arrowLeft S SL = PolygonRep.arrowLeft R RL)
    (hEright : PolygonRep.arrowRight S SR = PolygonRep.arrowRight L LR)
    (hdS : Disjoint (SL \ S) (SR \ S))
    (hdL : Disjoint (LL \ L) (LR \ L)) (hdR : Disjoint (RL \ R) (RR \ R))
    (h427L : Disjoint (LL \ L) (R \ L)) (h427R : Disjoint (L \ R) (RR \ R))
    (hcor58 : Disjoint (PolygonRep.arrowLeft L LL) (PolygonRep.arrowRight R RR))
    (hT : (cutEdges S ∩ T).card ≠ 2)
    (hZXr : Lstar ⊆ L ∩ LR)
    (h1r : ((L ∩ LR) \ Lstar).Nonempty) (h1r' : (L ∩ LR) \ Lstar ≠ Finset.univ)
    (h2r : (LR \ (L ∩ LR)).Nonempty) (h2r' : LR \ (L ∩ LR) ≠ Finset.univ)
    (hnmcr : IsNearMinCut x (2 * η) (LR \ Lstar))
    (hZXl : Rstar ⊆ R ∩ RL)
    (h1l : ((R ∩ RL) \ Rstar).Nonempty) (h1l' : (R ∩ RL) \ Rstar ≠ Finset.univ)
    (h2l : (RL \ (R ∩ RL)).Nonempty) (h2l' : RL \ (R ∩ RL) ≠ Finset.univ)
    (hnmcl : IsNearMinCut x (2 * η) (RL \ Rstar)) :
    (OccursLeft R RL RR T ∧ badEdgesLeft R RL Rstar ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ badEdgesLeft R RL Rstar, x e) ∨
      (OccursRight L LL LR T ∧ badEdgesRight L LR Lstar ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ badEdgesRight L LR Lstar, x e) := by
  have hsubL : badEdgesLeft R RL Rstar ⊆ cutEdges S := by
    refine (badEdgesLeft_subset_arrowLeft R RL Rstar).trans ?_
    rw [← hEleft]
    exact PolygonRep.arrowLeft_subset_cut S SL
  have hsubR : badEdgesRight L LR Lstar ⊆ cutEdges S := by
    refine (badEdgesRight_subset_arrowRight L LR Lstar).trans ?_
    rw [← hEright]
    exact PolygonRep.arrowRight_subset_cut S SR
  rcases occurs_of_cut_card_ne_two hinterLR hEleft hEright hdS hdL hdR h427L
    h427R hcor58 hT with hl | hr
  · exact Or.inl ⟨hl, hsubL,
      one_sub_le_sum_badEdgesLeft hx hZXl h1l h1l' h2l h2l' hnmcl⟩
  · exact Or.inr ⟨hr, hsubR,
      one_sub_le_sum_badEdgesRight hx hZXr h1r h1r' h2r h2r' hnmcr⟩

/-- **`hsat` for the concrete events, with the geometry supplied by the
polygon.**

`exists_occurring_badEvent` takes six disjointness facts as parameters.  All
six are instances of results now proved outright, so given the polygon and
the `S_L`/`S_R` data they are discharged rather than assumed:

  * `hdS`, `hdL`, `hdR` — Lemma 4.27 at `S`, at `L`, at `R`;
  * `h427L` — Lemma 4.27 at `L`, with `R` as the right-crosser;
  * `h427R` — Lemma 4.27 at `R`, with `L` as the left-crosser (`R` crossing
    `L` on the right *is* `L` crossing `R` on the left: the arc condition is
    literally the same proposition, and the crossing is symmetrized);
  * `hcor58` — Corollary 5.8's second half, which since the generalization of
    Lemma 4.27 to almost diagonal central cuts is unconditional.

What remains as hypotheses here is genuinely elsewhere's work: `hinterLR` and
the two arrow equalities (Lemma 5.7 and Lemma 5.1), and Lemma 5.6's per-side
near-minimality data. -/
theorem exists_occurring_badEvent_of_polygon (P : PolygonRep 𝒞)
    (hx : x ∈ subtourLP n) (hη0 : 0 < η) (hη : η < 1 / 10)
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    {S L R SL SR LL LR RL RR Lstar Rstar : Finset (Fin n)}
    {T : Finset (Sym2 (Fin n))}
    (hS : S ∈ 𝒞) (hL : L ∈ 𝒞) (hR : R ∈ 𝒞)
    (hSL : P.IsSL S SL) (hSR : P.IsSR S SR)
    (hLL : P.IsSL L LL) (hLR : P.IsSR L LR)
    (hRL : P.IsSL R RL) (hRR : P.IsSR R RR)
    (hcR : P.CrossesOnRight R L)
    (hinterLR : L ∩ R = S)
    (hEleft : PolygonRep.arrowLeft S SL = PolygonRep.arrowLeft R RL)
    (hEright : PolygonRep.arrowRight S SR = PolygonRep.arrowRight L LR)
    (hT : (cutEdges S ∩ T).card ≠ 2)
    (hZXr : Lstar ⊆ L ∩ LR)
    (h1r : ((L ∩ LR) \ Lstar).Nonempty) (h1r' : (L ∩ LR) \ Lstar ≠ Finset.univ)
    (h2r : (LR \ (L ∩ LR)).Nonempty) (h2r' : LR \ (L ∩ LR) ≠ Finset.univ)
    (hnmcr : IsNearMinCut x (2 * η) (LR \ Lstar))
    (hZXl : Rstar ⊆ R ∩ RL)
    (h1l : ((R ∩ RL) \ Rstar).Nonempty) (h1l' : (R ∩ RL) \ Rstar ≠ Finset.univ)
    (h2l : (RL \ (R ∩ RL)).Nonempty) (h2l' : RL \ (R ∩ RL) ≠ Finset.univ)
    (hnmcl : IsNearMinCut x (2 * η) (RL \ Rstar)) :
    (OccursLeft R RL RR T ∧ badEdgesLeft R RL Rstar ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ badEdgesLeft R RL Rstar, x e) ∨
      (OccursRight L LL LR T ∧ badEdgesRight L LR Lstar ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ badEdgesRight L LR Lstar, x e) :=
  exists_occurring_badEvent hx hinterLR hEleft hEright
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hS hSL.1 hSR.1 hSL.2.1 hSR.2.1)
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hL hLL.1 hLR.1 hLL.2.1 hLR.2.1)
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hR hRL.1 hRR.1 hRL.2.1 hRR.2.1)
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hL hLL.1 hR hLL.2.1 hcR)
    (P.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight hx hη0 (by linarith)
      hC hR hL hRR.1 ⟨hcR.1.symm, hcR.2⟩ hRR.2.1)
    (P.arrowLeft_disjoint_arrowRight hx hη0 hη hC hL hR hcR hLL hRR)
    hT hZXr h1r h1r' h2r h2r' hnmcr hZXl h1l h1l' h2l h2l' hnmcl

end TSPGap


/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MatchingDefs
import TSPGap.Flow

/-!
# The network of KKO21's matching lemma

Rows are the **oriented bundles** `(u, u')` of distinct atoms of `S`
(`OrientedBundle`), columns are the atoms, and an arc joins a row to each of
its two endpoints.  Row capacity `rowCap`, column capacity `demand`.

* `cutCap_ge_of_hall`: the Hall condition for every atom family gives the cut
  condition of `exists_flow_of_cut` at the total demand — every row touching
  the sink side's complement pays its capacity either as an uncaptured row or
  across an incidence arc.
* `exists_saturating_flow`: a flow of value exactly the total demand, and then
  **every column is saturated** because the column inequalities sum to an
  equality (`col_eq_of_total`).
* The unoriented allocation `bundleAlloc` adds the flow into `u` from both
  orientations of the bundle `{u, u'}` and divides by `F_u`; it is
  nonnegative, supported on good bundles at their endpoints, sums at `u` to
  `x(δ↑(u)) Z_u` (`sum_bundleAlloc`), and a good bundle allocates at most
  `(1 + α) x_e` in total (`bundleAlloc_bound`) — the `/2` in the row
  capacities cancels the two orientations.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Oriented bundles -/

/-- An oriented bundle at the cut with atoms `ch`: an ordered pair of distinct
atoms. -/
structure OrientedBundle (ch : Finset (Finset (Fin n))) where
  fst : Finset (Fin n)
  snd : Finset (Fin n)
  fst_mem : fst ∈ ch
  snd_mem : snd ∈ ch
  ne : fst ≠ snd

namespace OrientedBundle

variable {ch : Finset (Finset (Fin n))}

theorem ext' {p q : OrientedBundle ch} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  cases p; cases q; cases h1; cases h2; rfl

/-- Oriented bundles are the off-diagonal pairs of atoms. -/
def equivOffDiag : OrientedBundle ch ≃ {p : Finset (Fin n) × Finset (Fin n) //
    p.1 ∈ ch ∧ p.2 ∈ ch ∧ p.1 ≠ p.2} where
  toFun p := ⟨(p.fst, p.snd), p.fst_mem, p.snd_mem, p.ne⟩
  invFun q := ⟨q.1.1, q.1.2, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv p := by cases p; rfl
  right_inv q := by rcases q with ⟨⟨a, b⟩, h⟩; rfl

noncomputable instance : Fintype (OrientedBundle ch) :=
  Fintype.ofEquiv _ equivOffDiag.symm

/-- The reversed orientation. -/
def rev (p : OrientedBundle ch) : OrientedBundle ch :=
  ⟨p.snd, p.fst, p.snd_mem, p.fst_mem, p.ne.symm⟩

/-- A sum over oriented bundles is the double sum over ordered pairs. -/
theorem sum_eq (f : Finset (Fin n) → Finset (Fin n) → ℝ) :
    ∑ p : OrientedBundle ch, f p.fst p.snd = ∑ u ∈ ch, ∑ u' ∈ ch.erase u, f u u' := by
  have h1 : ∑ p : OrientedBundle ch, f p.fst p.snd
      = ∑ q : {p : Finset (Fin n) × Finset (Fin n) // p.1 ∈ ch ∧ p.2 ∈ ch ∧ p.1 ≠ p.2},
          f q.1.1 q.1.2 :=
    Fintype.sum_equiv equivOffDiag _ _ (fun p => rfl)
  rw [h1, ← Finset.sum_subtype ((ch ×ˢ ch).filter (fun p => p.1 ≠ p.2)) (fun p => by
    simp only [Finset.mem_filter, Finset.mem_product]; tauto)
    (fun p : Finset (Fin n) × Finset (Fin n) => f p.1 p.2)]
  rw [Finset.sum_finset_product' _ ch (fun u => ch.erase u) (fun p => by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase]; tauto)]

/-- A function of the pair, read off an oriented bundle. -/
theorem apply_eq {f : Finset (Fin n) → Finset (Fin n) → ℝ} (p : OrientedBundle ch) :
    (fun a b => if h : a ∈ ch ∧ b ∈ ch ∧ a ≠ b then f a b else 0) p.fst p.snd = f p.fst p.snd := by
  simp [p.fst_mem, p.snd_mem, p.ne]

end OrientedBundle

/-! ### The network -/

section Network

variable (x) (μ : TreeDist n x) (S : Finset (Fin n)) (ch : Finset (Finset (Fin n)))
  (ε₂ α εB : ℝ) (k : ℕ)

/-- Row capacities. -/
noncomputable def rowCapacity (p : OrientedBundle ch) : ℝ := rowCap μ ε₂ α p.fst p.snd

/-- Column capacities (demands). -/
noncomputable def colCapacity (u : {u // u ∈ ch}) : ℝ := demand x S εB k u.1

/-- Arc capacities: a row reaches its two endpoints. -/
noncomputable def arcCapacity (p : OrientedBundle ch) (u : {u // u ∈ ch}) : ℝ :=
  if u.1 = p.fst ∨ u.1 = p.snd then rowCapacity x μ ch ε₂ α p else 0

/-- The total demand. -/
noncomputable def totalDemand : ℝ := ∑ u : {u // u ∈ ch}, colCapacity x S ch εB k u

/-- The atoms on the sink side's complement, as a family. -/
noncomputable def atomsOf (SB : Finset {u // u ∈ ch}) : Finset (Finset (Fin n)) :=
  SBᶜ.image (fun u => u.1)

theorem atomsOf_subset (SB : Finset {u // u ∈ ch}) : atomsOf ch SB ⊆ ch := by
  intro u hu
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hu
  exact v.2

theorem mem_atomsOf {SB : Finset {u // u ∈ ch}} {u : Finset (Fin n)} :
    u ∈ atomsOf ch SB ↔ ∃ v : {u // u ∈ ch}, v ∉ SB ∧ v.1 = u := by
  unfold atomsOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, Finset.mem_compl.mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, Finset.mem_compl.mpr hv, rfl⟩

/-- The demand of the sink side's complement is the demand of its atoms. -/
theorem sum_col_compl (SB : Finset {u // u ∈ ch}) :
    ∑ u ∈ SBᶜ, colCapacity x S ch εB k u = ∑ u ∈ atomsOf ch SB, demand x S εB k u := by
  unfold atomsOf
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  rfl

/-- **The cut condition from Hall.**  If every atom family's demand is covered
by the rows touching it, every cut has capacity at least the total demand. -/
theorem cutCap_ge_of_hall (hx : ∀ e, 0 ≤ x e) (hα : 0 ≤ α)
    (hdisj : ∀ u ∈ ch, ∀ u' ∈ ch, u ≠ u' → Disjoint u u')
    (hall : ∀ Q ⊆ ch, ∑ u ∈ Q, demand x S εB k u ≤ touchCap μ ε₂ α ch Q)
    (SA : Finset (OrientedBundle ch)) (SB : Finset {u // u ∈ ch}) :
    totalDemand x S ch εB k ≤ cutCap (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α)
      (colCapacity x S ch εB k) SA SB := by
  unfold cutCap totalDemand
  set Q := atomsOf ch SB with hQ
  have hrow_nn : ∀ p : OrientedBundle ch, 0 ≤ rowCapacity x μ ch ε₂ α p := fun p =>
    rowCap_nonneg hx μ hα (hdisj _ p.fst_mem _ p.snd_mem p.ne)
  -- the rows touching `Q`
  have htouch : touchCap μ ε₂ α ch Q
      = ∑ p : OrientedBundle ch,
          (if p.fst ∈ Q ∨ p.snd ∈ Q then rowCapacity x μ ch ε₂ α p else 0) := by
    unfold touchCap rowCapacity
    exact (OrientedBundle.sum_eq _).symm
  -- split the columns
  have hcol : ∑ u : {u // u ∈ ch}, colCapacity x S ch εB k u
      = ∑ u ∈ SB, colCapacity x S ch εB k u + ∑ u ∈ SBᶜ, colCapacity x S ch εB k u := by
    rw [← Finset.sum_add_sum_compl SB]
  rw [hcol, sum_col_compl]
  -- a touching row pays either as an uncaptured row or across an arc
  have hpay : ∑ p : OrientedBundle ch,
      (if p.fst ∈ Q ∨ p.snd ∈ Q then rowCapacity x μ ch ε₂ α p else 0)
      ≤ ∑ p ∈ SAᶜ, rowCapacity x μ ch ε₂ α p
        + ∑ p ∈ SA, ∑ u ∈ SBᶜ, arcCapacity x μ ch ε₂ α p u := by
    rw [← Finset.sum_add_sum_compl SA (fun p =>
      if p.fst ∈ Q ∨ p.snd ∈ Q then rowCapacity x μ ch ε₂ α p else 0), add_comm]
    refine add_le_add (Finset.sum_le_sum fun p _ => ?_) (Finset.sum_le_sum fun p _ => ?_)
    · split_ifs
      · exact le_rfl
      · exact hrow_nn p
    · split_ifs with h
      · -- an endpoint of `p` is an atom of `SBᶜ`
        obtain ⟨v, hv, hveq⟩ : ∃ v : {u // u ∈ ch}, v ∉ SB ∧ (v.1 = p.fst ∨ v.1 = p.snd) := by
          rcases h with h | h
          · obtain ⟨v, hv, hve⟩ := (mem_atomsOf ch).mp h; exact ⟨v, hv, Or.inl hve⟩
          · obtain ⟨v, hv, hve⟩ := (mem_atomsOf ch).mp h; exact ⟨v, hv, Or.inr hve⟩
        have hvmem : v ∈ SBᶜ := Finset.mem_compl.mpr hv
        calc rowCapacity x μ ch ε₂ α p = arcCapacity x μ ch ε₂ α p v := by
              unfold arcCapacity; rw [if_pos hveq]
          _ ≤ ∑ u ∈ SBᶜ, arcCapacity x μ ch ε₂ α p u :=
              Finset.single_le_sum (f := fun u => arcCapacity x μ ch ε₂ α p u)
                (fun u _ => by unfold arcCapacity; split_ifs <;> [exact hrow_nn p; exact le_rfl])
                hvmem
      · exact Finset.sum_nonneg fun u _ => by
          unfold arcCapacity; split_ifs <;> [exact hrow_nn p; exact le_rfl]
  have hH := hall Q (atomsOf_subset ch SB)
  rw [htouch] at hH
  linarith

/-- **The saturating flow.** -/
theorem exists_saturating_flow (hx : ∀ e, 0 ≤ x e) (hα : 0 ≤ α) (hεB : εB ≤ 1)
    (hdisj : ∀ u ∈ ch, ∀ u' ∈ ch, u ≠ u' → Disjoint u u')
    (hall : ∀ Q ⊆ ch, ∑ u ∈ Q, demand x S εB k u ≤ touchCap μ ε₂ α ch Q) :
    ∃ z : OrientedBundle ch → {u // u ∈ ch} → ℝ,
      IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z
      ∧ ∀ u, ∑ p, z p u = colCapacity x S ch εB k u := by
  have hrow_nn : ∀ p : OrientedBundle ch, 0 ≤ rowCapacity x μ ch ε₂ α p := fun p =>
    rowCap_nonneg hx μ hα (hdisj _ p.fst_mem _ p.snd_mem p.ne)
  have hcol_nn : ∀ u : {u // u ∈ ch}, 0 ≤ colCapacity x S ch εB k u := by
    intro u
    unfold colCapacity demand
    have hF : 0 ≤ fFactor x S εB u.1 := by unfold fFactor; split_ifs <;> linarith
    have hZ : 0 ≤ zFactor x S k u.1 := by
      have := one_le_zFactor (x := x) S k u.1; linarith
    exact mul_nonneg (mul_nonneg (upSum_nonneg hx S u.1) hF) hZ
  obtain ⟨z, hz, htot⟩ := exists_flow_of_cut (τ := totalDemand x S ch εB k)
    (fun p u => by unfold arcCapacity; split_ifs <;> [exact hrow_nn p; exact le_rfl])
    hrow_nn hcol_nn (Finset.sum_nonneg fun u _ => hcol_nn u)
    (cutCap_ge_of_hall x μ S ch ε₂ α εB k hx hα hdisj hall)
  refine ⟨z, hz, ?_⟩
  -- the column inequalities sum to an equality
  have hsum : ∑ u : {u // u ∈ ch}, ∑ p, z p u = ∑ u : {u // u ∈ ch}, colCapacity x S ch εB k u := by
    rw [← flowTotal_eq_col, htot]; rfl
  exact fun u => (Finset.sum_eq_sum_iff_of_le (fun u _ => hz.col u)).mp hsum u (Finset.mem_univ u)

end Network

/-! ### The unoriented allocation -/

section Alloc

variable (x) {ch : Finset (Finset (Fin n))} (S : Finset (Fin n)) (εB : ℝ)
  (z : OrientedBundle ch → {u // u ∈ ch} → ℝ)

/-- The oriented bundle `(u, u')`, when it exists. -/
noncomputable def orient (u u' : Finset (Fin n)) : Option (OrientedBundle ch) :=
  if h : u ∈ ch ∧ u' ∈ ch ∧ u ≠ u' then some ⟨u, u', h.1, h.2.1, h.2.2⟩ else none

/-- **The allocation of the bundle `{u, u'}` to `u`**: the flow into `u` from
both orientations, divided by `F_u`. -/
noncomputable def bundleAlloc (u u' : Finset (Fin n)) : ℝ :=
  if h : u ∈ ch ∧ u' ∈ ch ∧ u ≠ u' then
    (z ⟨u, u', h.1, h.2.1, h.2.2⟩ ⟨u, h.1⟩ + z ⟨u', u, h.2.1, h.1, h.2.2.symm⟩ ⟨u, h.1⟩)
      / fFactor x S εB u
  else 0

variable {μ : TreeDist n x} {ε₂ α : ℝ} {k : ℕ}

theorem bundleAlloc_nonneg (hεB : εB < 1)
    (hz : IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z)
    (u u' : Finset (Fin n)) : 0 ≤ bundleAlloc x S εB z u u' := by
  unfold bundleAlloc
  split_ifs
  · exact div_nonneg (add_nonneg (hz.nonneg _ _) (hz.nonneg _ _)) (fFactor_pos hεB u).le
  · exact le_rfl

/-- A nonzero allocation sits on a good bundle at one of its endpoints. -/
theorem bundleAlloc_support
    (hz : IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z)
    {u u' : Finset (Fin n)} (h : bundleAlloc x S εB z u u' ≠ 0) :
    u ∈ ch ∧ u' ∈ ch ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u' := by
  unfold bundleAlloc at h
  split_ifs at h with hm
  · refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
    by_contra hbad
    apply h
    have h1 : z ⟨u, u', hm.1, hm.2.1, hm.2.2⟩ ⟨u, hm.1⟩ = 0 := by
      refine le_antisymm ?_ (hz.nonneg _ _)
      refine (hz.le_cap _ _).trans ?_
      unfold arcCapacity rowCapacity rowCap
      split_ifs <;> simp_all
    have h2 : z ⟨u', u, hm.2.1, hm.1, hm.2.2.symm⟩ ⟨u, hm.1⟩ = 0 := by
      refine le_antisymm ?_ (hz.nonneg _ _)
      refine (hz.le_cap _ _).trans ?_
      unfold arcCapacity rowCapacity rowCap
      have : ¬ IsGoodBundle μ ε₂ u' u := fun h' => hbad (isGoodBundle_comm.mp h')
      split_ifs <;> simp_all
    rw [h1, h2, add_zero, zero_div]
  · exact absurd rfl h

/-- The flow out of a row goes to its two endpoints only. -/
theorem row_sum_eq
    (hz : IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z)
    (p : OrientedBundle ch) :
    ∑ f, z p f = z p ⟨p.fst, p.fst_mem⟩ + z p ⟨p.snd, p.snd_mem⟩ := by
  have hzero : ∀ f : {u // u ∈ ch}, f ≠ ⟨p.fst, p.fst_mem⟩ → f ≠ ⟨p.snd, p.snd_mem⟩ →
      z p f = 0 := by
    intro f h1 h2
    refine le_antisymm ?_ (hz.nonneg _ _)
    refine (hz.le_cap _ _).trans ?_
    unfold arcCapacity
    rw [if_neg]
    rintro (h | h)
    · exact h1 (Subtype.ext h)
    · exact h2 (Subtype.ext h)
  have hne : (⟨p.fst, p.fst_mem⟩ : {u // u ∈ ch}) ≠ ⟨p.snd, p.snd_mem⟩ :=
    fun h => p.ne (congrArg Subtype.val h)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨p.fst, p.fst_mem⟩),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)]
  rw [Finset.sum_eq_zero fun f hf => hzero f (Finset.mem_erase.mp (Finset.mem_erase.mp hf).2).1
    (Finset.mem_erase.mp hf).1]
  ring

/-- **A bundle allocates at most `(1 + α) x_e`** over its two endpoints: the
two orientations' row sums. -/
theorem bundleAlloc_bound (hx : ∀ e, 0 ≤ x e) (hεB : εB < 1)
    (hz : IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z)
    {u u' : Finset (Fin n)} (hu : u ∈ ch) (hu' : u' ∈ ch) (huu' : u ≠ u') (hd : Disjoint u u')
    (hα : 0 ≤ α) :
    bundleAlloc x S εB z u u' * fFactor x S εB u + bundleAlloc x S εB z u' u * fFactor x S εB u'
      ≤ (1 + α) * pairSum x u u' := by
  have hF : fFactor x S εB u ≠ 0 := (fFactor_pos hεB u).ne'
  have hF' : fFactor x S εB u' ≠ 0 := (fFactor_pos hεB u').ne'
  set p : OrientedBundle ch := ⟨u, u', hu, hu', huu'⟩ with hp
  set p' : OrientedBundle ch := ⟨u', u, hu', hu, huu'.symm⟩ with hp'
  have e1 : bundleAlloc x S εB z u u' * fFactor x S εB u
      = z p ⟨u, hu⟩ + z p' ⟨u, hu⟩ := by
    unfold bundleAlloc
    rw [dif_pos ⟨hu, hu', huu'⟩, div_mul_cancel₀ _ hF]
  have e2 : bundleAlloc x S εB z u' u * fFactor x S εB u'
      = z p' ⟨u', hu'⟩ + z p ⟨u', hu'⟩ := by
    unfold bundleAlloc
    rw [dif_pos ⟨hu', hu, huu'.symm⟩, div_mul_cancel₀ _ hF']
  have r1 := hz.row p
  have r2 := hz.row p'
  rw [row_sum_eq x S εB z hz] at r1 r2
  have hcap : rowCapacity x μ ch ε₂ α p + rowCapacity x μ ch ε₂ α p' ≤ (1 + α) * pairSum x u u' := by
    unfold rowCapacity
    show rowCap μ ε₂ α u u' + rowCap μ ε₂ α u' u ≤ (1 + α) * pairSum x u u'
    rw [rowCap_comm μ ε₂ α u' u]
    unfold rowCap
    have := pairSum_nonneg_lp hx hd
    split_ifs
    · linarith
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + α) this]
  rw [e1, e2]
  change z p ⟨u, hu⟩ + z p' ⟨u, hu⟩ + (z p' ⟨u', hu'⟩ + z p ⟨u', hu'⟩) ≤ _
  linarith

/-- The flow into an atom, regrouped by the first and the second endpoint. -/
theorem col_sum_eq
    (hz : IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z)
    {u : Finset (Fin n)} (hu : u ∈ ch) :
    ∑ p, z p ⟨u, hu⟩
      = ∑ u' ∈ ch.erase u, (if h : u' ∈ ch ∧ u' ≠ u then
          z ⟨u, u', hu, h.1, h.2.symm⟩ ⟨u, hu⟩ + z ⟨u', u, h.1, hu, h.2⟩ ⟨u, hu⟩ else 0) := by
  -- read the flow off the pair
  set g : Finset (Fin n) → Finset (Fin n) → ℝ := fun a b =>
    if h : a ∈ ch ∧ b ∈ ch ∧ a ≠ b then z ⟨a, b, h.1, h.2.1, h.2.2⟩ ⟨u, hu⟩ else 0 with hg
  have h1 : ∑ p, z p ⟨u, hu⟩ = ∑ p : OrientedBundle ch, g p.fst p.snd := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hg]
    simp only [p.fst_mem, p.snd_mem, p.ne, and_self, ne_eq, not_false_eq_true, dite_true]
  rw [h1, OrientedBundle.sum_eq]
  -- rows not at `u` carry nothing into `u`
  have hzero : ∀ a ∈ ch, ∀ b ∈ ch.erase a, a ≠ u → b ≠ u → g a b = 0 := by
    intro a ha b hb hau hbu
    rw [hg]
    simp only
    split_ifs with h
    · refine le_antisymm ?_ (hz.nonneg _ _)
      refine (hz.le_cap _ _).trans ?_
      unfold arcCapacity
      rw [if_neg]
      rintro (h' | h')
      · exact hau h'.symm
      · exact hbu h'.symm
    · rfl
  -- split off the first index `u`
  rw [← Finset.add_sum_erase _ _ hu]
  have h2 : ∑ a ∈ ch.erase u, ∑ b ∈ ch.erase a, g a b = ∑ a ∈ ch.erase u, g a u := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have hau := (Finset.mem_erase.mp ha).1
    rw [Finset.sum_eq_single u]
    · intro b hb hbu; exact hzero a (Finset.mem_erase.mp ha).2 b hb hau hbu
    · intro h; exact absurd (Finset.mem_erase.mpr ⟨hau.symm, hu⟩) h
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u' hu' => ?_
  have hu'u := (Finset.mem_erase.mp hu').1
  have hu'c := (Finset.mem_erase.mp hu').2
  rw [dif_pos ⟨hu'c, hu'u⟩, hg]
  simp only [hu, hu'c, hu'u, hu'u.symm, and_self, ne_eq, not_false_eq_true, dite_true]

/-- **The allocation at an atom sums to `x(δ↑(u)) Z_u`** (KKO (27)). -/
theorem sum_bundleAlloc (hεB : εB < 1)
    (hz : IsFlow (arcCapacity x μ ch ε₂ α) (rowCapacity x μ ch ε₂ α) (colCapacity x S ch εB k) z)
    (hsat : ∀ v, ∑ p, z p v = colCapacity x S ch εB k v)
    {u : Finset (Fin n)} (hu : u ∈ ch) :
    ∑ u' ∈ ch.erase u, bundleAlloc x S εB z u u' = upSum x S u * zFactor x S k u := by
  have hF : fFactor x S εB u ≠ 0 := (fFactor_pos hεB u).ne'
  have hcol := hsat ⟨u, hu⟩
  rw [col_sum_eq x S εB z hz hu] at hcol
  have hsum : (∑ u' ∈ ch.erase u, bundleAlloc x S εB z u u') * fFactor x S εB u
      = ∑ u' ∈ ch.erase u, (if h : u' ∈ ch ∧ u' ≠ u then
          z ⟨u, u', hu, h.1, h.2.symm⟩ ⟨u, hu⟩ + z ⟨u', u, h.1, hu, h.2⟩ ⟨u, hu⟩ else 0) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    have hu'u := (Finset.mem_erase.mp hu').1
    have hu'c := (Finset.mem_erase.mp hu').2
    unfold bundleAlloc
    rw [dif_pos ⟨hu, hu'c, hu'u.symm⟩, dif_pos ⟨hu'c, hu'u⟩, div_mul_cancel₀ _ hF]
  rw [hcol] at hsum
  unfold colCapacity demand at hsum
  have hsum' : (∑ u' ∈ ch.erase u, bundleAlloc x S εB z u u') * fFactor x S εB u
      = (upSum x S u * zFactor x S k u) * fFactor x S εB u := by
    rw [hsum]; ring
  exact mul_right_cancel₀ hF hsum'

end Alloc

end TSPGap

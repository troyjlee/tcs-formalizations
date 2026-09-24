/-
# Rao's one-step contraction: the pieces before the encoding

Rao's Lemma 4 is proved by fixing `U`, sampling a `v`-set `V ⊆ X \ U`, writing `W = U ∪ V`,
and showing

  `E_{V,S} |χ(S,W)| ≤ (2/3) · E_S |χ(S,U)|`

by exhibiting a prefix-free encoding of the pairs `(V,S)` whose length is
`log(R^w·C(n−u,v)) + a·|χ(S,U)| − b·|χ(S,W)|` with `a/b ≤ 2/3`, then applying Lemma 5.

This file collects the parts of that argument that contain **no encoding**, which is where
the mathematics actually is:

* `sum_choose_le_pow` — the binomial estimate `∑_{i≤a} C(m,v+i) ≤ C(m,v)·(m/v)^a` behind
  Rao's step (b) ("since `U` has been fixed, there are … choices for `W ∪ χ(X,U)`");
* `chi_card_le_inter` — his step (d): the set the encoder has *already* written down,
  `χ(j,U) ∩ χ(S,U)`, is at least as big as `|χ(S,W)|`. This is what makes the encoding pay
  for itself: `|χ(S,W)|` bits are saved because that many bits were already determined.
* `jWitness` — the auxiliary minimizer `j` of step (c), as a function of the data the decoder
  has, which is what makes it usable in an encoding at all.

The `τ`/`φ` classes and the two cases come next; nothing here depends on them.
-/
import Sunflower.RaoChi
import Sunflower.PrefixCode

open Finset

namespace Sunflower

namespace Rao

/-! ## The binomial estimate

`W ∪ χ(S,U)` differs from `V` by at most `|χ(S,U)|` elements, so the number of choices for it
is `∑_{i ≤ a} C(n−u, v+i)`. Rao bounds that by `C(n−u,v)·(n/v)^a`, via `C(m+a, v+a)`. -/

/-- Adding `a` to both arguments dominates the sum of the `a+1` slices: choosing `v+a` from
`m+a` can be done by first choosing which of the `a` new elements to use. -/
theorem sum_choose_le_choose_add (m v : ℕ) :
    ∀ a : ℕ, ∑ i ∈ Finset.range (a + 1), m.choose (v + i) ≤ (m + a).choose (v + a) := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ]
      have h1 : m.choose (v + (a + 1)) ≤ (m + a).choose (v + a + 1) := by
        have : m ≤ m + a := Nat.le_add_right _ _
        calc m.choose (v + (a + 1)) = m.choose (v + a + 1) := by ring_nf
          _ ≤ (m + a).choose (v + a + 1) := Nat.choose_le_choose _ this
      have h2 : (m + a).choose (v + a) + (m + a).choose (v + a + 1)
          = (m + (a + 1)).choose (v + (a + 1)) := by
        rw [show m + (a + 1) = (m + a) + 1 by ring, show v + (a + 1) = (v + a) + 1 by ring,
          Nat.choose_succ_succ']
      omega

/-- `C(m+a, v+a) ≤ C(m,v)·(m/v)^a` for `1 ≤ v ≤ m`: each step multiplies by
`(m+t)/(v+t) ≤ m/v`. -/
theorem choose_add_le_pow {m v : ℕ} (hv : 1 ≤ v) (hvm : v ≤ m) :
    ∀ a : ℕ, (((m + a).choose (v + a) : ℕ) : ℝ) ≤ (m.choose v : ℝ) * ((m : ℝ) / v) ^ a := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hmv : (v : ℝ) ≤ (m : ℝ) := by exact_mod_cast hvm
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
      -- `(m+a+1)·C(m+a, v+a) = C(m+a+1, v+a+1)·(v+a+1)`
      have hkey : ((m + a) + 1) * (m + a).choose (v + a)
          = ((m + a) + 1).choose ((v + a) + 1) * ((v + a) + 1) :=
        Nat.add_one_mul_choose_eq _ _
      have hkeyR : (((m + a) + 1 : ℕ) : ℝ) * ((m + a).choose (v + a) : ℝ)
          = (((m + a) + 1).choose ((v + a) + 1) : ℝ) * (((v + a) + 1 : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hkey
      have hden : (0 : ℝ) < ((v + a : ℕ) : ℝ) + 1 := by positivity
      have hstep : ((((m + a) + 1).choose ((v + a) + 1) : ℕ) : ℝ)
          = ((m + a).choose (v + a) : ℝ) * ((((m + a) : ℕ) : ℝ) + 1) / ((((v + a) : ℕ) : ℝ) + 1) := by
        field_simp at hkeyR ⊢
        push_cast at hkeyR ⊢
        linarith [hkeyR]
      -- `(m+a+1)/(v+a+1) ≤ m/v`
      have hratio : ((((m + a) : ℕ) : ℝ) + 1) / ((((v + a) : ℕ) : ℝ) + 1) ≤ (m : ℝ) / v := by
        rw [div_le_div_iff₀ (by positivity) hv0]
        push_cast
        nlinarith [hmv, hv0, (by positivity : (0:ℝ) ≤ (a:ℝ))]
      have hnn : (0 : ℝ) ≤ ((m + a).choose (v + a) : ℝ) := by positivity
      calc ((((m + (a+1)).choose (v + (a+1)) : ℕ)) : ℝ)
          = (((m + a).choose (v + a) : ℝ)) * ((((m + a) : ℕ) : ℝ) + 1) / ((((v + a) : ℕ) : ℝ) + 1) := by
            rw [show m + (a+1) = (m + a) + 1 by ring, show v + (a+1) = (v + a) + 1 by ring]
            exact hstep
        _ = ((m + a).choose (v + a) : ℝ) * (((((m + a) : ℕ) : ℝ) + 1) / ((((v + a) : ℕ) : ℝ) + 1)) := by
            ring
        _ ≤ ((m + a).choose (v + a) : ℝ) * ((m : ℝ) / v) := by
            exact mul_le_mul_of_nonneg_left hratio hnn
        _ ≤ ((m.choose v : ℝ) * ((m : ℝ) / v) ^ a) * ((m : ℝ) / v) := by
            refine mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (m.choose v : ℝ) * ((m : ℝ) / v) ^ (a + 1) := by ring

/-- **Rao's step (b) estimate.** The `a+1` slices `C(m,v), …, C(m,v+a)` sum to at most
`C(m,v)·(m/v)^a`. -/
theorem sum_choose_le_pow {m v : ℕ} (hv : 1 ≤ v) (hvm : v ≤ m) (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (m.choose (v + i) : ℝ)) ≤ (m.choose v : ℝ) * ((m : ℝ) / v) ^ a := by
  have h1 : (∑ i ∈ Finset.range (a + 1), (m.choose (v + i) : ℝ))
      = ((∑ i ∈ Finset.range (a + 1), m.choose (v + i) : ℕ) : ℝ) := by push_cast; rfl
  rw [h1]
  refine le_trans ?_ (choose_add_le_pow hv hvm a)
  exact_mod_cast sum_choose_le_choose_add m v a

/-! ## The slice ratio

Case 2 needs the other direction: a *fixed* `t`-set `Y` is contained in a uniformly random
`v`-subset of an `m`-set with probability `C(m−t, v−t)/C(m,v) ≤ (v/(m−t))^t` — Rao's "`V`
includes `χ(y,U) \ B` with probability at most `(v/(n−u−k))^{|χ(X,U)|−|B|}`".

Stated additively (`m = m' + t`, `v = v' + t`) so that no `ℕ` subtraction appears, and
division-free. -/

/-- The descending-product identity `C(m',v')·∏_{j<t}(m'+j+1) = C(m'+t,v'+t)·∏_{j<t}(v'+j+1)`,
each step being `(n+1)·C(n,k) = C(n+1,k+1)·(k+1)`. -/
theorem choose_add_prod (m' v' : ℕ) : ∀ t : ℕ,
    (m'.choose v' : ℝ) * ∏ j ∈ Finset.range t, ((m' + j + 1 : ℕ) : ℝ)
      = ((m' + t).choose (v' + t) : ℝ) * ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have hstep : ((m' + t) + 1 : ℕ) * (m' + t).choose (v' + t)
          = ((m' + t) + 1).choose ((v' + t) + 1) * ((v' + t) + 1) :=
        Nat.add_one_mul_choose_eq _ _
      have hstepR : (((m' + t) + 1 : ℕ) : ℝ) * (((m' + t).choose (v' + t) : ℕ) : ℝ)
          = ((((m' + t) + 1).choose ((v' + t) + 1) : ℕ) : ℝ) * ((((v' + t) + 1 : ℕ)) : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hstep
      calc (m'.choose v' : ℝ) * ∏ j ∈ Finset.range (t + 1), ((m' + j + 1 : ℕ) : ℝ)
          = ((m'.choose v' : ℝ) * ∏ j ∈ Finset.range t, ((m' + j + 1 : ℕ) : ℝ))
              * ((m' + t + 1 : ℕ) : ℝ) := by
            rw [Finset.prod_range_succ]; ring
        _ = (((m' + t).choose (v' + t) : ℝ) * ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ))
              * ((m' + t + 1 : ℕ) : ℝ) := by rw [ih]
        _ = ((((m' + t) + 1 : ℕ) : ℝ) * (((m' + t).choose (v' + t) : ℕ) : ℝ))
              * ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ) := by ring
        _ = (((((m' + t) + 1).choose ((v' + t) + 1) : ℕ)) : ℝ) * ((((v' + t) + 1 : ℕ)) : ℝ)
              * ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ) := by rw [hstepR]
        _ = ((m' + (t + 1)).choose (v' + (t + 1)) : ℝ)
              * ∏ j ∈ Finset.range (t + 1), ((v' + j + 1 : ℕ) : ℝ) := by
            rw [Finset.prod_range_succ, show m' + (t + 1) = (m' + t) + 1 by ring,
              show v' + (t + 1) = (v' + t) + 1 by ring]
            ring

/-- **The slice-ratio estimate**, division-free: `C(m',v')·m'^t ≤ C(m'+t, v'+t)·(v'+t)^t`,
i.e. `C(m−t,v−t)/C(m,v) ≤ (v/(m−t))^t` after dividing. -/
theorem choose_mul_pow_le (m' v' t : ℕ) :
    (m'.choose v' : ℝ) * (m' : ℝ) ^ t
      ≤ ((m' + t).choose (v' + t) : ℝ) * (((v' + t : ℕ) : ℝ)) ^ t := by
  have hid := choose_add_prod m' v' t
  have hlow : (m' : ℝ) ^ t ≤ ∏ j ∈ Finset.range t, ((m' + j + 1 : ℕ) : ℝ) := by
    calc (m' : ℝ) ^ t = ∏ _j ∈ Finset.range t, (m' : ℝ) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ j ∈ Finset.range t, ((m' + j + 1 : ℕ) : ℝ) := by
          refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
          have : m' ≤ m' + j + 1 := by omega
          exact_mod_cast this
  have hhigh : ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ) ≤ (((v' + t : ℕ) : ℝ)) ^ t := by
    calc ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ)
        ≤ ∏ _j ∈ Finset.range t, (((v' + t : ℕ) : ℝ)) := by
          refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j hj => ?_
          rw [Finset.mem_range] at hj
          have : v' + j + 1 ≤ v' + t := by omega
          exact_mod_cast this
      _ = (((v' + t : ℕ) : ℝ)) ^ t := by rw [Finset.prod_const, Finset.card_range]
  calc (m'.choose v' : ℝ) * (m' : ℝ) ^ t
      ≤ (m'.choose v' : ℝ) * ∏ j ∈ Finset.range t, ((m' + j + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = ((m' + t).choose (v' + t) : ℝ) * ∏ j ∈ Finset.range t, ((v' + j + 1 : ℕ) : ℝ) := hid
    _ ≤ ((m' + t).choose (v' + t) : ℝ) * (((v' + t : ℕ) : ℝ)) ^ t :=
        mul_le_mul_of_nonneg_left hhigh (by positivity)

/-! ## Counting the `V`s that swallow a fixed set

Case 2 needs: for a *fixed* `Y`, how many `v`-subsets `V` of the ground set contain it. The
answer is exact — remove `Y` and count freely — and combining with `choose_mul_pow_le` gives
Rao's "`V` includes `χ(y,U) \ B` with probability at most `(v/(n−u−k))^{|χ(X,U)|−|B|}`". -/

variable {α : Type*} [DecidableEq α]

/-- The `v`-subsets of `X` containing a fixed `Y ⊆ X` biject with the `(v−|Y|)`-subsets of
`X \ Y`, so there are `C(|X|−|Y|, v−|Y|)` of them. -/
theorem card_filter_superset {X Y : Finset α} (hYX : Y ⊆ X) {v : ℕ} (hYv : Y.card ≤ v) :
    ((X.powersetCard v).filter (fun V => Y ⊆ V)).card
      = ((X.card - Y.card).choose (v - Y.card)) := by
  classical
  have hcard : (X \ Y).card = X.card - Y.card := Finset.card_sdiff_of_subset hYX
  rw [← hcard, ← Finset.card_powersetCard]
  refine Finset.card_nbij' (fun V => V \ Y) (fun T => T ∪ Y) ?_ ?_ ?_ ?_
  · intro V hV
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe,
      Finset.mem_powersetCard] at hV ⊢
    refine ⟨Finset.sdiff_subset_sdiff hV.1.1 (Finset.Subset.refl _), ?_⟩
    rw [Finset.card_sdiff_of_subset hV.2, hV.1.2]
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.coe_filter,
      Set.mem_ofPred_eq] at hT ⊢
    have hTX : T ⊆ X := le_trans hT.1 Finset.sdiff_subset
    refine ⟨⟨Finset.union_subset hTX hYX, ?_⟩, Finset.subset_union_right⟩
    have hdisj : Disjoint T Y := by
      refine Finset.disjoint_left.mpr fun x hx hxY => ?_
      exact (Finset.mem_sdiff.mp (hT.1 hx)).2 hxY
    rw [Finset.card_union_of_disjoint hdisj, hT.2]
    omega
  · intro V hV
    simp only [Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_powersetCard] at hV
    exact Finset.sdiff_union_of_subset hV.2
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hT
    refine Finset.union_sdiff_cancel_right ?_
    refine Finset.disjoint_left.mpr fun x hx hxY => ?_
    exact (Finset.mem_sdiff.mp (hT.1 hx)).2 hxY

/-- **The case-2 slice bound.** The fraction of `v`-subsets of `X` containing a fixed `Y` is at
most `(v/(|X|−|Y|))^{|Y|}`, in division-free form. -/
theorem card_filter_superset_le {X Y : Finset α} (hYX : Y ⊆ X) {v : ℕ} (hYv : Y.card ≤ v)
    (_hvX : v ≤ X.card) :
    ((((X.powersetCard v).filter (fun V => Y ⊆ V)).card : ℕ) : ℝ)
        * ((X.card - Y.card : ℕ) : ℝ) ^ Y.card
      ≤ ((X.card.choose v : ℕ) : ℝ) * (v : ℝ) ^ Y.card := by
  have hYX' : Y.card ≤ X.card := Finset.card_le_card hYX
  have h := choose_mul_pow_le (X.card - Y.card) (v - Y.card) Y.card
  rw [card_filter_superset hYX hYv]
  have e1 : (X.card - Y.card) + Y.card = X.card := by omega
  have e2 : (v - Y.card) + Y.card = v := by omega
  rw [e1, e2] at h
  exact h

/-! ## Step (d): the encoder has already paid for `|χ(S,W)|`

Rao's key claim, and the reason the encoding gains anything. The encoder writes down
`χ(j,U) ∩ χ(S,U)` for an auxiliary member `j`; that set is at least as large as `|χ(S,W)|`,
so those bits are not spent twice. -/

variable {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)} {S U W : Finset α}

/-- **Rao's step (d).** If `j`'s residual at `U` is contained in `W ∪ χ(S,U)`, then the
already-encoded set `χ(j,U) ∩ χ(S,U)` has size at least `|χ(S,W)|`.

The witness `T` behind `χ(j,U)` is a member of `𝓕` sitting inside `S ∪ W`, so minimality of
`χ(S,W)` bounds it by `|T \ W|`; and `T \ W` lands inside both `χ(j,U)` (as `U ⊆ W`) and
`χ(S,U)` (as `χ(j,U) ⊆ W ∪ χ(S,U)`). -/
theorem chi_card_le_inter {j : Finset α} (hS : S ∈ 𝓕) (hj : j ∈ 𝓕) (hUW : U ⊆ W)
    (hjsub : chi 𝓕 j U ⊆ W ∪ chi 𝓕 S U) :
    (chi 𝓕 S W).card ≤ ((chi 𝓕 j U) ∩ (chi 𝓕 S U)).card := by
  classical
  set T : Finset α := chiWitness 𝓕 j U with hT
  have hTF : T ∈ 𝓕 := chiWitness_mem hj
  have hTU : T \ U = chi 𝓕 j U := rfl
  -- `T ⊆ S ∪ W`
  have hTSW : T ⊆ S ∪ W := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.mem_union_right _ (hUW hxU)
    · have hxchi : x ∈ chi 𝓕 j U := by rw [← hTU]; exact Finset.mem_sdiff.mpr ⟨hx, hxU⟩
      rcases Finset.mem_union.mp (hjsub hxchi) with h | h
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (chi_subset hS h)
  -- minimality of `χ(S,W)`
  have hmin : (chi 𝓕 S W).card ≤ (T \ W).card := chi_card_le_of_cand hS hTF hTSW
  -- `T \ W ⊆ χ(j,U) ∩ χ(S,U)`
  have hsub : T \ W ⊆ (chi 𝓕 j U) ∩ (chi 𝓕 S U) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxj : x ∈ chi 𝓕 j U := by
      rw [← hTU]
      exact Finset.mem_sdiff.mpr ⟨hx.1, fun hxU => hx.2 (hUW hxU)⟩
    refine Finset.mem_inter.mpr ⟨hxj, ?_⟩
    rcases Finset.mem_union.mp (hjsub hxj) with h | h
    · exact absurd h hx.2
    · exact h
  exact le_trans hmin (Finset.card_le_card hsub)

/-! ## The auxiliary minimizer `j`

Rao: "Let `j` be such that `χ(j,U) ⊆ W ∪ χ(X,U)`, and `|χ(j,U)|` is minimized." The point of
choosing it canonically is that the *decoder* can recompute it from `U` and `W ∪ χ(S,U)`,
which are exactly the fields already written; the encoder therefore needs no bits for it. -/

/-- The members whose `U`-residual has been covered by what is already encoded. -/
noncomputable def jCands (𝓕 : Finset (Finset α)) (U D : Finset α) : Finset (Finset α) :=
  𝓕.filter fun T => chi 𝓕 T U ⊆ D

lemma mem_jCands {D T : Finset α} : T ∈ jCands 𝓕 U D ↔ T ∈ 𝓕 ∧ chi 𝓕 T U ⊆ D := by
  rw [jCands, Finset.mem_filter]

/-- `S` itself is a candidate, for `D = W ∪ χ(S,U)`. -/
lemma mem_jCands_self (hS : S ∈ 𝓕) : S ∈ jCands 𝓕 U (W ∪ chi 𝓕 S U) :=
  mem_jCands.mpr ⟨hS, Finset.subset_union_right⟩

/-- The canonical `j`: a candidate minimizing `|χ(j,U)|`. A function of `(𝓕, U, D)` only —
and `D = W ∪ χ(S,U)` is a field of the encoding, so the decoder has it. -/
noncomputable def jWitness (𝓕 : Finset (Finset α)) (U D : Finset α) : Finset α :=
  if h : (jCands 𝓕 U D).Nonempty then
    Classical.choose (Finset.exists_min_image (jCands 𝓕 U D) (fun T => (chi 𝓕 T U).card) h)
  else ∅

lemma jWitness_mem_cands {D : Finset α} (h : (jCands 𝓕 U D).Nonempty) :
    jWitness 𝓕 U D ∈ jCands 𝓕 U D := by
  rw [jWitness, dif_pos h]
  exact (Classical.choose_spec
    (Finset.exists_min_image (jCands 𝓕 U D) (fun T => (chi 𝓕 T U).card) h)).1

lemma jWitness_min {D : Finset α} (h : (jCands 𝓕 U D).Nonempty) {T : Finset α}
    (hT : T ∈ jCands 𝓕 U D) :
    (chi 𝓕 (jWitness 𝓕 U D) U).card ≤ (chi 𝓕 T U).card := by
  rw [jWitness, dif_pos h]
  exact (Classical.choose_spec
    (Finset.exists_min_image (jCands 𝓕 U D) (fun T => (chi 𝓕 T U).card) h)).2 T hT

/-- Step (d) at the canonical `j`: what the encoder has written down is big enough. -/
theorem chi_card_le_inter_jWitness (hS : S ∈ 𝓕) (hUW : U ⊆ W) :
    (chi 𝓕 S W).card
      ≤ ((chi 𝓕 (jWitness 𝓕 U (W ∪ chi 𝓕 S U)) U) ∩ (chi 𝓕 S U)).card := by
  have hne : (jCands 𝓕 U (W ∪ chi 𝓕 S U)).Nonempty := ⟨S, mem_jCands_self hS⟩
  have hmem := jWitness_mem_cands hne
  rw [mem_jCands] at hmem
  exact chi_card_le_inter hS hmem.1 hUW hmem.2

/-- The encoder writes `χ(j,U) ∩ χ(S,U)` as a subset of `χ(S,U)`, so `|χ(S,U)|` bits suffice —
and by `chi_card_le_inter_jWitness` at least `|χ(S,W)|` of them were forced. -/
lemma inter_subset_chi (_hS : S ∈ 𝓕) {j : Finset α} :
    (chi 𝓕 j U) ∩ (chi 𝓕 S U) ⊆ chi 𝓕 S U := Finset.inter_subset_right

/-- Rao's `j` is also at most as costly as `S`: `|χ(j,U)| ≤ |χ(S,U)|`, which is what lets the
encoding of `χ(j,U) ∩ χ(S,U)` fit in `|χ(S,U)|` bits. -/
lemma jWitness_card_le (hS : S ∈ 𝓕) :
    (chi 𝓕 (jWitness 𝓕 U (W ∪ chi 𝓕 S U)) U).card ≤ (chi 𝓕 S U).card :=
  jWitness_min ⟨S, mem_jCands_self hS⟩ (mem_jCands_self hS)

/-! ## The class `τ`, and what the decoder knows

Rao's

  `τ(A,X,V) = {y : A ⊆ χ(y,U) ⊆ V ∪ χ(X,U), |χ(y,U)| = |χ(X,U)|}`

is written as a function of `X` and `V`, but for it to be usable in an encoding it must be a
function of **fields already decoded**. It is: `V ∪ χ(X,U)` is field (3), `|χ(X,U)|` is field
(2), and `A` is field (4). So `tau` below takes `(A, D, a)` — no `S`, no `V`.

Note `χ(T,U)` never meets `U`, so `⊆ V ∪ χ(S,U)` and `⊆ W ∪ χ(S,U)` define the same class;
the second form is used here since `W ∪ χ(S,U)` is what gets encoded.

### An implicit decoding dependency in the paper's case 1

Rao's steps (c)–(d) encode `χ(j,U) ∩ χ(X,U)` and then say: "Let `A` be the lexicographically
first subset of `χ(j,U) ∩ χ(X,U)` of size `|χ(X,W)|`. … we can encode `X` using a binary
string of length at most `log(φ(X,V)) + 1`."

Under the sequential, field-by-field reading formalized here, the decoder cannot yet determine
the next width: that field has length `log φ(X,V) + 1`, and

  `φ(X,V) = R^w·(ρv/n)^{|χ(X,U)|}·(vR/n)^{−|χ(X,W)|}`

depends on `|χ(X,W)|`, which is not among the decoded fields — `A` is *defined* from it rather
than transmitted. The formalized resolution is to **encode `A` itself** as a subset of
`χ(j,U)` (which the decoder knows, since `j` is a function of `U` and field (3)). That is the
same `|χ(j,U)| ≤ |χ(S,U)|` bits Rao budgets for step (c), and now `|χ(X,W)| = |A|` is
read off the field, so `φ` — and the next field's width — is determined.

With `A` transmitted the fields are
(1) case bit, (2) `|χ(S,U)|` in unary, (3) `W ∪ χ(S,U)`, (4) `A`, (5) `S` within
`τ(A,D,a)`, (6) `V ∩ χ(S,U)`, and the total is
`log(R^w·C(n−u,v)) + a·(log ρ + 3) − b·log(vR/n) + 4`, which is Rao's bound with `c = 3`. -/

/-- Rao's `τ`, as a function of decoded fields only: the members whose `U`-residual contains
`A`, sits inside `D`, and has size `a`. -/
noncomputable def tau (𝓕 : Finset (Finset α)) (U A D : Finset α) (a : ℕ) :
    Finset (Finset α) :=
  𝓕.filter fun T => A ⊆ chi 𝓕 T U ∧ chi 𝓕 T U ⊆ D ∧ (chi 𝓕 T U).card = a

lemma mem_tau {A D T : Finset α} {a : ℕ} :
    T ∈ tau 𝓕 U A D a ↔
      T ∈ 𝓕 ∧ A ⊆ chi 𝓕 T U ∧ chi 𝓕 T U ⊆ D ∧ (chi 𝓕 T U).card = a := by
  rw [tau, Finset.mem_filter]

/-- `S` lies in its own class — which is what the encoder needs in order to point at it. -/
lemma mem_tau_self {A : Finset α} (hS : S ∈ 𝓕) (hA : A ⊆ chi 𝓕 S U) :
    S ∈ tau 𝓕 U A (W ∪ chi 𝓕 S U) (chi 𝓕 S U).card :=
  mem_tau.mpr ⟨hS, hA, Finset.subset_union_right, rfl⟩

/-- The class shrinks as `A` grows: more of the residual is pinned down. -/
lemma tau_subset_of_subset {A A' D : Finset α} {a : ℕ} (h : A ⊆ A') :
    tau 𝓕 U A' D a ⊆ tau 𝓕 U A D a := by
  intro T hT
  rw [mem_tau] at hT ⊢
  exact ⟨hT.1, le_trans h hT.2.1, hT.2.2⟩

/-- **The candidate `A` exists and is transmittable**: at the canonical `j`, some subset of
`χ(j,U)` of size exactly `|χ(S,W)|` contains no more than the encoder can afford, and `S`
belongs to the class it names. This packages step (d) for the encoder. -/
theorem exists_A_for_encoding (hS : S ∈ 𝓕) (hUW : U ⊆ W) :
    ∃ A : Finset α,
      A ⊆ chi 𝓕 (jWitness 𝓕 U (W ∪ chi 𝓕 S U)) U ∧
      A ⊆ chi 𝓕 S U ∧
      A.card = (chi 𝓕 S W).card ∧
      S ∈ tau 𝓕 U A (W ∪ chi 𝓕 S U) (chi 𝓕 S U).card := by
  classical
  set j : Finset α := jWitness 𝓕 U (W ∪ chi 𝓕 S U) with hj
  have hbig : (chi 𝓕 S W).card ≤ ((chi 𝓕 j U) ∩ (chi 𝓕 S U)).card :=
    chi_card_le_inter_jWitness hS hUW
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq hbig
  refine ⟨A, ?_, ?_, hAcard, ?_⟩
  · exact le_trans hAsub Finset.inter_subset_left
  · exact le_trans hAsub Finset.inter_subset_right
  · exact mem_tau_self hS (le_trans hAsub Finset.inter_subset_right)

end Rao

end Sunflower

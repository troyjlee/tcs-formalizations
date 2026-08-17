/-
# ALWZ's dummy padding, formalized

Inside their Lemma 2.10, ALWZ write:

> We may also assume that all sets in `F′` have size exactly `w`, by adding different dummy
> elements to each set of size less than `w`. We take care to scale by a large enough factor so
> that a negligible amount of weight falls on each dummy element, and so the spreadness
> hypothesis is preserved.

That sentence is formalization note A3: the "scale by a large enough factor" is doing real
work, and padding with only one dummy set per member **can break spreadness**. If `S` has size `u < v`
and all of its weight `σ S` sits on the single padded copy `S ∪ D`, then the link at `D` alone
carries `σ S`, and spreadness would demand `σ S·κ^{v−u} ≤ M`, whereas all we know is
`σ S·κ^u ≤ M`. For `u = 1`, `v` large, that is off by `κ^{v−2}`.

The formalized construction realizes that scaling: give `S` **`q` disjoint padded copies**, each carrying
`σ S`, so that the weight above any dummy is `σ S` while the total mass is multiplied by `q`.
Then the spreadness requirement at a dummy-containing `T` is `σ S·κ^{|T|} ≤ q·M`, which
`q ≥ κ^v` supplies — and since the mass floor `A` is multiplied by `q` as well, the ratio `A/M`
that the Janson bottom depends on is unchanged. Nothing is lost and uniformity is gained.

## What it buys

`JansonMass.failCount_le_of_janson_uniformMass` reaches a `≤v`-bounded system through the
*heaviest size class*, at a cost of `v²` in the exponent: one factor `v` because the class holds
only a `1/v` fraction of the mass, one because the class width can be anywhere in `[1,v]`.
Padding makes the system exactly `v`-uniform with no loss at all, so the exponent is
`A·κ·p/(8Mv)` — one factor `v` better. That factor is precisely the `log log w` by which
`KappaZero.kappaZero` exceeds ALWZ's constant.

## This file

The construction (`padCopy`, `padWeight`, `padGround`) and the three properties that make it a
legitimate substitute: it is `v`-uniform, its mass is `q·wTotal`, and it is `(q·M, κ)`-spread.
-/
import Sunflower.JansonMass
import Sunflower.Padding

open Finset

set_option maxHeartbeats 1000000

namespace Sunflower

open SpreadCore

variable {α : Type*} [DecidableEq α]

/-! ## The construction -/

/-- The `k`-th private dummy block of `S`, when padding to width `v`: the `v − |S|` points
`(S, k(v−|S|)), …, (S, (k+1)(v−|S|) − 1)`. Tagging by `S` makes the blocks private to `S`, and
the index range makes the `k` blocks of one `S` disjoint. -/
def padBlock (v : ℕ) (S : Finset α) (k : ℕ) : Finset (Padded α) :=
  (Finset.Ico (k * (v - S.card)) ((k + 1) * (v - S.card))).image fun i => Sum.inr (S, i)

/-- The `k`-th padded copy of `S`: `S` itself together with its `k`-th dummy block. -/
def padCopy (v : ℕ) (S : Finset α) (k : ℕ) : Finset (Padded α) :=
  S.image Sum.inl ∪ padBlock v S k

lemma mem_padBlock {v : ℕ} {S : Finset α} {k : ℕ} {x : Padded α} :
    x ∈ padBlock v S k ↔
      ∃ i, i ∈ Finset.Ico (k * (v - S.card)) ((k + 1) * (v - S.card)) ∧ Sum.inr (S, i) = x := by
  rw [padBlock, Finset.mem_image]

lemma inl_notMem_padBlock {v : ℕ} {S : Finset α} {k : ℕ} {x : α} :
    (Sum.inl x : Padded α) ∉ padBlock v S k := by
  intro h
  obtain ⟨i, -, hi⟩ := mem_padBlock.mp h
  exact Sum.inl_ne_inr hi.symm

lemma card_padBlock (v : ℕ) (S : Finset α) (k : ℕ) : (padBlock v S k).card = v - S.card := by
  rw [padBlock, Finset.card_image_of_injective _ (fun i j hij => by
    simpa using hij), Nat.card_Ico, Nat.succ_mul]
  omega

lemma card_padCopy {v : ℕ} {S : Finset α} (h : S.card ≤ v) (k : ℕ) :
    (padCopy v S k).card = v := by
  classical
  rw [padCopy, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Sum.inl_injective,
    card_padBlock]
  · omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact inl_notMem_padBlock hx'

lemma inl_mem_padCopy {v : ℕ} {S : Finset α} {k : ℕ} {x : α} :
    (Sum.inl x : Padded α) ∈ padCopy v S k ↔ x ∈ S := by
  classical
  rw [padCopy, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
      cases hxy
      exact hy
    · exact absurd h inl_notMem_padBlock
  · intro h
    exact Or.inl (Finset.mem_image_of_mem _ h)

lemma inr_mem_padCopy {v : ℕ} {S : Finset α} {k : ℕ} {U : Finset α} {i : ℕ} :
    (Sum.inr (U, i) : Padded α) ∈ padCopy v S k ↔
      U = S ∧ i ∈ Finset.Ico (k * (v - S.card)) ((k + 1) * (v - S.card)) := by
  classical
  rw [padCopy, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h
      exact absurd hy (by simp)
    · obtain ⟨j, hj, hji⟩ := mem_padBlock.mp h
      have : U = S ∧ i = j := by
        have := Sum.inr_injective hji
        exact ⟨(Prod.mk.injEq .. ▸ this).1.symm, (Prod.mk.injEq .. ▸ this).2.symm⟩
      exact ⟨this.1, this.2 ▸ hj⟩
  · rintro ⟨rfl, hi⟩
    exact Or.inr (mem_padBlock.mpr ⟨i, hi, rfl⟩)

/-- The padded system: `q` copies of each member of the support, each carrying its full
weight — so the mass is multiplied by `q` while the weight above any dummy stays `σ S`. -/
noncomputable def padWeight (X : Finset α) (σ : Finset α → ℕ) (v q : ℕ) :
    Finset (Padded α) → ℕ :=
  fun P => ∑ Sk ∈ (supp X σ) ×ˢ Finset.range q, if padCopy v Sk.1 Sk.2 = P then σ Sk.1 else 0

/-- The padded ground set. -/
noncomputable def padGround (X : Finset α) (σ : Finset α → ℕ) (v q : ℕ) : Finset (Padded α) :=
  X.image Sum.inl ∪ ((supp X σ) ×ˢ Finset.range q).biUnion fun Sk => padBlock v Sk.1 Sk.2

lemma padCopy_subset_padGround {X : Finset α} {σ : Finset α → ℕ} {v q : ℕ} {S : Finset α}
    {k : ℕ} (hS : S ∈ supp X σ) (hk : k ∈ Finset.range q) :
    padCopy v S k ⊆ padGround X σ v q := by
  classical
  intro x hx
  rw [padCopy, Finset.mem_union] at hx
  rw [padGround, Finset.mem_union]
  rcases hx with h | h
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    exact Or.inl (Finset.mem_image_of_mem _ (subset_of_mem_supp hS hy))
  · refine Or.inr (Finset.mem_biUnion.mpr ⟨(S, k), ?_, h⟩)
    rw [Finset.mem_product]
    exact ⟨hS, hk⟩

/-! ## The three properties -/

/-- The padded system is supported on the padded copies, hence `v`-uniform. -/
lemma padWeight_ne_zero {X : Finset α} {σ : Finset α → ℕ} {v q : ℕ} {P : Finset (Padded α)}
    (h : padWeight X σ v q P ≠ 0) :
    ∃ S ∈ supp X σ, ∃ k ∈ Finset.range q, padCopy v S k = P := by
  classical
  rw [padWeight] at h
  obtain ⟨Sk, hSk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_product] at hSk
  by_cases hc : padCopy v Sk.1 Sk.2 = P
  · exact ⟨Sk.1, hSk.1, Sk.2, hSk.2, hc⟩
  · rw [if_neg hc] at hne
    exact absurd rfl hne

lemma wBounded_padWeight {X : Finset α} {σ : Finset α → ℕ} {v q : ℕ}
    (hb : WBounded X v σ) : WBounded (padGround X σ v q) v (padWeight X σ v q) := by
  intro P hP
  obtain ⟨S, hS, k, hk, rfl⟩ := padWeight_ne_zero hP
  exact ⟨padCopy_subset_padGround hS hk,
    le_of_eq (card_padCopy (hb S (mem_supp.mp hS).2).2 k)⟩

lemma suppUniform_padWeight {X : Finset α} {σ : Finset α → ℕ} {v q : ℕ}
    (hb : WBounded X v σ) : SuppUniform (padGround X σ v q) (padWeight X σ v q) v := by
  intro P hP
  obtain ⟨S, hS, k, hk, rfl⟩ := padWeight_ne_zero (mem_supp.mp hP).2
  exact card_padCopy (hb S (mem_supp.mp hS).2).2 k

/-- The link of the padded system, as a sum over the copies. -/
lemma wLink_padWeight (X : Finset α) (σ : Finset α → ℕ) (v q : ℕ) (T : Finset (Padded α)) :
    wLink (padGround X σ v q) (padWeight X σ v q) T
      = ∑ Sk ∈ (supp X σ) ×ˢ Finset.range q,
          if T ⊆ padCopy v Sk.1 Sk.2 then σ Sk.1 else 0 := by
  classical
  rw [wLink]
  simp only [padWeight]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Sk hSk => ?_
  rw [Finset.mem_product] at hSk
  by_cases hT : T ⊆ padCopy v Sk.1 Sk.2
  · rw [if_pos hT]
    rw [Finset.sum_eq_single (padCopy v Sk.1 Sk.2)]
    · rw [if_pos rfl]
    · intro P _ hne
      rw [if_neg (fun hc => hne hc.symm)]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (padCopy_subset_padGround hSk.1 hSk.2), hT⟩) hmem
  · rw [if_neg hT]
    refine Finset.sum_eq_zero fun P hP => ?_
    rw [Finset.mem_filter] at hP
    by_cases hc : padCopy v Sk.1 Sk.2 = P
    · exact absurd (hc ▸ hP.2) hT
    · rw [if_neg hc]

/-- The mass is multiplied by `q`. -/
lemma wTotal_padWeight (X : Finset α) (σ : Finset α → ℕ) (v q : ℕ) :
    wTotal (padGround X σ v q) (padWeight X σ v q) = q * wTotal X σ := by
  classical
  have h := wLink_padWeight X σ v q ∅
  rw [wLink_empty] at h
  rw [h]
  have h1 : ∀ Sk ∈ (supp X σ) ×ˢ Finset.range q,
      (if (∅ : Finset (Padded α)) ⊆ padCopy v Sk.1 Sk.2 then σ Sk.1 else 0) = σ Sk.1 := by
    intro Sk _
    rw [if_pos (Finset.empty_subset _)]
  rw [Finset.sum_congr rfl h1, Finset.sum_product]
  have h2 : ∀ S ∈ supp X σ, ∑ _k ∈ Finset.range q, σ S = q * σ S := by
    intro S _
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  congr 1
  -- `∑_{S ∈ supp} σ S = wTotal X σ`
  have := wTotal_eq_sum_supp X σ
  exact_mod_cast this.symm

/-- **The padded system is spread**, with `M` scaled by `q` — the point of the construction.

At a `T` containing a dummy, only one copy can contain `T`, so the link carries just `σ S`,
and `σ S·κ^{|T|} ≤ M·κ^v ≤ q·M`. At a `T` inside the original ground set, the link is `q` times
the original one. Both need `q ≥ κ^v`, which is the "large enough factor" of the paper. -/
lemma wLinkBounded_padWeight {X : Finset α} {σ : Finset α → ℕ} {M κ : ℝ} {v q : ℕ}
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ) (hκ : 1 ≤ κ) (hM : 0 ≤ M)
    (hE : σ ∅ = 0) (hq : κ ^ v ≤ (q : ℝ)) :
    WLinkBounded (padGround X σ v q) (padWeight X σ v q) ((q : ℝ) * M) κ := by
  classical
  intro T hT
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  rw [wLink_padWeight, ← Finset.sum_filter]
  set F := ((supp X σ) ×ˢ Finset.range q).filter fun Sk => T ⊆ padCopy v Sk.1 Sk.2 with hF
  by_cases hd : ∃ U : Finset α, ∃ i : ℕ, (Sum.inr (U, i) : Padded α) ∈ T
  · -- a dummy pins down the copy
    obtain ⟨U, i, hUi⟩ := hd
    have hsingle : F ⊆ {(U, i / (v - U.card))} := by
      intro Sk hSk
      rw [hF, Finset.mem_filter, Finset.mem_product] at hSk
      have hmem := hSk.2 hUi
      rw [inr_mem_padCopy] at hmem
      obtain ⟨hUS, hi⟩ := hmem
      rw [Finset.mem_Ico] at hi
      have hpos : 0 < v - Sk.1.card := by
        by_contra hc
        push Not at hc
        have h0 : v - Sk.1.card = 0 := by omega
        rw [h0, Nat.mul_zero, Nat.mul_zero] at hi
        omega
      have hk : Sk.2 = i / (v - Sk.1.card) := (Nat.div_eq_of_lt_le hi.1 hi.2).symm
      rw [Finset.mem_singleton, Prod.ext_iff]
      subst hUS
      exact ⟨rfl, hk⟩
    have hsum : ∑ Sk ∈ F, (σ Sk.1 : ℝ) ≤ (σ U : ℝ) := by
      calc ∑ Sk ∈ F, (σ Sk.1 : ℝ)
          ≤ ∑ Sk ∈ ({(U, i / (v - U.card))} : Finset (Finset α × ℕ)), (σ Sk.1 : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsingle fun _ _ _ => by positivity
        _ = (σ U : ℝ) := by rw [Finset.sum_singleton]
    -- `σ U ≤ M`, and `|T| ≤ v` whenever the link is nonzero
    by_cases hFe : F = ∅
    · rw [hFe]
      simp only [Finset.sum_empty, Nat.cast_zero, zero_mul]
      positivity
    · obtain ⟨Sk, hSk⟩ := Finset.nonempty_of_ne_empty hFe
      rw [hF, Finset.mem_filter, Finset.mem_product] at hSk
      have hTv : T.card ≤ v := by
        have h1 : T.card ≤ (padCopy v Sk.1 Sk.2).card := Finset.card_le_card hSk.2
        rwa [card_padCopy (hb Sk.1 (mem_supp.mp hSk.1.1).2).2] at h1
      have hσU : (σ U : ℝ) ≤ M := by
        by_cases hU0 : σ U = 0
        · rw [hU0]; exact_mod_cast hM
        · have hUX : U ⊆ X := (hb U hU0).1
          have hUsupp : U ∈ supp X σ := mem_supp.mpr ⟨hUX, hU0⟩
          have hUne : U.Nonempty := by
            rcases Finset.eq_empty_or_nonempty U with rfl | h
            · exact absurd hE hU0
            · exact h
          have h1 : (σ U : ℝ) ≤ (wLink X σ U : ℝ) := by
            have : σ U ≤ wLink X σ U := by
              rw [wLink]
              refine Finset.single_le_sum (f := σ) (fun _ _ => Nat.zero_le _) ?_
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_powerset.mpr hUX, Finset.Subset.rfl⟩
            exact_mod_cast this
          have h2 := hl U hUne
          have h3 : (1 : ℝ) ≤ κ ^ U.card := one_le_pow₀ hκ
          nlinarith [h1, h2, h3, Nat.cast_nonneg (α := ℝ) (wLink X σ U)]
      have hpow : κ ^ T.card ≤ κ ^ v := pow_le_pow_right₀ hκ hTv
      have hcast : ((∑ Sk ∈ F, σ Sk.1 : ℕ) : ℝ) = ∑ Sk ∈ F, (σ Sk.1 : ℝ) := by push_cast; ring
      rw [hcast]
      calc (∑ Sk ∈ F, (σ Sk.1 : ℝ)) * κ ^ T.card ≤ (σ U : ℝ) * κ ^ v := by
            refine mul_le_mul hsum hpow (by positivity) (by positivity)
        _ ≤ M * (q : ℝ) := by
            refine mul_le_mul hσU hq (by positivity) hM
        _ = (q : ℝ) * M := by ring
  · -- no dummy: the link is `q` times the original one
    push Not at hd
    set TX := unpad T with hTX
    have hTeq : T = TX.image Sum.inl := by
      ext x
      constructor
      · intro hx
        cases x with
        | inl a => exact Finset.mem_image_of_mem _ (mem_unpad.mpr hx)
        | inr Ui => exact absurd hx (hd Ui.1 Ui.2)
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact mem_unpad.mp ha
    have hiff : ∀ S : Finset α, ∀ k : ℕ, T ⊆ padCopy v S k ↔ TX ⊆ S := by
      intro S k
      constructor
      · intro hsub x hx
        have hxT : (Sum.inl x : Padded α) ∈ T := mem_unpad.mp hx
        exact inl_mem_padCopy.mp (hsub hxT)
      · intro hsub x hx
        rw [hTeq] at hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact inl_mem_padCopy.mpr (hsub ha)
    have hTXcard : TX.card = T.card := by
      rw [hTeq, Finset.card_image_of_injective _ Sum.inl_injective]
    have hTXne : TX.Nonempty := by
      obtain ⟨x, hx⟩ := hT
      cases x with
      | inl a => exact ⟨a, mem_unpad.mpr hx⟩
      | inr Ui => exact absurd hx (hd Ui.1 Ui.2)
    have hsum : ∑ Sk ∈ F, σ Sk.1 = q * wLink X σ TX := by
      have h1 : F = ((supp X σ).filter fun S => TX ⊆ S) ×ˢ Finset.range q := by
        rw [hF]
        ext Sk
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_filter,
          hiff Sk.1 Sk.2]
        tauto
      rw [h1, Finset.sum_product]
      have h2 : ∀ S ∈ (supp X σ).filter fun S => TX ⊆ S, ∑ _k ∈ Finset.range q, σ S = q * σ S := by
        intro S _
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
      congr 1
      -- the support-restricted link is the link
      rw [wLink]
      refine Finset.sum_subset ?_ ?_
      · intro S hS
        rw [Finset.mem_filter] at hS ⊢
        exact ⟨Finset.mem_powerset.mpr (subset_of_mem_supp hS.1), hS.2⟩
      · intro S hS hSn
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        rw [Finset.mem_filter] at hSn
        by_contra hc
        exact hSn ⟨mem_supp.mpr ⟨hS.1, hc⟩, hS.2⟩
    rw [hsum, ← hTXcard]
    have h2 := hl TX hTXne
    have hcast : (((q * wLink X σ TX : ℕ)) : ℝ) = (q : ℝ) * (wLink X σ TX : ℝ) := by push_cast; ring
    rw [hcast, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)

/-- Every padded copy contains the original member — this is what makes covering transfer:
a set containing a member of the padded system contains a member of the original one. -/
lemma image_subset_padCopy (v : ℕ) (S : Finset α) (k : ℕ) :
    S.image Sum.inl ⊆ padCopy v S k := by
  rw [padCopy]
  exact Finset.subset_union_left

/-! ## The padding step, packaged -/

/-- **ALWZ's padding step of Lemma 2.10.** A `≤v`-bounded `(M,κ)`-spread system with no empty
member becomes, on an enlarged ground set, a `v`-**uniform** `(q·M, κ)`-spread system of mass
`q·wTotal` whose every member contains an original member — provided `q ≥ κ^v`, which is the
paper's "scale by a large enough factor so that a negligible amount of weight falls on each
dummy element".

The scaling is not cosmetic: with `q = 1` (one padded copy per member), the third clause need
not hold, since the link at a member's own dummies can carry its whole weight.
-/
theorem exists_padding {X : Finset α} {σ : Finset α → ℕ} {M κ : ℝ} {v : ℕ} (q : ℕ)
    (hb : WBounded X v σ) (hl : WLinkBounded X σ M κ) (hκ : 1 ≤ κ) (hM : 0 ≤ M)
    (hE : σ ∅ = 0) (hq : κ ^ v ≤ (q : ℝ)) :
    WBounded (padGround X σ v q) v (padWeight X σ v q)
      ∧ SuppUniform (padGround X σ v q) (padWeight X σ v q) v
      ∧ WLinkBounded (padGround X σ v q) (padWeight X σ v q) ((q : ℝ) * M) κ
      ∧ wTotal (padGround X σ v q) (padWeight X σ v q) = q * wTotal X σ
      ∧ ∀ P ∈ supp (padGround X σ v q) (padWeight X σ v q),
          ∃ S ∈ supp X σ, S.image Sum.inl ⊆ P := by
  refine ⟨wBounded_padWeight hb, suppUniform_padWeight hb,
    wLinkBounded_padWeight hb hl hκ hM hE hq, wTotal_padWeight X σ v q, ?_⟩
  intro P hP
  obtain ⟨S, hS, k, -, rfl⟩ := padWeight_ne_zero (mem_supp.mp hP).2
  exact ⟨S, hS, image_subset_padCopy v S k⟩

/-- **The point of the scaling**: the Janson budget is *unchanged*. The bottom step's exponent
depends on the mass only through the ratio `A/M`, and padding multiplies both by `q`. -/
lemma janson_exponent_padding {A M κ p : ℝ} {q v : ℕ} (hq : 0 < (q : ℝ)) (hM : M ≠ 0)
    (hv : (v : ℝ) ≠ 0) :
    ((q : ℝ) * A) * κ * p / (8 * ((q : ℝ) * M) * (v : ℝ)) = A * κ * p / (8 * M * (v : ℝ)) := by
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq
  field_simp

end Sunflower

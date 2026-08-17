/-
# Rao's residual `χ`

Rao's Definition 3: given a family `𝓕`, a member `S` and a set `W`, let

  `χ(𝓕, S, W) = T \ W`,  where `T ∈ 𝓕` minimizes `|T \ W|` among members with `T ⊆ S ∪ W`.

So `χ` measures how much of *some* member of `𝓕` is still missing from `W`, given the freedom
to switch from `S` to any member that `S ∪ W` already contains. It is the quantity the coding
argument contracts: Rao's Lemma 4 shows `E|χ|` drops by a factor `2/3` per round, and
`χ = ∅` exactly when `W` contains a member — which is the covering event.

Two design choices, both from the plan:

* **families, not sequences.** Rao states everything for sequences `S₁,…,S_ℓ` (allowing
  repeats) because some applications need it. The sunflower theorem and the BCW note only need
  distinct sets, so `χ` is defined on a `Finset (Finset α)`.
* **no order on `α`.** Rao breaks ties by "the smallest such `y`", which needs an order on the
  index set. Here the tie-break is `Finset.exists_min_image` + `Classical.choose`: a function
  of `(𝓕, S, W)` and nothing else, which is all the decoder needs — it never has to *compute*
  the witness, only to know that both encoder and decoder mean the same one.

Everything is division-free and counting-based (`chiSum` is a sum over `powersetCard`), in the
style of `Bridge.lean`.
-/
import Sunflower.Spread
import Sunflower.Bridge

open Finset

namespace Sunflower

namespace Rao

variable {α : Type*} [DecidableEq α]

/-- The members of `𝓕` that `S ∪ W` already contains — the candidates to switch to. -/
def cands (𝓕 : Finset (Finset α)) (S W : Finset α) : Finset (Finset α) :=
  𝓕.filter fun T => T ⊆ S ∪ W

lemma mem_cands {𝓕 : Finset (Finset α)} {S W T : Finset α} :
    T ∈ cands 𝓕 S W ↔ T ∈ 𝓕 ∧ T ⊆ S ∪ W := by
  rw [cands, Finset.mem_filter]

lemma cands_nonempty {𝓕 : Finset (Finset α)} {S W : Finset α} (hS : S ∈ 𝓕) :
    (cands 𝓕 S W).Nonempty :=
  ⟨S, mem_cands.mpr ⟨hS, Finset.subset_union_left⟩⟩

/-- The member of `𝓕` that `χ` switches to: a minimizer of `|T \ W|` over the candidates
(and `S` itself if there are none, which cannot happen for `S ∈ 𝓕`). -/
noncomputable def chiWitness (𝓕 : Finset (Finset α)) (S W : Finset α) : Finset α :=
  if h : (cands 𝓕 S W).Nonempty then
    Classical.choose (Finset.exists_min_image (cands 𝓕 S W) (fun T => (T \ W).card) h)
  else S

/-- **Rao's residual.** -/
noncomputable def chi (𝓕 : Finset (Finset α)) (S W : Finset α) : Finset α :=
  chiWitness 𝓕 S W \ W

section
variable {𝓕 : Finset (Finset α)} {S W U : Finset α}

lemma chiWitness_mem_cands (hS : S ∈ 𝓕) : chiWitness 𝓕 S W ∈ cands 𝓕 S W := by
  rw [chiWitness, dif_pos (cands_nonempty hS)]
  exact (Classical.choose_spec
    (Finset.exists_min_image (cands 𝓕 S W) (fun T => (T \ W).card) (cands_nonempty hS))).1

lemma chiWitness_mem (hS : S ∈ 𝓕) : chiWitness 𝓕 S W ∈ 𝓕 :=
  (mem_cands.mp (chiWitness_mem_cands hS)).1

lemma chiWitness_subset (hS : S ∈ 𝓕) : chiWitness 𝓕 S W ⊆ S ∪ W :=
  (mem_cands.mp (chiWitness_mem_cands hS)).2

/-- Minimality: no candidate has a smaller residual. -/
lemma chi_card_le_of_cand (hS : S ∈ 𝓕) {T : Finset α} (hT : T ∈ 𝓕) (hTsub : T ⊆ S ∪ W) :
    (chi 𝓕 S W).card ≤ (T \ W).card := by
  rw [chi, chiWitness, dif_pos (cands_nonempty hS)]
  exact (Classical.choose_spec
    (Finset.exists_min_image (cands 𝓕 S W) (fun T => (T \ W).card)
      (cands_nonempty hS))).2 T (mem_cands.mpr ⟨hT, hTsub⟩)

/-- `χ ⊆ S`: the witness lies in `S ∪ W`, and `W` is removed. -/
lemma chi_subset (hS : S ∈ 𝓕) : chi 𝓕 S W ⊆ S := by
  intro x hx
  rw [chi, Finset.mem_sdiff] at hx
  rcases Finset.mem_union.mp (chiWitness_subset hS hx.1) with h | h
  · exact h
  · exact absurd h hx.2

/-- Taking `S` itself as the candidate: `|χ| ≤ |S \ W|`. -/
lemma chi_card_le_sdiff (hS : S ∈ 𝓕) : (chi 𝓕 S W).card ≤ (S \ W).card :=
  chi_card_le_of_cand hS hS Finset.subset_union_left

/-- **Monotonicity in `W`** (Rao's `|χ(x,U)| ≥ |χ(x,W)|` for `U ⊆ W`): revealing more of the
ground set cannot increase the residual. The witness for `U` is still a candidate for `W`. -/
lemma chi_card_mono (hS : S ∈ 𝓕) (hUW : U ⊆ W) :
    (chi 𝓕 S W).card ≤ (chi 𝓕 S U).card := by
  have hT : chiWitness 𝓕 S U ∈ 𝓕 := chiWitness_mem hS
  have hTsub : chiWitness 𝓕 S U ⊆ S ∪ W :=
    le_trans (chiWitness_subset hS) (Finset.union_subset_union_right hUW)
  refine le_trans (chi_card_le_of_cand hS hT hTsub) ?_
  exact Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hUW)

/-- **`χ` vanishes exactly on the covering event.** -/
lemma chi_eq_empty_iff (hS : S ∈ 𝓕) : chi 𝓕 S W = ∅ ↔ ∃ T ∈ 𝓕, T ⊆ W := by
  constructor
  · intro h
    refine ⟨chiWitness 𝓕 S W, chiWitness_mem hS, ?_⟩
    intro x hx
    by_contra hxW
    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxW⟩) (by rw [chi] at h; rw [h]; simp)
  · rintro ⟨T, hT, hTW⟩
    have hTsub : T ⊆ S ∪ W := le_trans hTW Finset.subset_union_right
    have h0 : (T \ W).card = 0 := by
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
      exact hTW
    have := chi_card_le_of_cand hS hT hTsub
    rw [h0] at this
    exact Finset.card_eq_zero.mp (Nat.le_zero.mp this)

/-- If one residual is empty then all of them are: both say that `W` covers a member. -/
lemma chi_eq_empty_congr {S' : Finset α} (hS : S ∈ 𝓕) (hS' : S' ∈ 𝓕)
    (h : chi 𝓕 S W = ∅) : chi 𝓕 S' W = ∅ :=
  (chi_eq_empty_iff hS').mpr ((chi_eq_empty_iff hS).mp h)

/-- On an uncovered `W`, every residual is nonempty, hence of size at least `1`. -/
lemma one_le_chi_card_of_uncovered (hS : S ∈ 𝓕) (h : ¬ ∃ T ∈ 𝓕, T ⊆ W) :
    1 ≤ (chi 𝓕 S W).card := by
  rcases Nat.eq_zero_or_pos (chi 𝓕 S W).card with h0 | h1
  · exact absurd ((chi_eq_empty_iff hS).mp (Finset.card_eq_zero.mp h0)) h
  · exact h1

end

/-! ## The summed residual

Rao's `E[|χ(X,W)|]` over a uniform member `X` and a uniform `m`-set `W`, kept as an integer
sum: dividing by `|𝓕|·C(n,m)` is deferred to the very end. -/

/-- `∑_{|W| = m} ∑_{S ∈ 𝓕} |χ(𝓕, S, W)|`. -/
noncomputable def chiSum (X : Finset α) (𝓕 : Finset (Finset α)) (m : ℕ) : ℕ :=
  ∑ W ∈ X.powersetCard m, ∑ S ∈ 𝓕, (chi 𝓕 S W).card

/-- **The residual controls the uncovered count** (Phase C's last step). Every uncovered `W`
contributes at least `|𝓕|` to `chiSum`, so a small summed residual means few uncovered sets.

`fixedCount X P m` counts the `m`-subsets of `X` satisfying `P`; here `P` is "no member of `𝓕`
is contained in `W`", the failure event. -/
theorem fixedCount_mul_card_le_chiSum (X : Finset α) (𝓕 : Finset (Finset α)) (m : ℕ) :
    fixedCount X (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W) m * 𝓕.card ≤ chiSum X 𝓕 m := by
  classical
  rw [chiSum, fixedCount]
  calc ((X.powersetCard m).filter (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W)).card * 𝓕.card
      = ∑ _W ∈ (X.powersetCard m).filter (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W), 𝓕.card := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ W ∈ (X.powersetCard m).filter (fun W => ¬ ∃ T ∈ 𝓕, T ⊆ W),
          ∑ S ∈ 𝓕, (chi 𝓕 S W).card := by
        refine Finset.sum_le_sum fun W hW => ?_
        rw [Finset.mem_filter] at hW
        calc 𝓕.card = ∑ _S ∈ 𝓕, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ S ∈ 𝓕, (chi 𝓕 S W).card :=
              Finset.sum_le_sum fun S hS => one_le_chi_card_of_uncovered hS hW.2
    _ ≤ ∑ W ∈ X.powersetCard m, ∑ S ∈ 𝓕, (chi 𝓕 S W).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The trivial bound `|χ| ≤ w` for a `w`-uniform family, hence `chiSum ≤ w·|𝓕|·C(n,m)`:
the starting point (`m = 0`) of Rao's `k·(2/3)^m` induction. -/
theorem chiSum_le {w m : ℕ} {X : Finset α} {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕) :
    chiSum X 𝓕 m ≤ (X.card.choose m) * (𝓕.card * w) := by
  classical
  rw [chiSum]
  calc ∑ W ∈ X.powersetCard m, ∑ S ∈ 𝓕, (chi 𝓕 S W).card
      ≤ ∑ _W ∈ X.powersetCard m, ∑ _S ∈ 𝓕, w := by
        refine Finset.sum_le_sum fun W _ => Finset.sum_le_sum fun S hS => ?_
        calc (chi 𝓕 S W).card ≤ S.card := Finset.card_le_card (chi_subset hS)
          _ = w := hu hS
    _ = (X.card.choose m) * (𝓕.card * w) := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
          Finset.card_powersetCard]

end Rao

end Sunflower

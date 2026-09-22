/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SubdivisionPacking
import TSPGap.BlackBoxes

/-!
# The Edmonds–Johnson `O`-join bound

**KKO22 Proposition 2.4** (`edmondsJohnson_ojoin`): for nonnegative costs `c` on the complete
graph `K_n`, an even set `O`, and `y ≥ 0` with `y(δ(S)) ≥ 1` for every `S` with `|S ∩ O|`
odd, some `O`-join `J` has `c(J) ≤ ⟨c, y⟩`.

The route (`OJOIN_DESIGN.md`) is packing plus weak duality, with no LP duality:

* **weak duality** (`card_le_sum_of_packing`): a family of `k` `T`-cuts with every edge in
  at most `m e` of them gives `k ≤ ∑_e y_e m_e` for every such `y` — each cut carries
  `y`-mass at least `1`;
* **positive integer weights** (`exists_join_le_of_weights`): the subdivision packing
  (`exists_packing_of_weights`, from Seymour's theorem) has `k = 2 w(J₀)` and `m e = 2 w e`
  for a `w`-minimum `T`-join `J₀`, so `w(J₀) ≤ ∑_e y_e w_e`;
* **real costs** (`exists_join_cost_le`): for `k ≥ 1` the weights `w_k e := ⌈k c_e⌉ + 1` are
  positive integers with `k c_e ≤ w_k e ≤ k c_e + 2`; the `c`-minimum `T`-join `J*` then has
  `c(J*) ≤ w_k(J_k)/k ≤ ∑ y_e w_k(e)/k ≤ ⟨c, y⟩ + 2 ∑ y_e / k` for every `k`, hence
  `c(J*) ≤ ⟨c, y⟩`.  No limit of packings is taken.

Weak duality completes the consumer argument, but the existence of the packing carries the
full min–max content: Seymour's theorem is the substantive replacement for LP duality.

The complete graph is the multigraph `knGraph n` on the off-diagonal `Sym2 (Fin n)`; its cuts
are `cutEdges`, its degrees `degIn`, and an even `O` has an `O`-join (`exists_join_kn`, pairing
up `O`).  Empty `O` (the empty join), zero costs, and zero coordinates of `y` need no
special treatment.
-/

namespace TSPGap

open Finset
open Classical
open scoped symmDiff

namespace MGraph

variable {V E : Type*} [Fintype V] [Fintype E] (G : MGraph V E)

/-! ### Weak duality -/

/-- **Weak duality.**  `k` sets with an odd number of terminals, every edge in at most `m e`
of their cuts, bound every `y ≥ 0` with `y(δ(U)) ≥ 1` on the `T`-odd sets from below. -/
theorem card_le_sum_of_packing {T : Finset V} {k : ℕ} {S : Fin k → Finset V}
    (hS : ∀ i, Odd (S i ∩ T).card) {m : E → ℕ}
    (hm : ∀ e, (univ.filter fun i => e ∈ G.cut (S i)).card ≤ m e)
    {y : E → ℝ} (hy0 : ∀ e, 0 ≤ y e)
    (hycut : ∀ U : Finset V, Odd (U ∩ T).card → 1 ≤ ∑ e ∈ G.cut U, y e) :
    (k : ℝ) ≤ ∑ e, y e * m e := by
  have h1 : (k : ℝ) ≤ ∑ i : Fin k, ∑ e ∈ G.cut (S i), y e := by
    calc (k : ℝ) = ∑ i : Fin k, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin k, ∑ e ∈ G.cut (S i), y e := sum_le_sum fun i _ => hycut _ (hS i)
  have h2 : ∑ i : Fin k, ∑ e ∈ G.cut (S i), y e =
      ∑ e, y e * ((univ.filter fun i => e ∈ G.cut (S i)).card : ℝ) := by
    have : ∀ i : Fin k, ∑ e ∈ G.cut (S i), y e =
        ∑ e, if e ∈ G.cut (S i) then y e else 0 := by
      intro i
      rw [← sum_filter, filter_mem_eq_inter, univ_inter]
    simp only [this]
    rw [sum_comm]
    refine sum_congr rfl fun e _ => ?_
    rw [← sum_boole, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have h3 : ∑ e, y e * ((univ.filter fun i => e ∈ G.cut (S i)).card : ℝ) ≤
      ∑ e, y e * m e :=
    sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (by exact_mod_cast hm e) (hy0 e)
  linarith

/-! ### Positive integer weights -/

/-- **Edmonds–Johnson for positive integer weights.** -/
theorem exists_join_le_of_weights (w : E → ℕ) (hw : ∀ e, 1 ≤ w e) {T : Finset V}
    (hT : ∃ J, G.IsJoin T J) {y : E → ℝ} (hy0 : ∀ e, 0 ≤ y e)
    (hycut : ∀ U : Finset V, Odd (U ∩ T).card → 1 ≤ ∑ e ∈ G.cut U, y e) :
    ∃ J, G.IsJoin T J ∧ (∑ e ∈ J, (w e : ℝ)) ≤ ∑ e, y e * w e := by
  obtain ⟨J₁, hJ₁⟩ := hT
  obtain ⟨J₀, hJ₀, hmin⟩ := exists_min_image (univ.filter fun J => G.IsJoin T J)
    (fun J => ∑ e ∈ J, w e) ⟨J₁, by simpa using hJ₁⟩
  rw [mem_filter] at hJ₀
  have hmin' : ∀ J, G.IsJoin T J → ∑ e ∈ J₀, w e ≤ ∑ e ∈ J, w e :=
    fun J hJ => hmin J (by simpa using hJ)
  obtain ⟨k, S, hk, hS, hcount⟩ := G.exists_packing_of_weights w hw hJ₀.2 hmin'
  have h := G.card_le_sum_of_packing hS hcount hy0 hycut
  rw [hk] at h
  push_cast at h
  rw [show ∑ e, y e * (2 * (w e : ℝ)) = 2 * ∑ e, y e * w e by
    rw [mul_sum]; exact sum_congr rfl fun e _ => by ring] at h
  exact ⟨J₀, hJ₀.2, by linarith⟩

/-! ### Real costs -/

/-- **Edmonds–Johnson for nonnegative real costs**: the `c`-minimum `T`-join costs at most
`∑_e y_e c_e`. -/
theorem exists_join_cost_le (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) {T : Finset V}
    (hT : ∃ J, G.IsJoin T J) {y : E → ℝ} (hy0 : ∀ e, 0 ≤ y e)
    (hycut : ∀ U : Finset V, Odd (U ∩ T).card → 1 ≤ ∑ e ∈ G.cut U, y e) :
    ∃ J, G.IsJoin T J ∧ ∑ e ∈ J, c e ≤ ∑ e, y e * c e := by
  obtain ⟨J₁, hJ₁⟩ := hT
  obtain ⟨J, hJ, hmin⟩ := exists_min_image (univ.filter fun J => G.IsJoin T J)
    (fun J => ∑ e ∈ J, c e) ⟨J₁, by simpa using hJ₁⟩
  rw [mem_filter] at hJ
  refine ⟨J, hJ.2, le_of_forall_pos_lt_add fun ε hε => ?_⟩
  set Y : ℝ := ∑ e, y e with hY
  have hY0 : 0 ≤ Y := sum_nonneg fun e _ => hy0 e
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * Y / ε)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hk
  have hkY : 2 * Y < k * ε := by
    rw [div_lt_iff₀ hε] at hk
    linarith
  -- the integer weights
  set w : E → ℕ := fun e => ⌈(k : ℝ) * c e⌉₊ + 1 with hw
  have hw1 : ∀ e, 1 ≤ w e := fun e => by simp [hw]
  have hwlo : ∀ e, (k : ℝ) * c e ≤ w e := fun e => by
    simp only [hw]
    push_cast
    linarith [Nat.le_ceil ((k : ℝ) * c e)]
  have hwhi : ∀ e, (w e : ℝ) ≤ k * c e + 2 := fun e => by
    simp only [hw]
    push_cast
    have := Nat.ceil_lt_add_one (mul_nonneg hk0.le (hc e))
    linarith
  obtain ⟨Jk, hJk, hJkw⟩ := G.exists_join_le_of_weights w hw1 ⟨J₁, hJ₁⟩ hy0 hycut
  have h1 : ∑ e ∈ J, c e ≤ ∑ e ∈ Jk, c e := hmin Jk (by simpa using hJk)
  have h2 : (k : ℝ) * ∑ e ∈ Jk, c e ≤ ∑ e ∈ Jk, (w e : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum fun e _ => hwlo e
  have h3 : ∑ e, y e * (w e : ℝ) ≤ ∑ e, y e * (k * c e + 2) :=
    sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hwhi e) (hy0 e)
  have h4 : ∑ e, y e * ((k : ℝ) * c e + 2) = k * ∑ e, y e * c e + 2 * Y := by
    rw [hY, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by ring
  have h5 : (k : ℝ) * ∑ e ∈ J, c e < k * (∑ e, y e * c e + ε) := by
    calc (k : ℝ) * ∑ e ∈ J, c e ≤ k * ∑ e ∈ Jk, c e :=
          mul_le_mul_of_nonneg_left h1 hk0.le
      _ ≤ ∑ e ∈ Jk, (w e : ℝ) := h2
      _ ≤ ∑ e, y e * (w e : ℝ) := hJkw
      _ ≤ k * ∑ e, y e * c e + 2 * Y := by rw [← h4]; exact h3
      _ < k * (∑ e, y e * c e + ε) := by linarith
  exact lt_of_mul_lt_mul_left h5 hk0.le

/-- The odd vertices of a single edge are its two ends. -/
theorem odd_singleton {e : E} {a b : V} (hab : G.ends e = s(a, b)) :
    G.odd {e} = {a, b} := by
  ext v
  rw [mem_odd, deg, inc, filter_singleton]
  by_cases hv : v ∈ G.ends e
  · rw [if_pos hv, card_singleton]
    rw [hab, Sym2.mem_iff] at hv
    simp [hv, odd_one]
  · rw [if_neg hv, card_empty]
    rw [hab, Sym2.mem_iff] at hv
    push Not at hv
    simp [hv.1, hv.2]

/-- In a multigraph joining every pair of distinct vertices, an even vertex set has a join:
pair up the vertices. -/
theorem exists_join_of_complete (hG : ∀ a b : V, a ≠ b → ∃ e, G.ends e = s(a, b))
    (O : Finset V) (hO : Even O.card) : ∃ J, G.IsJoin O J := by
  induction hcard : O.card using Nat.strong_induction_on generalizing O with
  | _ m ih =>
  rcases O.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨∅, by rw [IsJoin, G.isEven_iff_odd_eq_empty.mp G.isEven_empty]⟩
  · have h2 : 2 ≤ O.card := by
      obtain ⟨r, hr⟩ := hO
      have := card_pos.mpr ⟨a, ha⟩
      omega
    obtain ⟨b, hb⟩ : (O.erase a).Nonempty := by
      rw [← card_pos, card_erase_of_mem ha]; omega
    have hba : b ≠ a := (mem_erase.mp hb).1
    have hbO : b ∈ O := (mem_erase.mp hb).2
    set O' := (O.erase a).erase b with hO'
    have hcard' : O'.card = O.card - 2 := by
      rw [hO', card_erase_of_mem hb, card_erase_of_mem ha]; omega
    obtain ⟨J', hJ'⟩ := ih O'.card (by omega) O' (by
      obtain ⟨r, hr⟩ := hO
      exact ⟨r - 1, by omega⟩) rfl
    obtain ⟨e, he⟩ := hG a b hba.symm
    refine ⟨J' ∆ {e}, ?_⟩
    rw [IsJoin, odd_symmDiff, hJ', G.odd_singleton he]
    ext v
    rw [mem_symmDiff, hO', mem_erase, mem_erase, mem_insert, mem_singleton]
    by_cases hva : v = a
    · subst hva; simp [ha]
    · by_cases hvb : v = b
      · subst hvb; simp [hbO, hba]
      · simp [hva, hvb]

end MGraph

/-! ### The complete graph -/

variable {n : ℕ}

/-- The complete graph `K_n` as a loopless multigraph on the off-diagonal `Sym2 (Fin n)`. -/
def knGraph (n : ℕ) : MGraph (Fin n) {e : Sym2 (Fin n) // ¬ e.IsDiag} where
  ends e := e.1
  loopless e := e.2

/-- An even vertex set of `K_n` has a join. -/
theorem exists_join_kn (O : Finset (Fin n)) (hO : Even O.card) :
    ∃ J, (knGraph n).IsJoin O J :=
  (knGraph n).exists_join_of_complete
    (fun a b hab => ⟨⟨s(a, b), by rw [Sym2.mk_isDiag_iff]; exact hab⟩, rfl⟩) O hO

/-- The cut of `K_n`, as a multigraph cut, is `cutEdges`. -/
theorem map_cut_kn (S : Finset (Fin n)) :
    ((knGraph n).cut S).map (Function.Embedding.subtype _) = cutEdges S := by
  ext e
  simp only [mem_map, Function.Embedding.coe_subtype, cutEdges, mem_filter, mem_univ, true_and,
    mem_compl]
  constructor
  · rintro ⟨⟨e, he⟩, hc, rfl⟩
    obtain ⟨a, b, hab, hne⟩ := (knGraph n).exists_ends_eq_ne ⟨e, he⟩
    change e = s(a, b) at hab
    subst hab
    rw [MGraph.mem_cut] at hc
    change (∃ x ∈ s(a, b), x ∈ S) ∧ ∃ x ∈ s(a, b), x ∉ S at hc
    simp only [Sym2.mem_iff] at hc
    obtain ⟨⟨x, hx, hxS⟩, ⟨y, hy, hyS⟩⟩ := hc
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd hxS hyS
    · exact ⟨x, hxS, y, hyS, rfl⟩
    · exact ⟨x, hxS, y, hyS, Sym2.eq_swap⟩
    · exact absurd hxS hyS
  · rintro ⟨u, hu, v, hv, rfl⟩
    have hne : u ≠ v := fun h => hv (h ▸ hu)
    refine ⟨⟨s(u, v), by rw [Sym2.mk_isDiag_iff]; exact hne⟩, ?_, rfl⟩
    rw [MGraph.mem_cut]
    exact ⟨⟨u, Sym2.mem_mk_left _ _, hu⟩, ⟨v, Sym2.mem_mk_right _ _, hv⟩⟩

theorem sum_cut_kn (y : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    ∑ e ∈ (knGraph n).cut S, y e.1 = cutSum y S := by
  rw [cutSum, ← map_cut_kn, sum_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Edmonds–Johnson O-join polyhedron** (KKO22 Prop 2.4), proved.
If `y ≥ 0` satisfies `y(δ(S)) ≥ 1` for every `O`-odd cut `S`, then some
`O`-join costs at most `⟨c, y⟩`. -/
theorem edmondsJohnson_ojoin {c : Sym2 (Fin n) → ℝ} (hc : ∀ e, 0 ≤ c e)
    (O : Finset (Fin n)) (hO : Even O.card)
    {y : Sym2 (Fin n) → ℝ} (hy0 : ∀ e, 0 ≤ y e)
    (hycut : ∀ S : Finset (Fin n), Odd (S ∩ O).card → 1 ≤ cutSum y S) :
    ∃ J : Finset (Sym2 (Fin n)),
      (∀ e ∈ J, ¬ e.IsDiag) ∧
      (∀ v, v ∈ O ↔ Odd (degIn J v)) ∧
      ∑ e ∈ J, c e ≤ lpCost c y := by
  obtain ⟨J', hJ', hcost⟩ := (knGraph n).exists_join_cost_le (fun e => c e.1) (fun e => hc e.1)
    (exists_join_kn O hO) (y := fun e => y e.1) (fun e => hy0 e.1)
    (fun U hU => by
      rw [sum_cut_kn]
      refine hycut U ?_
      convert hU using 3
      congr
      exact Subsingleton.elim _ _)
  refine ⟨J'.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro e he
    rw [mem_map] at he
    obtain ⟨⟨e, he'⟩, -, rfl⟩ := he
    exact he'
  · intro v
    have hdeg : degIn (J'.map (Function.Embedding.subtype _)) v = (knGraph n).deg J' v := by
      rw [degIn, MGraph.deg, MGraph.inc, filter_map, card_map]
      congr 1
      ext e
      simp only [mem_filter, Function.comp_apply, Function.Embedding.coe_subtype]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, e.2⟩⟩
    rw [(knGraph n).isJoin_iff.mp hJ' v, hdeg]
  · rw [sum_map, lpCost]
    refine le_trans hcost (le_of_eq ?_)
    rw [sum_subtype (edgeFinset n) (p := fun e : Sym2 (Fin n) => ¬ e.IsDiag)
      (fun e => by simp [edgeFinset])]
    exact sum_congr rfl fun e _ => mul_comm _ _

end TSPGap

/-
# ALWZ Lemma 3.1: Theorem 1.9 is tight up to the `o(1)` in the exponent

`KappaZeroPad.exists_isRobustSunflower_pad` says a `w`-uniform family of size `κ₀^w` with
`κ₀ = O(log w · log log w)` contains an `(a,b)`-robust sunflower. Lemma 3.1 is the converse
direction: **there are `w`-uniform families of size `(log w)^{w(1−o(1))} with no
`(1/2,1/2)`-robust sunflower at all**, so the `log w` in `κ₀` cannot be removed.

## The construction (ALWZ §3)

Split the ground set into `w` blocks of size `m ≈ (log w)/2` and take **transversals** — one
element from each block. A `1/2`-biased random set misses a given block with probability
`2^{-m} ≈ 1/√w`, so it misses *some* block with probability bounded away from `0`, and a set
that misses a block contains no transversal. That is Claim 3.2: the family is not satisfying.

But it is *not* enough: the family does contain robust sunflowers, at large kernels. Fix a
partial transversal `K` on all but one block; the link at `K` is that block's singletons, and
a random set hits a block of size `m` with probability `1 − 2^{-m}`, which is close to `1`.
The kernel of a robust sunflower can be large, and large kernels leave too few blocks free.

The repair (Claim 3.3) is to **prune the family to a code**: keep only transversals that
pairwise agree in at most `w − s` coordinates. A kernel is contained in two distinct members,
so it meets at most `w − s` blocks, leaving `s` blocks untouched — and `s ≈ √w` blocks are
enough for the miss probability, since `(1 − 2^{-m})^s ≤ exp(−s·2^{-m}) ≤ exp(−1) < 1/2`.
Pruning costs a factor: a greedy/maximal code has size at least `m^w / (2^w·m^s)`, which is
still `m^{w(1−o(1))}`.

## What is formalized here

* `exists_no_robustSunflower_core` — the construction at free parameters `(w, m, s)`, under
  `2^m ≤ s` (the only inequality the probability argument needs).
* `exists_no_robustSunflower` — the instantiation `m = ⌊log₂w⌋/2`, `s = ⌊√w⌋`, giving size
  `≥ ((log₂w)/16)^{w−√w} = (log w)^{w(1−o(1))}`.

The paper states the constant as `((log w)/8)^{w−√w}`; `16` is what the integer-valued
`m = ⌊log₂w⌋/2` gives without further care. Only the `(1−o(1))` in the exponent matters.
-/
import Sunflower.BlockProb
import Sunflower.Robust

open Finset

namespace Sunflower

namespace LowerBound

variable {w m : ℕ}

/-! ## The transversal family and its blocks -/

/-- The transversal picked by `f`: one element from each of the `w` blocks. -/
def tset (f : Fin w → Fin m) : Finset (Fin w × Fin m) :=
  Finset.univ.image fun i => (i, f i)

/-- The `i`-th block of the ground set. -/
def blk (m : ℕ) (i : Fin w) : Finset (Fin w × Fin m) :=
  ({i} : Finset (Fin w)) ×ˢ (Finset.univ : Finset (Fin m))

/-- The number of coordinates on which two transversals agree. -/
def agree (f g : Fin w → Fin m) : ℕ :=
  (Finset.univ.filter fun i => f i = g i).card

lemma mem_tset {f : Fin w → Fin m} {x : Fin w × Fin m} : x ∈ tset f ↔ f x.1 = x.2 := by
  simp only [tset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    rw [← hi]
  · intro h
    exact ⟨x.1, by rw [h]⟩

lemma card_tset (f : Fin w → Fin m) : (tset f).card = w := by
  rw [tset, Finset.card_image_of_injective _ (fun i j hij => by
    simpa using congrArg Prod.fst hij), Finset.card_univ, Fintype.card_fin]

lemma tset_injective : Function.Injective (tset (w := w) (m := m)) := by
  intro f g hfg
  funext i
  have : (i, f i) ∈ tset g := by rw [← hfg]; exact mem_tset.mpr rfl
  exact (mem_tset.mp this).symm

lemma mem_blk {i : Fin w} {x : Fin w × Fin m} : x ∈ blk m i ↔ x.1 = i := by
  rw [blk, Finset.mem_product, Finset.mem_singleton]
  simp

lemma card_blk (i : Fin w) : (blk m i).card = m := by
  simp [blk]

lemma blk_disjoint {i j : Fin w} (hij : i ≠ j) : Disjoint (blk m i) (blk m j) := by
  rw [Finset.disjoint_left]
  intro x hi hj
  exact hij (by rw [← mem_blk.mp hi, mem_blk.mp hj])

lemma agree_comm (f g : Fin w → Fin m) : agree f g = agree g f := by
  rw [agree, agree]
  exact congrArg Finset.card (Finset.filter_congr fun i _ => by exact eq_comm)

lemma agree_self (f : Fin w → Fin m) : agree f f = w := by
  rw [agree]
  simp

/-- Two transversals meet exactly in the coordinates where they agree. -/
lemma card_inter_tset (f g : Fin w → Fin m) : (tset f ∩ tset g).card = agree f g := by
  have himg : tset f ∩ tset g
      = (Finset.univ.filter fun i => f i = g i).image fun i => (i, f i) := by
    ext x
    simp only [Finset.mem_inter, mem_tset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x.1, by rw [h1, h2], by rw [h1]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨rfl, hi.symm⟩
  rw [himg, Finset.card_image_of_injective _ (fun i j hij => by simpa using congrArg Prod.fst hij),
    agree]

/-! ## The code: pruning to large pairwise distance -/

/-- `C` is a code of distance at least `s`: distinct members agree in `≤ w − s` coordinates. -/
def Good (s : ℕ) (C : Finset (Fin w → Fin m)) : Prop :=
  ∀ f ∈ C, ∀ g ∈ C, f ≠ g → agree f g + s ≤ w

/-- The transversals agreeing with `g` in more than `w − s` coordinates. -/
def ball (s : ℕ) (g : Fin w → Fin m) : Finset (Fin w → Fin m) :=
  Finset.univ.filter fun f => w < agree f g + s

lemma card_ball_le (hm : 1 ≤ m) (s : ℕ) (g : Fin w → Fin m) :
    (ball s g).card ≤ 2 ^ w * m ^ s := by
  classical
  set 𝒟 : Finset (Finset (Fin w)) :=
    (Finset.univ : Finset (Fin w)).powerset.filter fun D => D.card < s with h𝒟
  -- every element of the ball agrees with `g` off a set of fewer than `s` coordinates
  have hsub : ball s g ⊆ 𝒟.biUnion fun D =>
      Fintype.piFinset fun i => if i ∈ D then (Finset.univ : Finset (Fin m)) else {g i} := by
    intro f hf
    rw [ball, Finset.mem_filter] at hf
    set D : Finset (Fin w) := Finset.univ.filter fun i => f i ≠ g i with hD
    have hcompl : D.card + agree f g = w := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin w)))
        (p := fun i => f i ≠ g i)
      rw [hD, agree]
      simpa using this
    have hDcard : D.card < s := by omega
    refine Finset.mem_biUnion.mpr ⟨D, ?_, ?_⟩
    · rw [h𝒟, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hDcard⟩
    · refine Fintype.mem_piFinset.mpr fun i => ?_
      by_cases hi : i ∈ D
      · rw [if_pos hi]; exact Finset.mem_univ _
      · rw [if_neg hi, Finset.mem_singleton]
        rw [hD, Finset.mem_filter] at hi
        push Not at hi
        exact hi (Finset.mem_univ i)
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_biUnion_le) ?_)
  -- each piece has size `m^{|D|} ≤ m^s`, and there are at most `2^w` pieces
  have hpiece : ∀ D ∈ 𝒟,
      (Fintype.piFinset fun i => if i ∈ D then (Finset.univ : Finset (Fin m)) else {g i}).card
        ≤ m ^ s := by
    intro D hD
    have hcard : (Fintype.piFinset fun i =>
        if i ∈ D then (Finset.univ : Finset (Fin m)) else {g i}).card = m ^ D.card := by
      rw [Fintype.card_piFinset]
      have : ∀ i : Fin w,
          (if i ∈ D then (Finset.univ : Finset (Fin m)) else {g i}).card
            = if i ∈ D then m else 1 := by
        intro i; by_cases hi : i ∈ D <;> simp [hi]
      rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_ite]
      simp
    rw [hcard]
    refine Nat.pow_le_pow_right hm ?_
    rw [h𝒟, Finset.mem_filter] at hD
    omega
  refine le_trans (Finset.sum_le_sum hpiece) ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

/-- **Greedy/Gilbert–Varshamov**: a maximal code of distance `s` covers everything by balls,
hence has size at least `m^w / (2^w·m^s)`. -/
lemma exists_good_code (hm : 1 ≤ m) {s : ℕ} (hs : 1 ≤ s) :
    ∃ C : Finset (Fin w → Fin m), Good s C ∧ m ^ w ≤ C.card * (2 ^ w * m ^ s) := by
  classical
  set 𝒮 : Finset (Finset (Fin w → Fin m)) :=
    (Finset.univ : Finset (Fin w → Fin m)).powerset.filter fun C => Good s C with h𝒮
  have hne : 𝒮.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [h𝒮, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by
      intro f hf; exact absurd hf (Finset.notMem_empty f)⟩
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image 𝒮 Finset.card hne
  have hCgood : Good s C := by
    rw [h𝒮, Finset.mem_filter] at hC
    exact hC.2
  refine ⟨C, hCgood, ?_⟩
  -- maximality: every transversal lies in some ball
  have hcover : (Finset.univ : Finset (Fin w → Fin m)) ⊆ C.biUnion (ball s) := by
    intro f _
    by_contra hf
    have hnone : ∀ g ∈ C, agree f g + s ≤ w := by
      intro g hg
      by_contra hlt
      exact hf (Finset.mem_biUnion.mpr ⟨g, hg, by
        rw [ball, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega⟩⟩)
    have hfC : f ∉ C := by
      intro hmem
      have := hnone f hmem
      rw [agree_self] at this
      omega
    have hgood' : Good s (insert f C) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hnone b hb'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · rw [agree_comm]; exact hnone a ha'
        · exact hCgood a ha' b hb' hab
    have hmem' : insert f C ∈ 𝒮 := by
      rw [h𝒮, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hgood'⟩
    have := hmax _ hmem'
    rw [Finset.card_insert_of_notMem hfC] at this
    omega
  calc m ^ w = (Finset.univ : Finset (Fin w → Fin m)).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ ≤ (C.biUnion (ball s)).card := Finset.card_le_card hcover
    _ ≤ ∑ g ∈ C, (ball s g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ C, 2 ^ w * m ^ s := Finset.sum_le_sum fun g _ => card_ball_le hm s g
    _ = C.card * (2 ^ w * m ^ s) := by rw [Finset.sum_const, smul_eq_mul]

/-! ## No robust sunflower -/

/-- The probability estimate behind Claim 3.3: if `s` blocks are free of `K`, a `1/2`-biased
subset of the remaining ground set misses one of them with probability `> 1/2`. -/
lemma pBiased_hit_all_le {K : Finset (Fin w × Fin m)} {I : Finset (Fin w)} {s : ℕ}
    (hI : ∀ i ∈ I, Disjoint K (blk m i)) (hIs : s ≤ I.card) (h2m : 2 ^ m ≤ s) :
    pBiased (Finset.univ \ K) (1/2) (fun R => ∀ i ∈ I, ¬ Disjoint R (blk m i)) < 1/2 := by
  classical
  have hblkX : ∀ i ∈ I, blk m i ⊆ Finset.univ \ K := by
    intro i hi x hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    exact fun hxK => (Finset.disjoint_left.mp (hI i hi)) hxK hx
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (blk m i) (blk m j) :=
    fun i _ j _ hij => blk_disjoint hij
  rw [pBiased_forall_not_disjoint (1/2) (blk m) I hblkX hdisj]
  have hterm : ∀ i ∈ I, (1 : ℝ) - (1 - 1/2) ^ (blk m i).card = 1 - (1/2 : ℝ) ^ m := by
    intro i _
    rw [card_blk]
    norm_num
  rw [Finset.prod_congr rfl hterm, Finset.prod_const]
  -- `(1 − 2^{-m})^{|I|} ≤ exp(−|I|·2^{-m}) ≤ exp(−1) < 1/2`
  have hx0 : (0 : ℝ) < (1/2 : ℝ) ^ m := by positivity
  have hx1 : (1/2 : ℝ) ^ m ≤ 1 := by
    refine pow_le_one₀ (by norm_num) (by norm_num)
  have hstep : (1 : ℝ) - (1/2 : ℝ) ^ m ≤ Real.exp (-(1/2 : ℝ) ^ m) := by
    have := Real.add_one_le_exp (-(1/2 : ℝ) ^ m)
    linarith
  have hpow : ((1 : ℝ) - (1/2 : ℝ) ^ m) ^ I.card
      ≤ (Real.exp (-(1/2 : ℝ) ^ m)) ^ I.card :=
    pow_le_pow_left₀ (by linarith) hstep _
  have hexp : (Real.exp (-(1/2 : ℝ) ^ m)) ^ I.card
      = Real.exp ((I.card : ℝ) * (-(1/2 : ℝ) ^ m)) := by
    rw [Real.exp_nat_mul]
  -- `|I|·2^{-m} ≥ 1`
  have hge : (1 : ℝ) ≤ (I.card : ℝ) * (1/2 : ℝ) ^ m := by
    have h1 : ((2 : ℝ) ^ m) ≤ (I.card : ℝ) := by
      have : ((2 ^ m : ℕ) : ℝ) ≤ (I.card : ℝ) := by
        exact_mod_cast le_trans h2m hIs
      simpa using this
    have h2 : ((2 : ℝ) ^ m) * (1/2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    calc (1 : ℝ) = ((2 : ℝ) ^ m) * (1/2 : ℝ) ^ m := h2.symm
      _ ≤ (I.card : ℝ) * (1/2 : ℝ) ^ m := by
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt hx0)
  have hmono : Real.exp ((I.card : ℝ) * (-(1/2 : ℝ) ^ m)) ≤ Real.exp (-1) := by
    refine Real.exp_le_exp.mpr ?_
    have : (I.card : ℝ) * (-(1/2 : ℝ) ^ m) = -((I.card : ℝ) * (1/2 : ℝ) ^ m) := by ring
    rw [this]
    linarith
  have hhalf : Real.exp (-1 : ℝ) < 1/2 := by
    have h1 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
      linarith
    have h2 : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := by
      rw [Real.exp_neg]
    rw [h2, inv_lt_comm₀ (by positivity) (by norm_num)]
    linarith
  calc ((1 : ℝ) - (1/2 : ℝ) ^ m) ^ I.card ≤ (Real.exp (-(1/2 : ℝ) ^ m)) ^ I.card := hpow
    _ = Real.exp ((I.card : ℝ) * (-(1/2 : ℝ) ^ m)) := hexp
    _ ≤ Real.exp (-1) := hmono
    _ < 1/2 := hhalf

/-- **ALWZ Lemma 3.1, at free parameters.** A code of distance `s` among the transversals of
`w` blocks of size `m` contains no `(1/2,1/2)`-robust sunflower, as soon as `2^m ≤ s`. -/
theorem no_robustSunflower_of_good {s : ℕ} (_hs : 1 ≤ s) (h2m : 2 ^ m ≤ s)
    {C : Finset (Fin w → Fin m)} (hC : Good s C) :
    ∀ 𝒢 ⊆ C.image tset, ¬ IsRobustSunflower (1/2) (1/2) (Finset.univ : Finset (Fin w × Fin m)) 𝒢 := by
  classical
  intro 𝒢 h𝒢 hrs
  obtain ⟨hker, hsat⟩ := hrs
  -- `𝒢` has two distinct members
  obtain ⟨S, hS, S', hS', hSS'⟩ : ∃ S ∈ 𝒢, ∃ S' ∈ 𝒢, S ≠ S' := by
    by_contra hcon
    push Not at hcon
    rcases Finset.eq_empty_or_nonempty 𝒢 with rfl | ⟨T, hT⟩
    · -- the empty family is not satisfying
      have hlink : link (∅ : Finset (Finset (Fin w × Fin m)))
          (kernel (∅ : Finset (Finset (Fin w × Fin m)))) = ∅ := by
        simp [link]
      rw [IsSatisfying, hlink] at hsat
      have hzero : pBiased
          (Finset.univ \ kernel (∅ : Finset (Finset (Fin w × Fin m)))) (1/2)
          (fun R => ∃ S ∈ (∅ : Finset (Finset (Fin w × Fin m))), S ⊆ R) = 0 := by
        rw [pBiased]
        simp
      rw [hzero] at hsat
      norm_num at hsat
    · -- a one-element family has its member as kernel
      have h𝒢eq : 𝒢 = {T} := by
        refine Finset.Subset.antisymm (fun U hU => ?_) (Finset.singleton_subset_iff.mpr hT)
        rw [Finset.mem_singleton]
        exact hcon U hU T hT
      have hkerT : kernel 𝒢 = T := by
        rw [h𝒢eq, kernel, dif_pos (Finset.singleton_nonempty T)]
        exact Finset.inf'_singleton id
      rw [hkerT] at hker
      exact hker hT
  -- they come from distinct codewords
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (h𝒢 hS)
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (h𝒢 hS')
  have hfg : f ≠ g := fun h => hSS' (by rw [h])
  set K : Finset (Fin w × Fin m) := kernel 𝒢 with hK
  -- the kernel meets at most `w − s` blocks
  set I : Finset (Fin w) := Finset.univ.filter fun i => Disjoint K (blk m i) with hI
  have hIcard : s ≤ I.card := by
    have hcompl : ∀ i ∈ Finset.univ.filter (fun i => ¬ Disjoint K (blk m i)), f i = g i := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨x, hxK, hxb⟩ := Finset.not_disjoint_iff.mp hi.2
      have hxS : x ∈ tset f := kernel_subset hS hxK
      have hxS' : x ∈ tset g := kernel_subset hS' hxK
      have h1 : f x.1 = x.2 := mem_tset.mp hxS
      have h2 : g x.1 = x.2 := mem_tset.mp hxS'
      have hx1 : x.1 = i := mem_blk.mp hxb
      rw [← hx1, h1, h2]
    have hsubset : Finset.univ.filter (fun i => ¬ Disjoint K (blk m i))
        ⊆ Finset.univ.filter fun i => f i = g i := by
      intro i hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcompl i hi⟩
    have hle : (Finset.univ.filter fun i => ¬ Disjoint K (blk m i)).card ≤ agree f g :=
      le_trans (Finset.card_le_card hsubset) (le_of_eq rfl)
    have hsum : I.card + (Finset.univ.filter fun i => ¬ Disjoint K (blk m i)).card = w := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin w)))
        (p := fun i => Disjoint K (blk m i))
      rw [hI]
      simpa using this
    have := hC f hf g hg hfg
    omega
  -- so the link cannot be satisfying
  have hIdisj : ∀ i ∈ I, Disjoint K (blk m i) := by
    intro i hi
    rw [hI, Finset.mem_filter] at hi
    exact hi.2
  have himp : ∀ R : Finset (Fin w × Fin m),
      (∃ S ∈ link 𝒢 K, S ⊆ R) → ∀ i ∈ I, ¬ Disjoint R (blk m i) := by
    rintro R ⟨T, hT, hTR⟩ i hi
    rw [mem_link] at hT
    obtain ⟨U, hU, hKU, rfl⟩ := hT
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp (h𝒢 hU)
    have hx : (i, h i) ∈ tset h \ K := by
      refine Finset.mem_sdiff.mpr ⟨mem_tset.mpr rfl, ?_⟩
      intro hmem
      exact (Finset.disjoint_left.mp (hIdisj i hi)) hmem (mem_blk.mpr rfl)
    exact Finset.not_disjoint_iff.mpr ⟨(i, h i), hTR hx, mem_blk.mpr rfl⟩
  have hle : pBiased (Finset.univ \ K) (1/2) (fun R => ∃ S ∈ link 𝒢 K, S ⊆ R)
      ≤ pBiased (Finset.univ \ K) (1/2) (fun R => ∀ i ∈ I, ¬ Disjoint R (blk m i)) :=
    pBiased_mono (by norm_num) (by norm_num) _ himp
  have hlt := pBiased_hit_all_le hIdisj hIcard h2m
  rw [IsSatisfying] at hsat
  linarith

/-- **ALWZ Lemma 3.1, at free parameters.** -/
theorem exists_no_robustSunflower_core (hm : 1 ≤ m) {s : ℕ} (hs : 1 ≤ s) (h2m : 2 ^ m ≤ s) :
    ∃ 𝓕 : Finset (Finset (Fin w × Fin m)),
      IsUniform w 𝓕
      ∧ m ^ w ≤ 𝓕.card * (2 ^ w * m ^ s)
      ∧ ∀ 𝒢 ⊆ 𝓕, ¬ IsRobustSunflower (1/2) (1/2) (Finset.univ : Finset (Fin w × Fin m)) 𝒢 := by
  obtain ⟨C, hC, hcard⟩ := exists_good_code hm hs
  refine ⟨C.image tset, ?_, ?_, no_robustSunflower_of_good hs h2m hC⟩
  · intro S hS
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hS
    exact card_tset f
  · rwa [Finset.card_image_of_injective _ tset_injective]

/-- **ALWZ Lemma 3.1.** For every `w ≥ 4` there is a `w`-uniform set system of size at least
`((log₂w)/16)^{w−√w} = (log w)^{w(1−o(1))}` containing no `(1/2,1/2)`-robust sunflower.

Together with `Sunflower.exists_isRobustSunflower_pad` — every `w`-uniform family of size
`κ₀^w` with `κ₀ = O(log w · log log w)` *does* contain one — this pins the truth down to the
`log log w`: the `log w` is necessary. -/
theorem exists_no_robustSunflower (w : ℕ) (hw : 4 ≤ w) :
    ∃ 𝓕 : Finset (Finset (Fin w × Fin (Nat.log 2 w / 2))),
      IsUniform w 𝓕
      ∧ ((Nat.log 2 w : ℝ) / 16) ^ (w - Nat.sqrt w) ≤ (𝓕.card : ℝ)
      ∧ ∀ 𝒢 ⊆ 𝓕, ¬ IsRobustSunflower (1/2) (1/2)
          (Finset.univ : Finset (Fin w × Fin (Nat.log 2 w / 2))) 𝒢 := by
  set L : ℕ := Nat.log 2 w with hL
  set m : ℕ := L / 2 with hm
  set s : ℕ := Nat.sqrt w with hs
  have hw0 : w ≠ 0 := by omega
  -- `2 ≤ L`, hence `1 ≤ m`
  have hL2 : 2 ≤ L := by
    rw [hL]
    exact (Nat.le_log_iff_pow_le Nat.one_lt_two hw0).mpr (by norm_num; omega)
  have hm1 : 1 ≤ m := by omega
  -- `2 ≤ s`, and `2^m ≤ s`
  have hs2 : 2 ≤ s := by
    rw [hs]
    exact Nat.le_sqrt'.mpr (by norm_num; omega)
  have h2m : 2 ^ m ≤ s := by
    rw [hs]
    refine Nat.le_sqrt'.mpr ?_
    calc (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ w := Nat.pow_log_le_self 2 hw0
  have hsw : 2 * s ≤ w := by
    have h1 : s * s ≤ w := by rw [hs]; exact Nat.sqrt_le w
    nlinarith
  obtain ⟨𝓕, huni, hcard, hno⟩ := exists_no_robustSunflower_core (w := w) (m := m) hm1
    (by omega : 1 ≤ s) h2m
  refine ⟨𝓕, huni, ?_, hno⟩
  -- `m^{w−s} ≤ |𝓕|·2^w` in `ℕ`
  have hpow : m ^ (w - s) ≤ 𝓕.card * 2 ^ w := by
    have hsplit : m ^ w = m ^ (w - s) * m ^ s := by
      rw [← pow_add]
      congr 1
      omega
    have hms : 0 < m ^ s := Nat.pow_pos (by omega)
    have := hcard
    rw [hsplit] at this
    have h2 : m ^ (w - s) * m ^ s ≤ (𝓕.card * 2 ^ w) * m ^ s := by
      calc m ^ (w - s) * m ^ s ≤ 𝓕.card * (2 ^ w * m ^ s) := this
        _ = (𝓕.card * 2 ^ w) * m ^ s := by ring
    exact Nat.le_of_mul_le_mul_right h2 hms
  -- and then in `ℝ`
  have hpowR : (m : ℝ) ^ (w - s) ≤ (𝓕.card : ℝ) * 2 ^ w := by exact_mod_cast hpow
  have hL4m : L ≤ 4 * m := by omega
  have hbase : ((L : ℝ) / 16) ≤ (m : ℝ) / 4 := by
    have : (L : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast hL4m
    linarith
  have h4 : (2 : ℝ) ^ w ≤ 4 ^ (w - s) := by
    have hexp : (4 : ℝ) ^ (w - s) = 2 ^ (2 * (w - s)) := by
      rw [pow_mul]; norm_num
    rw [hexp]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) < 4 ^ (w - s) := by positivity
  calc ((L : ℝ) / 16) ^ (w - s) ≤ ((m : ℝ) / 4) ^ (w - s) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ = (m : ℝ) ^ (w - s) / 4 ^ (w - s) := by rw [div_pow]
    _ ≤ ((𝓕.card : ℝ) * 2 ^ w) / 4 ^ (w - s) := by
        exact div_le_div_of_nonneg_right hpowR hpos.le
    _ ≤ (𝓕.card : ℝ) := by
        rw [div_le_iff₀ hpos]
        have hcnn : (0 : ℝ) ≤ (𝓕.card : ℝ) := Nat.cast_nonneg _
        calc (𝓕.card : ℝ) * 2 ^ w ≤ (𝓕.card : ℝ) * 4 ^ (w - s) :=
              mul_le_mul_of_nonneg_left h4 hcnn
          _ = (𝓕.card : ℝ) * 4 ^ (w - s) := rfl

end LowerBound

end Sunflower

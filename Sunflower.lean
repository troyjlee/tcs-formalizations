/-
# Sunflowers

A Lean 4 formalization of sunflower theorems, targeting the improved bound of
Alweiss–Lovett–Wu–Zhang (STOC 2020 Best Paper; *Annals of Mathematics* 194 (2021) 795–815).

Mathlib contains no notion of a sunflower; this development supplies the definitions and
builds toward:

* `Sunflower.ErdosRado` — the classical `(r-1)^w * w!` bound (1960). **Fully proved.**
* `Sunflower.Spread`    — the robust-sunflower / spread framework of ALWZ: links,
  `R`-spread families, the reduction "a large uniform family has a large spread link"
  (`exists_spread_link`), and the lifting of disjoint petals to a sunflower.
  **Fully proved.**
* `Sunflower.ALWZ`      — the improved `(C r³ log w log log w)^w` bound.
  **Fully proved** (`alwz`, and `spread_lemma` with explicit `C = 2^41`);
  axioms: `[propext, Classical.choice, Quot.sound]`.
* `Sunflower.RaoBCW`    — the sharper `(C r log w)^w` bound on Rao's coding route, with the
  Bell–Chueluecha–Warnke `2r`-colour improvement: `rao_bcw` and `rao_bcw_bounded` at the
  explicit `C = 2^60`, from Theorem 1.9 at `O(log w)`
  (`RaoSchedule.exists_isRobustSunflower_rao`). **Fully proved**;
  axioms: `[propext, Classical.choice, Quot.sound]`. Independent of the ALWZ iteration:
  Rao's coding estimate replaces the Janson/second-moment core.
* `Sunflower.Robust`    — ALWZ §1.1: satisfying set systems (Def 1.5), robust sunflowers
  (Def 1.7), the disjointness step (Lemma 1.6) and `(1/r,1/r)`-robust ⟹ `r`-sunflower
  (Lemma 1.8). The `p`-biased distribution appears here as a finite sum, no measure theory.
  Theorem 1.9 itself lives downstream — `KappaZeroPad` on the ALWZ route, `RaoSchedule` on
  the Rao route; the file documents precisely what it needs.
* `Sunflower.Janson`    — towards Janson's inequality (needed for Theorem 1.9 *as
  published*): **Harris/FKG for the `p`-biased measure**, proved from mathlib's
  Ahlswede–Daykin four functions theorem via log-modularity of the weight. Steps 2–4
  independence on disjoint coordinates, basic Janson (`janson`) and extended Janson
  (`janson_ext`). All four steps proved.
* `Sunflower.Bridge`    — the `p`-biased ↔ fixed-size transfer that adopting Janson forces
  back (Janson does not hold on the slice): layering, antitonicity of the fixed-size
  probability for a decreasing event, and Markov on `|R|` — no concentration inequality.
* `Sunflower.BridgeBack`, `Satisfying` — the same transfer in the direction Theorem 1.9 needs
  (fixed-size ⟹ `p`-biased), which costs a *lower* tail for `|R|`: the exact variance
  (`variance_card`) with Chebyshev, and the MGF `(pz + 1 − p)^{|X|}` (`mgf_card`) with Chernoff.
  `isSatisfying_of_failCount_exp` turns the iteration's failure bound into Definition 1.5;
  `isSatisfying_of_isSpread_iterated` is ALWZ's Theorem 2.5 at free `(a, b)` in schedule form,
  and `exists_isRobustSunflower_of_satisfying` is their Lemma 2.4 — Theorem 2.5 ⟹ Theorem 1.9.
  `Sunflower.Schedule` then picks the schedule, and `Sunflower.KappaZero` verifies its three
  conditions at the closed-form constant
  `κ₀ = (2^20/a)·(lg(16/b) + lg w + lg(1/a) + 20)³`, giving **`exists_isRobustSunflower`** —
  ALWZ Theorem 1.9, with no hypothesis on `κ`.
* `Sunflower.JansonCover` — Janson specialised to the covering event of a weighted system:
  `μ` and `Δ` become explicit sums of powers of `p` over the support, and combining with
  `Bridge` gives `failCount X σ m₀ ≤ 2·exp(−μ+Δ)·C(|X|,m₀)` — the Janson-shaped replacement
  for the second moment in `SpreadBottom.bottom_le`.
* `Sunflower.Padding`   — uniformization by private dummy elements, which restores the
  papers' *`w`-set system* hypothesis (`|S| ≤ w`) from the uniform one (`|S| = w`).
  Exports `alwz_bounded` and `erdos_rado_bounded`, with the same constants: padding
  preserves the number of members exactly.
* `Sunflower.SpreadCore`, `SpreadBottom`, `SpreadIterate`, `SpreadAssemble` —
  the probabilistic core: ALWZ §2 recast as finitary counting (encoding
  argument, reduction rounds, heaviest-class second moment replacing Janson,
  width-schedule iteration, and the arithmetic instantiation). All sorry-free.
* `Sunflower.JansonBottom`, `JansonIterate` — the Janson route to the bottom step, replacing
  the second moment: the two spread estimates (`mu_ge`, `delta_le`), the κ-budget in
  `log(1/β)` rather than `1/β` form, the heaviest-class reduction that makes it consumable
  from `WBounded`, and `iterate_le_janson` — the width-schedule iteration running on the
  Janson bottom.
* `Sunflower.JansonChase` — the constant chase for that route, and what it found:
  `janson_mass_budget_infeasible` shows the mass-routed budget is *unsatisfiable* at the
  instantiation (by a factor `|𝓖|/κ²`), because that support-indexed formulation sees only the
  support while the iteration's invariant is mass-based. `failCount_le_of_janson_isSpread` is the support-spread
  bottom, run on support-spreadness (`IsSpread κ (supp X σ)`), whose exponent `κp/(8v²)`
  carries no mass/support ratio; `iterate_le_janson_supp` runs the iteration on it, and
  `janson_supp_conditions` completes the chase for its three conditions at the
  `spread_core_main` parameters (`p = 1/(8r)`, `εbot = 1/(4r)`), with
  `janson_bottom_at_params` plugging them back in.

  Support-spreadness of the iteration's own systems is then shown **false**
  (`suppSpread_not_of_wLinkBounded`: a star of weight-`1` pairs with heavy ballast), and
  replaced by `isSpread_weightClass` — the heaviest *dyadic weight class* of the support is
  spread as a family. That makes the Janson bottom follow from `WLinkBounded` alone
  (`failCount_le_of_janson_massSpread`) and the iteration unconditional
  (`iterate_le_janson_mass`), at a cost of `log₂` of the largest multiplicity in the budget:
  `janson_mass_conditions` does that chase, and `width_le_of_multiplicity_budget` prices it as
  a ceiling on the width.
* `Sunflower.JansonMass` — **ALWZ's own Lemma 2.10**, and what fixes all of the above:
  index Janson by *copies* of the members (`janson_mult_q`), as the paper does, instead of by
  distinct members. Then `μ` and `Δ` are masses, `WLinkBounded` is exactly the hypothesis the
  `Δ` estimate needs, and the bottom bound is `exp(−A·κ·p/(8·M·v))` — no support size, no
  multiplicity factor, no side hypothesis (`failCount_le_janson_mass_budget`). With the
  heaviest-size-class reduction this is `failCount_le_of_janson_uniformMass`, the iteration is
  `iterate_le_janson_alwz`, and the chase `janson_alwz_conditions` closes at
  `p = 1/(8r)`, `εbot = 1/(4r)`.
* `Sunflower.DummyPad` — **ALWZ's dummy padding**, expanded in formalization note A3: a
  `≤v`-bounded `κ`-spread system becomes `v`-*uniform* on an enlarged ground set, still spread,
  with every member containing an original one (`exists_padding`). One-copy padding can break
  spreadness — the link at a member's own dummies would carry its whole weight — so each member
  gets `q ≥ κ^v` disjoint copies, which is the paper's "scale by a large enough factor so that a
  negligible amount of weight falls on each dummy element". `janson_exponent_padding` records
  why that costs nothing: the bottom step sees the mass only through `A/M`, and both scale by
  `q`.
* `Sunflower.PadBottom` — the padding cashed in. The `p`-biased measure is carried along
  `Sum.inl` (`pBiased_map_inl`) and the dummies are invisible (`pBiased_uncovered_ground_eq'`),
  so the uniform bound applies to the padded system and comes back:
  `failCount_le_of_janson_padded` is the bottom step for `≤v`-bounded systems with exponent
  `A·κ·p/(8Mv)` — **no `v²`** — and `iterate_le_janson_pad` runs the iteration on it, needing
  `log(2/εbot) ≤ A₀κp/(32ML)` where the size-class route needs `A₀κp/(64ML²)`.
* `Sunflower.SchedulePad`, `KappaZeroPad` — the schedule chase re-run on that bottom. The
  middle condition is now *linear* in the number `L` of rounds (`1024·L·log(8/b) ≤ κa` in
  `isSatisfying_of_isSpread_of_kappa_pad`, against `2048·L²·log(8/b)` in `Schedule`), and the
  binding condition becomes the third one, `4096·L·(log₂w+1) ≤ κa`. That changes the closed
  form: **`exists_isRobustSunflower_pad`** is Theorem 1.9 at
  `κ₀ = (2^20/a)·(lg(1/a) + lg(16/b) + lg lg w + 40)·(lg w + lg(16/b))`, which for fixed
  `a, b` is `O(lg w · lg lg w)` — ALWZ's own shape — where `KappaZero.exists_isRobustSunflower`
  pays `O(lg w · (lg lg w)²)`. The two brackets split the data cleanly: the first is doubly
  logarithmic (and bounds `L ≤ 5U`), the second singly.
* `Sunflower.Kraft` — **Rao's Lemma 5**, the converse of Shannon's noiseless coding theorem
  under the uniform distribution: a prefix-free encoding of `t` objects has average length at
  least `log₂ t`. Mathlib has Kraft–McMillan for *uniquely decodable* codes but no prefix-free
  notion, so `uniquelyDecodable_of_prefixFree` bridges to it and `kraft_le_one` is Kraft; the
  Shannon converse is then Jensen for `log`. This is the one tool in Rao's "Coding for
  sunflowers", the route to replacing the width-schedule iteration and reaching
  `(C r log w)^w`. `logb_card_le_avg_of_kraft` states it in Kraft-weight form, so a "virtual"
  encoding — each field contributing the reciprocal of its number of choices — works too.
* `Sunflower.PrefixCode` — self-delimiting codes that **carry their decoder**
  (`dec (enc i ++ rest) = some (i, rest)`), which is what makes an encoding argument checkable:
  prefix-freeness and injectivity follow from that one law, and the combinators compose —
  `tagCode`, `unaryCode` (`0^n1`), `memCode`/`powersetCode` (fixed width into a set of known
  size), `Code.sigma` (a field whose width depends on what is already decoded, which is the
  informal "since `U` has been fixed there are `N` choices"), and `logb_card_le_of_code`.
* `Sunflower.RaoSpread` — Rao's spread condition in its **absolute** form
  `|𝓕_Z| ≤ R^{w−|Z|}`, which is not ALWZ's normalized `IsSpread` and must not be conflated
  with it: `isSpread_of_isRaoSpread` converts one to the other for families of size `≥ R^w`,
  so the existing robust-sunflower assembly is reusable, and `card_ground_ge` is Rao's
  `w·R ≤ |X|` (his "`n/k > 6`"), the source of the geometric slack in his second encoding case.
* `Sunflower.RaoChi` — Rao's residual `χ(𝓕,S,W) = T \ W` for the member `T ⊆ S ∪ W`
  minimizing `|T \ W|`: the quantity his Lemma 4 contracts by `2/3` per round. Monotone in
  `W`, vanishing exactly on the covering event, and tied to the existing `fixedCount` by
  `fixedCount_mul_card_le_chiSum` — a small summed residual means few uncovered sets. The
  tie-break is `Finset.exists_min_image` + choice rather than an order on `α`: a function of
  `(𝓕,S,W)`, which is all a decoder needs.
* `Sunflower.RaoEncoding` — the parts of Rao's one-step contraction that carry no encoding:
  the binomial estimate `∑_{i≤a} C(m,v+i) ≤ C(m,v)·(m/v)^a` (his step (b)), his step (d)
  (`chi_card_le_inter`: the already-written `χ(j,U) ∩ χ(S,U)` is at least as large as
  `|χ(S,W)|`, which is why the encoding gains anything), the canonical auxiliary minimizer
  `jWitness` as a function of decoded fields, and the class `τ` likewise. Working out what the
  decoder knows at each field exposes an **implicit dependency in the paper's case 1**: on the
  sequential reading used here, the width of the field encoding `S` depends on `|χ(S,W)|`,
  which is not yet transmitted. Transmitting `A` itself makes the dependency explicit within
  the target budget.
* `Sunflower.RaoCase1` — that encoder, built: `case1Code` is the five-field record (`a` in
  unary, `D = V ∪ χ(S,U)`, `A ⊆ χ(j,U)`, `S` inside `τ(A,D,a)`, `V ∩ χ(S,U)`), each field's
  width depending only on those before it; `case1Decode` is the decoder and
  `case1Decode_encode` proves it inverts the encoder, which is what makes `case1PairCode` a
  code on the pairs `(V,S)` at all. `card_Dcands` counts field (3)'s candidates exactly, and
  `jWitness_union_U`/`tau_union_U` are why `j` and `τ` can be recomputed from what was sent.
* `Sunflower.RaoCase2` — the double count behind case 2, done as cardinalities rather than
  Rao's random experiment: `sum_card_tau_eq` swaps the order of summation, `filter_tau_eq`
  identifies the `V`s that put a member in the class as exactly those swallowing
  `χ(T,U) \ χ(S,U)` (so `card_filter_superset` counts them), and `card_traceFiber_le` is the
  single use of spreadness — grouping members by `B = χ(T,U) ∩ χ(S,U)`, each group sits in the
  link at `B`. `card_exceptional_le` is the estimate itself:
  `#{V : |τ(A,V,a)| > φ} ≤ C(n−u,v)·(8/ρ)^a`. The `8` is `2·(3 + 1)`: `3` from
  `n−u−a ≥ (n−u)/3` and `1` from `1/R ≤ v/(n−u)` — the two terms of the geometric ratio
  `x + 1/R`, summed exactly by `sum_traces_pow` where Rao bounds the trace count by `2^a`
  (his constant is `6`) — and the `2` from the trimming slack `|𝓕| ≤ R^w + 1`, absorbed into
  the base via `a ≥ 1`. The directly transcribed case-2 field list admits an explicit decoder;
  no analogous dependency appears there (formalization note R1).
* `Sunflower.RaoJoin` — the two branches joined by a tag bit (`Code.byCases`) into `raoCode`,
  a single code on the pairs `(V,S)`, and `contraction_of_lengths`: per-branch length bounds of
  the shape `log₂(R^w·C(n−u,v)) + A·|χ(S,U)| − B·|χ(S,U∪V)|` give
  `B·∑|χ(S,U∪V)| ≤ A·∑|χ(S,U)|`, which at `A/B ≤ 2/3` is Rao's contraction.
  `chi_pos_or_all_covered` handles the `a = 0` boundary the target length cannot charge.
* `Sunflower.RaoWidths` — field widths (`⌈log₂N⌉` bits index a set of size `N`, costing
  `log₂N + 1` — Rao's "+1"s) and his closing constant chase, made explicit:
  `branch1_fits`/`branch2_fits` bring both branches into the common shape
  `log₂N + A·a − B·b` with `A = log₂ρ + 7`, `B = log₂κ`, and `ratio_ok` gives `3A ≤ 2B` at
  `log₂ρ = 21`, `log₂κ = 42` — `A/B = 28/42 = 2/3` exactly. The chain actually runs on the
  *trimmed* constants (`branch2_fits_trimmed`, `ratio_ok_trimmed`): the slack of a family
  known only up to `|𝓕| ≤ R^w + 1` costs case 2 one bit and one `a`, and the chase re-closes
  at `log₂ρ = 23`, `log₂κ = 2log₂ρ − 1 = 45`, again with both constraints tight.
  `contraction_of_branch_bounds` assembles them into the contraction.
* `Sunflower.RaoLengths` — the widths instantiated. Each field is `width n = ⌈log₂n⌉` bits for
  its own cardinality, so the codes are defined unconditionally and the estimates enter only in
  the length calculation — which matters for case 1, whose `τ`-field is bounded by `φ` *only on
  case-1 pairs*. `tau_card_le_phi_of_not_case2` is what the case-1 branch knows,
  `logb_phi` expands `log₂φ` (its `a·log₂vn` is exactly what cancels field (3)'s cost), and
  `case2Code'_length_le` and `case1_length_le` are the two instantiated bounds, and
  **`contraction`** is Rao's Lemma 4: one round of sampling contracts the summed residual,
  `3·∑|χ(S,U∪V)| ≤ 2·∑|χ(S,U)|`. Phase B of the plan is closed.
* `Sunflower.RaoCover` — iterating it. `sum_pair_union` is the exact decomposition
  `∑_{|U|=u}∑_{|V|=v} f(U ∪ V) = C(u+v,u)·∑_{|W|=u+v} f(W)`, every `(u+v)`-set arising from
  exactly `C(u+v,u)` splits — the identity form of the double count that
  `SpreadCore.failCount_compose` uses in a specialized, inequality form. `chiSum_step` sums the
  fixed-`U` contraction over all `U` into a recursion between consecutive slices — the `U` that
  already cover a member contribute `0` to both sides — and `chiAvg_iter_le` iterates it to
  Rao's `E|χ(X,W_j)| ≤ k·(2/3)^j`. `chiAvg_schedule` then picks the schedule: `j > 3·log(w/ε)`
  rounds of size `v` drive the average residual below `ε` per member, the round count coming
  from `log(3/2) ≥ 1/3`. **`rao_fixed_cover`** closes Phase C: for an absolutely `R`-spread
  `w`-uniform family, a uniform `m`-subset of the ground set contains a member except with
  probability `< ε` — Rao's Lemma 4 in the fixed-size model, and the input to the `p`-biased
  transfer.
* `Sunflower.RaoSatisfying` — that transfer, i.e. **BCW's Theorem 3**: `rao_isSatisfying` gives
  `IsSatisfying δ ε X 𝓕` for an absolutely `R`-spread `w`-uniform family. Nothing new is needed —
  this is the interface of formalization note F7, and the bridge (`pBiased_le_fixedCount_add_tail`
  plus the Chernoff lower tail `pBiased_card_lt_le_exp`) was already built for the ALWZ route;
  only the plain-family versions of two weighted lemmas had to be added.
* `Sunflower.RaoRobust` — the structured/pseudorandom dichotomy in *absolute* form.
  `exists_rao_spread_link` takes a core `Z` of **maximum size** among those whose link is still
  large (`R^{w−|Z|} ≤ |𝓕_Z|`); maximality is then exactly `IsRaoSpread` of that link, since
  every proper extension has already fallen below the threshold. `link_link` (`(𝓕_Z)_Y =
  𝓕_{Z∪Y}`) is what makes the two levels line up. `exists_isRobustSunflower_of_link` then
  assembles Theorem 1.9 from it, modulo one hypothesis — that the extracted link is satisfying —
  which is `rao_isSatisfying` at `δ = a`, `ε = b` once the schedule is chosen.
  `isSatisfying_of_trimmed` supplies the missing reduction: `rao_isSatisfying` needs the family
  to sit *at* the threshold (`|𝓕| ≤ R^w` as well as `≥`), which is Rao's `ℓ = ⌈r^k⌉`. He gets
  there by "removing sets can only increase the expectation"; that is not a pointwise statement
  once the law of `S` changes, so instead one trims to `⌈R^w⌉` and returns by monotonicity of
  the covering *event* (`IsSatisfying.mono`), which is genuinely monotone.
* `Sunflower.RaoSchedule` — the schedule in closed form: `v = ⌈2⁴⁵n/R⌉`, `j = ⌈3log(4w/ε)⌉+1`,
  and the single condition `2⁵⁵·δ⁻¹·(log(w/ε)+1) ≤ R` discharging all eight side conditions
  of `rao_isSatisfying` (`rao_isSatisfying_of_kappa`), on the back of Rao's ground-set bound
  `wR ≤ n`. The endpoint is **`exists_isRobustSunflower_rao`** — Theorem 1.9 at
  `κ₀ = raoKappa 2⁶⁰ a b w = (2⁶⁰/a)·lg(w/b)`, which for fixed `a,b` is `O(lg w)` against
  `exists_isRobustSunflower_pad`'s `O(lg w · lg lg w)`, matching the shape forced by
  `LowerBound` up to the known subexponential loss. Rao's technical range `δ, ε ≤ 1/2` turns
  out never to be used by the formalized chase, so the theorem exports directly at ALWZ's
  full range `0 < a, b ≤ 1`, `w ≥ 2`.
* `Sunflower.SunflowerNote` — the note's `2r`-colour improvement.
  `exists_pairwiseDisjoint_of_many_colours` generalizes Lemma 1.6 from "all `r` classes
  succeed" to "at least `r` of `q`": the same double count of (colouring, colour) pairs, with
  linearity of expectation in place of the union bound, extracting `r` disjoint members from
  `r ≤ q(1−b)`. `exists_pairwiseDisjoint_of_raoSpread` is the specialization `q = 2r`,
  `δ = 1/(2r)`, `b = 1/2` (the rate condition holding with equality): an absolutely
  `R`-spread `w`-uniform family with `|𝓕| ≥ R^w` and `R ≥ 2⁵⁶·r·(log(2w)+1)` contains `r`
  pairwise disjoint members. The budget `1/2` in place of `1/r` is what removes the `log r`.
  The note's statements are also exported source-shaped: `bcw_theorem3` (existential `B`,
  `k ≥ 2`, `0 < δ, ε ≤ 1/2`, natural log, only `|𝓕| ≥ R^w`), `bcw_disjoint` (the
  generalized corollary — `⌊δ⁻¹⌋(1−ε)` disjoint sets, the colouring run at `1/⌊δ⁻¹⌋ ≥ δ` so
  no monotonicity in the density is needed), and `rao_disjoint_original` — Rao's own
  `O(r log(rw))` spread-to-disjoint estimate at `δ = ε = 1/r` via the union bound
  (Lemma 1.6), preserved as a proof route independent of the `2r`-colour improvement.
* `Sunflower.BCWLower` — **the note's Lemma 4**: for `r ≤ ¼δ⁻¹ log(k/ε)` the full
  transversal family of `k` blocks of size `r` (the `tset`/`blk` machinery of `LowerBound`,
  unpruned) is exactly `r`-spread with `r^k` members, yet a `δ`-biased set covers it with
  probability `< 1 − ε` — so Theorem 3's spread requirement is essentially optimal,
  `ε`-dependence included (`bcw_lemma4`). The probability side is
  `BlockProb.pBiased_forall_not_disjoint`; the arithmetic
  `(1−(1−δ)^r)^k ≤ e^{−e^{−2δr}k} ≤ e^{−√ε} < 1−ε` needs the cubic Taylor lower bound on
  `exp` — the last step has margin `≈ 0.007` at `ε = 1/2`. This completes the note: all four
  of its statements (Theorem 1 = `rao_bcw`, Lemma 2 = `exists_pairwiseDisjoint_of_raoSpread`,
  Theorem 3, Lemma 4) are formalized.
* `Sunflower.RaoBCW` — Rao's induction, and the endpoint of the route: **`rao_bcw`** — every
  `w`-uniform family of size at least `(C·r·lg w)^w` contains an `r`-sunflower (`r, w ≥ 2`,
  explicitly `C = 2⁶⁰`) — and **`rao_bcw_bounded`**, the same threshold for `w`-set systems
  via the private-dummy padding, i.e. ALWZ Theorem 1.4 with the `r³` and the `lg lg w` both
  removed. A spread family gives an empty-core sunflower through the `2r`-colour lemma; a
  violating core hands the induction a strictly narrower link, large in *absolute* terms with
  the same `R` (`hasSunflower_of_hasSunflower_link` reattaches the core). `rao_bcw_original`
  re-exports Rao's own `(C·r·log(rw))^w` as a regression check.
* `Sunflower.BlockProb`, `LowerBound` — **ALWZ Lemma 3.1**, the other side of Theorem 1.9:
  `exists_no_robustSunflower` builds, for every `w ≥ 4`, a `w`-uniform family of size
  `((log₂w)/16)^{w−√w} = (log w)^{w(1−o(1))}` with **no** `(1/2,1/2)`-robust sunflower — so the
  `log w` in `κ₀` is necessary and only the `log log w` is in question. The construction is the
  paper's: transversals of `w` blocks of size `≈(log w)/2`, pruned to a code of distance `√w` so
  that every kernel leaves `√w` blocks untouched, and a `1/2`-biased set misses one of them with
  probability `≥ 1 − e^{-1} > 1/2`. `BlockProb` supplies the block events —
  `Pr[R ∩ B = ∅] = (1−p)^{|B|}` and its product over disjoint blocks, by independence.
* `Sunflower.JansonAssemble` — `spread_core_janson`: the spread lemma itself on the Janson
  route, **statement-for-statement identical to `spread_core_main`** and with no extra
  hypothesis. The library therefore carries two proof chains for the spread lemma, one with a
  second-moment bottom and one with a Janson bottom; the latter is source-shaped and its bottom
  allowance costs `log(1/β)` rather than `1/β`.
* `Sunflower.JansonALWZ` — the main theorem on that route: `spread_lemma_janson`,
  `alwz_janson`, `alwz_bounded_janson`. The reduction from the spread lemma to the sunflower
  bound (`alwz_of_spread_lemma`) and the padding wrapper (`alwz_bounded_of_alwz`) are shared
  verbatim with the second-moment route, so the two differ in exactly one lemma.

See `docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md` for the version choices, source
clarifications, and design notes recorded by this development — in particular why the main
theorem uses base-`1.9` logarithms.
-/
import Sunflower.Defs
import Sunflower.Lg
import Sunflower.Spread
import Sunflower.SpreadCore
import Sunflower.SpreadBottom
import Sunflower.SpreadIterate
import Sunflower.SpreadAssemble
import Sunflower.ALWZ
import Sunflower.ErdosRado
import Sunflower.Padding
import Sunflower.Robust
import Sunflower.Janson
import Sunflower.Bridge
import Sunflower.JansonCover
import Sunflower.JansonBottom
import Sunflower.JansonIterate
import Sunflower.JansonChase
import Sunflower.JansonMass
import Sunflower.JansonAssemble
import Sunflower.JansonALWZ
import Sunflower.BridgeBack
import Sunflower.Satisfying
import Sunflower.Schedule
import Sunflower.KappaZero
import Sunflower.DummyPad
import Sunflower.PadBottom
import Sunflower.SchedulePad
import Sunflower.KappaZeroPad
import Sunflower.BlockProb
import Sunflower.LowerBound
import Sunflower.Kraft
import Sunflower.PrefixCode
import Sunflower.RaoSpread
import Sunflower.RaoChi
import Sunflower.RaoEncoding
import Sunflower.RaoCase1
import Sunflower.RaoCase2
import Sunflower.RaoJoin
import Sunflower.RaoWidths
import Sunflower.RaoLengths
import Sunflower.RaoCover
import Sunflower.RaoSatisfying
import Sunflower.RaoRobust
import Sunflower.RaoSchedule
import Sunflower.SunflowerNote
import Sunflower.RaoBCW
import Sunflower.BCWLower

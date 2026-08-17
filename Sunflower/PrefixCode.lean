/-
# Self-delimiting codes, with decoders

Rao's encoding argument is written the way encoding arguments always are: "encode `|χ(X,U)|`;
then encode `W ∪ χ(X,U)`; since `U` is fixed there are at most `N` choices, so this takes
`log N + 1` bits; …". Two things have to be true for that to be a proof — the pieces must
concatenate into something *decodable* (else Kraft does not apply), and the claimed lengths
must be right. Informally the first is left to the reader.

Here a code **carries its decoder**:

  `dec (enc i ++ rest) = some (i, rest)`.

That single law is what makes the argument work: it gives injectivity and prefix-freeness for
free (`Code.prefixFree`), and it composes — the decoder for a concatenation runs the decoders
in order, which is exactly the informal "since `U` has been fixed, there are `N` choices"
reasoning made checkable. Field lengths may depend on everything decoded so far, via
`Code.sigma`.

## Contents

* `Code`, `Code.prefixFree`, `Code.encInj` — the structure and its consequences;
* `tagCode` (one bit), `unaryCode` (`0^n1`, for a length not known to the decoder),
  `ofInjLen` / `ofCardLe` (fixed-width index into a set of known size), `Code.sigma`
  (dependent concatenation), `Code.prod`, `Code.comap` (restrict along an injection);
* `logb_card_le_of_code` — the payoff, via `Coding.card_le_of_encoding`: a code whose words
  are at most `ℓ` bits on a set `T` forces `log₂|T| ≤ ℓ`.

The lengths are additive by construction (`length_sigma`), so a Rao-style calculation becomes
an inequality between explicit sums rather than an appeal to "combining all of the above".
-/
import Sunflower.Kraft

open Finset

namespace Sunflower

namespace Coding

universe u v

/-- A **self-delimiting code**: an encoder together with a decoder that consumes exactly the
codeword and returns the rest of the stream untouched. -/
structure Code (ι : Type u) where
  /-- The encoder. -/
  enc : ι → List Bool
  /-- The decoder: reads a codeword off the front, returns the value and the remainder. -/
  dec : List Bool → Option (ι × List Bool)
  /-- The decoder inverts the encoder, whatever follows. -/
  dec_enc : ∀ (i : ι) (r : List Bool), dec (enc i ++ r) = some (i, r)

namespace Code

variable {ι : Type u} {κ : Type v}

/-- **Codes are prefix-free**: if one codeword starts another, the values agree. Run the
decoder on the longer word — it must return both. -/
theorem prefixFree (C : Code ι) {i j : ι} (h : C.enc i <+: C.enc j) : i = j := by
  obtain ⟨r, hr⟩ := h
  have h1 : C.dec (C.enc j) = some (i, r) := by rw [← hr]; exact C.dec_enc i r
  have h2 : C.dec (C.enc j) = some (j, []) := by
    have := C.dec_enc j []
    rwa [List.append_nil] at this
  rw [h1] at h2
  exact (Prod.mk.injEq .. ▸ Option.some.inj h2).1

theorem encInj (C : Code ι) : Function.Injective C.enc := fun _ _ h =>
  C.prefixFree ⟨[], by rw [List.append_nil, h]⟩

/-! ## The combinators -/

/-- One bit. -/
def tagCode : Code Bool where
  enc b := [b]
  dec s := match s with
    | [] => none
    | b :: r => some (b, r)
  dec_enc := by intro b r; rfl

/-- The unary decoder: count the `false`s up to the first `true`. -/
def unaryDec : List Bool → Option (ℕ × List Bool)
  | [] => none
  | true :: r => some (0, r)
  | false :: r => (unaryDec r).map fun p => (p.1 + 1, p.2)

/-- `0^n 1` — for a natural number whose size the decoder does not know in advance. Rao uses
it for `|χ(X,U)|`, whose "trivial encoding" costs `|χ(X,U)| + 1` bits. -/
def unaryCode : Code ℕ where
  enc n := List.replicate n false ++ [true]
  dec := unaryDec
  dec_enc := by
    intro n
    induction n with
    | zero => intro r; rfl
    | succ n ih =>
        intro r
        rw [List.replicate_succ, List.cons_append, List.cons_append]
        show (unaryDec (List.replicate n false ++ [true] ++ r)).map _ = _
        rw [ih r]
        rfl

@[simp] lemma length_tagCode (b : Bool) : (tagCode.enc b).length = 1 := rfl

@[simp] lemma length_unaryCode (n : ℕ) : (unaryCode.enc n).length = n + 1 := by
  simp [unaryCode]

/-- **Dependent concatenation**: encode `i`, then encode a value whose code may depend on `i`.
This is what "since `U` has been fixed, there are `N` choices" means formally — the second
decoder is chosen by what the first one returned. -/
def sigma {κ : ι → Type v} (C : Code ι) (D : ∀ i, Code (κ i)) : Code (Σ i, κ i) where
  enc p := C.enc p.1 ++ (D p.1).enc p.2
  dec s := (C.dec s).bind fun p => ((D p.1).dec p.2).map fun q => (⟨p.1, q.1⟩, q.2)
  dec_enc := by
    rintro ⟨i, x⟩ r
    show (C.dec (C.enc i ++ (D i).enc x ++ r)).bind _ = _
    rw [List.append_assoc, C.dec_enc]
    show ((D i).dec ((D i).enc x ++ r)).map _ = _
    rw [(D i).dec_enc]
    rfl

@[simp] lemma length_sigma {κ : ι → Type v} (C : Code ι) (D : ∀ i, Code (κ i))
    (p : Σ i, κ i) :
    ((C.sigma D).enc p).length = (C.enc p.1).length + ((D p.1).enc p.2).length := by
  simp [sigma]

/-- Plain concatenation. -/
def prod (C : Code ι) (D : Code κ) : Code (ι × κ) where
  enc p := C.enc p.1 ++ D.enc p.2
  dec s := (C.dec s).bind fun p => (D.dec p.2).map fun q => ((p.1, q.1), q.2)
  dec_enc := by
    rintro ⟨i, x⟩ r
    show (C.dec (C.enc i ++ D.enc x ++ r)).bind _ = _
    rw [List.append_assoc, C.dec_enc]
    show (D.dec (D.enc x ++ r)).map _ = _
    rw [D.dec_enc]
    rfl

@[simp] lemma length_prod (C : Code ι) (D : Code κ) (p : ι × κ) :
    ((C.prod D).enc p).length = (C.enc p.1).length + (D.enc p.2).length := by
  simp [prod]

open scoped Classical in
/-- Restrict a code along an injection: to encode `ι'`, encode its image in `ι`. -/
noncomputable def comap (C : Code ι) (f : κ → ι) (hf : Function.Injective f) : Code κ where
  enc x := C.enc (f x)
  dec s := (C.dec s).bind fun p =>
    if h : ∃ x, f x = p.1 then some (Classical.choose h, p.2) else none
  dec_enc := by
    intro x r
    show (C.dec (C.enc (f x) ++ r)).bind _ = _
    rw [C.dec_enc]
    have hex : ∃ y, f y = f x := ⟨x, rfl⟩
    show (if h : ∃ y, f y = f x then some (Classical.choose h, r) else none) = _
    rw [dif_pos hex, hf (Classical.choose_spec hex)]

@[simp] lemma length_comap (C : Code ι) (f : κ → ι) (hf : Function.Injective f) (x : κ) :
    ((C.comap f hf).enc x).length = (C.enc (f x)).length := rfl

open scoped Classical in
/-- A fixed-width code from any injection with constant-length values. -/
noncomputable def ofInjLen (f : ι → List Bool) (k : ℕ) (hlen : ∀ i, (f i).length = k)
    (hinj : Function.Injective f) : Code ι where
  enc := f
  dec s := if h : ∃ i, f i = s.take k then some (Classical.choose h, s.drop k) else none
  dec_enc := by
    intro i r
    have htake : (f i ++ r).take k = f i := by
      rw [← hlen i]; exact List.take_left ..
    have hdrop : (f i ++ r).drop k = r := by
      rw [← hlen i]; exact List.drop_left ..
    have hex : ∃ j, f j = (f i ++ r).take k := ⟨i, htake.symm⟩
    show (if h : ∃ j, f j = (f i ++ r).take k then some (Classical.choose h, _) else none) = _
    rw [dif_pos hex, hdrop]
    have hfeq : f (Classical.choose hex) = f i := by
      rw [Classical.choose_spec hex, htake]
    rw [hinj hfeq]

/-- **Fixed-width index into a finite set**: `k` bits suffice for a type of size `≤ 2^k`. This
is the workhorse — "encode `S` inside the class `τ`, which has at most `φ` elements" becomes
`ofCardLe` at `k = ⌈log₂ φ⌉`. -/
noncomputable def ofCardLe (ι : Type u) [Fintype ι] (k : ℕ) (h : Fintype.card ι ≤ 2 ^ k) :
    Code ι :=
  let e : ι ↪ (Fin k → Bool) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_fun] using h))
  ofInjLen (fun i => List.ofFn (e i)) k (fun i => by simp)
    (fun i j hij => e.injective (List.ofFn_injective hij))

lemma length_ofCardLe (ι : Type u) [Fintype ι] (k : ℕ) (h : Fintype.card ι ≤ 2 ^ k) (i : ι) :
    ((ofCardLe ι k h).enc i).length = k := by
  simp [ofCardLe, ofInjLen]

/-- The decoder for `byCases`: read the tag, then run the corresponding branch decoder. -/
noncomputable def byCasesDec {ι : Type u} {Q : ι → Prop}
    (C₁ : Code {i // ¬ Q i}) (C₂ : Code {i // Q i}) :
    List Bool → Option (ι × List Bool)
  | [] => none
  | true :: r => (C₂.dec r).map fun p => (p.1.1, p.2)
  | false :: r => (C₁.dec r).map fun p => (p.1.1, p.2)

/-- **Case analysis**: a tag bit, then the code of the branch it selects. This is Rao's "the
first bit of the encoding is set to 0/1, and we proceed like this". Writing it directly rather
than as a `sigma` over `Bool` keeps the branch types out of a dependent pair, so injectivity
stays a matter of `Option` matching. -/
noncomputable def byCases {ι : Type u} (Q : ι → Prop) [DecidablePred Q]
    (C₁ : Code {i // ¬ Q i}) (C₂ : Code {i // Q i}) : Code ι where
  enc i := if h : Q i then true :: C₂.enc ⟨i, h⟩ else false :: C₁.enc ⟨i, h⟩
  dec := byCasesDec C₁ C₂
  dec_enc := by
    intro i r
    by_cases h : Q i
    · simp only [dif_pos h, List.cons_append, byCasesDec, C₂.dec_enc, Option.map_some]
    · simp only [dif_neg h, List.cons_append, byCasesDec, C₁.dec_enc, Option.map_some]

/-- The tag costs exactly one bit. -/
lemma length_byCases {ι : Type u} (Q : ι → Prop) [DecidablePred Q]
    (C₁ : Code {i // ¬ Q i}) (C₂ : Code {i // Q i}) (i : ι) :
    ((byCases Q C₁ C₂).enc i).length
      = 1 + (if h : Q i then (C₂.enc ⟨i, h⟩).length else (C₁.enc ⟨i, h⟩).length) := by
  by_cases h : Q i
  · rw [byCases]
    simp only [dif_pos h, List.length_cons]
    omega
  · rw [byCases]
    simp only [dif_neg h, List.length_cons]
    omega

/-- A length bound for the two branches gives one for the whole code. -/
theorem length_byCases_le {ι : Type u} (Q : ι → Prop) [DecidablePred Q]
    (C₁ : Code {i // ¬ Q i}) (C₂ : Code {i // Q i}) {L : ι → ℕ}
    (h₁ : ∀ (i : ι) (h : ¬ Q i), 1 + (C₁.enc ⟨i, h⟩).length ≤ L i)
    (h₂ : ∀ (i : ι) (h : Q i), 1 + (C₂.enc ⟨i, h⟩).length ≤ L i) (i : ι) :
    ((byCases Q C₁ C₂).enc i).length ≤ L i := by
  rw [length_byCases]
  by_cases h : Q i
  · rw [dif_pos h]; exact h₂ i h
  · rw [dif_neg h]; exact h₁ i h

/-- Codewords of a `byCases` code are nonempty — the tag alone guarantees it, which is the
side condition Kraft needs. -/
lemma byCases_enc_ne_nil {ι : Type u} (Q : ι → Prop) [DecidablePred Q]
    (C₁ : Code {i // ¬ Q i}) (C₂ : Code {i // Q i}) (i : ι) :
    (byCases Q C₁ C₂).enc i ≠ [] := by
  rw [byCases]
  by_cases h : Q i
  · simp only [dif_pos h]; exact List.cons_ne_nil _ _
  · simp only [dif_neg h]; exact List.cons_ne_nil _ _

/-- **Encode a member of a known finite set** in `k` bits, whenever `|T| ≤ 2^k`. Rao's
"encode `S` inside `τ(A,X,V)`, whose size is at most `φ(X,V)`". -/
noncomputable def memCode {ι : Type u} (T : Finset ι) (k : ℕ) (h : T.card ≤ 2 ^ k) :
    Code {x // x ∈ T} :=
  ofCardLe {x // x ∈ T} k (by rwa [Fintype.card_coe])

@[simp] lemma length_memCode {ι : Type u} (T : Finset ι) (k : ℕ) (h : T.card ≤ 2 ^ k)
    (x : {x // x ∈ T}) : ((memCode T k h).enc x).length = k :=
  length_ofCardLe _ k _ x

/-- **Encode a subset of a known finite set** in `|s|` bits — one per element, which is what
"this takes `|χ(X,U)|` bits" means in Rao's steps (c) and (e). -/
noncomputable def powersetCode {α : Type u} [DecidableEq α] (s : Finset α) :
    Code {t // t ∈ s.powerset} :=
  memCode s.powerset s.card (by rw [Finset.card_powerset])

@[simp] lemma length_powersetCode {α : Type u} [DecidableEq α] (s : Finset α)
    (t : {t // t ∈ s.powerset}) : ((powersetCode s).enc t).length = s.card :=
  length_memCode _ _ _ t

end Code

/-- **The payoff.** A code whose words are at most `ℓ` bits long on a nonempty `T` forces
`log₂|T| ≤ ℓ`. This is Rao's Lemma 5 applied to a concrete encoding: exhibit the code, bound
its lengths, read off a bound on the number of objects. -/
theorem logb_card_le_of_code {ι : Type u} (C : Code ι) {T : Finset ι} (hT : T.Nonempty)
    {ℓ : ℝ} (hne : ∀ i ∈ T, C.enc i ≠ [])
    (hlen : ∀ i ∈ T, ((C.enc i).length : ℝ) ≤ ℓ) :
    Real.logb 2 (T.card : ℝ) ≤ ℓ :=
  card_le_of_encoding hT C.enc (fun _i _ _j _ h => C.prefixFree h) hne hlen

/-- **The contraction step of an encoding argument.** If the objects of `P` — at least `N` of
them — are encoded in

  `log₂ N + A·f i − B·g i`

bits, then `B·∑ g ≤ A·∑ f`. This is Rao's "applying Lemma 5, we conclude that the expected
length must satisfy … and so `E|χ(X,W)| ≤ (2/3)·E|χ(X,U)|`", with `A/B ≤ 2/3` supplying the
factor: the encoding cannot beat `log₂` of the number of objects, so whatever it *saves* on
`g` it must have spent on `f`.

Both of Rao's cases produce a code of exactly this shape, so this is the only place the coding
layer meets the combinatorics. -/
theorem sum_le_of_code {ι : Type u} (C : Code ι) {P : Finset ι} (hP : P.Nonempty)
    {N A B : ℝ} {f g : ι → ℝ} (hN : 0 < N) (hcard : N ≤ (P.card : ℝ))
    (hne : ∀ i ∈ P, C.enc i ≠ [])
    (hlen : ∀ i ∈ P, ((C.enc i).length : ℝ) ≤ Real.logb 2 N + A * f i - B * g i) :
    B * ∑ i ∈ P, g i ≤ A * ∑ i ∈ P, f i := by
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP
  -- Lemma 5: the average length is at least `log₂|P|`
  have h1 : Real.logb 2 (P.card : ℝ) ≤ (∑ i ∈ P, ((C.enc i).length : ℝ)) / (P.card : ℝ) :=
    logb_card_le_avg_length hP C.enc (fun i _ j _ h => C.prefixFree h) hne
  -- and at most `log₂ N + (A·∑f − B·∑g)/|P|`
  have h2 : (∑ i ∈ P, ((C.enc i).length : ℝ))
      ≤ (P.card : ℝ) * Real.logb 2 N + (A * ∑ i ∈ P, f i - B * ∑ i ∈ P, g i) := by
    calc (∑ i ∈ P, ((C.enc i).length : ℝ))
        ≤ ∑ i ∈ P, (Real.logb 2 N + A * f i - B * g i) := Finset.sum_le_sum hlen
      _ = (P.card : ℝ) * Real.logb 2 N + (A * ∑ i ∈ P, f i - B * ∑ i ∈ P, g i) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  -- `log₂ N ≤ log₂|P|` closes it
  have h3 : Real.logb 2 N ≤ Real.logb 2 (P.card : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hN hcard
  have h4 : (P.card : ℝ) * Real.logb 2 (P.card : ℝ) ≤ ∑ i ∈ P, ((C.enc i).length : ℝ) := by
    rw [le_div_iff₀ hPpos] at h1
    linarith [h1]
  nlinarith [h2, h3, h4, hPpos]

/-- A code that begins with a tag bit never has an empty codeword, which is the side condition
Kraft needs. Rao's encoding does begin with a case bit. -/
lemma enc_ne_nil_of_tag {_ι : Type u} {κ : Bool → Type u} (D : ∀ b, Code (κ b))
    (p : Σ b, κ b) : (Code.tagCode.sigma D).enc p ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [Code.length_sigma] at hlen
  simp at hlen

/-! ## Sanity checks

Small round-trips, exercising the combinators the way the encoding argument will. -/

example : (Code.tagCode.prod Code.unaryCode).enc (true, 2) = [true, false, false, true] := rfl

example : (Code.tagCode.prod Code.unaryCode).dec ([true, false, false, true] ++ [false, true])
    = some ((true, 2), [false, true]) :=
  (Code.tagCode.prod Code.unaryCode).dec_enc (true, 2) [false, true]

example (b : Bool) (n : ℕ) :
    ((Code.tagCode.prod Code.unaryCode).enc (b, n)).length = n + 2 := by
  rw [Code.length_prod, Code.length_tagCode, Code.length_unaryCode]
  show 1 + (n + 1) = n + 2
  omega

/-- **A record of Rao's shape**: a number in unary, then a member of a class whose *width
depends on that number*. This is the dependency the informal argument leaves implicit
("since `|χ(X,U)|` has been encoded, there are at most `φ` choices"), and `Code.sigma` is
where it becomes a proof obligation rather than a remark. -/
noncomputable example {ι : Type} (T : ℕ → Finset ι) (N : ℕ → ℕ)
    (h : ∀ a, (T a).card ≤ 2 ^ N a) : Code (Σ a : ℕ, {x // x ∈ T a}) :=
  Code.unaryCode.sigma fun a => Code.memCode (T a) (N a) (h a)

/-- …and its length is the sum of the field widths, by construction. -/
example {ι : Type} (T : ℕ → Finset ι) (N : ℕ → ℕ) (h : ∀ a, (T a).card ≤ 2 ^ N a)
    (a : ℕ) (x : {x // x ∈ T a}) :
    ((Code.unaryCode.sigma fun a => Code.memCode (T a) (N a) (h a)).enc ⟨a, x⟩).length
      = (a + 1) + N a := by
  rw [Code.length_sigma, Code.length_unaryCode, Code.length_memCode]

end Coding

end Sunflower

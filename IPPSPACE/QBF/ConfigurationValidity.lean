/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationEncoding
import IPPSPACE.QBF.BooleanGadgets

/-!
# Quantifier-free validity of encoded configurations

Validity is assembled field by field in the exact product/vector layout of
`configurationCodec`. One-hot state and head fields use quadratic-size formulas;
two-bit symbols need no constraint. The construction never enumerates whole
configurations. These formulas recognize the finite component codec's exact
image; conditions relating those components to an upstream machine's windowed
configuration remain a separate integration obligation.
-/

namespace IPPSPACE

open Complexity

/-- A bounded quantifier-free formula recognizing exactly the image of a codec
at any supplied vector of variable names. Repeated names are permitted. -/
structure CodecValidity {α : Type} {width : ℕ}
    (codec : FixedWidthCodec α width) (bound : ℕ) where
  formula : (Fin width → ℕ) → QBF
  eval_iff : ∀ names assignment, (formula names).eval assignment = true ↔
    ∃ a, codec.encode a = assignment ∘ names
  quantifierFree : ∀ names, (formula names).QuantifierFree
  names_mem : ∀ names i, i ∈ qbfNames (formula names) → ∃ j, names j = i
  nodeCount_le : ∀ names, nodeCount (formula names) ≤ bound

namespace CodecValidity

variable {α β : Type} {width v N M : ℕ}

theorem names_lt {codec : FixedWidthCodec α width} (valid : CodecValidity codec N)
    (names : Fin width → ℕ) (B : ℕ) (hnames : ∀ j, names j < B) :
    ∀ i ∈ qbfNames (valid.formula names), i < B := by
  intro i hi
  obtain ⟨j, rfl⟩ := valid.names_mem names i hi
  exact hnames j

/-- Every fixed-length Boolean word is a valid word encoding. -/
def word (width : ℕ) : CodecValidity (FixedWidthCodec.word width) 1 where
  formula _ := .tru
  eval_iff names assignment := by
    simp only [QBF.eval_tru, true_iff]
    exact ⟨assignment ∘ names, rfl⟩
  quantifierFree _ := by simp [QBF.QuantifierFree, QBF.quantDepth]
  names_mem _ _ h := by simp [qbfNames] at h
  nodeCount_le _ := le_rfl

/-- An explicit equivalence of represented data leaves validity unchanged. -/
def ofEquiv (e : α ≃ β) {codec : FixedWidthCodec β width}
    (valid : CodecValidity codec N) : CodecValidity (codec.ofEquiv e) N where
  formula := valid.formula
  eval_iff names assignment := by
    rw [valid.eval_iff]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨e.symm b, by simpa [FixedWidthCodec.ofEquiv] using hb⟩
    · rintro ⟨a, ha⟩
      exact ⟨e a, ha⟩
  quantifierFree := valid.quantifierFree
  names_mem := valid.names_mem
  nodeCount_le := valid.nodeCount_le

/-- Reassociate a width expression in both the codec and its validity proof. -/
def castWidth {codec : FixedWidthCodec α width} (h : width = v)
    (valid : CodecValidity codec N) : CodecValidity (codec.castWidth h) N := by
  subst v
  exact valid

/-- Consecutive fields are valid exactly when both components are valid. -/
def prod {left : FixedWidthCodec α width} {right : FixedWidthCodec β v}
    (lv : CodecValidity left N) (rv : CodecValidity right M) :
    CodecValidity (left.prod right) (N + M + 1) where
  formula names := .conj (lv.formula (names ∘ Fin.castAdd v))
    (rv.formula (names ∘ Fin.natAdd width))
  eval_iff names assignment := by
    simp only [QBF.eval_conj, Bool.and_eq_true, lv.eval_iff, rv.eval_iff]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨(a, b), ?_⟩
      change Fin.append (left.encode a) (right.encode b) = assignment ∘ names
      rw [ha, hb]
      exact Fin.append_castAdd_natAdd (f := assignment ∘ names)
    · rintro ⟨⟨a, b⟩, hab⟩
      constructor
      · refine ⟨a, ?_⟩
        funext i
        simpa [FixedWidthCodec.prod] using congrFun hab (Fin.castAdd v i)
      · refine ⟨b, ?_⟩
        funext i
        simpa [FixedWidthCodec.prod] using congrFun hab (Fin.natAdd width i)
  quantifierFree names := QBF.quantifierFree_conj.mpr
    ⟨lv.quantifierFree _, rv.quantifierFree _⟩
  names_mem names i hi := by
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, hj⟩ := lv.names_mem _ _ hi
      exact ⟨Fin.castAdd v j, hj⟩
    · obtain ⟨j, hj⟩ := rv.names_mem _ _ hi
      exact ⟨Fin.natAdd width j, hj⟩
  nodeCount_le names := by
    have hl := lv.nodeCount_le (names ∘ Fin.castAdd v)
    have hr := rv.nodeCount_le (names ∘ Fin.natAdd width)
    simp only [nodeCount]
    omega

/-- A row-major vector is valid exactly when each independently encoded field
is valid. The formula has one copy of the component test per row. -/
def vector {codec : FixedWidthCodec α width} (valid : CodecValidity codec N) (n : ℕ) :
    CodecValidity (codec.vector n) ((N + 1) * n + 1) where
  formula names := qbfAllFin n (fun i =>
    valid.formula (fun j => names (finProdFinEquiv (i, j))))
  eval_iff names assignment := by
    rw [eval_qbfAllFin]
    simp only [valid.eval_iff]
    constructor
    · intro h
      choose values hvalues using h
      refine ⟨values, ?_⟩
      funext i
      have hi := congrFun (hvalues (finProdFinEquiv.symm i).1)
        (finProdFinEquiv.symm i).2
      change codec.encode (values (finProdFinEquiv.symm i).1)
        (finProdFinEquiv.symm i).2 = assignment (names i)
      simpa only [Function.comp_apply, Prod.mk.eta, Equiv.apply_symm_apply] using hi
    · rintro ⟨values, hvalues⟩ i
      refine ⟨values i, ?_⟩
      funext j
      have hj := congrFun hvalues (finProdFinEquiv (i, j))
      change codec.encode (values (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 =
        assignment (names (finProdFinEquiv (i, j))) at hj
      simpa only [Equiv.symm_apply_apply, Function.comp_apply] using hj
  quantifierFree names := quantifierFree_qbfAllFin _ _ (fun _ => valid.quantifierFree _)
  names_mem names i hi := by
    obtain ⟨row, hrow⟩ := (mem_qbfNames_qbfAllFin _ _ _).mp hi
    obtain ⟨col, hcol⟩ := valid.names_mem _ _ hrow
    exact ⟨finProdFinEquiv (row, col), hcol⟩
  nodeCount_le names := nodeCount_qbfAllFin_le _ _ _ (fun _ => valid.nodeCount_le _)

private theorem blockValues_names_mem {width : ℕ} (names : Fin width → ℕ)
    (values : Fin width → Bool) (i : ℕ) (hi : i ∈ qbfNames (blockValues names values)) :
    ∃ j, names j = i := by
  induction width with
  | zero => simp [blockValues, qbfNames] at hi
  | succ width ih =>
    rcases Finset.mem_union.mp hi with hi | hi
    · refine ⟨0, ?_⟩
      cases hv : values 0 <;> simpa [bitValue, hv, qbfNames, eq_comm] using hi
    · obtain ⟨j, hj⟩ := ih (Fin.tail names) (Fin.tail values) hi
      exact ⟨j.succ, hj⟩

/-- The one-hot formula enumerates only the `n` head/state positions, with `n`
literal checks in each disjunct. It does not enumerate configuration tuples. -/
def fin (n : ℕ) : CodecValidity (FixedWidthCodec.fin n) ((3 * n + 2) * n + 1) where
  formula names := qbfAnyFin n (fun i => blockValues names (FixedWidthCodec.encodeFin i))
  eval_iff names assignment := by
    simp only [eval_qbfAnyFin, eval_blockValues]
    simp only [FixedWidthCodec.fin, eq_comm]
  quantifierFree names := quantifierFree_qbfAnyFin _ _ (fun _ => quantifierFree_blockValues _ _)
  names_mem names i hi := by
    obtain ⟨j, hj⟩ := (mem_qbfNames_qbfAnyFin _ _ _).mp hi
    exact blockValues_names_mem names (FixedWidthCodec.encodeFin j) i hj
  nodeCount_le names := nodeCount_qbfAnyFin_le _ _ _ (fun _ => nodeCount_blockValues_le _ _)

end CodecValidity

/-- A polynomial node budget for one-hot positions. -/
def oneHotValiditySize (n : ℕ) : ℕ := (3 * n + 2) * n + 1

/-- A head plus `n` unrestricted two-bit symbols. -/
def tapeValiditySize (n : ℕ) : ℕ := oneHotValiditySize n + (2 * n + 1) + 1

/-- Explicit polynomial bound for the complete configuration validity formula.
The state and tape counts are machine constants; input length and space occur
only through additions and products. -/
def configurationValiditySize (states tapes inputLength space : ℕ) : ℕ :=
  oneHotValiditySize states +
    (oneHotValiditySize (inputLength + space + 2) +
      (((tapeValiditySize (space + 1) + 1) * tapes + 1) +
        tapeValiditySize (space + 2) + 1) + 1) + 1

/-- Concrete validity proof following the exact products, vectors and final
width cast in `configurationCodec`. Two-bit alphabet numbering is unrestricted
because every pair of bits names a symbol. -/
def configurationValidity {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ) :
    CodecValidity (configurationCodec stateNumber symbolBits tapes inputLength space)
      (configurationValiditySize states tapes inputLength space) := by
  let symbol := (CodecValidity.word 2).ofEquiv symbolBits
  let tape := fun n => (CodecValidity.fin n).prod (symbol.vector n)
  let raw := ((CodecValidity.fin states).ofEquiv stateNumber).prod
    ((CodecValidity.fin (inputLength + space + 2)).prod
      (((tape (space + 1)).vector tapes).prod (tape (space + 2))))
  exact raw.castWidth (by dsimp [configurationWidth]; ring)

/-- The executable quantifier-free validity formula for the whole finite
configuration component product, at arbitrary variable names. -/
def configurationValidityFormula {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  (configurationValidity stateNumber symbolBits tapes inputLength space).formula names

/-- Evaluation recognizes exactly the encoder image, rather than merely words
that happen to receive some value from the permissive component decoder. -/
theorem eval_configurationValidityFormula {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (assignment : ℕ → Bool) :
    (configurationValidityFormula stateNumber symbolBits tapes inputLength space names).eval
      assignment = true ↔
    ∃ c, (configurationCodec stateNumber symbolBits tapes inputLength space).encode c =
      assignment ∘ names :=
  (configurationValidity stateNumber symbolBits tapes inputLength space).eval_iff names assignment

theorem quantifierFree_configurationValidityFormula {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    (configurationValidityFormula stateNumber symbolBits tapes inputLength space names).QuantifierFree :=
  (configurationValidity stateNumber symbolBits tapes inputLength space).quantifierFree names

theorem qbfNames_configurationValidityFormula_mem {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) (i : ℕ)
    (hi : i ∈ qbfNames
      (configurationValidityFormula stateNumber symbolBits tapes inputLength space names)) :
    ∃ j, names j = i :=
  (configurationValidity stateNumber symbolBits tapes inputLength space).names_mem names i hi

theorem qbfNames_configurationValidityFormula_lt {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (B : ℕ) (hnames : ∀ j, names j < B) :
    ∀ i ∈ qbfNames (configurationValidityFormula stateNumber symbolBits tapes inputLength space names),
      i < B :=
  (configurationValidity stateNumber symbolBits tapes inputLength space).names_lt names B hnames

theorem nodeCount_configurationValidityFormula_le {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    nodeCount (configurationValidityFormula stateNumber symbolBits tapes inputLength space names) ≤
      configurationValiditySize states tapes inputLength space :=
  (configurationValidity stateNumber symbolBits tapes inputLength space).nodeCount_le names

/-- The formula's exact-image guarantee also characterizes successful canonical
decoding, including rejection of zero-hot and multiply-hot fields. -/
theorem eval_configurationValidityFormula_iff_decodeCanonical {Q Γ : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (symbolBits : Γ ≃ (Fin 2 → Bool))
    (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (assignment : ℕ → Bool) :
    (configurationValidityFormula stateNumber symbolBits tapes inputLength space names).eval
      assignment = true ↔
    ∃ c, (configurationCodec stateNumber symbolBits tapes inputLength space).decodeCanonical
      (assignment ∘ names) = some c := by
  simp only [eval_configurationValidityFormula, FixedWidthCodec.decodeCanonical_eq_some_iff]

/-- Expand the bound as a polynomial in the numeric component parameters. -/
theorem configurationValiditySize_eq (states tapes inputLength space : ℕ) :
    configurationValiditySize states tapes inputLength space =
      3 * states ^ 2 + 2 * states +
      3 * (inputLength + space + 2) ^ 2 + 2 * (inputLength + space + 2) +
      (3 * (space + 1) ^ 2 + 4 * (space + 1) + 4) * tapes +
      3 * (space + 2) ^ 2 + 4 * (space + 2) + 9 := by
  unfold configurationValiditySize tapeValiditySize oneHotValiditySize
  ring

/-- Substituting a polynomial space budget gives an explicit natural-coefficient
polynomial node bound in the original machine input length. -/
noncomputable def configurationValidityPolynomial
    (states tapes : ℕ) (space : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3 * states ^ 2 + 2 * states) +
    3 * (Polynomial.X + space + 2) ^ 2 + 2 * (Polynomial.X + space + 2) +
    (3 * (space + 1) ^ 2 + 4 * (space + 1) + 4) * Polynomial.C tapes +
    3 * (space + 2) ^ 2 + 4 * (space + 2) + 9

@[simp] theorem configurationValidityPolynomial_eval
    (states tapes : ℕ) (space : Polynomial ℕ) (inputLength : ℕ) :
    (configurationValidityPolynomial states tapes space).eval inputLength =
      configurationValiditySize states tapes inputLength (space.eval inputLength) := by
  simp [configurationValidityPolynomial, configurationValiditySize_eq]

end IPPSPACE

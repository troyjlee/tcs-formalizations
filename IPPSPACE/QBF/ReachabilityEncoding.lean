/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ReachabilityTemplate
import IPPSPACE.QBF.PrenexReduction

/-!
# Binary-size bounds for the concrete reachability construction

All generated variable names, including binders, are bounded by the endpoints
and the three fresh blocks allocated at each squaring level. Combined with the
node bounds and the canonical binary codec, these are actual bit-length bounds.
The final executable output is a closed prenex QBF encoding whose language
membership is exactly reachability for the supplied Boolean edge template.

These results bound output representations, not construction time or upstream
machine configuration encodings.
-/

namespace IPPSPACE

open Complexity

theorem qbfNames_existsBlock_lt (start width B : ℕ) (φ : QBF)
    (hblock : start + width ≤ B) (hφ : ∀ i ∈ qbfNames φ, i < B) :
    ∀ i ∈ qbfNames (existsBlock start width φ), i < B := by
  induction width generalizing start with
  | zero => exact hφ
  | succ width ih =>
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · exact ih (start + 1) (by omega) i hi

theorem qbfNames_forallBlock_lt (start width B : ℕ) (φ : QBF)
    (hblock : start + width ≤ B) (hφ : ∀ i ∈ qbfNames φ, i < B) :
    ∀ i ∈ qbfNames (forallBlock start width φ), i < B := by
  induction width generalizing start with
  | zero => exact hφ
  | succ width ih =>
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · exact ih (start + 1) (by omega) i hi

theorem qbfNames_bitEquality_lt (a b B : ℕ) (ha : a < B) (hb : b < B) :
    ∀ i ∈ qbfNames (bitEquality a b), i < B := by
  intro i hi
  have hi' : i = a ∨ i = b := by simpa [bitEquality, qbfNames] using hi
  rcases hi' with rfl | rfl <;> assumption

theorem qbfNames_blockEquality_lt {width : ℕ} (a b : Fin width → ℕ) (B : ℕ)
    (ha : ∀ j, a j < B) (hb : ∀ j, b j < B) :
    ∀ i ∈ qbfNames (blockEquality a b), i < B := by
  induction width with
  | zero => simp [blockEquality, qbfNames]
  | succ width ih =>
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_bitEquality_lt _ _ B (ha 0) (hb 0) i hi
    · exact ih (Fin.tail a) (Fin.tail b) (fun j => ha j.succ) (fun j => hb j.succ) i hi

theorem qbfNames_bitValue_lt (name B : ℕ) (value : Bool) (hname : name < B) :
    ∀ i ∈ qbfNames (bitValue name value), i < B := by
  cases value <;> simpa [bitValue, qbfNames] using hname

theorem qbfNames_blockValues_lt {width : ℕ} (names : Fin width → ℕ)
    (values : Fin width → Bool) (B : ℕ) (hnames : ∀ j, names j < B) :
    ∀ i ∈ qbfNames (blockValues names values), i < B := by
  induction width with
  | zero => simp [blockValues, qbfNames]
  | succ width ih =>
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_bitValue_lt _ B (values 0) (hnames 0) i hi
    · exact ih (Fin.tail names) (Fin.tail values) (fun j => hnames j.succ) i hi

theorem qbfNames_selectedPair_lt {width : ℕ} (a middle b u v : Fin width → ℕ) (B : ℕ)
    (ha : ∀ j, a j < B) (hm : ∀ j, middle j < B) (hb : ∀ j, b j < B)
    (hu : ∀ j, u j < B) (hv : ∀ j, v j < B) :
    ∀ i ∈ qbfNames (selectedPair a middle b u v), i < B := by
  intro i hi
  simp only [selectedPair, qbfNames, Finset.mem_union] at hi
  rcases hi with (hi | hi) | (hi | hi)
  · exact qbfNames_blockEquality_lt u a B hu ha i hi
  · exact qbfNames_blockEquality_lt v middle B hv hm i hi
  · exact qbfNames_blockEquality_lt u middle B hu hm i hi
  · exact qbfNames_blockEquality_lt v b B hv hb i hi

theorem qbfNames_forallNames_lt (names : List ℕ) (φ : QBF) (B : ℕ)
    (hnames : ∀ i ∈ names, i < B) (hφ : ∀ i ∈ qbfNames φ, i < B) :
    ∀ i ∈ qbfNames (forallNames names φ), i < B := by
  induction names with
  | nil => exact hφ
  | cons j names ih =>
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hnames i (by simp)
    · exact ih (fun k hk => hnames k (List.mem_cons_of_mem _ hk)) i hi

/-- Closing a formula introduces only names already occurring in its syntax. -/
theorem qbfNames_closeQBF_lt (φ : QBF) (B : ℕ) (hφ : ∀ i ∈ qbfNames φ, i < B) :
    ∀ i ∈ qbfNames (closeQBF φ), i < B := by
  apply qbfNames_forallNames_lt _ φ B _ hφ
  intro i hi
  exact hφ i (freeVars_subset_qbfNames φ ((mem_freeVarList i φ).mp hi))

/-- A template supported on the two endpoint blocks introduces no other names. -/
theorem qbfNames_instantiateEdge_lt {width : ℕ} (base : QBF) (hbase : base.QuantifierFree)
    (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (a b : Fin width → ℕ) (B : ℕ) (ha : ∀ j, a j < B) (hb : ∀ j, b j < B) :
    ∀ i ∈ qbfNames (instantiateEdge base a b), i < B := by
  intro i hi
  rw [instantiateEdge, qbfNames_renameQBF] at hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hbound := hvars j ((qbfNames_eq_freeVars_of_quantifierFree base hbase) ▸ hj)
  by_cases hfirst : j < width
  · simpa [edgeBlockRenaming, hfirst] using ha ⟨j, hfirst⟩
  · simpa [edgeBlockRenaming, hfirst, hbound] using hb ⟨j - width, by omega⟩

/-- Idle transitions use only the names already supplied as endpoints. -/
theorem qbfNames_stutterFormula_lt (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (hEdge : ∀ a b B, (∀ j, a j < B) → (∀ j, b j < B) →
      ∀ i ∈ qbfNames (edgeFormula a b), i < B)
    (a b : Fin width → ℕ) (B : ℕ) (ha : ∀ j, a j < B) (hb : ∀ j, b j < B) :
    ∀ i ∈ qbfNames (stutterFormula width edgeFormula a b), i < B := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact qbfNames_blockEquality_lt a b B ha hb i hi
  · exact hEdge a b B ha hb i hi

theorem blockNames_lt_of_le (start width B : ℕ) (h : start + width ≤ B)
    (i : Fin width) : blockNames start width i < B :=
  (Nat.add_lt_add_left i.isLt start).trans_le h

/-- Each level allocates three width-sized blocks; the recursive copy uses
exactly the next interval, so no generated name exceeds the final boundary. -/
theorem qbfNames_reachFormula_lt (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (hEdge : ∀ a b B, (∀ j, a j < B) → (∀ j, b j < B) →
      ∀ i ∈ qbfNames (edgeFormula a b), i < B)
    (depth fresh : ℕ) (a b : Fin width → ℕ)
    (ha : ∀ j, a j < fresh) (hb : ∀ j, b j < fresh) :
    ∀ i ∈ qbfNames (reachFormula width edgeFormula depth fresh a b),
      i < fresh + 3 * width * depth := by
  induction depth generalizing fresh a b with
  | zero => simpa [reachFormula] using hEdge a b fresh ha hb
  | succ depth ih =>
    have hB : fresh + 3 * width ≤ fresh + 3 * width * (depth + 1) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    have hrec := ih (fresh + 3 * width) (blockNames (fresh + width) width)
      (blockNames (fresh + 2 * width) width)
      (blockNames_lt_of_le _ _ _ (by omega)) (blockNames_lt_of_le _ _ _ (by omega))
    simp only [reachFormula]
    apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
    apply qbfNames_forallBlock_lt _ _ _ _ (by omega)
    apply qbfNames_forallBlock_lt _ _ _ _ (by omega)
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_selectedPair_lt _ _ _ _ _ _
        (fun j => (ha j).trans_le (by omega))
        (blockNames_lt_of_le _ _ _ (by omega))
        (fun j => (hb j).trans_le (by omega))
        (blockNames_lt_of_le _ _ _ (by omega))
        (blockNames_lt_of_le _ _ _ (by omega)) i hi
    · have hr := hrec i hi
      simp only [Nat.mul_add, Nat.mul_one]
      omega

/-- Fixed endpoint values add no names beyond the two initial blocks. -/
theorem qbfNames_fixedEndpointReachFormula_lt (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (hEdge : ∀ a b B, (∀ j, a j < B) → (∀ j, b j < B) →
      ∀ i ∈ qbfNames (edgeFormula a b), i < B)
    (source target : Fin width → Bool) :
    ∀ i ∈ qbfNames (fixedEndpointReachFormula width edgeFormula source target),
      i < 2 * width + 3 * width * width := by
  have hreach := qbfNames_reachFormula_lt width (stutterFormula width edgeFormula)
    (qbfNames_stutterFormula_lt width edgeFormula hEdge) width (2 * width)
    (blockNames 0 width) (blockNames width width)
    (blockNames_lt_of_le _ _ _ (by omega)) (blockNames_lt_of_le _ _ _ (by omega))
  unfold fixedEndpointReachFormula
  apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
  apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact qbfNames_blockValues_lt _ source _ (blockNames_lt_of_le _ _ _ (by omega)) i hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_blockValues_lt _ target _ (blockNames_lt_of_le _ _ _ (by omega)) i hi
    · exact hreach i hi

theorem qbfNames_templateReachability_lt {width : ℕ} (base : QBF) (hbase : base.QuantifierFree)
    (hvars : ∀ i ∈ base.freeVars, i < 2 * width) (source target : Fin width → Bool) :
    ∀ i ∈ qbfNames (templateReachability base source target),
      i < 2 * width + 3 * width * width := by
  apply qbfNames_closeQBF_lt
  exact qbfNames_fixedEndpointReachFormula_lt width (instantiateEdge base)
    (qbfNames_instantiateEdge_lt base hbase hvars) source target

theorem qbfMaxVar_templateReachability_le {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    qbfMaxVar (templateReachability base source target) ≤ 2 * width + 3 * width * width := by
  apply qbfMaxVar_le_of_name_bound
  intro i hi
  exact Nat.le_of_lt (qbfNames_templateReachability_lt base hbase hvars source target i hi)

/-- Numeric bounds imply a coarse polynomial bit bound; the codec itself still
uses binary names. This lemma is also useful for other configuration formulas. -/
theorem length_encodeQBF_le_of_numeric_bounds (φ : QBF) (N B : ℕ)
    (hnodes : nodeCount φ ≤ N) (hnames : qbfMaxVar φ ≤ B) :
    (encodeQBF φ).length ≤ N * (2 * B + 4) := by
  apply (length_encodeQBF_le_of_maxVar φ B hnames).trans
  apply Nat.mul_le_mul hnodes
  have := nat_size_le_self B
  omega

/-- Prenex conversion preserves node count and increases names only by its
linear fresh-counter budget, so the same polynomial estimate applies directly. -/
theorem length_encodeQBF_toPrenex_le_of_numeric_bounds (φ : QBF) (N B : ℕ)
    (hnodes : nodeCount φ ≤ N) (hnames : qbfMaxVar φ ≤ B) :
    (encodeQBF (toPrenex φ).toQBF).length ≤ N * (2 * (B + N + 1) + 4) := by
  apply length_encodeQBF_le_of_numeric_bounds
  · simpa using hnodes
  · have := qbfMaxVar_toPrenex_le φ
    omega

/-- A node budget using the bit length of the original edge template. -/
def reachabilityNodeBudget (templateLength width : ℕ) : ℕ :=
  2 * (templateLength + 18 * width + 6 + width * (43 * width + 9))

/-- Upper boundary of all blocks in a width-level reachability formula. -/
def reachabilityNameBudget (width : ℕ) : ℕ := 2 * width + 3 * width * width

theorem nodeCount_templateReachability_le_budget {width : ℕ} (base : QBF)
    (source target : Fin width → Bool) :
    nodeCount (templateReachability base source target) ≤
      reachabilityNodeBudget (encodeQBF base).length width := by
  apply (nodeCount_templateReachability_le base source target).trans
  unfold reachabilityNodeBudget
  have := nodeCount_le_length_encodeQBF base
  omega

/-- The sharper estimate retains the actual binary width of the largest name. -/
theorem length_encode_templateReachability_le_binary {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    (encodeQBF (templateReachability base source target)).length ≤
      reachabilityNodeBudget (encodeQBF base).length width *
        (2 * (reachabilityNameBudget width).size + 4) := by
  apply (length_encodeQBF_le_of_maxVar _ _
    (qbfMaxVar_templateReachability_le base hbase hvars source target)).trans
  exact Nat.mul_le_mul (nodeCount_templateReachability_le_budget base source target) (Nat.le_refl _)

theorem length_encode_templateReachability_le {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    (encodeQBF (templateReachability base source target)).length ≤
      reachabilityNodeBudget (encodeQBF base).length width *
        (2 * reachabilityNameBudget width + 4) :=
  length_encodeQBF_le_of_numeric_bounds _ _ _
    (nodeCount_templateReachability_le_budget base source target)
    (qbfMaxVar_templateReachability_le base hbase hvars source target)

/-- The actual binary target string, after the verified capture-safe conversion. -/
def encodeTemplateReachability {width : ℕ} (base : QBF)
    (source target : Fin width → Bool) : List Bool :=
  encodeQBF (toPrenex (templateReachability base source target)).toQBF

theorem encodeTemplateReachability_mem_iff {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    EncodedTruePrenex (encodeTemplateReachability base source target) ↔
      Relation.ReflTransGen (templateEdge base) source target := by
  rw [encodeTemplateReachability, encodedTruePrenex_encode_iff _
    (toPrenex_closed _ (templateReachability_closed base source target)), toPrenex_isTrue_iff]
  exact templateReachability_true_iff base hbase hvars source target

theorem encodeTemplateReachability_length_le {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    (encodeTemplateReachability base source target).length ≤
      reachabilityNodeBudget (encodeQBF base).length width *
        (2 * (reachabilityNameBudget width +
          reachabilityNodeBudget (encodeQBF base).length width + 1) + 4) :=
  length_encodeQBF_toPrenex_le_of_numeric_bounds _ _ _
    (nodeCount_templateReachability_le_budget base source target)
    (qbfMaxVar_templateReachability_le base hbase hvars source target)

theorem reachabilityNodeBudget_le_square (L width : ℕ) :
    reachabilityNodeBudget L width ≤ 100 * (L + 2 * width + 1) ^ 2 := by
  unfold reachabilityNodeBudget
  nlinarith

theorem reachabilityNameBudget_le_square (L width : ℕ) :
    reachabilityNameBudget width ≤ 5 * (L + 2 * width + 1) ^ 2 := by
  calc
    reachabilityNameBudget width ≤ 5 * (width + 1) ^ 2 := by
      unfold reachabilityNameBudget
      nlinarith
    _ ≤ 5 * (L + 2 * width + 1) ^ 2 := by gcongr; omega

/-- A single explicit degree-four polynomial bounds the binary closed QBF.
`L + 2*width` counts the edge-template bits and the two concrete endpoint vectors. -/
theorem length_encode_templateReachability_le_poly {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    (encodeQBF (templateReachability base source target)).length ≤
      1400 * ((encodeQBF base).length + 2 * width + 1) ^ 4 := by
  apply (length_encode_templateReachability_le base hbase hvars source target).trans
  have hN := reachabilityNodeBudget_le_square (encodeQBF base).length width
  have hB := reachabilityNameBudget_le_square (encodeQBF base).length width
  have hpos : 1 ≤ ((encodeQBF base).length + 2 * width + 1) ^ 2 := Nat.one_le_pow' _ _
  have hfactor : 2 * reachabilityNameBudget width + 4 ≤
      14 * ((encodeQBF base).length + 2 * width + 1) ^ 2 := by omega
  apply (Nat.mul_le_mul hN hfactor).trans_eq
  ring

/-- The actual closed-prenex binary target also has degree-four output growth;
this avoids unnecessarily squaring the already coarse raw-encoding bound. -/
theorem encodeTemplateReachability_length_le_poly {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    (encodeTemplateReachability base source target).length ≤
      21600 * ((encodeQBF base).length + 2 * width + 1) ^ 4 := by
  apply (encodeTemplateReachability_length_le base hbase hvars source target).trans
  have hN := reachabilityNodeBudget_le_square (encodeQBF base).length width
  have hB := reachabilityNameBudget_le_square (encodeQBF base).length width
  have hpos : 1 ≤ ((encodeQBF base).length + 2 * width + 1) ^ 2 := Nat.one_le_pow' _ _
  have hfactor : 2 * (reachabilityNameBudget width +
      reachabilityNodeBudget (encodeQBF base).length width + 1) + 4 ≤
      216 * ((encodeQBF base).length + 2 * width + 1) ^ 2 := by omega
  apply (Nat.mul_le_mul hN hfactor).trans_eq
  ring

/-- One fixed natural-coefficient polynomial for the encoded target length. -/
noncomputable def reachabilityOutputPolynomial : Polynomial ℕ :=
  21600 * (Polynomial.X + 1) ^ 4

@[simp] theorem reachabilityOutputPolynomial_eval (S : ℕ) :
    reachabilityOutputPolynomial.eval S = 21600 * (S + 1) ^ 4 := by
  simp [reachabilityOutputPolynomial]

theorem encodeTemplateReachability_length_le_eval {width : ℕ} (base : QBF)
    (hbase : base.QuantifierFree) (hvars : ∀ i ∈ base.freeVars, i < 2 * width)
    (source target : Fin width → Bool) :
    (encodeTemplateReachability base source target).length ≤
      reachabilityOutputPolynomial.eval ((encodeQBF base).length + 2 * width) := by
  simpa using encodeTemplateReachability_length_le_poly base hbase hvars source target

end IPPSPACE

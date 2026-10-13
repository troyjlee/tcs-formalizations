/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ReachabilityEncoding

/-!
# Reachability of an accepting configuration

Machines need not finish in one prescribed configuration. The construction here
existentially chooses a target satisfying a supplied Boolean acceptance formula,
while fixing the initial state and retaining one copy of the reachability body.
It proves exact semantics and polynomial node and binary-output bounds. Representing the actual
machine transition and acceptance tests, and certifying construction time,
remain separate obligations.
-/

namespace IPPSPACE

open Complexity

/-- A Boolean state supplies the first variable block; other names are false. -/
def stateBlockAssignment {width : ℕ} (state : Fin width → Bool) (i : ℕ) : Bool :=
  if hi : i < width then state ⟨i, hi⟩ else false

/-- Acceptance is the actual evaluation of a formula on one state block. -/
def templateAccepts {width : ℕ} (accept : QBF) (state : Fin width → Bool) : Prop :=
  accept.eval (stateBlockAssignment state) = true

/-- Instantiate an acceptance template at a vector of variable names. -/
def instantiateAccept {width : ℕ} (accept : QBF) (names : Fin width → ℕ) : QBF :=
  renameQBF (fun i => if hi : i < width then names ⟨i, hi⟩ else i) accept

theorem eval_instantiateAccept {width : ℕ} (accept : QBF)
    (haccept : accept.QuantifierFree) (hvars : ∀ i ∈ accept.freeVars, i < width)
    (names : Fin width → ℕ) (assignment : ℕ → Bool) :
    (instantiateAccept accept names).eval assignment = true ↔
      templateAccepts accept (assignment ∘ names) := by
  rw [instantiateAccept, eval_renameQBF_quantifierFree _ accept haccept]
  have heq := accept.eval_eq_of_agree
    (assignment ∘ (fun i => if hi : i < width then names ⟨i, hi⟩ else i))
    (stateBlockAssignment (assignment ∘ names)) (by
      intro i hi
      simp [stateBlockAssignment, hvars i hi])
  rw [heq]
  rfl

@[simp] theorem nodeCount_instantiateAccept {width : ℕ} (accept : QBF)
    (names : Fin width → ℕ) :
    nodeCount (instantiateAccept accept names) = nodeCount accept :=
  nodeCount_renameQBF _ _

/-- Fix the source and quantify over possible accepting targets. -/
def acceptingReachFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (acceptFormula : (Fin width → ℕ) → QBF) (source : Fin width → Bool) : QBF :=
  existsBlock 0 width (existsBlock width width
    (.conj (blockValues (blockNames 0 width) source)
      (.conj (acceptFormula (blockNames width width))
        (reachFormula width (stutterFormula width edgeFormula) width (2 * width)
          (blockNames 0 width) (blockNames width width)))))

/-- Exact semantics with an arbitrary final-state predicate, including acceptance
of the initial state without a transition. -/
theorem eval_acceptingReachFormula (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (hEdge : ∀ a b assignment,
      (edgeFormula a b).eval assignment = true ↔ edge (assignment ∘ a) (assignment ∘ b))
    (acceptFormula : (Fin width → ℕ) → QBF) (accepts : (Fin width → Bool) → Prop)
    (hAccept : ∀ names assignment,
      (acceptFormula names).eval assignment = true ↔ accepts (assignment ∘ names))
    (source : Fin width → Bool) (assignment : ℕ → Bool) :
    (acceptingReachFormula width edgeFormula acceptFormula source).eval assignment = true ↔
      ∃ target, accepts target ∧ Relation.ReflTransGen edge source target := by
  have hfirst : ∀ i, blockNames 0 width i < width := by
    intro i
    simp [blockNames]
  have ha : ∀ i, blockNames 0 width i < 2 * width := by
    intro i
    have := hfirst i
    omega
  have hb : ∀ i, blockNames width width i < 2 * width := by
    intro i
    have := i.isLt
    dsimp [blockNames]
    omega
  have hread (left right : Fin width → Bool) :
      writeBlock width right (writeBlock 0 left assignment) ∘ blockNames 0 width = left := by
    rw [writeBlock_comp_before _ _ _ _ hfirst, writeBlock_comp_blockNames]
  simp only [acceptingReachFormula, eval_existsBlock, QBF.eval_conj,
    Bool.and_eq_true, eval_blockValues, hAccept,
    eval_reachFormula_reachable width edgeFormula edge hEdge (2 * width) _ _ ha hb,
    hread, writeBlock_comp_blockNames]
  simp

theorem nodeCount_acceptingReachFormula_le (width : ℕ)
    (edgeFormula : (Fin width → ℕ) → (Fin width → ℕ) → QBF)
    (acceptFormula : (Fin width → ℕ) → QBF)
    (edgeSize acceptSize : ℕ)
    (hEdge : ∀ a b, nodeCount (edgeFormula a b) ≤ edgeSize)
    (hAccept : ∀ names, nodeCount (acceptFormula names) ≤ acceptSize)
    (source : Fin width → Bool) :
    nodeCount (acceptingReachFormula width edgeFormula acceptFormula source) ≤
      edgeSize + acceptSize + 15 * width + 5 + width * (43 * width + 9) := by
  have hreach := nodeCount_reachFormula_stutter_le width edgeFormula edgeSize hEdge
    (2 * width) (blockNames 0 width) (blockNames width width)
  have hsource := nodeCount_blockValues_le (blockNames 0 width) source
  have htarget := hAccept (blockNames width width)
  simp only [acceptingReachFormula, nodeCount_existsBlock, nodeCount]
  omega

/-- A closed QBF for reaching an accepting state, using actual edge and acceptance
formulas as inputs to the construction. -/
def templateAcceptingReachability {width : ℕ} (base accept : QBF)
    (source : Fin width → Bool) : QBF :=
  closeQBF (acceptingReachFormula width (instantiateEdge base) (instantiateAccept accept) source)

theorem templateAcceptingReachability_closed {width : ℕ} (base accept : QBF)
    (source : Fin width → Bool) : (templateAcceptingReachability base accept source).Closed :=
  closeQBF_closed _

theorem templateAcceptingReachability_true_iff {width : ℕ} (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (source : Fin width → Bool) :
    (templateAcceptingReachability base accept source).IsTrue ↔
      ∃ target, templateAccepts accept target ∧
        Relation.ReflTransGen (templateEdge base) source target :=
  eval_closeQBF_of_constant _ _
    (eval_acceptingReachFormula width _ _ (eval_instantiateEdge base hbase hbaseVars)
      _ _ (eval_instantiateAccept accept haccept hacceptVars) source) _

/-- Neither the transition template nor the acceptance template is duplicated. -/
theorem nodeCount_templateAcceptingReachability_le {width : ℕ} (base accept : QBF)
    (source : Fin width → Bool) :
    nodeCount (templateAcceptingReachability base accept source) ≤
      2 * (nodeCount base + nodeCount accept + 15 * width + 5 + width * (43 * width + 9)) :=
  (nodeCount_closeQBF_le _).trans (Nat.mul_le_mul_left 2
    (nodeCount_acceptingReachFormula_le width _ _ (nodeCount base) (nodeCount accept)
      (fun _ _ => (nodeCount_instantiateEdge _ _ _).le)
      (fun _ => (nodeCount_instantiateAccept _ _).le) source))

/-- A canonical input to the already analyzed prenex interactive verifier. -/
def encodeAcceptingReachability {width : ℕ} (base accept : QBF)
    (source : Fin width → Bool) : List Bool :=
  encodeQBF (toPrenex (templateAcceptingReachability base accept source)).toQBF

/-- Language membership of the generated string is exactly accepting reachability.
This statement does not certify polynomial-time production of that string. -/
theorem encodedTruePrenex_encodeAcceptingReachability_iff {width : ℕ} (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (source : Fin width → Bool) :
    EncodedTruePrenex (encodeAcceptingReachability base accept source) ↔
      ∃ target, templateAccepts accept target ∧
        Relation.ReflTransGen (templateEdge base) source target := by
  rw [encodeAcceptingReachability, encodedTruePrenex_encode_iff _
    (toPrenex_closed _ (templateAcceptingReachability_closed base accept source)),
    toPrenex_isTrue_iff]
  exact templateAcceptingReachability_true_iff base accept hbase hbaseVars haccept hacceptVars source

/-- Instantiated acceptance tests use only names from their supplied state block. -/
theorem qbfNames_instantiateAccept_lt {width : ℕ} (accept : QBF)
    (haccept : accept.QuantifierFree) (hvars : ∀ i ∈ accept.freeVars, i < width)
    (names : Fin width → ℕ) (B : ℕ) (hnames : ∀ j, names j < B) :
    ∀ i ∈ qbfNames (instantiateAccept accept names), i < B := by
  intro i hi
  rw [instantiateAccept, qbfNames_renameQBF] at hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hbound := hvars j ((qbfNames_eq_freeVars_of_quantifierFree accept haccept) ▸ hj)
  simpa [hbound] using hnames ⟨j, hbound⟩

theorem qbfNames_templateAcceptingReachability_lt {width : ℕ} (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (source : Fin width → Bool) :
    ∀ i ∈ qbfNames (templateAcceptingReachability base accept source),
      i < 2 * width + 3 * width * width := by
  have hreach := qbfNames_reachFormula_lt width (stutterFormula width (instantiateEdge base))
    (qbfNames_stutterFormula_lt width _ (qbfNames_instantiateEdge_lt base hbase hbaseVars))
    width (2 * width) (blockNames 0 width) (blockNames width width)
    (blockNames_lt_of_le _ _ _ (by omega)) (blockNames_lt_of_le _ _ _ (by omega))
  apply qbfNames_closeQBF_lt
  unfold acceptingReachFormula
  apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
  apply qbfNames_existsBlock_lt _ _ _ _ (by omega)
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact qbfNames_blockValues_lt _ source _ (blockNames_lt_of_le _ _ _ (by omega)) i hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact qbfNames_instantiateAccept_lt accept haccept hacceptVars _ _
        (blockNames_lt_of_le _ _ _ (by omega)) i hi
    · exact hreach i hi

theorem qbfMaxVar_templateAcceptingReachability_le {width : ℕ} (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (source : Fin width → Bool) :
    qbfMaxVar (templateAcceptingReachability base accept source) ≤ reachabilityNameBudget width := by
  apply qbfMaxVar_le_of_name_bound
  intro i hi
  exact (qbfNames_templateAcceptingReachability_lt base accept hbase hbaseVars
    haccept hacceptVars source i hi).le

theorem nodeCount_templateAcceptingReachability_le_budget {width : ℕ} (base accept : QBF)
    (source : Fin width → Bool) :
    nodeCount (templateAcceptingReachability base accept source) ≤
      reachabilityNodeBudget ((encodeQBF base).length + (encodeQBF accept).length) width := by
  apply (nodeCount_templateAcceptingReachability_le base accept source).trans
  unfold reachabilityNodeBudget
  have := nodeCount_le_length_encodeQBF base
  have := nodeCount_le_length_encodeQBF accept
  omega

/-- The actual prenex binary target has polynomial size in the two template
encodings and the configuration width. The construction never enumerates states. -/
theorem encodeAcceptingReachability_length_le_poly {width : ℕ} (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (source : Fin width → Bool) :
    (encodeAcceptingReachability base accept source).length ≤
      21600 * ((encodeQBF base).length + (encodeQBF accept).length + 2 * width + 1) ^ 4 := by
  let L := (encodeQBF base).length + (encodeQBF accept).length
  have hsize := length_encodeQBF_toPrenex_le_of_numeric_bounds
    (templateAcceptingReachability base accept source)
    (reachabilityNodeBudget L width) (reachabilityNameBudget width)
    (nodeCount_templateAcceptingReachability_le_budget base accept source)
    (qbfMaxVar_templateAcceptingReachability_le base accept hbase hbaseVars haccept hacceptVars source)
  apply hsize.trans
  have hN := reachabilityNodeBudget_le_square L width
  have hB := reachabilityNameBudget_le_square L width
  have hpos : 1 ≤ (L + 2 * width + 1) ^ 2 := by
    have hp : 0 < (L + 2 * width + 1) ^ 2 := by positivity
    omega
  have hfactor : 2 * (reachabilityNameBudget width + reachabilityNodeBudget L width + 1) + 4 ≤
      216 * (L + 2 * width + 1) ^ 2 := by omega
  apply (Nat.mul_le_mul hN hfactor).trans_eq
  change 100 * (L + 2 * width + 1) ^ 2 * (216 * (L + 2 * width + 1) ^ 2) =
    21600 * (L + 2 * width + 1) ^ 4
  ring

end IPPSPACE

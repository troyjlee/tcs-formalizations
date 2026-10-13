/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Renaming
import IPPSPACE.QBF.Prenex
import IPPSPACE.QBF.EncodingBounds

/-!
# Capture-safe prenex conversion

Quantifier movement is justified by explicit freshness conditions. The converter
allocates distinct bound names from one increasing counter and leaves original
free names unchanged. Its proofs concern syntax, semantics and representation
size; they do not establish a machine-time bound.
-/

namespace IPPSPACE

open Complexity

def Quantifier.index : Quantifier → ℕ
  | .ex i | .all i => i

def Quantifier.dual : Quantifier → Quantifier
  | .ex i => .all i
  | .all i => .ex i

def Quantifier.withIndex : Quantifier → ℕ → Quantifier
  | .ex _, i => .ex i
  | .all _, i => .all i

@[simp] theorem Quantifier.index_withIndex (q : Quantifier) (i : ℕ) :
    (q.withIndex i).index = i := by cases q <;> rfl

@[simp] theorem Quantifier.freeVars_bind (q : Quantifier) (φ : QBF) :
    (q.bind φ).freeVars = φ.freeVars \ {q.index} := by cases q <;> rfl

@[simp] theorem Quantifier.index_dual (q : Quantifier) : q.dual.index = q.index := by
  cases q <;> rfl

theorem prefixQBF_append (qs rs : List Quantifier) (φ : QBF) :
    prefixQBF (qs ++ rs) φ = prefixQBF qs (prefixQBF rs φ) := by
  induction qs <;> simp_all

theorem mem_freeVars_prefixQBF (qs : List Quantifier) (φ : QBF) (i : ℕ) :
    i ∈ (prefixQBF qs φ).freeVars ↔
      i ∈ φ.freeVars ∧ ∀ q ∈ qs, i ≠ q.index := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    cases q <;> simp [Quantifier.bind, QBF.freeVars, ih, Quantifier.index,
      and_left_comm, and_comm]

theorem eval_prefixQBF_congr (qs : List Quantifier) (φ ψ : QBF)
    (h : ∀ x, φ.eval x = ψ.eval x) (x : ℕ → Bool) :
    (prefixQBF qs φ).eval x = (prefixQBF qs ψ).eval x := by
  induction qs generalizing x with
  | nil => exact h x
  | cons q qs ih => cases q <;> simp [Quantifier.bind, QBF.eval, ih]

theorem eval_prefixQBF_dual_neg (qs : List Quantifier) (φ : QBF) (x : ℕ → Bool) :
    (prefixQBF (qs.map Quantifier.dual) (.neg φ)).eval x = !(prefixQBF qs φ).eval x := by
  induction qs generalizing x with
  | nil => rfl
  | cons q qs ih => cases q <;> simp [Quantifier.dual, Quantifier.bind, QBF.eval, ih]

/-- The two binary propositional connectives share the same conversion step. -/
inductive QBFConnective where
  | conj
  | disj

def QBFConnective.formula : QBFConnective → QBF → QBF → QBF
  | .conj => .conj
  | .disj => .disj

theorem QBFConnective.quantifierFree (op : QBFConnective) (φ ψ : QBF)
    (hφ : φ.QuantifierFree) (hψ : ψ.QuantifierFree) :
    (op.formula φ ψ).QuantifierFree := by
  cases op <;> simp_all [QBFConnective.formula, QBF.QuantifierFree, QBF.quantDepth]

@[simp] theorem QBFConnective.freeVars (op : QBFConnective) (φ ψ : QBF) :
    (op.formula φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by cases op <;> rfl

@[simp] theorem QBFConnective.names (op : QBFConnective) (φ ψ : QBF) :
    qbfNames (op.formula φ ψ) = qbfNames φ ∪ qbfNames ψ := by cases op <;> rfl

@[simp] theorem QBFConnective.nodeCount (op : QBFConnective) (φ ψ : QBF) :
    nodeCount (op.formula φ ψ) = nodeCount φ + nodeCount ψ + 1 := by cases op <;> rfl

theorem eval_bind_binary_left (q : Quantifier) (op : QBFConnective) (φ ψ : QBF)
    (h : q.index ∉ ψ.freeVars) (x : ℕ → Bool) :
    (q.bind (op.formula φ ψ)).eval x = (op.formula (q.bind φ) ψ).eval x := by
  cases q <;> cases op <;>
    simp only [Quantifier.bind, QBFConnective.formula, QBF.eval, Quantifier.index] at h ⊢ <;>
    rw [QBF.eval_update_not_mem x _ false ψ h, QBF.eval_update_not_mem x _ true ψ h] <;>
    cases ψ.eval x <;> simp

theorem eval_bind_binary_right (q : Quantifier) (op : QBFConnective) (φ ψ : QBF)
    (h : q.index ∉ φ.freeVars) (x : ℕ → Bool) :
    (q.bind (op.formula φ ψ)).eval x = (op.formula φ (q.bind ψ)).eval x := by
  cases q <;> cases op <;>
    simp only [Quantifier.bind, QBFConnective.formula, QBF.eval, Quantifier.index] at h ⊢ <;>
    rw [QBF.eval_update_not_mem x _ false φ h, QBF.eval_update_not_mem x _ true φ h] <;>
    cases φ.eval x <;> simp

theorem eval_prefix_binary_left (qs : List Quantifier) (op : QBFConnective) (φ ψ : QBF)
    (h : ∀ q ∈ qs, q.index ∉ ψ.freeVars) (x : ℕ → Bool) :
    (prefixQBF qs (op.formula φ ψ)).eval x = (op.formula (prefixQBF qs φ) ψ).eval x := by
  induction qs generalizing x with
  | nil => rfl
  | cons q qs ih =>
    have ht : ∀ r ∈ qs, r.index ∉ ψ.freeVars := fun r hr => h r (List.mem_cons_of_mem _ hr)
    calc
      _ = (q.bind (op.formula (prefixQBF qs φ) ψ)).eval x := by
        cases q <;> simp [Quantifier.bind, QBF.eval, ih ht]
      _ = _ := eval_bind_binary_left q op _ ψ (h q (by simp)) x

theorem eval_prefix_binary_right (qs : List Quantifier) (op : QBFConnective) (φ ψ : QBF)
    (h : ∀ q ∈ qs, q.index ∉ φ.freeVars) (x : ℕ → Bool) :
    (prefixQBF qs (op.formula φ ψ)).eval x = (op.formula φ (prefixQBF qs ψ)).eval x := by
  induction qs generalizing x with
  | nil => rfl
  | cons q qs ih =>
    have ht : ∀ r ∈ qs, r.index ∉ φ.freeVars := fun r hr => h r (List.mem_cons_of_mem _ hr)
    calc
      _ = (q.bind (op.formula φ (prefixQBF qs ψ))).eval x := by
        cases q <;> simp [Quantifier.bind, QBF.eval, ih ht]
      _ = _ := eval_bind_binary_right q op φ _ (h q (by simp)) x

theorem eval_prefix_binary_merge (qs rs : List Quantifier) (op : QBFConnective) (φ ψ : QBF)
    (hleft : ∀ q ∈ qs, q.index ∉ (prefixQBF rs ψ).freeVars)
    (hright : ∀ r ∈ rs, r.index ∉ φ.freeVars) (x : ℕ → Bool) :
    (prefixQBF (qs ++ rs) (op.formula φ ψ)).eval x =
      (op.formula (prefixQBF qs φ) (prefixQBF rs ψ)).eval x := by
  rw [prefixQBF_append]
  calc
    _ = (prefixQBF qs (op.formula φ (prefixQBF rs ψ))).eval x :=
      eval_prefixQBF_congr qs _ _ (eval_prefix_binary_right rs op φ ψ hright) x
    _ = _ := eval_prefix_binary_left qs op φ _ hleft x

theorem freeVars_prefix_dual_neg (qs : List Quantifier) (φ : QBF) :
    (prefixQBF (qs.map Quantifier.dual) (.neg φ)).freeVars = (prefixQBF qs φ).freeVars := by
  ext i
  simp [mem_freeVars_prefixQBF, QBF.freeVars]

theorem freeVars_prefix_binary_subset (qs rs : List Quantifier) (op : QBFConnective)
    (φ ψ : QBF) : (prefixQBF (qs ++ rs) (op.formula φ ψ)).freeVars ⊆
      (prefixQBF qs φ).freeVars ∪ (prefixQBF rs ψ).freeVars := by
  intro i hi
  obtain ⟨hi, hq⟩ := (mem_freeVars_prefixQBF _ _ _).mp hi
  rcases Finset.mem_union.mp (by simpa using hi) with hi | hi
  · exact Finset.mem_union_left _ ((mem_freeVars_prefixQBF _ _ _).mpr
      ⟨hi, fun q hmem => hq q (List.mem_append_left _ hmem)⟩)
  · exact Finset.mem_union_right _ ((mem_freeVars_prefixQBF _ _ _).mpr
      ⟨hi, fun q hmem => hq q (List.mem_append_right _ hmem)⟩)

theorem mem_qbfNames_prefixQBF (qs : List Quantifier) (φ : QBF) (i : ℕ) :
    i ∈ qbfNames (prefixQBF qs φ) ↔
      i ∈ qbfNames φ ∨ ∃ q ∈ qs, i = q.index := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    cases q <;> simp [Quantifier.bind, qbfNames, ih, Quantifier.index,
      or_left_comm, or_comm]

/-- A conversion result carries all invariants needed at its enclosing syntax node.
The proof fields are erased from executable code. -/
structure PrenexResult (source : QBF) (env : ℕ → ℕ) (start : ℕ) where
  formula : PrenexQBF
  next : ℕ
  next_eq : next = start + formula.quantifiers.length
  prefix_range : ∀ q ∈ formula.quantifiers, start ≤ q.index ∧ q.index < next
  matrix_bound : ∀ i ∈ qbfNames formula.matrix, i < next
  freeVars : ∀ i ∈ formula.toQBF.freeVars, ∃ j ∈ source.freeVars, env j = i
  correct : ∀ x, formula.toQBF.eval x = source.eval (x ∘ env)
  nodes : nodeCount formula.toQBF = nodeCount source

theorem PrenexResult.next_ge {φ : QBF} {env : ℕ → ℕ} {start : ℕ}
    (r : PrenexResult φ env start) : start ≤ r.next := by rw [r.next_eq]; omega

theorem PrenexResult.next_le {φ : QBF} {env : ℕ → ℕ} {start : ℕ}
    (r : PrenexResult φ env start) : r.next ≤ start + nodeCount φ := by
  have hn := r.nodes
  have he := r.next_eq
  simp only [PrenexQBF.toQBF, nodeCount_prefixQBF] at hn
  omega

theorem PrenexResult.names_bound {φ : QBF} {env : ℕ → ℕ} {start : ℕ}
    (r : PrenexResult φ env start) (i : ℕ) (hi : i ∈ qbfNames r.formula.toQBF) : i < r.next := by
  rcases (mem_qbfNames_prefixQBF _ _ _).mp hi with hi | ⟨q, hq, rfl⟩
  · exact r.matrix_bound i hi
  · exact (r.prefix_range q hq).2

def PrenexResult.neg {φ : QBF} {env : ℕ → ℕ} {start : ℕ}
    (r : PrenexResult φ env start) : PrenexResult (.neg φ) env start where
  formula := ⟨r.formula.quantifiers.map Quantifier.dual, .neg r.formula.matrix,
    r.formula.matrix_quantifierFree⟩
  next := r.next
  next_eq := by simpa using r.next_eq
  prefix_range := by
    intro q hq
    change q ∈ List.map Quantifier.dual r.formula.quantifiers at hq
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hq
    subst q
    simpa using r.prefix_range a ha
  matrix_bound := r.matrix_bound
  freeVars := by
    intro i hi
    rw [PrenexQBF.toQBF, freeVars_prefix_dual_neg] at hi
    exact r.freeVars i hi
  correct := by
    intro x
    change (prefixQBF _ _).eval x = !(φ.eval (x ∘ env))
    rw [eval_prefixQBF_dual_neg]
    exact congrArg Bool.not (r.correct x)
  nodes := by
    have hn := r.nodes
    simp only [PrenexQBF.toQBF, nodeCount_prefixQBF] at hn ⊢
    simp only [nodeCount, List.length_map]
    omega

def PrenexResult.binary {φ ψ : QBF} {env : ℕ → ℕ} {start : ℕ}
    (op : QBFConnective) (r : PrenexResult φ env start)
    (s : PrenexResult ψ env r.next)
    (hψ : ∀ i ∈ qbfNames ψ, env i < start) : PrenexResult (op.formula φ ψ) env start where
  formula := ⟨r.formula.quantifiers ++ s.formula.quantifiers,
    op.formula r.formula.matrix s.formula.matrix,
    op.quantifierFree _ _ r.formula.matrix_quantifierFree s.formula.matrix_quantifierFree⟩
  next := s.next
  next_eq := by
    simp only [List.length_append]
    have hr := r.next_eq
    have hs := s.next_eq
    omega
  prefix_range := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ⟨(r.prefix_range q hq).1, ((r.prefix_range q hq).2).trans_le s.next_ge⟩
    · exact ⟨r.next_ge.trans (s.prefix_range q hq).1, (s.prefix_range q hq).2⟩
  matrix_bound := by
    intro i hi
    rcases Finset.mem_union.mp (by simpa using hi) with hi | hi
    · exact (r.matrix_bound i hi).trans_le s.next_ge
    · exact s.matrix_bound i hi
  freeVars := by
    intro i hi
    rcases Finset.mem_union.mp (freeVars_prefix_binary_subset _ _ _ _ _ hi) with hi | hi
    · obtain ⟨j, hj, heq⟩ := r.freeVars i hi
      exact ⟨j, by simpa using Finset.mem_union_left ψ.freeVars hj, heq⟩
    · obtain ⟨j, hj, heq⟩ := s.freeVars i hi
      exact ⟨j, by simpa using Finset.mem_union_right φ.freeVars hj, heq⟩
  correct := by
    intro x
    change (prefixQBF _ _).eval x = _
    rw [eval_prefix_binary_merge]
    · cases op
      · exact congrArg₂ Bool.and (r.correct x) (s.correct x)
      · exact congrArg₂ Bool.or (r.correct x) (s.correct x)
    · intro q hq hi
      obtain ⟨j, hj, heq⟩ := s.freeVars q.index hi
      have hj' := hψ j (freeVars_subset_qbfNames ψ hj)
      have hq' := (r.prefix_range q hq).1
      omega
    · intro q hq hi
      have hi' := r.matrix_bound q.index (freeVars_subset_qbfNames _ hi)
      have hq' := (s.prefix_range q hq).1
      omega
  nodes := by
    have hr := r.nodes
    have hs := s.nodes
    simp only [PrenexQBF.toQBF, nodeCount_prefixQBF] at hr hs ⊢
    simp only [QBFConnective.nodeCount, List.length_append]
    omega

def PrenexResult.quantify {φ : QBF} {env : ℕ → ℕ} {start : ℕ}
    (q : Quantifier)
    (r : PrenexResult φ (Function.update env q.index start) (start + 1))
    (hφ : ∀ i ∈ qbfNames φ, env i < start) : PrenexResult (q.bind φ) env start where
  formula := ⟨q.withIndex start :: r.formula.quantifiers, r.formula.matrix,
    r.formula.matrix_quantifierFree⟩
  next := r.next
  next_eq := by
    have hr := r.next_eq
    simp only [List.length_cons]
    omega
  prefix_range := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · have hr := r.next_ge
      simp only [Quantifier.index_withIndex]
      exact ⟨Nat.le_refl _, by omega⟩
    · have hr := r.prefix_range a ha
      exact ⟨by omega, hr.2⟩
  matrix_bound := r.matrix_bound
  freeVars := by
    intro i hi
    change i ∈ ((q.withIndex start).bind r.formula.toQBF).freeVars at hi
    rw [Quantifier.freeVars_bind, Quantifier.index_withIndex] at hi
    obtain ⟨hi, hni⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨j, hj, heq⟩ := r.freeVars i hi
    have hne : j ≠ q.index := by
      intro he
      subst j
      simp only [Function.update_self] at heq
      exact hni (Finset.mem_singleton.mpr heq.symm)
    refine ⟨j, ?_, ?_⟩
    · rw [Quantifier.freeVars_bind]
      exact Finset.mem_sdiff.mpr ⟨hj, by simpa using hne⟩
    · simpa [Function.update_of_ne hne] using heq
  correct := by
    intro x
    have he (b : Bool) : r.formula.toQBF.eval (Function.update x start b) =
        φ.eval (Function.update (x ∘ env) q.index b) := by
      rw [r.correct]
      apply φ.eval_eq_of_agree
      intro j hj
      by_cases hji : j = q.index
      · subst j
        simp [Function.comp_def]
      · have hjn : env j ≠ start := Nat.ne_of_lt (hφ j (freeVars_subset_qbfNames φ hj))
        simp [Function.comp_def, Function.update_of_ne hji, Function.update_of_ne hjn]
    change ((q.withIndex start).bind r.formula.toQBF).eval x = (q.bind φ).eval (x ∘ env)
    cases q <;> simp [Quantifier.withIndex, Quantifier.bind, QBF.eval, he, Quantifier.index]
  nodes := by
    have hr := r.nodes
    simp only [PrenexQBF.toQBF, nodeCount_prefixQBF] at hr ⊢
    simp only [List.length_cons]
    cases q <;> simp only [Quantifier.bind, nodeCount] <;> omega

def PrenexResult.quantifierFree (φ : QBF) (hφ : φ.QuantifierFree)
    (env : ℕ → ℕ) (start : ℕ) (henv : ∀ i ∈ qbfNames φ, env i < start) :
    PrenexResult φ env start where
  formula := ⟨[], renameQBF env φ, by simpa [QBF.QuantifierFree] using hφ⟩
  next := start
  next_eq := by simp
  prefix_range := by simp
  matrix_bound := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ((qbfNames_renameQBF env φ) ▸ hi)
    exact henv j hj
  freeVars := by
    intro i hi
    have hn := freeVars_subset_qbfNames (renameQBF env φ) hi
    rw [qbfNames_renameQBF, qbfNames_eq_freeVars_of_quantifierFree φ hφ] at hn
    exact Finset.mem_image.mp hn
  correct := eval_renameQBF_quantifierFree env φ hφ
  nodes := by simp [PrenexQBF.toQBF]

/-- Structural conversion with an environment for currently bound variable names.
All environment values actually occurring in the source lie below `start`. -/
def prenexAux : (φ : QBF) → (env : ℕ → ℕ) → (start : ℕ) →
    (∀ i ∈ qbfNames φ, env i < start) → PrenexResult φ env start
  | .var i, env, start, h => PrenexResult.quantifierFree (.var i) rfl env start h
  | .tru, env, start, h => PrenexResult.quantifierFree .tru rfl env start h
  | .fls, env, start, h => PrenexResult.quantifierFree .fls rfl env start h
  | .neg φ, env, start, h => (prenexAux φ env start h).neg
  | .conj φ ψ, env, start, h =>
      let left := prenexAux φ env start (fun i hi => h i (Finset.mem_union_left _ hi))
      let hright : ∀ i ∈ qbfNames ψ, env i < start :=
        fun i hi => h i (Finset.mem_union_right _ hi)
      let right := prenexAux ψ env left.next (fun i hi => (hright i hi).trans_le left.next_ge)
      left.binary .conj right hright
  | .disj φ ψ, env, start, h =>
      let left := prenexAux φ env start (fun i hi => h i (Finset.mem_union_left _ hi))
      let hright : ∀ i ∈ qbfNames ψ, env i < start :=
        fun i hi => h i (Finset.mem_union_right _ hi)
      let right := prenexAux ψ env left.next (fun i hi => (hright i hi).trans_le left.next_ge)
      left.binary .disj right hright
  | .ex i φ, env, start, h =>
      let hbody : ∀ j ∈ qbfNames φ, env j < start :=
        fun j hj => h j (Finset.mem_insert_of_mem hj)
      let child := prenexAux φ (Function.update env i start) (start + 1) (by
        intro j hj
        by_cases hji : j = i
        · subst j; simp
        · rw [Function.update_of_ne hji]
          exact (hbody j hj).trans (Nat.lt_succ_self _))
      child.quantify (.ex i) hbody
  | .all i φ, env, start, h =>
      let hbody : ∀ j ∈ qbfNames φ, env j < start :=
        fun j hj => h j (Finset.mem_insert_of_mem hj)
      let child := prenexAux φ (Function.update env i start) (start + 1) (by
        intro j hj
        by_cases hji : j = i
        · subst j; simp
        · rw [Function.update_of_ne hji]
          exact (hbody j hj).trans (Nat.lt_succ_self _))
      child.quantify (.all i) hbody

/-- Convert any upstream QBF to prenex form while preserving free-variable names. -/
def toPrenex (φ : QBF) : PrenexQBF :=
  (prenexAux φ id (qbfMaxVar φ + 1)
    (fun i hi => Nat.lt_succ_of_le (le_qbfMaxVar_of_mem φ i hi))).formula

@[simp] theorem eval_toPrenex (φ : QBF) (x : ℕ → Bool) :
    (toPrenex φ).toQBF.eval x = φ.eval x :=
  (prenexAux φ id (qbfMaxVar φ + 1) _).correct x

@[simp] theorem nodeCount_toPrenex (φ : QBF) :
    nodeCount (toPrenex φ).toQBF = nodeCount φ :=
  (prenexAux φ id (qbfMaxVar φ + 1) _).nodes

theorem freeVars_toPrenex_subset (φ : QBF) : (toPrenex φ).toQBF.freeVars ⊆ φ.freeVars := by
  intro i hi
  obtain ⟨j, hj, heq⟩ := (prenexAux φ id (qbfMaxVar φ + 1) _).freeVars i hi
  change j = i at heq
  exact heq ▸ hj

theorem toPrenex_closed (φ : QBF) (hφ : φ.Closed) : (toPrenex φ).toQBF.Closed := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hmem := freeVars_toPrenex_subset φ hi
  simp [show φ.freeVars = ∅ from hφ] at hmem

@[simp] theorem toPrenex_isTrue_iff (φ : QBF) : (toPrenex φ).toQBF.IsTrue ↔ φ.IsTrue := by
  simp [QBF.IsTrue]

/-- The global counter introduces at most one fresh name per source syntax node. -/
theorem qbfMaxVar_toPrenex_le (φ : QBF) :
    qbfMaxVar (toPrenex φ).toQBF ≤ qbfMaxVar φ + (nodeCount φ + 1) := by
  let r := prenexAux φ id (qbfMaxVar φ + 1)
    (fun i hi => Nat.lt_succ_of_le (le_qbfMaxVar_of_mem φ i hi))
  apply qbfMaxVar_le_of_name_bound
  intro i hi
  have hname := r.names_bound i hi
  have hnext := r.next_le
  omega

/-- A quadratic bound in actual binary input length, including arbitrarily large
original variable names and all fresh binder names. This is not a time bound. -/
theorem length_encodeQBF_toPrenex_le (φ : QBF) :
    (encodeQBF (toPrenex φ).toQBF).length ≤
      (encodeQBF φ).length * (4 * (encodeQBF φ).length + 8) := by
  apply length_encodeQBF_le_quadratic φ (toPrenex φ).toQBF
  · exact Nat.le_of_eq (nodeCount_toPrenex φ)
  · exact qbfMaxVar_toPrenex_le φ

end IPPSPACE

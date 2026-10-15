import Toda.Counting.AmplificationChoices.Defs
import Toda.Counting.AmplificationIndexing.Encoding

/-!
# Uniform lookup in amplification trees

The preorder cursor follows at most one edge per tree level. Its encoded
state has polynomial unary size, and the actual FP loop agrees with the
recursive activity and leaf predicates on every valid node index.
-/

namespace Toda.Counting.AmplificationIndexing

open Complexity AmplificationChoices

def activityCode (active : Bool) : ℕ := if active then 1 else 0

theorem activityCode_lt (active : Bool) : activityCode active < 2 := by
  cases active <;> decide

theorem cursorStep_descend {base k i offset : ℕ} (bits : List Bool) (active : Bool)
    (hb : nodeCount (k + 1) < base) (hi : i < nodeCount (k + 1)) (hz : i ≠ 0) :
    cursorStep base bits (offset + i)
      (encode base (nodeCount (k + 1)) i (activityCode active)) =
    encode base (nodeCount k) ((i - 1) % nodeCount k)
      (activityCode (active && (decide ((i - 1) / nodeCount k < 2) ||
        bits[offset]?.getD false))) := by
  have hbpos : 0 < base := lt_trans (nodeCount_pos _) hb
  have hip : i < base := lt_trans hi hb
  have hks : nodeCount k < base := by rw [nodeCount_succ] at hb; omega
  have hrem : (i - 1) % nodeCount k < base :=
    lt_trans (Nat.mod_lt _ (nodeCount_pos k)) hks
  have hdiv : (nodeCount (k + 1) - 1) / 3 = nodeCount k := by
    simp [nodeCount_succ]
  simp only [cursorStep, cursorSize_encode hbpos hip (activityCode_lt active),
    cursorPosition_encode hip (activityCode_lt active),
    cursorActive_encode (activityCode_lt active), hdiv, hz, ↓reduceIte,
    Nat.add_sub_cancel]
  have hact : (if activityCode active = 1 ∧
      ((i - 1) / nodeCount k < 2 ∨ bits[offset]?.getD false = true) then 1 else 0) =
      activityCode (active && (decide ((i - 1) / nodeCount k < 2) ||
        bits[offset]?.getD false)) := by
    cases active <;> cases hbit : bits[offset]?.getD false <;>
      by_cases hchild : (i - 1) / nodeCount k < 2 <;>
      simp [activityCode, hchild]
  rw [hact, Nat.mod_eq_of_lt
    (encode_lt_capacity hbpos hks hrem (activityCode_lt _))]

/-- The bounded cursor has exactly the recursive activity and leaf semantics. -/
theorem cursor_iterate_correct (k : ℕ) {base i offset : ℕ}
    (bits : List Bool) (active : Bool) (hb : nodeCount k < base)
    (hi : i < nodeCount k) :
    cursorActive ((cursorStep base bits (offset + i))^[k]
      (encode base (nodeCount k) i (activityCode active))) =
        activityCode (nodeActive k active (bits.drop offset) i) ∧
    (cursorSize base ((cursorStep base bits (offset + i))^[k]
      (encode base (nodeCount k) i (activityCode active))) = 1 ↔ nodeLeaf k i = true) := by
  induction k generalizing base i offset active with
  | zero =>
      have hbpos : 0 < base := by simp only [nodeCount_zero] at hb; omega
      have hip : i < base := lt_trans hi hb
      simp only [Function.iterate_zero, id_eq,
        cursorActive_encode (activityCode_lt active), nodeActive,
        cursorSize_encode hbpos hip (activityCode_lt active), nodeCount_zero, nodeLeaf,
        and_self, iff_self]
  | succ k ih =>
      have hbpos : 0 < base := lt_trans (nodeCount_pos _) hb
      by_cases hz : i = 0
      · subst i
        have hfix : cursorStep base bits (offset + 0)
            (encode base (nodeCount (k + 1)) 0 (activityCode active)) =
            encode base (nodeCount (k + 1)) 0 (activityCode active) :=
          cursorStep_fixed hbpos hb (activityCode_lt active) bits (offset + 0)
        simp only [Function.iterate_fixed hfix]
        simp only [cursorActive_encode (activityCode_lt active), nodeActive,
          ↓reduceIte, cursorSize_encode hbpos hbpos (activityCode_lt active), nodeLeaf]
        have hn := nodeCount_pos k
        simp only [nodeCount_succ, Bool.false_eq_true, iff_false, true_and]
        omega
      · rw [Function.iterate_succ_apply,
          cursorStep_descend bits active hb hi hz]
        let child := (i - 1) / nodeCount k
        let rel := (i - 1) % nodeCount k
        let shift := 1 + child * nodeCount k
        let nextActive := active && (decide (child < 2) || bits[offset]?.getD false)
        have hks : nodeCount k < base := by rw [nodeCount_succ] at hb; omega
        have hir : rel < nodeCount k := Nat.mod_lt _ (nodeCount_pos k)
        have hsplit : offset + i = (offset + shift) + rel := by
          have hdm := Nat.mod_add_div (i - 1) (nodeCount k)
          rw [Nat.mul_comm (nodeCount k)] at hdm
          dsimp [shift, child, rel]
          omega
        have hc := ih (base := base) (i := rel) (offset := offset + shift)
          nextActive hks hir
        rw [hsplit]
        convert hc using 1 <;>
          simp [nodeActive, nodeLeaf, hz, rel, nextActive, child, shift,
            List.getElem?_drop, List.drop_drop, Nat.add_comm]

theorem cursorRun_correct (k : ℕ) (bits : List Bool) (i : ℕ)
    (hi : i < nodeCount k) :
    cursorActive (cursorRun (nodeCount k) k bits i) =
      activityCode (nodeActive k true bits i) ∧
    (cursorSize (nodeCount k + 1) (cursorRun (nodeCount k) k bits i) = 1 ↔
      nodeLeaf k i = true) := by
  have hc := cursor_iterate_correct k (base := nodeCount k + 1)
    (i := i) (offset := 0) bits true (by omega) hi
  simpa [cursorRun, cursorStart, Nat.min_eq_left (Nat.le_of_lt hi), activityCode] using hc

theorem nodeActive_fppred {k i : List Bool → ℕ} {bits : List Bool → List Bool}
    (hn : UnaryFn fun x => nodeCount (k x)) (hk : UnaryFn k)
    (hi : UnaryFn i) (hb : bits ∈ FP) :
    FPPred fun x => i x < nodeCount (k x) ∧ nodeActive (k x) true (bits x) (i x) = true := by
  apply ((FPPred.lt hi hn).and (cursorRun_active_fppred hn hk hi hb)).of_iff
  intro x
  by_cases h : i x < nodeCount (k x)
  · rw [(cursorRun_correct (k x) (bits x) (i x) h).1]
    cases nodeActive (k x) true (bits x) (i x) <;> simp [activityCode]
  · simp [h]

theorem nodeLeaf_fppred {k i : List Bool → ℕ} {bits : List Bool → List Bool}
    (hn : UnaryFn fun x => nodeCount (k x)) (hk : UnaryFn k)
    (hi : UnaryFn i) (hb : bits ∈ FP) :
    FPPred fun x => i x < nodeCount (k x) ∧ nodeLeaf (k x) (i x) = true := by
  apply ((FPPred.lt hi hn).and (cursorRun_leaf_fppred hn hk hi hb)).of_iff
  intro x
  by_cases h : i x < nodeCount (k x)
  · rw [(cursorRun_correct (k x) (bits x) (i x) h).2]
  · simp [h]

end Toda.Counting.AmplificationIndexing

import Toda.Arithmetic.Amplification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact signed choices for a complete ternary amplification tree

Each node has one choice bit. Inactive nodes, and active leaves, require a
false bit. This canonical padding makes an inactive subtree contribute one.
The tree is stored in preorder, with three contiguous child blocks.
-/

namespace Toda.Counting.AmplificationChoices

open scoped BigOperators

/-- All nodes, including the leaves, of the complete ternary tree. -/
def nodeCount : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + 3 * nodeCount k

@[simp] theorem nodeCount_zero : nodeCount 0 = 1 := rfl
@[simp] theorem nodeCount_succ (k : ℕ) : nodeCount (k + 1) = 1 + 3 * nodeCount k := rfl

theorem nodeCount_pos (k : ℕ) : 0 < nodeCount k := by cases k <;> simp [nodeCount]

theorem nodeCount_arithmetic (k : ℕ) : 2 * nodeCount k + 1 = 3 ^ (k + 1) := by
  induction k with
  | zero => norm_num [nodeCount]
  | succ k ih => rw [nodeCount_succ, pow_succ]; omega

/-- Whether the given preorder node is active under the chosen pruning bits. -/
def nodeActive : ℕ → Bool → List Bool → ℕ → Bool
  | 0, active, _, _ => active
  | k + 1, active, bits, i =>
      if i = 0 then active else
        nodeActive k (active && (decide ((i - 1) / nodeCount k < 2) ||
          bits[0]?.getD false))
          (bits.drop (1 + ((i - 1) / nodeCount k) * nodeCount k))
          ((i - 1) % nodeCount k)

/-- Whether the given preorder node is a leaf. -/
def nodeLeaf : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, i => if i = 0 then false else nodeLeaf k ((i - 1) % nodeCount k)

/-- A single signed factor. Every bit on an inactive node is forced false. -/
def localFactor (k : ℕ) (active : Bool) (m : ℤ) (bits : List Bool) (i : ℕ) : ℤ :=
  if nodeActive k active bits i then
    if nodeLeaf k i then (if bits[i]?.getD false then 0 else m)
    else (if bits[i]?.getD false then -2 else 3)
  else (if bits[i]?.getD false then 0 else 1)

/-- The root factor at an internal node. -/
def rootFactor (active bit : Bool) : ℤ :=
  if active then (if bit then -2 else 3) else (if bit then 0 else 1)

@[simp] theorem localFactor_root (k : ℕ) (active : Bool) (m : ℤ) (bits : List Bool) :
    localFactor (k + 1) active m bits 0 = rootFactor active (bits[0]?.getD false) := by
  simp [localFactor, nodeActive, nodeLeaf, rootFactor]

/-- The child block index and its local offset recover exactly. -/
theorem child_index {n : ℕ} (hn : 0 < n) (j : ℕ) (i : Fin n) :
    (1 + j * n + i.val - 1) / n = j ∧
      (1 + j * n + i.val - 1) % n = i.val := by
  have hsub : 1 + j * n + i.val - 1 = i.val + n * j := by simp only [Nat.mul_comm n j]; omega
  rw [hsub, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.isLt,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  simp

/-- A local factor in a child block agrees with its smaller-tree factor. -/
theorem localFactor_child (k : ℕ) (active : Bool) (m : ℤ) (bits : List Bool)
    (j : ℕ) (i : Fin (nodeCount k)) :
    localFactor (k + 1) active m bits (1 + j * nodeCount k + i.val) =
      localFactor k (active && (decide (j < 2) || bits[0]?.getD false)) m
        (bits.drop (1 + j * nodeCount k)) i.val := by
  obtain ⟨hdiv, hmod⟩ := child_index (nodeCount_pos k) j i
  simp [localFactor, nodeActive, nodeLeaf, hdiv, hmod, List.getElem?_drop]

end Toda.Counting.AmplificationChoices

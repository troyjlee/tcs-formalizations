import Toda.Counting.AmplificationIndexing.Cursor

/-!
# Exact coordinates of the bounded preorder cursor

The arithmetic encoding has no collisions on valid coordinates. Its
polynomial capacity does not truncate a valid state, and a cursor that has
reached its target remains there.
-/

namespace Toda.Counting.AmplificationIndexing

theorem encode_div_two {base size position active : ℕ} (ha : active < 2) :
    encode base size position active / 2 = base * size + position := by
  unfold encode
  omega

@[simp] theorem cursorSize_encode {base size position active : ℕ}
    (hb : 0 < base) (hp : position < base) (ha : active < 2) :
    cursorSize base (encode base size position active) = size := by
  rw [cursorSize, encode_div_two ha]
  rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hp]
  omega

@[simp] theorem cursorPosition_encode {base size position active : ℕ}
    (hp : position < base) (ha : active < 2) :
    cursorPosition base (encode base size position active) = position := by
  rw [cursorPosition, encode_div_two ha]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp]

@[simp] theorem cursorActive_encode {base size position active : ℕ}
    (ha : active < 2) : cursorActive (encode base size position active) = active := by
  unfold cursorActive encode
  omega

/-- Reaching relative position zero makes the bounded transition stationary. -/
theorem cursorStep_fixed {base size active : ℕ} (hb : 0 < base)
    (hs : size < base) (ha : active < 2) (bits : List Bool) (index : ℕ) :
    cursorStep base bits index (encode base size 0 active) =
      encode base size 0 active := by
  simp only [cursorStep, cursorPosition_encode hb ha, ite_true]
  exact Nat.mod_eq_of_lt (encode_lt_capacity hb hs hb ha)

/-- A valid state at the target stays fixed under any further iteration. -/
theorem iterate_cursorStep_fixed {base size active : ℕ} (hb : 0 < base)
    (hs : size < base) (ha : active < 2) (bits : List Bool) (index steps : ℕ) :
    (cursorStep base bits index)^[steps] (encode base size 0 active) =
      encode base size 0 active := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', ih, cursorStep_fixed hb hs ha]

end Toda.Counting.AmplificationIndexing

import Complexitylib.Classes.P.StringAccess

/-!
# A bounded, polynomial-time preorder cursor

The cursor stores the current subtree size, the index inside that subtree,
and an activity bit. Its state is a unary number of quadratic size in the
tree size. The input position minus the current relative index is the root
position of the current subtree.
-/

namespace Toda.Counting.AmplificationIndexing

open Complexity

def encode (base size position active : ℕ) : ℕ :=
  2 * (base * size + position) + active

def cursorSize (base state : ℕ) : ℕ := state / 2 / base
def cursorPosition (base state : ℕ) : ℕ := state / 2 % base
def cursorActive (state : ℕ) : ℕ := state % 2

def capacity (base : ℕ) : ℕ := 2 * base ^ 2

def cursorStep (base : ℕ) (bits : List Bool) (index state : ℕ) : ℕ :=
  let size := cursorSize base state
  let position := cursorPosition base state
  let childSize := (size - 1) / 3
  let child := (position - 1) / childSize
  let active := if cursorActive state = 1 ∧
      (child < 2 ∨ bits[index - position]?.getD false = true) then 1 else 0
  (if position = 0 then state
   else encode base childSize ((position - 1) % childSize) active) % capacity base

def cursorStart (nodes index : ℕ) : ℕ :=
  encode (nodes + 1) nodes (min index nodes) 1

def cursorRun (nodes steps : ℕ) (bits : List Bool) (index : ℕ) : ℕ :=
  (cursorStep (nodes + 1) bits index)^[steps] (cursorStart nodes index)

theorem encode_lt_capacity {base size position active : ℕ}
    (hb : 0 < base) (hs : size < base) (hp : position < base) (ha : active < 2) :
    encode base size position active < capacity base := by
  unfold encode capacity
  have hmul : base * size ≤ base * (base - 1) := Nat.mul_le_mul_left base (by omega)
  have hbmul : base * (base - 1) = base ^ 2 - base := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_two]
  have : base ≤ base ^ 2 := by nlinarith
  rw [hbmul] at hmul
  omega

theorem cursorStart_lt_capacity (nodes index : ℕ) :
    cursorStart nodes index < capacity (nodes + 1) :=
  encode_lt_capacity (by omega) (by omega) (by have := Nat.min_le_right index nodes; omega)
    (by omega)

theorem cursorRun_lt_capacity (nodes steps : ℕ) (bits : List Bool) (index : ℕ) :
    cursorRun nodes steps bits index < capacity (nodes + 1) := by
  induction steps with
  | zero => exact cursorStart_lt_capacity nodes index
  | succ steps ih =>
      rw [cursorRun, Function.iterate_succ_apply']
      exact Nat.mod_lt _ (by unfold capacity; positivity)

theorem cursorRun_unary {nodes steps index : List Bool → ℕ}
    {bits : List Bool → List Bool} (hn : UnaryFn nodes) (hk : UnaryFn steps)
    (hi : UnaryFn index) (hb : bits ∈ FP) :
    UnaryFn fun x => cursorRun (nodes x) (steps x) (bits x) (index x) := by
  have hbase : UnaryFn fun x => nodes x + 1 := hn.add (UnaryFn.const 1)
  have hcap : UnaryFn fun x => capacity (nodes x + 1) :=
    (UnaryFn.const 2).mul (hbase.pow_const 2)
  have hstart : UnaryFn fun x => cursorStart (nodes x) (index x) :=
    ((UnaryFn.const 2).mul ((hbase.mul hn).add (hi.min hn))).add (UnaryFn.const 1)
  have hs : UnaryFn fun w => cursorSize (nodes (pairFst w) + 1) (pairSnd w).length :=
    (UnaryFn.index.div (UnaryFn.const 2)).div hbase.lift
  have hp : UnaryFn fun w => cursorPosition (nodes (pairFst w) + 1) (pairSnd w).length :=
    (UnaryFn.index.div (UnaryFn.const 2)).mod hbase.lift
  have ht : UnaryFn fun w =>
      (cursorSize (nodes (pairFst w) + 1) (pairSnd w).length - 1) / 3 :=
    (hs.sub (UnaryFn.const 1)).div (UnaryFn.const 3)
  have hc : UnaryFn fun w =>
      (cursorPosition (nodes (pairFst w) + 1) (pairSnd w).length - 1) /
        ((cursorSize (nodes (pairFst w) + 1) (pairSnd w).length - 1) / 3) :=
    (hp.sub (UnaryFn.const 1)).div ht
  have hread : FPPred fun w =>
      (bits (pairFst w))[index (pairFst w) -
        cursorPosition (nodes (pairFst w) + 1) (pairSnd w).length]?.getD false = true :=
    FPPred.getBit (mem_FP_comp Cobham.fstBlock_mem_FP hb) (hi.lift.sub hp)
  have ha : UnaryFn fun w =>
      if cursorActive (pairSnd w).length = 1 ∧
          ( (cursorPosition (nodes (pairFst w) + 1) (pairSnd w).length - 1) /
              ((cursorSize (nodes (pairFst w) + 1) (pairSnd w).length - 1) / 3) < 2 ∨
            (bits (pairFst w))[index (pairFst w) -
              cursorPosition (nodes (pairFst w) + 1) (pairSnd w).length]?.getD false = true)
        then 1 else 0 :=
    UnaryFn.ite
      ((FPPred.eq (UnaryFn.index.mod (UnaryFn.const 2)) (UnaryFn.const 1)).and
        ((FPPred.lt hc (UnaryFn.const 2)).or hread))
      (UnaryFn.const 1) (UnaryFn.const 0)
  have hstep : UnaryFn fun w => cursorStep (nodes (pairFst w) + 1)
      (bits (pairFst w)) (index (pairFst w)) (pairSnd w).length :=
    (UnaryFn.ite (FPPred.eq hp (UnaryFn.const 0)) UnaryFn.index
      (((UnaryFn.const 2).mul ((hbase.lift.mul ht).add
        ((hp.sub (UnaryFn.const 1)).mod ht))).add ha)).mod hcap.lift
  exact UnaryFn.iterate hstep hstart hk hcap fun x j _ =>
    Nat.le_of_lt (cursorRun_lt_capacity (nodes x) j (bits x) (index x))

theorem cursorRun_active_fppred {nodes steps index : List Bool → ℕ}
    {bits : List Bool → List Bool} (hn : UnaryFn nodes) (hk : UnaryFn steps)
    (hi : UnaryFn index) (hb : bits ∈ FP) :
    FPPred fun x => cursorActive (cursorRun (nodes x) (steps x) (bits x) (index x)) = 1 :=
  FPPred.eq ((cursorRun_unary hn hk hi hb).mod (UnaryFn.const 2)) (UnaryFn.const 1)

theorem cursorRun_leaf_fppred {nodes steps index : List Bool → ℕ}
    {bits : List Bool → List Bool} (hn : UnaryFn nodes) (hk : UnaryFn steps)
    (hi : UnaryFn index) (hb : bits ∈ FP) :
    FPPred fun x => cursorSize (nodes x + 1)
      (cursorRun (nodes x) (steps x) (bits x) (index x)) = 1 :=
  FPPred.eq (((cursorRun_unary hn hk hi hb).div (UnaryFn.const 2)).div
    (hn.add (UnaryFn.const 1))) (UnaryFn.const 1)

end Toda.Counting.AmplificationIndexing

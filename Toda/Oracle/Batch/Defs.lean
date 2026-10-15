import Toda.Oracle.Batch.Codec

/-! # A streaming batch-query oracle machine -/

namespace Toda.Oracle.Batch

open Complexity

inductive Phase where
  | boot | tag | data | query | yes | no | rewind | halt
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.boot, .tag, .data, .query, .yes, .no, .rewind, .halt}
  complete := by intro q; cases q <;> simp

def binary (symbol : Γ) : Bool := symbol = .zero || symbol = .one

def transition (q : Phase) (inp query out : Γ) : OracleLocalTransition 0 Phase where
  nextState := match q with
    | .boot => .tag
    | .tag => if inp = .one then .data else if inp = .zero then .query else .halt
    | .data => if binary inp then .tag else .halt
    | .query => .query
    | .yes | .no => .rewind
    | .rewind => if query = .start then .tag else .rewind
    | .halt => .halt
  queryWrite := if q = .data then TM.readBackWrite inp else TM.readBackWrite query
  workWrites := fun _ => .blank
  outputWrite := if q = .yes then .one else if q = .no then .zero else .blank
  inputDir := if q = .boot ∨ ((q = .tag ∨ q = .data) ∧ binary inp) then .right
    else TM.idleDir inp
  queryDir := if q = .boot ∨ (q = .data ∧ binary inp) then .right else
    if q = .rewind then (if query = .start then .right else .left) else TM.idleDir query
  workDirs := fun _ => .right
  outputDir := if q = .yes ∨ q = .no then .right else TM.idleDir out

/-- A constant-state, zero-work-tape machine evaluates a stream of queries. -/
def machine : OracleTM 0 where
  Q := Phase
  qstart := .boot
  qhalt := .halt
  queryTransition := fun q => if q = .query then some (.yes, .no) else none
  localTransition := fun q inp query _ out => transition q inp query out
  localTransition_right_of_start := by
    intro q inp query work out
    refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
    · intro h; subst inp; cases q <;> simp [transition, binary, TM.idleDir]
    · intro h; subst query; cases q <;> simp [transition, binary, TM.idleDir]
    · intro h; subst out; cases q <;> simp [transition, TM.idleDir]

/-- Only cells before the query head matter; stale cells after it are allowed. -/
def QueryPrefix (t : Tape) (bits : List Bool) : Prop :=
  t.head = bits.length + 1 ∧
    ∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)

theorem QueryPrefix.oracleQuery {t : Tape} {bits : List Bool}
    (h : QueryPrefix t bits) : t.oracleQuery = bits := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i hi hj
    simp only [Tape.oracleQuery, List.getElem_ofFn]
    rw [h.2 i hj]
    cases bits[i] <;> rfl

theorem QueryPrefix.write_bit {t : Tape} {bits : List Bool}
    (h : QueryPrefix t bits) (bit : Bool) :
    QueryPrefix (t.writeAndMove (Γ.ofBool bit) .right) (bits ++ [bit]) := by
  refine ⟨by simp [Tape.move, Tape.write_head, h.1], ?_⟩
  intro i hi
  have hh : t.head ≠ 0 := by rw [h.1]; omega
  simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, hh, ↓reduceIte]
  by_cases heq : i = bits.length
  · subst i
    simp [h.1]
  · have hlt : i < bits.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    rw [Function.update_of_ne (by rw [h.1]; omega), h.2 i hlt,
      List.getElem_append_left hlt]

theorem query_idle {query : Tape} (hi : query.StartInvariant) {bits : List Bool}
    (hq : QueryPrefix query bits) : TM.transitionTape query = query :=
  TM.transitionTape_eq_self (hi.read_ne_start (by rw [hq.1]; omega))

theorem output_idle {output : Tape} {bits : List Bool}
    (h : output.HasBinaryPrefix bits) :
    output.writeAndMove Γ.blank (TM.idleDir output.read) = output := by
  have hr := h.read_blank
  simpa [TM.transitionTape, hr, TM.readBackWrite] using
    TM.transitionTape_eq_self (t := output) (by simp [hr])

theorem output_write_blank {output : Tape} {bits : List Bool}
    (h : output.HasBinaryPrefix bits) : output.write Γ.blank = output := by
  simpa [TM.idleDir, h.read_blank, Tape.move] using output_idle h

end Toda.Oracle.Batch

import Toda.Counting.CanonicalWitness
import Mathlib.Data.Fintype.Sum

/-!
# A deterministic verifier for prepared canonical witnesses

The verifier uses one extra work tape containing the witness. It simulates one
nondeterministic transition for each bit until the source halts, then requires
every remaining bit to be false. Finally it returns to output cell one and
writes the Boolean verdict. Statements about prepared configurations do not
assert that an ordinary input has already been split and loaded onto the tapes.
-/

namespace Toda.Counting.CanonicalVerifier

open Complexity

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- Source states, output-reset states, verdict-writing states, and a halt state. -/
abbrev State (N : NTM n) := Sum N.Q (Sum Bool (Sum Bool Unit))

abbrev seek (N : NTM n) (allow : Bool) : State N := .inr (.inl allow)
abbrev finish (N : NTM n) (allow : Bool) : State N := .inr (.inr (.inl allow))
abbrev stop (N : NTM n) : State N := .inr (.inr (.inr ()))

private def keepSymbol : Γ → Γw
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

private theorem write_keepSymbol (t : Tape) (hi : t.StartInvariant) :
    t.write (keepSymbol t.read).toΓ = t := by
  by_cases hh : t.head = 0
  · simp [Tape.write, hh]
  · have hr := hi.read_ne_start (by omega : 1 ≤ t.head)
    have heq : (keepSymbol t.read).toΓ = t.read := by
      cases h : t.read <;> simp_all [keepSymbol, Γw.toΓ]
    rw [heq]
    simp [Tape.write, hh, Tape.read]

private def auxiliaryDelta (N : NTM n) (q : State N) (o : Γ) (d : Dir3) :
    State N × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  (q, fun _ => .blank, keepSymbol o, .right, fun _ => .right, d)

private def delta (N : NTM n) (q : State N) (i : Γ)
    (w : Fin (n + 1) → Γ) (o : Γ) :
    State N × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  match q with
  | .inl q =>
      if q = N.qhalt then
        if w (Fin.last n) = .zero then auxiliaryDelta N (.inl q) o .right
        else auxiliaryDelta N (seek N (decide (w (Fin.last n) = .blank))) o .right
      else if w (Fin.last n) = .zero ∨ w (Fin.last n) = .one then
        let r := N.δ (decide (w (Fin.last n) = .one)) q i
          (fun j => w j.castSucc) o
        (.inl r.1, Fin.snoc r.2.1 .blank, r.2.2.1, r.2.2.2.1,
          Fin.snoc r.2.2.2.2.1 .right, r.2.2.2.2.2)
      else auxiliaryDelta N (seek N false) o .right
  | .inr (.inl allow) =>
      if o = .start then auxiliaryDelta N (finish N allow) o .right
      else auxiliaryDelta N (seek N allow) o .left
  | .inr (.inr (.inl allow)) =>
      (stop N, fun _ => .blank, if allow && decide (o = .one) then .one else .zero,
        .right, fun _ => .right, .right)
  | .inr (.inr (.inr _)) => auxiliaryDelta N (stop N) o .right

/-- An actual deterministic TM, with the witness on its final work tape. -/
def machine (N : NTM n) : TM (n + 1) where
  Q := State N
  qstart := .inl N.qstart
  qhalt := stop N
  δ := delta N
  δ_right_of_start := by
    intro q i w o
    rcases q with q | (allow | (allow | u))
    · by_cases hq : q = N.qhalt
      · by_cases hw : w (Fin.last n) = .zero <;>
          simp [delta, auxiliaryDelta, hq, hw]
      · by_cases hw : w (Fin.last n) = .zero ∨ w (Fin.last n) = .one
        · have h := N.δ_right_of_start (decide (w (Fin.last n) = .one)) q i
            (fun j => w j.castSucc) o
          simp only [delta, hq, ite_false, hw, ite_true]
          refine ⟨h.1, ?_, h.2.2⟩
          intro j
          refine Fin.lastCases ?_ ?_ j
          · simp
          · intro j hj
            simpa using h.2.1 j hj
        · simp [delta, auxiliaryDelta, hq, hw]
    · by_cases ho : o = .start <;> simp [delta, auxiliaryDelta, ho]
    · simp [delta]
    · simp [delta, auxiliaryDelta]

/-- The witness head advances one cell after consuming the current symbol. -/
def advanceChoice (t : Tape) : Tape := (t.write Γ.blank).move .right

/-- Place a source configuration and an already-loaded witness tape together. -/
def embed (N : NTM n) (c : Cfg n N.Q) (witness : Tape) : Cfg (n + 1) (machine N).Q where
  state := .inl c.state
  input := c.input
  work := Fin.snoc c.work witness
  output := c.output

/-- A finite binary suffix followed immediately by a blank, under the head. -/
def HasChoices (t : Tape) (bits : List Bool) : Prop :=
  1 ≤ t.head ∧
  (∀ j (hj : j < bits.length), t.cells (t.head + j) = Γ.ofBool bits[j]) ∧
  t.cells (t.head + bits.length) = .blank

theorem hasChoices_nil_read (t : Tape) (h : HasChoices t []) : t.read = .blank := by
  simpa [Tape.read] using h.2.2

theorem hasChoices_cons_read (t : Tape) (b : Bool) (bits : List Bool)
    (h : HasChoices t (b :: bits)) : t.read = Γ.ofBool b := by
  simpa [Tape.read] using h.2.1 0 (by simp)

theorem hasChoices_advance (t : Tape) (b : Bool) (bits : List Bool)
    (h : HasChoices t (b :: bits)) : HasChoices (advanceChoice t) bits := by
  have hh : t.head ≠ 0 := by have := h.1; omega
  refine ⟨by simp [advanceChoice, Tape.move, Tape.write_head], ?_, ?_⟩
  · intro j hj
    have hj' := h.2.1 (j + 1) (by simpa using hj)
    have hne : t.head + 1 + j ≠ t.head := by omega
    simpa [advanceChoice, Tape.move, Tape.write, hh, hne,
      Nat.add_assoc, Nat.add_comm 1 j] using hj'
  · have hne : t.head + 1 + bits.length ≠ t.head := by omega
    simpa [advanceChoice, Tape.move, Tape.write, hh, hne,
      Nat.add_assoc, Nat.add_comm 1 bits.length] using h.2.2

/-- The standard prepared witness tape starts at the first bit, not its marker. -/
def witnessTape (bits : List Bool) : Tape := (Tape.init (bits.map Γ.ofBool)).move .right

theorem witnessTape_hasChoices (bits : List Bool) : HasChoices (witnessTape bits) bits := by
  refine ⟨by simp [witnessTape, Tape.move], ?_, ?_⟩
  · intro j hj
    simpa [witnessTape, Tape.move, Nat.add_comm] using Tape.init_ofBool_cells_lt bits j hj
  · simpa [witnessTape, Tape.move, Nat.add_comm] using
      Tape.init_ofBool_cells_ge bits bits.length le_rfl

private def auxiliaryCfg (N : NTM n) (q : State N) (d : Dir3)
    (c : Cfg (n + 1) (machine N).Q) : Cfg (n + 1) (machine N).Q where
  state := q
  input := c.input.move .right
  work := fun j => (c.work j).writeAndMove Γ.blank .right
  output := c.output.move d

private theorem step_auxiliary (N : NTM n) (c : Cfg (n + 1) (machine N).Q)
    (q : State N) (d : Dir3) (hs : c.state ≠ stop N) (hi : c.output.StartInvariant)
    (hd : delta N c.state c.input.read (fun j => (c.work j).read) c.output.read =
      auxiliaryDelta N q c.output.read d) :
    (machine N).step c = some (auxiliaryCfg N q d c) := by
  simp only [TM.step, machine, hs, ite_false, hd, auxiliaryDelta]
  rw [show c.output.writeAndMove (keepSymbol c.output.read).toΓ d = c.output.move d by
    exact congrArg (fun t => t.move d) (write_keepSymbol c.output hi)]
  rfl

private theorem finish_step (N : NTM n) (allow : Bool)
    (c : Cfg (n + 1) (machine N).Q) (hs : c.state = finish N allow)
    (hh : c.output.head = 1) :
    ∃ c', (machine N).step c = some c' ∧ (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (allow && decide (c.output.cells 1 = .one)) := by
  let verdict := allow && decide (c.output.cells 1 = .one)
  let c' : Cfg (n + 1) (machine N).Q :=
    { state := stop N
      input := c.input.move .right
      work := fun j => (c.work j).writeAndMove Γ.blank .right
      output := c.output.writeAndMove (Γw.ofBool verdict).toΓ .right }
  refine ⟨c', ?_, rfl, ?_⟩
  · cases allow <;> by_cases ho : c.output.cells 1 = Γ.one <;>
      simp [TM.step, machine, delta, hs, finish, stop, Tape.read, hh, c', verdict,
        ho, Γw.ofBool]
  · simp only [c', Tape.writeAndMove, Tape.move, Tape.write, hh,
      show ¬(1 : ℕ) = 0 by decide, ite_false, Function.update_self]
    exact Γw.ofBool_toΓ verdict

/-- Resetting the output head and writing a normalized verdict takes exactly
`head + 2` transitions. The `allow` flag can force rejection. -/
theorem seek_reaches_halt (N : NTM n) (allow : Bool) (k : ℕ)
    (c : Cfg (n + 1) (machine N).Q) (hs : c.state = seek N allow)
    (hi : c.output.StartInvariant) (hk : c.output.head = k) :
    ∃ c', (machine N).reachesIn (k + 2) c c' ∧ (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (allow && decide (c.output.cells 1 = .one)) := by
  induction k generalizing c with
  | zero =>
    have hr : c.output.read = .start := by simpa [Tape.read, hk] using hi.1
    let c₁ := auxiliaryCfg N (finish N allow) .right c
    have hstep : (machine N).step c = some c₁ :=
      step_auxiliary N c _ _ (by rw [hs]; intro h; cases h) hi
        (by simp [delta, hs, seek, hr])
    obtain ⟨c₂, hstep₂, hhalt, hout⟩ := finish_step N allow c₁ rfl
      (by simp [c₁, auxiliaryCfg, Tape.move, hk])
    refine ⟨c₂, TM.reachesIn.step hstep (TM.reachesIn.step hstep₂ TM.reachesIn.zero),
      hhalt, ?_⟩
    exact hout
  | succ k ih =>
    have hr : c.output.read ≠ .start := hi.read_ne_start (by omega)
    let c₁ := auxiliaryCfg N (seek N allow) .left c
    have hstep : (machine N).step c = some c₁ :=
      step_auxiliary N c _ _ (by rw [hs]; intro h; cases h) hi
        (by simp [delta, hs, seek, hr])
    obtain ⟨c₂, hreach, hhalt, hout⟩ := ih c₁ rfl (hi.move .left)
      (by simp [c₁, auxiliaryCfg, Tape.move, hk])
    exact ⟨c₂, TM.reachesIn.step hstep hreach, hhalt, hout⟩

/-- List form of the canonical witness predicate, checking one padding bit at a time. -/
def canonicalListFrom (N : NTM n) : List Bool → Cfg n N.Q → Prop
  | [], c => N.halted c ∧ c.output.cells 1 = .one
  | b :: bits, c =>
      if N.halted c then b = false ∧ canonicalListFrom N bits c
      else canonicalListFrom N bits (N.trace 1 (fun _ => b) c)

instance (N : NTM n) (bits : List Bool) (c : Cfg n N.Q) :
    Decidable (canonicalListFrom N bits c) := by
  induction bits generalizing c with
  | nil => unfold canonicalListFrom; infer_instance
  | cons b bits ih =>
    unfold canonicalListFrom
    letI := ih c
    letI := ih (N.trace 1 (fun _ => b) c)
    infer_instance

private theorem canonicalListFrom_halted_congr (N : NTM n) (bits : List Bool)
    (c c' : Cfg n N.Q) (hc : N.halted c) (hc' : N.halted c')
    (ho : c.output.cells 1 = c'.output.cells 1) :
    canonicalListFrom N bits c ↔ canonicalListFrom N bits c' := by
  change c.state = N.qhalt at hc
  change c'.state = N.qhalt at hc'
  induction bits with
  | nil => simp [canonicalListFrom, NTM.halted, Cfg.isHalted, hc, hc', ho]
  | cons b bits ih =>
    simp only [canonicalListFrom, NTM.halted, Cfg.isHalted, hc, hc', ite_true, ih]

private def paddingCfg (N : NTM n) (c : Cfg n N.Q) : Cfg n N.Q where
  state := c.state
  input := c.input.move .right
  work := fun j => (c.work j).writeAndMove Γ.blank .right
  output := c.output.move .right

private theorem step_padding (N : NTM n) (c : Cfg n N.Q) (w : Tape)
    (hc : N.halted c) (hi : c.output.StartInvariant) (hw : w.read = .zero) :
    (machine N).step (embed N c w) =
      some (embed N (paddingCfg N c) (advanceChoice w)) := by
  have h := step_auxiliary N (embed N c w) (.inl c.state) .right
    (by intro h; cases h) hi (by simp [delta, embed, hc, hw])
  rw [h]
  congr 1
  apply Cfg.ext <;> try rfl
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [auxiliaryCfg, embed, advanceChoice]
  · intro j
    simp [auxiliaryCfg, embed, paddingCfg]

private theorem step_source (N : NTM n) (c : Cfg n N.Q) (w : Tape) (b : Bool)
    (hc : ¬ N.halted c) (hw : w.read = Γ.ofBool b) :
    (machine N).step (embed N c w) =
      some (embed N (N.trace 1 (fun _ => b) c) (advanceChoice w)) := by
  change c.state ≠ N.qhalt at hc
  have hb : decide (Γ.ofBool b = Γ.one) = b := by cases b <;> decide
  have hvalid : Γ.ofBool b = .zero ∨ Γ.ofBool b = .one := by cases b <;> simp [Γ.ofBool]
  rcases hd : N.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read with
    ⟨q, ww, ow, id, wd, od⟩
  simp only [TM.step, machine, embed, delta, Sum.inl_ne_inr, ite_false, hc,
    Fin.snoc_last, hw, hb, hvalid, ite_true, Fin.snoc_castSucc, hd, NTM.trace]
  congr 1
  apply Cfg.ext <;> try rfl
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [advanceChoice]
  · intro j
    simp

private theorem source_output_invariant (N : NTM n) (c : Cfg n N.Q) (b : Bool)
    (hi : c.output.StartInvariant) : (N.trace 1 (fun _ => b) c).output.StartInvariant := by
  by_cases hc : N.halted c
  · simpa [N.trace_halted 1 _ hc] using hi
  · change c.state ≠ N.qhalt at hc
    rcases hd : N.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simpa [NTM.trace, hc, hd] using hi.writeAndMove ow od

private theorem source_output_head_le (N : NTM n) (c : Cfg n N.Q) (b : Bool) :
    (N.trace 1 (fun _ => b) c).output.head ≤ c.output.head + 1 := by
  by_cases hc : N.halted c
  · simp [N.trace_halted 1 _ hc]
  · change c.state ≠ N.qhalt at hc
    rcases hd : N.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read with
      ⟨q, ww, ow, id, wd, od⟩
    simpa [NTM.trace, hc, hd] using c.output.head_writeAndMove_le ow od

private theorem step_then_seek (N : NTM n) (c : Cfg n N.Q) (w : Tape)
    (allow : Bool) (hi : c.output.StartInvariant)
    (hd : delta N (.inl c.state) c.input.read
      (fun j => ((embed N c w).work j).read) c.output.read =
      auxiliaryDelta N (seek N allow) c.output.read .right) :
    ∃ c', (machine N).reachesIn (c.output.head + 4) (embed N c w) c' ∧
      (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (allow && decide (c.output.cells 1 = .one)) := by
  let c₁ := auxiliaryCfg N (seek N allow) .right (embed N c w)
  have hs : (machine N).step (embed N c w) = some c₁ :=
    step_auxiliary N _ _ _ (by intro h; cases h) hi hd
  obtain ⟨c₂, hr, hh, ho⟩ := seek_reaches_halt N allow (c.output.head + 1) c₁
    rfl (hi.move .right) rfl
  exact ⟨c₂, TM.reachesIn.step hs hr, hh, ho⟩

/-- A prepared source configuration and finite witness are checked by the
actual TM in at most `2 * witnessLength + outputHead + 4` transitions. -/
theorem prepared_correct (N : NTM n) (bits : List Bool) (c : Cfg n N.Q) (w : Tape)
    (hi : c.output.StartInvariant) (hw : HasChoices w bits) :
    ∃ c' t, t ≤ 2 * bits.length + c.output.head + 4 ∧
      (machine N).reachesIn t (embed N c w) c' ∧ (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (decide (canonicalListFrom N bits c)) := by
  induction bits generalizing c w with
  | nil =>
    have hread := hasChoices_nil_read w hw
    obtain ⟨c', hr, hh, ho⟩ := step_then_seek N c w (decide (N.halted c)) hi (by
      by_cases hc : c.state = N.qhalt <;>
        simp [delta, embed, hread, hc, NTM.halted, Cfg.isHalted])
    refine ⟨c', c.output.head + 4, by simp, hr, hh, ?_⟩
    simpa only [canonicalListFrom, Bool.decide_and] using ho
  | cons b bits ih =>
    have hread := hasChoices_cons_read w b bits hw
    have htail := hasChoices_advance w b bits hw
    by_cases hc : N.halted c
    · cases b with
      | false =>
        obtain ⟨c', t, ht, hr, hh, ho⟩ := ih (paddingCfg N c) (advanceChoice w)
          (hi.move .right) htail
        refine ⟨c', t + 1, ?_, TM.reachesIn.step (step_padding N c w hc hi hread) hr,
          hh, ?_⟩
        · simp only [paddingCfg, Tape.move, List.length_cons] at ht ⊢
          omega
        · have heq := canonicalListFrom_halted_congr N bits (paddingCfg N c) c hc hc rfl
          have hs : c.state = N.qhalt := hc
          simpa only [canonicalListFrom, NTM.halted, Cfg.isHalted, hs, ite_true,
            true_and, heq] using ho
      | true =>
        obtain ⟨c', hr, hh, ho⟩ := step_then_seek N c w false hi (by
          simp [delta, embed, hread, Γ.ofBool, show c.state = N.qhalt from hc])
        refine ⟨c', c.output.head + 4, by omega, hr, hh, ?_⟩
        simpa [canonicalListFrom, hc] using ho
    · obtain ⟨c', t, ht, hr, hh, ho⟩ := ih (N.trace 1 (fun _ => b) c) (advanceChoice w)
        (source_output_invariant N c b hi) htail
      refine ⟨c', t + 1, ?_, TM.reachesIn.step (step_source N c w b hc hread) hr,
        hh, ?_⟩
      · have hhead := source_output_head_le N c b
        simp only [List.length_cons]
        omega
      · simpa only [canonicalListFrom, hc, ite_false] using ho

private theorem canonicalListFrom_halted (N : NTM n) (bits : List Bool)
    (c : Cfg n N.Q) (hc : N.halted c) :
    canonicalListFrom N bits c ↔ c.output.cells 1 = .one ∧ ∀ b ∈ bits, b = false := by
  change c.state = N.qhalt at hc
  induction bits with
  | nil => simp [canonicalListFrom, NTM.halted, Cfg.isHalted, hc]
  | cons b bits ih =>
    simp only [canonicalListFrom, NTM.halted, Cfg.isHalted, hc, ite_true, ih,
      List.forall_mem_cons]
    tauto

private theorem canonicalWitnessFrom_halted (N : NTM n) (T : ℕ)
    (c : Cfg n N.Q) (choices : Fin T → Bool) (hc : N.halted c) :
    canonicalWitnessFrom N T c choices ↔
      c.output.cells 1 = .one ∧ choices = fun _ => false := by
  change c.state = N.qhalt at hc
  cases T with
  | zero =>
    have hchoices : choices = fun _ => false := by funext i; exact Fin.elim0 i
    simp [canonicalWitnessFrom, NTM.halted, Cfg.isHalted, hc, hchoices]
  | succ T => simp [canonicalWitnessFrom, NTM.halted, Cfg.isHalted, hc]

private theorem forall_mem_ofFn_false_iff (T : ℕ) (choices : Fin T → Bool) :
    (∀ b ∈ List.ofFn choices, b = false) ↔ choices = fun _ => false := by
  constructor
  · intro h
    funext i
    exact h (choices i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact congrFun h i

/-- The list predicate checked by the machine is exactly the existing
canonical fixed-width witness predicate. -/
theorem canonicalListFrom_ofFn_iff (N : NTM n) (T : ℕ) (c : Cfg n N.Q)
    (choices : Fin T → Bool) :
    canonicalListFrom N (List.ofFn choices) c ↔ canonicalWitnessFrom N T c choices := by
  induction T generalizing c with
  | zero => simp [canonicalListFrom, canonicalWitnessFrom]
  | succ T ih =>
    by_cases hc : N.halted c
    · rw [canonicalListFrom_halted N _ c hc, canonicalWitnessFrom_halted N _ c _ hc,
        forall_mem_ofFn_false_iff]
    · rw [List.ofFn_succ, canonicalListFrom, ite_eq_right hc,
        canonicalWitnessFrom, ite_eq_right hc]
      exact ih _ _

/-- The prepared verifier checks canonical witnesses with their original finite
indexing, with an explicit linear transition bound. -/
theorem prepared_correct_ofFn (N : NTM n) (T : ℕ) (c : Cfg n N.Q)
    (choices : Fin T → Bool) (hi : c.output.StartInvariant) :
    ∃ c' t, t ≤ 2 * T + c.output.head + 4 ∧
      (machine N).reachesIn t (embed N c (witnessTape (List.ofFn choices))) c' ∧
      (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (decide (canonicalWitnessFrom N T c choices)) := by
  obtain ⟨c', t, ht, hr, hh, ho⟩ := prepared_correct N (List.ofFn choices) c
    (witnessTape (List.ofFn choices)) hi (witnessTape_hasChoices _)
  refine ⟨c', t, by simpa using ht, hr, hh, ?_⟩
  simpa only [canonicalListFrom_ofFn_iff] using ho

/-- The source input has its ordinary initial tapes; only the additional
witness tape is prepared. Loading that tape from an encoded ordinary input is
a separate setup obligation. -/
def initialPrepared (N : NTM n) (x : List Bool) (choices : List Bool) :
    Cfg (n + 1) (machine N).Q := embed N (N.initCfg x) (witnessTape choices)

/-- From a source input and preloaded witness, the canonical predicate is
verified in at most `2*T+4` actual deterministic transitions. -/
theorem initialPrepared_correct (N : NTM n) (x : List Bool) (T : ℕ)
    (choices : Fin T → Bool) :
    ∃ c' t, t ≤ 2 * T + 4 ∧
      (machine N).reachesIn t (initialPrepared N x (List.ofFn choices)) c' ∧
      (machine N).halted c' ∧
      c'.output.cells 1 = Γ.ofBool (decide (choices ∈ canonicalWitnesses N x T)) := by
  obtain ⟨c', t, ht, hr, hh, ho⟩ := prepared_correct_ofFn N T (N.initCfg x) choices
    Tape.StartInvariant.init_nil
  refine ⟨c', t, by simpa using ht, hr, hh, ?_⟩
  simpa only [canonicalWitnesses, mem_canonicalWitnessesFrom] using ho

end Toda.Counting.CanonicalVerifier

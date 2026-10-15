import Toda.Oracle.Postprocess.Defs

namespace Toda.Oracle.Postprocess

open Complexity

variable {n k : ℕ}

theorem left_append {α : Type} (a : Fin n → α) (b : Fin (k + 1) → α) :
    (fun i => Fin.append a b (Fin.castAdd (k + 1) i)) = a := by funext i; simp

theorem right_append {α : Type} (a : Fin n → α) (b : Fin (k + 1) → α) :
    (fun i => Fin.append a b (Fin.natAdd n i)) = b := by funext i; simp

theorem read_left_append (a : Fin n → Tape) (b : Fin (k + 1) → Tape) :
    left (fun i => (Fin.append a b i).read) = fun i => (a i).read := by
  funext i
  simp only [left, Fin.append_left]

theorem read_right_append (a : Fin n → Tape) (b : Fin (k + 1) → Tape) :
    right (fun i => (Fin.append a b i).read) = fun i => (b i).read := by
  funext i
  simp only [right, Fin.append_right]

theorem write_append {a b : ℕ} (t : Fin a → Tape) (u : Fin b → Tape)
    (w : Fin a → Γw) (v : Fin b → Γw) (d : Fin a → Dir3) (e : Fin b → Dir3) :
    (fun i => (Fin.append t u i).writeAndMove ((Fin.append w v i).toΓ) (Fin.append d e i)) =
      Fin.append (fun i => (t i).writeAndMove (w i).toΓ (d i))
        (fun i => (u i).writeAndMove (v i).toΓ (e i)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left, Fin.append_right]

theorem write_snoc (t : Fin k → Tape) (u : Tape) (w : Fin k → Γw) (v : Γw)
    (d : Fin k → Dir3) (e : Dir3) :
    (fun i => Tape.writeAndMove ((Fin.snoc t u : Fin (k + 1) → Tape) i) (Γw.toΓ ((Fin.snoc w v : Fin (k + 1) → Γw) i)) ((Fin.snoc d e : Fin (k + 1) → Dir3) i)) =
      Fin.snoc (fun i => (t i).writeAndMove (w i).toΓ (d i)) (u.writeAndMove v.toΓ e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]

@[simp] theorem fresh_step (parked : Bool) :
    (fresh parked).writeAndMove Γ.blank (TM.idleDir (fresh parked).read) = fresh true := by
  cases parked
  · rfl
  · exact Preprocess.blankOutput_step 1

@[simp] theorem fresh_readBack (parked : Bool) :
    TM.readBackWrite (fresh parked).read = Γw.blank := by cases parked <;> rfl

@[simp] theorem sourceCfg_init (M : OracleTM n) (N : TM k) (input : List Bool) :
    sourceCfg M N (M.initCfg input) false = (machine M N).initCfg input := by
  have hw : Fin.append (fun _ : Fin n => Tape.init [])
      (Fin.snoc (fun _ : Fin k => Tape.init []) (Tape.init [])) =
        (fun _ : Fin (n + (k + 1)) => Tape.init []) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp
  change ({ state := Sum.inl M.qstart, input := Tape.init (input.map Γ.ofBool), query := Tape.init [], work := Fin.append (fun _ => Tape.init []) (Fin.snoc (fun _ => Tape.init []) (Tape.init [])), output := Tape.init [] } : OracleCfg (n + (k + 1)) (machine M N).Q) = _
  rw [hw]
  rfl

theorem source_step (M : OracleTM n) (N : TM k) (oracle : BooleanOracle)
    {cfg next : OracleCfg n M.Q} (hstep : M.step oracle cfg = some next) (parked : Bool) :
    ∃ parked', (machine M N).step oracle (sourceCfg M N cfg parked) =
      some (sourceCfg M N next parked') := by
  have hhalt : cfg.state ≠ M.qhalt := by intro h; simp [OracleTM.step, h] at hstep
  cases hquery : M.queryTransition cfg.state with
  | some states =>
    refine ⟨parked, ?_⟩
    simp only [OracleTM.step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
    rw [← hstep]
    simp [OracleTM.step, machine, sourceCfg, hhalt, hquery]
    split <;> simp_all
  | none =>
    refine ⟨true, ?_⟩
    simp only [OracleTM.step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
    rw [← hstep]
    simp only [OracleTM.step, machine, sourceCfg, reduceCtorEq, ↓reduceIte, hhalt,
      hquery, Option.map_none, localTransition, right,
      Fin.append_right, Fin.snoc_last, Fin.snoc_castSucc]
    rw [read_left_append]
    simp only [write_append, write_snoc, fresh_readBack]
    simp only [show Γw.blank.toΓ = Γ.blank from rfl, fresh_step]

theorem source_run (M : OracleTM n) (N : TM k) (oracle : BooleanOracle)
    {elapsed : ℕ} {cfg final : OracleCfg n M.Q}
    (hreach : M.reachesIn oracle elapsed cfg final) (parked : Bool) :
    ∃ parked', (machine M N).reachesIn oracle elapsed (sourceCfg M N cfg parked)
      (sourceCfg M N final parked') := by
  induction hreach generalizing parked with
  | zero => exact ⟨parked, .zero⟩
  | step hstep _ ih =>
    obtain ⟨nextParked, hone⟩ := source_step M N oracle hstep parked
    obtain ⟨finalParked, htail⟩ := ih nextParked
    exact ⟨finalParked, .step hone htail⟩

theorem oracle_reachesIn_startInvariant {M : OracleTM n} {oracle : BooleanOracle}
    {elapsed : ℕ} {cfg final : OracleCfg n M.Q}
    (hreach : M.reachesIn oracle elapsed cfg final)
    (hi : cfg.input.StartInvariant) (hq : cfg.query.StartInvariant)
    (hw : ∀ i, (cfg.work i).StartInvariant) (ho : cfg.output.StartInvariant) :
    final.input.StartInvariant ∧ final.query.StartInvariant ∧
      (∀ i, (final.work i).StartInvariant) ∧ final.output.StartInvariant := by
  induction hreach with
  | zero => exact ⟨hi, hq, hw, ho⟩
  | @step first middle t final hstep htail ih =>
    have hn : first.state ≠ M.qhalt := by intro h; simp [OracleTM.step, h] at hstep
    cases hquery : M.queryTransition first.state with
    | some pair =>
      simp only [OracleTM.step, hn, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst middle
      exact ih hi hq hw ho
    | none =>
      simp only [OracleTM.step, hn, ↓reduceIte, hquery, Option.some.injEq] at hstep
      subst middle
      exact ih (hi.move _) (hq.writeAndMove _ _) (fun i => (hw i).writeAndMove _ _)
        (ho.writeAndMove _ _)

end Toda.Oracle.Postprocess

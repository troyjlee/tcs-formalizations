import Toda.Oracle.FunctionPostprocess.Defs

namespace Toda.Oracle.FunctionPostprocess

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

open Postprocess (write_append write_snoc fresh_step fresh_readBack)

@[simp] theorem sourceCfg_init (M : FunctionTM n) (N : TM k) (input : List Bool) :
    sourceCfg M N (M.initCfg input) false = (machine M N).initCfg input := by
  have hw : Fin.append (fun _ : Fin n => Tape.init [])
      (Fin.snoc (fun _ : Fin k => Tape.init []) (Tape.init [])) =
        (fun _ : Fin (n + (k + 1)) => Tape.init []) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp
  change ({ state := Sum.inl M.qstart, input := Tape.init (input.map Γ.ofBool), query := Tape.init [], answer := Tape.init [], work := Fin.append (fun _ => Tape.init []) (Fin.snoc (fun _ => Tape.init []) (Tape.init [])), output := Tape.init [] } : FunctionCfg (n + (k + 1)) (machine M N).Q) = _
  rw [hw]
  rfl

theorem source_step (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    {cfg next : FunctionCfg n M.Q} (hstep : M.step oracle cfg = some next) (parked : Bool) :
    ∃ parked', (machine M N).step oracle (sourceCfg M N cfg parked) =
      some (sourceCfg M N next parked') := by
  have hhalt : cfg.state ≠ M.qhalt := by intro h; simp [FunctionTM.step, h] at hstep
  cases hquery : M.queryTransition cfg.state with
  | some states =>
    refine ⟨parked, ?_⟩
    simp only [FunctionTM.step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
    rw [← hstep]
    simp [FunctionTM.step, machine, sourceCfg, hhalt, hquery]
  | none =>
    refine ⟨true, ?_⟩
    simp only [FunctionTM.step, hhalt, ↓reduceIte, hquery, Option.some.injEq] at hstep
    rw [← hstep]
    simp only [FunctionTM.step, machine, sourceCfg, reduceCtorEq, ↓reduceIte, hhalt,
      hquery, Option.map_none, localTransition, right,
      Fin.append_right, Fin.snoc_last, Fin.snoc_castSucc]
    rw [read_left_append]
    simp only [write_append, write_snoc, fresh_readBack]
    simp only [show Γw.blank.toΓ = Γ.blank from rfl, fresh_step]

theorem source_run (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    {elapsed : ℕ} {cfg final : FunctionCfg n M.Q}
    (hreach : M.reachesIn oracle elapsed cfg final) (parked : Bool) :
    ∃ parked', (machine M N).reachesIn oracle elapsed (sourceCfg M N cfg parked)
      (sourceCfg M N final parked') := by
  induction hreach generalizing parked with
  | zero => exact ⟨parked, .zero⟩
  | step hstep _ ih =>
    obtain ⟨nextParked, hone⟩ := source_step M N oracle hstep parked
    obtain ⟨finalParked, htail⟩ := ih nextParked
    exact ⟨finalParked, .step hone htail⟩

end Toda.Oracle.FunctionPostprocess

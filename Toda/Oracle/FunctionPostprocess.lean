import Toda.Oracle.FunctionPostprocess.Normalize

/-! # Ordinary FP postprocessing after a full-answer oracle computation -/

namespace Toda.Oracle.FunctionPostprocess

open Complexity

variable {n k : ℕ}

theorem entry_eq (N : TM k) (realInput stream : Tape) (bits : List Bool)
    (hh : stream.head = 1) (hc : stream.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    entry N realInput stream = TM.retargetInputStartedCfg N bits realInput := by
  have hs : stream = (Tape.init (bits.map Γ.ofBool)).move .right := Tape.ext hh hc
  subst stream
  congr 1

/-- A complete source oracle run followed by an ordinary machine, with fresh
scratch and a charged rewind of the answer tape. -/
theorem run (M : FunctionTM n) (N : TM k) (oracle : FunctionOracle)
    {post : List Bool → List Bool} {S : ℕ → ℕ} (hpost : N.ComputesInTime post S)
    (input answers : List Bool) {cfg : FunctionCfg n M.Q} {time : ℕ}
    (hsource : M.reachesIn oracle time (M.initCfg input) cfg) (hhalt : M.halted cfg)
    (hout : cfg.output.HasBinaryPrefix answers) :
    ∃ final elapsed, elapsed ≤ time + answers.length + 3 + S answers.length ∧
      (machine M N).reachesIn oracle elapsed ((machine M N).initCfg input) final ∧
      (machine M N).halted final ∧ final.output.HasOutput (post answers) := by
  have hinv := FunctionTM.reachesIn_startInvariant hsource (FunctionCfg.init_startInvariant _ _)
  let realInput := TM.transitionInput cfg.input
  let query := TM.transitionTape cfg.query
  let answer := TM.transitionTape cfg.answer
  let scratch : Fin n → Tape := fun i => TM.transitionTape (cfg.work i)
  have hreal : realInput.read ≠ .start :=
    PrepareBatch.transitionInput_read_ne_start cfg.input hinv.input
  have hquery : query.read ≠ .start :=
    PrepareBatch.transitionTape_read_ne_start cfg.query hinv.query
  have hanswer : answer.read ≠ .start :=
    PrepareBatch.transitionTape_read_ne_start cfg.answer hinv.answer
  have hscratch : ∀ i, (scratch i).read ≠ .start := fun i =>
    PrepareBatch.transitionTape_read_ne_start (cfg.work i) (hinv.work i)
  obtain ⟨parked, hsourceLift⟩ := source_run M N oracle hsource false
  have hboundary := boundary_step M N oracle cfg parked hhalt hout.read_blank
  obtain ⟨ready, hrewind, hh, hc⟩ := rewind_run M N oracle realInput query answer scratch
    hreal hquery hanswer hscratch cfg.output.head cfg.output rfl hinv.output
  have hentry := entry_eq N realInput ready answers hh
    (hc.trans (hout.cells_eq_init hinv.output.1))
  obtain ⟨postFinal, postTime, hpostTime, hpostRun, hpostHalt, hpostOut⟩ :=
    TM.retargetInputStarted_computesVirtual N hpost answers realInput
  have hpostLift := post_run M N oracle query answer scratch hquery hanswer hscratch hpostRun
  rw [← hentry] at hpostLift
  have htail := FunctionTM.reachesIn_trans (FunctionTM.reachesIn.step hboundary hrewind) hpostLift
  have hrun := FunctionTM.reachesIn_trans hsourceLift htail
  refine ⟨postCfg M N query answer scratch postFinal,
    time + (cfg.output.head + 2 + postTime), ?_, ?_, ?_, hpostOut⟩
  · have := hout.1
    omega
  · simpa using hrun
  · exact congrArg (fun q => Sum.inr (some q)) hpostHalt

/-- Polynomial-time full-answer computation is closed under ordinary FP
postprocessing into a normalized Boolean verdict. -/
theorem mem_pWithFunctionOracle (oracle : FunctionOracle)
    {result post : List Bool → List Bool} {language : Language}
    (M : FunctionTM n) {T : ℕ → ℕ} (hT : PolyBound T)
    (hsource : ∀ input, ∃ cfg elapsed, elapsed ≤ T input.length ∧
      M.reachesIn oracle elapsed (M.initCfg input) cfg ∧ M.halted cfg ∧
      cfg.output.HasBinaryPrefix (result input))
    (hpost : post ∈ FP)
    (hyes : ∀ input, input ∈ language → post (result input) = [true])
    (hno : ∀ input, input ∉ language → post (result input) = [false]) :
    language ∈ PWithFunctionOracle oracle := by
  obtain ⟨degree, postTapes, N, S, hcompute, htime⟩ := hpost
  obtain ⟨A, B, hS⟩ := PolyBound.exists_mul_pow_bound (BigO.pow_polynomial_bound htime)
  let bound := fun length => 2 * T length + 3 + A * (T length + 1) ^ B
  refine ⟨n + (postTapes + 1), machine M N, bound, ?_, ?_⟩
  · intro input
    obtain ⟨sourceFinal, sourceTime, hsourceTime, hsourceRun, hsourceHalt, hsourceOut⟩ :=
      hsource input
    obtain ⟨final, elapsed, hbound, hrun, hhalt, hout⟩ :=
      run M N oracle hcompute input (result input) hsourceRun hsourceHalt hsourceOut
    have hlength := FunctionTM.output_length_le_of_reachesIn hsourceRun hsourceOut.hasOutput
    have hpostBound : S (result input).length ≤ A * (T input.length + 1) ^ B :=
      (hS (result input).length).trans
      (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) B))
    refine ⟨final, elapsed, ?_, hrun, hhalt, ?_, ?_⟩
    · dsimp [bound]
      omega
    · intro hin
      have h := hout
      rw [hyes input hin] at h
      simpa [Γ.ofBool] using h.1 0 (by simp)
    · intro hin
      have h := hout
      rw [hno input hin] at h
      simpa [Γ.ofBool] using h.1 0 (by simp)
  · exact (((PolyBound.const 2).mul hT).add (PolyBound.const 3)).add
      ((PolyBound.const A).mul ((hT.add (PolyBound.const 1)).pow B))

end Toda.Oracle.FunctionPostprocess

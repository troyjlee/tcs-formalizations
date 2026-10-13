/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.BlocksFP
import IPPSPACE.QBF.ConfigurationValidity

/-!
# Polynomial-time construction of exact one-hot validity

This certifies the actual `CodecValidity.fin` formula used for configuration
states and heads. Both nested ranges have polynomial-time unary lengths; the
certificate constructs the formula and its binary names, rather than testing
an already supplied configuration. Width zero retains its rejecting formula.
-/

namespace IPPSPACE

open Complexity

private theorem ofFn_val_eq_map_range {α : Type} (width : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin width => f i.val) = (List.range width).map f := by
  apply List.ext_get
  · simp
  · intro i hleft hright
    simp

theorem finValidity_eq_range (start width : ℕ) :
    (CodecValidity.fin width).formula (blockNames start width) =
      qbfAny ((List.range width).map (fun hot =>
        blockValues (blockNames start width) (fun i => decide (hot = i.val)))) := by
  unfold CodecValidity.fin qbfAnyFin
  have heq (hot : Fin width) : FixedWidthCodec.encodeFin hot =
      (fun i : Fin width => decide (hot.val = i.val)) := by
    funext i
    simp [FixedWidthCodec.encodeFin, Fin.ext_iff]
  simp only [heq]
  exact congrArg qbfAny (ofFn_val_eq_map_range width
    (fun hot => blockValues (blockNames start width) (fun i => decide (hot = i.val))))

/-- Exact one-hot validity construction is in the actual upstream `FP` class
for polynomial-time block starts and widths. -/
theorem encode_finValidity_mem_FP {start width : List Bool → ℕ}
    (hstart : UnaryFn start) (hwidth : UnaryFn width) :
    (fun z => encodeQBF ((CodecValidity.fin (width z)).formula
      (blockNames (start z) (width z)))) ∈ FP := by
  have hvalue : FPPred fun v =>
      decide ((pairSnd (pairFst v)).length = (pairSnd v).length) = true :=
    (FPPred.eq UnaryFn.index.lift UnaryFn.index).of_iff (fun _ => by simp)
  have hbody := encodeQBF_blockValues_contiguous_mem_FP
    (values := fun w i => decide ((pairSnd w).length = i)) hstart.lift hwidth.lift hvalue
  have h := encodeQBF_qbfAny_range_mem_FP (body := fun z hot =>
    blockValues (blockNames (start z) (width z)) (fun i => decide (hot = i.val))) hwidth hbody
  simpa only [← finValidity_eq_range] using h

end IPPSPACE

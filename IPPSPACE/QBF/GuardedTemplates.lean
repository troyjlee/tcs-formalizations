/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationValidity
import IPPSPACE.QBF.CodecReachability

/-!
# Validity guards for local configuration formulas

A local formula need only be proved correct on codec images. Conjoining exact
validity tests then extends that correctness to all Boolean words, rejecting
malformed endpoints. This supplies the representation obligations needed by
the succinct accepting-reachability construction without enumerating codes.
-/

namespace IPPSPACE

open Complexity

namespace FixedWidthCodec

variable {α : Type} {width : ℕ}

theorem liftPredicate_iff (codec : FixedWidthCodec α width) (accepts : α → Prop)
    (bits : Fin width → Bool) :
    codec.liftPredicate accepts bits ↔ ∃ a, codec.encode a = bits ∧ accepts a := by
  cases h : codec.decodeCanonical bits with
  | none =>
    simp only [liftPredicate, h]
    constructor
    · exact False.elim
    · rintro ⟨a, rfl, _⟩
      simp at h
  | some a =>
    have he := (codec.decodeCanonical_eq_some_iff bits a).mp h
    rw [← he, codec.liftPredicate_encode]
    simp only [codec.encode_injective.eq_iff, exists_eq_left]

theorem liftRelation_iff (codec : FixedWidthCodec α width) (edge : α → α → Prop)
    (source target : Fin width → Bool) :
    codec.liftRelation edge source target ↔
      ∃ a b, codec.encode a = source ∧ codec.encode b = target ∧ edge a b := by
  cases h : codec.decodeCanonical source with
  | none =>
    simp only [liftRelation, h]
    constructor
    · exact False.elim
    · rintro ⟨a, b, rfl, _, _⟩
      simp at h
  | some a =>
    have he := (codec.decodeCanonical_eq_some_iff source a).mp h
    rw [← he, codec.liftRelation_from_encode_iff]
    simp only [codec.encode_injective.eq_iff]
    constructor
    · rintro ⟨b, hb, hab⟩
      exact ⟨a, b, rfl, hb, hab⟩
    · rintro ⟨c, b, rfl, hb, hab⟩
      exact ⟨b, hb, hab⟩

end FixedWidthCodec

variable {α : Type} {width bound : ℕ} {codec : FixedWidthCodec α width}

/-- Validate the one configuration block before testing acceptance. -/
def guardedAcceptance (valid : CodecValidity codec bound) (accept : QBF) : QBF :=
  .conj (valid.formula Fin.val) accept

/-- Validate both endpoint blocks before testing a local transition. -/
def guardedEdge (valid : CodecValidity codec bound) (base : QBF) : QBF :=
  .conj (valid.formula Fin.val)
    (.conj (valid.formula (fun i => width + i.val)) base)

theorem templateAccepts_guardedAcceptance (valid : CodecValidity codec bound)
    (accept : QBF) (accepts : α → Prop)
    (haccept : ∀ a, templateAccepts accept (codec.encode a) ↔ accepts a)
    (bits : Fin width → Bool) :
    templateAccepts (guardedAcceptance valid accept) bits ↔ codec.liftPredicate accepts bits := by
  have hbits : stateBlockAssignment bits ∘ Fin.val = bits := by
    funext i
    simp [stateBlockAssignment, i.isLt]
  simp only [templateAccepts, guardedAcceptance, QBF.eval_conj, Bool.and_eq_true,
    valid.eval_iff, hbits, codec.liftPredicate_iff]
  constructor
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, rfl, (haccept a).mp ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨⟨a, rfl⟩, (haccept a).mpr ha⟩

theorem templateEdge_guardedEdge (valid : CodecValidity codec bound)
    (base : QBF) (edge : α → α → Prop)
    (hedge : ∀ a b, templateEdge base (codec.encode a) (codec.encode b) ↔ edge a b)
    (source target : Fin width → Bool) :
    templateEdge (guardedEdge valid base) source target ↔ codec.liftRelation edge source target := by
  have hs : edgeBlockAssignment source target ∘ Fin.val = source := by
    funext i
    simp [edgeBlockAssignment, i.isLt]
  have ht : edgeBlockAssignment source target ∘ (fun i : Fin width => width + i.val) = target := by
    funext i
    simp [edgeBlockAssignment, show ¬width + i.val < width by omega,
      show width + i.val < 2 * width by omega]
  simp only [templateEdge, guardedEdge, QBF.eval_conj, Bool.and_eq_true,
    valid.eval_iff, hs, ht, codec.liftRelation_iff]
  constructor
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, hab⟩
    exact ⟨a, b, rfl, rfl, (hedge a b).mp hab⟩
  · rintro ⟨a, b, rfl, rfl, hab⟩
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩, (hedge a b).mpr hab⟩

theorem guardedAcceptance_quantifierFree (valid : CodecValidity codec bound)
    (accept : QBF) (haccept : accept.QuantifierFree) :
    (guardedAcceptance valid accept).QuantifierFree :=
  QBF.quantifierFree_conj.mpr ⟨valid.quantifierFree _, haccept⟩

theorem guardedEdge_quantifierFree (valid : CodecValidity codec bound)
    (base : QBF) (hbase : base.QuantifierFree) :
    (guardedEdge valid base).QuantifierFree :=
  QBF.quantifierFree_conj.mpr ⟨valid.quantifierFree _,
    QBF.quantifierFree_conj.mpr ⟨valid.quantifierFree _, hbase⟩⟩

theorem guardedAcceptance_freeVars_lt (valid : CodecValidity codec bound)
    (accept : QBF) (haccept : ∀ i ∈ accept.freeVars, i < width) :
    ∀ i ∈ (guardedAcceptance valid accept).freeVars, i < width := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨j, rfl⟩ := valid.names_mem _ i (freeVars_subset_qbfNames _ hi)
    exact j.isLt
  · exact haccept i hi

theorem guardedEdge_freeVars_lt (valid : CodecValidity codec bound)
    (base : QBF) (hbase : ∀ i ∈ base.freeVars, i < 2 * width) :
    ∀ i ∈ (guardedEdge valid base).freeVars, i < 2 * width := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨j, rfl⟩ := valid.names_mem _ i (freeVars_subset_qbfNames _ hi)
    have := j.isLt
    omega
  · rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, rfl⟩ := valid.names_mem _ i (freeVars_subset_qbfNames _ hi)
      have := j.isLt
      omega
    · exact hbase i hi

theorem nodeCount_guardedAcceptance_le (valid : CodecValidity codec bound) (accept : QBF) :
    nodeCount (guardedAcceptance valid accept) ≤ bound + nodeCount accept + 1 := by
  have := valid.nodeCount_le Fin.val
  simp only [guardedAcceptance, nodeCount]
  omega

theorem nodeCount_guardedEdge_le (valid : CodecValidity codec bound) (base : QBF) :
    nodeCount (guardedEdge valid base) ≤ 2 * bound + nodeCount base + 2 := by
  have := valid.nodeCount_le Fin.val
  have := valid.nodeCount_le (fun i => width + i.val)
  simp only [guardedEdge, nodeCount]
  omega

end IPPSPACE

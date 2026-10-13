/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationEncoding
import IPPSPACE.QBF.AcceptingReachability

/-!
# Reachability through canonical configuration codes

Extending a relation to Boolean words must reject invalid representations;
otherwise malformed intermediate words could create spurious paths. The
canonical decoder gives an extension with exactly the original reachability
from every encoded initial state. The final theorem connects a proved local
edge/acceptance representation to the existing succinct QBF construction.
It does not supply a machine transition formula or assume PSPACE hardness.
-/

namespace IPPSPACE

namespace FixedWidthCodec

variable {α : Type} {width : ℕ}

/-- Extend a relation to words, rejecting either noncanonical endpoint. -/
def liftRelation (codec : FixedWidthCodec α width) (edge : α → α → Prop)
    (source target : Fin width → Bool) : Prop :=
  match codec.decodeCanonical source, codec.decodeCanonical target with
  | some a, some b => edge a b
  | _, _ => False

/-- Extend an accepting-state predicate, rejecting noncanonical words. -/
def liftPredicate (codec : FixedWidthCodec α width) (accepts : α → Prop)
    (bits : Fin width → Bool) : Prop :=
  match codec.decodeCanonical bits with
  | some a => accepts a
  | none => False

@[simp] theorem liftRelation_encode (codec : FixedWidthCodec α width)
    (edge : α → α → Prop) (a b : α) :
    codec.liftRelation edge (codec.encode a) (codec.encode b) ↔ edge a b := by
  simp [liftRelation]

@[simp] theorem liftPredicate_encode (codec : FixedWidthCodec α width)
    (accepts : α → Prop) (a : α) :
    codec.liftPredicate accepts (codec.encode a) ↔ accepts a := by
  simp [liftPredicate]

theorem liftRelation_from_encode_iff (codec : FixedWidthCodec α width)
    (edge : α → α → Prop) (a : α) (target : Fin width → Bool) :
    codec.liftRelation edge (codec.encode a) target ↔
      ∃ b, codec.encode b = target ∧ edge a b := by
  cases h : codec.decodeCanonical target with
  | none =>
    simp only [liftRelation, decodeCanonical_encode, h]
    constructor
    · exact False.elim
    · rintro ⟨b, rfl, _⟩
      simp at h
  | some b =>
    have hencode := (codec.decodeCanonical_eq_some_iff target b).mp h
    rw [← hencode]
    simp only [liftRelation_encode]
    constructor
    · intro hab
      exact ⟨b, rfl, hab⟩
    · rintro ⟨c, hc, hac⟩
      exact codec.encode_injective hc ▸ hac

/-- Paths beginning at a valid code cannot pass through invalid words. -/
theorem liftRelation_reachable_from_encode_iff (codec : FixedWidthCodec α width)
    (edge : α → α → Prop) (a : α) (target : Fin width → Bool) :
    Relation.ReflTransGen (codec.liftRelation edge) (codec.encode a) target ↔
      ∃ b, codec.encode b = target ∧ Relation.ReflTransGen edge a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a, rfl, .refl⟩
    | @tail middle target _ hstep ih =>
      obtain ⟨b, rfl, hpath⟩ := ih
      obtain ⟨c, hcode, hbc⟩ := (codec.liftRelation_from_encode_iff edge b target).mp hstep
      exact ⟨c, hcode, hpath.tail hbc⟩
  · rintro ⟨b, rfl, h⟩
    exact Relation.ReflTransGen.lift codec.encode (fun _ _ hab =>
      (codec.liftRelation_encode edge _ _).mpr hab) a b h

@[simp] theorem liftRelation_reachable_encode_iff (codec : FixedWidthCodec α width)
    (edge : α → α → Prop) (a b : α) :
    Relation.ReflTransGen (codec.liftRelation edge) (codec.encode a) (codec.encode b) ↔
      Relation.ReflTransGen edge a b := by
  rw [codec.liftRelation_reachable_from_encode_iff]
  simp only [codec.encode_injective.eq_iff, exists_eq_left]

/-- Acceptance through Boolean codes is exactly acceptance in the original
component relation; this includes zero-step acceptance. -/
theorem liftRelation_accepting_reachable_iff (codec : FixedWidthCodec α width)
    (edge : α → α → Prop) (accepts : α → Prop) (a : α) :
    (∃ target, codec.liftPredicate accepts target ∧
      Relation.ReflTransGen (codec.liftRelation edge) (codec.encode a) target) ↔
      ∃ b, accepts b ∧ Relation.ReflTransGen edge a b := by
  constructor
  · rintro ⟨target, haccept, hreach⟩
    obtain ⟨b, rfl, hab⟩ := (codec.liftRelation_reachable_from_encode_iff edge a target).mp hreach
    exact ⟨b, (codec.liftPredicate_encode accepts b).mp haccept, hab⟩
  · rintro ⟨b, haccept, hab⟩
    exact ⟨codec.encode b, (codec.liftPredicate_encode accepts b).mpr haccept,
      (codec.liftRelation_reachable_encode_iff edge a b).mpr hab⟩

end FixedWidthCodec

open Complexity

/-- A local representation proof transports all the way to the canonical
prenex language. Both hypotheses concern one step or one accepting state,
not a reachability assertion or a complexity-class inclusion. -/
theorem encodedAcceptingReachability_iff_of_codec {α : Type} {width : ℕ}
    (codec : FixedWidthCodec α width) (edge : α → α → Prop) (accepts : α → Prop)
    (base accept : QBF)
    (hbase : base.QuantifierFree) (hbaseVars : ∀ i ∈ base.freeVars, i < 2 * width)
    (haccept : accept.QuantifierFree) (hacceptVars : ∀ i ∈ accept.freeVars, i < width)
    (hEdge : ∀ source target,
      templateEdge base source target ↔ codec.liftRelation edge source target)
    (hAccept : ∀ bits, templateAccepts accept bits ↔ codec.liftPredicate accepts bits)
    (initial : α) :
    EncodedTruePrenex (encodeAcceptingReachability base accept (codec.encode initial)) ↔
      ∃ final, accepts final ∧ Relation.ReflTransGen edge initial final := by
  rw [encodedTruePrenex_encodeAcceptingReachability_iff base accept hbase hbaseVars
    haccept hacceptVars]
  have hrel : templateEdge (width := width) base = codec.liftRelation edge := by
    funext source target
    exact propext (hEdge source target)
  simp only [hrel, hAccept]
  exact codec.liftRelation_accepting_reachable_iff edge accepts initial

end IPPSPACE

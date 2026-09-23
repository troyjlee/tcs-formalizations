/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Lean

/-!
# Enforced axiom inventory

The audit accepts only the ordinary classical axioms. Missing declarations
and additional axioms are build errors, including when a proof reaches
`sorryAx` transitively. This command inspects the elaborated environment;
it introduces no mathematical axiom.
-/

open Lean Elab Command in
elab "#check_tsp_axioms " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"

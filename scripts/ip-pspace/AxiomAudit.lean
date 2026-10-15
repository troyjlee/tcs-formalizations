/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee

The module-origin audit follows Samuel Schlesinger's Complexitylib AxiomGuard
(Apache-2.0, revision recorded in vendor/UPSTREAM.json).
-/
import IPPSPACE
import Lean

/-!
Audit every declaration originating in the project and all imported Complexitylib/CSLib modules,
including private/generated declarations, and traverse their axiom dependencies.
This trusts the compiled environment and is not an independent kernel checker.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if (`IPPSPACE).isPrefixOf moduleName || (`Complexitylib).isPrefixOf moduleName ||
        (`Cslib).isPrefixOf moduleName then
      let moduleData := env.header.moduleData[moduleIdx]
      unless moduleData.constNames.size == moduleData.constants.size do
        throwError "Malformed declaration table for {moduleName}"
      for h : idx in *...moduleData.constants.size do
        let name := moduleData.constNames[idx]!
        count := count + 1
        match moduleData.constants[idx] with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | _ => pure ()
        let axioms ← liftCoreM (collectAxioms name)
        let unexpected := axioms.filter fun ax => !allowed.contains ax
        unless unexpected.isEmpty do
          throwError "{name} depends on disallowed axioms: {unexpected}"
  if count == 0 then
    throwError "Audit did not find any project declarations"
  logInfo m!"Axiom audit passed: {count} declarations, including {theoremCount} theorems; only standard Lean axioms."

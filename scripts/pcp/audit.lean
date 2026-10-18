import PCP
import Lean

/-! Audit every local and vendored declaration, including private helpers.
Only the three standard logical axioms are permitted; there are no proof-hole exceptions.
The final theorem types and use of the Lemma 3.3 generator proof are also checked. -/

open Lean

namespace PCPAudit

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def auditedModule (m : Name) : Bool :=
  (`PCP).isPrefixOf m || (`Complexitylib).isPrefixOf m || (`Cslib).isPrefixOf m

def projectModules (env : Environment) : Array Name :=
  env.header.moduleNames.filter auditedModule

/-- Declarations belonging to this project or its explicitly vendored reference libraries.

Private declarations are **included**: `Name.isInternal` is true for `_private…` names, and
skipping them left unused private proof holes outside the enforced inventory. Compiler-generated
auxiliaries are included too. Every declaration must pass the same strict axiom check. -/
def projectDecls (env : Environment) : Array Name := Id.run do
  let mods := env.header.moduleNames
  let mut out := #[]
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | some idx =>
        if h : idx.toNat < mods.size then
          if auditedModule mods[idx.toNat] then out := out.push name
    | none => pure ()
  return out

/-- Follow proof bodies, including private helpers, to ensure that the generator
soundness proof is on the production route rather than merely imported. -/
def declarationUses (env : Environment) (root target : Name) : Bool := Id.run do
  let mut pending := [root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if n == target then return true
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let some body := ci.value? (allowOpaque := true) | continue
    for dep in body.getUsedConstants do
      let some idx := env.getModuleIdxFor? dep | continue
      if h : idx.toNat < env.header.moduleNames.size then
        if (`PCP).isPrefixOf env.header.moduleNames[idx.toNat] then
          pending := dep :: pending
  return false

end PCPAudit

section SignatureLock
open PCP

/-- The intended type of the forward PCP theorem, transcribed independently of the declaration. -/
def IntendedForwardType : Prop := ∀ (L : Language), InNP Machine.PolyTimeRel L →
  ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
    Machine.PolyTimeAlg alg ∧ V.ImplementedBy alg ∧ V.queries = q ∧
    V.CanonicalRandomness a b ∧
    (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
    (∀ x : List Bool, L x → V.CompleteAt x) ∧
    (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2))

/-- The intended type of the reverse lemma, transcribed independently. -/
def IntendedReverseType : Prop := ∀ (M : CostModel) (L : Language) (V : Verifier) (a b : ℕ)
    (p : Polynomial ℕ), M.Efficient V → V.CanonicalRandomness a b →
    (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) →
    (∀ x : List Bool, L x → V.CompleteAt x) →
    (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) →
    InNP M.PolyTimeRel L

/-- The declarations whose statements are locked, paired with their intended transcriptions. -/
def lockedSignatures : List (Name × Name) :=
  [(``PCP.np_subset_pcp, ``IntendedForwardType),
   (``PCP.pcp_subset_np, ``IntendedReverseType),
   (``PCP.ReferenceNP.to_inNP, ``PCP.Audit.ReferenceNP.IntendedInclusionType),
   (``PCP.ReferenceNP.of_inNP, ``PCP.Audit.ReferenceNP.IntendedConverseType),
   (``PCP.ReferenceNP.inNP_iff_mem, ``PCP.Audit.ReferenceNP.IntendedEquivalenceType),
   (``PCP.ReferenceNP.np_subset_pcp, ``PCP.Audit.ReferenceNP.IntendedPCPType),
   (``PCP.Algebraic.GeneratorLowDegreeTest.exists_close,
     ``PCP.Audit.GeneratorLowDegree.IntendedSoundnessType),
   (``PCP.Algebraic.GeneratorLowDegreeTest.check_eq_zero_iff_exists_polynomial,
     ``PCP.Audit.GeneratorLowDegree.IntendedCharacterizationType)]

end SignatureLock

open PCPAudit Lean.Elab.Command in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let decls := projectDecls env
  let mut errors : Array String := #[]
  for d in decls do
    let axioms ← liftCoreM (collectAxioms d)
    for a in axioms do
      unless allowedAxioms.contains a do
        errors := errors.push s!"{d} depends on forbidden axiom {a}"

  -- Signature lock: each production declaration must have exactly its transcribed type.
  for (decl, intended) in lockedSignatures do
    let some di := env.find? decl | errors := errors.push s!"locked declaration {decl} is missing"
    let some ii := env.find? intended
      | errors := errors.push s!"transcription {intended} is missing"
    let some intendedStmt := ii.value? | errors := errors.push s!"{intended} has no value"
    let ok ← liftTermElabM (Meta.isDefEq di.type intendedStmt)
    unless ok do
      errors := errors.push
        s!"SIGNATURE DRIFT: {decl} no longer matches its transcription {intended}"

  -- These are checks of elaborated proof dependencies, not import dependencies.
  for root in [``PCP.Algebraic.BinaryLocalRowDecoding.exists_polynomial_distance_le,
      ``PCP.np_subset_pcp, ``PCP.ReferenceNP.np_subset_pcp] do
    unless declarationUses env root ``PCP.Algebraic.GeneratorLowDegreeTest.exists_close do
      errors := errors.push
        s!"LEMMA 3.3 PROOF DISCONNECTED: {root} does not use generator soundness"
  for oldProof in [``PCP.Algebraic.pointLineSoundness_largeField,
      ``PCP.Algebraic.PointLineTest.exists_close_of_small_rejection] do
    if declarationUses env ``PCP.Algebraic.GeneratorLowDegreeTest.exists_close oldProof then
      errors := errors.push s!"LEMMA 3.3 PROOF DEPENDENCY: generator soundness uses {oldProof}"

  for oldModule in [`PCP.Algebraic.InterpolationTestGeneratorSoundness,
      `PCP.Algebraic.InterpolationTestSoundness, `PCP.Algebraic.RepairedLowDegreeSoundness,
      `PCP.CSP.Basic] do
    if env.header.moduleNames.contains oldModule then
      errors := errors.push s!"EXCLUDED MODULE IMPORTED: {oldModule}"

  let mods := projectModules env
  logInfo s!"inspected {decls.size} project declarations in {mods.size} modules; \
    no proof holes or extra axioms permitted; {lockedSignatures.length} signatures locked"
  for m in mods do
    IO.println s!"MODULE {m}"
  unless errors.isEmpty do
    throwError "AUDIT FAILED:\n{"\n".intercalate errors.toList}"
  logInfo "AUDIT PASSED"

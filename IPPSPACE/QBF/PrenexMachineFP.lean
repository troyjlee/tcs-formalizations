/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexMachineEncoding
import IPPSPACE.QBF.SyntaxChildrenFP
import IPPSPACE.QBF.PrenexRunBounds

/-!
# Machine-based polynomial-time prenex worklist execution

The total encoded transition uses only binary names, persistent pair stacks,
scoped lookup, immediate syntax children, and local prefix assembly. The proved
polynomial storage bound and linear iteration ruler give an actual upstream FP
certificate for the exact existing capture-safe `toPrenex` converter.
-/

namespace IPPSPACE

open Complexity

def prenexVisitTaskBits (formula env : List Bool) : List Bool :=
  [false, false, false] ++ pair formula env

def prenexQuantifyTaskBits (q fresh : List Bool) : List Bool :=
  [true, false, false] ++ pair q fresh

def prenexAtomDataBits (matrix next : List Bool) : List Bool :=
  pair [] (pair matrix next)

def prenexNegDataBits (value : List Bool) : List Bool :=
  pair (dualQuantifierPrefixBits (pairFst value))
    (pair ([false, true, true] ++ pairFst (pairSnd value)) (pairSnd (pairSnd value)))

def prenexBinaryDataBits (tag left right : List Bool) : List Bool :=
  pair (pairFst left ++ pairFst right)
    (pair (tag ++ pairFst (pairSnd left) ++ pairFst (pairSnd right)) (pairSnd (pairSnd right)))

def prenexQuantifyDataBits (q fresh child : List Bool) : List Bool :=
  pair ((q.take 3 ++ frameNameBits fresh) ++ pairFst child)
    (pair (pairFst (pairSnd child)) (pairSnd (pairSnd child)))

theorem packPrenexMachineState_mem_FP {next tasks values : List Bool → List Bool}
    (hn : next ∈ FP) (ht : tasks ∈ FP) (hv : values ∈ FP) :
    (fun z => packPrenexMachineState (next z) (tasks z) (values z)) ∈ FP :=
  mem_FP_pair hn (mem_FP_pair ht hv)

theorem prenexVisitTaskBits_mem_FP {formula env : List Bool → List Bool}
    (hf : formula ∈ FP) (he : env ∈ FP) :
    (fun z => prenexVisitTaskBits (formula z) (env z)) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP _) (mem_FP_pair hf he)

theorem prenexQuantifyTaskBits_mem_FP {q fresh : List Bool → List Bool}
    (hq : q ∈ FP) (hf : fresh ∈ FP) :
    (fun z => prenexQuantifyTaskBits (q z) (fresh z)) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP _) (mem_FP_pair hq hf)

theorem prenexAtomDataBits_mem_FP {matrix next : List Bool → List Bool}
    (hm : matrix ∈ FP) (hn : next ∈ FP) :
    (fun z => prenexAtomDataBits (matrix z) (next z)) ∈ FP :=
  mem_FP_pair (constFn_mem_FP []) (mem_FP_pair hm hn)

theorem prenexNegDataBits_mem_FP {value : List Bool → List Bool} (hv : value ∈ FP) :
    (fun z => prenexNegDataBits (value z)) ∈ FP :=
  mem_FP_pair (dualQuantifierPrefixBits_mem_FP (mem_FP_comp hv pairFst_mem_FP))
    (mem_FP_pair (Cobham.appendFn_mem_FP (constFn_mem_FP _)
      (mem_FP_comp (mem_FP_comp hv pairSnd_mem_FP) pairFst_mem_FP))
      (mem_FP_comp (mem_FP_comp hv pairSnd_mem_FP) pairSnd_mem_FP))

theorem prenexBinaryDataBits_mem_FP {tag left right : List Bool → List Bool}
    (htag : tag ∈ FP) (hl : left ∈ FP) (hr : right ∈ FP) :
    (fun z => prenexBinaryDataBits (tag z) (left z) (right z)) ∈ FP :=
  mem_FP_pair (Cobham.appendFn_mem_FP (mem_FP_comp hl pairFst_mem_FP) (mem_FP_comp hr pairFst_mem_FP))
    (mem_FP_pair (Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP htag
      (mem_FP_comp (mem_FP_comp hl pairSnd_mem_FP) pairFst_mem_FP))
      (mem_FP_comp (mem_FP_comp hr pairSnd_mem_FP) pairFst_mem_FP))
      (mem_FP_comp (mem_FP_comp hr pairSnd_mem_FP) pairSnd_mem_FP))

theorem prenexQuantifyDataBits_mem_FP {q fresh child : List Bool → List Bool}
    (hq : q ∈ FP) (hf : fresh ∈ FP) (hc : child ∈ FP) :
    (fun z => prenexQuantifyDataBits (q z) (fresh z) (child z)) ∈ FP :=
  mem_FP_pair (Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (take_mem_FP hq (UnaryFn.const 3)) (frameNameBits_mem_FP hf))
    (mem_FP_comp hc pairFst_mem_FP))
    (mem_FP_pair (mem_FP_comp (mem_FP_comp hc pairSnd_mem_FP) pairFst_mem_FP)
      (mem_FP_comp (mem_FP_comp hc pairSnd_mem_FP) pairSnd_mem_FP))

@[simp] theorem prenexAtomDataBits_encode (matrix : QBF) (next : ℕ) :
    prenexAtomDataBits (encodeQBF matrix) next.bits = encodeScopedPrenexData ⟨[], matrix, next⟩ := rfl

@[simp] theorem prenexNegDataBits_encode (value : ScopedPrenexData) :
    prenexNegDataBits (encodeScopedPrenexData value) = encodeScopedPrenexData value.neg := by
  simp [prenexNegDataBits, encodeScopedPrenexData, ScopedPrenexData.neg,
    dualQuantifierPrefixBits_encode, encodeQBF]

@[simp] theorem prenexBinaryDataBits_encode (op : QBFConnective) (left right : ScopedPrenexData) :
    prenexBinaryDataBits (match op with | .conj => [true, false, false] | .disj => [true, false, true])
      (encodeScopedPrenexData left) (encodeScopedPrenexData right) =
      encodeScopedPrenexData (left.binary op right) := by
  cases op <;> simp [prenexBinaryDataBits, encodeScopedPrenexData, ScopedPrenexData.binary,
    QBFConnective.formula, encodeQBF]

@[simp] theorem prenexQuantifyDataBits_encode (q : Quantifier) (fresh : ℕ) (child : ScopedPrenexData) :
    prenexQuantifyDataBits q.token.encode fresh.bits (encodeScopedPrenexData child) =
      encodeScopedPrenexData (child.quantify q fresh) := by
  cases q <;> simp [prenexQuantifyDataBits, encodeScopedPrenexData, ScopedPrenexData.quantify,
    Quantifier.withIndex, Quantifier.token, SyntaxToken.encode, encodeNatName]

/-- A raw visit dispatches on the source constructor, keeping its lexical
scope with each saved child. Only binder entry increments the binary counter. -/
def prenexVisitBitsStep (next tasks values formula env : List Bool) : List Bool :=
  let first := syntaxFirstChildBits formula
  let second := syntaxSecondChildBits formula
  let name := syntaxTokenNameDigits formula
  if formula.take 3 = [false, false, false] then
    packPrenexMachineState next tasks
      (pair (prenexAtomDataBits ([false, false, false] ++ frameNameBits (nameEnvironmentLookupBits name env)) next) values)
  else if formula.take 3 = [false, false, true] then
    packPrenexMachineState next tasks (pair (prenexAtomDataBits [false, false, true] next) values)
  else if formula.take 3 = [false, true, false] then
    packPrenexMachineState next tasks (pair (prenexAtomDataBits [false, true, false] next) values)
  else if formula.take 3 = [false, true, true] then
    packPrenexMachineState next (pair (prenexVisitTaskBits first env) (pair [false, false, true] tasks)) values
  else if formula.take 3 = [true, false, false] then
    packPrenexMachineState next
      (pair (prenexVisitTaskBits first env) (pair (prenexVisitTaskBits second env) (pair [false, true, false] tasks))) values
  else if formula.take 3 = [true, false, true] then
    packPrenexMachineState next
      (pair (prenexVisitTaskBits first env) (pair (prenexVisitTaskBits second env) (pair [false, true, true] tasks))) values
  else if formula.take 3 = [true, true, false] ∨ formula.take 3 = [true, true, true] then
    packPrenexMachineState (nameBitsValue next + 1).bits
      (pair (prenexVisitTaskBits first (pair (pair name next) env))
        (pair (prenexQuantifyTaskBits (syntaxTokenBits formula) next) tasks)) values
  else packPrenexMachineState next [] []

/-- Total encoded transition; malformed control/underflow follows the typed
machine's terminal failure state on every canonical internal configuration. -/
def prenexMachineBitsStep (bits : List Bool) : List Bool :=
  let next := prenexStateNextBits bits
  let tasks := prenexStateTasks bits
  let values := prenexStateValues bits
  let task := pairFst tasks
  let rest := pairSnd tasks
  let payload := task.drop 3
  let top := pairFst values
  let more := pairSnd values
  if tasks = [] then bits
  else if task.take 3 = [false, false, false] then
    prenexVisitBitsStep next rest values (pairFst payload) (pairSnd payload)
  else if task.take 3 = [false, false, true] then
    if values = [] then packPrenexMachineState next [] []
    else packPrenexMachineState next rest (pair (prenexNegDataBits top) more)
  else if task.take 3 = [false, true, false] then
    if values = [] ∨ more = [] then packPrenexMachineState next [] []
    else packPrenexMachineState next rest
      (pair (prenexBinaryDataBits [true, false, false] (pairFst more) top) (pairSnd more))
  else if task.take 3 = [false, true, true] then
    if values = [] ∨ more = [] then packPrenexMachineState next [] []
    else packPrenexMachineState next rest
      (pair (prenexBinaryDataBits [true, false, true] (pairFst more) top) (pairSnd more))
  else if task.take 3 = [true, false, false] then
    if values = [] then packPrenexMachineState next [] []
    else packPrenexMachineState next rest
      (pair (prenexQuantifyDataBits (pairFst payload) (pairSnd payload) top) more)
  else packPrenexMachineState next [] []

theorem prenexVisitBitsStep_mem_FP {next tasks values formula env : List Bool → List Bool}
    (hn : next ∈ FP) (ht : tasks ∈ FP) (hv : values ∈ FP)
    (hf : formula ∈ FP) (he : env ∈ FP) :
    (fun z => prenexVisitBitsStep (next z) (tasks z) (values z) (formula z) (env z)) ∈ FP := by
  have htag (tag : List Bool) := bitStrings_eq_fppred (take_mem_FP hf (UnaryFn.const 3))
    (constFn_mem_FP tag)
  have hfirst := syntaxFirstChildBits_mem_FP hf
  have hsecond := syntaxSecondChildBits_mem_FP hf
  have hname := syntaxTokenNameDigits_mem_FP hf
  have hvisitfirst := prenexVisitTaskBits_mem_FP hfirst he
  have hvisitsecond := prenexVisitTaskBits_mem_FP hsecond he
  have hleaf := prenexAtomDataBits_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false, false, false])
      (frameNameBits_mem_FP (nameEnvironmentLookupBits_mem_FP hname he))) hn
  have hbind := packPrenexMachineState_mem_FP (nameBitsValue_succ_bits_mem_FP hn)
    (mem_FP_pair (prenexVisitTaskBits_mem_FP hfirst (mem_FP_pair (mem_FP_pair hname hn) he))
      (mem_FP_pair (prenexQuantifyTaskBits_mem_FP (syntaxTokenBits_mem_FP hf) hn) ht)) hv
  exact (htag [false, false, false]).ite_mem_FP
    (packPrenexMachineState_mem_FP hn ht (mem_FP_pair hleaf hv))
    ((htag [false, false, true]).ite_mem_FP
      (packPrenexMachineState_mem_FP hn ht
        (mem_FP_pair (prenexAtomDataBits_mem_FP (constFn_mem_FP [false, false, true]) hn) hv))
      ((htag [false, true, false]).ite_mem_FP
        (packPrenexMachineState_mem_FP hn ht
          (mem_FP_pair (prenexAtomDataBits_mem_FP (constFn_mem_FP [false, true, false]) hn) hv))
        ((htag [false, true, true]).ite_mem_FP
          (packPrenexMachineState_mem_FP hn
            (mem_FP_pair hvisitfirst (mem_FP_pair (constFn_mem_FP [false, false, true]) ht)) hv)
          ((htag [true, false, false]).ite_mem_FP
            (packPrenexMachineState_mem_FP hn
              (mem_FP_pair hvisitfirst (mem_FP_pair hvisitsecond
                (mem_FP_pair (constFn_mem_FP [false, true, false]) ht))) hv)
            ((htag [true, false, true]).ite_mem_FP
              (packPrenexMachineState_mem_FP hn
                (mem_FP_pair hvisitfirst (mem_FP_pair hvisitsecond
                  (mem_FP_pair (constFn_mem_FP [false, true, true]) ht))) hv)
              (((htag [true, true, false]).or (htag [true, true, true])).ite_mem_FP hbind
                (packPrenexMachineState_mem_FP hn (constFn_mem_FP []) (constFn_mem_FP []))))))))

/-- Actual FP certificate for the full total encoded worklist transition. -/
theorem prenexMachineBitsStep_mem_FP : prenexMachineBitsStep ∈ FP := by
  have hid : (id : List Bool → List Bool) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hn : prenexStateNextBits ∈ FP := pairFst_mem_FP
  have ht : prenexStateTasks ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hv : prenexStateValues ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have htask := mem_FP_comp ht pairFst_mem_FP
  have hrest := mem_FP_comp ht pairSnd_mem_FP
  have hpayload := drop_mem_FP htask (UnaryFn.const 3)
  have htop := mem_FP_comp hv pairFst_mem_FP
  have hmore := mem_FP_comp hv pairSnd_mem_FP
  have htag (tag : List Bool) := bitStrings_eq_fppred (take_mem_FP htask (UnaryFn.const 3))
    (constFn_mem_FP tag)
  have hempty := bitStrings_eq_fppred hv (constFn_mem_FP [])
  have hshort := hempty.or (bitStrings_eq_fppred hmore (constFn_mem_FP []))
  have hfail := packPrenexMachineState_mem_FP hn (constFn_mem_FP []) (constFn_mem_FP [])
  have hbinary (tag : List Bool) := packPrenexMachineState_mem_FP hn hrest
    (mem_FP_pair (prenexBinaryDataBits_mem_FP (constFn_mem_FP tag)
      (mem_FP_comp hmore pairFst_mem_FP) htop) (mem_FP_comp hmore pairSnd_mem_FP))
  exact (bitStrings_eq_fppred ht (constFn_mem_FP [])).ite_mem_FP hid
    ((htag [false, false, false]).ite_mem_FP
      (prenexVisitBitsStep_mem_FP hn hrest hv (mem_FP_comp hpayload pairFst_mem_FP)
        (mem_FP_comp hpayload pairSnd_mem_FP))
      ((htag [false, false, true]).ite_mem_FP
        (hempty.ite_mem_FP hfail
          (packPrenexMachineState_mem_FP hn hrest (mem_FP_pair (prenexNegDataBits_mem_FP htop) hmore)))
        ((htag [false, true, false]).ite_mem_FP
          (hshort.ite_mem_FP hfail (hbinary [true, false, false]))
          ((htag [false, true, true]).ite_mem_FP
            (hshort.ite_mem_FP hfail (hbinary [true, false, true]))
            ((htag [true, false, false]).ite_mem_FP
              (hempty.ite_mem_FP hfail (packPrenexMachineState_mem_FP hn hrest
                (mem_FP_pair (prenexQuantifyDataBits_mem_FP
                  (mem_FP_comp hpayload pairFst_mem_FP) (mem_FP_comp hpayload pairSnd_mem_FP) htop) hmore)))
              hfail)))))

private theorem prenex_pair_ne_nil (left right : List Bool) : pair left right ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [pair_length, List.length_nil] at hl
  omega

private theorem prenex_source_var_name (name : ℕ) :
    syntaxTokenNameDigits (encodeQBF (.var name)) = name.bits := by
  simpa only [encodeQBF, List.append_nil] using
    syntaxTokenNameDigits_named [false, false, false] rfl name []

private theorem prenex_source_ex_name (name : ℕ) (body : QBF) :
    syntaxTokenNameDigits (encodeQBF (.ex name body)) = name.bits := by
  exact syntaxTokenNameDigits_named [true, true, false] rfl name (encodeQBF body)

private theorem prenex_source_all_name (name : ℕ) (body : QBF) :
    syntaxTokenNameDigits (encodeQBF (.all name body)) = name.bits := by
  exact syntaxTokenNameDigits_named [true, true, true] rfl name (encodeQBF body)

private theorem prenex_source_ex_token (name : ℕ) (body : QBF) :
    syntaxTokenBits (encodeQBF (.ex name body)) = (SyntaxToken.ex name).encode :=
  syntaxTokenBits_encode (.ex name) (encodeQBF body)

private theorem prenex_source_all_token (name : ℕ) (body : QBF) :
    syntaxTokenBits (encodeQBF (.all name body)) = (SyntaxToken.all name).encode :=
  syntaxTokenBits_encode (.all name) (encodeQBF body)

/-- The visit transition has the exact typed worklist behavior, including
saved sibling environments and the binder's binary fresh counter. -/
theorem prenexVisitBitsStep_encode (formula : QBF) (env : List (ℕ × ℕ))
    (tasks : List PrenexTask) (values : List ScopedPrenexData) (next : ℕ) :
    prenexVisitBitsStep next.bits (encodePrenexTasks tasks) (encodePrenexValues values)
      (encodeQBF formula) (encodeNameEnvironment env) =
      encodePrenexMachineState (prenexMachineStep ⟨.visit formula env :: tasks, values, next⟩) := by
  cases formula <;>
    simp only [prenexVisitBitsStep, syntaxFirstChildBits_encodeQBF, syntaxSecondChildBits_encodeQBF,
      qbfChildren, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      prenex_source_var_name, prenex_source_ex_name, prenex_source_all_name,
      prenex_source_ex_token, prenex_source_all_token] <;>
    simp [prenexMachineStep, encodePrenexMachineState, encodePrenexTasks,
      encodePrenexValues, encodePrenexTask, prenexVisitTaskBits, prenexQuantifyTaskBits,
      packPrenexMachineState, prenexAtomDataBits, encodeScopedPrenexData,
      encodeQBF, encodeNatName, encodeNameEnvironment, Quantifier.token]

/-- The total raw transition refines the typed machine on all encoded states,
including empty worklists and malformed assembly stacks. -/
theorem prenexMachineBitsStep_encode (state : PrenexMachineState) :
    prenexMachineBitsStep (encodePrenexMachineState state) =
      encodePrenexMachineState (prenexMachineStep state) := by
  rcases state with ⟨tasks, values, next⟩
  cases tasks with
  | nil => simp [prenexMachineBitsStep, prenexMachineStep]
  | cons task tasks =>
    simp only [prenexMachineBitsStep, prenexStateNextBits_encode, prenexStateTasks_encode,
      prenexStateValues_encode, encodePrenexTasks, pairFst_pair, pairSnd_pair,
      prenex_pair_ne_nil, ↓reduceIte]
    cases task with
    | visit formula env =>
      simpa [encodePrenexTask] using prenexVisitBitsStep_encode formula env tasks values next
    | neg =>
      cases values <;> simp [prenexMachineStep,
        encodePrenexValues, encodePrenexTask, prenex_pair_ne_nil,
        packPrenexMachineState, encodePrenexMachineState, PrenexMachineState.fail]
    | binary op =>
      cases values with
      | nil => cases op <;> simp [prenexMachineStep,
          encodePrenexValues, encodePrenexTask, packPrenexMachineState,
          encodePrenexMachineState, PrenexMachineState.fail]
      | cons right values => cases values with
        | nil => cases op <;> simp [prenexMachineStep,
            encodePrenexValues, encodePrenexTask, prenex_pair_ne_nil, packPrenexMachineState,
            encodePrenexMachineState, PrenexMachineState.fail]
        | cons left values => cases op <;>
            simp [prenexMachineStep,
              encodePrenexValues, encodePrenexTask, prenex_pair_ne_nil,
              prenexBinaryDataBits, ScopedPrenexData.binary, encodeScopedPrenexData,
              QBFConnective.formula, encodeQBF,
              packPrenexMachineState, encodePrenexMachineState]
    | quantify q fresh =>
      cases values <;> simp [prenexMachineStep,
        encodePrenexValues, encodePrenexTask, prenex_pair_ne_nil,
        packPrenexMachineState, encodePrenexMachineState, PrenexMachineState.fail]

/-- Iteration of the certified transition, under a polynomial bound on the
entire typed state encoding. The bound is a storage fact, not a runtime oracle. -/
theorem prenexMachineRun_mem_FP_of_bound {state : List Bool → PrenexMachineState}
    {steps : List Bool → ℕ} (hstate : (fun z => encodePrenexMachineState (state z)) ∈ FP)
    (hsteps : UnaryFn steps) {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hsize : ∀ z n, n ≤ steps z →
      (encodePrenexMachineState (prenexMachineRun n (state z))).length ≤ bound z.length) :
    (fun z => encodePrenexMachineState (prenexMachineRun (steps z) (state z))) ∈ FP := by
  have hsemi : Function.Semiconj encodePrenexMachineState prenexMachineStep prenexMachineBitsStep :=
    fun state => (prenexMachineBitsStep_encode state).symm
  have h := iterate_mem_FP_of_polyBound prenexMachineBitsStep_mem_FP hstate hsteps.mem_FP hbound
    (fun z n hn => by
      rw [← hsemi.iterate_right n (state z)]
      exact hsize z n (by simpa using hn))
  apply mem_FP_of_eq h
  intro z
  simp only [List.length_replicate]
  exact (hsemi.iterate_right (steps z) (state z)).symm

theorem prenexMachineInitial_mem_FP {formula : List Bool → QBF}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) :
    (fun z => encodePrenexMachineState (prenexMachineInitial (formula z))) ∈ FP :=
  packPrenexMachineState_mem_FP (prenexStart_bits_mem_FP hformula)
    (mem_FP_pair (prenexVisitTaskBits_mem_FP hformula (constFn_mem_FP [])) (constFn_mem_FP []))
    (constFn_mem_FP [])

/-- The completed top payload is written as ordinary prefix-then-matrix syntax. -/
def prenexMachineOutputBits (bits : List Bool) : List Bool :=
  let values := prenexStateValues bits
  let value := pairFst values
  if values = [] then encodeQBF .fls
  else pairFst value ++ pairFst (pairSnd value)

theorem prenexMachineOutputBits_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => prenexMachineOutputBits (bits z)) ∈ FP := by
  have hv := mem_FP_comp (mem_FP_comp hbits pairSnd_mem_FP) pairSnd_mem_FP
  have htop := mem_FP_comp hv pairFst_mem_FP
  exact (bitStrings_eq_fppred hv (constFn_mem_FP [])).ite_mem_FP (constFn_mem_FP _)
    (Cobham.appendFn_mem_FP (mem_FP_comp htop pairFst_mem_FP)
      (mem_FP_comp (mem_FP_comp htop pairSnd_mem_FP) pairFst_mem_FP))

@[simp] theorem prenexMachineOutputBits_encode (state : PrenexMachineState) :
    prenexMachineOutputBits (encodePrenexMachineState state) = encodeQBF (prenexMachineOutput state) := by
  rcases state with ⟨tasks, values, next⟩
  simp only [prenexMachineOutputBits, prenexStateValues_encode, prenexMachineOutput]
  cases values <;> simp [encodePrenexValues, prenex_pair_ne_nil, encodeScopedPrenexData,
    encodeQBF_prefixQBF_tokens]

/-- The exact existing capture-safe prenex converter is polynomial-time in the
binary source encoding. Fresh names are never expanded to unary, and the
worklist machine uses the proved polynomial storage bound at every step. -/
theorem encode_toPrenex_mem_FP {formula : List Bool → QBF}
    (hformula : (fun z => encodeQBF (formula z)) ∈ FP) :
    (fun z => encodeQBF (toPrenex (formula z)).toQBF) ∈ FP := by
  have hnode : UnaryFn fun z => nodeCount (formula z) :=
    (decodeQBF_nodeCount_unaryFn hformula).of_eq (fun z => by simp)
  have hsteps := (UnaryFn.const 2).mul hnode
  obtain ⟨P, hP⟩ := Cobham.output_length_poly_of_mem_FP hformula
  have hbound : PolyBound fun n => 8192 * (P.eval n + 1) ^ 3 :=
    (PolyBound.const 8192).mul (((PolyBound.eval P).add (PolyBound.const 1)).pow 3)
  have hrun := prenexMachineRun_mem_FP_of_bound (prenexMachineInitial_mem_FP hformula) hsteps
    hbound (fun z n hn => by
      have hlen : n ≤ 2 * (encodeQBF (formula z)).length :=
        hn.trans (Nat.mul_le_mul_left 2 (nodeCount_le_length_encodeQBF (formula z)))
      exact (prenexMachineRun_initial_length_le (formula z) n hlen).trans
        (Nat.mul_le_mul_left 8192 (Nat.pow_le_pow_left (Nat.add_le_add_right (hP z) 1) 3)))
  apply mem_FP_of_eq (prenexMachineOutputBits_mem_FP hrun)
  intro z
  rw [prenexMachineOutputBits_encode, prenexMachineOutput_eq_toPrenex]

/-- Preserve the full converted formula with a success tag; reject malformed
and trailing source input using the original complete QBF decoder. -/
def decodeToPrenexOutput (bits : List Bool) : List Bool :=
  match decodeQBF bits with
  | none => []
  | some formula => true :: encodeQBF (toPrenex formula).toQBF

theorem decodeToPrenexOutput_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    (fun z => decodeToPrenexOutput (bits z)) ∈ FP := by
  have hconvert := encode_toPrenex_mem_FP (encode_decodeQBF_getD_mem_FP .fls hbits)
  apply mem_FP_of_eq ((decodeQBF_success_fppred hbits).ite_mem_FP
    (mem_FP_comp hconvert (Cobham.cons_mem_FP true)) (constFn_mem_FP []))
  intro z
  cases hd : decodeQBF (bits z) <;> simp [decodeToPrenexOutput, hd]

@[simp] theorem decodeToPrenexOutput_encode (formula : QBF) :
    decodeToPrenexOutput (encodeQBF formula) = true :: encodeQBF (toPrenex formula).toQBF := by
  simp [decodeToPrenexOutput]

theorem decodeToPrenexOutput_eq_nil_iff (bits : List Bool) :
    decodeToPrenexOutput bits = [] ↔ decodeQBF bits = none := by
  cases hd : decodeQBF bits <;> simp [decodeToPrenexOutput, hd]

end IPPSPACE

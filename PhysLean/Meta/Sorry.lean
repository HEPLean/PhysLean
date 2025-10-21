/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Linters.Sorry
/-!

# Meta results regarding `sorry` and `psuedo` attributions

Some of the code here is adapted from from the file: Lean.Util.CollectAxioms
copyright (c) 2020 Microsoft Corporation. Authored by Leonardo de Moura.

-/
open Lean
namespace PhysLean

namespace CollectSorry

/-- A structure used for collecting names of results dependent on the
  `sorryAx` axiom and the `Lean.ofReduceBool` axiom. -/
structure State where
  /-- The names which have already been visited as part of the state. -/
  visited : NameSet := {}
  /-- The names which depend on the `sorryAx` axiom. -/
  containsSorry : NameSet := {}
  /-- The names which depend on the `Lean.ofReduceBool` axiom. -/
  containsOfReduceBool : NameSet := {}

/-- A monad used for collecting names of results dependent on the
  `sorryAx` axiom and the `Lean.ofReduceBool` axiom. -/
abbrev M := ReaderT Environment $ StateM State

/-- Given a `c : Name` updating the monad `M` based on which results which `c` uses
  depend on the `sorryAx` axiom and the `Lean.ofReduceBool` axiom. -/
partial def collect (c : Name) (parents : NameSet) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM fun x =>
    collect x (parents.insert c)
  let s ← get

  if s.containsSorry.contains c then
    modify fun s => { s with containsSorry := s.containsSorry.append parents}
  if s.containsOfReduceBool.contains c then
    modify fun s => { s with containsOfReduceBool := s.containsOfReduceBool.append parents}
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    -- We should take the constant from the kernel env, which may differ from the one in the elab
    -- env in case of (async) errors.
    match env.checked.get.find? c with
    | some (ConstantInfo.axiomInfo v) =>
        if v.name == ``sorryAx then
            modify fun s => { s with containsSorry := s.containsSorry.append (parents.insert c) }
        if v.name == ``Lean.ofReduceBool then
            modify fun s => { s with containsOfReduceBool :=
              s.containsOfReduceBool.append (parents.insert c)}
        collectExpr v.type
    | some (ConstantInfo.defnInfo v) =>
        collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.thmInfo v) =>
        collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) =>
        collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.quotInfo _) => pure ()
    | some (ConstantInfo.ctorInfo v) =>
        collectExpr v.type
    | some (ConstantInfo.recInfo v) =>
        collectExpr v.type
    | some (ConstantInfo.inductInfo v) =>
        collectExpr v.type *> v.ctors.forM fun x => collect x (parents.insert c)
    | none => pure ()

/-- Given a `c : Array Name` updating the monad `M` based on which results
  depend on the `sorryAx` axiom and the `Lean.ofReduceBool` axiom. -/
partial def allSorryPseudo (c : Array Name) : M Unit := do
  c.forM fun x => collect x {}

end CollectSorry

/-- Given a `c : Array Name` the names of all results used to defined
  the results in `c` with the `sorryAx` axiom and the `Lean.ofReduceBool` axiom. -/
def collectSorryPseudo (c : Array Name) : CoreM (Array Name × Array Name) := do
  let env ← getEnv
  let (_, s) := ((CollectSorry.allSorryPseudo c).run env).run {}
  pure (s.containsSorry.toArray, s.containsOfReduceBool.toArray)

/-- The axioms of a constant. -/
def allWithSorryPseudo : CoreM (Array Name × Array Name) := do
  let x ← collectSorryPseudo ((← allUserConsts).map fun c => c.name)
  return x

/-- All names which are attributed `sorryful`. -/
unsafe def allSorryfulAttributed : CoreM (Array Name) := do
  let env ← getEnv
  let sorryfulInfos := (sorryfulExtension.getState env)
  return sorryfulInfos.map fun info => info.name

/-- All names which are attributed `psuedo`. -/
unsafe def allPseudoAttributed : CoreM (Array Name) := do
  let env ← getEnv
  let pseudoInfos := (pseudoExtension.getState env)
  return pseudoInfos.map fun info => info.name

/-- Checks whether all results attributed `sorryful` depend on the ```sorryAx`
  axiom and vice versa. -/
unsafe def sorryfulPseudoTest : MetaM Unit := do
  let (allWithSorry, allWithPsuedo) ← PhysLean.allWithSorryPseudo
  let allConst ← PhysLean.allUserConsts
  let allConst := allConst.map fun c => c.name
  let allWithSorry := allWithSorry.filter fun n => n ∈ allConst
  let allWithPsuedo := allWithPsuedo.filter fun n => n ∈ allConst
  let sorryAttributed ← allSorryfulAttributed
  let psuedoAttributed ← allPseudoAttributed
  let withSorryAxiomNotAttributed :=
    allWithSorry.filter fun x => ¬ x ∈ sorryAttributed
  let withPsuedoAxiomNotAttributed :=
    allWithPsuedo.filter fun x => ¬ x ∈ psuedoAttributed
  let attributedNotWithSorryAxiom :=
    sorryAttributed.filter fun x => ¬ x ∈ allWithSorry
  let attributedNotWithPsuedoAxiom :=
    psuedoAttributed.filter fun x => ¬ x ∈ allWithPsuedo
  if withSorryAxiomNotAttributed ≠ #[] ∨ attributedNotWithSorryAxiom ≠ #[]
    ∨ withPsuedoAxiomNotAttributed ≠ #[] ∨ attributedNotWithPsuedoAxiom ≠ #[] then
    panic! s!"
\x1b[31mThere is an error in the sorryful/psuedo attribution system:\x1b[0m
  The following names depend on `sorryAx` but are not attributed `sorryful:
  {withSorryAxiomNotAttributed}
  The following names are attributed `sorryful` but do not depend on `sorryAx`:
  {attributedNotWithSorryAxiom}
  The following names depend on `Lean.ofReduceBool` but are not attributed `psuedo`:
  {withPsuedoAxiomNotAttributed}
  The following names are attributed `psuedo` but do not depend on `Lean.ofReduceBool`:
  {attributedNotWithPsuedoAxiom}"
  println! "\x1b[32mSorryful/psuedo results are all correctly attributed test passed.\x1b[0m"

end PhysLean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Tactic.Lint.Basic
import Lean.Util.CollectAxioms
/-!

# The linter for `sorry` declarations and the sorryful attribute

This module defines an attribute `sorryful` and a linter `noSorry`.

The attribute `sorryful` adds the declaration to an environment extension
`sorryfulExtension` which can be used to create TODO entries.

The linter `noSorry` checks for declarations that contain the `sorryAx` axiom
if and only if it has the `sorryful` attribute.

## Coloring `sorryful`

It is possible to color the `sorryful` attribute in VSCode.
This is part of the `.vscode/settings.json` file, but requires the `TODO Highlight` extension
to be downloaded.

-/

/-!

## The sorryful attribute

-/

open Lean

/-- The information for stored for a decleration marked with `sorryful`. -/
structure SorryfulInfo where
  /-- Name of result. -/
  name : Name

/-- An enviroment extension containing the information of declerations
  which carry the `sorryful` attribute. -/
initialize sorryfulExtension : SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  registerSimplePersistentEnvExtension {
    name := `sorryfulExtension
    addEntryFn := fun arr info => arr.push info
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Adds an entry to `sorryfulExtension`. -/
def addSorryfulEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) : m Unit :=
  modifyEnv (sorryfulExtension.addEntry · declName)

/-- The `sorryful` attribute allows declerations to contain the `sorryAx` axiom.
  In converse, a decleration with the `sorryful` attribute must contain the `sorryAx` axiom. -/
syntax (name := Sorryful_attr) "sorryful" : attr

/-- Registration of the `sorryful` attribute. -/
initialize Lean.registerBuiltinAttribute {
  name := `Sorryful_attr
  descr := "The `sorryful` attribute allows declerations to contain the `sorryAx` axiom.
    In converse, a decleration with the `sorryful` attribute must contain the `sorryAx` axiom."
  add := fun decl stx _attrKind => do
    addSorryfulEntry decl
  applicationTime := .beforeElaboration
}

/-!

## The noSorry linter

-/

namespace PhysLean.Linter

open Lean Elab

open Batteries.Tactic.Lint in
/-- The `noSorry` linter. This checks declarations contain the `sorryAx` axiom
  if and only if they have the `sorryful` attribute. -/
@[env_linter] def noSorry : Batteries.Tactic.Lint.Linter where
  noErrorsFound :=
    "A decleration which contains the `sorryAx` if and only if it has
    the `@[sorryful]` attribute. "
  errorsFound := "THE FOLLOWING RESULTS EITHER HAVE THE `sorryAx` AXIOM AND
  ARE NOT MARKED WITH THE `@[sorryful]` attribute OR DO NOT HAVE THE `sorryAx` AXIOM
  AND ARE MARKED WITH THE `@[sorryful]` attribute."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    let axioms ← collectAxioms declName
    let sorryful_results := sorryfulExtension.getState (← getEnv)
    if declName ∈ sorryful_results ↔ ``sorryAx ∈ axioms then
      return none
    return m!"contains `sorryAx` and is not marked with @[sorryful]
      or is marked with @[sorryful] and does not contain `sorryAx`."

end PhysLean.Linter

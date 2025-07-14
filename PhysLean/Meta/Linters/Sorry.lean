/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
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

## The sorryful environment extension

-/

open Lean

/-- The information for stored for a decleration marked with `sorryful`. -/
structure SorryfulInfo where
  /-- Name of result. -/
  name : Name
  /-- The docstring of the result. -/
  docstring : String
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. -/
  line : Nat

/-- An enviroment extension containing the information of declerations
  which carry the `sorryful` attribute. -/
initialize sorryfulExtension : SimplePersistentEnvExtension SorryfulInfo (Array SorryfulInfo) ←
  registerSimplePersistentEnvExtension {
    name := `sorryfulExtension
    addEntryFn := fun arr info => arr.push info
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Adds an entry to `sorryfulExtension`. -/
def addSorryfulEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (docString : String) (fileName : Name) (line : Nat) : m Unit :=
  modifyEnv (sorryfulExtension.addEntry · ⟨declName, docString, fileName, line⟩)

/-!

## The `psudo` environment extension

-/

/-- The information for stored for a decleration marked with `pseudo`. -/
structure PseudoInfo where
  /-- Name of result. -/
  name : Name

/-- An enviroment extension containing the information of declerations
  which carry the `pseudo` attribute. -/
initialize pseudoExtension : SimplePersistentEnvExtension PseudoInfo (Array PseudoInfo) ←
  registerSimplePersistentEnvExtension {
    name := `pseudoExtension
    addEntryFn := fun arr info => arr.push info
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Adds an entry to `pseudoExtension`. -/
def addPseudofulEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) : m Unit :=
  modifyEnv (pseudoExtension.addEntry · ⟨declName⟩)

/-!

## The sorryful attribute

-/

/-- The `sorryful` attribute allows declerations to contain the `sorryAx` axiom.
  In converse, a decleration with the `sorryful` attribute must contain the `sorryAx` axiom. -/
syntax (name := Sorryful_attr) "sorryful" : attr

/-- Registration of the `sorryful` attribute. -/
initialize Lean.registerBuiltinAttribute {
  name := `Sorryful_attr
  descr := "The `sorryful` attribute allows declerations to contain the `sorryAx` axiom.
    In converse, a decleration with the `sorryful` attribute must contain the `sorryAx` axiom."
  add := fun decl stx _attrKind => do
    let pos := stx.getPos?
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let nameSpace := (← getCurrNamespace)
      let docstring ← Name.getDocString decl
      addSorryfulEntry decl docstring modName line
    | none => throwError "Invalid syntax for `note` command"
  applicationTime := AttributeApplicationTime.beforeElaboration
}

/-!

## The pseudo attribute

-/

/-- The `pseudo` attribute allows declerations to contain the `Lean.ofReduceBool` axiom.
  In converse, a decleration with the `pseudo` attribute must contain the
  `Lean.ofReduceBool` axiom. -/
syntax (name := Pseudo_attr) "pseudo" : attr

/-- Registration of the `pseudo` attribute. -/
initialize Lean.registerBuiltinAttribute {
  name := `Pseudo_attr
  descr := "The `pseudo` attribute allows declerations to contain the `Lean.ofReduceBool` axiom.
    In converse, a decleration with the `pseudo` attribute must contain the
    `Lean.ofReduceBool` axiom."
  add := fun decl stx _attrKind => do
    let pos := stx.getPos?
    -- match pos with
    -- | some pos => do
      -- let env ← getEnv
      -- let fileMap ← getFileMap
      -- let filePos := fileMap.toPosition pos
      -- let line := filePos.line
      --- let modName := env.mainModule
      -- let nameSpace := (← getCurrNamespace)
      -- let docstring ← Name.getDocString decl
    addPseudofulEntry decl
  applicationTime := AttributeApplicationTime.beforeElaboration
}

/-!

## The noSorry linter

-/

namespace PhysLean.Linter

open Lean Elab

open Batteries.Tactic.Lint in
/-- The `noSorry` linter. This checks the following:
- A declaration contains the `sorryAx` axiom if and only if it has the `sorryful` attribute.
- A declaration contains the `Lean.ofReduceBool` axiom if and only if it has the `pseudo` attribute.
-/
@[env_linter] def noSorry : Batteries.Tactic.Lint.Linter where
  noErrorsFound :=
    "All declerations are marked correctly with the `@[sorryful]`
    or `@[pseudo]` attribute when needed. "
  errorsFound := "The following results either contain the `sorryAx`
    or the `Lean.ofReduceBool` axiom and are not marked with the `@[sorryful]`
    or `@[pseudo]` attribute respectively. Or they are marked with
    the `@[sorryful]` or `@[pseudo]` attribute and do not contain the
    `sorryAx` or `Lean.ofReduceBool` axiom respectively."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    let axioms ← collectAxioms declName
    let sorryful_results := sorryfulExtension.getState (← getEnv)
    let pseudo_results := pseudoExtension.getState (← getEnv)
    if (declName ∈ (sorryful_results.map fun x => x.name) ↔ ``sorryAx ∈ axioms)
      ∧ (declName ∈ (pseudo_results.map fun x => x.name) ↔ ``Lean.ofReduceBool ∈ axioms) then
      return none
    return m!"{declName} contains either
      `sorryAx` or `Lean.ofReduceBool` and is not marked with @[sorryful]
      or @[pseudo] respectively, or is marked with @[sorryful] or @[pseudo]
      and does not contain `sorryAx` or `Lean.ofReduceBool` respectively."

end PhysLean.Linter

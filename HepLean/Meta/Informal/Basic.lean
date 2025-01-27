/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lake.DSL.DeclUtil
/-!

## Informal definitions and lemmas

This file contains the necessary structures that must be imported into a file
for it to contain informal definitions and lemmas.

Everything else about informal definitions and lemmas are in the `Informal.Post` module.

-/
open Lean Parser

/-- The structure representing an informal definition. -/
structure InformalDefinition where
  /-- The name of the informal definition. This is autogenerated. -/
  name : Name
  /-- The mathematical description of the definition. -/
  math : String
  /-- The physics description of the definition. -/
  physics : String := "No physics description provided"
  /-- References. -/
  ref : String := "No references provided"
  /-- The names of top-level commands we expect this definition to depend on. -/
  deps : List Name := []

/-- The structure representing an informal proof. -/
structure InformalLemma where
  /-- The name of the informal lemma. This is autogenerated. -/
  name : Name
  /-- The mathematical description of the lemma. -/
  math : String
  /-- The physics description of the lemma. -/
  physics : String := "No physics description provided"
  /-- A description of the proof. -/
  proof : String := "No proof description provided"
  /-- References. -/
  ref : String := "No references provided"
  /-- The names of top-level commands we expect this lemma to depend on. -/
  deps : List Name := []

namespace Informal

/-!

## Syntax

See also `Lake.DSL.LeanLibDecl`.

-/

/-- An informal definition is a definition which is not type checked, and is written as a string
literal.
It can be used to plan out sections for future formalization, or to include results which the
formalization is not immediately known. Each informal definition must included a `math := "..."`
entry, but can also include the following entries `physics := "..."`, `ref := "..."`, and
`deps := [...]`. Use the attribute `note_attr_informal` from `HepLean.Meta.Notes.Basic` to mark the
informal definition as a note.
-/
elab (name := informalDefDecl)
attrs?:optional(Term.attributes)
kw:"informal_definition " sig:Lake.DSL.structDeclSig : command => withRef kw do
  Lake.DSL.elabConfigDecl ``InformalDefinition sig none (Lake.DSL.expandAttrs attrs?)

/-- An informal lemma is a lemma which is not type checked, and is written as a string literal.
It can be used to plan out sections for future formalization, or to include results which
the formalization is not immediately known. Each informal definition must included a `math := "..."`
entry, but can also include the following entries `physics := "..."`, `ref := "..."`, and
`deps := [...]`. Use the attribute `note_attr_informal` from `HepLean.Meta.Notes.Basic` to mark the
informal lemma as a note.
-/
elab (name := informalLemmaDecl)
attrs?:optional(Term.attributes)
kw:"informal_lemma " sig:Lake.DSL.structDeclSig : command => withRef kw do
  Lake.DSL.elabConfigDecl ``InformalLemma sig none (Lake.DSL.expandAttrs attrs?)

end Informal


import Mathlib.Tactic.Linter.Header


open Lean

-- higher priority to override the one in Batteries
/-- `sorryful_lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := sorryfulLemma) (priority := default + 1) declModifiers
  group("sorryful_lemma " declId ppIndent(declSig) declVal) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «sorryfulLemma»] def expandSorryFulLemma : Macro := fun stx =>
  -- Not using a macro match, to be more resilient against changes to `lemma`.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

/-!
#  The "DocString" style linter

The "DocString" linter validates style conventions regarding doc-string formatting.
-/

open Lean Elab


/--
The "DocString" linter validates style conventions regarding doc-string formatting.
-/
register_option linter.sorryLint : Bool := {
  defValue := true
  descr := "enable the style.sorryLint linter"
}

namespace PhysLean.Linter



def sorryLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.sorryLint (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let fm ← getFileMap
  let declId :=
    if stx[1].isOfKind ``Lean.Parser.Command.instance then
      stx[1][3][0]
    else
      stx[1][1]
  if let .missing := declId then return
  let declName : Name :=
    if let `_root_ :: rest := declId[0].getId.components then
      rest.foldl (· ++ ·) default
    else (← getCurrNamespace) ++ declId[0].getId
  let axioms ← collectAxioms declName
  let msg := m!"`{declName}` contains or depends on a `sorry`."
  if [`sorryfulLemma].contains stx.getKind ↔  ¬ ``sorryAx ∈ axioms then
    Linter.logLint linter.sorryLint declId msg
  else return

initialize addLinter sorryLinter


end PhysLean.Linter

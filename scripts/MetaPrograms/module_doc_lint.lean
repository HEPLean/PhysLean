/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import Mathlib.Tactic.Linter.TextBased
import Batteries.Data.Array.Merge
/-!

# Linting of module documentation

This file lints the module documentation for consistency.
It currently only checks module headings, and as such many improvements to this file could
be made.

-/

open Lean System Meta


/-!

## Checking headings

-/

structure DocLintError where
  msg : String
  file : FilePath

def getHeaddings (f : FilePath) : IO (Array String) := do
  let lines ← IO.FS.lines f
  return lines.filter (fun l ↦ l.trim.startsWith "#")

def getTableOfContents (f : FilePath) : IO (Array String) := do
  let lines := (← IO.FS.lines f).toList
  let tofC := ((lines.splitAt (lines.findIdx (fun l ↦ l.trim == "## iii. Table of contents")+1))).2
  let toc := (tofC.splitAt (tofC.findIdx (fun l ↦ l.trim == "## iv. References"))).1
  return toc.toArray

def checkHeadings (f : FilePath) : IO (List DocLintError) := do
  let headings ← getHeaddings f
  let mut errors := []
  /- Title header. -/
  let title := headings[0]?
  match title with
  | none =>
    errors := {msg := "No title heading found", file := f} :: errors
  | some t =>
    if !(t.startsWith "# ") then
      errors := {msg := s!"Title heading '{t}' does not start with '# '", file := f} :: errors
  /- Overview line header. -/
  let overview := headings[1]?
  match overview with
  | none =>
    errors := {msg := "No overview heading found", file := f} :: errors
  | some o =>
    if o ≠  "## i. Overview" then
      errors := {msg := s!"Overview heading '{o}' is not '## i. Overview'", file := f} :: errors
  /- Key results header. -/
  let keyResults := headings[2]?
  match keyResults with
  | none =>
    errors := {msg := "No key results heading found", file := f} :: errors
  | some k =>
    if k ≠ "## ii. Key results" then
      errors := {msg := s!"Key results heading '{k}' is not '## ii. Key results'", file := f} :: errors
  /- Table of contents heading -/
  let toc := headings[3]?
  match toc with
  | none =>
    errors := {msg := "No table of contents heading found", file := f} :: errors
  | some t =>
    if t ≠ "## iii. Table of contents" then
      errors := {msg := s!"Table of contents heading '{t}' is not '## iii. Table of contents'", file := f} :: errors
  /- References heading -/
  let references := headings[4]?
  match references with
  | none =>
    errors := {msg := "No references heading found", file := f} :: errors
  | some r =>
    if r ≠ "## iv. References" then
      errors := {msg := s!"References heading '{r}' is not '## iv. References'", file := f} :: errors
  /- Other headings-/
  let otherHeadings := headings.drop 5
  if otherHeadings.any (fun h ↦ h.startsWith "# ") then
    errors := {msg := s!"Other level 11 headings found: {otherHeadings.filter (fun h ↦ h.startsWith "1# ")}", file := f} :: errors
  if otherHeadings = #[] then
    errors := {msg := "No other headings found", file := f} :: errors
  let otherHeaddingsSplit := otherHeadings.map (fun h ↦ (h.splitOn " ").take 2)
  /- Should be something like '[##, ###, ##]`. -/
  let levels := otherHeaddingsSplit.map (fun h ↦ h[0]!)
  /- levels should be something like '[##, ###, ##]`. -/
  let notJustHashes := levels.filter (fun l ↦ !(l.all (· == '#')))
  if notJustHashes.size ≠ 0 then
    errors := {msg := s!"Malformed space: {notJustHashes}", file := f} :: errors
  /- Every section reference should end in a dot.  -/
  let levelsNoDot := otherHeaddingsSplit.filter (fun l ↦ !(l[1]!.endsWith "."))
  if levelsNoDot.size ≠ 0 then
    errors := {msg := s!"Section references not ending in a dot: {levelsNoDot}", file := f} :: errors
  /- The number of dots should equal one less then the number of dashes e.g.
    ## A., ### A.1. etc. -/
  let badLevels := otherHeaddingsSplit.filter (fun l ↦ l[0]!.count '#' ≠ l[1]!.count '.' + 1 )
  if badLevels.size ≠ 0 then
    errors := {msg := s!"Section references with the wrong number of hashes: {badLevels}", file := f} :: errors
  /- Duplicate tags -/
  if ¬ List.Nodup otherHeaddingsSplit.toList then
    let dups := otherHeaddingsSplit.toList.filter (fun x ↦ otherHeaddingsSplit.toList.count x > 1)
    errors := {msg := s!"Duplicate section tags found {dups}", file := f} :: errors

  /- Table of contents check. -/
  let tocLines ← getTableOfContents f
  let expectedLevel1 (n : ℕ) := (otherHeadings.filter (fun l ↦ l.count '#' ≤ n)).map fun l =>
    let l' := l
    let l' := l'.replace "#### "  "  - "
    let l' := l'.replace "### "  " - "
    let l' := l'.replace "## "  "- "
    l'
  let tocLinesNoEmpty := tocLines.filter (fun l ↦ l.trim ≠ "")
  if tocLinesNoEmpty ≠ expectedLevel1 4 then
    errors := {msg := s!"Table of contents does not match headings. \n Given:
{String.intercalate "\n" tocLinesNoEmpty.toList}\n Expected:
{String.intercalate "\n" (expectedLevel1 4).toList}\nEnd of Error.", file := f} :: errors
  return errors

/-- The array of modules not to be linted. -/
def noLintArray : IO (Array FilePath) := do
  let path := (mkFilePath ["scripts", "MetaPrograms", "module_doc_no_lint"]).addExtension "txt"
  let lines ← IO.FS.lines path
  return lines.map (fun l ↦ mkFilePath [l])

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `PhysLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let filePaths := hepLeanMod.imports.filterMap (fun imp ↦
    if imp.module == `Init then
      none
    else
      some ((mkFilePath (imp.module.toString.split (· == '.'))).addExtension "lean"))
  let noLint ← noLintArray
  let modulesToCheck := filePaths.filter (fun p ↦ !noLint.contains p)
  let errors := (← modulesToCheck.mapM checkHeadings).toList.flatten
  /- Printing the errors -/
  for eM in errors do
    IO.println s!"\x1b[31mError: \x1b[0m {eM.file}: {eM.msg}"
  if errors.length > 0 then
    IO.println "\n"
    throw <| IO.userError s!"Errors found."
  else
    IO.println "\x1b[32mNo documentation style issues found.\x1b[0m"
  return 0

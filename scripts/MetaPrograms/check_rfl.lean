/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import HepLean.Meta.AllFilePaths
import HepLean.Meta.TransverseTactics
import Lake.Util.Log
/-!

This file produces a list of places where `rfl` will complete the goal.

## References
The content of this file is based on the following sources (released under the Apache 2.0 license).

- https://github.com/dwrensha/tryAtEachStep/blob/main/tryAtEachStep.lean
- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

Modifications have been made to the original content of these files here.

See also:
- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E
-/

namespace Lean.Elab.TacticInfo

def name? : TacticInfo → Option Name
  | {stx := .node _ kind _, ..} => kind
  | _ => none

/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  open Lean.Parser in
  match t.name? with
  | ``cdot
  | ``cdotTk
  | ``Tactic.«tactic_<;>_»
  | ``Tactic.case
  | ``Tactic.change
  | ``Tactic.changeWith
  | ``Tactic.exact
  | ``Tactic.inductionAlt
  | ``Tactic.paren
  | ``Tactic.tacticSeq
  | ``Tactic.tacticSeq1Indented
  | ``Tactic.tacticSeqBracketed
  | ``Term.byTactic
  | `null
  | none
      => false
  | _ => true

end Lean.Elab.TacticInfo

open Lean Elab
open System (FilePath)

#check Lake.LogLevel.ansiColor
#check Lake.Ansi.chalk

def printRfl (s : String) : IO Unit :=
  println! Lake.Ansi.chalk (Lake.LogLevel.ansiColor .warning) s
def printSynthetic (s : String) : IO Unit :=
  println! Lake.Ansi.chalk (Lake.LogLevel.ansiColor .info) s

def visitTacticInfo (file : FilePath) (ci : ContextInfo) (ti : TacticInfo) : CoreM Unit := do
  let {stx, ..} := ti
  let some sp := stx.getPos? (canonicalOnly := true) | return -- Ignore `Lean.SourceInfo.synthetic`
  let some ep := stx.getTailPos? | return
  let s := ci.fileMap.source.extract sp ep
  let {line, column} := ci.fileMap.toPosition sp
  let message := s!"{file}:{line}:{column + 1} [{ti.name?}] {s}"
  unless ti.isSubstantive do
    printSynthetic message
    return
  if s == "rfl" then
    printRfl message
  else
    println! message
  -- println! s!"goalsBefore.size == {ti.goalsBefore.length}"
  /-
  for g in ti.goalsBefore do
    (← IO.getStdout).flush
    let mctx := ti.mctxBefore
    --let doprint : MetaM _ := Meta.ppGoal g
    --let x ← doprint.run' (s := {mctx})
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
              <| Tactic.run g (Tactic.evalTactic (← `(tactic| rfl)))
    try
      let (mvars, _) ← dotac.run' {} {mctx}
      if mvars.isEmpty && s != "rfl" then
        let {line, column} := ci.fileMap.toPosition sp
        println! "{file}:{line}:{column + 1} {s}"
    catch _ => pure ()
    return
  -/
    -- println! "extra"


/- See conversation here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E -/
unsafe def processAllFiles : IO Unit := do
  let files ← allFilePaths
  let tasks := files.map fun f =>
    ((IO.asTask $ IO.Process.run
    {cmd := "lake", args := #["exe", "check_rfl", f.toString]}), f)
  tasks.toList.enum.forM fun (n, (t, path)) => do
    println! "{n} of {tasks.size}: {path}"
    let tn ← IO.wait (← t)
    match tn with
    | .ok x => println! x
    | .error _ => println! "Error"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [path] => transverseTactics path visitTacticInfo
  | _ => processAllFiles

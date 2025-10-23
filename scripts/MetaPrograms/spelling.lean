/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Post
import Mathlib.Lean.CoreM
import PhysLean.Meta.Linters.Sorry
import PhysLean.Meta.Sorry
import Mathlib.Data.List.Defs
/-!

# Script to help checking spelling of results

-/

open Lean

def allWords : MetaM (Array String) := do
  let allConstants ← PhysLean.allUserConsts
  let allDocStrings ← allConstants.mapM fun c => Lean.Name.getDocString c.name
  let allDocStrings := allDocStrings.filter (fun x => x ≠ "")
  let allList := allDocStrings.flatMap (fun s =>
      (s.split (fun c => c.isWhitespace || ".,?!:;()[]{}<>\"'".contains c)).toArray)
  let allList := (allList.filter (fun w => w ≠ "" ∧ w ≠ " ")).toList.dedup.toArray

  let allList := allList.qsort (fun a b => a < b)
  let allList := allList.filter (fun s => s.all Char.isAlpha)
  return allList

unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  println! "Checking spelling."
  let env ← importModules (loadExts := true) #[`PhysLean] {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let (array, _) ← (Lean.Core.CoreM.toIO · ctx state) do (allWords).run'
  println! "{array}"

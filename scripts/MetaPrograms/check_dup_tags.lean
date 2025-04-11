/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
import PhysLean.Meta.TODO.Basic
import Mathlib.Lean.CoreM
import PhysLean.Meta.Informal.Post
import PhysLean.Meta.Informal.SemiFormal
/-!

# Checks for duplicate TODO tags

-/

open Lean System Meta PhysLean


def tagsFromTODOs : MetaM (Array String) := do
  let env ← getEnv
  let todoInfo := (todoExtension.getState env)
  -- pure (todoInfo.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList
  pure (todoInfo.map fun x => x.tag)

unsafe def informalTODO (x : ConstantInfo) : CoreM String := do
  let tag ← Informal.getTag x
  return tag

unsafe def tagsFromInformal : CoreM (Array String) := do
  (← AllInformal).mapM (fun x => Informal.getTag x)

unsafe def tagsFromSemiformal  : CoreM (Array String) := do
  let env ← getEnv
  let semiInformalInfos := (wantedExtension.getState env)
  pure (semiInformalInfos.map fun x => x.tag)

unsafe def tagDuplicateTest : MetaM Unit := do
  let tags := ((← tagsFromTODOs) ++ (← tagsFromInformal) ++ (← tagsFromSemiformal)).toList
  if !tags.Nodup then
    let duplicates := tags.filter (fun tag => tags.count tag > 1) |>.eraseDups
    println! duplicates
    panic! s!"Duplicate tags found: {duplicates}"
  pure ()

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  println! "Checking for duplicate tags."
  let _ ← CoreM.withImportModules #[`PhysLean] (tagDuplicateTest).run'
  println! "Finish duplicate tag check."
  pure 0
